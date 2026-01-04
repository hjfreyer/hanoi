use std::io::{BufReader, BufWriter};
use std::net::TcpListener;
use std::path::PathBuf;
use std::sync::{Arc, Mutex};

use anyhow::{Context, Result};
use dap::events::{OutputEventBody, StoppedEventBody};
use dap::prelude::*;
use dap::responses::{
    ResponseBody, ScopesResponse, SetBreakpointsResponse, StackTraceResponse, ThreadsResponse,
    VariablesResponse,
};
use hanoi::bytecode::{Library as BytecodeLibrary, SentenceIndex};
use hanoi::parser::source;
use hanoi::vm::{ProgramCounter, Vm};
use hanoi::{compiler2, vm};

use itertools::Itertools;
struct DebugSession {
    bytecode: BytecodeLibrary,
    vm: Vm,
}

impl DebugSession {
    fn step(&mut self, granularity: Option<dap::types::SteppingGranularity>) -> Result<()> {
        match granularity.unwrap_or(dap::types::SteppingGranularity::Statement) {
            dap::types::SteppingGranularity::Statement => {
                // Step until we reach a new statement (new line in source)
                self.step_to_next_line()
            }
            dap::types::SteppingGranularity::Line => {
                // Step until we reach a new line in source
                self.step_to_next_line()
            }
            dap::types::SteppingGranularity::Instruction => {
                // Default: step one instruction (word) at a time
                self.vm
                    .step()
                    .map(|_| ())
                    .map_err(|e| anyhow::anyhow!("{:?}", e))
            }
        }
    }

    fn step_to_next_line(&mut self) -> Result<()> {
        // Get the current line number
        let current_line = self
            .vm
            .call_stack
            .last()
            .and_then(|pc| {
                let debuginfo = &self.bytecode.debuginfo;
                let sentence_idx: usize = pc.sentence_idx.into();
                debuginfo
                    .sentences
                    .get(sentence_idx)
                    .and_then(|sentence| sentence.words.get(pc.word_idx))
                    .and_then(|word| word.span.as_ref())
                    .map(|span| span.begin.line)
            })
            .unwrap_or(0);

        // Step until we reach a different line or the program exits
        loop {
            match self.vm.step() {
                Ok(hanoi::vm::StepResult::Exit) => {
                    return Ok(());
                }
                Ok(hanoi::vm::StepResult::Continue) => {
                    // Check if we've moved to a new line
                    let new_line = self.vm.call_stack.last().and_then(|pc| {
                        let debuginfo = &self.bytecode.debuginfo;
                        let sentence_idx: usize = pc.sentence_idx.into();
                        debuginfo
                            .sentences
                            .get(sentence_idx)
                            .and_then(|sentence| sentence.words.get(pc.word_idx))
                            .and_then(|word| word.span.as_ref())
                            .map(|span| span.begin.line)
                    });

                    if let Some(line) = new_line {
                        if line != current_line {
                            // We've reached a new line, stop stepping
                            return Ok(());
                        }
                    } else {
                        // No debug info available, step once and stop
                        return Ok(());
                    }
                }
                Err(e) => {
                    return Err(anyhow::anyhow!("VM step error: {:?}", e));
                }
            }
        }
    }

    fn get_locals(&self, _frame_id: i64) -> Vec<types::Variable> {
        eprintln!("Get locals: {}", _frame_id);
        let Some(last_frame) = self.vm.stack.iter().last() else {
            eprintln!("No last frame");
            return vec![];
        };
        let vm::Value::Tuple(vals) = last_frame else {
            eprintln!("Last frame is not a tuple: {:?}", last_frame);
            return vec![];
        };
        let Some((vm::Value::Map(locals), stack)) = vals.iter().collect_tuple() else {
            eprintln!("tuple structure wrong: {:?}", vals);
            return vec![];
        };
        locals
            .iter()
            .map(|(k, v)| types::Variable {
                name: format!("local[{:?}]", k),
                value: format_value(v),
                type_field: Some(v.r#type().to_string()),
                ..Default::default()
            })
            .collect()
    }

    fn get_stack(&self, _frame_id: i64) -> Vec<types::Variable> {
        // Return each stack entry as its own variable
        // Stack is iterated in reverse so stack[0] is the top
        self.vm
            .stack
            .iter()
            .rev()
            .enumerate()
            .map(|(idx, value)| {
                let value_str = format_value(value);
                types::Variable {
                    name: format!("stack[{}]", idx),
                    value: value_str,
                    type_field: Some(value.r#type().to_string()),
                    ..Default::default()
                }
            })
            .collect()
    }
}

struct DebuggerState {
    session: Option<DebugSession>,
    program_path: Option<PathBuf>,
}

fn main() -> Result<()> {
    // Listen on a TCP port instead of stdio.
    // Default to 127.0.0.1:4711, overridable via HANOI_DAP_ADDR.
    let addr = std::env::var("HANOI_DAP_ADDR").unwrap_or_else(|_| "127.0.0.1:4711".to_string());
    let listener = TcpListener::bind(&addr)?;
    eprintln!("Hanoi DAP debugger listening on {}", addr);

    // Handle a single client connection then exit.
    if let Some(stream) = listener.incoming().next() {
        let stream = stream?;
        let input = BufReader::new(stream.try_clone()?);
        let output = BufWriter::new(stream);

        let mut server = Server::new(input, output);
        let state = Arc::new(Mutex::new(DebuggerState {
            session: None,
            program_path: None,
        }));

        while let Some(request) = server.poll_request()? {
            if let Err(err) = handle_request(&mut server, request, Arc::clone(&state)) {
                let error_msg = format!("Error handling request: {:#}\n", err);
                eprintln!("{}", error_msg);
                let _ = send_console_output(&mut server, &error_msg);
            }
        }
    }

    Ok(())
}

fn handle_request<R, W>(
    server: &mut Server<R, W>,
    request: Request,
    state: Arc<Mutex<DebuggerState>>,
) -> Result<()>
where
    R: std::io::Read,
    W: std::io::Write,
{
    match request.command {
        Command::Initialize(_) => {
            send_console_output(server, "Initializing Hanoi debugger (dap-rs)...\n")?;
            let caps = types::Capabilities {
                supports_configuration_done_request: Some(true),
                supports_stepping_granularity: Some(true),
                ..Default::default()
            };
            let response = request.success(ResponseBody::Initialize(caps));
            server.respond(response)?;

            server.send_event(Event::Initialized)?;
        }
        Command::Launch(ref args) => {
            send_console_output(server, "Launching Hanoi program...\n")?;
            // Extract program path from launch arguments
            // The program field is typically in the launch arguments
            let program_path = args
                .additional_data
                .as_ref()
                .and_then(|data| data.get("program"))
                .and_then(|v| v.as_str())
                .map(PathBuf::from)
                .context("Program path not specified in launch arguments")?;

            // Determine base directory (parent of the .han file)
            let base_dir = program_path
                .parent()
                .context("Program path has no parent directory")?
                .to_path_buf();

            // Compile the .han file
            send_console_output(
                server,
                &format!("Compiling {}...\n", program_path.display()),
            )?;
            let loader = source::Loader { base_dir };
            let bytecode =
                compiler2::compile(&loader).context("Failed to compile Hanoi program")?;

            // Store in state
            {
                let mut state = state.lock().unwrap();
                let vm = Vm::new(bytecode.clone(), SentenceIndex::from(0));
                state.program_path = Some(program_path.clone());
                let mut session = DebugSession { bytecode, vm };
                session.vm.reset_call_stack();
                state.session = Some(session);
            }

            let response = request.clone().success(ResponseBody::Launch);
            server.respond(response)?;

            send_console_output(
                server,
                &format!(
                    "Hanoi debugger compiled and loaded program from {}\n",
                    program_path.display()
                ),
            )?;

            // Send a stop event to indicate the program is ready to be debugged
            let stop_body = StoppedEventBody {
                reason: dap::types::StoppedEventReason::Entry,
                description: Some("Program launched and ready for debugging".to_string()),
                thread_id: Some(1),
                preserve_focus_hint: None,
                text: None,
                all_threads_stopped: None,
                hit_breakpoint_ids: None,
            };
            server.send_event(Event::Stopped(stop_body))?;
        }
        Command::ConfigurationDone => {
            send_console_output(server, "Configuration done.\n")?;
            let response = request.success(ResponseBody::ConfigurationDone);
            server.respond(response)?;
        }
        Command::SetBreakpoints(_) => {
            send_console_output(server, "Setting breakpoints...\n")?;
            let body = ResponseBody::SetBreakpoints(SetBreakpointsResponse {
                breakpoints: vec![],
            });
            let response = request.success(body);
            server.respond(response)?;
        }
        Command::Threads => {
            send_console_output(server, "Getting threads...\n")?;
            let body = ResponseBody::Threads(ThreadsResponse {
                threads: vec![types::Thread {
                    id: 1,
                    name: "main".to_string(),
                    ..Default::default()
                }],
            });
            let response = request.success(body);
            server.respond(response)?;
        }
        Command::StepIn(ref args) => {
            let granularity = args.granularity.as_ref();

            {
                let mut state = state.lock().unwrap();
                if let Some(ref mut session) = state.session {
                    match session.step(granularity.cloned()) {
                        Ok(_) => {
                            // VM advanced one step
                        }
                        Err(err) => {
                            let msg = format!("VM step error: {err:?}\n");
                            let _ = send_console_output(server, &msg);
                        }
                    }
                } else {
                    let _ = send_console_output(
                        server,
                        "No debug session available; did launch succeed?\n",
                    );
                }
            }

            let response = request.success(ResponseBody::StepIn);
            server.respond(response)?;

            // After stepping, notify the client that execution has stopped again.
            let stop_body = StoppedEventBody {
                reason: dap::types::StoppedEventReason::Step,
                description: Some("Stepped in".to_string()),
                thread_id: Some(1),
                preserve_focus_hint: None,
                text: None,
                all_threads_stopped: Some(true),
                hit_breakpoint_ids: None,
            };
            server.send_event(Event::Stopped(stop_body))?;
        }
        Command::StackTrace(_) => {
            send_console_output(server, "Getting stack trace...\n")?;

            let (stack_frames, total_frames) = {
                let state = state.lock().unwrap();
                if let Some(ref session) = state.session {
                    build_stack_frames(&session.bytecode, &session.vm)
                        .context("Failed to build stack frames")?
                } else {
                    (vec![], Some(0))
                }
            };

            let body = ResponseBody::StackTrace(StackTraceResponse {
                stack_frames,
                total_frames,
            });
            let response = request.success(body);
            server.respond(response)?;
        }
        Command::Scopes(ref args) => {
            send_console_output(server, "Getting scopes...\n")?;
            eprintln!("Get scopes: {}", args.frame_id);
            let scopes = {
                let state = state.lock().unwrap();
                if let Some(ref session) = state.session {
                    let frame_id = args.frame_id;
                    // Use frame_id * 2 for Locals, frame_id * 2 + 1 for Stack
                    let locals_ref = (frame_id as i64) * 2;
                    let stack_ref = (frame_id as i64) * 2 + 1;

                    let num_locals_variables = session.get_locals(frame_id).len() as i64;
                    let num_stack_variables = session.get_stack(frame_id).len() as i64;

                    dbg!(vec![
                        types::Scope {
                            name: "Locals".to_string(),
                            variables_reference: locals_ref,
                            named_variables: Some(num_locals_variables),
                            ..Default::default()
                        },
                        types::Scope {
                            name: "Stack".to_string(),
                            variables_reference: stack_ref,
                            named_variables: Some(num_stack_variables),
                            ..Default::default()
                        },
                    ])
                } else {
                    vec![]
                }
            };

            let body = ResponseBody::Scopes(ScopesResponse { scopes });
            let response = request.success(body);
            server.respond(response)?;
        }
        Command::Variables(ref args) => {
            send_console_output(server, "Getting variables...\n")?;

            let variables = {
                let state = state.lock().unwrap();
                if let Some(ref session) = state.session {
                    let variables_ref = args.variables_reference;

                    // Decode the variables_reference:
                    // - Even numbers (frame_id * 2) are Locals scopes
                    // - Odd numbers (frame_id * 2 + 1) are Stack scopes
                    let frame_id = variables_ref / 2;
                    if variables_ref % 2 == 0 {
                        // Locals scope
                        session.get_locals(frame_id)
                    } else {
                        // Stack scope
                        session.get_stack(frame_id)
                    }
                } else {
                    vec![]
                }
            };

            let body = ResponseBody::Variables(VariablesResponse { variables });
            let response = request.success(body);
            server.respond(response)?;
        }
        Command::Disconnect(_) => {
            send_console_output(server, "Disconnecting...\n")?;
            // Acknowledge the disconnect request; no special cleanup yet.
            let response = request.success(ResponseBody::Disconnect);
            server.respond(response)?;
            // After this, the client will typically close the connection.
        }
        ref other => {
            let message = format!("Unhandled DAP command: {:?}", other);
            eprintln!("{}", message);
            let response = request.clone().error("UnhandledCommand");
            server.respond(response)?;
            anyhow::bail!("Unhandled DAP command: {:?}", other);
        }
    }

    Ok(())
}

fn build_stack_frames(
    bytecode: &BytecodeLibrary,
    vm: &Vm,
) -> Result<(Vec<types::StackFrame>, Option<i64>)> {
    let mut frames = Vec::new();

    // Iterate through call stack in reverse order (top of stack first)
    for (frame_id, pc) in vm.call_stack.iter().rev().enumerate() {
        let frame = build_stack_frame(bytecode, *pc, frame_id as i64 + 1)?;
        frames.push(frame);
    }

    let total = frames.len() as i64;
    Ok((frames, Some(total)))
}

fn build_stack_frame(
    bytecode: &BytecodeLibrary,
    pc: ProgramCounter,
    frame_id: i64,
) -> Result<types::StackFrame> {
    let debuginfo = &bytecode.debuginfo;
    let sentence_idx: usize = pc.sentence_idx.into();

    // Get debuginfo sentence
    let debuginfo_sentence = debuginfo
        .sentences
        .get(sentence_idx)
        .with_context(|| format!("Missing debuginfo for sentence index {}", sentence_idx))?;

    // Get debuginfo word
    let debuginfo_word = debuginfo_sentence.words.get(pc.word_idx).with_context(|| {
        format!(
            "Missing debuginfo word at index {} in sentence {}",
            pc.word_idx, sentence_idx
        )
    })?;

    // Get source location from debuginfo
    let source = debuginfo_word.span.as_ref().and_then(|span| {
        debuginfo
            .files
            .get(span.file)
            .map(|file_path| types::Source {
                name: Some(
                    file_path
                        .file_name()
                        .and_then(|n| n.to_str())
                        .unwrap_or("unknown")
                        .to_string(),
                ),
                path: Some(
                    file_path
                        .canonicalize()
                        .unwrap()
                        .to_string_lossy()
                        .to_string(),
                ),
                ..Default::default()
            })
    });

    let (line, column) = debuginfo_word
        .span
        .as_ref()
        .map(|span| (span.begin.line as i64, span.begin.col as i64))
        .unwrap_or((0, 0));

    Ok(types::StackFrame {
        id: frame_id,
        name: format!("sentence_{}", sentence_idx),
        source,
        line: line,
        column: column,
        ..Default::default()
    })
}

fn format_value(value: &hanoi::vm::Value) -> String {
    match value {
        hanoi::vm::Value::Symbol(idx) => {
            let idx_val: usize = (*idx).into();
            format!("Symbol({})", idx_val)
        }
        hanoi::vm::Value::Usize(u) => format!("{}", u),
        hanoi::vm::Value::Bool(b) => format!("{}", b),
        hanoi::vm::Value::Char(c) => format!("'{}'", c),
        hanoi::vm::Value::Tuple(vals) => {
            let inner = vals
                .iter()
                .map(|v| format_value(v))
                .collect::<Vec<_>>()
                .join(", ");
            format!("({})", inner)
        }
        hanoi::vm::Value::Array(arr) => {
            let inner = arr
                .iter()
                .map(|opt| {
                    opt.as_ref()
                        .map(|v| format_value(v))
                        .unwrap_or_else(|| "None".to_string())
                })
                .collect::<Vec<_>>()
                .join(", ");
            format!("[{}]", inner)
        }
        hanoi::vm::Value::Map(map) => {
            let inner = map
                .iter()
                .map(|(k, v)| format!("{:?}: {}", k, format_value(v)))
                .collect::<Vec<_>>()
                .join(", ");
            format!("{{{}}}", inner)
        }
    }
}

fn send_console_output<R, W>(server: &mut Server<R, W>, text: &str) -> Result<()>
where
    R: std::io::Read,
    W: std::io::Write,
{
    let body = OutputEventBody {
        category: Some(dap::types::OutputEventCategory::Console),
        output: text.to_string(),
        ..Default::default()
    };
    server.send_event(Event::Output(body))?;
    Ok(())
}
