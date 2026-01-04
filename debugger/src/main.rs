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
use hanoi::compiler2;
use hanoi::parser::source;
use hanoi::vm::{ProgramCounter, Vm};

struct DebuggerState {
    bytecode: Option<BytecodeLibrary>,
    program_path: Option<PathBuf>,
    vm: Option<Vm>,
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
            bytecode: None,
            program_path: None,
            vm: None,
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
                state.bytecode = Some(bytecode.clone());
                state.program_path = Some(program_path.clone());
                state.vm = Some(Vm::new(bytecode, SentenceIndex::from(0)));
                state.vm.as_mut().unwrap().reset_call_stack();
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
        Command::StepIn(_) => {
            send_console_output(server, "Stepping in...\n")?;

            {
                let mut state = state.lock().unwrap();
                if let Some(ref mut vm) = state.vm {
                    match vm.step() {
                        Ok(_) => {
                            // VM advanced one step; nothing else to do here for now.
                        }
                        Err(err) => {
                            // Log VM step errors to the debug console.
                            let msg = format!("VM step error: {err:?}\n");
                            // Ignore errors from console output to avoid masking the original error.
                            let _ = send_console_output(server, &msg);
                        }
                    }
                } else {
                    let _ = send_console_output(
                        server,
                        "No VM available to step; did launch succeed?\n",
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
                if let (Some(ref vm), Some(ref bytecode)) =
                    (state.vm.as_ref(), state.bytecode.as_ref())
                {
                    build_stack_frames(bytecode, vm).context("Failed to build stack frames")?
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
        Command::Scopes(_) => {
            send_console_output(server, "Getting scopes...\n")?;

            let scopes = {
                let state = state.lock().unwrap();
                if let Some(ref vm) = state.vm {
                    let num_variables = vm.stack.len() as i64;

                    vec![types::Scope {
                        name: "Stack".to_string(),
                        variables_reference: 1,
                        named_variables: Some(num_variables),
                        ..Default::default()
                    }]
                } else {
                    vec![]
                }
            };

            let body = ResponseBody::Scopes(ScopesResponse { scopes });
            let response = request.success(body);
            server.respond(response)?;
        }
        Command::Variables(ref _args) => {
            send_console_output(server, "Getting variables...\n")?;

            let variables = {
                let state = state.lock().unwrap();
                if let Some(ref vm) = state.vm {
                    // Return each stack entry as its own variable
                    // Stack is iterated in reverse so stack[0] is the top
                    vm.stack
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
        let frame = build_stack_frame(bytecode, *pc, frame_id as i64)?;
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
