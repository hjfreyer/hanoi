use bytecode::{Library, SentenceIndex, Value};
use crate::VM;

/// An Environment is a Hanoi CSP machine implemented in async Rust.
#[allow(async_fn_in_trait)]
pub trait Environment {
    /// Handles an event emitted by the main Hanoi machine.
    async fn handle_event(&mut self, event: Value) -> Result<(), String>;

    /// Asynchronously waits for an event.
    /// The runtime will verify whether the returned event is accepted by the main machine.
    async fn wait_for_event(&mut self) -> Result<Value, String>;
}

pub fn extract_putch_char(
    value: &Value,
    std_io: &Option<Value>,
    std_stdout: &Option<Value>,
    std_putch: &Option<Value>,
) -> Option<char> {
    if let (Some(io_val), Some(stdout_val), Some(putch_val)) = (std_io, std_stdout, std_putch) {
        if let Value::Tuple(elems) = value {
            if elems.len() == 2 {
                if &elems[0] == io_val {
                    if let Value::Tuple(elems2) = &elems[1] {
                        if elems2.len() == 2 {
                            if &elems2[0] == stdout_val {
                                if let Value::Tuple(elems3) = &elems2[1] {
                                    if elems3.len() == 2 {
                                        if &elems3[0] == putch_val {
                                            if let Value::Tuple(elems4) = &elems3[1] {
                                                if elems4.len() == 2 {
                                                    if let Value::Int(n) = elems4[0] {
                                                        return char::from_u32(n as u32);
                                                    }
                                                }
                                            }
                                        }
                                    }
                                }
                            }
                        }
                    }
                }
            }
        }
    }
    None
}

/// A default environment that accepts CSP-style stdout events and prints them to stdout,
/// optionally capturing them in an internal buffer.
pub struct DefaultEnvironment {
    capture_buffer: Option<String>,
    std_io: Option<Value>,
    std_stdout: Option<Value>,
    std_putch: Option<Value>,
}

impl DefaultEnvironment {
    /// Creates a new DefaultEnvironment that writes directly to stdout.
    pub fn new(library: &Library) -> Self {
        Self {
            capture_buffer: None,
            std_io: library.symbols.get("std::io::io").cloned(),
            std_stdout: library.symbols.get("std::io::stdout::stdout").cloned(),
            std_putch: library.symbols.get("std::io::stdout::putch").cloned(),
        }
    }

    /// Creates a new DefaultEnvironment that captures stdout in a string buffer.
    pub fn with_capture(library: &Library) -> Self {
        Self {
            capture_buffer: Some(String::new()),
            std_io: library.symbols.get("std::io::io").cloned(),
            std_stdout: library.symbols.get("std::io::stdout::stdout").cloned(),
            std_putch: library.symbols.get("std::io::stdout::putch").cloned(),
        }
    }

    /// Returns the captured output, if capture was enabled.
    pub fn captured_output(&self) -> Option<&str> {
        self.capture_buffer.as_deref()
    }
}

impl Environment for DefaultEnvironment {
    async fn handle_event(&mut self, event: Value) -> Result<(), String> {
        if let Some(ch) = extract_putch_char(&event, &self.std_io, &self.std_stdout, &self.std_putch) {
            if let Some(ref mut buf) = self.capture_buffer {
                buf.push(ch);
            } else {
                use std::io::Write;
                print!("{}", ch);
                let _ = std::io::stdout().flush();
            }
        }
        Ok(())
    }

    async fn wait_for_event(&mut self) -> Result<Value, String> {
        Err("DefaultEnvironment does not support input events".to_string())
    }
}

/// The Runtime coordinates a VM running a "main" Hanoi CSP machine and an async Rust Environment.
pub struct Runtime<E: Environment> {
    vm: VM,
    pub environment: E,
    main_init: SentenceIndex,
    main_accept: SentenceIndex,
    main_tau_reduce: SentenceIndex,
    main_emit: SentenceIndex,
    main_process: SentenceIndex,
    main_is_done: SentenceIndex,
    #[allow(dead_code)]
    main_is_ready_to_finish: SentenceIndex,
}

impl<E: Environment> Runtime<E> {
    /// Creates a new Runtime.
    ///
    /// # Arguments
    /// * `library` - The compiled bytecode library.
    /// * `prefix` - The namespace of the main Hanoi machine (e.g., "main").
    /// * `environment` - The async Rust environment instance.
    pub fn new(
        library: Library,
        prefix: &str,
        environment: E,
    ) -> Result<Self, String> {
        let resolve = |suffix: &str| -> Result<SentenceIndex, String> {
            let name = format!("{}::{}", prefix, suffix);
            library.exports.get(&name)
                .copied()
                .ok_or_else(|| format!("Could not find sentence export '{}'", name))
        };

        let main_init = resolve("init")?;
        let main_accept = resolve("accept")?;
        let main_tau_reduce = resolve("tau_reduce")?;
        let main_emit = resolve("emit")?;
        let main_process = resolve("process")?;
        let main_is_done = resolve("is_done")?;
        let main_is_ready_to_finish = resolve("is_ready_to_finish")?;

        Ok(Self {
            vm: VM::new(library),
            environment,
            main_init,
            main_accept,
            main_tau_reduce,
            main_emit,
            main_process,
            main_is_done,
            main_is_ready_to_finish,
        })
    }

    /// Access the underlying VM.
    pub fn vm(&self) -> &VM {
        &self.vm
    }

    /// Access the underlying VM mutably.
    pub fn vm_mut(&mut self) -> &mut VM {
        &mut self.vm
    }

    /// Runs the coordinate execution loop until the main Hanoi machine terminates (is_done returns true).
    pub async fn run(&mut self) -> Result<(), String> {
        let mut state = self.execute_init()?;

        loop {
            // 1. Fixed-point tau reductions
            loop {
                let (new_state, did_reduce) = self.execute_tau_reduce(state.clone())?;
                state = new_state;
                if !did_reduce {
                    break;
                }
            }

            // 2. Check if done
            if self.execute_is_done(state.clone())? {
                break;
            }

            // 3. Check if the hanoi machine wants to emit an event
            let (event, has_event) = self.execute_emit(state.clone())?;
            if has_event {
                // Pass event off to the environment
                self.environment.handle_event(event.clone()).await?;
                // Transition Main state
                state = self.execute_process(state, event)?;
                continue;
            }

            // 4. Asynchronously wait for the environment to pass an event
            let event = self.environment.wait_for_event().await?;
            if !self.execute_accept(state.clone(), event.clone())? {
                return Err(format!(
                    "Environment returned event {:?}, which is not accepted by the machine",
                    event
                ));
            }

            // 6. Transition Main state
            state = self.execute_process(state, event)?;
        }

        Ok(())
    }

    /// Runs the coordinate execution loop for a test.
    /// It sends the start_val event, runs the SUT, and checks if it emits pass_val or fail_val.
    pub async fn run_test(
        &mut self,
        start_val: &Value,
        pass_val: &Value,
        fail_val: &Value,
    ) -> Result<(), String> {
        let mut state = self.execute_init()?;

        // 1. Initial fixed-point tau reductions
        loop {
            let (new_state, did_reduce) = self.execute_tau_reduce(state.clone())?;
            state = new_state;
            if !did_reduce {
                break;
            }
        }

        // 2. Check if start_val is accepted
        if !self.execute_accept(state.clone(), start_val.clone())? {
            return Err(format!(
                "Test machine does not accept start event {:?}",
                start_val
            ));
        }

        // 3. Process the start event
        state = self.execute_process(state, start_val.clone())?;

        // 4. Run coordinated loop
        loop {
            // A. Fixed-point tau reductions
            loop {
                let (new_state, did_reduce) = self.execute_tau_reduce(state.clone())?;
                state = new_state;
                if !did_reduce {
                    break;
                }
            }

            // B. Check if the hanoi machine wants to emit an event
            let (event, has_event) = self.execute_emit(state.clone())?;
            if has_event {
                if &event == pass_val {
                    return Ok(());
                } else if &event == fail_val {
                    return Err("Test failed: emitted fail event".to_string());
                }

                // Pass event off to the environment
                self.environment.handle_event(event.clone()).await?;
                // Transition Main state
                state = self.execute_process(state, event)?;
                continue;
            }

            // C. Check if done (terminated without emitting pass or fail)
            if self.execute_is_done(state.clone())? {
                return Err("Test machine terminated without emitting pass or fail event".to_string());
            }

            // D. Asynchronously wait for the environment to pass an event
            let event = self.environment.wait_for_event().await?;
            if !self.execute_accept(state.clone(), event.clone())? {
                return Err(format!(
                    "Environment returned event {:?}, which is not accepted by the machine",
                    event
                ));
            }

            // F. Transition Main state
            state = self.execute_process(state, event)?;
        }
    }

    // Helper sentence execution wrappers

    fn execute_init(&mut self) -> Result<Value, String> {
        if !self.vm.stack.is_empty() {
            return Err(format!("Stack not empty before init: {:?}", self.vm.stack));
        }
        self.vm.stack.push(Value::Tuple(Vec::new()));
        self.vm.execute(self.main_init)?;
        let res = self.vm.pop()?;
        if !self.vm.stack.is_empty() {
            return Err(format!("Stack not empty after init: {:?}", self.vm.stack));
        }
        Ok(res)
    }

    fn execute_accept(&mut self, state: Value, event: Value) -> Result<bool, String> {
        if !self.vm.stack.is_empty() {
            return Err(format!("Stack not empty before accept: {:?}", self.vm.stack));
        }
        let pair = Value::Tuple(vec![state, event]);
        self.vm.stack.push(pair);
        self.vm.execute(self.main_accept)?;
        let res = self.vm.pop()?;
        if !self.vm.stack.is_empty() {
            return Err(format!("Stack not empty after accept: {:?}", self.vm.stack));
        }
        match res {
            Value::Bool(b) => Ok(b),
            v => Err(format!("Expected Value::Bool from accept, found {:?}", v)),
        }
    }

    fn execute_tau_reduce(&mut self, state: Value) -> Result<(Value, bool), String> {
        if !self.vm.stack.is_empty() {
            return Err(format!("Stack not empty before tau_reduce: {:?}", self.vm.stack));
        }
        self.vm.stack.push(state);
        self.vm.execute(self.main_tau_reduce)?;
        let res = self.vm.pop()?;
        if !self.vm.stack.is_empty() {
            return Err(format!("Stack not empty after tau_reduce: {:?}", self.vm.stack));
        }
        match res {
            Value::Tuple(mut elems) if elems.len() == 2 => {
                let new_state = elems.pop().unwrap();
                let did_reduce = match elems.pop().unwrap() {
                    Value::Bool(b) => b,
                    v => return Err(format!("Expected bool for did_reduce, found {:?}", v)),
                };
                Ok((new_state, did_reduce))
            }
            other => Err(format!("Expected (new_state, did_reduce) tuple from tau_reduce, found {:?}", other))
        }
    }

    fn execute_emit(&mut self, state: Value) -> Result<(Value, bool), String> {
        if !self.vm.stack.is_empty() {
            return Err(format!("Stack not empty before emit: {:?}", self.vm.stack));
        }
        self.vm.stack.push(state);
        self.vm.execute(self.main_emit)?;
        let res = self.vm.pop()?;
        if !self.vm.stack.is_empty() {
            return Err(format!("Stack not empty after emit: {:?}", self.vm.stack));
        }
        match res {
            Value::Tuple(mut elems) if elems.len() == 2 => {
                let event = elems.pop().unwrap();
                let has_event = match elems.pop().unwrap() {
                    Value::Bool(b) => b,
                    v => return Err(format!("Expected bool for has_event, found {:?}", v)),
                };
                Ok((event, has_event))
            }
            other => Err(format!("Expected (event, has_event) tuple from emit, found {:?}", other))
        }
    }

    fn execute_process(&mut self, state: Value, event: Value) -> Result<Value, String> {
        if !self.vm.stack.is_empty() {
            return Err(format!("Stack not empty before process: {:?}", self.vm.stack));
        }
        self.vm.stack.push(Value::Tuple(vec![state, event]));
        self.vm.execute(self.main_process)?;
        let res = self.vm.pop()?;
        if !self.vm.stack.is_empty() {
            return Err(format!("Stack not empty after process: {:?}", self.vm.stack));
        }
        Ok(res)
    }

    fn execute_is_done(&mut self, state: Value) -> Result<bool, String> {
        if !self.vm.stack.is_empty() {
            return Err(format!("Stack not empty before is_done: {:?}", self.vm.stack));
        }
        self.vm.stack.push(state);
        self.vm.execute(self.main_is_done)?;
        let res = self.vm.pop()?;
        if !self.vm.stack.is_empty() {
            return Err(format!("Stack not empty after is_done: {:?}", self.vm.stack));
        }
        match res {
            Value::Bool(b) => Ok(b),
            v => Err(format!("Expected bool from is_done, found {:?}", v)),
        }
    }
}
