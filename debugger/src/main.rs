use std::io::{self, BufReader, BufWriter};

use dap::events::OutputEventBody;
use dap::prelude::*;
use dap::responses::{ResponseBody, SetBreakpointsResponse, ThreadsResponse};
use thiserror::Error;

#[derive(Error, Debug)]
enum AdapterError {
    #[error("Unhandled command")]
    UnhandledCommand,
}

type Result<T> = std::result::Result<T, Box<dyn std::error::Error + Send + Sync>>;

fn main() -> Result<()> {
    let stdin = io::stdin();
    let stdout = io::stdout();

    let input = BufReader::new(stdin.lock());
    let output = BufWriter::new(stdout.lock());

    let mut server = Server::new(input, output);

    while let Some(request) = server.poll_request()? {
        handle_request(&mut server, request)?;
    }

    Ok(())
}

fn handle_request<R, W>(server: &mut Server<R, W>, request: Request) -> Result<()>
where
    R: std::io::Read,
    W: std::io::Write,
{
    match request.command {
        Command::Initialize(_) => {
            let caps = types::Capabilities::default();
            let response = request.success(ResponseBody::Initialize(caps));
            server.respond(response)?;

            server.send_event(Event::Initialized)?;
            send_console_output(server, "Hanoi debugger (dap-rs) initialized and running.\n")?;
        }
        Command::Launch(ref args) => {
            let _ = args; // placeholder for future runtime wiring

            let response = request.clone().success(ResponseBody::Launch);
            server.respond(response)?;
            eprintln!("eprintln test.");
            send_console_output(server, "Hanoi debugger (dap-rs) received launch request.\n")?;
        }
        Command::ConfigurationDone => {
            let response = request.success(ResponseBody::ConfigurationDone);
            server.respond(response)?;
        }
        Command::SetBreakpoints(_) => {
            let body = ResponseBody::SetBreakpoints(SetBreakpointsResponse {
                breakpoints: vec![],
            });
            let response = request.success(body);
            server.respond(response)?;
        }
        Command::Threads => {
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
        ref other => {
            let message = format!("Unhandled DAP command: {:?}", other);
            eprintln!("{}", message);
            let response = request.clone().error("UnhandledCommand");
            server.respond(response)?;
            return Err(Box::new(AdapterError::UnhandledCommand));
        }
    }

    Ok(())
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

