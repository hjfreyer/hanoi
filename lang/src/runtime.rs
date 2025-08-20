use itertools::Itertools;

use crate::flat;

pub struct Runtime {}

#[derive(Debug, thiserror::Error)]
pub enum Error {
    #[error("Invalid value")]
    InvalidValue,
}

impl Runtime {
    pub fn handle_request(&mut self, value: flat::Value) -> Result<flat::Value, Error> {
        let Some((tag, args)) = value.into_tagged() else {
            return Err(Error::InvalidValue);
        };
        match tag.as_str() {
            "stall" => {
                // Handle stall request
                let msg = args
                    .into_iter()
                    .exactly_one()
                    .map_err(|_| Error::InvalidValue)?;
                Ok(msg)
            }
            _ => Err(Error::InvalidValue),
        }
    }
    
    pub(crate) fn handle_exit(&self, status: usize) {
        std::process::exit(status as i32)
    }
}
