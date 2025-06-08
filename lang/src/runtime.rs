use itertools::Itertools;

use crate::{flat, vm::Vm};

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
}
