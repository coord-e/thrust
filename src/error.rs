#[derive(Debug)]
pub enum Error {
    Verification(crate::chc::CheckSatError),
}

impl From<crate::chc::CheckSatError> for Error {
    fn from(err: crate::chc::CheckSatError) -> Self {
        Error::Verification(err)
    }
}

pub type Result<T> = std::result::Result<T, Error>;
