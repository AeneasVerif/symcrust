// Allows printing errors, which is a prerequisite for using ERROR as an argument to
// std::result::Result.
impl std::fmt::Display for Error {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        write!(f, "{}", self)
    }
}

// Allows using errors within std::result::Result.
impl std::error::Error for Error {}

// Allows using the ? operator to early-return in functions that return MLKEM_ERROR, capturing the
// fact that NO_ERROR is the success case.
// Note: this requires
impl std::ops::FromResidual<Result<std::convert::Infallible, Error>> for Error {
    fn from_residual(r: Result<std::convert::Infallible, Error>) -> Error {
        match r {
            Result::Ok(_) => Error::NoError,
            Result::Err(e) => e,
        }
    }
}

