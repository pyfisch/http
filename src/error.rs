use std::error;
use std::fmt;
use std::result;

use url;

use header;
use method;
use request;
use status;

/// A generic "error" for HTTP connections
///
/// This error type is less specific than the error returned from other
/// functions in this crate, but all other errors can be converted to this
/// error. Consumers of this crate can typically consume and work with this form
/// of error for conversions with the `?` operator.
#[derive(Debug)]
pub struct Error {
    inner: ErrorKind,
}

/// A `Result` typedef to use with the `http::Error` type
pub type Result<T> = result::Result<T, Error>;

#[derive(Debug)]
enum ErrorKind {
    StatusCode(status::InvalidStatusCode),
    Method(method::InvalidMethod),
    Url(url::ParseError),
    BadTarget(request::BadTarget),
    HeaderName(header::InvalidHeaderName),
    HeaderNameShared(header::InvalidHeaderNameBytes),
    HeaderValue(header::InvalidHeaderValue),
    HeaderValueShared(header::InvalidHeaderValueBytes),
}

impl fmt::Display for Error {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        error::Error::description(self).fmt(f)
    }
}

impl error::Error for Error {
    fn description(&self) -> &str {
        use self::ErrorKind::*;

        match self.inner {
            StatusCode(ref e) => e.description(),
            Method(ref e) => e.description(),
            Url(ref e) => e.description(),
            BadTarget(ref e) => e.description(),
            HeaderName(ref e) => e.description(),
            HeaderNameShared(ref e) => e.description(),
            HeaderValue(ref e) => e.description(),
            HeaderValueShared(ref e) => e.description(),
        }
    }
}

impl From<status::InvalidStatusCode> for Error {
    fn from(err: status::InvalidStatusCode) -> Error {
        Error { inner: ErrorKind::StatusCode(err) }
    }
}

impl From<method::InvalidMethod> for Error {
    fn from(err: method::InvalidMethod) -> Error {
        Error { inner: ErrorKind::Method(err) }
    }
}

impl From<url::ParseError> for Error {
    fn from(err: url::ParseError) -> Error {
        Error { inner: ErrorKind::Url(err) }
    }
}

impl From<request::BadTarget> for Error {
    fn from(err: request::BadTarget) -> Error {
        Error { inner: ErrorKind::BadTarget(err) }
    }
}

impl From<header::InvalidHeaderName> for Error {
    fn from(err: header::InvalidHeaderName) -> Error {
        Error { inner: ErrorKind::HeaderName(err) }
    }
}

impl From<header::InvalidHeaderNameBytes> for Error {
    fn from(err: header::InvalidHeaderNameBytes) -> Error {
        Error { inner: ErrorKind::HeaderNameShared(err) }
    }
}

impl From<header::InvalidHeaderValue> for Error {
    fn from(err: header::InvalidHeaderValue) -> Error {
        Error { inner: ErrorKind::HeaderValue(err) }
    }
}

impl From<header::InvalidHeaderValueBytes> for Error {
    fn from(err: header::InvalidHeaderValueBytes) -> Error {
        Error { inner: ErrorKind::HeaderValueShared(err) }
    }
}
