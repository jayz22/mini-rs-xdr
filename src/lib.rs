use std::{
    error, fmt, io,
    io::{BufRead, BufReader, Cursor, Read, Write},
    marker::PhantomData,
};

#[allow(dead_code)]
type Result<T> = core::result::Result<T, Error>;

/// Error contains all errors returned by functions in this crate. It can be
/// compared via `PartialEq`, however any contained IO errors will only be
/// compared on their `ErrorKind`.
#[derive(Debug)]
pub enum Error {
    Invalid,
    Unsupported,
    LengthExceedsMax,
    LengthMismatch,
    NonZeroPadding,
    Utf8Error(core::str::Utf8Error),
    #[cfg(feature = "alloc")]
    InvalidHex,
    Io(io::Error),
    StackOverflow,
}

impl PartialEq for Error {
    fn eq(&self, other: &Self) -> bool {
        match (self, other) {
            (Self::Utf8Error(l), Self::Utf8Error(r)) => l == r,
            // IO errors cannot be compared, but in the absence of any more
            // meaningful way to compare the errors we compare the kind of error
            // and ignore the embedded source error or OS error. The main use
            // case for comparing errors outputted by the XDR library is for
            // error case testing, and a lack of the ability to compare has a
            // detrimental affect on failure testing, so this is a tradeoff.
            #[cfg(feature = "std")]
            (Self::Io(l), Self::Io(r)) => l.kind() == r.kind(),
            _ => core::mem::discriminant(self) == core::mem::discriminant(other),
        }
    }
}

impl error::Error for Error {
    #[must_use]
    fn source(&self) -> Option<&(dyn error::Error + 'static)> {
        match self {
            Self::Io(e) => Some(e),
            _ => None,
        }
    }
}

impl fmt::Display for Error {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Error::Invalid => write!(f, "xdr value invalid"),
            Error::Unsupported => write!(f, "xdr value unsupported"),
            Error::LengthExceedsMax => write!(f, "xdr value max length exceeded"),
            Error::LengthMismatch => write!(f, "xdr value length does not match"),
            Error::NonZeroPadding => write!(f, "xdr padding contains non-zero bytes"),
            Error::Utf8Error(e) => write!(f, "{e}"),
            #[cfg(feature = "alloc")]
            Error::InvalidHex => write!(f, "hex invalid"),
            Error::Io(e) => write!(f, "{e}"),
            Error::StackOverflow => write!(f, "stack overflow"),
        }
    }
}

impl From<core::str::Utf8Error> for Error {
    #[must_use]
    fn from(e: core::str::Utf8Error) -> Self {
        Error::Utf8Error(e)
    }
}

#[cfg(feature = "alloc")]
impl From<FromUtf8Error> for Error {
    #[must_use]
    fn from(e: FromUtf8Error) -> Self {
        Error::Utf8Error(e.utf8_error())
    }
}

impl From<io::Error> for Error {
    #[must_use]
    fn from(e: io::Error) -> Self {
        Error::Io(e)
    }
}

impl From<Error> for () {
    fn from(_: Error) {}
}

pub struct ReadXdrIter<R: Read, S: ReadXdr> {
    reader: BufReader<R>,
    stack_limit: u32,
    _s: PhantomData<S>,
}

impl<R: Read, S: ReadXdr> ReadXdrIter<R, S> {
    fn new(r: R, stack_limit: u32) -> Self {
        Self {
            reader: BufReader::new(r),
            stack_limit,
            _s: PhantomData,
        }
    }
}

impl<R: Read, S: ReadXdr> Iterator for ReadXdrIter<R, S> {
    type Item = Result<S>;

    // Next reads the internal reader and XDR decodes it into the Self type. If
    // the EOF is reached without reading any new bytes `None` is returned. If
    // EOF is reached after reading some bytes a truncated entry is assumed an
    // an `Error::Io` containing an `UnexpectedEof`. If any other IO error
    // occurs it is returned. Iteration of this iterator stops naturally when
    // `None` is returned, but not when a `Some(Err(...))` is returned. The
    // caller is responsible for checking each Result.
    fn next(&mut self) -> Option<Self::Item> {
        // Try to fill the buffer to see if the EOF has been reached or not.
        // This happens to effectively peek to see if the stream has finished
        // and there are no more items.  It is necessary to do this because the
        // xdr types in this crate heavily use the `std::io::Read::read_exact`
        // method that doesn't distinguish between an EOF at the beginning of a
        // read and an EOF after a partial fill of a read_exact.
        match self.reader.fill_buf() {
            // If the reader has no more data and is unable to fill any new data
            // into its internal buf, then the EOF has been reached.
            Ok([]) => return None,
            // If an error occurs filling the buffer, treat that as an error and stop.
            Err(e) => return Some(Err(Error::Io(e))),
            // If there is data in the buf available for reading, continue.
            Ok([..]) => (),
        };
        // Read the buf into the type.
        match S::read_xdr(&mut self.reader, self.stack_limit) {
            Ok(s) => Some(Ok(s)),
            Err(e) => Some(Err(e)),
        }
    }
}

#[inline(always)]
fn subtract_stack_limit_maybe_error(mut stack_limit: u32) -> Result<u32> {
    stack_limit -= 1;
    if stack_limit == 0 {
        return Err(Error::StackOverflow);
    }
    Ok(stack_limit)
}

pub trait ReadXdr
where
    Self: Sized,
{
    /// Read the XDR and construct the type.
    ///
    /// Read bytes from the given read implementation, decoding the bytes as
    /// XDR, and construct the type implementing this interface from those
    /// bytes.
    ///
    /// Just enough bytes are read from the read implementation to construct the
    /// type. Any residual bytes remain in the read implementation.
    ///
    /// All implementations should continue if the read implementation returns
    /// [`ErrorKind::Interrupted`](std::io::ErrorKind::Interrupted).
    ///
    /// Use [`ReadXdr::read_xdr_to_end`] when the intent is for all bytes in the
    /// read implementation to be consumed by the read.

    fn read_xdr(r: &mut impl Read, stack_limit: u32) -> Result<Self>;

    /// Read the XDR and construct the type, and consider it an error if the
    /// read does not completely consume the read implementation.
    ///
    /// Read bytes from the given read implementation, decoding the bytes as
    /// XDR, and construct the type implementing this interface from those
    /// bytes.
    ///
    /// Just enough bytes are read from the read implementation to construct the
    /// type, and then confirm that no further bytes remain. To confirm no
    /// further bytes remain additional bytes are attempted to be read from the
    /// read implementation. If it is possible to read any residual bytes from
    /// the read implementation an error is returned. The read implementation
    /// may not be exhaustively read if there are residual bytes, and it is
    /// considered undefined how many residual bytes or how much of the residual
    /// buffer are consumed in this case.
    ///
    /// All implementations should continue if the read implementation returns
    /// [`ErrorKind::Interrupted`](std::io::ErrorKind::Interrupted).

    fn read_xdr_to_end(r: &mut impl Read, stack_limit: u32) -> Result<Self> {
        let stack_limit = subtract_stack_limit_maybe_error(stack_limit)?;

        let s = Self::read_xdr(r, stack_limit)?;
        // Check that any further reads, such as this read of one byte, read no
        // data, indicating EOF. If a byte is read the data is invalid.
        if r.read(&mut [0u8; 1])? == 0 {
            Ok(s)
        } else {
            Err(Error::Invalid)
        }
    }

    /// Read the XDR and construct the type.
    ///
    /// Read bytes from the given read implementation, decoding the bytes as
    /// XDR, and construct the type implementing this interface from those
    /// bytes.
    ///
    /// Just enough bytes are read from the read implementation to construct the
    /// type. Any residual bytes remain in the read implementation.
    ///
    /// All implementations should continue if the read implementation returns
    /// [`ErrorKind::Interrupted`](std::io::ErrorKind::Interrupted).
    ///
    /// Use [`ReadXdr::read_xdr_into_to_end`] when the intent is for all bytes
    /// in the read implementation to be consumed by the read.

    fn read_xdr_into(&mut self, r: &mut impl Read, stack_limit: u32) -> Result<()> {
        let stack_limit = subtract_stack_limit_maybe_error(stack_limit)?;
        *self = Self::read_xdr(r, stack_limit)?;
        Ok(())
    }

    /// Read the XDR into the existing value, and consider it an error if the
    /// read does not completely consume the read implementation.
    ///
    /// Read bytes from the given read implementation, decoding the bytes as
    /// XDR, and construct the type implementing this interface from those
    /// bytes.
    ///
    /// Just enough bytes are read from the read implementation to construct the
    /// type, and then confirm that no further bytes remain. To confirm no
    /// further bytes remain additional bytes are attempted to be read from the
    /// read implementation. If it is possible to read any residual bytes from
    /// the read implementation an error is returned. The read implementation
    /// may not be exhaustively read if there are residual bytes, and it is
    /// considered undefined how many residual bytes or how much of the residual
    /// buffer are consumed in this case.
    ///
    /// All implementations should continue if the read implementation returns
    /// [`ErrorKind::Interrupted`](std::io::ErrorKind::Interrupted).

    fn read_xdr_into_to_end(&mut self, r: &mut impl Read, stack_limit: u32) -> Result<()> {
        let stack_limit = subtract_stack_limit_maybe_error(stack_limit)?;
        Self::read_xdr_into(self, r, stack_limit)?;
        // Check that any further reads, such as this read of one byte, read no
        // data, indicating EOF. If a byte is read the data is invalid.
        if r.read(&mut [0u8; 1])? == 0 {
            Ok(())
        } else {
            Err(Error::Invalid)
        }
    }

    /// Create an iterator that reads the read implementation as a stream of
    /// values that are read into the implementing type.
    ///
    /// Read bytes from the given read implementation, decoding the bytes as
    /// XDR, and construct the type implementing this interface from those
    /// bytes.
    ///
    /// Just enough bytes are read from the read implementation to construct the
    /// type, and then confirm that no further bytes remain. To confirm no
    /// further bytes remain additional bytes are attempted to be read from the
    /// read implementation. If it is possible to read any residual bytes from
    /// the read implementation an error is returned. The read implementation
    /// may not be exhaustively read if there are residual bytes, and it is
    /// considered undefined how many residual bytes or how much of the residual
    /// buffer are consumed in this case.
    ///
    /// All implementations should continue if the read implementation returns
    /// [`ErrorKind::Interrupted`](std::io::ErrorKind::Interrupted).

    fn read_xdr_iter<R: Read>(r: &mut R, stack_limit: u32) -> ReadXdrIter<&mut R, Self> {
        ReadXdrIter::new(r, stack_limit)
    }

    /// Construct the type from the XDR bytes.
    ///
    /// An error is returned if the bytes are not completely consumed by the
    /// deserialization.

    fn from_xdr(bytes: impl AsRef<[u8]>, stack_limit: u32) -> Result<Self> {
        let stack_limit = subtract_stack_limit_maybe_error(stack_limit)?;
        let mut cursor = Cursor::new(bytes.as_ref());
        let t = Self::read_xdr_to_end(&mut cursor, stack_limit)?;
        Ok(t)
    }
}

pub trait WriteXdr {
    fn write_xdr(&self, w: &mut impl Write, stack_limit: u32) -> Result<()>;

    fn to_xdr(&self, stack_limit: u32) -> Result<Vec<u8>> {
        let stack_limit = subtract_stack_limit_maybe_error(stack_limit)?;
        let mut cursor = Cursor::new(vec![]);
        self.write_xdr(&mut cursor, stack_limit)?;
        let bytes = cursor.into_inner();
        Ok(bytes)
    }
}

impl ReadXdr for u32 {
    fn read_xdr(r: &mut impl Read, stack_limit: u32) -> Result<Self> {
        let _ = subtract_stack_limit_maybe_error(stack_limit)?;
        let mut b = [0u8; 4];
        r.read_exact(&mut b)?;
        let i = u32::from_be_bytes(b);
        Ok(i)
    }
}

impl WriteXdr for u32 {
    fn write_xdr(&self, w: &mut impl Write, stack_limit: u32) -> Result<()> {
        let _ = subtract_stack_limit_maybe_error(stack_limit)?;
        let b: [u8; 4] = self.to_be_bytes();
        w.write_all(&b)?;
        Ok(())
    }
}

impl<T: ReadXdr> ReadXdr for Option<T> {
    fn read_xdr(r: &mut impl Read, stack_limit: u32) -> Result<Self> {
        let stack_limit = subtract_stack_limit_maybe_error(stack_limit)?;
        let i = u32::read_xdr(r, stack_limit)?;
        match i {
            0 => Ok(None),
            1 => {
                let t = T::read_xdr(r, stack_limit)?;
                Ok(Some(t))
            }
            _ => Err(Error::Invalid),
        }
    }
}

impl<T: WriteXdr> WriteXdr for Option<T> {
    fn write_xdr(&self, w: &mut impl Write, stack_limit: u32) -> Result<()> {
        let stack_limit = subtract_stack_limit_maybe_error(stack_limit)?;
        if let Some(t) = self {
            1u32.write_xdr(w, stack_limit)?;
            t.write_xdr(w, stack_limit)?;
        } else {
            0u32.write_xdr(w, stack_limit)?;
        }
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn it_works() {
        let stack_limit = 5;
        let a: Option<Option<Option<u32>>> = Some(Some(Some(5)));
        let mut buf = Vec::new();
        a.write_xdr(&mut buf, stack_limit).unwrap();
        println!("{:?}", buf)
    }

    #[should_panic]
    #[test]
    fn stack_overflow() {
        let stack_limit = 2;
        let a: Option<Option<Option<u32>>> = Some(Some(Some(5)));
        let mut buf = Vec::new();
        a.write_xdr(&mut buf, stack_limit).unwrap();
        println!("{:?}", buf)
    }
}
