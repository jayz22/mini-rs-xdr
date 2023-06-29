use core::cell::RefCell;
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
    Io(io::Error),
    StackOverflow,
}

impl PartialEq for Error {
    fn eq(&self, other: &Self) -> bool {
        match (self, other) {
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
            Error::Io(e) => write!(f, "{e}"),
            Error::StackOverflow => write!(f, "stack overflow"),
        }
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

// The `DLR` part is the original buffer type passed into the ReadXdr type.
pub struct ReadXdrIter<R: Read, S: ReadXdr> {
    reader: DepthLimitedRead<BufReader<R>>,
    _s: PhantomData<S>,
}

impl<R: Read, S: ReadXdr> ReadXdrIter<R, S> {
    fn new(r: R, depth_limit: u32) -> Self {
        Self {
            reader: DepthLimitedRead::new(BufReader::new(r), depth_limit),
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
        match self.reader.inner.fill_buf() {
            // If the reader has no more data and is unable to fill any new data
            // into its internal buf, then the EOF has been reached.
            Ok([]) => return None,
            // If an error occurs filling the buffer, treat that as an error and stop.
            Err(e) => return Some(Err(Error::Io(e))),
            // If there is data in the buf available for reading, continue.
            Ok([..]) => (),
        };
        // Read the buf into the type.
        let dg = match DepthGuard::new(&mut self.reader) {
            Ok(dg) => dg,
            Err(e) => return Some(Err(e)),
        };
        match S::read_xdr(&mut self.reader) {
            Ok(s) => Some(Ok(s)),
            Err(e) => Some(Err(e)),
        }
    }
}

pub trait DepthLimiter {
    fn enter(&self) -> Result<()>;
    fn leave(&self);
}

struct DepthGuard<'a, D: DepthLimiter>(&'a D);

impl<'a, D: DepthLimiter> DepthGuard<'a, D> {
    fn new(d: &'a D) -> Result<Self> {
        d.enter()?;
        Ok(Self(d))
    }
}

impl<'a, D: DepthLimiter> Drop for DepthGuard<'a, D> {
    fn drop(&mut self) {
        self.0.leave()
    }
}

struct DepthLimitedRead<R: Read> {
    inner: R,
    depth: RefCell<u32>,
}

impl<R: Read> DepthLimitedRead<R> {
    fn new(inner: R, depth: u32) -> Self {
        DepthLimitedRead {
            inner,
            depth: RefCell::new(depth),
        }
    }
}

impl<R: Read> DepthLimiter for DepthLimitedRead<R> {
    fn enter(&self) -> Result<()> {
        let depth = *self.depth.borrow();
        if depth == 0 {
            return Err(Error::StackOverflow);
        }
        self.depth.replace(depth - 1);
        Ok(())
    }

    fn leave(&self) {
        let depth = *self.depth.borrow();
        self.depth.replace(depth.saturating_add(1));
    }
}

impl<R: Read> Read for DepthLimitedRead<R> {
    fn read(&mut self, buf: &mut [u8]) -> io::Result<usize> {
        self.inner.read(buf)
    }
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

    fn read_xdr<DLR: DepthLimiter + Read>(r: &mut DLR) -> Result<Self>;

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

    fn read_xdr_to_end<DLR: DepthLimiter + Read>(r: &mut DLR) -> Result<Self> {
        let s = Self::read_xdr(r)?;
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

    fn read_xdr_into<DLR: DepthLimiter + Read>(&mut self, r: &mut DLR) -> Result<()> {
        *self = Self::read_xdr(r)?;
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

    fn read_xdr_into_to_end<DLR: DepthLimiter + Read>(&mut self, r: &mut DLR) -> Result<()> {
        Self::read_xdr_into(self, r)?;
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

    fn read_xdr_iter<R: Read>(r: &mut R, depth_limit: u32) -> ReadXdrIter<&mut R, Self> {
        ReadXdrIter::new(r, depth_limit)
    }

    /// Construct the type from the XDR bytes.
    ///
    /// An error is returned if the bytes are not completely consumed by the
    /// deserialization.

    fn from_xdr(bytes: impl AsRef<[u8]>, depth_limit: u32) -> Result<Self> {
        let mut cursor = DepthLimitedRead::new(Cursor::new(bytes.as_ref()), depth_limit);
        let t = Self::read_xdr_to_end(&mut cursor)?;
        Ok(t)
    }
}

pub trait WriteXdr {
    fn write_xdr(&self, w: &mut impl Write) -> Result<()>;

    fn to_xdr(&self) -> Result<Vec<u8>> {
        let mut cursor = Cursor::new(vec![]);
        self.write_xdr(&mut cursor)?;
        let bytes = cursor.into_inner();
        Ok(bytes)
    }
}

impl ReadXdr for u32 {
    fn read_xdr<DLR: DepthLimiter + Read>(r: &mut DLR) -> Result<Self> {
        let dg = DepthGuard::new(r)?;
        let mut b = [0u8; 4];
        r.read_exact(&mut b)?;
        let i = u32::from_be_bytes(b);
        Ok(i)
    }
}

impl WriteXdr for u32 {
    fn write_xdr(&self, w: &mut impl Write) -> Result<()> {
        let b: [u8; 4] = self.to_be_bytes();
        w.write_all(&b)?;
        Ok(())
    }
}

impl<T: ReadXdr> ReadXdr for Option<T> {
    fn read_xdr<DLR: DepthLimiter + Read>(r: &mut DLR) -> Result<Self> {
        let dg = DepthGuard::new(r)?;
        let i = u32::read_xdr(r)?;
        match i {
            0 => Ok(None),
            1 => {
                let t = T::read_xdr(r)?;
                Ok(Some(t))
            }
            _ => Err(Error::Invalid),
        }
    }
}

impl<T: WriteXdr> WriteXdr for Option<T> {
    fn write_xdr(&self, w: &mut impl Write) -> Result<()> {
        if let Some(t) = self {
            1u32.write_xdr(w)?;
            t.write_xdr(w)?;
        } else {
            0u32.write_xdr(w)?;
        }
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn it_works() {
        let a: Option<Option<Option<u32>>> = Some(Some(Some(5)));
        let mut buf = Vec::new();
        a.write_xdr(&mut buf).unwrap();

        let mut dlr = DepthLimitedRead::new(Cursor::new(buf.as_slice()), 1);
        let a_back: Option<Option<Option<u32>>> = ReadXdr::read_xdr(&mut dlr).unwrap();
        assert_eq!(a, a_back);
    }
}
