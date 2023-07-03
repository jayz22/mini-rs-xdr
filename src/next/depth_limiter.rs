use super::Error;
#[cfg(feature = "std")]
use std::io::{Read, Write};

pub trait DepthLimiter {
    fn enter(&mut self) -> Result<(), Error>;
    fn leave(&mut self);
    fn with_limited_depth<T, F>(&mut self, f: F) -> Result<T, Error>
    where
        F: FnOnce(&mut Self) -> Result<T, Error>,
    {
        self.enter()?;
        let res = f(self)?;
        self.leave();
        Ok(res)
    }
}

pub struct DepthGuard<'a, D: DepthLimiter>(&'a mut D);

impl<'a, D: DepthLimiter> DepthGuard<'a, D> {
    #[allow(unused)]
    pub fn new(d: &'a mut D) -> Result<Self, Error> {
        d.enter()?;
        Ok(Self(d))
    }
}

impl<'a, D: DepthLimiter> Drop for DepthGuard<'a, D> {
    fn drop(&mut self) {
        self.0.leave()
    }
}

#[cfg(feature = "std")]
pub(crate) struct DepthLimitedRead<R: Read> {
    pub(crate) inner: R,
    depth: u32,
}

#[cfg(feature = "std")]
impl<R: Read> DepthLimitedRead<R> {
    pub(crate) fn new(inner: R, depth: u32) -> Self {
        DepthLimitedRead { inner, depth }
    }
}

#[cfg(feature = "std")]
impl<R: Read> DepthLimiter for DepthLimitedRead<R> {
    fn enter(&mut self) -> Result<(), Error> {
        if self.depth == 0 {
            return Err(Error::StackOverflow);
        }
        self.depth -= 1;
        Ok(())
    }

    fn leave(&mut self) {
        self.depth = self.depth.saturating_add(1);
    }
}

#[cfg(feature = "std")]
impl<R: Read> Read for DepthLimitedRead<R> {
    fn read(&mut self, buf: &mut [u8]) -> std::io::Result<usize> {
        self.inner.read(buf)
    }
}

#[cfg(feature = "std")]
pub(crate) struct DepthLimitedWrite<W: Write> {
    pub(crate) inner: W,
    depth: u32,
}

#[cfg(feature = "std")]
impl<W: Write> DepthLimitedWrite<W> {
    pub(crate) fn new(inner: W, depth: u32) -> Self {
        DepthLimitedWrite { inner, depth }
    }
}

#[cfg(feature = "std")]
impl<W: Write> DepthLimiter for DepthLimitedWrite<W> {
    fn enter(&mut self) -> Result<(), Error> {
        if self.depth == 0 {
            return Err(Error::StackOverflow);
        }
        self.depth -= 1;
        Ok(())
    }

    fn leave(&mut self) {
        self.depth = self.depth.saturating_add(1);
    }
}

#[cfg(feature = "std")]
impl<W: Write> Write for DepthLimitedWrite<W> {
    fn write(&mut self, buf: &[u8]) -> std::io::Result<usize> {
        self.inner.write(buf)
    }

    fn flush(&mut self) -> std::io::Result<()> {
        self.inner.flush()
    }
}
