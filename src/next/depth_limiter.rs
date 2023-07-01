use super::{Error, Result};
use std::io::{Read, Write};

pub trait DepthLimiter {
    fn enter(&mut self) -> Result<()>;
    fn leave(&mut self);
    fn with_limited_depth<T, F>(&mut self, f: F) -> Result<T>
    where
        F: FnOnce(&mut Self) -> Result<T>,
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
    pub fn new(d: &'a mut D) -> Result<Self> {
        d.enter()?;
        Ok(Self(d))
    }
}

impl<'a, D: DepthLimiter> Drop for DepthGuard<'a, D> {
    fn drop(&mut self) {
        self.0.leave()
    }
}

pub(crate) struct DepthLimitedRead<R: Read> {
    pub(crate) inner: R,
    depth: u32,
}

impl<R: Read> DepthLimitedRead<R> {
    pub(crate) fn new(inner: R, depth: u32) -> Self {
        DepthLimitedRead { inner, depth }
    }
}

impl<R: Read> DepthLimiter for DepthLimitedRead<R> {
    fn enter(&mut self) -> Result<()> {
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

impl<R: Read> Read for DepthLimitedRead<R> {
    fn read(&mut self, buf: &mut [u8]) -> std::io::Result<usize> {
        self.inner.read(buf)
    }
}

pub(crate) struct DepthLimitedWrite<W: Write> {
    pub(crate) inner: W,
    depth: u32,
}

impl<W: Write> DepthLimitedWrite<W> {
    pub(crate) fn new(inner: W, depth: u32) -> Self {
        DepthLimitedWrite { inner, depth }
    }
}

impl<W: Write> DepthLimiter for DepthLimitedWrite<W> {
    fn enter(&mut self) -> Result<()> {
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

impl<W: Write> Write for DepthLimitedWrite<W> {
    fn write(&mut self, buf: &[u8]) -> std::io::Result<usize> {
        self.inner.write(buf)
    }

    fn flush(&mut self) -> std::io::Result<()> {
        self.inner.flush()
    }
}
