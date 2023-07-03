// use super::Error;
#[cfg(feature = "std")]
use core::cell::RefCell;
#[cfg(feature = "std")]
use std::io::{Read, Write};

pub trait DepthLimiter {
    type Error;

    fn enter(&self) -> Result<(), Self::Error>;

    fn leave(&self);

    fn with_limited_depth<T, F>(&mut self, f: F) -> Result<T, Self::Error>
    where
        F: FnOnce(&mut Self) -> Result<T, Self::Error>,
    {
        self.enter()?;
        let res = f(self)?;
        self.leave();
        Ok(res)
    }
}

pub struct DepthGuard<'a, D: DepthLimiter>(&'a D);

impl<'a, D: DepthLimiter> DepthGuard<'a, D> {
    #[allow(unused)]
    pub fn new(d: &'a D) -> Result<Self, D::Error> {
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
    depth: RefCell<u32>,
}

#[cfg(feature = "std")]
impl<R: Read> DepthLimitedRead<R> {
    pub(crate) fn new(inner: R, depth: u32) -> Self {
        DepthLimitedRead {
            inner,
            depth: RefCell::new(depth),
        }
    }
}

#[cfg(feature = "std")]
impl<R: Read> DepthLimiter for DepthLimitedRead<R> {
    type Error = super::Error;

    fn enter(&self) -> Result<(), Self::Error> {
        let depth = *self.depth.borrow();
        if depth == 0 {
            return Err(Self::Error::StackOverflow);
        }
        self.depth.replace(depth - 1);
        Ok(())
    }

    fn leave(&self) {
        let depth = *self.depth.borrow();
        self.depth.replace(depth.saturating_add(1));
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
    depth: RefCell<u32>,
}

#[cfg(feature = "std")]
impl<W: Write> DepthLimitedWrite<W> {
    pub(crate) fn new(inner: W, depth: u32) -> Self {
        DepthLimitedWrite {
            inner,
            depth: RefCell::new(depth),
        }
    }
}

#[cfg(feature = "std")]
impl<W: Write> DepthLimiter for DepthLimitedWrite<W> {
    type Error = super::Error;

    fn enter(&self) -> Result<(), Self::Error> {
        let depth = *self.depth.borrow();
        if depth == 0 {
            return Err(Self::Error::StackOverflow);
        }
        self.depth.replace(depth - 1);
        Ok(())
    }

    fn leave(&self) {
        let depth = *self.depth.borrow();
        self.depth.replace(depth.saturating_add(1));
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
