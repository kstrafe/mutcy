use crate::{IntoWeak, Key, Meta, Rw};
use std::rc::Rc;

#[cfg(test)]
mod tests;

type Handler<I, O> = Rc<dyn Fn(&mut Key, I) -> Option<O>>;
pub struct Callback<I, O>(Handler<I, O>);

impl<I, O> Callback<I, O> {
    pub fn new<W, T, F>(receiver: &W, handler: F) -> Self
    where
        W: IntoWeak<T>,
        T: Meta + 'static,
        F: Fn(Rw<T>, I) -> O + 'static,
    {
        let receiver = receiver.into();
        Self(Rc::new(move |key, input| {
            receiver.upgrade().map(|x| (handler)(&mut x.rw(key), input))
        }))
    }

    pub fn call(&self, key: &mut Key, input: I) -> Option<O> {
        (self.0)(key, input)
    }
}
