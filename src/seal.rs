use crate::AssocInner;
use std::rc::Rc;

pub trait Sealed {
    #[allow(private_interfaces)]
    fn assoc(&self) -> &Rc<AssocInner>;
}
