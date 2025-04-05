use crate::{Associated, Sealed};
use std::rc::Rc;

// While this type is a ZST, `Rc` allocates its strong/weak count inside the
// allocation, meaning that we will get `!Rc::ptr_eq` for two allocations.
pub(crate) struct AssocInner;

#[doc(hidden)]
impl Associated for Rc<AssocInner> {}

#[allow(private_interfaces)]
impl Sealed for Rc<AssocInner> {
    fn assoc(&self) -> &Rc<AssocInner> {
        self
    }
}

#[test]
fn assoc_inner_rc_different() {
    assert!(!Rc::ptr_eq(&Rc::new(AssocInner), &Rc::new(AssocInner)));
    assert_eq!(
        &raw const *Box::new(AssocInner),
        &raw const *Box::new(AssocInner)
    );
}
