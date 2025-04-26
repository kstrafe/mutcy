use super::{Callback, Key, Rc};
use crate::KeyCell;

#[test]
fn callback() {
    let key = &mut Key::acquire();
    let item = Rc::new(KeyCell::new(1, ()));

    let callback = Callback::new(&item, |this, input: i32| **this + input);

    assert_eq!(Some(2), callback.call(key, 1));
    assert_eq!(Some(3), callback.call(key, 2));

    drop(item);

    assert_eq!(None, callback.call(key, 0));
}
