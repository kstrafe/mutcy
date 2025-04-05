use mutcy::Key;

#[test]
#[should_panic]
fn key_uniqueness() {
    let _key1 = Key::acquire();
    let _key2 = Key::acquire();
}

#[test]
fn key_acquire_after_drop() {
    let key1 = Key::acquire();
    drop(key1);
    let _ = Key::acquire();
}

#[test]
fn key_per_thread() {
    let _key_1 = Key::acquire();

    for _ in 0..100 {
        let thread = std::thread::spawn(|| {
            let _key_n = Key::acquire();
        });

        thread.join().unwrap();
    }
}
