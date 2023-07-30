use std::rc::Rc;

/// Insert `value` into `vec`, and make it sorted.
///
/// # NOTE
/// `vec` should not contain `value` or this function will panic.
pub(crate) fn insert_into_vec<T: Ord>(vec: &mut Vec<Rc<T>>, value: T) {
    let value = Rc::new(value);

    let idx = vec
        .binary_search(&value)
        .expect_err("`vec` should not contain `value`");

    vec.insert(idx, value);
}
