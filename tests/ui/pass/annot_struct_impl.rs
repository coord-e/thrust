//@check-pass

struct VecWrap<T> {
    inner: Vec<T>
}

impl<T> thrust_models::Model for VecWrap<T> where T: thrust_models::Model {
  type Ty = (
      thrust_models::model::Array<
          thrust_models::model::Int,
          <T as thrust_models::Model>::Ty
      >,
      thrust_models::model::Int,
  );
}

#[thrust_macros::context]
impl<T> VecWrap<T> {
  #[thrust::trusted]
  #[thrust_macros::ensures(result.1 == 0)]
  fn new() -> Self {
      VecWrap { inner: Vec::new() }
  }

  #[thrust::trusted]
  #[thrust_macros::ensures((!self).0 == (*self).0.store((*self).1, elem))]
  #[thrust_macros::ensures((!self).1 == (*self).1 + 1)]
  fn push(&mut self, elem: T) {
      self.inner.push(elem);
  }

  #[thrust::trusted]
  #[thrust_macros::ensures(result == (*self).1)]
  fn len(&self) -> usize {
      self.inner.len()
  }

  #[thrust::trusted]
  #[thrust_macros::requires(index < (*self).1)]
  #[thrust_macros::ensures(*result == (*self).0[index])]
  fn get(&self, index: usize) -> &T {
      &self.inner[index]
  }
}

fn main() {
    let mut v = VecWrap::new();
    v.push(10);
    v.push(20);
    assert!(v.len() == 2);
    assert!(*v.get(0) == 10);
    assert!(*v.get(1) == 20);
}
