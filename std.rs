// This file is injected to source code by Thrust

#[thrust::extern_spec_fn]
#[thrust::requires(true)]
#[thrust::ensures(result == <x>)]
fn _extern_spec_box_new<T>(x: T) -> Box<T> {
    Box::new(x)
}

#[thrust::extern_spec_fn]
#[thrust::requires(true)]
#[thrust::ensures(*x == ^y && *y == ^x)]
fn _extern_spec_std_mem_swap<T>(x: &mut T, y: &mut T) {
    std::mem::swap(x, y);
}
