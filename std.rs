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

#[thrust::extern_spec_fn]
#[thrust::requires(opt != std::option::Option::<T0>::None())]
#[thrust::ensures(std::option::Option::<T0>::Some(result) == opt)]
fn _extern_spec_option_unwrap<T>(opt: Option<T>) -> T {
    Option::unwrap(opt)
}

#[thrust::extern_spec_fn]
#[thrust::requires(exists x:T0. res == std::result::Result::<T0, T1>::Ok(x))]
#[thrust::ensures(std::result::Result::<T0, T1>::Ok(result) == res)]
fn _extern_spec_result_unwrap<T, E: std::fmt::Debug>(res: Result<T, E>) -> T {
    Result::unwrap(res)
}
