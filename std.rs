// This file is injected to source code by Thrust

mod thrust_models {
    pub trait Model {
        #[thrust::def::model_ty]
        type Ty;
    }

    pub mod model {
        use std::marker::PhantomData;

        #[thrust::def::int_model]
        pub struct Int;

        #[thrust::def::mut_model]
        pub struct Mut<T>(PhantomData<T>);

        #[thrust::def::box_model]
        pub struct Box<T>(PhantomData<T>);

        #[thrust::def::array_model]
        pub struct Array<I, T>(PhantomData<I>, PhantomData<T>);

        pub struct Vec<T>(pub Array<Int, T>, pub usize);
    }

    impl Model for isize {
        type Ty = model::Int;
    }

    impl Model for i32 {
        type Ty = model::Int;
    }

    impl Model for i64 {
        type Ty = model::Int;
    }

    impl Model for usize {
        type Ty = model::Int;
    }

    impl Model for u32 {
        type Ty = model::Int;
    }

    impl Model for u64 {
        type Ty = model::Int;
    }

    impl Model for bool {
        type Ty = bool;
    }

    impl Model for () {
        type Ty = ();
    }

    impl<T0> Model for (T0,) where T0: Model {
        type Ty = (<T0 as Model>::Ty,);
    }

    impl<T0, T1> Model for (T0, T1) where T0: Model, T1: Model {
        type Ty = (<T0 as Model>::Ty, <T1 as Model>::Ty);
    }

    impl<T0, T1, T2> Model for (T0, T1, T2) where T0: Model, T1: Model, T2: Model {
        type Ty = (<T0 as Model>::Ty, <T1 as Model>::Ty, <T2 as Model>::Ty);
    }

    impl<'a, T> Model for &'a mut T where T: Model {
        type Ty = model::Mut<<T as Model>::Ty>;
    }

    impl<'a, T> Model for &'a T where T: Model {
        type Ty = &'a <T as Model>::Ty;
    }

    impl<T> Model for Box<T> where T: Model {
        type Ty = model::Box<<T as Model>::Ty>;
    }

    impl<T> Model for Vec<T> where T: Model {
        type Ty = model::Vec<<T as Model>::Ty>;
    }

    impl<T> Model for Option<T> where T: Model {
        type Ty = Option<<T as Model>::Ty>;
    }

    impl<T, E> Model for Result<T, E> where T: Model, E: Model {
        type Ty = Result<<T as Model>::Ty, <E as Model>::Ty>;
    }
}

#[thrust::extern_spec_fn]
#[thrust::requires(true)]
#[thrust::ensures(result == <x>)]
fn _extern_spec_box_new<T>(x: T) -> Box<T> where T: thrust_models::Model {
    Box::new(x)
}

#[thrust::extern_spec_fn]
#[thrust::requires(true)]
#[thrust::ensures(*x == ^y && *y == ^x)]
fn _extern_spec_std_mem_swap<T>(x: &mut T, y: &mut T) where T: thrust_models::Model {
    std::mem::swap(x, y);
}

#[thrust::extern_spec_fn]
#[thrust::requires(true)]
#[thrust::ensures(^dest == src && result == *dest)]
fn _extern_spec_std_mem_replace<T>(dest: &mut T, src: T) -> T where T: thrust_models::Model {
    std::mem::replace(dest, src)
}

#[thrust::extern_spec_fn]
#[thrust::requires(opt != std::option::Option::<T0>::None())]
#[thrust::ensures(std::option::Option::<T0>::Some(result) == opt)]
fn _extern_spec_option_unwrap<T>(opt: Option<T>) -> T where T: thrust_models::Model {
    Option::unwrap(opt)
}

#[thrust::extern_spec_fn]
#[thrust::requires(true)]
#[thrust::ensures(
    (*opt == std::option::Option::<T0>::None() && result == true)
    || (*opt != std::option::Option::<T0>::None() && result == false)
)]
fn _extern_spec_option_is_none<T>(opt: &Option<T>) -> bool where T: thrust_models::Model {
    Option::is_none(opt)
}

#[thrust::extern_spec_fn]
#[thrust::requires(true)]
#[thrust::ensures(
    (*opt == std::option::Option::<T0>::None() && result == false)
    || (*opt != std::option::Option::<T0>::None() && result == true)
)]
fn _extern_spec_option_is_some<T>(opt: &Option<T>) -> bool where T: thrust_models::Model {
    Option::is_some(opt)
}

#[thrust::extern_spec_fn]
#[thrust::requires(true)]
#[thrust::ensures(
    (opt != std::option::Option::<T0>::None() && std::option::Option::<T0>::Some(result) == opt)
    || (opt == std::option::Option::<T0>::None() && result == default)
)]
fn _extern_spec_option_unwrap_or<T>(opt: Option<T>, default: T) -> T where T: thrust_models::Model {
    Option::unwrap_or(opt, default)
}

#[thrust::extern_spec_fn]
#[thrust::requires(true)]
#[thrust::ensures(
    (exists x:T0. opt == std::option::Option::<T0>::Some(x) && result == std::result::Result::<T0, T1>::Ok(x))
    || (opt == std::option::Option::<T0>::None() && result == std::result::Result::<T0, T1>::Err(err))
)]
fn _extern_spec_option_ok_or<T, E>(opt: Option<T>, err: E) -> Result<T, E> where T: thrust_models::Model, E: thrust_models::Model {
    Option::ok_or(opt, err)
}

#[thrust::extern_spec_fn]
#[thrust::requires(true)]
#[thrust::ensures(^opt == std::option::Option::<T0>::None() && result == *opt)]
fn _extern_spec_option_take<T>(opt: &mut Option<T>) -> Option<T> where T: thrust_models::Model {
    Option::take(opt)
}

#[thrust::extern_spec_fn]
#[thrust::requires(true)]
#[thrust::ensures(^opt == std::option::Option::<T0>::Some(src) && result == *opt)]
fn _extern_spec_option_replace<T>(opt: &mut Option<T>, src: T) -> Option<T> where T: thrust_models::Model {
    Option::replace(opt, src)
}

#[thrust::extern_spec_fn]
#[thrust::requires(true)]
#[thrust::ensures(
    (exists x:T0. opt == <std::option::Option::<T0>::Some(x)> && result == std::option::Option::<&T0>::Some(<x>))
    || (opt == <std::option::Option::<T0>::None()> && result == std::option::Option::<&T0>::None())
)]
fn _extern_spec_option_as_ref<T>(opt: &Option<T>) -> Option<&T> where T: thrust_models::Model {
    Option::as_ref(opt)
}

#[thrust::extern_spec_fn]
#[thrust::requires(true)]
#[thrust::ensures(
    (exists x1:T0, x2:T0.
      *opt == std::option::Option::<T0>::Some(x1) &&
      ^opt == std::option::Option::<T0>::Some(x2) &&
      result == std::option::Option::<&mut T0>::Some(<x1, x2>)
    )
    || (
      *opt == std::option::Option::<T0>::None() &&
      ^opt == std::option::Option::<T0>::None() &&
      result == std::option::Option::<&mut T0>::None()
    )
)]
fn _extern_spec_option_as_mut<T>(opt: &mut Option<T>) -> Option<&mut T> where T: thrust_models::Model {
    Option::as_mut(opt)
}

#[thrust::extern_spec_fn]
#[thrust::requires(exists x:T0. res == std::result::Result::<T0, T1>::Ok(x))]
#[thrust::ensures(std::result::Result::<T0, T1>::Ok(result) == res)]
fn _extern_spec_result_unwrap<T, E: std::fmt::Debug>(res: Result<T, E>) -> T where T: thrust_models::Model {
    Result::unwrap(res)
}

#[thrust::extern_spec_fn]
#[thrust::requires(exists x:T1. res == std::result::Result::<T0, T1>::Err(x))]
#[thrust::ensures(std::result::Result::<T0, T1>::Err(result) == res)]
fn _extern_spec_result_unwrap_err<T: std::fmt::Debug, E>(res: Result<T, E>) -> E where T: thrust_models::Model, E: thrust_models::Model {
    Result::unwrap_err(res)
}

#[thrust::extern_spec_fn]
#[thrust::requires(true)]
#[thrust::ensures(
    (exists x:T0. res == std::result::Result::<T0, T1>::Ok(x) && result == std::option::Option::<T0>::Some(x))
    || (exists x:T1. res == std::result::Result::<T0, T1>::Err(x) && result == std::option::Option::<T0>::None())
)]
fn _extern_spec_result_ok<T, E>(res: Result<T, E>) -> Option<T> where T: thrust_models::Model, E: thrust_models::Model {
    Result::ok(res)
}

#[thrust::extern_spec_fn]
#[thrust::requires(true)]
#[thrust::ensures(
    (exists x:T0. res == std::result::Result::<T0, T1>::Ok(x) && result == std::option::Option::<T1>::None())
    || (exists x:T1. res == std::result::Result::<T0, T1>::Err(x) && result == std::option::Option::<T1>::Some(x))
)]
fn _extern_spec_result_err<T, E>(res: Result<T, E>) -> Option<E> where T: thrust_models::Model, E: thrust_models::Model {
    Result::err(res)
}

#[thrust::extern_spec_fn]
#[thrust::requires(true)]
#[thrust::ensures(
    (exists x:T0. *res == std::result::Result::<T0, T1>::Ok(x) && result == true)
    || (exists x:T1. *res == std::result::Result::<T0, T1>::Err(x) && result == false)
)]
fn _extern_spec_result_is_ok<T, E>(res: &Result<T, E>) -> bool where T: thrust_models::Model, E: thrust_models::Model {
    Result::is_ok(res)
}

#[thrust::extern_spec_fn]
#[thrust::requires(true)]
#[thrust::ensures(
    (exists x:T0. *res == std::result::Result::<T0, T1>::Ok(x) && result == false)
    || (exists x:T1. *res == std::result::Result::<T0, T1>::Err(x) && result == true)
)]
fn _extern_spec_result_is_err<T, E>(res: &Result<T, E>) -> bool where T: thrust_models::Model, E: thrust_models::Model {
    Result::is_err(res)
}

#[thrust::extern_spec_fn]
#[thrust::requires(true)] // TODO: require x != i32::MIN
#[thrust::ensures(result >= 0 && (result == x || result == -x))]
fn _extern_spec_i32_abs(x: i32) -> i32 {
    i32::abs(x)
}

#[thrust::extern_spec_fn]
#[thrust::requires(true)]
#[thrust::ensures(
    (x >= y && result == (x - y))
    || (x < y && result == (y - x))
)]
fn _extern_spec_i32_abs_diff(x: i32, y: i32) -> u32 {
    i32::abs_diff(x, y)
}

#[thrust::extern_spec_fn]
#[thrust::requires(true)]
#[thrust::ensures((x == 0 && result == 0) || (x > 0 && result == 1) || (x < 0 && result == -1))]
fn _extern_spec_i32_signum(x: i32) -> i32 {
    i32::signum(x)
}

#[thrust::extern_spec_fn]
#[thrust::requires(true)]
#[thrust::ensures((x < 0 && result == false) || (x >= 0 && result == true))]
fn _extern_spec_i32_is_positive(x: i32) -> bool {
    i32::is_positive(x)
}

#[thrust::extern_spec_fn]
#[thrust::requires(true)]
#[thrust::ensures((x <= 0 && result == true) || (x > 0 && result == false))]
fn _extern_spec_i32_is_negative(x: i32) -> bool {
    i32::is_negative(x)
}

#[thrust::extern_spec_fn]
#[thrust::requires(true)]
#[thrust::ensures(*result.1 == 0)]
fn _extern_spec_vec_new<T>() -> Vec<T> where T: thrust_models::Model {
    Vec::<T>::new()
}

#[thrust::extern_spec_fn]
#[thrust::requires(true)]
#[thrust::ensures(^vec == ((*(*vec).0).store(*(*vec).1, elem), *(*vec).1 + 1))]
fn _extern_spec_vec_push<T>(vec: &mut Vec<T>, elem: T) where T: thrust_models::Model {
    Vec::push(vec, elem)
}

#[thrust::extern_spec_fn]
#[thrust::requires(true)]
#[thrust::ensures(result == *(*vec).1)]
fn _extern_spec_vec_len<T>(vec: &Vec<T>) -> usize where T: thrust_models::Model {
    Vec::len(vec)
}

#[thrust::extern_spec_fn]
#[thrust::requires(index < *(*vec).1)]
#[thrust::ensures(*result == (*(*vec).0).select(index))]
fn _extern_spec_vec_index<T>(vec: &Vec<T>, index: usize) -> &T where T: thrust_models::Model {
    <Vec<T> as std::ops::Index<usize>>::index(vec, index)
}

#[thrust::extern_spec_fn]
#[thrust::requires(index < *(*vec).1)]
#[thrust::ensures(
    *result == (*(*vec).0).select(index) &&
    ^result == (*(^vec).0).select(index) &&
    ^vec == (<(*(*vec).0).store(index, ^result)>, (*vec).1)
)]
fn _extern_spec_vec_index_mut<T>(vec: &mut Vec<T>, index: usize) -> &mut T where T: thrust_models::Model {
    <Vec<T> as std::ops::IndexMut<usize>>::index_mut(vec, index)
}

#[thrust::extern_spec_fn]
#[thrust::requires(true)]
#[thrust::ensures(*(^vec).1 == 0)]
fn _extern_spec_vec_clear<T>(vec: &mut Vec<T>) where T: thrust_models::Model {
    Vec::clear(vec)
}

#[thrust::extern_spec_fn]
#[thrust::requires(true)]
#[thrust::ensures(
    (^vec).0 == (*vec).0 && (
        (
            *(*vec).1 > 0 &&
            *(^vec).1 == *(*vec).1 - 1 &&
            result == std::option::Option::<T0>::Some((*(*vec).0).select(*(*vec).1 - 1))
        ) || (
            *(*vec).1 == 0 &&
            *(^vec).1 == 0 &&
            result == std::option::Option::<T0>::None()
        )
    )
)]
fn _extern_spec_vec_pop<T>(vec: &mut Vec<T>) -> Option<T> where T: thrust_models::Model {
    Vec::pop(vec)
}

#[thrust::extern_spec_fn]
#[thrust::requires(true)]
#[thrust::ensures(result == (*(*vec).1 == 0))]
fn _extern_spec_vec_is_empty<T>(vec: &Vec<T>) -> bool where T: thrust_models::Model {
    Vec::is_empty(vec)
}

#[thrust::extern_spec_fn]
#[thrust::requires(true)]
#[thrust::ensures(
    (
        *(*vec).1 > len &&
        ^vec == (<(*vec).0>, <len>)
    ) || (
        *(*vec).1 <= len &&
        ^vec == *vec
    )
)]
fn _extern_spec_vec_truncate<T>(vec: &mut Vec<T>, len: usize) where T: thrust_models::Model {
    Vec::truncate(vec, len)
}
