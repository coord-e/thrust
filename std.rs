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

        impl<T> PartialEq<T> for Int where T: super::Model<Ty = Self> {
            #[thrust::ignored]
            fn eq(&self, _other: &T) -> bool {
                unimplemented!()
            }
        }

        impl<T> PartialOrd<T> for Int where T: super::Model<Ty = Self> {
            #[thrust::ignored]
            fn partial_cmp(&self, _other: &T) -> Option<std::cmp::Ordering> {
                unimplemented!()
            }
        }

        impl<T> std::ops::Add<T> for Int where T: super::Model<Ty = Self> {
            type Output = Self;

            #[thrust::ignored]
            fn add(self, _rhs: T) -> Self::Output {
                unimplemented!()
            }
        }

        impl<T> std::ops::Sub<T> for Int where T: super::Model<Ty = Self> {
            type Output = Self;

            #[thrust::ignored]
            fn sub(self, _rhs: T) -> Self::Output {
                unimplemented!()
            }
        }

        impl<T> std::ops::Mul<T> for Int where T: super::Model<Ty = Self> {
            type Output = Self;

            #[thrust::ignored]
            fn mul(self, _rhs: T) -> Self::Output {
                unimplemented!()
            }
        }

        impl std::ops::Neg for Int {
            type Output = Self;

            #[thrust::ignored]
            fn neg(self) -> Self::Output {
                unimplemented!()
            }
        }

        #[thrust::def::mut_model]
        pub struct Mut<T: ?Sized>(PhantomData<T>);

        impl<T> Mut<T> {
            #[allow(dead_code)]
            #[thrust::def::mut_new]
            #[thrust::ignored]
            pub fn new(_a: T, _b: T) -> Self {
                unimplemented!()
            }
        }

        impl<T, U> PartialEq<U> for Mut<T> where U: super::Model<Ty = Self> {
            #[thrust::ignored]
            fn eq(&self, _other: &U) -> bool {
                unimplemented!()
            }
        }

        impl<T> std::ops::Deref for Mut<T> {
            type Target = T;

            #[thrust::ignored]
            fn deref(&self) -> &Self::Target {
                unimplemented!()
            }
        }

        impl<T> std::ops::Not for Mut<T> {
            type Output = T;

            #[thrust::ignored]
            fn not(self) -> Self::Output {
                unimplemented!()
            }
        }

        #[thrust::def::box_model]
        pub struct Box<T: ?Sized>(PhantomData<T>);

        impl<T> Box<T> {
            #[allow(dead_code)]
            #[thrust::def::box_new]
            #[thrust::ignored]
            pub fn new(_x: T) -> Self {
                unimplemented!()
            }
        }

        impl<T, U> PartialEq<U> for Box<T> where U: super::Model<Ty = Self> {
            #[thrust::ignored]
            fn eq(&self, _other: &U) -> bool {
                unimplemented!()
            }
        }

        impl<T> std::ops::Deref for Box<T> {
            type Target = T;

            #[thrust::ignored]
            fn deref(&self) -> &Self::Target {
                unimplemented!()
            }
        }

        #[thrust::def::array_model]
        pub struct Array<I: ?Sized, T: ?Sized>(PhantomData<I>, PhantomData<T>);

        impl<I, T, U> PartialEq<U> for Array<I, T> where U: super::Model<Ty = Self> {
            #[thrust::ignored]
            fn eq(&self, _other: &U) -> bool {
                unimplemented!()
            }
        }

        impl<I, T, U> std::ops::Index<U> for Array<I, T> where U: super::Model<Ty = I> {
            type Output = T;

            #[thrust::ignored]
            fn index(&self, _index: U) -> &Self::Output {
                unimplemented!()
            }
        }

        impl<I, T> Array<I, T> {
            #[allow(dead_code)]
            #[thrust::def::array_store]
            #[thrust::ignored]
            pub fn store<U>(&self, _index: U, _value: T) -> Self where U: super::Model<Ty = I> {
                unimplemented!()
            }
        }

        #[thrust::def::closure_model]
        pub struct Closure<T: ?Sized>(PhantomData<T>);

        impl<T: ?Sized> PartialEq for Closure<T> {
            #[thrust::ignored]
            fn eq(&self, _other: &Self) -> bool {
                unimplemented!()
            }
        }

        /// Refers to the precondition of a closure in a specification.
        ///
        /// Prefer the `thrust_macros::pre!(f(x))` surface syntax, which desugars to this; the
        /// `args` here is the tuple of logical arguments (`(x,)` for one argument, `()` for none).
        #[allow(dead_code)]
        #[thrust::def::closure_precondition]
        #[thrust::ignored]
        pub fn closure_precondition<F, Args>(_f: F, _args: Args) -> bool {
            unimplemented!()
        }

        /// Refers to the postcondition of a closure in a specification, relating the
        /// logical arguments `args` to the closure's `result`.
        ///
        /// Prefer the `thrust_macros::post!(f(x), r)` surface syntax, which desugars to this.
        #[allow(dead_code)]
        #[thrust::def::closure_postcondition]
        #[thrust::ignored]
        pub fn closure_postcondition<F, Args, R>(_f: F, _args: Args, _result: R) -> bool {
            unimplemented!()
        }

        pub struct Vec<T: ?Sized>(pub Array<Int, T>, pub Int);

        impl<T, U> PartialEq<U> for Vec<T> where U: super::Model<Ty = Self> {
            #[thrust::ignored]
            fn eq(&self, _other: &U) -> bool {
                unimplemented!()
            }
        }

        /// `Seq<T>` is the ghost sequence type used in specifications.
        /// Like `Vec`, it is represented logically as `(Array<Int, T>, Int)`
        /// — the array carries elements, the int carries length. Concrete
        /// operations (indexing, push, concat, …) are added incrementally
        /// in follow-up commits.
        #[thrust::def::seq_model]
        pub struct Seq<T: ?Sized>(pub Array<Int, T>, pub Int);

        impl<T, U> PartialEq<U> for Seq<T> where U: super::Model<Ty = Self> {
            #[thrust::ignored]
            fn eq(&self, _other: &U) -> bool {
                unimplemented!()
            }
        }
    }

    impl<T> Model for model::Seq<T> where T: Model {
        type Ty = model::Seq<<T as Model>::Ty>;
    }

    impl Model for model::Int {
        type Ty = model::Int;
    }

    macro_rules! int_model {
        ($T:ty) => {
            impl Model for $T {
                type Ty = model::Int;
            }

            impl PartialEq<model::Int> for $T {
                #[thrust::ignored]
                fn eq(&self, _other: &model::Int) -> bool {
                    unimplemented!()
                }
            }

            impl PartialOrd<model::Int> for $T {
                #[thrust::ignored]
                fn partial_cmp(&self, _other: &model::Int) -> Option<std::cmp::Ordering> {
                    unimplemented!()
                }
            }

            impl std::ops::Add<model::Int> for $T {
                type Output = model::Int;

                #[thrust::ignored]
                fn add(self, _rhs: model::Int) -> Self::Output {
                    unimplemented!()
                }
            }

            impl std::ops::Sub<model::Int> for $T {
                type Output = model::Int;

                #[thrust::ignored]
                fn sub(self, _rhs: model::Int) -> Self::Output {
                    unimplemented!()
                }
            }

            impl std::ops::Mul<model::Int> for $T {
                type Output = model::Int;

                #[thrust::ignored]
                fn mul(self, _rhs: model::Int) -> Self::Output {
                    unimplemented!()
                }
            }
        };
    }

    int_model!(isize);
    int_model!(i32);
    int_model!(i64);
    int_model!(usize);
    int_model!(u32);
    int_model!(u64);

    impl Model for bool {
        type Ty = bool;
    }

    impl<T: ?Sized> Model for model::Closure<T> {
        type Ty = model::Closure<T>;
    }

    macro_rules! impl_tuple_model {
        ($($T:ident),*) => {
            impl<$($T),*> Model for ($($T,)*) where $($T: Model),* {
                type Ty = ($(<$T as Model>::Ty,)*);
            }
        };
    }

    impl_tuple_model!();
    impl_tuple_model!(T0);
    impl_tuple_model!(T0, T1);
    impl_tuple_model!(T0, T1, T2);
    impl_tuple_model!(T0, T1, T2, T3);
    impl_tuple_model!(T0, T1, T2, T3, T4);
    impl_tuple_model!(T0, T1, T2, T3, T4, T5);
    impl_tuple_model!(T0, T1, T2, T3, T4, T5, T6);
    impl_tuple_model!(T0, T1, T2, T3, T4, T5, T6, T7);
    impl_tuple_model!(T0, T1, T2, T3, T4, T5, T6, T7, T8);
    impl_tuple_model!(T0, T1, T2, T3, T4, T5, T6, T7, T8, T9);

    impl<'a, T: ?Sized> Model for &'a mut T where T: Model {
        type Ty = model::Mut<<T as Model>::Ty>;
    }

    impl<T: ?Sized> Model for model::Mut<T> {
        type Ty = model::Mut<T>;
    }

    impl<'a, T: ?Sized> Model for &'a T where T: Model {
        type Ty = &'a <T as Model>::Ty;
    }

    impl<T: ?Sized> Model for Box<T> where T: Model {
        type Ty = model::Box<<T as Model>::Ty>;
    }

    impl<T: ?Sized> Model for model::Box<T> {
        type Ty = model::Box<T>;
    }

    impl<I: ?Sized, T: ?Sized> Model for model::Array<I, T> {
        type Ty = model::Array<I, T>;
    }

    impl<T> Model for Vec<T> where T: Model {
        type Ty = model::Vec<<T as Model>::Ty>;
    }

    impl<T: ?Sized> Model for model::Vec<T> {
        type Ty = model::Vec<T>;
    }

    impl<T> Model for Option<T> where T: Model {
        type Ty = Option<<T as Model>::Ty>;
    }

    impl<T, E> Model for Result<T, E> where T: Model, E: Model {
        type Ty = Result<<T as Model>::Ty, <E as Model>::Ty>;
    }

    #[allow(dead_code)]
    #[thrust::def::exists]
    #[thrust::ignored]
    pub fn exists<T>(_x: T) -> bool {
        unimplemented!()
    }

    #[allow(dead_code)]
    #[thrust::def::forall]
    #[thrust::ignored]
    pub fn forall<T>(_x: T) -> bool {
        unimplemented!()
    }

    #[allow(dead_code)]
    #[thrust::def::implies]
    #[thrust::ignored]
    pub fn implies(_lhs: bool, _rhs: bool) -> bool {
        unimplemented!()
    }

    #[thrust::def::invariant_marker]
    #[thrust::ignored]
    #[inline(never)]
    pub fn __invariant_marker<F>(_f: F) {
        unimplemented!()
    }

    #[allow(dead_code)]
    #[thrust::def::fn_param_wrapper]
    pub struct FnParam<T>(std::marker::PhantomData<T>);

    impl<T> Model for FnParam<T> where T: Model {
        type Ty = FnParam<<T as Model>::Ty>;
    }

    impl<T> FnParam<T> {
        #[allow(dead_code)]
        #[thrust::def::fn_param_at_entry]
        #[thrust::ignored]
        pub fn at_entry(self) -> T {
            unimplemented!()
        }
    }
}

#[thrust::extern_spec_fn]
#[thrust_macros::requires(true)]
#[thrust_macros::ensures(result == thrust_models::model::Box::new(x))]
fn _extern_spec_box_new<T>(x: T) -> Box<T> where T: thrust_models::Model, T::Ty: PartialEq {
    Box::new(x)
}

#[thrust::extern_spec_fn]
#[thrust_macros::requires(true)]
#[thrust_macros::ensures(result == (x == y))]
fn _extern_spec_box_partialeq_eq<T>(x: &Box<T>, y: &Box<T>) -> bool
  where T: thrust_models::Model + PartialEq, T::Ty: PartialEq
{
    <Box<T> as PartialEq>::eq(x, y)
}

#[thrust::extern_spec_fn]
#[thrust_macros::requires(true)]
#[thrust_macros::ensures(*x == !y && *y == !x)]
fn _extern_spec_std_mem_swap<T>(x: &mut T, y: &mut T) where T: thrust_models::Model, T::Ty: PartialEq {
    std::mem::swap(x, y)
}

#[thrust::extern_spec_fn]
#[thrust_macros::requires(true)]
#[thrust_macros::ensures(!dest == src && result == *dest)]
fn _extern_spec_std_mem_replace<T>(dest: &mut T, src: T) -> T where T: thrust_models::Model, T::Ty: PartialEq {
    std::mem::replace(dest, src)
}

#[thrust::extern_spec_fn]
#[thrust_macros::requires(true)]
#[thrust_macros::ensures(result == (x == y))]
fn _extern_spec_option_partialeq_eq<T>(x: &Option<T>, y: &Option<T>) -> bool
  where T: thrust_models::Model + PartialEq, T::Ty: PartialEq
{
    <Option<T> as PartialEq>::eq(x, y)
}

#[thrust::extern_spec_fn]
#[thrust_macros::requires(opt != None)]
#[thrust_macros::ensures(Some(result) == opt)]
fn _extern_spec_option_unwrap<T>(opt: Option<T>) -> T where T: thrust_models::Model, T::Ty: PartialEq {
    Option::unwrap(opt)
}

#[thrust::extern_spec_fn]
#[thrust_macros::requires(true)]
#[thrust_macros::ensures(
    (*opt == None && result == true)
    || (*opt != None && result == false)
)]
fn _extern_spec_option_is_none<T>(opt: &Option<T>) -> bool where T: thrust_models::Model, T::Ty: PartialEq {
    Option::is_none(opt)
}

#[thrust::extern_spec_fn]
#[thrust_macros::requires(true)]
#[thrust_macros::ensures(
    (*opt == None && result == false)
    || (*opt != None && result == true)
)]
fn _extern_spec_option_is_some<T>(opt: &Option<T>) -> bool where T: thrust_models::Model, T::Ty: PartialEq {
    Option::is_some(opt)
}

#[thrust::extern_spec_fn]
#[thrust_macros::requires(true)]
#[thrust_macros::ensures(
    (opt != None && Some(result) == opt)
    || (opt == None && result == default)
)]
fn _extern_spec_option_unwrap_or<T>(opt: Option<T>, default: T) -> T where T: thrust_models::Model, T::Ty: PartialEq {
    Option::unwrap_or(opt, default)
}

#[thrust::extern_spec_fn]
#[thrust_macros::requires(
    opt == None || thrust_models::exists(|i| opt == Some(i) && thrust_macros::pre!(f(i)))
)]
#[thrust_macros::ensures(
    (opt == None && result == None)
    || thrust_models::exists(|i| thrust_models::exists(|j|
        opt == Some(i) && thrust_macros::post!(f(i), j) && result == Some(j)))
)]
fn _extern_spec_option_map<T, U, F>(opt: Option<T>, f: F) -> Option<U>
where
    T: thrust_models::Model, T::Ty: PartialEq,
    U: thrust_models::Model, U::Ty: PartialEq,
    F: FnOnce(T) -> U,
{
    Option::map(opt, f)
}

#[thrust::extern_spec_fn]
#[thrust_macros::requires(opt != None || thrust_macros::pre!(f()))]
#[thrust_macros::ensures(
    (opt != None && Some(result) == opt)
    || (opt == None && thrust_macros::post!(f(), result))
)]
fn _extern_spec_option_unwrap_or_else<T, F>(opt: Option<T>, f: F) -> T
where
    T: thrust_models::Model, T::Ty: PartialEq,
    F: FnOnce() -> T,
{
    Option::unwrap_or_else(opt, f)
}

#[thrust::extern_spec_fn]
#[thrust_macros::requires(true)]
#[thrust_macros::ensures(
    (thrust_models::exists(|x| opt == Some(x) && result == Ok(x)))
    || (opt == None && result == Err(err))
)]
fn _extern_spec_option_ok_or<T, E>(opt: Option<T>, err: E) -> Result<T, E>
    where T: thrust_models::Model, T::Ty: PartialEq,
          E: thrust_models::Model, E::Ty: PartialEq,
{
    Option::ok_or(opt, err)
}

#[thrust::extern_spec_fn]
#[thrust_macros::requires(true)]
#[thrust_macros::ensures(!opt == None && result == *opt)]
fn _extern_spec_option_take<T>(opt: &mut Option<T>) -> Option<T> where T: thrust_models::Model, T::Ty: PartialEq {
    Option::take(opt)
}

#[thrust::extern_spec_fn]
#[thrust_macros::requires(true)]
#[thrust_macros::ensures(!opt == Some(src) && result == *opt)]
fn _extern_spec_option_replace<T>(opt: &mut Option<T>, src: T) -> Option<T>
    where T: thrust_models::Model, T::Ty: PartialEq
{
    Option::replace(opt, src)
}

#[thrust::extern_spec_fn]
#[thrust_macros::requires(true)]
#[thrust_macros::ensures(
    thrust_models::exists(|x| opt == &Some(x) && result == Some(&x))
    || (opt == &None && result == None)
)]
fn _extern_spec_option_as_ref<T>(opt: &Option<T>) -> Option<&T> where T: thrust_models::Model, T::Ty: PartialEq {
    Option::as_ref(opt)
}

#[thrust::extern_spec_fn]
#[thrust_macros::requires(true)]
#[thrust_macros::ensures(
    thrust_models::exists(|x1, x2|
      *opt == Some(x1) &&
      !opt == Some(x2) &&
      result == Some(thrust_models::model::Mut::new(x1, x2))
    )
    || (
      *opt == None &&
      !opt == None &&
      result == None
    )
)]
fn _extern_spec_option_as_mut<T>(opt: &mut Option<T>) -> Option<&mut T>
  where T: thrust_models::Model, T::Ty: PartialEq
{
    Option::as_mut(opt)
}

#[thrust::extern_spec_fn]
#[thrust_macros::requires(true)]
#[thrust_macros::ensures(result == (x == y))]
fn _extern_spec_result_partialeq_eq<T, E>(x: &Result<T, E>, y: &Result<T, E>) -> bool
  where T: thrust_models::Model + PartialEq, T::Ty: PartialEq,
        E: thrust_models::Model + PartialEq, E::Ty: PartialEq,
{
    <Result<T, E> as PartialEq>::eq(x, y)
}

#[thrust::extern_spec_fn]
#[thrust_macros::requires(thrust_models::exists(|x| res == Ok(x)))]
#[thrust_macros::ensures(Ok(result) == res)]
fn _extern_spec_result_unwrap<T, E: std::fmt::Debug>(res: Result<T, E>) -> T
  where T: thrust_models::Model, T::Ty: PartialEq,
        E: thrust_models::Model, E::Ty: PartialEq,
{
    Result::unwrap(res)
}

#[thrust::extern_spec_fn]
#[thrust_macros::requires(thrust_models::exists(|x| res == Err(x)))]
#[thrust_macros::ensures(Err(result) == res)]
fn _extern_spec_result_unwrap_err<T: std::fmt::Debug, E>(res: Result<T, E>) -> E
  where T: thrust_models::Model, T::Ty: PartialEq,
        E: thrust_models::Model, E::Ty: PartialEq,
{
    Result::unwrap_err(res)
}

#[thrust::extern_spec_fn]
#[thrust_macros::requires(true)]
#[thrust_macros::ensures(
    thrust_models::exists(|x| res == Ok(x) && result == Some(x))
    || thrust_models::exists(|x| res == Err(x) && result == None)
)]
fn _extern_spec_result_ok<T, E>(res: Result<T, E>) -> Option<T>
  where T: thrust_models::Model, T::Ty: PartialEq,
        E: thrust_models::Model, E::Ty: PartialEq,
{
    Result::ok(res)
}

#[thrust::extern_spec_fn]
#[thrust_macros::requires(true)]
#[thrust_macros::ensures(
    thrust_models::exists(|x| res == Ok(x) && result == None)
    || thrust_models::exists(|x| res == Err(x) && result == Some(x))
)]
fn _extern_spec_result_err<T, E>(res: Result<T, E>) -> Option<E>
  where T: thrust_models::Model, T::Ty: PartialEq,
        E: thrust_models::Model, E::Ty: PartialEq,
{
    Result::err(res)
}

#[thrust::extern_spec_fn]
#[thrust_macros::requires(true)]
#[thrust_macros::ensures(
    thrust_models::exists(|x| *res == Ok(x) && result == true)
    || thrust_models::exists(|x| *res == Err(x) && result == false)
)]
fn _extern_spec_result_is_ok<T, E>(res: &Result<T, E>) -> bool
  where T: thrust_models::Model, T::Ty: PartialEq,
        E: thrust_models::Model, E::Ty: PartialEq,
{
    Result::is_ok(res)
}

#[thrust::extern_spec_fn]
#[thrust_macros::requires(true)]
#[thrust_macros::ensures(
    thrust_models::exists(|x| *res == Ok(x) && result == false)
    || thrust_models::exists(|x| *res == Err(x) && result == true)
)]
fn _extern_spec_result_is_err<T, E>(res: &Result<T, E>) -> bool
  where T: thrust_models::Model, T::Ty: PartialEq,
        E: thrust_models::Model, E::Ty: PartialEq,
{
    Result::is_err(res)
}

#[thrust::extern_spec_fn]
#[thrust_macros::requires(true)] // TODO: require x != i32::MIN
#[thrust_macros::ensures(result >= 0 && (result == x || result == -x))]
fn _extern_spec_i32_abs(x: i32) -> i32 {
    i32::abs(x)
}

#[thrust::extern_spec_fn]
#[thrust_macros::requires(true)]
#[thrust_macros::ensures(
    (x >= y && result == (x - y))
    || (x < y && result == (y - x))
)]
fn _extern_spec_i32_abs_diff(x: i32, y: i32) -> u32 {
    i32::abs_diff(x, y)
}

#[thrust::extern_spec_fn]
#[thrust_macros::requires(true)]
#[thrust_macros::ensures((x == 0 && result == 0) || (x > 0 && result == 1) || (x < 0 && result == -1))]
fn _extern_spec_i32_signum(x: i32) -> i32 {
    i32::signum(x)
}

#[thrust::extern_spec_fn]
#[thrust_macros::requires(true)]
#[thrust_macros::ensures((x < 0 && result == false) || (x >= 0 && result == true))]
fn _extern_spec_i32_is_positive(x: i32) -> bool {
    i32::is_positive(x)
}

#[thrust::extern_spec_fn]
#[thrust_macros::requires(true)]
#[thrust_macros::ensures((x <= 0 && result == true) || (x > 0 && result == false))]
fn _extern_spec_i32_is_negative(x: i32) -> bool {
    i32::is_negative(x)
}

#[thrust::extern_spec_fn]
#[thrust_macros::requires(true)]
#[thrust_macros::ensures(result.1 == 0)]
fn _extern_spec_vec_new<T>() -> Vec<T> where T: thrust_models::Model, T::Ty: PartialEq {
    Vec::<T>::new()
}

#[thrust::extern_spec_fn]
#[thrust_macros::requires(true)]
#[thrust_macros::ensures(!vec == thrust_models::model::Vec((*vec).0.store((*vec).1, elem), (*vec).1 + 1))]
fn _extern_spec_vec_push<T>(vec: &mut Vec<T>, elem: T)
    where T: thrust_models::Model, T::Ty: PartialEq
{
    Vec::push(vec, elem)
}

#[thrust::extern_spec_fn]
#[thrust_macros::requires(true)]
#[thrust_macros::ensures(result == vec.1)]
fn _extern_spec_vec_len<T>(vec: &Vec<T>) -> usize where T: thrust_models::Model, T::Ty: PartialEq {
    Vec::len(vec)
}

#[thrust::extern_spec_fn]
#[thrust_macros::requires(index < vec.1)]
#[thrust_macros::ensures(*result == vec.0[index])]
fn _extern_spec_vec_index<T>(vec: &Vec<T>, index: usize) -> &T where T: thrust_models::Model, T::Ty: PartialEq {
    <Vec<T> as std::ops::Index<usize>>::index(vec, index)
}

#[thrust::extern_spec_fn]
#[thrust_macros::requires(index < (*vec).1)]
#[thrust_macros::ensures(
    *result == (*vec).0[index] &&
    !result == (!vec).0[index] &&
    !vec == thrust_models::model::Vec((*vec).0.store(index, !result), (*vec).1)
)]
fn _extern_spec_vec_index_mut<T>(vec: &mut Vec<T>, index: usize) -> &mut T
    where T: thrust_models::Model, T::Ty: PartialEq
{
    <Vec<T> as std::ops::IndexMut<usize>>::index_mut(vec, index)
}

#[thrust::extern_spec_fn]
#[thrust_macros::requires(true)]
#[thrust_macros::ensures((!vec).1 == 0)]
fn _extern_spec_vec_clear<T>(vec: &mut Vec<T>) where T: thrust_models::Model, T::Ty: PartialEq {
    Vec::clear(vec)
}

#[thrust::extern_spec_fn]
#[thrust_macros::requires(true)]
#[thrust_macros::ensures(
    (!vec).0 == (*vec).0 && (
        (
            (*vec).1 > 0 &&
            (!vec).1 == (*vec).1 - 1 &&
            result == Some((*vec).0[(*vec).1 - 1])
        ) || (
            (*vec).1 == 0 &&
            (!vec).1 == 0 &&
            result == None
        )
    )
)]
fn _extern_spec_vec_pop<T>(vec: &mut Vec<T>) -> Option<T> where T: thrust_models::Model, T::Ty: PartialEq {
    Vec::pop(vec)
}

#[thrust::extern_spec_fn]
#[thrust_macros::requires(true)]
#[thrust_macros::ensures(result == ((*vec).1 == 0))]
fn _extern_spec_vec_is_empty<T>(vec: &Vec<T>) -> bool where T: thrust_models::Model, T::Ty: PartialEq {
    Vec::is_empty(vec)
}

#[thrust::extern_spec_fn]
#[thrust_macros::requires(true)]
#[thrust_macros::ensures(
    (
        (*vec).1 > len &&
        !vec == thrust_models::model::Vec((*vec).0, len)
    ) || (
        (*vec).1 <= len &&
        !vec == *vec
    )
)]
fn _extern_spec_vec_truncate<T>(vec: &mut Vec<T>, len: usize) where T: thrust_models::Model, T::Ty: PartialEq {
    Vec::truncate(vec, len)
}

// TODO: The following specs of some trait methods are too restrictive; we should allow for a
//       per-impl spec once we can describe the spec of blanket impls.

#[thrust::extern_spec_fn]
#[thrust_macros::requires(true)]
#[thrust_macros::ensures(result == (*x == *y))]
fn _extern_spec_partialeq_eq<T>(x: &T, y: &T) -> bool
  where T: thrust_models::Model + PartialEq, T::Ty: PartialEq
{
    PartialEq::eq(x, y)
}

#[thrust::extern_spec_fn]
#[thrust_macros::requires(true)]
#[thrust_macros::ensures(result == (*x < *y))]
fn _extern_spec_partialord_lt<T>(x: &T, y: &T) -> bool
  where T: thrust_models::Model + PartialOrd, T::Ty: PartialOrd
{
    PartialOrd::lt(x, y)
}

#[thrust::extern_spec_fn]
#[thrust_macros::requires(true)]
#[thrust_macros::ensures(result == (*x > *y))]
fn _extern_spec_partialord_gt<T>(x: &T, y: &T) -> bool
  where T: thrust_models::Model + PartialOrd, T::Ty: PartialOrd
{
    PartialOrd::gt(x, y)
}
