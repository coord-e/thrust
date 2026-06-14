// Reproduces: an integer literal used as an `Array<Int, T>` index in a spec
// expression fails to type-check (E0308 "expected `Int`, found integer").
//
// `thrust_models::model::Array<I, T>` has an `Index<I>` impl whose index
// type is the `I` parameter; for `Array<Int, T>` that is the `model::Int`
// ZST, which is not the same as Rust's `{integer}` literal type. The spec
// attribute path lowers `it[0]` as a Rust expression, so the `0` must be
// a `model::Int`-typed term. No such literal is constructible in Rust
// source today.
//
// See `array_index_literal_int_workaround.rs` for the bound-variable
// form that sidesteps the literal.

#[thrust_macros::requires(true)]
#[thrust_macros::ensures(
    thrust_models::exists(|it: thrust_models::model::Array<thrust_models::model::Int, i64>|
        it[0] == 0
    )
)]
fn head(arr: Vec<i64>) -> i64 {
    arr[0]
}

fn main() {}
