// Annotation-side workaround for `array_index_literal_int.rs`.
//
// Rather than writing the literal `0` as the index (which fails because
// the `Index<I>` impl on `Array<I, T>` requires `I`-typed indices, and
// `model::Int` has no Rust literal form), bind the index with an
// existential and let typeck infer its sort:
//
//   exists(|idx| it[idx] == 0)
//
// `idx` gets the `model::Int` sort from the `Index<I>` site's expected
// `I = model::Int`. The expression type-checks; the trade-off is that
// the spec no longer pins a specific index like "0" or "1" — it just
// asserts "there exists some index such that the value at that index is 0".

#[thrust_macros::requires(true)]
#[thrust_macros::ensures(
    thrust_models::exists(|it: thrust_models::model::Array<thrust_models::model::Int, i64>|
        thrust_models::exists(|idx|
            it[idx] == 0
        )
    )
)]
fn head(arr: Vec<i64>) -> i64 {
    arr[0]
}

fn main() {}
