# Thrust

Thrust is a refinement type checking and inference tool for Rust.

## Getting Started

- Make sure [Z3](https://github.com/Z3Prover/z3) is installed.
- The main binary, `thrust-rustc`, behaves like `rustc` but includes Thrust's verification.
- In the following instructions, we assume the Thrust source code is cloned locally and commands are executed within it.

Take the following Rust code (`gcd.rs`):

```rust
fn gcd(mut a: i32, mut b: i32) -> i32 {
    while a != b {
        let (l, r) = if a < b {
            (&mut a, &b)
        } else {
            (&mut b, &a)
        };
        *l -= *r;
    }
    a
}

#[thrust::callable]
fn check_gcd(a: i32, b: i32) {
    assert!(gcd(a, b) <= a);
}

fn main() {}
```

Let Thrust verify that the program is correct. Here, we use `cargo run` in the Thrust source tree to build and run `thrust-rustc`. Note that you need to disable the debug overflow assertions in rustc, as they are currently not supported in Thrust.

```console
$ cargo run -- -Adead_code -C debug-assertions=false gcd.rs && echo 'safe'
   Compiling thrust v0.1.0 (/home/coord_e/rust-refinement/thrust)
    Finished `dev` profile [unoptimized + debuginfo] target(s) in 0.08s
     Running `target/debug/thrust-rustc -Adead_code -C debug-assertions=false gcd.rs`
error: verification error: Unsat

error: aborting due to 1 previous error
```

Thrust says the program is not safe (possible to panic). In fact, we have a bug in our `gcd` function:

```diff
 fn gcd(mut a: i32, mut b: i32) -> i32 {
     while a != b {
-        let (l, r) = if a < b {
+        let (l, r) = if a > b {
             (&mut a, &b)
         } else {
             (&mut b, &a)
```

Now Thrust verifies the program is actually safe.

```console
$ cargo run -- -Adead_code -C debug-assertions=false gcd_fixed.rs && echo 'safe'
    Finished `dev` profile [unoptimized + debuginfo] target(s) in 0.08s
     Running `target/debug/thrust-rustc -Adead_code -C debug-assertions=false gcd.rs`
safe
```

Integration test examples are located under `tests/ui/` and can be executed using `cargo test`. You can review these examples to understand what the current Thrust implementation can handle.

## Annotation

Thrust can verify a wide range of programs without explicit annotations, but you can use `#[thrust_macros::requires(expr)]` and `#[thrust_macros::ensures(expr)]` to annotate the precondition and postcondition of a function, aiding in verification or specifying the intended behavior. Here, `expr` is an ordinary Rust expression that Thrust interprets as a logical formula. It supports the usual integer, boolean, and comparison operators, calls to functions declared with `#[thrust_macros::predicate]`, and the model operations described below.

```rust
#[thrust_macros::requires(n >= 0)]
#[thrust_macros::ensures((result * 2) == n * (n + 1))]
fn sum(n: i32) -> i32 {
    if n == 0 {
        0
    } else {
        n + sum(n - 1)
    }
}
```

In an `ensures` expression, the special identifier `result` refers to the return value of the function. `requires` and `ensures` are independent: you can write either one on its own, and a missing one defaults to `true`.

### Mutable references

Within an annotation, a mutable reference `ma: &mut T` is modeled by its value at the time the function is called and its value when the function returns (the *prophecy* value). Use the deref operator `*ma` to denote the current value and the unary `!ma` to denote the final value. You can also construct a mutable-reference model directly with `thrust_models::model::Mut::new(current, final)`.

```rust
use thrust_models::model::Mut;

// `add` increments the referent by `a`. Equivalently, `!ma == *ma + a`.
#[thrust_macros::ensures(ma == Mut::new(*ma, *ma + a))]
fn add(ma: &mut i32, a: i32) {
    *ma += a;
}
```

### Refinement types

The conditions on `requires`/`ensures` are internally encoded as refinement types of the parameter and return types. You can also specify these refinement types directly. A refinement type is written `{ binder: type | formula }`, where `type` is a Rust type and `formula` constrains the value bound to `binder`. Use `#[thrust_macros::param(name: type)]` for a parameter and `#[thrust_macros::ret(type)]` for the return value:

```rust
#[thrust_macros::param(n: { x: i32 | x >= 0 })]
#[thrust_macros::ret({ x: i32 | (x * 2) == n * (n + 1) })]
fn sum(n: i32) -> i32 {
    if n == 0 {
        0
    } else {
        n + sum(n - 1)
    }
}
```

`#[thrust_macros::sig(..)]` is a shorthand that combines the parameter and return refinements into a single function-signature-shaped annotation:

```rust
#[thrust_macros::sig(fn(x: { v: i32 | v > 0 }) -> { r: i32 | r >= x })]
fn g(x: i32) -> i32 {
    x
}
```

Refinements may be nested inside generic arguments and reference types, e.g. `Box<{ v: i64 | v > 0 }>` or `&mut { v: i32 | v >= 0 }`.

### Trusted and callable functions

The body of a function marked with `#[thrust::trusted]` is not analyzed by Thrust; only its annotated specification is used. This is useful for modeling functions whose implementation Thrust cannot (or should not) verify.

```rust
#[thrust::trusted]
#[thrust_macros::ensures(result != x)]
fn rand_except(x: i32) -> i32 { unimplemented!() }
```

`#[thrust::callable]` marks a function as an entry point whose specification must hold for all inputs (i.e. it has no precondition); Thrust checks such functions even when nothing in the crate calls them.

### Predicates

`#[thrust_macros::predicate]` declares a reusable logical predicate that can be referenced from `requires`/`ensures` expressions and from other predicates. Its parameters use the model types from `thrust_models::model` (for example `Int`). The body is a string literal containing the predicate's definition written in SMT-LIB2, referring to the parameters by name (followed by `true` to satisfy the `-> bool` return type).

```rust
#[thrust_macros::predicate]
fn is_double(x: thrust_models::model::Int, doubled_x: thrust_models::model::Int) -> bool {
    "(= (* x 2) doubled_x)"; true
}

#[thrust_macros::ensures(is_double(x, result))]
fn double(x: i64) -> i64 {
    x + x
}
```

A predicate can also be declared in a `trait` (as a method, possibly without a body) and defined per-implementation in `impl` blocks; wrap both with `#[thrust_macros::context]`.

### Existentials

`thrust_models::exists(|x: T| formula)` introduces an existentially quantified variable in a formula.

```rust
use thrust_models::exists;

#[thrust_macros::ensures(exists(|x: i32| result == 2 * x))]
fn f() -> i32 {
    let n = rand();
    n + n
}
```

### Loop invariants

Place a `thrust_macros::invariant!(..)` call at the top of a loop body to declare a loop invariant. The argument is a closure whose parameters name the live variables the invariant refers to (with their types) and whose body is the invariant formula.

```rust
while cond {
    thrust_macros::invariant!(|x: i64, y: i64| x >= 1 && y >= 1);
    // ...
}
```

### Methods and traits

To annotate methods, wrap the surrounding `impl` block or `trait` definition with `#[thrust_macros::context]` so the annotations can see the enclosing generics and `Self`. Inside a method specification, `self` is modeled like any other reference: `*self` is the current value and `!self` the final value.

```rust
struct Counter(i32);

// Model a `Counter` by its integer value.
impl thrust_models::Model for Counter {
    type Ty = thrust_models::model::Int;
}

#[thrust_macros::context]
impl Counter {
    #[thrust::trusted]
    #[thrust_macros::ensures(!self == *self + 1)]
    fn increment(&mut self) {
        self.0 += 1;
    }
}
```

If a method's annotation refers to a loop invariant, use `#[thrust_macros::invariant_context]` on the method so the invariant can also see the enclosing generics and `Self`.

### Higher-order functions

Inside a specification, `thrust_macros::pre!(f(args..))` and `thrust_macros::post!(f(args..), result)` refer to the pre- and postcondition of a closure or function parameter `f`. This lets you give a precise specification to a higher-order function in terms of its callable argument.

```rust
#[thrust_macros::requires(thrust_macros::pre!(f(x)))]
#[thrust_macros::ensures(thrust_macros::post!(f(x), result))]
fn apply<F: FnOnce(i32) -> i32>(x: i32, f: F) -> i32 {
    f(x)
}
```

### Model types

Annotations describe values using *model types* from the `thrust_models` crate, which Thrust injects into the compiled crate. Each Rust type has an associated model accessed through the `thrust_models::Model` trait: integers are modeled by `model::Int`, `&mut T`/`Box<T>` by `model::Mut`/`model::Box`, slices and arrays by `model::Array`, and so on. The constructors and operations used above (`Mut::new`, `Box::new`, `Array::store`, indexing, `exists`, `pre!`/`post!`) are all provided by this crate. When a custom type needs a logical representation, implement `thrust_models::Model` for it to define its `Ty`.

## Configuration

Several environment variables are used by Thrust to configure its behavior:

- `THRUST_SOLVER`: A CHC solver command used to solve CHC constraints generated by Thrust. Default: `z3`
- `THRUST_SOLVER_ARGS`: Whitespace-separated command-line flags passed to the solver. The default is `fp.spacer.global=true fp.validate=true` when the solver is `z3`.
- `THRUST_SOLVER_TIMEOUT_SECS`: Timeout for waiting on results from the solver. Default: `30`
- `THRUST_OUTPUT_DIR`: When configured, Thrust outputs intermediate smtlib2 files into this directory.
- `THRUST_ENUM_EXPANSION_DEPTH_LIMIT`: When Thrust works with enums, it "expands" the structure of the enum value onto its environment. This configuration value sets the limit on the depth of recursion during this expansion to handle enums that are defined recursively. It is our future work to discover a sensible value for this automatically. Default: `2`

## Development

The implementation of the Thrust is largely divided into the following modules.

- `analyze`: MIR analysis. Further divided into the modules corresponding to the program units: `analyze::crate_`, `analyze::local_def`, and `analyze::basic_block`. `analyze::annot` and `analyze::annot_fn` translate the lowered annotation attributes into refinement types and formulas.
- `refine`: Typing environment and related implementations.
- `rty`: Refinement type primitives.
- `chc`: CHC and logic primitives, and it also implements an invocation of the underlying CHC solver.

The surface annotation syntax (`#[thrust_macros::requires]`, `ensures`, `param`, `ret`, `sig`, `predicate`, `invariant!`, `pre!`/`post!`, …) is implemented in the `thrust-macros` crate. These procedural macros expand into a small set of internal plugin attributes — chiefly `#[thrust::formula_fn]` companion functions (written as ordinary Rust over the `thrust_models` model types) together with `#[thrust::requires_path]`, `#[thrust::ensures_path]`, and `#[thrust::refinement_path(..)]` markers that link those companions to the function being specified. `analyze::annot_fn` then reads the type-checked HIR of each `formula_fn` to build the corresponding `chc::Formula`/`rty::Refinement`. The model types themselves are declared in `std.rs`, which Thrust injects into every crate it analyzes.

The implementation generates subtyping constraints in the form of CHCs (`chc::System`). The entry point is `analyze::crate_::Analyzer::run`, followed by `analyze::local_def::Analyzer::run` and `analyze::basic_block::Analyzer::run`, while accumulating the necessary information in `analyze::Analyzer`. Once `chc::System` is collected for the entire input, it invokes an external CHC solver via the `chc::solver` module and subsequently reports the result.

## Publication

Hiromi Ogawa, Taro Sekiyama, and Hiroshi Unno. Thrust: A Prophecy-based Refinement Type System for Rust. PLDI 2025.

## License

Licensed under either of

 * Apache License, Version 2.0
   ([LICENSE-APACHE](LICENSE-APACHE) or http://www.apache.org/licenses/LICENSE-2.0)
 * MIT license
   ([LICENSE-MIT](LICENSE-MIT) or http://opensource.org/licenses/MIT)

at your option.

## Contribution

Unless you explicitly state otherwise, any contribution intentionally submitted
for inclusion in the work by you, as defined in the Apache-2.0 license, shall be
dual licensed as above, without any additional terms or conditions.
