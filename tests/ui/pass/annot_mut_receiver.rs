//@check-pass
//@compile-flags: -Adead_code -C debug-assertions=off

struct Counter;

impl thrust_models::Model for Counter {
    type Ty = thrust_models::model::Int;
}

impl Counter {
    #[thrust_macros::requires(true)]
    #[thrust_macros::ensures(true)]
    fn increment(&mut self) {}
}

// TODO: test call-site verification once the ZST-local-in-live-locals bug is fixed
// (see elaborate_unused_args in local_def.rs — unit placeholder copies non-unit refinement)
fn main() {}
