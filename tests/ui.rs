fn main() {
    let mut config = ui_test::Config::rustc("tests/ui/");
    config.program.program = env!("CARGO_BIN_EXE_thrust-rustc").into();
    config.output_conflict_handling = ui_test::ignore_output_conflict;
    ui_test::run_tests(config).unwrap();
}
