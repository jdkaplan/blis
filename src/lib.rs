pub mod bytecode;
pub mod compile;
pub mod parse;
pub mod runtime;
pub mod vm;

#[cfg(test)]
mod testing;

#[cfg(test)]
mod tests {
    use std::path::PathBuf;

    use rstest::rstest;

    use crate::testing::{replace_object_ids, snapshot_name};

    use super::compile::Compiler;
    use super::parse::Parser;
    use super::vm::{Vm, VmOptions, VmResult};

    struct TestResult {
        result: VmResult<()>,
        stdout: String,
        stderr: String,
    }

    fn run(source: &str) -> TestResult {
        let ast = Parser::parse(source).unwrap();
        let program = Compiler::compile(&ast).unwrap();

        let mut stdout = Vec::new();
        let mut stderr = Vec::new();

        let result = {
            let mut vm = Vm::new(VmOptions {
                stdout: Box::new(&mut stdout),
                stderr: Box::new(&mut stderr),
            });
            vm.interpret(program)
        };

        TestResult {
            result,
            stdout: replace_object_ids(String::from_utf8(stdout).unwrap()),
            stderr: replace_object_ids(String::from_utf8(stderr).unwrap()),
        }
    }

    #[rstest]
    fn test_programs(#[files("test_programs/*.blis")] path: PathBuf) {
        let source = std::fs::read_to_string(&path).unwrap();
        let run = run(&source);

        assert!(run.result.is_ok(), "{:?}", run.stderr);

        insta::with_settings!({
            input_file => &path,
            description => source,
            omit_expression => true,
        }, {
            insta::assert_snapshot!(snapshot_name(&path, "stdout"), run.stdout);
        })
    }

    #[rstest]
    fn test_runtime_errors(#[files("test_programs/err_runtime/*.blis")] path: PathBuf) {
        let source = std::fs::read_to_string(&path).unwrap();
        let run = run(&source);

        assert!(run.result.is_err());

        insta::with_settings!({
            input_file => &path,
            description => source,
            omit_expression => true,
        }, {
            insta::assert_snapshot!(snapshot_name(&path, "error"), run.result.unwrap_err());
            insta::assert_snapshot!(snapshot_name(&path, "stdout"), run.stdout);
            insta::assert_snapshot!(snapshot_name(&path, "stderr"), run.stderr);
        })
    }
}
