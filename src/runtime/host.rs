use crate::runtime::Value;
use crate::vm::VmOptions;

pub type HostFn = fn(opts: &mut VmOptions<'_>, argc: u8, argv: &[Value]) -> Value;

pub fn print(opts: &mut VmOptions<'_>, _argc: u8, argv: &[Value]) -> Value {
    if let Some(first) = argv.first() {
        write!(opts.stdout, "{}", first).unwrap();
        for v in &argv[1..] {
            write!(opts.stdout, " {}", v).unwrap();
        }
    }

    Value::Nil
}

pub fn println(opts: &mut VmOptions<'_>, argc: u8, argv: &[Value]) -> Value {
    let v = print(opts, argc, argv);
    writeln!(opts.stdout).unwrap();
    v
}

pub fn list_append(_: &mut VmOptions<'_>, argc: u8, argv: &[Value]) -> Value {
    assert_eq!(argc, 2);

    let elt = argv[1].clone();

    let ptr = argv[0].try_as_object_ref().unwrap();
    let list = unsafe { ptr.as_mut() }.try_as_list_mut().unwrap();

    list.items.push(elt);
    Value::Nil
}
