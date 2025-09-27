const std = @import("std");
const panic = std.debug.panic;

const Op = @import("op.zig").Op;
const SliceReader = @import("op.zig").SliceReader;

const Self = @This();

program: []const u8,
pc: usize,

pub fn run(self: *Self) !void {
    while (Op.scan(self.program[self.pc..])) |op| {
        std.debug.print("{}", .{op});
        self.pc += op.len();
    } else |err| switch (err) {
        error.ReadFailed => panic("unreachable (?)", .{}),
        error.EndOfStream => return,
        error.UnknownOpcode => panic("unknown op code at pc={}", .{self.pc}),
    }
}

test Self {
    const program: []const u8 = &.{0x00};
    var vm: Self = .{
        .program = program,
        .pc = 0,
    };
    try vm.run();
}
