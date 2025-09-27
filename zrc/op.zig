pub const Op = enum(u7) {
    @"return" = 0x00,
    pop = 0x01,
    pop_n = 0x02,
    pop_under_n = 0x03,

    constant = 0x04,
    nil = 0x05,
    false = 0x06,
    true = 0x07,
    list = 0x08,
    object = 0x09,
    type = 0x0a,

    call = 0x10,
    closure = 0x11,

    get_local = 0x20,
    set_local = 0x21,
    get_upvalue = 0x22,
    set_upvalue = 0x23,
    define_global = 0x26,
    get_global = 0x27,
    set_global = 0x28,
    get_field = 0x29,
    set_field = 0x2a,
    get_method = 0x2b,
    set_method = 0x2c,
    get_index = 0x2d,
    set_index = 0x2e,

    not = 0x30,
    eq = 0x31,
    ne = 0x32,
    gt = 0x33,
    ge = 0x34,
    lt = 0x35,
    le = 0x36,

    neg = 0x37,
    add = 0x38,
    sub = 0x39,
    mul = 0x3a,
    div = 0x3b,
    rem = 0x3c,

    // Jumps
    jump = 0x60,
    jump_false_peek = 0x61,
    jump_false_pop = 0x62,
    jump_true_peek = 0x63,
    jump_true_pop = 0x64,
    loop = 0x65,

    pub const ScanError = std.Io.Reader.Error || error{UnknownOpcode};

    // TODO: Debug info
    pub fn scan(reader: *std.Io.Reader) ScanError!Result {
        const byte = try reader.takeByte();
        const op: Op = switch (byte) {
            0x0...0xa, 0x10, 0x11, 0x20...0x23, 0x26...0x2e, 0x30...0x3c, 0x60...0x65 => @enumFromInt(byte),
            else => return error.UnknownOpcode,
        };
        return switch (op.tag()) {
            .one => .{ .one = op },
            .two => .{ .two = .{ .op = op, .byte = try reader.takeByte() } },
            .three => .{ .three = .{ .op = op, .short = try reader.takeInt(u16, .big) } },
            .dyn => blk: {
                _ = try reader.peekByte();
                const upvalue_count = try reader.peekByte();
                break :blk .{ .dyn = .{ .op = op, .len = upvalue_count + 2 } };
            },
        };
    }

    pub const Tag = enum { one, two, three, dyn };

    pub const Result = union(enum) {
        one: Op,
        two: struct {
            op: Op,
            byte: u8,
        },
        three: struct {
            op: Op,
            short: u16,
        },
        dyn: struct {
            op: Op,
            len: usize,
        },
    };
};

const std = @import("std");
