const std = @import("std");

// @TODO Utf32le?
pub const Encoding = enum {
    ascii,
    utf8,
    utf16le,
    codepoint,

    pub fn CharT(comptime self: Encoding) type {
        return switch (self) {
            .ascii, .utf8 => u8,
            .utf16le => u16,
            .codepoint => u21,
        };
    }

    pub fn ctEncode(comptime encoding: Encoding, comptime cp: u21) []const encoding.CharT() {
        if (encoding == .codepoint) return &.{cp};

        const len = charLenInEncoding(cp, encoding);
        var res: [len]encoding.CharT() = undefined;
        switch (encoding) {
            .ascii => {
                res[0] = @truncate(u8, cp);
            },
            .utf8 => _ = std.unicode.utf8Encode(cp, &res) catch unreachable,
            .utf16le => {
                const utf8_c = ctUtf8EncodeChar(cp);
                _ = std.unicode.utf8ToUtf16Le(&res, utf8_c) catch unreachable;
            },
            .codepoint => unreachable,
        }
        return &res;
    }

    // TODO Clean this whole file up
    pub fn ReadCodepointError(comptime encoding: Encoding, comptime Reader: type) type {
        return switch (encoding) {
            .ascii, .codepoint => error{EndOfStream} || Reader.Error,
            else => error{ DecodeError, EndOfStream } || Reader.Error,
        };
    }

    pub fn needsDecoding(comptime encoding: Encoding) bool {
        return switch (encoding) {
            .ascii, .codepoint => false,
            else => true,
        };
    }

    pub fn ReadError(comptime encoding: Encoding, comptime Reader: type) type {
        return switch (encoding) {
            .ascii, .codepoint => Reader.Error,
            else => error{DecodeError} || Reader.Error,
        };
    }

    inline fn utf8DoNextByte(reader: anytype, value: *u21) !void {
        const c = reader.readByte() catch |err| switch (err) {
            error.EndOfStream => return error.DecodeError,
            else => |e| return e,
        };
        if (c & 0b11000000 != 0b10000000) return error.DecodeError;
        value.* <<= 6;
        value.* |= c & 0b00111111;
    }

    pub inline fn readCodepointWithFirstChar(
        comptime encoding: Encoding,
        reader: anytype,
        c: encoding.CharT(),
    ) encoding.ReadError(@TypeOf(reader))!(if (encoding == .ascii) u8 else u21) {
        switch (encoding) {
            .ascii => return c,
            .utf8 => {
                const length = std.unicode.utf8CodepointSequenceLength(c) catch return error.DecodeError;
                switch (length) {
                    1 => return c,
                    2 => {
                        const c0: u21 = c;
                        var value: u21 = c0 & 0b00011111;
                        try utf8DoNextByte(reader, &value);
                        if (value < 0x80) return error.DecodeError;
                        return value;
                    },
                    3 => {
                        const c0: u21 = c;
                        var value: u21 = c0 & 0b00001111;
                        try utf8DoNextByte(reader, &value);
                        try utf8DoNextByte(reader, &value);
                        if (value < 0x800 or (0xd800 <= value and value <= 0xdfff))
                            return error.DecodeError;
                        return value;
                    },
                    4 => {
                        const c0: u21 = c;
                        var value: u21 = c0 & 0b00000111;
                        try utf8DoNextByte(reader, &value);
                        try utf8DoNextByte(reader, &value);
                        try utf8DoNextByte(reader, &value);

                        if (value < 0x10000 or value > 0x10FFFF) return error.DecodeError;
                        return value;
                    },
                    else => unreachable,
                }
            },
            .utf16le => {
                const c0: u21 = c;
                if (c0 & ~@as(u21, 0x03ff) == 0xd800) {
                    const c1: u21 = reader.readIntLittle(u16) catch |err| switch (err) {
                        error.EndOfStream => return error.DecodeError,
                        else => |e| return e,
                    };
                    if (c1 & ~@as(u21, 0x03ff) != 0xdc00) return error.DecodeError;
                    return 0x10000 + (((c0 & 0x03ff) << 10) | (c1 & 0x03ff));
                } else if (c0 & ~@as(u21, 0x03ff) == 0xdc00)
                    return error.DecodeError;
                return c0;
            },
            .codepoint => return c,
        }
    }

    pub inline fn readCodepoint(
        comptime encoding: Encoding,
        reader: anytype,
    ) encoding.ReadCodepointError(@TypeOf(reader))!(if (encoding == .ascii) u8 else u21) {
        switch (encoding) {
            .ascii => return try reader.readByte(),
            .utf8 => {
                const c0 = try reader.readByte();
                return try encoding.readCodepointWithFirstChar(reader, c0);
            },
            .utf16le => {
                const c0 = try reader.readIntLittle(u16);
                return try encoding.readCodepointWithFirstChar(reader, c0);
            },
            .codepoint => return reader.readIntNative(u21),
        }
    }
};

// TODO Prune
fn utf16leCharSequenceLength(first_char: u16) !u2 {
    const c0: u21 = first_char;
    if (first_char & ~@as(u21, 0x03ff) == 0xd800) {
        return 2;
    } else if (c0 & ~@as(u21, 0x03ff) == 0xdc00) {
        return error.UnexpectedSecondSurrogateHalf;
    }
    return 1;
}

fn utf16leDecode(chars: []const u16) !u21 {
    const c0: u21 = chars[0];
    if (c0 & ~@as(u21, 0x03ff) == 0xd800) {
        const c1: u21 = chars[1];
        if (c1 & ~@as(u21, 0x03ff) != 0xdc00) return error.ExpectedSecondSurrogateHalf;
        return 0x10000 + (((c0 & 0x03ff) << 10) | (c1 & 0x03ff));
    } else if (c0 & ~@as(u21, 0x03ff) == 0xdc00) {
        return error.UnexpectedSecondSurrogateHalf;
    } else {
        return c0;
    }
}

pub fn ctUtf8EncodeChar(comptime codepoint: u21) []const u8 {
    var buf: [4]u8 = undefined;
    return buf[0 .. std.unicode.utf8Encode(codepoint, &buf) catch unreachable];
}

fn checkAscii(comptime codepoint: u21) void {
    if (codepoint > 127) @compileError("Cannot match character '" ++ ctUtf8EncodeChar(codepoint) ++ "' in ascii mode.");
}

fn charLenInEncoding(comptime codepoint: u21, comptime encoding: Encoding) usize {
    switch (encoding) {
        .ascii => {
            checkAscii(codepoint);
            return 1;
        },
        .utf8 => return std.unicode.utf8CodepointSequenceLength(codepoint) catch unreachable,
        .utf16le => return if (codepoint < 0x10000) 1 else 2,
        .codepoint => return 1,
    }
}

fn ctDecode(comptime encoding: Encoding, comptime str: []const encoding.CharT()) []const u21 {
    if (encoding == .codepoint) return str;

    var len = switch (encoding) {
        .codepoint => unreachable,
        .ascii => str.len,
        .utf8 => std.unicode.utf8CountCodepoints(str) catch @compileError("Invalid utf8 string"),
        .utf16le => std.unicode.utf16CountCodepoints(str) catch @compileError("Invalid utf16 string"),
    };

    var result: [len]u21 = undefined;
    var str_idx: usize = 0;
    var res_idx: usize = 0;
    while (str_idx < str.len) : (res_idx += 1) {
        switch (encoding) {
            .codepoint => unreachable,
            .ascii => {
                if (str[str_idx] > 127) @compileError("Invalid ascii character");
                result[res_idx] = str[str_idx];
                str_idx += 1;
            },
            .utf8 => {
                const u8_len = std.unicode.utf8ByteSequenceLength(str[str_idx]) catch unreachable;
                result[res_idx] = std.unicode.utf8Decode(str[str_idx..][0..u8_len]) catch unreachable;
                str_idx += u8_len;
            },
            .utf16le => {
                const u16_len = utf16leCharSequenceLength(str[str_idx]) catch unreachable;
                result[res_idx] = utf16leDecode(str[str_idx..][0..u16_len]) catch unreachable;
                str_idx += u16_len;
            },
        }
    }

    return &result;
}

fn ctIntStr(comptime int: anytype) []const u8 {
    var buf: [16]u8 = undefined;
    return std.fmt.bufPrint(&buf, "{}", .{int}) catch unreachable;
}
