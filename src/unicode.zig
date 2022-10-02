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
};

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

fn ctUtf8EncodeChar(comptime codepoint: u21) []const u8 {
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

fn ctEncode(comptime encoding: Encoding, comptime str: []const u21) []const encoding.CharT() {
    if (encoding == .codepoint) return str;

    var len: usize = 0;
    for (str) |c| len += charLenInEncoding(c, encoding);

    var result: [len]encoding.CharT() = undefined;
    var idx: usize = 0;
    for (str) |c| {
        switch (encoding) {
            .ascii => {
                result[idx] = @truncate(u8, c);
                idx += 1;
            },
            .utf8 => idx += std.unicode.utf8Encode(c, result[idx..]) catch unreachable,
            .utf16le => {
                const utf8_c = ctUtf8EncodeChar(c);
                idx += std.unicode.utf8ToUtf16Le(result[idx..], utf8_c) catch unreachable;
            },
            .codepoint => unreachable,
        }
    }
    return &result;
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

// @TODO Test with invalid utf8 strings and valid + invalid utf16 strings too
test "ctDecode + ctEncode" {
    comptime {
        const target = "Τι λέει;";
        const u21_target = ctDecode(.utf8, target);
        try std.testing.expectEqualSlices(u8, target, ctEncode(.utf8, u21_target));
    }
}

fn ctIntStr(comptime int: anytype) []const u8 {
    var buf: [16]u8 = undefined;
    return std.fmt.bufPrint(&buf, "{}", .{int}) catch unreachable;
}
