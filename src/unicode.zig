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

    pub fn needsDecoding(comptime encoding: Encoding) bool {
        return switch (encoding) {
            .ascii, .codepoint => false,
            else => true,
        };
    }

    inline fn utf8DoNextByte(reader: anytype, value: *u21) (@TypeOf(reader).Error || error{DecodeError})!void {
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
    ) !(if (encoding == .ascii) u8 else u21) {
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
    ) !(if (encoding == .ascii) u8 else u21) {
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

pub fn utf16leCharSequenceLength(first_char: u16) !u2 {
    const c0: u21 = first_char;
    if (first_char & ~@as(u21, 0x03ff) == 0xd800) {
        return 2;
    } else if (c0 & ~@as(u21, 0x03ff) == 0xdc00) {
        return error.UnexpectedSecondSurrogateHalf;
    }
    return 1;
}

pub fn utf16leDecode(chars: []const u16) !u21 {
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
