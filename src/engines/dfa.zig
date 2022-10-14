const std = @import("std");

const root = @import("../ctregex.zig");
const unicode = @import("../unicode.zig");
const FiniteAutomaton = @import("../finite_automaton.zig");

const NextChar = root.NextChar;
const Encoding = root.Encoding;
const MatchOptions = root.MatchOptions;
const MatchError = root.MatchError;

inline fn nextChar(
    comptime encoding: Encoding,
    comptime single_char: bool,
    input: []const encoding.CharT(),
    input_idx: *usize,
) NextChar(encoding, single_char, error{}) {
    if (single_char) {
        defer input_idx.* += 1;
        return input[input_idx.*];
    } else switch (encoding) {
        .ascii, .codepoint => {
            defer input_idx.* += 1;
            return input[input_idx.*];
        },
        .utf8 => {
            const length = std.unicode.utf8ByteSequenceLength(input[input_idx.*]) catch return error.DecodeError;
            defer input_idx.* += length;
            if (length == 1) return input[input_idx.*];
            if (input_idx.* + length > input.len) return error.DecodeError;
            return switch (length) {
                2 => std.unicode.utf8Decode2(input[input_idx.*..]) catch return error.DecodeError,
                3 => std.unicode.utf8Decode3(input[input_idx.*..]) catch return error.DecodeError,
                4 => std.unicode.utf8Decode4(input[input_idx.*..]) catch return error.DecodeError,
                else => unreachable,
            };
        },
        .utf16le => {
            const length = unicode.utf16leCharSequenceLength(input[input_idx.*]) catch return error.DecodeError;
            defer input_idx.* += length;
            if (length == 1) return input[input_idx.*];
            if (input_idx.* + 2 > input.len) return error.DecodeError;
            return unicode.utf16leDecode(input[input_idx.*..][0..2]) catch return error.DecodeError;
        },
    }
}

pub inline fn matchSlice(
    comptime options: MatchOptions,
    comptime automaton: FiniteAutomaton,
    comptime single_char: bool,
    input: []const options.encoding.CharT(),
) MatchError(
    options.encoding,
    options.decodeErrorMode,
    []const options.encoding.CharT(),
)!bool {
    const decode_err_value = switch (options.decodeErrorMode) {
        .fail => false,
        else => error.DecodeError,
    };

    var state: std.math.IntFittingRange(0, automaton.stateCount() - 1) = 0;
    var input_idx: usize = 0;
    matching: while (input_idx < input.len) {
        const char = nextChar(
            options.encoding,
            single_char,
            input,
            &input_idx,
        ) catch return decode_err_value;

        inline for (automaton.transitions) |t| {
            if (t.source == state and t.label == char) {
                state = t.target;
                continue :matching;
            }
        }

        // Matched no transitions and not at end of stream
        // If we report decoding errors and we are in single char mode, check for an encoding error
        if (single_char and options.decodeErrorMode == .@"error") {
            const last_char = input[input_idx - 1];
            const length = switch (options.encoding) {
                .ascii, .codepoint => unreachable,
                .utf8 => std.unicode.utf8ByteSequenceLength(last_char) catch return error.DecodeError,
                .utf16le => unicode.utf16leDecode(last_char) catch return error.DecodeError,
            };
            if (input_idx - 1 + length > input.len) return error.DecodeError;
            // We need the checks from the decoding functions too here
            _ = switch (options.encoding) {
                .ascii, .codepoint => unreachable,
                .utf8 => std.unicode.utf8Decode(input[input_idx - 1 ..][0..length]) catch return error.DecodeError,
                .utf16le => unicode.utf16leDecode(input[input_idx - 1 ..][0..length]) catch return error.DecodeError,
            };
        }

        return false;
    }

    // We are now at the end of the stream, check if we are in a final state
    inline for (automaton.final_states) |fs| {
        if (fs == state) return true;
    }
    return false;
}

inline fn readNextChar(
    comptime encoding: Encoding,
    comptime single_char: bool,
    comptime Reader: type,
    reader: Reader,
) NextChar(encoding, single_char, error{EndOfStream} || Reader.Error) {
    if (single_char)
        switch (encoding) {
            .ascii, .utf8 => return try reader.readByte(),
            .utf16le => return try reader.readIntLittle(u16),
            .codepoint => return @truncate(u21, try reader.readIntNative(u32)),
        }
    else
        return try encoding.readCodepoint(reader);
}

pub inline fn matchReader(
    comptime options: MatchOptions,
    comptime automaton: FiniteAutomaton,
    comptime single_char: bool,
    reader: anytype,
) MatchError(
    options.encoding,
    options.decodeErrorMode,
    @TypeOf(reader),
)!bool {
    const decode_err_value = switch (options.decodeErrorMode) {
        .fail => false,
        else => error.DecodeError,
    };

    var state: std.math.IntFittingRange(0, automaton.stateCount() - 1) = 0;
    matching: while (true) {
        const char = readNextChar(
            options.encoding,
            single_char,
            @TypeOf(reader),
            reader,
        ) catch |err| {
            // We use if-else here and not switch because the error set depends on options
            if (err == error.EndOfStream) {
                inline for (automaton.final_states) |fs| {
                    if (fs == state) return true;
                }
                return false;
            } else if (err == error.DecodeError) {
                return decode_err_value;
            } else if (@TypeOf(reader).Error != error{}) {
                return @errSetCast(@TypeOf(reader).Error, err);
            }
            unreachable;
        };

        inline for (automaton.transitions) |t| {
            if (t.source == state and t.label == char) {
                state = t.target;
                continue :matching;
            }
        }

        // Matched no transitions and not at end of stream
        // If we report decoding errors and we are in single char mode, check for an encoding error
        if (single_char and options.decodeErrorMode == .@"error") {
            _ = try options.encoding.readCodepointWithFirstChar(reader, char);
        }

        return false;
    }
}
