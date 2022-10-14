const std = @import("std");
const unicode = @import("unicode.zig");
const LL = @import("ll.zig");
const FiniteAutomaton = @import("finite_automaton.zig");

const ctUtf8EncodeChar = unicode.ctUtf8EncodeChar;
pub const Encoding = unicode.Encoding;

// TODO Gradually add PCRE features, mention what we support in readme
//   and test all of them in all option combinations possible
const PcreGrammar = struct {
    const AstNode = union(enum) {
        string: []const u21,
        char: u21,
        sequence: []const AstNode,
        alternation: []const AstNode,
        star: *const AstNode,
        plus: *const AstNode,
        optional: *const AstNode,
    };
    pub const Subject = AstNode;

    pub const Symbol = union(enum) {
        const Action = enum {
            char,
            sequence,
            alternation,
            star,
            plus,
            optional,
        };

        empty_stack: void,
        start: void,
        alt: void,
        alt0: void,
        mod: void,
        seq: void,
        seq0: void,
        term: u21,
        action: Action,
    };
    pub const start_symbol = .start;

    fn term(t: u21) Symbol {
        return .{ .term = t };
    }

    fn action(t: Symbol.Action) Symbol {
        return .{ .action = t };
    }

    /// Should only be called at comptime
    fn reject(comptime fmt: []const u8, comptime values: anytype) LL.Move(Symbol) {
        var buff: [std.fmt.count(fmt, values)]u8 = undefined;
        return .{ .reject = std.fmt.bufPrint(&buff, fmt, values) catch unreachable };
    }

    pub fn applyAction(
        comptime act: Symbol.Action,
        comptime prev_term: u21,
        comptime subject: []const AstNode,
    ) []const AstNode {
        return switch (act) {
            .char => &[1]AstNode{.{ .char = prev_term }} ++ subject,
            // .sequence and .alternation check for existing symbols they can just add to, otherwise they create it and invert
            //   the operands from the stack
            // Additionally, .sequence will also concatenate multiple characters into a string
            .sequence => if (subject[0] == .char and subject[1] == .char)
                &[1]AstNode{.{ .string = &.{ subject[1].char, subject[0].char } }} ++ subject[2..]
            else if (subject[0] == .char and subject[1] == .string)
                &[1]AstNode{.{ .string = subject[1].string ++ &[1]u21{subject[0].char} }} ++ subject[2..]
            else if (subject[1] == .sequence)
                &[1]AstNode{.{ .sequence = subject[1].sequence ++ &[1]AstNode{subject[0]} }} ++ subject[2..]
            else
                &[1]AstNode{.{ .sequence = &[2]AstNode{ subject[1], subject[0] } }} ++ subject[2..],
            .alternation => if (subject[1] == .alternation)
                &[1]AstNode{.{ .alternation = subject[1].alternation ++ &[1]AstNode{subject[0]} }} ++ subject[2..]
            else
                &[1]AstNode{.{ .alternation = &[2]AstNode{ subject[1], subject[0] } }} ++ subject[2..],
            .star => &[1]AstNode{.{ .star = &subject[0] }} ++ subject[1..],
            .plus => &[1]AstNode{.{ .plus = &subject[0] }} ++ subject[1..],
            .optional => &[1]AstNode{.{ .optional = &subject[0] }} ++ subject[1..],
        };
    }

    pub fn table(comptime symbol: Symbol, comptime new_term: u21) LL.Move(Symbol) {
        return switch (symbol) {
            .start => switch (new_term) {
                ')', '*', '+', '?', '|' => reject("Unexpected symbol '{s}' at start of input", .{ctUtf8EncodeChar(new_term)}),
                0 => .push_epsilon,
                '(' => .{ .push = &.{ term('('), .alt0, term(')'), .mod, .seq, .alt } },
                else => .{ .push = &.{ term(new_term), action(.char), .mod, .seq, .alt } },
            },
            .alt0 => switch (new_term) {
                ')', '*', '+', '?', '|', 0 => reject("Unexpected symbol '{s}'", .{ctUtf8EncodeChar(new_term)}),
                '(' => .{ .push = &.{ term('('), .alt0, term(')'), .mod, .seq, .alt } },
                else => .{ .push = &.{ term(new_term), action(.char), .mod, .seq, .alt } },
            },
            .alt => switch (new_term) {
                ')', 0 => .push_epsilon,
                '|' => .{ .push = &.{ term('|'), .seq0, action(.alternation), .alt } },
                else => reject("Expected closing parenthesis or alternation", .{}),
            },
            .mod => switch (new_term) {
                '*' => .{ .push = &.{ term('*'), action(.star) } },
                '+' => .{ .push = &.{ term('+'), action(.plus) } },
                '?' => .{ .push = &.{ term('?'), action(.optional) } },
                else => .push_epsilon,
            },
            .seq0 => switch (new_term) {
                '(' => .{ .push = &.{ term('('), .alt0, term(')'), .mod, .seq } },
                ')', '*', '+', '?', '|', 0 => reject("Unexpected symbol '{s}'", .{ctUtf8EncodeChar(new_term)}),
                else => .{ .push = &.{ term(new_term), action(.char), .mod, .seq } },
            },
            .seq => switch (new_term) {
                '(' => .{ .push = &.{ term('('), .alt0, term(')'), .mod, action(.sequence), .seq } },
                ')', '|', 0 => .push_epsilon,
                '*', '+', '?' => reject("Unexpected symbol '{s}'", .{ctUtf8EncodeChar(new_term)}),
                else => .{ .push = &.{ term(new_term), action(.char), .mod, action(.sequence), .seq } },
            },
            .empty_stack => if (new_term == 0) .accept else reject(
                "Expected end of input, got '{s}'",
                .{ctUtf8EncodeChar(new_term)},
            ),
            .term => |t| if (t == new_term) .pop else reject("Expected '{s}', got '{s}'", .{
                ctUtf8EncodeChar(t),
                ctUtf8EncodeChar(new_term),
            }),
            // Handled by LL
            .action => unreachable,
        };
    }
};

fn astToAutomatonInner(comptime curr: PcreGrammar.AstNode) FiniteAutomaton {
    const single = FiniteAutomaton.single;
    return switch (curr) {
        .string => |s| FiniteAutomaton.string(s),
        .char => |c| single(c),
        .sequence => |seq| seq_fa: {
            var fa = astToAutomatonInner(seq[0]).concat(astToAutomatonInner(seq[1]));
            for (seq[2..]) |ast| {
                fa = fa.concat(astToAutomatonInner(ast));
            }
            break :seq_fa fa;
        },
        .alternation => |seq| seq_fa: {
            var fa = astToAutomatonInner(seq[0]).alt(astToAutomatonInner(seq[1]));
            for (seq[2..]) |ast| {
                fa = fa.alt(astToAutomatonInner(ast));
            }
            break :seq_fa fa;
        },
        .star => |ast| astToAutomatonInner(ast.*).star(),
        .plus => |ast| astToAutomatonInner(ast.*).plus(),
        .optional => |ast| astToAutomatonInner(ast.*).opt(),
    };
}

fn astToAutomaton(comptime ast: []const PcreGrammar.AstNode) FiniteAutomaton {
    std.debug.assert(ast.len == 1);
    return astToAutomatonInner(ast[0]);
}

const dfa = struct {
    // TODO: Move this to global scope, use it from matchReader as well and in the nfa engine
    // TODO: Could maybe abstract further so that slice and Reader come from the same body?
    // Always includes an error union to be able to try or catch with any settings
    fn NextChar(
        comptime encoding: Encoding,
        comptime single_char: bool,
        comptime additional_errors: type,
    ) type {
        return if (single_char)
            additional_errors!encoding.CharT()
        else switch (encoding) {
            .ascii, .codepoint => additional_errors!encoding.CharT(),
            .utf8, .utf16le => (error{DecodeError} || additional_errors)!u21,
        };
    }

    // We use an implicit error union to get an empty error union when necessary and be able to catch later on
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

        var state: std.math.IntFittingRange(0, automaton.size() - 1) = 0;
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
            if (single_char and options.decodeErrorMode == .@"error" and
                options.encoding != .ascii and options.encoding != .codepoint)
            {
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

        var state: std.math.IntFittingRange(0, automaton.size() - 1) = 0;
        matching: while (true) {
            const char = readNextChar(
                options.encoding,
                single_char,
                @TypeOf(reader),
                reader,
            ) catch |err| {
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
};

pub const Engine = enum {
    /// dfa if no captures (/backreferences), nfa otherwise
    auto,
    dfa,
    nfa,
};

pub const DecodeErrorMode = enum {
    @"error",
    fail,
};

pub const MatchOptions = struct {
    engine: Engine = .auto,
    encoding: Encoding = .ascii,
    decodeErrorMode: DecodeErrorMode = .@"error",
};

const InputKind = enum {
    reader,
    char_slice,
    byte_slice,
};

fn inputKind(comptime encoding: Encoding, comptime Input: type) InputKind {
    const type_info = @typeInfo(Input);
    if (type_info != .Pointer) return .reader;

    const Char = encoding.CharT();
    const child = type_info.Pointer.child;
    switch (type_info.Pointer.size) {
        .Slice => if (child != Char) {
            if (child == u8) return .byte_slice;

            @compileError("Expected input of type []const " ++ @typeName(Char) ++ ", got " ++
                @typeName(Input));
        } else return .char_slice,
        .One => {
            const child_type_info = @typeInfo(child);
            return switch (child_type_info) {
                .Array => |arr| if (arr.child != Char) {
                    if (arr.child == u8) return .byte_slice;

                    @compileError("Expected input of type *const [N]" ++ @typeName(Char) ++
                        ", got " ++ @typeName(Input));
                } else .char_slice,
                else => .reader,
            };
        },
        else => @compileError("Input should be Reader or a slice of either characters or bytes"),
    }
}

pub fn MatchError(
    comptime encoding: Encoding,
    comptime decodeErrorMode: DecodeErrorMode,
    comptime Input: type,
) type {
    var error_set = switch (inputKind(encoding, Input)) {
        .reader => Input.Error,
        else => error{},
    };

    if (decodeErrorMode == .@"error" and encoding.needsDecoding()) {
        error_set = error{DecodeError} || error_set;
    }
    return error_set;
}

pub fn MatchResult(
    comptime options: MatchOptions,
    comptime pattern: [:0]const u8,
    comptime Input: type,
) type {
    // We need the pattern to eventually check if the .auto engine will be .dfa or .nfa (if we use .auto)
    _ = pattern;

    const error_set = MatchError(options.encoding, options.decodeErrorMode, Input);
    if (options.engine != .nfa) return if (error_set == error{}) bool else error_set!bool;
    std.debug.todo("NFA engine, determine when to use NFA in .auto");
}

// We use this function to cache determinized automata
fn cachedDeterminize(comptime pattern: [:0]const u8) FiniteAutomaton {
    return comptime astToAutomaton(LL.parse(PcreGrammar, pattern)).determinize();
}

pub fn match(
    comptime options: MatchOptions,
    comptime pattern: [:0]const u8,
    input: anytype,
) MatchResult(options, pattern, @TypeOf(input)) {
    const Char = options.encoding.CharT();

    // TODO: minimize
    comptime var automaton = astToAutomaton(LL.parse(PcreGrammar, pattern));

    // If we can always just use the first character to check for a transition, do it
    const single_char = comptime automaton.singleCharBoundInEncoding(options.encoding);
    if (options.encoding == .ascii and !single_char)
        @compileError("Found non ascii characters in regex while in .ascii mode");

    // TODO: NFA engine
    const engine = dfa;
    if (engine == dfa) {
        automaton = comptime cachedDeterminize(pattern);
    }

    // Switch to correct engine function
    switch (comptime inputKind(options.encoding, @TypeOf(input))) {
        .reader => return try engine.matchReader(options, automaton, single_char, input),
        .char_slice => return try engine.matchSlice(options, automaton, single_char, @as([]const Char, input)),
        .byte_slice => {
            var fbs = std.io.fixedBufferStream(@as([]const u8, input));
            return try engine.matchReader(options, automaton, single_char, fbs.reader());
        },
    }
}

test "DFA match" {
    // TODO: Was 1500 before removeUnreachableStates
    @setEvalBranchQuota(1_600);
    comptime {
        var fbs = std.io.fixedBufferStream("abdefé");
        std.debug.assert(try match(.{ .encoding = .utf8 }, "ab(def)*é|aghi|abz", fbs.reader()));
        //std.debug.assert(try match(.{}, "ab(def)*é|aghi|abz", "abdefé"));
    }

    try std.testing.expect(try match(.{ .encoding = .utf8 }, "ab(def)*é|aghi|abz", "abdefé"));
    //var fbs = std.io.fixedBufferStream("abdefé");
    //try std.testing.expect(try match(.{}, "ab(def)*é|aghi|abz", fbs.reader()));
}
// TODO Reorganize files, only keep public interface in this file
//   Flesh out structure of things, add `std.debug.todo`s
// TODO Lots and lots of docs
// TODO startsWithMatch is trivial
//   We probably need our own writer type to test utf16le and u21
//   Make a new test.zig file that refAllDecls's all files with tests and tests exposed api
//   In this file, only test internals
// TODO: Test that the ast is as expected, convert to automaton then test that the automaton
//   is as expected

// TODO: Experiment with creating the nfa directly instead of an intermediary AST
