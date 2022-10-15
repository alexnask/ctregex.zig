const std = @import("std");
const dfa = @import("engines/dfa.zig");
const unicode = @import("unicode.zig");
const LL = @import("ll.zig");
const FiniteAutomaton = @import("finite_automaton.zig");

const ctUtf8EncodeChar = unicode.ctUtf8EncodeChar;
pub const Encoding = unicode.Encoding;

// TODO Gradually add PCRE features, mention what we support in readme
//   and test all of them in all option combinations possible
const PcreGrammar = struct {
    pub const Subject = FiniteAutomaton;

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

    fn reject(comptime fmt: []const u8, comptime values: anytype) LL.Move(Symbol) {
        var buff: [std.fmt.count(fmt, values)]u8 = undefined;
        return .{ .reject = std.fmt.bufPrint(&buff, fmt, values) catch unreachable };
    }

    // Construct our FA through actions called by the LL parser
    pub fn applyAction(
        comptime act: Symbol.Action,
        comptime prev_term: u21,
        comptime subject: []const FiniteAutomaton,
    ) []const FiniteAutomaton {
        const single = FiniteAutomaton.single;
        const alt = FiniteAutomaton.alt;
        const concat = FiniteAutomaton.concat;

        return switch (act) {
            .char => &[1]FiniteAutomaton{single(prev_term)} ++ subject,
            .sequence => &[1]FiniteAutomaton{concat(subject[1], subject[0])} ++ subject[2..],
            .alternation => &[1]FiniteAutomaton{alt(subject[1], subject[0])} ++ subject[2..],
            .star => &[1]FiniteAutomaton{subject[0].star()} ++ subject[1..],
            .plus => &[1]FiniteAutomaton{subject[0].plus()} ++ subject[1..],
            .optional => &[1]FiniteAutomaton{subject[0].opt()} ++ subject[1..],
        };
    }

    // LL1 table
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
                if (new_term == 0) "EOF" else ctUtf8EncodeChar(new_term),
            }),
            // Handled by LL
            .action => unreachable,
        };
    }
};

// Return type of nextChar.* engine functions
pub fn NextChar(
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

// We deconstruct slices into this and cachedDeterminize to cache for
// different slices with the same contents
fn cachedNFA(comptime N: usize, comptime pattern: [N:0]u8) FiniteAutomaton {
    return comptime LL.parse(PcreGrammar, &pattern)[0];
}

fn cachedAutoFA(comptime N: usize, comptime pattern: [N:0]u8) FiniteAutomaton {
    // TODO: Call cachedNFA, detect if we an make DFA
    return comptime cachedDFA(N, pattern);
}

fn cachedDFA(comptime N: usize, comptime pattern: [N:0]u8) FiniteAutomaton {
    return comptime LL.parse(PcreGrammar, &pattern)[0].determinize();
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
    decodeErrorMode: DecodeErrorMode = .fail,
};

pub const Operation = enum {
    match,
    starts_with,
};

inline fn matchInner(
    comptime options: MatchOptions,
    comptime N: usize,
    comptime pattern: [N:0]u8,
    comptime operation: Operation,
    input: anytype,
) MatchResult(options, &pattern, @TypeOf(input)) {
    const Char = options.encoding.CharT();

    // TODO NFA engine and auto detection
    const automaton = switch (options.engine) {
        .auto => comptime cachedAutoFA(pattern.len, pattern[0..].*),
        .nfa => comptime cachedNFA(pattern.len, pattern[0..].*),
        .dfa => comptime cachedDFA(pattern.len, pattern[0..].*),
    };
    const engine = dfa;

    // If we can always just use the first character to check for a transition, do it
    const single_char = comptime automaton.singleCharBoundInEncoding(options.encoding);
    if (options.encoding == .ascii and !single_char)
        @compileError("Found non ascii characters in regex while in .ascii mode");

    // Switch to correct engine function
    switch (comptime inputKind(options.encoding, @TypeOf(input))) {
        .reader => return try engine.matchReader(
            options,
            automaton,
            operation,
            single_char,
            input,
        ),
        .char_slice => return try engine.matchSlice(
            options,
            automaton,
            operation,
            single_char,
            @as([]const Char, input),
        ),
        .byte_slice => {
            var fbs = std.io.fixedBufferStream(@as([]const u8, input));
            return try engine.matchReader(
                options,
                automaton,
                operation,
                single_char,
                fbs.reader(),
            );
        },
    }
}

pub fn match(
    comptime options: MatchOptions,
    comptime pattern: [:0]const u8,
    input: anytype,
) MatchResult(options, pattern, @TypeOf(input)) {
    return matchInner(options, pattern.len, pattern[0..].*, .match, input);
}

pub fn startsWith(
    comptime options: MatchOptions,
    comptime pattern: [:0]const u8,
    input: anytype,
) MatchResult(options, pattern, @TypeOf(input)) {
    return matchInner(options, pattern.len, pattern[0..].*, .starts_with, input);
}

test "DFA match" {
    @setEvalBranchQuota(2_100);
    comptime {
        //std.debug.assert(startsWith(.{ .encoding = .utf8 }, "ab(def*é|aghi|abz)😊", "abaghi😊erreftrefe"));
        //std.debug.assert(try match(.{}, "ab(def)*é|aghi|abz", "abdefé"));
    }

    //try std.testing.expect(match(.{ .encoding = .utf8 }, "ab(def)*é|aghi|abz", "abdefé"));
    var fbs = std.io.fixedBufferStream("abdefé");
    try std.testing.expect(match(.{ .encoding = .utf8 }, "ab(def)*é|aghi|abz", fbs.reader()));
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
