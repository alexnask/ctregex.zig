const std = @import("std");
const unicode = @import("unicode.zig");
const LL = @import("ll.zig");

const ctUtf8EncodeChar = unicode.ctUtf8EncodeChar;
const Encoding = unicode.Encoding;

const Engine = enum {
    /// dfa if no captures (/backreferences), nfa otherwise
    auto,
    dfa,
    nfa,
};

pub const MatchOptions = struct {
    // TODO ignoreUnicodeErros option?
    engine: Engine = .auto,
    encoding: Encoding = .utf8,
};

// TODO Complete grammar
// TODO Add tests
const PcreGrammar = struct {
    pub const Subject = union(enum) {
        char: u21,
        concat: []const Subject,
        alt: []const Subject,
        star: *const Subject,
        plus: *const Subject,
        opt: *const Subject,
    };

    pub const Symbol = union(enum) {
        // TODO Use @TagType(SubjectType) if they always match up, I don't think they will
        const Action = enum {
            char,
            concat,
            alt,
            star,
            plus,
            opt,
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

    pub fn applyAction(comptime act: Symbol.Action, comptime prev_term: u21, comptime subject: []const Subject) []const Subject {
        return switch (act) {
            .char => &[1]Subject{.{ .char = prev_term }} ++ subject,
            // .concat and .alt check for existing symbols they can just add to, otherwise they create it and invert
            //   the operands from the stack
            .concat => if (subject[1] == .concat)
                &[1]Subject{.{ .concat = subject[1].concat ++ &[1]Subject{subject[0]} }} ++ subject[2..]
            else
                &[1]Subject{.{ .concat = &[2]Subject{ subject[1], subject[0] } }} ++ subject[2..],
            .alt => if (subject[1] == .alt)
                &[1]Subject{.{ .alt = subject[1].alt ++ &[1]Subject{subject[0]} }} ++ subject[2..]
            else
                &[1]Subject{.{ .alt = &[2]Subject{ subject[1], subject[0] } }} ++ subject[2..],
            .star => &[1]Subject{.{ .star = &subject[0] }} ++ subject[1..],
            .plus => &[1]Subject{.{ .plus = &subject[0] }} ++ subject[1..],
            .opt => &[1]Subject{.{ .opt = &subject[0] }} ++ subject[1..],
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
                '|' => .{ .push = &.{ term('|'), .seq0, action(.alt), .alt } },
                else => reject("Expected closing parenthesis or alternation", .{}),
            },
            .mod => switch (new_term) {
                '*' => .{ .push = &.{ term('*'), action(.star) } },
                '+' => .{ .push = &.{ term('+'), action(.plus) } },
                '?' => .{ .push = &.{ term('?'), action(.opt) } },
                else => .push_epsilon,
            },
            .seq0 => switch (new_term) {
                '(' => .{ .push = &.{ term('('), .alt0, term(')'), .mod, .seq } },
                ')', '*', '+', '?', '|', 0 => reject("Unexpected symbol '{s}'", .{ctUtf8EncodeChar(new_term)}),
                else => .{ .push = &.{ term(new_term), action(.char), .mod, .seq } },
            },
            .seq => switch (new_term) {
                '(' => .{ .push = &.{ term('('), .alt0, term(')'), .mod, action(.concat), .seq } },
                ')', '|', 0 => .push_epsilon,
                '*', '+', '?' => reject("Unexpected symbol '{s}'", .{ctUtf8EncodeChar(new_term)}),
                else => .{ .push = &.{ term(new_term), action(.char), .mod, action(.concat), .seq } },
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

test "PcreGrammar" {
    _ = comptime LL.parse(PcreGrammar, "abc(def)*");
}

// @TODO Split this stuff into unicode.zig or smth
