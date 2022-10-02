const std = @import("std");

pub fn Move(comptime Symbol: type) type {
    return union(enum) {
        reject: []const u8,
        pop: void,
        push: []const Symbol,
        accept: void,
        push_epsilon: void,
    };
}

// TODO Tests
/// Parse `str` into an AST type based on `Grammar`
pub fn parse(comptime Grammar: type, comptime str: [:0]const u8) []const Grammar.Subject {
    var stack: []const Grammar.Symbol = &.{Grammar.start_symbol};
    var str_idx: usize = 0;

    var subject: []const Grammar.Subject = &.{};
    var prev_term: u21 = 0;
    while (true) {
        const symbol = if (stack.len == 0) .empty_stack else blk: {
            const s = stack[0];
            stack = stack[1..];
            break :blk s;
        };

        if (symbol == .action) {
            subject = Grammar.applyAction(symbol.action, prev_term, subject);
            continue;
        }

        // Get next terminal
        const cp_len = std.unicode.utf8ByteSequenceLength(str[str_idx]) catch @compileError("Invalid utf8 sequence");
        const term = std.unicode.utf8Decode(str[str_idx..][0..cp_len]) catch @compileError("Invalid utf8 sequence");

        // Look up result in parsing table
        switch (Grammar.table(symbol, term)) {
            .push_epsilon => {},
            .push => |v| stack = v ++ stack,
            .pop => {
                // Advance to next term, keep previous term around
                str_idx += cp_len;
                prev_term = term;
            },
            // @TODO Show error location
            .reject => |msg| @compileError("Parsing error: " ++ msg),
            .accept => return subject,
        }
    }
}
