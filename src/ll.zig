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

// We use this to cache by contents of slice instead of pointer
fn parseInner(comptime Grammar: type, comptime N: usize, comptime str: [N:0]u8) []const Grammar.Subject {
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

        // Look up the resulting move in the grammar's parsing table and apply it
        switch (Grammar.table(symbol, term)) {
            .push_epsilon => {},
            .push => |v| stack = v ++ stack,
            .pop => {
                // Advance to next term, keep previous term around
                str_idx += cp_len;
                prev_term = term;
            },
            // TODO: Show error location
            .reject => |msg| {
                var err_buf: [1024]u8 = undefined;
                const err = std.fmt.bufPrint(
                    &err_buf,
                    \\ Parsing error: {s}
                    \\       {s}
                    \\       
                    ++ &[1]u8{'~'} ** (str_idx - 1) ++ &[1]u8{'^'},
                    .{ msg, str[0 .. str_idx + cp_len] },
                ) catch unreachable;
                @compileError(err);
            },
            .accept => return subject,
        }
    }
}

// TODO: Tests
/// Parse `str` into type based on `Grammar` and execute grammar defined actions that can manipulate and return subjects
pub fn parse(comptime Grammar: type, comptime str: [:0]const u8) []const Grammar.Subject {
    return parseInner(Grammar, str.len, str[0..str.len].*);
}
