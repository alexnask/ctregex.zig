//! Comptile time finite automata
//! Starting state is implicitly '0' and we can grab the ending state from
//!   as the maximum target of all transitions
const std = @import("std");

const Self = @This();

pub const empty = Self{
    .final_states = &.{},
    .transitions = &.{},
};

pub const epsilon = Self{
    .final_states = &.{0},
    .transitions = &.{},
};

pub const Transition = struct {
    source: comptime_int,
    target: comptime_int,

    // TODO one_of, string?
    input: union(enum) {
        single: u21,
        range: struct {
            start: u21,
            /// `end` is inclusive
            end: u21,
        },
    },
};

final_states: []const comptime_int,
transitions: []const Transition,

pub fn concat(comptime lhs: Self, comptime rhs: Self) Self {
    // Offset to be added to states from rhs
    const rhs_offset = lhs.size();

    // For every final state of lhs, we copy the transitions from rhs' start state
    // Also, if rhs' start state is also final we keep lhs' final states final instead of removing them
    const rhs_start_final = rhs.isFinal(0);
    var final_states: [rhs.final_states.len + if (rhs_start_final) lhs.final_states.len else 0]comptime_int = undefined;
    if (rhs_start_final) {
        // If both lhs and rhs final states are sorted, the result will be sorted
        std.mem.copy(comptime_int, final_states, lhs.final_states);
        for (final_states[lhs.final_states.len..][0..rhs.final_states.len]) |*s, idx|
            s.* = rhs.final_states[idx] + rhs_offset;
    } else for (final_states[0..rhs.final_states.len]) |*s, idx|
        s.* = rhs.final_states[idx] + rhs_offset;

    const rhs_start_transitions = rhs.transitionsFrom(0);
    const new_transition_count = lhs.final_states.len * rhs_start_transitions.len;
    var transitions: [lhs.transitions.len + rhs.transitions.len + new_transition_count]Transition = undefined;
    std.mem.copy(Transition, &transitions, lhs.transitions);

    var transition_idx = lhs.transitions.len;
    for (lhs.final_states) |s| {
        for (rhs_start_transitions) |t| {
            transitions[transition_idx] = .{
                .source = s,
                .target = t.target + rhs_offset,
                .input = t.input,
            };
            transition_idx += 1;
        }
    }

    // TODO Find the actual block that should be sorted? We don't need to starts at `0` here
    std.sort.sort(
        Transition,
        transitions[0..transition_idx],
        {},
        transitionLessThan,
    );

    for (transitions[transition_idx..]) |*t, idx| t.* = .{
        .source = rhs.transitions[idx].source + rhs_offset,
        .target = rhs.transitions[idx].target + rhs_offset,
        .input = rhs.transitions[idx].input,
    };

    return .{
        .final_states = &final_states,
        .transitions = &transitions,
    };
}

pub fn alt(comptime lhs: Self, comptime rhs: Self) Self {
    // Offset to be added to states from rhs, we need 1 extra for the initial state we insert
    const rhs_offset = lhs.size() + 1;

    // If at least one of the start states is final, our new start state also needs to be
    const new_state_final = lhs.isFinal(0) or rhs.isFinal(0);
    var final_states: [
        lhs.final_states.len + rhs.final_states.len +
            @boolToInt(new_state_final)
    ]comptime_int = undefined;

    {
        var offset = 0;
        if (new_state_final) {
            offset = 1;
            final_states[0] = 0;
        }
        for (final_states[offset..lhs.final_states.len]) |*s, idx| s.* = lhs.final_states[idx] + 1;
        for (final_states[offset..][lhs.final_states.len..]) |*s, idx| s.* = rhs.final_states[idx] + rhs_offset;
    }

    // We don't need to sort any section of transitions, we insert transitions from our new start state to lhs states
    //  then to rhs states, then all the lhs transitions and finally the rhs transitions
    const lhs_start_transitions = lhs.transitionsFrom(0);
    const rhs_start_transitions = rhs.transitionsFrom(0);
    const new_transition_count = lhs_start_transitions.len + rhs_start_transitions.len;
    var transitions: [lhs.transitions.len + rhs.transitions.len + new_transition_count]Transition = undefined;
    for (lhs_start_transitions) |t, idx| {
        transitions[idx] = .{
            .source = 0,
            .target = t.target + 1,
            .input = t.input,
        };
    }
    for (rhs_start_transitions) |t, idx| {
        transitions[lhs_start_transitions.len + idx] = .{
            .source = 0,
            .target = t.target + rhs_offset,
            .input = t.input,
        };
    }

    const old_transition_section = lhs_start_transitions.len + rhs_start_transitions.len;
    for (transitions[old_transition_section..][0..lhs.transitions.len]) |*t, idx| t.* = .{
        .source = lhs.transitions[idx].source + 1,
        .target = lhs.transitions[idx].target + 1,
        .input = lhs.transitions[idx].input,
    };
    for (transitions[old_transition_section + lhs.transitions.len ..]) |*t, idx| t.* = .{
        .source = rhs.transitions[idx].source + rhs_offset,
        .target = rhs.transitions[idx].target + rhs_offset,
        .input = rhs.transitions[idx].input,
    };

    return .{
        .final_states = &final_states,
        .transitions = &transitions,
    };
}

pub fn char(comptime c: u21) Self {
    return .{ .final_states = &.{1}, .transitions = &.{.{
        .source = 0,
        .target = 1,
        .input = .{ .single = c },
    }} };
}

pub fn opt(comptime self: Self) Self {
    var final_states: [self.final_states.len + 1]comptime_int = undefined;
    final_states[0] = 0;
    for (final_states[1..]) |*s, idx| s.* = self.final_states[idx] + 1;

    const start_transitions = self.transitionsFrom(0);
    var transitions: [self.transitions.len + start_transitions.len]Transition = undefined;
    for (transitions[0..start_transitions.len]) |*t, idx| {
        t.* = .{
            .source = 0,
            .target = start_transitions[idx].target + 1,
            .input = start_transitions[idx].input,
        };
    }
    for (transitions[start_transitions.len..]) |*t, idx| t.* = .{
        .source = self.transitions[idx].source + 1,
        .target = self.transitions[idx].target + 1,
        .input = self.transitions[idx].input,
    };

    return .{
        .final_states = &final_states,
        .transitions = &transitions,
    };
}

fn starOrPlus(comptime self: Self, comptime kind: enum { star, plus }) Self {
    const offset = switch (kind) {
        .star => 1,
        .plus => 0,
    };
    // Almost exactly the same as opt, but with additional cloning of starting transitions to the final states
    var final_states: [self.final_states.len + offset]comptime_int = undefined;
    if (offset != 0) {
        final_states[0] = 0;
    }
    for (final_states[offset..]) |*s, idx| s.* = self.final_states[idx] + 1;

    const start_transitions = self.transitionsFrom(0);
    const new_transition_count = start_transitions.len * (self.final_states.len + 1);
    var transitions: [self.transitions.len + new_transition_count]Transition = undefined;
    for (transitions[0..start_transitions.len]) |*t, idx| t.* = .{
        .source = 0,
        .target = start_transitions[idx].target + 1,
        .input = start_transitions[idx].input,
    };
    for (transitions[start_transitions.len..][0..self.transitions.len]) |*t, idx| t.* = .{
        .source = self.transitions[idx].source + 1,
        .target = self.transitions[idx].target + 1,
        .input = self.transitions[idx].input,
    };

    var transition_idx = start_transitions.len + self.transitions.len;
    for (final_states[offset..]) |s| {
        for (start_transitions) |t| {
            transitions[transition_idx] = .{
                .source = s,
                .target = t.target + 1,
                .input = t.input,
            };
            transition_idx += 1;
        }
    }
    std.debug.assert(transition_idx == transitions.len);
    // TODO: Optimize block we need to sort like concat?
    std.sort.sort(
        Transition,
        transitions[start_transitions.len + self.transitions.len ..],
        {},
        transitionLessThan,
    );

    return .{
        .final_states = &final_states,
        .transitions = &transitions,
    };
}

pub fn star(comptime self: Self) Self {
    return self.starOrPlus(.star);
}

pub fn plus(comptime self: Self) Self {
    return self.starOrPlus(.plus);
}

pub fn removeDeadStates(comptime self: Self) Self {
    var state_reachable: []bool = b: {
        var res = [1]bool{true};
        break :b &res;
    };
    var max_state = 0;
    for (self.transitions) |t| {
        if (t.target > max_state) max_state = t.target;
        if (t.source > max_state) max_state = t.source;

        // Allocate to max_state if necessary, guarantee we are in bounds later
        if (state_reachable.len <= max_state)
            state_reachable = b: {
                var new_arr = [1]bool{false} ** (max_state + 1);
                std.mem.copy(bool, &new_arr, state_reachable);
                break :b &new_arr;
            };

        if (state_reachable[t.source])
            state_reachable[t.target] = true;
    }

    // Map from current states to new states
    const new_state = block: {
        var res: [max_state + 1]comptime_int = undefined;
        var already_removed = 0;
        for (res) |*new, old| {
            if (!state_reachable[old])
                already_removed += 1;
            new.* = old - already_removed;
        }
        break :block res;
    };

    // Filter final states
    var final_states: [self.final_states.len]comptime_int = undefined;
    var final_states_idx = 0;
    for (self.final_states) |s| {
        if (state_reachable[s]) {
            final_states[final_states_idx] = new_state[s];
            final_states_idx += 1;
        }
    }

    // Filter transitions and fix states
    var transitions: [self.transitions.len]Transition = undefined;
    var transitions_idx = 0;
    for (self.transitions) |t| {
        if (!state_reachable[t.source] or !state_reachable[t.target])
            continue;

        transitions[transitions_idx] = .{
            .source = new_state[t.source],
            .target = new_state[t.target],
            .input = t.input,
        };
        transitions_idx += 1;
    }

    return .{
        .final_states = final_states[0..final_states_idx],
        .transitions = transitions[0..transitions_idx],
    };
}

fn isFinal(comptime self: Self, comptime state: comptime_int) bool {
    // Assume this is sorted
    for (self.final_states) |s| {
        if (s > state) return false;
        if (s == state) return true;
    }
    unreachable;
}

fn size(comptime self: Self) comptime_int {
    var max = 0;
    for (self.transitions) |t| {
        if (t.target > max) max = t.target;
        if (t.source > max) max = t.source;
    }
    return max + 1;
}

fn transitionsFrom(comptime self: Self, comptime source: comptime_int) []const Transition {
    var idx = 0;
    while (idx < self.transitions.len) : (idx += 1) {
        if (self.transitions[idx].source == source) {
            const start = idx;
            while (idx < self.transitions.len and self.transitions[idx].source == source) : (idx += 1) {}
            return self.transitions[start..idx];
        } else if (self.transitions[idx].source > source) {
            break;
        }
    }

    return &.{};
}

fn transitionLessThan(_: void, comptime lhs: Transition, comptime rhs: Transition) bool {
    return lhs.source < rhs.source;
}

fn isSorted(comptime self: Self) bool {
    return comptime std.sort.isSorted(
        Transition,
        self.transitions,
        {},
        transitionLessThan,
    );
}

fn ctExpectEqualSlices(comptime T: type, comptime expected: []const T, comptime actual: []const T) void {
    var debug_buf: [1024]u8 = undefined;

    if (expected.len != actual.len) {
        @compileError(std.fmt.bufPrint(&debug_buf, "slice lengths differ. expected {d}, found {d}\n", .{ expected.len, actual.len }) catch unreachable);
    }
    var i: usize = 0;
    while (i < expected.len) : (i += 1) {
        if (!std.meta.eql(expected[i], actual[i])) {
            @compileError(std.fmt.bufPrint(&debug_buf, "index {} incorrect. expected {any}, found {any}\n", .{ i, expected[i], actual[i] }) catch unreachable);
        }
    }
}

fn expectEqualAutomata(comptime expected: Self, comptime actual: Self) !void {
    try std.testing.expect(actual.isSorted());
    ctExpectEqualSlices(comptime_int, expected.final_states, actual.final_states);
    ctExpectEqualSlices(Transition, expected.transitions, actual.transitions);
}

// TODO: More tests with some complex automata
test "Test automaton building blocks" {
    comptime {
        const a = char('a');
        try expectEqualAutomata(a, .{ .final_states = &.{1}, .transitions = &.{
            .{
                .source = 0,
                .target = 1,
                .input = .{ .single = 'a' },
            },
        } });

        const b = char('b');
        const @"a·b" = concat(a, b).removeDeadStates();
        try expectEqualAutomata(@"a·b", .{ .final_states = &.{2}, .transitions = &.{
            .{
                .source = 0,
                .target = 1,
                .input = .{ .single = 'a' },
            },
            .{
                .source = 1,
                .target = 2,
                .input = .{ .single = 'b' },
            },
        } });

        const @"a|b" = alt(a, b).removeDeadStates();
        try expectEqualAutomata(@"a|b", .{ .final_states = &.{ 1, 2 }, .transitions = &.{
            .{
                .source = 0,
                .target = 1,
                .input = .{ .single = 'a' },
            },
            .{
                .source = 0,
                .target = 2,
                .input = .{ .single = 'b' },
            },
        } });

        const @"a?" = opt(a).removeDeadStates();
        try expectEqualAutomata(@"a?", .{ .final_states = &.{ 0, 1 }, .transitions = &.{
            .{
                .source = 0,
                .target = 1,
                .input = .{ .single = 'a' },
            },
        } });

        const @"a*" = star(a).removeDeadStates();
        try expectEqualAutomata(@"a*", .{ .final_states = &.{ 0, 1 }, .transitions = &.{
            .{
                .source = 0,
                .target = 1,
                .input = .{ .single = 'a' },
            },
            .{
                .source = 1,
                .target = 1,
                .input = .{ .single = 'a' },
            },
        } });

        const @"a+" = plus(a).removeDeadStates();
        try expectEqualAutomata(@"a+", .{ .final_states = &.{1}, .transitions = &.{
            .{
                .source = 0,
                .target = 1,
                .input = .{ .single = 'a' },
            },
            .{
                .source = 1,
                .target = 1,
                .input = .{ .single = 'a' },
            },
        } });
    }
}

// TODO determinize function, minimize function, isDFA function

