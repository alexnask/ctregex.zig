//! Comptile time finite automata
//! Starting state is implicitly '0' and we can grab the ending state from
//!   as the maximum target of all transitions
const std = @import("std");
const Encoding = @import("../unicode.zig").Encoding;
const ctUtf8EncodeChar = @import("../unicode.zig").ctUtf8EncodeChar;
const ctutils = @import("../ct_utils.zig");
const CtArrayList = ctutils.CtArrayList;
const CtSortedList = ctutils.CtSortedList;

const Self = @This();

pub const empty = Self{
    .final_states = &.{},
    .transitions = &.{},
};

pub const epsilon = Self{
    .final_states = &.{0},
    .transitions = &.{},
};

// TODO, range, string, any_of etc. labels?
//   Only try after we have completed the finite_automaton systems
const Label = u32;

// We use an extern struct here because we are copying transitions all over the place
// so using buf[0..len].* = slice[0..slice.len].* instead of mem.copy saves a lot of branches
pub const Transition = extern struct {
    source: usize,
    target: usize,

    label: Label,
};

final_states: []const usize,
transitions: []const Transition,

fn startReachableAndTransitions(comptime self: Self) std.meta.Tuple(&.{ bool, []const Transition }) {
    var start_transitions: []const Transition = undefined;
    start_transitions.ptr = self.transitions.ptr;
    start_transitions.len = 0;

    var start_reachable = false;
    for (self.transitions) |t| {
        if (t.source == 0) {
            start_transitions.len += 1;
        } else if (start_reachable) break;
        if (t.target == 0) start_reachable = true;
    }

    return .{ start_reachable, start_transitions };
}

// TODO: This should work and create no dead or unreachable nodes, prove
pub fn concat(comptime lhs: Self, comptime rhs: Self) Self {
    const rhs_start_reachable_transitions = rhs.startReachableAndTransitions();
    const rhs_start_reachable = rhs_start_reachable_transitions[0];
    const rhs_start_transitions = rhs_start_reachable_transitions[1];

    // Offset to be added to states from rhs
    const rhs_offset = lhs.stateCount() - if (rhs_start_reachable) 0 else 1;

    // Works because final_states are not empty and are sorted
    const rhs_start_final = rhs.final_states[0] == 0;
    const remove_final_state = rhs_start_final and !rhs_start_reachable;

    // For every final state of lhs, we copy the transitions from rhs' start state
    // Also, if rhs' start state is also final we keep lhs' final states final instead of removing them
    // If the rhs start state is not reachable, we remove it
    const rhs_final_state_offset = @boolToInt(remove_final_state);
    var final_states: [
        rhs.final_states.len - rhs_final_state_offset +
            if (rhs_start_final) lhs.final_states.len else 0
    ]usize = undefined;
    if (rhs_start_final) {
        // If both lhs and rhs final states are sorted, the result will be sorted
        final_states[0..lhs.final_states.len].* = lhs.final_states[0..].*;

        for (final_states[lhs.final_states.len..][0 .. rhs.final_states.len - rhs_final_state_offset]) |*s, idx|
            s.* = rhs.final_states[idx + rhs_final_state_offset] + rhs_offset;
    } else for (final_states[0 .. rhs.final_states.len - rhs_final_state_offset]) |*s, idx|
        s.* = rhs.final_states[idx + rhs_final_state_offset] + rhs_offset;

    // If the rhs start state is not reachable, we remove its transitions from the rhs portion
    const new_transition_count = lhs.final_states.len * rhs_start_transitions.len;
    const copy_from_rhs_count = if (rhs_start_reachable) rhs.transitions.len else rhs.transitions.len - rhs_start_transitions.len;
    var transitions: [lhs.transitions.len + copy_from_rhs_count + new_transition_count]Transition = undefined;
    transitions[0..lhs.transitions.len].* = lhs.transitions[0..].*;

    var transition_idx = lhs.transitions.len;
    for (lhs.final_states) |s| {
        for (rhs_start_transitions) |t| {
            transitions[transition_idx] = .{
                .source = s,
                .target = t.target + rhs_offset,
                .label = t.label,
            };
            transition_idx += 1;
        }
    }

    // TODO: Interleave copies from original, then when in final state copy the new ones, then till next final state etc.
    //   This way we can avoid sorting here
    std.sort.sort(
        Transition,
        transitions[0..transition_idx],
        {},
        transitionLessThan,
    );

    const rhs_transition_offset = if (rhs_start_reachable) 0 else rhs_start_transitions.len;
    for (transitions[transition_idx..]) |*t, idx| {
        t.* = rhs.transitions[idx + rhs_transition_offset];
        t.source += rhs_offset;
        t.target += rhs_offset;
    }

    return .{
        .final_states = &final_states,
        .transitions = &transitions,
    };
}

// TODO: This should work and create no dead or unreachable nodes, prove
pub fn alt(comptime lhs: Self, comptime rhs: Self) Self {
    const lhs_start_reachable_transitions = lhs.startReachableAndTransitions();
    const lhs_start_reachable = lhs_start_reachable_transitions[0];
    const lhs_start_transitions = lhs_start_reachable_transitions[1];
    const lhs_start_final = lhs.final_states[0] == 0;
    const lhs_remove_final_state = lhs_start_final and !lhs_start_reachable;

    const rhs_start_reachable_transitions = rhs.startReachableAndTransitions();
    const rhs_start_reachable = rhs_start_reachable_transitions[0];
    const rhs_start_transitions = rhs_start_reachable_transitions[1];
    const rhs_start_final = rhs.final_states[0] == 0;
    const rhs_remove_final_state = rhs_start_final and !rhs_start_reachable;

    // Offset to be added to states from rhs, we need 1 extra for the initial state we insert
    const lhs_offset = if (lhs_start_reachable) 1 else 0;
    const rhs_offset = lhs.stateCount() + lhs_offset - if (rhs_start_reachable) 0 else 1;

    // If at least one of the start states is final, our new start state also needs to be
    const new_state_final = lhs_start_final or rhs_start_final;
    const removed_final_states = @boolToInt(lhs_remove_final_state) + @boolToInt(rhs_remove_final_state);
    var final_states: [
        lhs.final_states.len + rhs.final_states.len - removed_final_states +
            @boolToInt(new_state_final)
    ]usize = undefined;

    {
        var offset = 0;
        if (new_state_final) {
            offset = 1;
            final_states[0] = 0;
        }
        for (final_states[offset..lhs.final_states.len]) |*s, idx|
            s.* = lhs.final_states[idx + @boolToInt(lhs_remove_final_state)] + lhs_offset;
        for (final_states[offset..][lhs.final_states.len..]) |*s, idx|
            s.* = rhs.final_states[idx + @boolToInt(rhs_remove_final_state)] + rhs_offset;
    }

    // We don't need to sort any section of transitions, we insert transitions from our new start state to lhs states
    //  then to rhs states, then all the lhs transitions and finally the rhs transitions
    const new_transition_count = lhs_start_transitions.len + rhs_start_transitions.len;

    const copy_from_rhs_count = if (rhs_start_reachable) rhs.transitions.len else rhs.transitions.len - rhs_start_transitions.len;
    const copy_from_lhs_count = if (lhs_start_reachable) lhs.transitions.len else lhs.transitions.len - lhs_start_transitions.len;
    var transitions: [copy_from_lhs_count + copy_from_rhs_count + new_transition_count]Transition = undefined;
    for (lhs_start_transitions) |t, idx| {
        transitions[idx] = .{
            .source = 0,
            .target = t.target + lhs_offset,
            .label = t.label,
        };
    }
    for (rhs_start_transitions) |t, idx| {
        transitions[lhs_start_transitions.len + idx] = .{
            .source = 0,
            .target = t.target + rhs_offset,
            .label = t.label,
        };
    }

    const lhs_transition_offset = if (lhs_start_reachable) 0 else lhs_start_transitions.len;
    const rhs_transition_offset = if (rhs_start_reachable) 0 else rhs_start_transitions.len;

    const old_transition_section = lhs_start_transitions.len + rhs_start_transitions.len;
    for (transitions[old_transition_section..][0..copy_from_lhs_count]) |*t, idx| {
        t.* = lhs.transitions[idx + lhs_transition_offset];
        t.source += lhs_offset;
        t.target += lhs_offset;
    }

    for (transitions[old_transition_section + copy_from_lhs_count ..]) |*t, idx| {
        t.* = rhs.transitions[idx + rhs_transition_offset];
        t.source += rhs_offset;
        t.target += rhs_offset;
    }

    return .{
        .final_states = &final_states,
        .transitions = &transitions,
    };
}

pub fn string(comptime s: []const Label) Self {
    return .{
        .final_states = &.{s.len},
        .transitions = blk: {
            var res: [s.len]Transition = undefined;
            for (res) |*t, idx| {
                t.* = .{
                    .source = idx,
                    .target = idx + 1,
                    .label = s[idx],
                };
            }
            break :blk &res;
        },
    };
}

pub fn single(comptime c: u21) Self {
    return .{ .final_states = &.{1}, .transitions = &.{.{
        .source = 0,
        .target = 1,
        .label = c,
    }} };
}

pub fn opt(comptime self: Self) Self {
    const start_reachable_transitions = self.startReachableAndTransitions();
    const start_reachable = start_reachable_transitions[0];
    const start_transitions = start_reachable_transitions[1];
    const start_final = self.final_states[0] == 0;
    const remove_final_state = start_final and !start_reachable;

    // State offset
    const offset = if (start_reachable) 1 else 0;

    const final_states_offset = @boolToInt(remove_final_state);
    var final_states: [self.final_states.len + @boolToInt(!remove_final_state)]usize = undefined;
    final_states[0] = 0;
    for (final_states[1..]) |*s, idx| s.* = self.final_states[idx + final_states_offset] + offset;

    const copy_from_self_count = if (start_reachable)
        self.transitions.len
    else
        self.transitions.len - start_transitions.len;

    var transitions: [copy_from_self_count + start_transitions.len]Transition = undefined;
    for (transitions[0..start_transitions.len]) |*t, idx| {
        t.* = start_transitions[idx];
        t.source = 0;
        t.target += offset;
    }

    const self_transition_offset = if (start_reachable) 0 else start_transitions.len;
    for (transitions[start_transitions.len..]) |*t, idx| {
        t.* = self.transitions[idx + self_transition_offset];
        t.source += offset;
        t.target += offset;
    }

    return .{
        .final_states = &final_states,
        .transitions = &transitions,
    };
}

fn starOrPlus(comptime self: Self, comptime kind: enum { star, plus }) Self {
    const start_reachable_transitions = self.startReachableAndTransitions();
    const start_reachable = start_reachable_transitions[0];
    const start_transitions = start_reachable_transitions[1];
    const start_final = self.final_states[0] == 0;
    const remove_final_state = start_final and !start_reachable;

    // State offset
    const offset = if (start_reachable) 1 else 0;

    const new_state_final = switch (kind) {
        .star => true,
        .plus => false,
    };

    const final_states_offset = @boolToInt(remove_final_state);
    var final_states: [self.final_states.len - final_states_offset + @boolToInt(new_state_final)]usize = undefined;
    if (new_state_final) {
        final_states[0] = 0;
    }
    for (final_states[@boolToInt(new_state_final)..]) |*s, idx| s.* = self.final_states[idx + final_states_offset] + offset;

    const new_transition_count = start_transitions.len * (self.final_states.len + 1);
    const copy_from_self_count = if (start_reachable)
        self.transitions.len
    else
        self.transitions.len - start_transitions.len;

    var transitions: [copy_from_self_count + new_transition_count]Transition = undefined;
    // Transitions from new start state
    for (transitions[0..start_transitions.len]) |*t, idx| {
        t.* = start_transitions[idx];
        t.source = 0;
        t.target += offset;
    }

    // Rest of old transitions, minus the ones from start if we removed them
    const self_transition_offset = if (start_reachable) 0 else start_transitions.len;
    for (transitions[start_transitions.len..][0..copy_from_self_count]) |*t, idx| {
        t.* = self.transitions[idx + self_transition_offset];
        t.source += offset;
        t.target += offset;
    }

    var transition_idx = start_transitions.len + copy_from_self_count;
    // For each new final state (except state 0 if it is final, which has been handled already)
    //   copy the old start transitions with fixed source and targets
    for (final_states[@boolToInt(new_state_final)..]) |s| {
        for (start_transitions) |t| {
            transitions[transition_idx] = .{
                .source = s,
                .target = t.target + offset,
                .label = t.label,
            };
            transition_idx += 1;
        }
    }

    // TODO: Rewrite in a way we don't need to sort, should be very similar to concat()
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

fn allLabelsLessThan(comptime self: Self, ceil: u21) bool {
    for (self.transitions) |t| {
        if (t.label > ceil) return false;
    }
    return true;
}

pub fn singleCharBoundInEncoding(
    comptime self: Self,
    comptime encoding: Encoding,
) bool {
    return switch (encoding) {
        .ascii, .utf8 => self.allLabelsLessThan(127),
        .utf16le => {
            for (self.transitions) |t| {
                if (t.label > 0xd7ff and t.label < 0xe000) return false;
            }
            return true;
        },
        .codepoint => true,
    };
}

pub fn isDfa(comptime self: Self) bool {
    var start: usize = 0;
    var state = 0;
    for (self.transitions) |t, i| {
        if (t.source != state) {
            const state_transitions = self.transitions[start..i];
            for (state_transitions) |t1, j| {
                var idx = j + 1;
                while (idx < state_transitions.len) : (idx += 1) {
                    if (t1.label == state_transitions[idx].label) return false;
                }
            }
            // Trigger checks here before resetting state
            start = i;
            state = t.source;
        }
    }
    return true;
}

pub fn stateCount(comptime self: Self) usize {
    var max: usize = 0;
    for (self.transitions) |t| {
        if (t.target > max) max = t.target;
        if (t.source > max) max = t.source;
    }
    return max + 1;
}

fn transitionsFrom(comptime self: Self, comptime source: usize) []const Transition {
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

fn transitionLessThan(_: void, lhs: Transition, rhs: Transition) bool {
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
        @compileError(std.fmt.bufPrint(
            &debug_buf,
            "slice lengths differ. expected {d}, found {d}\n",
            .{ expected.len, actual.len },
        ) catch unreachable);
    }
    var i: usize = 0;
    while (i < expected.len) : (i += 1) {
        if (!std.meta.eql(expected[i], actual[i])) {
            @compileError(std.fmt.bufPrint(
                &debug_buf,
                "index {} incorrect. expected {any}, found {any}\n",
                .{ i, expected[i], actual[i] },
            ) catch unreachable);
        }
    }
}

fn expectEqualAutomata(comptime expected: Self, comptime actual: Self) !void {
    try std.testing.expect(actual.isSorted());
    ctExpectEqualSlices(usize, expected.final_states, actual.final_states);
    ctExpectEqualSlices(Transition, expected.transitions, actual.transitions);
}

// TODO: More tests with some complex automata
test "Test automaton building blocks" {
    comptime {
        const a = single('a');
        try expectEqualAutomata(.{ .final_states = &.{1}, .transitions = &.{
            .{
                .source = 0,
                .target = 1,
                .label = 'a',
            },
        } }, a);

        const b = single('b');
        const @"a·b" = concat(a, b);
        try expectEqualAutomata(.{ .final_states = &.{2}, .transitions = &.{
            .{
                .source = 0,
                .target = 1,
                .label = 'a',
            },
            .{
                .source = 1,
                .target = 2,
                .label = 'b',
            },
        } }, @"a·b");

        const @"a|b" = alt(a, b);
        try expectEqualAutomata(.{ .final_states = &.{ 1, 2 }, .transitions = &.{
            .{
                .source = 0,
                .target = 1,
                .label = 'a',
            },
            .{
                .source = 0,
                .target = 2,
                .label = 'b',
            },
        } }, @"a|b");

        const @"a?" = opt(a);
        try expectEqualAutomata(.{ .final_states = &.{ 0, 1 }, .transitions = &.{
            .{
                .source = 0,
                .target = 1,
                .label = 'a',
            },
        } }, @"a?");

        const @"a*" = star(a);
        try expectEqualAutomata(.{ .final_states = &.{ 0, 1 }, .transitions = &.{
            .{
                .source = 0,
                .target = 1,
                .label = 'a',
            },
            .{
                .source = 1,
                .target = 1,
                .label = 'a',
            },
        } }, @"a*");

        const @"a+" = plus(a);
        try expectEqualAutomata(.{ .final_states = &.{1}, .transitions = &.{
            .{
                .source = 0,
                .target = 1,
                .label = 'a',
            },
            .{
                .source = 1,
                .target = 1,
                .label = 'a',
            },
        } }, @"a+");
    }
}

// Used for debug purposes
pub fn printDotFile(comptime self: Self) void {
    var str: []const u8 =
        \\
        \\digraph fsm {
        \\    rankdir=LR;
        \\    node [shape = doublecircle];
    ;

    for (self.final_states) |fs| {
        var buf: [5]u8 = undefined;
        const res = std.fmt.bufPrint(&buf, " {d}", .{fs}) catch unreachable;
        str = str ++ res;
    }
    str = str ++
        \\;
        \\    node [shape = circle];
    ;

    for (self.transitions) |t| {
        var buf: [64]u8 = undefined;
        str = str ++ (std.fmt.bufPrint(
            &buf,
            "\n    {d} -> {d} [label = \"{s}\"];",
            .{ t.source, t.target, ctUtf8EncodeChar(t.label) },
        ) catch unreachable);
    }
    str = "\n" ++ str ++ "\n}";
    @compileError(str);
}
