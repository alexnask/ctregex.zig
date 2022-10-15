//! Comptile time finite automata
//! Starting state is implicitly '0' and we can grab the ending state from
//!   as the maximum target of all transitions
const std = @import("std");
const Encoding = @import("unicode.zig").Encoding;
const ctUtf8EncodeChar = @import("unicode.zig").ctUtf8EncodeChar;

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

pub fn singleCharBoundInEncoding(comptime self: Self, comptime encoding: Encoding) bool {
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

// TODO: Move to some ct_utilities.zig file
fn CtSortedList(comptime T: type) type {
    return struct {
        items: []const T = &.{},

        fn append(comptime self: *@This(), elem: usize) void {
            if (self.items.len == 0) {
                self.items = &[1]usize{elem};
                return;
            }

            var idx = self.items.len - 1;
            while (true) : (idx -= 1) {
                if (elem == self.items[idx]) return;
                if (elem > self.items[idx]) {
                    self.items = self.items[0 .. idx + 1] ++ &[1]usize{elem} ++ self.items[idx + 1 ..];
                    return;
                }
                if (idx == 0) break;
            }
            self.items = &[1]usize{elem} ++ self.items;
        }

        fn replace(comptime self: *@This(), comptime idx: usize, comptime value: T) void {
            if (idx == 0)
                self.items = &[1]T{value} ++ self.items[1..]
            else if (idx == self.items.len - 1)
                self.items = self.items[0..idx] ++ &[1]T{value}
            else
                self.items = self.items[0..idx] ++ &[1]T{value} ++ self.items[idx + 1 ..];
        }

        fn remove(comptime self: *@This(), comptime idx: usize) void {
            if (idx == self.items.len - 1)
                self.items = self.items[0 .. self.items.len - 1]
            else
                self.items = self.items[0..idx] ++ self.items[idx..];
        }

        fn contains(comptime self: @This(), elem: usize) bool {
            var idx: usize = self.items.len - 1;
            return while (true) : (idx -= 1) {
                if (self.items[idx] == elem) break true;
                if (self.items[idx] < elem) break false;
                if (idx == 0) break false;
            };
        }

        fn eql(comptime lhs: @This(), comptime rhs: @This()) bool {
            return std.mem.eql(T, lhs.items, rhs.items);
        }
    };
}

/// `T` must have a concrete byte representation for branch optimization purposes
fn CtArrayList(comptime T: type) type {
    return struct {
        items: []T,
        capacity: usize,

        fn initCapacity(comptime capacity: usize) @This() {
            var self = @This(){ .items = &.{}, .capacity = 0 };
            self.ensureTotalCapacity(capacity);
            return self;
        }

        fn fromSlice(comptime s: []const T) @This() {
            var buf: [s.len]T = undefined;
            std.mem.copy(T, &buf, s);
            return .{
                .items = &buf,
                .capacity = buf.len,
            };
        }

        fn append(comptime self: *@This(), comptime t: T) void {
            self.ensureTotalCapacity(self.items.len + 1);
            self.items.len += 1;

            self.items[self.items.len - 1] = t;
        }

        fn appendNTimes(comptime self: *@This(), comptime value: T, comptime n: usize) void {
            self.ensureTotalCapacity(self.items.len + n);
            const old_len = self.items.len;
            self.items.len += n;
            // TODO: This crashes the compiler :(
            // self.items[old_len..].* = [1]bool{value} ** (self.items.len - old_len);
            for (self.items[old_len..]) |*i| i.* = value;
        }

        fn appendSlice(comptime self: *@This(), comptime ts: []const T) void {
            self.ensureTotalCapacity(self.items.len + ts.len);
            self.items.len += ts.len;
            // TODO: This crashes the compiler :(
            // self.items[self.items.len - ts.len ..].* = ts[0..ts.len].*;
            const dst = self.items[self.items.len - ts.len ..];
            std.mem.copy(T, dst, ts);
        }

        fn insert(comptime self: *@This(), comptime n: usize, comptime t: T) void {
            self.ensureTotalCapacity(self.items.len + 1);
            self.items.len += 1;

            // TODO: This crashes the compiler :(
            // const to_move = self.items[n .. self.items.len - 1].*;
            // self.items[n + 1 ..].* = to_move;
            std.mem.copyBackwards(T, self.items[n + 1 ..], self.items[n .. self.items.len - 1]);
            self.items[n] = t;
        }

        fn orderedRemove(comptime self: *@This(), comptime i: usize) void {
            const new_len = self.items.len - 1;
            if (new_len == i) {
                self.items.len -= 1;
                return;
            }

            // TODO: This crashes the compiler so we still use the loop :/
            // self.items[i..new_len].* =  self.items[i + 1 ..].*;
            for (self.items[i..new_len]) |*b, j| b.* = self.items[i + 1 + j];
            self.items[new_len] = undefined;
            self.items.len = new_len;
        }

        fn ensureTotalCapacity(comptime self: *@This(), comptime new_capacity: usize) void {
            if (self.capacity >= new_capacity) return;
            const better_capacity = std.math.ceilPowerOfTwo(usize, new_capacity) catch unreachable;

            self.capacity = better_capacity;
            var buf: [self.capacity]T = undefined;
            buf[0..self.items.len].* = self.items[0..self.items.len].*;
            self.items = buf[0..self.items.len];
        }
    };
}

fn newStateIndex(
    comptime new_states: *[]SortedList,
    comptime old_states: SortedList,
) usize {
    for (new_states.*) |old, ns| {
        if (old.eql(old_states)) return ns;
    }

    var buf: [new_states.len + 1]SortedList = ([1]SortedList{undefined} ** new_states.len) ++ [1]SortedList{old_states};
    std.mem.copy(SortedList, &buf, new_states.*);
    new_states.* = &buf;
    const new_state = new_states.len - 1;

    return new_state;
}

const SortedList = CtSortedList(usize);

// TODO: Split into more files
// TODO Thoroughly test this as well as the assumption about dead states

const TransitionSlice = struct {
    start: usize,
    len: usize,
};

/// Returns number of copied transitions
fn appendFromSourcesFixSource(
    comptime transitions: *CtArrayList(Transition),
    comptime sources: SortedList,
    comptime source: usize,
) usize {
    var inserted: usize = 0;
    const max_source = sources.items[sources.items.len - 1];
    var curr_source_idx: usize = 0;
    for (transitions.items) |t, t_idx| {
        const curr_source = sources.items[curr_source_idx];

        if (t.source == curr_source) {
            const start_idx = t_idx;
            var curr = t_idx + 1;
            while (curr < transitions.items.len and
                transitions.items[curr].source == curr_source) : (curr += 1)
            {}

            const len = curr - start_idx;
            for (transitions.items[start_idx..curr]) |t2| {
                transitions.append(.{
                    .source = source,
                    .target = t2.target,
                    .label = t2.label,
                });
            }
            inserted += len;
            curr_source_idx += 1;
        } else if (t.source > curr_source)
            curr_source_idx += 1;

        if (curr_source_idx >= sources.items.len or t.source > max_source) break;
    }
    return inserted;
}

pub fn determinize(comptime self: Self) Self {
    if (self.isDfa()) return self;

    const old_state_max = self.stateCount() - 1;
    comptime var new_states: []SortedList = blk: {
        var buf: [old_state_max + 1]SortedList = undefined;
        for (buf) |*ns, i| ns.* = .{
            .items = &.{i},
        };
        break :blk &buf;
    };

    // The procedure to determinize `self` is the following:
    //   Keep a new_state -> {old_states...} map
    //    Initialize it with forall old_state -> {old_state}
    //  For each new_state:
    //    If an old_state, find slice of transitions in `transitions`
    //    If a new_state, insert transitions from each old state, find resulting slice
    //      This slice is now named `transition_slice`
    //      If transition_slice.len < 2, continue
    //      Start with base transition = transition_slice[-1]
    //      We will iteratively do the following as long as we have a base transition and at least one more transition:
    //        Find transitions with the same label as base_transition and remove them, keeping
    //        track of their targets.
    //        If we removed any transition, look up new state from the transition targets we built up
    //        and append a new transition to `transitions`, then remove the base transition
    //        We fix the base transition index as we go to always end up at the next transition.
    //  At the end, we have our new transitions and the automaton is deterministic
    //  Some of the states may now be unreachable so they are removed.

    var transitions = CtArrayList(Transition).fromSlice(self.transitions);
    var prev_end_idx: usize = 0;
    var state: usize = 0;
    // Transitions will always be sorted, even while we are modifying them
    while (state < new_states.len) : (state += 1) {
        var transition_slice: TransitionSlice = if (state <= old_state_max) blk: {
            if (prev_end_idx >= transitions.items.len) continue;
            if (transitions.items[prev_end_idx].source != state) continue;

            // Old state, just find the transition slice
            var idx: usize = prev_end_idx + 1;
            while (idx < transitions.items.len and
                transitions.items[idx].source == state) : (idx += 1)
            {}
            break :blk .{ .start = prev_end_idx, .len = idx - prev_end_idx };
        } else blk: {
            // New state, construct the transition slice by inserting at `prev_end_idx + 1`
            // We copy here and not when creating the new transition to get the already reduced transitions
            //   from previous states
            const inserted = appendFromSourcesFixSource(&transitions, new_states[state], state);
            break :blk .{ .start = prev_end_idx, .len = inserted };
        };
        defer prev_end_idx = transition_slice.start + transition_slice.len;

        // We cannot reduce from a single item
        if (transition_slice.len < 2) continue;

        // Reduce loop
        // Set our first base transition idx
        var base_transition_idx = transition_slice.start + transition_slice.len - 1;
        while (base_transition_idx > transition_slice.start) {
            const base_transition = transitions.items[base_transition_idx];
            // Track targets of equivalent transitions
            var old_targets = SortedList{ .items = &.{base_transition.target} };

            // Find and remove transitions with the same label as the base transition
            var transition_idx = base_transition_idx - 1;
            while (true) : (transition_idx -= 1) {
                const curr_transition = &transitions.items[transition_idx];

                if (base_transition.label == curr_transition.label) {
                    old_targets.append(curr_transition.target);
                    // We don't need to manipulate transition_idx because we are looping backwards
                    transitions.orderedRemove(transition_idx);
                    transition_slice.len -= 1;
                    // We removed a transition with an index less than the base transitions,
                    //   move base transition index up to match this
                    base_transition_idx -= 1;
                }
                if (transition_idx == transition_slice.start) break;
            }

            // Check if we removed any transitions
            if (old_targets.items.len > 1) {
                // If we did, add our new transition to a combined state in our current transition_slice
                // transition_slice stays the same because we add then remove a transition in the slice
                transitions.insert(transition_slice.start + transition_slice.len, .{
                    .source = state,
                    .target = newStateIndex(&new_states, old_targets),
                    .label = base_transition.label,
                });

                // Remove base transition
                // Base transition index stays the same since we removed the current base
                transitions.orderedRemove(base_transition_idx);
                continue;
            }
            base_transition_idx -= 1;
        }
    }

    var final_states = SortedList{};
    for (self.final_states) |old_fs| {
        for (new_states) |old_states, ns| {
            if (old_states.contains(old_fs))
                final_states.append(ns);
        }
    }

    minimize(&transitions, &final_states, new_states.len);

    return .{
        .final_states = final_states.items,
        .transitions = transitions.items,
    };
}

// Dfa minimization
// Ported "Fast brief practical DFA minimization" by Antti Valmari
// See: https://www.cs.cmu.edu/~cdm/papers/Valmari12.pdf

// We will create one partition for states and one for transitions
const Partition = struct {
    const Array = []usize;
    partition_count: usize, // `z`
    elements: Array, // `E`
    first: Array, // `F`
    past: Array, // `P`
    locations: Array, // 'L'
    set_of_elem: Array, // `S`

    fn init(comptime n: usize) Partition {
        var self: Partition = undefined;
        self.partition_count = @boolToInt(n != 0);

        var index_init: [n]usize = undefined;
        for (index_init) |*e, i| e.* = i;

        self.elements = blk: {
            var buf = index_init;
            break :blk &buf;
        };
        self.locations = blk: {
            var buf = index_init;
            break :blk &buf;
        };
        self.set_of_elem = blk: {
            var buf = std.mem.zeroes([n]usize);
            break :blk &buf;
        };

        if (n != 0) {
            self.first = blk: {
                var buf = std.mem.zeroes([n]usize);
                break :blk &buf;
            };
            self.past = blk: {
                var buf = [1]usize{n} ** n;
                break :blk &buf;
            };
        }

        return self;
    }

    fn mark(
        self: *Partition,
        e: usize,
        marked_elements: [*]usize, // M
        touched_sets: *[]usize, // W + w
    ) void {
        const s = self.set_of_elem[e];
        const i = self.locations[e];
        const j = self.first[s] + marked_elements[s];
        self.elements[i] = self.elements[j];
        self.locations[self.elements[i]] = i;
        self.elements[j] = e;
        self.locations[e] = j;

        const marked = marked_elements[s] != 0;
        marked_elements[s] += 1;
        if (!marked) {
            touched_sets.*.len += 1;
            touched_sets.*[touched_sets.*.len - 1] = s;
        }
    }

    fn split(
        self: *Partition,
        marked_elements: [*]usize, // M
        touched_sets: *[]usize, // W + w
    ) void {
        while (touched_sets.len > 0) {
            const s = touched_sets.*[touched_sets.*.len - 1];
            touched_sets.*.len -= 1;
            const j = self.first[s] + marked_elements[s];

            if (j == self.past[s]) {
                marked_elements[s] = 0;
                continue;
            }

            if (marked_elements[s] <= self.past[s] - j) {
                self.first[self.partition_count] = self.first[s];
                self.past[self.partition_count] = j;
                self.first[s] = j;
            } else {
                self.past[self.partition_count] = self.past[s];
                self.first[self.partition_count] = j;
                self.past[s] = j;
            }

            var i: usize = self.first[self.partition_count];
            while (i < self.past[self.partition_count]) : (i += 1) {
                self.set_of_elem[self.elements[i]] = self.partition_count;
            }
            marked_elements[s] = 0;
            marked_elements[self.partition_count] = 0;
            self.partition_count += 1;
        }
    }
};

fn cmp(transitions: []const Transition, i: usize, j: usize) bool {
    return transitions[i].label < transitions[j].label;
}

fn makeAdjacent(
    transitions: []const Transition,
    comptime field: []const u8,
    A: [*]usize,
    F: []usize, // nn = F.len - 1
) void {
    var q: usize = 0;
    var t: usize = 0;
    while (q <= F.len - 1) : (q += 1)
        F[q] = 0;
    while (t < transitions.len) : (t += 1)
        F[@field(transitions[t], field)] += 1;
    q = 0;
    while (q < F.len - 1) : (q += 1)
        F[q + 1] += F[q];
    t = transitions.len;
    while (t != 0) {
        t -= 1;
        F[@field(transitions[t], field)] -= 1;
        A[F[@field(transitions[t], field)]] = t;
    }
}

fn reach(
    blocks: *Partition,
    q: usize,
    reached_states: *usize,
) void {
    const i = blocks.locations[q];
    if (i >= reached_states.*) {
        blocks.elements[i] = blocks.elements[reached_states.*];
        blocks.locations[blocks.elements[i]] = i;
        blocks.elements[reached_states.*] = q;
        blocks.locations[q] = reached_states.*;
        reached_states.* += 1;
    }
}

fn removeUnreachable(
    blocks: *Partition,
    transitions: *[]Transition,
    comptime T: []const u8,
    comptime H: []const u8,
    reached_states: *usize,
    A: [*]usize,
    F: []usize, // nn = F.len - 1
) void {
    makeAdjacent(transitions.*, T, A, F);
    var i: usize = 0;
    var j: usize = undefined;
    while (i < reached_states.*) : (i += 1) {
        j = F[blocks.elements[i]];
        while (j < F[blocks.elements[i] + 1]) : (j += 1) {
            reach(blocks, @field(transitions.*[A[j]], H), reached_states);
        }
    }

    j = 0;
    var t: usize = 0;
    while (t < transitions.*.len) : (t += 1) {
        if (blocks.locations[@field(transitions.*[t], T)] < reached_states.*) {
            transitions.*[j] = transitions.*[t];
            j += 1;
        }
    }
    transitions.*.len = j;
    blocks.past[0] = reached_states.*;
    reached_states.* = 0;
}
fn minimize(
    comptime transitions: *CtArrayList(Transition),
    comptime final_states: *SortedList,
    comptime initial_state_count: usize,
) void {
    // nn = self.stateCount();
    // mm = self.transitions.items.len
    // q0 = 0
    // T = transitions.items | @field($, "source")
    // H = transitions.items | @field($, "target")
    // L = transitions.items | @field($, "label")

    var reached_states: usize = 0;
    // States partition
    var blocks = Partition.init(initial_state_count);

    const F: []usize = blk: {
        var buf: [initial_state_count + 1]usize = undefined;
        break :blk &buf;
    };

    const A: [*]usize = blk: {
        var buf: [transitions.items.len]usize = undefined;
        break :blk &buf;
    };

    // We only run the forward pass to remove unreachable states, we know there are no dead states
    reach(&blocks, 0, &reached_states);
    removeUnreachable(
        &blocks,
        &transitions.items,
        "source",
        "target",
        &reached_states,
        A,
        F,
    );
    const state_count = reached_states;

    var marked_elements: [*]usize = blk: {
        var buf: [transitions.items.len + 1]usize = undefined;
        buf[0] = state_count;
        break :blk &buf;
    };

    // Make initial transition partition
    var touched_sets: []usize = blk: {
        var buf: [transitions.items.len + 1]usize = undefined;
        buf[0] = 0;
        break :blk buf[0..1];
    };
    blocks.split(marked_elements, &touched_sets);

    var cords = Partition.init(transitions.items.len);
    std.sort.sort(usize, cords.elements, transitions.items, cmp);

    marked_elements[0] = 0;
    cords.partition_count = 0;
    var a = transitions.items[cords.elements[0]].label;
    var i: usize = 0;
    while (i < transitions.items.len) : (i += 1) {
        const t = cords.elements[i];
        if (transitions.items[t].label != a) {
            a = transitions.items[t].label;
            cords.past[cords.partition_count] = i;
            cords.partition_count += 1;
            cords.first[cords.partition_count] = i;
            marked_elements[cords.partition_count] = 0;
        }
        cords.set_of_elem[t] = cords.partition_count;
        cords.locations[t] = i;
    }
    cords.past[cords.partition_count] = transitions.items.len;
    cords.partition_count += 1;

    // Split blocks and cords
    makeAdjacent(transitions.items, "target", A, F);
    var b: usize = 1;
    var c: usize = 0;
    var j: usize = undefined;

    while (c < cords.partition_count) {
        i = cords.first[c];
        while (i < cords.past[c]) : (i += 1)
            blocks.mark(transitions.items[cords.elements[i]].source, marked_elements, &touched_sets);

        blocks.split(marked_elements, &touched_sets);
        c += 1;
        while (b < blocks.partition_count) {
            i = blocks.first[b];
            while (i < blocks.past[b]) : (i += 1) {
                j = F[blocks.elements[i]];
                while (j < F[blocks.elements[i] + 1]) : (j += 1)
                    cords.mark(A[j], marked_elements, &touched_sets);
            }
            cords.split(marked_elements, &touched_sets);
            b += 1;
        }
    }

    // If not zero, we will have to swap it with new state zero
    const new_start_state = blocks.set_of_elem[0];
    // We use this to swap 0 and new_start_state if new_start_state != 0
    const new_state = struct {
        fn f(nss: usize, set_of_elem: []usize, old_state: usize) usize {
            const new = set_of_elem[old_state];
            if (nss == 0) return new;
            return if (new == nss) 0 else if (new == 0) nss else new;
        }
    }.f;

    var out_idx: usize = 0;
    var t: usize = 0;
    while (t < transitions.items.len) : (t += 1) {
        const transition = &transitions.items[t];
        if (blocks.locations[transition.source] ==
            blocks.first[blocks.set_of_elem[transition.source]])
        {
            transition.source = new_state(new_start_state, blocks.set_of_elem, transition.source);
            transition.target = new_state(new_start_state, blocks.set_of_elem, transition.target);
            if (out_idx != t) {
                transitions.items[out_idx] = transition.*;
            }
            out_idx += 1;
        }
    }
    transitions.items = transitions.items[0..out_idx];
    std.sort.sort(
        Transition,
        transitions.items,
        {},
        transitionLessThan,
    );

    var fs_idx: usize = 0;
    while (fs_idx < final_states.items.len) {
        const fs = final_states.items[fs_idx];
        // Remove
        if (blocks.first[fs] >= initial_state_count) {
            final_states.remove(fs_idx);
            continue;
        }
        const new_fs = new_state(new_start_state, blocks.set_of_elem, fs);
        final_states.replace(fs_idx, new_fs);
        fs_idx += 1;
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
