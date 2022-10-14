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
const Label = u21;

// TODO: Remove memcpys for [..].* = [..].*; where possible
pub const Transition = struct {
    source: usize,
    target: usize,

    label: Label,
};

final_states: []const usize,
transitions: []const Transition,

// TODO New names
//   Unreachable state: Cannot be reached from the start state through any set of transitions
//   Dead state: Cannot reach any final state through any set of transitions
// Document guarantees about dead and unreachable nodes for every function, remove them when necessary in here

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
    const rhs_offset = lhs.size() - if (rhs_start_reachable) 0 else 1;

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
        std.mem.copy(usize, &final_states, lhs.final_states);
        for (final_states[lhs.final_states.len..][0 .. rhs.final_states.len - rhs_final_state_offset]) |*s, idx|
            s.* = rhs.final_states[idx + rhs_final_state_offset] + rhs_offset;
    } else for (final_states[0 .. rhs.final_states.len - rhs_final_state_offset]) |*s, idx|
        s.* = rhs.final_states[idx + rhs_final_state_offset] + rhs_offset;

    // If the rhs start state is not reachable, we remove its transitions from the rhs portion
    const new_transition_count = lhs.final_states.len * rhs_start_transitions.len;
    const copy_from_rhs_count = if (rhs_start_reachable) rhs.transitions.len else rhs.transitions.len - rhs_start_transitions.len;
    var transitions: [lhs.transitions.len + copy_from_rhs_count + new_transition_count]Transition = undefined;
    std.mem.copy(Transition, &transitions, lhs.transitions);

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

    // TODO: Interleaf copies from original, then when in final state copy the new ones, then till next final state etc.
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
    const rhs_offset = lhs.size() + lhs_offset - if (rhs_start_reachable) 0 else 1;

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

pub fn isFinal(comptime self: Self, comptime state: usize) bool {
    for (self.final_states) |s| {
        if (s == state) return true;
        if (s > state) return false;
    }
    return false;
}

pub fn size(comptime self: Self) usize {
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

// Always iterate with indices
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
            std.mem.set(T, self.items[old_len..self.items.len], value);
        }

        fn appendSlice(comptime self: *@This(), comptime ts: []const T) void {
            self.ensureTotalCapacity(self.items.len + ts.len);
            self.items.len += ts.len;
            const dst = self.items[self.items.len - ts.len ..];
            std.mem.copy(T, dst, ts);
        }

        fn insert(comptime self: *@This(), comptime n: usize, comptime t: T) void {
            self.ensureTotalCapacity(self.items.len + 1);
            self.items.len += 1;
            std.mem.copyBackwards(T, self.items[n + 1 .. self.items.len], self.items[n .. self.items.len - 1]);
            self.items[n] = t;
        }

        fn orderedRemove(comptime self: *@This(), comptime i: usize) void {
            const new_len = self.items.len - 1;
            if (new_len == i) {
                self.items.len -= 1;
                return;
            }

            for (self.items[i..new_len]) |*b, j| b.* = self.items[i + 1 + j];
            self.items[new_len] = undefined;
            self.items.len = new_len;
        }

        fn ensureTotalCapacity(comptime self: *@This(), comptime new_capacity: usize) void {
            if (self.capacity >= new_capacity) return;
            const better_capacity = std.math.ceilPowerOfTwo(usize, new_capacity) catch unreachable;

            self.capacity = better_capacity;
            var buf: [self.capacity]T = undefined;
            std.mem.copy(T, &buf, self.items);
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

// TODO Prune stuff
// TODO minimize function
// TODO: Split into more files
// TODO Thoroughly test this as well as the assumption about dead states

const TransitionSlice = struct {
    start: usize,
    len: usize,
};

// TODO: Check this
/// Returns number of copied transitions
fn appendFromSources(
    comptime transitions: *CtArrayList(Transition),
    comptime sources: SortedList,
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
            if (len == 1) {
                transitions.append(t);
            } else {
                transitions.appendSlice(transitions.items[start_idx..curr]);
            }
            inserted += len;
            curr_source_idx += 1;
        } else if (t.source > curr_source) {
            curr_source_idx += 1;
        }

        if (curr_source_idx >= sources.items.len or t.source > max_source) break;
    }
    return inserted;
}

pub fn determinize(comptime self: Self) Self {
    if (self.isDfa()) return self;

    const old_state_max = self.size() - 1;
    comptime var new_states: []SortedList = blk: {
        var buf: [old_state_max + 1]SortedList = undefined;
        for (buf) |*ns, i| ns.* = .{
            .items = &.{i},
        };
        break :blk &buf;
    };

    // The procedure to determinize `self` is the following:
    //   Keep a new_state -> {old_states...} map
    //    Initialize it with old_state -> {old_state}
    //  For each new_state:
    //    If an old_state, find slice of transitions in `transitions`
    //    If a new_state, insert transitions from each old state, find resulting slice
    //      This slice is now named `transition_slice`
    //      If transition_slice.len < 2, continue
    //      Start with base transition = transition_slice[-1]
    //      We will iteratively do the following as long as we have a base transition and at least one more transition:
    //        Find transitions with the same label as base_transition, removing equivalent transitions as we go, keeping
    //        track of the old targers.
    //        If we found any equivalent transitions, look up new state from the targets of the equivalent transitions
    //        and append a new transition to `transitions`, then remove the base transition
    //        We fix the base transition index as we go.
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
            const start_source_fix = prev_end_idx;
            const inserted = appendFromSources(
                &transitions,
                new_states[state],
            );
            // Fix transition sources
            for (transitions.items[start_source_fix..][0..inserted]) |*t|
                t.source = state;
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
                transition_slice.len += 1;

                // Remove base transition
                // Base transition index stays the same since we removed the current base
                transitions.orderedRemove(base_transition_idx);
                transition_slice.len -= 1;
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

    removeUnreachableStates(&transitions, &final_states);

    return .{
        .final_states = final_states.items,
        .transitions = transitions.items,
    };
}

fn removeUnreachableStates(
    comptime transitions: *CtArrayList(Transition),
    comptime final_states: *SortedList,
) void {
    var state_reachable = CtArrayList(bool).fromSlice(&.{true});
    var max_state: usize = 0;
    while (true) {
        var new_reachable = false;
        var t_idx: usize = 0;
        while (t_idx < transitions.items.len) : (t_idx += 1) {
            const t = transitions.items[t_idx];

            if (t.source > max_state) max_state = t.source;
            if (t.target > max_state) max_state = t.target;

            if (max_state + 1 > state_reachable.items.len) {
                const new_len = max_state + 1;
                state_reachable.appendNTimes(false, new_len - state_reachable.items.len);
            }

            if (state_reachable.items[t.source] and !state_reachable.items[t.target]) {
                state_reachable.items[t.target] = true;
                new_reachable = true;
            }
        }
        if (!new_reachable) break;
    }

    // Compute map from old to new states
    const new_states = blk: {
        var buf: [max_state + 1]usize = undefined;
        var new_state: usize = 0;
        for (state_reachable.items) |r, i| {
            buf[i] = new_state;
            if (r)
                new_state += 1;
        }
        break :blk buf;
    };

    // Remove transitions and fix states at the same time
    var t_idx: usize = 0;
    while (t_idx < transitions.items.len) {
        const t = &transitions.items[t_idx];

        if (!state_reachable.items[t.source] or !state_reachable.items[t.target]) {
            transitions.orderedRemove(t_idx);
            continue;
        }

        t.source = new_states[t.source];
        t.target = new_states[t.target];

        t_idx += 1;
    }

    var new_final_states = SortedList{ .items = &.{} };
    for (final_states.items) |fs| {
        if (!state_reachable.items[fs]) continue;
        new_final_states.append(new_states[fs]);
    }
    final_states.* = new_final_states;
}

// TODO Uses "Fast brief practical DFA minimization" by Valmari
//  https://www.cs.cmu.edu/~cdm/papers/Valmari12.pdf
