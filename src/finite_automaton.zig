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

// TODO 'string'?
pub const Input = union(enum) {
    single: u21,
    range: struct {
        start: u21,
        /// `end` is inclusive
        end: u21,
    },
    any_of: []const Input,

    fn reduce(comptime self: Input) ?Input {
        return switch (self) {
            .single => self,
            .range => |r| if (r.start == r.end) null else self,
            .any_of => |seq| blk: {
                if (seq.len == 0) break :blk null;
                var res: []const Input = &.{};
                for (seq) |i| {
                    if (reduce(i)) |r| res = res ++ &.{r};
                }
                break :blk res;
            },
        };
    }

    // TODO: Overlap removal tests
    fn removeOverlap(comptime self: Input, comptime _overlap: Input) ?Input {
        switch (_overlap) {
            .any_of => |seq| {
                var curr: ?Input = self;
                for (seq) |o| {
                    curr = curr.removeOverlap(o);
                    if (curr == null) break;
                }
                return curr;
            },
            else => {},
        }

        return switch (self) {
            .single => |c| switch (_overlap) {
                .single => |o| if (o == c) null else self,
                .range => |o| if (c >= o.start and c <= o.end) null else self,
                .any_of => unreachable,
            },
            .range => |r| switch (_overlap) {
                .single => |o| if (o >= r.start and o <= r.end) blk: {
                    const ret = switch (o) {
                        r.start => Input{ .range = .{ .start = r.start + 1, .end = r.end } },
                        r.end => Input{ .range = .{ .start = r.start, .end = r.end - 1 } },
                        else => Input{ .any_of = &.{
                            .{ .range = .{
                                .start = r.start,
                                .end = o - 1,
                            } },
                            .{ .range = .{ .start = o + 1, .end = r.end } },
                        } },
                    };
                    break :blk reduce(ret);
                } else self,
                .range => |o| if (o.start <= r.end)
                    reduce(.{ .range = .{
                        .start = std.math.min(r.start, o.start),
                        .end = o.start,
                    } })
                else if (r.start <= o.end)
                    reduce(.{ .range = .{
                        .start = std.math.min(r.start, o.start),
                        .end = std.math.max(r.end, o.end),
                    } })
                else
                    self,
                .any_of => unreachable,
            },
            .any_of => |seq| blk: {
                const res: []const Input = &.{};
                for (seq) |i| {
                    if (i.removeOverlap(_overlap)) |new| res = res ++ &[1]Input{new};
                }
                break :blk reduce(.{ .any_of = res });
            },
        };
    }

    fn overlap(comptime lhs: Input, comptime rhs: Input) ?Input {
        if (rhs == .any_of) return overlap(rhs, lhs);

        return switch (lhs) {
            .any_of => |seq| {
                var seq_overlaps_buf: [seq.len]Input = undefined;
                var seq_overlaps_idx: usize = 0;
                for (seq) |e| {
                    if (e.overlap(rhs)) |o| {
                        seq_overlaps_buf[seq_overlaps_idx] = o;
                        seq_overlaps_idx += 1;
                    }
                }
                return switch (seq_overlaps_idx) {
                    0 => null,
                    1 => seq_overlaps_buf[0],
                    else => .{ .any_of = seq_overlaps_buf[0..seq_overlaps_idx] },
                };
            },
            .single => |cl| switch (rhs) {
                .single => |cr| if (cl == cr) .{ .single = cl } else null,
                .range => |rr| if (cl >= rr.start and cl <= rr.end) .{ .single = cl } else null,
                .any_of => unreachable,
            },
            .range => |rl| switch (rhs) {
                .single => |cr| if (cr >= rl.start and cr <= rl.end) .{ .single = cr } else null,
                .range => |rr| if (rr.start <= rl.end) .{
                    .range = .{ .start = rr.start, .end = rl.end },
                } else if (rl.start <= rr.end) .{
                    .range = .{ .start = rl.start, .end = rr.end },
                } else null,
                .any_of => unreachable,
            },
        };
    }
};

pub const Transition = struct {
    source: usize,
    target: usize,

    input: Input,
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
                .input = t.input,
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

pub fn input(comptime i: Input) Self {
    return .{ .final_states = &.{1}, .transitions = &.{.{
        .source = 0,
        .target = 1,
        .input = i,
    }} };
}

pub fn single(comptime c: u21) Self {
    return .{ .final_states = &.{1}, .transitions = &.{.{
        .source = 0,
        .target = 1,
        .input = .{ .single = c },
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
                .input = t.input,
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

fn allInputsLessThan(comptime self: Self, ceil: u21) bool {
    for (self.transitions) |t| {
        switch (t.input) {
            .single => |c| if (c > ceil) return false,
            .range => |r| {
                if (r.start > ceil) return false;
                if (r.end > ceil) return false;
            },
            .any_of => |seq| {
                for (seq) |i| {
                    if (!i.allInputsLessThan(ceil)) return false;
                }
            },
        }
    }
    return true;
}

pub fn singleCharBoundInEncoding(comptime self: Self, comptime encoding: Encoding) bool {
    return switch (encoding) {
        .ascii, .utf8 => self.allInputsLessThan(127),
        .utf16le => {
            const helper = struct {
                fn f(i: Input) bool {
                    switch (i) {
                        .single => |c| if (c > 0xd7ff and c < 0xe000) return false,
                        .range => |r| {
                            // We assume r.start < r.end
                            // Range start in first u16 range, end outside
                            if (r.start <= 0xd7ff and r.end > 0xd7ff) return false;
                            // Range start in u16 gap
                            if (r.start > 0xd7ff and r.start < 0xe000) return false;
                            // The range start must be in second u16 range, so the end better be too
                            if (r.end < 0xe000) return false;
                            return true;
                        },
                        .any_of => |seq| {
                            for (seq) |s| if (!f(s)) return false;
                            return true;
                        },
                    }
                    return true;
                }
            }.f;
            // Single u16's are used in the ranges [0x0000, 0xD7FF] and [0xE000, 0xFFFF]
            for (self.transitions) |t| {
                if (!helper(t.input)) return false;
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
                    if (t1.input.overlap(state_transitions[idx].input) != null) return false;
                }
            }
            // Trigger checks here before resetting state
            start = i;
            state = t.source;
        }
    }
    return true;
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
                .input = .{ .single = 'a' },
            },
        } }, a);

        const b = single('b');
        const @"a·b" = concat(a, b);
        try expectEqualAutomata(.{ .final_states = &.{2}, .transitions = &.{
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
        } }, @"a·b");

        const @"a|b" = alt(a, b);
        try expectEqualAutomata(.{ .final_states = &.{ 1, 2 }, .transitions = &.{
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
        } }, @"a|b");

        const @"a?" = opt(a);
        try expectEqualAutomata(.{ .final_states = &.{ 0, 1 }, .transitions = &.{
            .{
                .source = 0,
                .target = 1,
                .input = .{ .single = 'a' },
            },
        } }, @"a?");

        const @"a*" = star(a);
        try expectEqualAutomata(.{ .final_states = &.{ 0, 1 }, .transitions = &.{
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
        } }, @"a*");

        const @"a+" = plus(a);
        try expectEqualAutomata(.{ .final_states = &.{1}, .transitions = &.{
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
            self.ensureCapacity(capacity);
            return self;
        }

        fn initFromSlice(comptime s: []const T) @This() {
            var buf: [s.len]T = undefined;
            std.mem.copy(T, &buf, s);
            return .{
                .items = &buf,
                .capacity = buf.len,
            };
        }

        fn append(comptime self: *@This(), comptime t: T) void {
            self.ensureCapacity(self.items.len + 1);
            self.items.len += 1;

            self.items[self.items.len - 1] = t;
        }

        fn appendSlice(comptime self: *@This(), comptime ts: []const T) void {
            self.ensureCapacity(self.items.len + ts.len);
            self.items.len += ts.len;
            const dst = self.items[self.items.len - ts.len ..];
            std.mem.copy(T, dst, ts);
        }

        fn insert(comptime self: *@This(), comptime n: usize, comptime t: T) void {
            self.ensureCapacity(self.items.len + 1);
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

        fn ensureCapacity(comptime self: *@This(), comptime new_capacity: usize) void {
            if (new_capacity > self.capacity) {
                self.capacity = std.mem.alignForward(new_capacity, 8);
                var buf: [self.capacity]T = undefined;
                std.mem.copy(T, &buf, self.items);
                self.items = buf[0..self.items.len];
            }
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
pub fn determinize(comptime self: Self) Self {
    if (self.isDfa()) return self;

    const old_state_max = self.size() - 1;

    // TODO: Do everything in place in old_transitions?
    var old_transitions = CtArrayList(Transition).initFromSlice(self.transitions);
    var new_transitions = CtArrayList(Transition).initCapacity(16);

    comptime var new_states: []SortedList = blk: {
        var buf: [old_state_max + 1]SortedList = undefined;
        for (buf) |*ns, i| ns.* = .{
            .items = &.{i},
        };
        break :blk &buf;
    };

    // TODO: Do this in place in old_transitions, no new_transitions
    //   For new states, first copy from old transitions then reduce again
    //   currently new states don't reduce at all

    // Go through all states
    // Go backwards to reduce the amount of moves when removing transitions
    var state: usize = 0;
    while (state <= old_state_max) : (state += 1) {
        var transition_slice: struct {
            start: usize,
            len: usize,
        } = blk: {
            // TODO: Go the other way?
            var idx: usize = old_transitions.items.len - 1;
            while (true) : (idx -= 1) {
                if (old_transitions.items[idx].source < state) break;
                if (old_transitions.items[idx].source == state) {
                    const end = idx + 1;
                    const start = while (old_transitions.items[idx].source == state) : (idx -= 1) {
                        if (idx == 0) break 0;
                    } else idx + 1;
                    break :blk .{ .start = start, .len = end - start };
                }

                if (idx == 0) break;
            }
            break :blk .{ .start = undefined, .len = 0 };
        };
        if (transition_slice.len == 0) continue;

        var base_transition_idx = transition_slice.start + transition_slice.len - 1;
        while (base_transition_idx > transition_slice.start) {
            const base_transition = old_transitions.items[base_transition_idx];

            var accumulated_overlap = base_transition.input;
            var old_targets = SortedList{ .items = &.{base_transition.target} };

            // Resolve one overlap
            var transition_idx = base_transition_idx - 1;
            while (true) : (transition_idx -= 1) {
                const curr_transition = &old_transitions.items[transition_idx];

                if (accumulated_overlap.overlap(curr_transition.input)) |overlap| blk: {
                    accumulated_overlap = overlap;
                    old_targets.append(curr_transition.target);

                    curr_transition.input = curr_transition.input.removeOverlap(overlap) orelse {
                        // We don't need to manipulate transition_idx because we are looping backwards
                        old_transitions.orderedRemove(transition_idx);
                        transition_slice.len -= 1;
                        // We removed a transition with an index less than the base transition,
                        //   move base transition up
                        base_transition_idx -= 1;
                        break :blk;
                    };
                }

                if (transition_idx <= transition_slice.start) break;
            }

            // We had some overlap
            if (old_targets.items.len > 1) {
                // Add our new transition to a combined state
                new_transitions.append(.{
                    .source = state,
                    .target = newStateIndex(&new_states, old_targets),
                    .input = accumulated_overlap,
                });

                // Clean up base transition
                old_transitions.items[base_transition_idx] = base_transition.input.removeOverlap(
                    accumulated_overlap,
                ) orelse {
                    // We removed the base tradition, our new base is at the same index
                    old_transitions.orderedRemove(base_transition_idx);
                    transition_slice.len -= 1;
                    continue;
                };
                // We didn't remove the base transition, go to next base
                base_transition_idx -= 1;
            } else {
                base_transition_idx -= 1;
            }
        }

        // Copy remaining transitions in result automaton transitions
        // These are guaranteed not to overlap
        if (transition_slice.len != 0)
            new_transitions.appendSlice(old_transitions.items[transition_slice.start..][0..transition_slice.len]);
    }

    var final_states = SortedList{};
    for (self.final_states) |old_fs| {
        for (new_states) |old_states, ns| {
            if (old_states.contains(old_fs))
                final_states.append(ns);
        }
    }

    // Add transitions for new states
    // These are used for transitionsFrom
    const temp_self = Self{
        .transitions = new_transitions.items,
        .final_states = final_states.items,
    };

    // TODO: Prove that this is correct (no unreachable nodes, sorting preserve)
    //   New states could potentially be dead, look for example
    // For new states, copy over remaining transitions from corresponding old states
    for (new_states[old_state_max + 1 ..]) |old_states, off| {
        const new_state = off + old_state_max + 1;

        const start_source_fix = new_transitions.items.len;
        for (old_states.items) |old_state| {
            new_transitions.appendSlice(temp_self.transitionsFrom(old_state));
        }
        for (new_transitions.items[start_source_fix..]) |*t| t.source = new_state;
    }

    return .{
        .final_states = final_states.items,
        .transitions = new_transitions.items,
    };
}

// TODO: See if we can make all algorithms guarantee that
//   1) their outputs contain no dead or unreachable states if their inputs don't
//   2) their transitions are sorted and were so without std.sort.sort call
// If 1 is not possible, we will need removeDeadStates and/or removeUnreachableStates and call it where needed

// TODO: assertNoDeadOrUnreachableStates()
