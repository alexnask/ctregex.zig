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

    // Check if a single input char can trigger both inputs
    fn overlaps(lhs: Input, rhs: Input) bool {
        if (rhs == .any_of) return overlaps(rhs, lhs);

        return switch (lhs) {
            .any_of => |seq| {
                for (seq) |e| if (e.overlaps(rhs)) return true;
                return false;
            },
            .single => |cl| switch (rhs) {
                .single => |cr| cl == cr,
                .range => |rr| cl >= rr.start and cl <= rr.end,
                .any_of => unreachable,
            },
            .range => |rl| switch (rhs) {
                .single => |cr| cr >= rl.start and cr <= rl.end,
                .range => |rr| rr.start <= rl.end or rl.start <= rr.end,
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

pub fn concat(comptime lhs: Self, comptime rhs: Self) Self {
    // Offset to be added to states from rhs
    const rhs_offset = lhs.size();

    // For every final state of lhs, we copy the transitions from rhs' start state
    // Also, if rhs' start state is also final we keep lhs' final states final instead of removing them
    const rhs_start_final = rhs.isFinal(0);
    var final_states: [rhs.final_states.len + if (rhs_start_final) lhs.final_states.len else 0]usize = undefined;
    if (rhs_start_final) {
        // If both lhs and rhs final states are sorted, the result will be sorted
        std.mem.copy(usize, &final_states, lhs.final_states);
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
    ]usize = undefined;

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
    var final_states: [self.final_states.len + 1]usize = undefined;
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
    var final_states: [self.final_states.len + offset]usize = undefined;
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

fn leadsToFinal(
    comptime self: Self,
    comptime state: usize,
    comptime visited: []const usize,
) bool {
    if (self.isFinal(state)) return true;
    const state_visited = for (visited) |v| {
        if (v == state) break true;
    } else false;
    // We hit a cycle
    if (state_visited) return false;

    for (self.transitionsFrom(state)) |t| {
        if (self.isFinal(t.target)) return true;
        if (t.source == t.target) continue;
        if (self.leadsToFinal(t.target, visited ++ &[1]usize{state})) return true;
    }
    return false;
}

pub fn removeDeadStates(comptime self: Self) Self {
    // We find all states reachable from transitions from the start state,
    //   and mark them as reachable if they lead to a final state.
    var state_reachable: []bool = b: {
        var res = [1]bool{true};
        break :b &res;
    };
    var max_state: usize = 0;
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

        // We also filter out states which do not lead to any final state through any transition
        if (state_reachable[t.source] and self.leadsToFinal(t.target, &.{t.source})) {
            state_reachable[t.target] = true;
        }
    }

    // Map from current states to new states
    const new_state = block: {
        var res: [max_state + 1]usize = undefined;
        var already_removed = 0;
        for (res) |*new, old| {
            if (!state_reachable[old])
                already_removed += 1;
            new.* = old - already_removed;
        }
        break :block res;
    };

    // Filter final states
    var final_states: [self.final_states.len]usize = undefined;
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

pub fn isDfa(comptime self: Self) bool {
    var start: usize = 0;
    var state = 0;
    for (self.transitions) |t, i| {
        if (t.source != state) {
            const state_transitions = self.transitions[start..i];
            for (state_transitions) |t1, j| {
                var idx = j + 1;
                while (idx < state_transitions.len) : (idx += 1) {
                    if (t1.input.overlaps(state_transitions[idx].input)) return false;
                }
            }
            // Trigger checks here before resetting state
            start = i;
            state = t.source;
        }
    }
    return true;
}

fn isFinal(comptime self: Self, comptime state: usize) bool {
    // Assume this is sorted
    for (self.final_states) |s| {
        if (s > state) return false;
        if (s == state) return true;
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

/// Assumes `sources` is sorted
fn transitionsFromMulti(comptime self: Self, comptime sources: []const usize) []Transition {
    var res: []Transition = &.{};
    var idx: usize = 0;
    var source_idx: usize = 0;
    while (idx < self.transitions.len and source_idx < sources.len) {
        if (self.transitions[idx].source == sources[source_idx]) {
            const start = idx;
            while (idx < self.transitions.len and self.transitions[idx].source == sources[source_idx]) : (idx += 1) {}
            var buf: [res.len + idx - start]Transition = undefined;
            std.mem.copy(Transition, &buf, res);
            std.mem.copy(Transition, buf[res.len..], self.transitions[start..idx]);
            res = &buf;
            source_idx += 1;
            continue;
        } else if (self.transitions[idx].source > sources[source_idx]) {
            source_idx += 1;
            continue;
        }
        idx += 1;
    }
    return res;
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
        const @"a·b" = concat(a, b).removeDeadStates();
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

        const @"a|b" = alt(a, b).removeDeadStates();
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

        const @"a?" = opt(a).removeDeadStates();
        try expectEqualAutomata(.{ .final_states = &.{ 0, 1 }, .transitions = &.{
            .{
                .source = 0,
                .target = 1,
                .input = .{ .single = 'a' },
            },
        } }, @"a?");

        const @"a*" = star(a).removeDeadStates();
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

        const @"a+" = plus(a).removeDeadStates();
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

// TODO: Move to some utility.zig file
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

        fn init(comptime s: []const T) @This() {
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
            // @@@
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
    comptime new_states: *[]CtSortedList(usize),
    comptime old_states: CtSortedList(usize),
    comptime transitions: *CtArrayList(Transition),
) usize {
    for (new_states.*) |old, ns| {
        if (old.eql(old_states)) return ns;
    }

    var buf: [new_states.len + 1]CtSortedList(usize) = ([1]CtSortedList(usize){undefined} ** new_states.len) ++ [1]CtSortedList(usize){old_states};
    std.mem.copy(CtSortedList(usize), &buf, new_states.*);
    new_states.* = &buf;
    const new_state = new_states.len - 1;

    var transition_idx: usize = 0;
    var old_state_idx: usize = 0;
    while (transition_idx < transitions.items.len and old_state_idx < old_states.items.len) {
        const transition = transitions.items[transition_idx];
        const old_state = old_states.items[old_state_idx];
        if (transition.source > old_state) {
            old_state_idx += 1;
            continue;
        }

        if (transition.source == old_state) {
            const start = transition_idx;
            while (transition_idx < transitions.items.len and
                transitions.items[transition_idx].source == old_state) : (transition_idx += 1)
            {}
            const len = transition_idx - start;
            transitions.appendSlice(transitions.items[start..transition_idx]);
            for (transitions.items[transitions.items.len - len ..]) |*t| {
                t.source = new_state;
            }
        }

        transition_idx += 1;
    }

    return new_state;
}

fn applyAccumulatedOverlap(
    comptime new_states: *[]CtSortedList(usize),
    comptime source_state: usize,
    comptime transitions: *CtArrayList(Transition),
    comptime overlap: Input,
    comptime affected_transitions: CtSortedList(usize),
    comptime current_transition: *usize,
) void {
    var old_states = CtSortedList(usize){};
    var idx: usize = affected_transitions.items.len - 1;
    while (true) : (idx -= 1) {
        const affected = &transitions.items[affected_transitions.items[idx]];
        old_states.append(affected.target);

        if (affected.input.removeOverlap(overlap)) |new_input| {
            affected.input = new_input;
        } else {
            transitions.orderedRemove(idx);
            if (idx < current_transition.*) {
                current_transition.* -= 1;
            }
        }

        if (idx == 0) break;
    }
    const new_state_idx = newStateIndex(new_states, old_states, transitions);

    transitions.insert(current_transition.*, .{
        .source = source_state,
        .target = new_state_idx,
        .input = overlap,
    });
}

// TODO Prune stuff
// TODO minimize function
// TODO Thoroughly test this as well as the assumption about dead states
/// If self has had dead states removed, the resulting DFA will have no dead nodes
pub fn determinize(comptime self: Self) Self {
    if (self.isDfa()) return self;

    var transitions = CtArrayList(Transition).init(self.transitions);
    comptime var new_states: []CtSortedList(usize) = blk: {
        var buf: [self.size()]CtSortedList(usize) = undefined;
        for (buf) |*ns, i| ns.* = .{
            .items = &.{i},
        };
        break :blk &buf;
    };

    var new_state: usize = 0;
    while (new_state < new_states.len) : (new_state += 1) {
        // Process transitions
        process_transitions: while (true) {
            var accumulated_overlap: ?Input = null;
            var affected_transitions = CtSortedList(usize){};
            var processed_any = false;
            var transition_idx: usize = 0;
            while (transition_idx < transitions.items.len) : (transition_idx += 1) {
                var transition = &transitions.items[transition_idx];
                if (transition.source < new_state) continue;
                if (transition.source > new_state) break;

                if (accumulated_overlap) |old_overlap| {
                    if (old_overlap.overlap(transition.input)) |new_overlap| {
                        accumulated_overlap = new_overlap;
                        affected_transitions.append(transition_idx);
                    } else if (affected_transitions.items.len > 1) {
                        // It's the end of this set of overlaps
                        applyAccumulatedOverlap(
                            &new_states,
                            new_state,
                            &transitions,
                            old_overlap,
                            affected_transitions,
                            &transition_idx,
                        );
                        processed_any = true;

                        accumulated_overlap = null;
                        affected_transitions.items.len = 0;
                    }
                } else {
                    accumulated_overlap = transition.input;
                    affected_transitions.append(transition_idx);
                }
            }
            // If we have actual accumulated_overlap, commit it before next loop
            if (affected_transitions.items.len > 1) {
                applyAccumulatedOverlap(
                    &new_states,
                    new_state,
                    &transitions,
                    accumulated_overlap.?,
                    affected_transitions,
                    &transition_idx,
                );
                processed_any = true;
            }

            if (!processed_any) break :process_transitions;
        }
    }

    var final_states = CtSortedList(usize){};
    for (self.final_states) |old_fs| {
        for (new_states) |old_states, ns| {
            if (old_states.contains(old_fs))
                final_states.append(ns);
        }
    }

    // TODO Prove that output will have sorted transitions and no dead nodes

    return .{
        .final_states = final_states.items,
        .transitions = transitions.items,
    };
}
