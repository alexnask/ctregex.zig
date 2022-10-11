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
    unreachable;
}

pub fn size(comptime self: Self) usize {
    var max = 0;
    for (self.transitions) |t| {
        if (t.target > max) max = t.target;
        if (t.source > max) max = t.source;
    }
    return max + 1;
}

/// Assumes `sources` is sorted
// Make this an iterator that accumulates.. is this possible without ++ ?
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
        try expectEqualAutomata(a, .{ .final_states = &.{1}, .transitions = &.{
            .{
                .source = 0,
                .target = 1,
                .input = .{ .single = 'a' },
            },
        } });

        const b = single('b');
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

const NewState = struct {
    old_states: []const usize,
};

// Cache this based on the slice contents somehow
fn newState(
    comptime new_states: *[]NewState,
    comptime new_states_analyzed: *[]bool,
    old_states: []const usize,
) usize {
    for (new_states.*) |s, idx| {
        if (std.mem.eql(usize, s.old_states, old_states)) return idx;
    }
    var buf: [new_states.len + 1]NewState = ([1]NewState{undefined} ** new_states.len) ++
        [1]NewState{.{ .old_states = old_states }};
    std.mem.copy(NewState, &buf, new_states.*);
    new_states.* = &buf;

    var buf2: [new_states_analyzed.len + 1]bool = ([1]bool{undefined} ** new_states_analyzed.len) ++ [1]bool{false};
    std.mem.copy(bool, &buf2, new_states_analyzed.*);
    new_states_analyzed.* = &buf2;
    return new_states.len - 1;
}

fn ctSortedAppend(comptime dest: *[]const usize, elem: usize) void {
    if (dest.len == 0) {
        dest.* = &[1]usize{elem};
        return;
    }
    var idx = dest.len - 1;
    while (true) : (idx -= 1) {
        if (elem == dest.*[idx]) return;
        if (elem > dest.*[idx]) {
            dest.* = dest.*[0 .. idx + 1] ++ &[1]usize{elem} ++ dest.*[idx + 1 ..];
            return;
        }
        if (idx == 0) break;
    }
    dest.* = &[1]usize{elem} ++ dest.*;
}

fn removeOverlapOrRemoveTransition(
    comptime ts: *[]Transition,
    comptime idx: usize,
    comptime t: *Transition,
    comptime overlap: Input,
) bool {
    if (t.input.removeOverlap(overlap)) |new_t|
        t.input = new_t
    else {
        std.mem.copy(Transition, ts.*[idx..], ts.*[idx + 1 ..]);
        ts.* = ts.*[0 .. ts.len - 1];
        return true;
    }
    return false;
}

fn ctRemoveTransition(comptime ts: *[]Transition, idx: usize) void {
    std.mem.copy(Transition, ts.*[idx..], ts.*[idx + 1 ..]);
    ts.* = ts.*[0 .. ts.len - 1];
}

// TODO minimize function
// TODO Thoroughly test this
pub fn determinize(comptime self: Self) Self {
    if (self.isDfa()) return self;

    comptime var new_states: []NewState = blk: {
        var buf = [1]NewState{.{ .old_states = &.{0} }};
        break :blk &buf;
    };
    var new_states_analyzed: []bool = blk: {
        var buf = [1]bool{false};
        break :blk &buf;
    };

    var transitions: []const Transition = &.{};
    while (true) {
        var all_analyzed = true;
        // This should pick up new states, no?
        var state_idx: usize = 0;
        while (state_idx < new_states.len) : (state_idx += 1) {
            const s = &new_states[state_idx];
            if (new_states_analyzed[state_idx]) continue;
            all_analyzed = false;
            var state_transitions = self.transitionsFromMulti(s.old_states);

            overlap_loop: while (state_transitions.len > 0) {
                for (state_transitions) |*t1, i| {
                    var curr_transition = t1.*;
                    var old_targets: []const usize = &.{t1.target};
                    for (state_transitions[i + 1 ..]) |*t2, j| {
                        if (curr_transition.input.overlap(t2.input)) |overlap| {
                            // Order is important because we are possibly removing from `state_transitions`
                            const b2 = removeOverlapOrRemoveTransition(&state_transitions, i + 1 + j, t2, overlap);
                            const b1 = removeOverlapOrRemoveTransition(&state_transitions, i, t1, overlap);
                            ctSortedAppend(&old_targets, t2.target);
                            // Make overlap a transition
                            curr_transition = Transition{
                                .source = state_idx,
                                .target = newState(&new_states, &new_states_analyzed, old_targets),
                                .input = overlap,
                            };

                            if (b1 or b2) {
                                // Stop here by breaking, we will get to overlap_loop
                                break;
                            }
                        }
                    }

                    if (old_targets.len > 1) {
                        // We had overlap
                        transitions = transitions ++ &[1]Transition{curr_transition};
                    } else {
                        // No overlap
                        transitions = transitions ++ &[1]Transition{.{
                            .source = state_idx,
                            .target = newState(&new_states, &new_states_analyzed, old_targets),
                            .input = t1.input,
                        }};
                        ctRemoveTransition(&state_transitions, i);
                    }
                    continue :overlap_loop;
                }
                break :overlap_loop;
            }
            new_states_analyzed[state_idx] = true;
        }

        if (all_analyzed)
            break;
    }

    var final_states: []const usize = &.{};
    for (self.final_states) |old_fs| {
        for (new_states) |s, idx| {
            for (s.old_states) |o| if (old_fs == o) {
                ctSortedAppend(&final_states, idx);
            };
        }
    }
    // Make sure transitions are sorted
    // TODO Is this actually guaranteed?
    //   I think so but prove it
    std.debug.assert(std.sort.isSorted(Transition, transitions, {}, transitionLessThan));

    return .{
        .final_states = final_states,
        .transitions = transitions,
    };
}