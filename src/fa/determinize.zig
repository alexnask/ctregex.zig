const std = @import("std");
const FiniteAutomaton = @import("finite_automaton.zig");
const Transition = FiniteAutomaton.Transition;

const ctutils = @import("../ct_utils.zig");
const CtSortedList = ctutils.CtSortedList;
const CtArrayList = ctutils.CtArrayList;

const SortedList = CtSortedList(usize);
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

// TODO: Split into more files (fa/finite_automaton.zig, fa/blocks.zig, fa/determinize.zig)
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

pub fn determinize(comptime self: FiniteAutomaton) FiniteAutomaton {
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

    // The second argument is used to make sure we don't get a cached Partition
    // with initialized memory
    fn init(comptime n: usize, comptime _: type) Partition {
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
        while (touched_sets.*.len > 0) {
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
    var blocks = Partition.init(initial_state_count, opaque {});

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
    //const state_count = reached_states;
    const final_state_count = blk: {
        var res: usize = 0;
        for (final_states.items) |fs| {
            if (blocks.locations[fs] < blocks.past[0])
                res += 1;
        }
        break :blk res;
    };

    var marked_elements: [*]usize = blk: {
        var buf: [transitions.items.len + 1]usize = undefined;
        buf[0] = final_state_count;
        break :blk &buf;
    };

    // Make initial transition partition
    var touched_sets: []usize = blk: {
        var buf: [transitions.items.len + 1]usize = undefined;
        buf[0] = 0;
        break :blk buf[0..1];
    };
    blocks.split(marked_elements, &touched_sets);

    var cords = Partition.init(transitions.items.len, opaque {});
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
    // The transactions are no longer sorted by source but we don't care since
    // we are going straight to match codegen or comptime matching next

    var new_final_states = SortedList{ .items = &.{} };
    for (final_states.items) |fs| {
        if (blocks.first[fs] < initial_state_count) {
            new_final_states.append(new_state(new_start_state, blocks.set_of_elem, fs));
        }
    }
    final_states.* = new_final_states;
}
