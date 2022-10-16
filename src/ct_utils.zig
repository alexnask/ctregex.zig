const std = @import("std");
const mem = std.mem;

pub fn CtSortedList(comptime T: type) type {
    return struct {
        items: []const T = &.{},

        pub fn append(comptime self: *@This(), elem: usize) void {
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

        pub fn replace(comptime self: *@This(), comptime idx: usize, comptime value: T) void {
            if (idx == 0)
                self.items = &[1]T{value} ++ self.items[1..]
            else if (idx == self.items.len - 1)
                self.items = self.items[0..idx] ++ &[1]T{value}
            else
                self.items = self.items[0..idx] ++ &[1]T{value} ++ self.items[idx + 1 ..];
        }

        pub fn remove(comptime self: *@This(), comptime idx: usize) void {
            if (idx == self.items.len - 1)
                self.items = self.items[0 .. self.items.len - 1]
            else
                self.items = self.items[0..idx] ++ self.items[idx..];
        }

        pub fn contains(comptime self: @This(), elem: usize) bool {
            var idx: usize = self.items.len - 1;
            return while (true) : (idx -= 1) {
                if (self.items[idx] == elem) break true;
                if (self.items[idx] < elem) break false;
                if (idx == 0) break false;
            };
        }

        pub fn eql(comptime lhs: @This(), comptime rhs: @This()) bool {
            return mem.eql(T, lhs.items, rhs.items);
        }
    };
}

/// `T` must have a concrete byte representation for branch optimization purposes
pub fn CtArrayList(comptime T: type) type {
    return struct {
        items: []T,
        capacity: usize,

        pub fn initCapacity(comptime capacity: usize) @This() {
            var self = @This(){ .items = &.{}, .capacity = 0 };
            self.ensureTotalCapacity(capacity);
            return self;
        }

        pub fn fromSlice(comptime s: []const T) @This() {
            var buf: [s.len]T = undefined;
            mem.copy(T, &buf, s);
            return .{
                .items = &buf,
                .capacity = buf.len,
            };
        }

        pub fn append(comptime self: *@This(), comptime t: T) void {
            self.ensureTotalCapacity(self.items.len + 1);
            self.items.len += 1;

            self.items[self.items.len - 1] = t;
        }

        pub fn appendNTimes(comptime self: *@This(), comptime value: T, comptime n: usize) void {
            self.ensureTotalCapacity(self.items.len + n);
            const old_len = self.items.len;
            self.items.len += n;
            // TODO: This crashes the compiler :(
            // self.items[old_len..].* = [1]bool{value} ** (self.items.len - old_len);
            for (self.items[old_len..]) |*i| i.* = value;
        }

        pub fn appendSlice(comptime self: *@This(), comptime ts: []const T) void {
            self.ensureTotalCapacity(self.items.len + ts.len);
            self.items.len += ts.len;
            // TODO: This crashes the compiler :(
            // self.items[self.items.len - ts.len ..].* = ts[0..ts.len].*;
            const dst = self.items[self.items.len - ts.len ..];
            mem.copy(T, dst, ts);
        }

        pub fn insert(comptime self: *@This(), comptime n: usize, comptime t: T) void {
            self.ensureTotalCapacity(self.items.len + 1);
            self.items.len += 1;

            // TODO: This crashes the compiler :(
            // const to_move = self.items[n .. self.items.len - 1].*;
            // self.items[n + 1 ..].* = to_move;
            mem.copyBackwards(T, self.items[n + 1 ..], self.items[n .. self.items.len - 1]);
            self.items[n] = t;
        }

        pub fn orderedRemove(comptime self: *@This(), comptime i: usize) void {
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

        pub fn ensureTotalCapacity(comptime self: *@This(), comptime new_capacity: usize) void {
            if (self.capacity >= new_capacity) return;
            const better_capacity = std.math.ceilPowerOfTwo(usize, new_capacity) catch unreachable;

            self.capacity = better_capacity;
            var buf: [self.capacity]T = undefined;
            buf[0..self.items.len].* = self.items[0..self.items.len].*;
            self.items = buf[0..self.items.len];
        }
    };
}
