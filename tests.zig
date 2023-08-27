const ctregex = @import("ctregex.zig");
const std = @import("std");
const expect = std.testing.expect;

fn encodeStr(comptime encoding: ctregex.Encoding, comptime str: []const u8) []const encoding.CharT() {
    return switch (encoding) {
        .ascii, .utf8 => str,
        .utf16le => block: {
            var temp: [str.len]u16 = undefined;
            break :block temp[0 .. std.unicode.utf8ToUtf16Le(&temp, str) catch unreachable];
        },
        .codepoint => block: {
            var temp: [str.len]u21 = undefined;
            var idx = 0;
            var it = std.unicode.Utf8View.initComptime(str).iterator();
            while (it.nextCodepoint()) |cp| {
                temp[idx] = cp;
                idx += 1;
            }
            break :block temp[0..idx];
        },
    };
}

fn testMatch(comptime regex: []const u8, comptime encoding: ctregex.Encoding, comptime str: []const u8) !void {
    const encoded_str = comptime encodeStr(encoding, str);
    try expect((try ctregex.match(regex, .{ .encoding = encoding }, encoded_str)) != null);
    comptime try expect((try ctregex.match(regex, .{ .encoding = encoding }, encoded_str)) != null);
}

fn testSearchInner(comptime regex: []const u8, comptime encoding: ctregex.Encoding, comptime str: []const encoding.CharT(), comptime found: []const encoding.CharT()) !void {
    const result = try ctregex.search(regex, .{ .encoding = encoding }, str);
    try expect(result != null);
    try expect(std.mem.eql(encoding.CharT(), result.?.slice, found));
}

fn testSearch(comptime regex: []const u8, comptime encoding: ctregex.Encoding, comptime str: []const u8, comptime found: []const u8) !void {
    const encoded_str = comptime encodeStr(encoding, str);
    const encoded_found = comptime encodeStr(encoding, found);

    try testSearchInner(regex, encoding, encoded_str, encoded_found);
    comptime try testSearchInner(regex, encoding, encoded_str, encoded_found);
}

fn testCapturesInner(comptime regex: []const u8, comptime encoding: ctregex.Encoding, comptime str: []const encoding.CharT(), comptime captures: []const ?[]const encoding.CharT()) !void {
    const result = try ctregex.match(regex, .{ .encoding = encoding }, str);
    try expect(result != null);

    const res_captures = &result.?.captures;
    try expect(res_captures.len == captures.len);

    var idx: usize = 0;
    while (idx < captures.len) : (idx += 1) {
        if (res_captures[idx] == null) {
            try expect(captures[idx] == null);
        } else {
            try expect(captures[idx] != null);
            try expect(std.mem.eql(encoding.CharT(), res_captures[idx].?, captures[idx].?));
        }
    }
}

fn testCaptures(comptime regex: []const u8, comptime encoding: ctregex.Encoding, comptime str: []const u8, comptime captures: []const ?[]const u8) !void {
    const encoded_str = comptime encodeStr(encoding, str);
    comptime var encoded_captures: [captures.len]?[]const encoding.CharT() = undefined;
    inline for (captures, 0..) |capt, idx| {
        if (capt) |capt_slice| {
            encoded_captures[idx] = comptime encodeStr(encoding, capt_slice);
        } else {
            encoded_captures[idx] = null;
        }
    }

    try testCapturesInner(regex, encoding, encoded_str, &encoded_captures);
    comptime try testCapturesInner(regex, encoding, encoded_str, &encoded_captures);
}

test "regex matching" {
    @setEvalBranchQuota(2550);
    try testMatch("abc|def", .ascii, "abc");
    try testMatch("abc|def", .ascii, "def");
    try testMatch("[Α-Ω][α-ω]+", .utf8, "Αλεξανδρος");
    try testMatch("[Α-Ω][α-ω]+", .utf16le, "Αλεξανδρος");
    try testMatch("[Α-Ω][α-ω]+", .codepoint, "Αλεξανδρος");
    try testMatch("[^a-z]{1,}", .ascii, "ABCDEF");
    try testMatch("[^a-z]{1,3}", .ascii, "ABC");
    try testMatch("Smile|(😀 | 😊){2}", .utf8, "😊😀");

    try testCaptures("(?:no\\ capture)([😀-🙏])*|(.*)", .utf8, "no capture", &[_]?[]const u8{ null, null });
    try testCaptures("(?:no\\ capture)([😀-🙏])*|(.*)", .utf8, "no capture😿😻", &[_]?[]const u8{ "😻", null });
    try testCaptures("(?:no\\ capture)([😀-🙏])*|(.*)", .utf8, "π = 3.14159...", &[_]?[]const u8{ null, "π = 3.14159..." });
}

test "regex searching" {
    @setEvalBranchQuota(3800);
    try testSearch("foo|bar", .ascii, "some very interesting test string including foobar.", "foo");
    try testSearch("(abc|αβγ)+", .utf8, "a lorem ipsum αβγαβγαβγ abcabc", "αβγαβγαβγ");
    try testSearch("(abc|αβγ)+", .utf16le, "a lorem ipsum αβγαβγαβγ abcabc", "αβγαβγαβγ");
    try testSearch("(abc|αβγ)+", .codepoint, "a lorem ipsum αβγαβγαβγ abcabc", "αβγαβγαβγ");
}
