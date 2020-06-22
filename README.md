# Zig compile time regular expressions
Generating fast code since 2020

## Features
- Comptime regular expression compilation
- Comptime and runtime matching
- UTF8, UTF16le, ASCII, codepoint array support
- Captures (with named `(:<name>...)` support)
- `|`, `*`, `+`, `?`, `(:?...)`, `[...]`, `[^...]`
- '\d', '\s' character classes

## TODO
- Faster generated code using DFAs when possible
- search, findAll, etc.
- More character classes
- More features (backreferences, `{N}`, etc.)

## Example

```zig
test "runtime matching" {
    @setEvalBranchQuota(1250);
    // The encoding is utf8 by default, you can use .ascii, .utf16le, .codepoint here instead.
    if (try match("(?<test>def|abc)([😇ω])+", .{.encoding = .utf8}, "abc😇ωωωωω")) |res| {
        std.debug.warn("Test: {}, 1: {}\n", .{ res.capture("test"), res.captures[1] });
    }
}

test "comptime matching" {
    @setEvalBranchQuota(2700);
    if (comptime try match("(?<test>def|abc)([😇ω])+", .{}, "abc😇ωωωωω")) |res| {
        @compileError("Test: " ++ res.capture("test").? ++ ", 1: " ++ res.captures[1].?);
    }
}
```

See tests.zig for more examples.
