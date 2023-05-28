const std = @import("std");

pub fn build(b: *std.Build) void {
    const target = b.standardTargetOptions(.{});

    // Standard release options allow the person running `zig build` to select
    // between Debug, ReleaseSafe, ReleaseFast, and ReleaseSmall.
    const optimize = b.standardOptimizeOption(.{});

    const lib = b.addStaticLibrary(.{
        .name = "ctregex",
        .root_source_file = .{ .path = "ctregex.zig" },
        .target = target,
        .optimize = optimize,
    });

    b.installArtifact(lib);
}
