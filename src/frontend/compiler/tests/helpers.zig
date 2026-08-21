//! Shared fixtures and expectation helpers for the test files in this
//! directory. Everything here is re-exported `pub` so topic files can
//! alias what they use.

pub const std = @import("std");

pub const mm0 = @import("mm0");

pub const Compiler = mm0.Compiler;

pub const FrontendEnv = mm0.Frontend.Env;

pub const FrontendExpr = mm0.Frontend.Expr;

pub const Expr = mm0.Expr;

pub const CompilerInference = mm0.CompilerSupport.Inference;

pub const MM0Parser = mm0.MM0Parser;

pub const Mmb = mm0.Mmb;

pub const Proof = mm0.Proof;

pub const ProofScript = mm0.ProofScript;

pub const RewriteRegistry = mm0.RewriteRegistry.RewriteRegistry;

pub const ConversionRole = mm0.RewriteRegistry.ConversionRole;

pub const CompilerMetadata = mm0.CompilerSupport.Metadata;

pub const CompilerViews = mm0.CompilerSupport.Views;

pub const DefOps = mm0.DefOps;

pub fn collectStatementCmds(
    allocator: std.mem.Allocator,
    mmb: Mmb,
) ![]Proof.StmtCmd {
    var cmds = std.ArrayListUnmanaged(Proof.StmtCmd){};
    var pos: usize = @intCast(mmb.header.p_proof);

    while (true) {
        const stmt_start = pos;
        const cmd = try Proof.Cmd.read(
            mmb.file_bytes,
            pos,
            mmb.file_bytes.len,
        );
        const stmt_cmd: Proof.StmtCmd = @enumFromInt(cmd.op);
        try cmds.append(allocator, stmt_cmd);
        if (stmt_cmd == .End) break;
        if (cmd.data == 0) return error.BadStatementLength;
        pos = stmt_start + cmd.data;
    }

    return try cmds.toOwnedSlice(allocator);
}

pub fn readProofCaseFile(
    allocator: std.mem.Allocator,
    stem: []const u8,
    ext: []const u8,
) ![]u8 {
    const path = try std.fmt.allocPrint(
        allocator,
        "tests/proof_cases/{s}.{s}",
        .{ stem, ext },
    );
    defer allocator.free(path);
    return try std.fs.cwd().readFileAlloc(
        allocator,
        path,
        std.math.maxInt(usize),
    );
}

pub fn replaceOnceOwned(
    allocator: std.mem.Allocator,
    src: []const u8,
    needle: []const u8,
    repl: []const u8,
) ![]u8 {
    const start = std.mem.indexOf(u8, src, needle) orelse {
        return error.ExpectedNeedle;
    };
    return try std.fmt.allocPrint(
        allocator,
        "{s}{s}{s}",
        .{
            src[0..start],
            repl,
            src[start + needle.len ..],
        },
    );
}

pub const AnnotatedMetadata = struct {
    env: FrontendEnv.GlobalEnv,
    registry: RewriteRegistry,
    fresh_bindings: std.AutoHashMap(
        u32,
        []const CompilerMetadata.FreshDecl,
    ),
    freshen_bindings: std.AutoHashMap(
        u32,
        []const CompilerMetadata.FreshenDecl,
    ),
    views: std.AutoHashMap(u32, CompilerMetadata.ViewDecl),
    sort_vars: CompilerMetadata.SortVarRegistry,
};

pub fn processAnnotatedMetadata(
    allocator: std.mem.Allocator,
    src: []const u8,
) !AnnotatedMetadata {
    var parser = MM0Parser.init(src, allocator);
    var result = AnnotatedMetadata{
        .env = FrontendEnv.GlobalEnv.init(allocator),
        .registry = RewriteRegistry.init(allocator),
        .fresh_bindings = std.AutoHashMap(
            u32,
            []const CompilerMetadata.FreshDecl,
        ).init(allocator),
        .freshen_bindings = std.AutoHashMap(
            u32,
            []const CompilerMetadata.FreshenDecl,
        ).init(allocator),
        .views = std.AutoHashMap(
            u32,
            CompilerMetadata.ViewDecl,
        ).init(allocator),
        .sort_vars = CompilerMetadata.SortVarRegistry.init(allocator),
    };

    while (try parser.next()) |stmt| {
        switch (stmt) {
            .sort => |sort_stmt| {
                try result.env.addStmt(stmt);
                try CompilerMetadata.processSortMetadata(
                    &parser,
                    sort_stmt,
                    parser.last_annotations,
                    &result.sort_vars,
                );
            },
            .term => |term_stmt| {
                try result.env.addStmt(stmt);
                try CompilerMetadata.processTermMetadata(
                    &result.env,
                    &result.registry,
                    term_stmt,
                    parser.last_annotations,
                );
            },
            .assertion => |assertion| {
                try result.env.addStmt(stmt);
                try CompilerMetadata.processAssertionMetadata(
                    allocator,
                    &parser,
                    &result.env,
                    &result.registry,
                    &result.fresh_bindings,
                    &result.freshen_bindings,
                    &result.views,
                    assertion,
                    parser.last_annotations,
                );
            },
        }
    }

    return result;
}

pub fn ruleArgIndex(
    rule: *const FrontendEnv.RuleDecl,
    name: []const u8,
) !usize {
    for (rule.arg_names, 0..) |arg_name, idx| {
        if (arg_name) |actual_name| {
            if (std.mem.eql(u8, actual_name, name)) return idx;
        }
    }
    return error.MissingRuleArg;
}

pub fn hasFreshenDecl(
    decls: []const CompilerMetadata.FreshenDecl,
    target_arg_idx: usize,
    blocker_arg_idx: usize,
) bool {
    for (decls) |decl| {
        if (decl.target_arg_idx == target_arg_idx and
            decl.blocker_arg_idx == blocker_arg_idx)
        {
            return true;
        }
    }
    return false;
}

pub fn renderedNoteText(
    buf: *std.ArrayListUnmanaged(u8),
    note: mm0.CompilerDiagnosticNote,
) ![]const u8 {
    var writer = buf.writer(std.testing.allocator);
    try mm0.renderCompilerNoteMessage(&writer, note.message);
    return buf.items;
}

pub fn expectHasNote(diag: anytype, expected: []const u8) !void {
    for (diag.notes[0..diag.note_count]) |note| {
        var buf = std.ArrayListUnmanaged(u8){};
        defer buf.deinit(std.testing.allocator);
        if (std.mem.eql(u8, try renderedNoteText(&buf, note), expected)) {
            return;
        }
    }
    return error.MissingExpectedNote;
}

pub fn expectNoteText(
    expected: []const u8,
    note: mm0.CompilerDiagnosticNote,
) !void {
    var buf = std.ArrayListUnmanaged(u8){};
    defer buf.deinit(std.testing.allocator);
    try std.testing.expectEqualStrings(
        expected,
        try renderedNoteText(&buf, note),
    );
}

pub fn expectNoteStartsWith(
    prefix: []const u8,
    note: mm0.CompilerDiagnosticNote,
) !void {
    var buf = std.ArrayListUnmanaged(u8){};
    defer buf.deinit(std.testing.allocator);
    try std.testing.expect(std.mem.startsWith(
        u8,
        try renderedNoteText(&buf, note),
        prefix,
    ));
}
