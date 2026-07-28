//! The `unpack` code action: rewrite a proof line containing inline rule
//! applications into separate labeled lines, one per hidden application.
//!
//! An inline application is an anonymous proof line (docs/proof.md, "Chained
//! rule applications"); unpacking materializes it. The hidden line's
//! conclusion is captured at check time (`InlineConclusionSink`) and becomes
//! the new line's mandatory `$ assertion $`. Everything the user wrote —
//! assertions, explicit bindings — is preserved verbatim from the source;
//! only conclusions and fresh labels are newly rendered.
//!
//! Two gates keep this sound without trusting the pretty-printer round-trip:
//! the document must analyze cleanly before the rewrite (otherwise there are
//! no trustworthy conclusions to materialize), and the rewritten document
//! must analyze cleanly afterwards (otherwise no action is offered). The
//! second gate also covers inference regressions: a nested application can
//! check only via a contextual hint from its parent, and while the written
//! conclusion carries at least the information the hint did, the gate makes
//! that an observed fact rather than an argument.

const std = @import("std");
const ProofScript = @import("./proof_script.zig");
const CompilerModule = @import("./compiler.zig");

const Compiler = CompilerModule.Compiler;
const InlineConclusionSink = CompilerModule.InlineConclusionSink;
const Span = ProofScript.Span;
const Ref = ProofScript.Ref;
const RuleApplication = ProofScript.RuleApplication;
const ProofLine = ProofScript.ProofLine;
const ProofBlock = ProofScript.ProofBlock;

pub const UnpackSuggestion = struct {
    title: []const u8,
    replacement: []const u8,
    replace_span: Span,

    pub fn deinit(
        self: UnpackSuggestion,
        allocator: std.mem.Allocator,
    ) void {
        allocator.free(self.title);
        allocator.free(self.replacement);
    }
};

/// Parse-only pre-gate: does `offset` sit on a proof line that the full
/// (compile-backed) unpack could apply to? Lets callers skip loading the
/// sibling `.mm0` for the common no-target case.
pub fn hasTargetAt(
    allocator: std.mem.Allocator,
    proof_src: []const u8,
    offset: usize,
) bool {
    var arena = std.heap.ArenaAllocator.init(allocator);
    defer arena.deinit();
    const target = findTarget(arena.allocator(), proof_src, offset) catch
        return false;
    return target != null;
}

/// Compute the unpack rewrite for the proof line at `offset`, or null when
/// there is nothing to unpack there or the rewrite cannot be validated.
/// The returned strings are owned by `allocator`.
pub fn unpackAtSourceOffset(
    allocator: std.mem.Allocator,
    mm0_src: []const u8,
    proof_src: []const u8,
    offset: usize,
) std.mem.Allocator.Error!?UnpackSuggestion {
    var work_arena = std.heap.ArenaAllocator.init(allocator);
    defer work_arena.deinit();
    const work = work_arena.allocator();

    const target = (findTarget(work, proof_src, offset) catch |err|
        switch (err) {
            error.OutOfMemory => return error.OutOfMemory,
            // A proof source that does not parse has no unpack targets.
            else => return null,
        }) orelse return null;

    // Gate 1 + conclusion capture: the document as written must analyze
    // cleanly, with the sink recording every inline application's
    // elaborated conclusion.
    var sink = InlineConclusionSink{ .allocator = work };
    if (!try analyzesCleanly(work, mm0_src, proof_src, &sink)) return null;

    // Fallback and retry candidates re-record a span; the last entry is the
    // one from the attempt that survived, so later inserts overwrite.
    var conclusions = std.AutoHashMapUnmanaged(u128, []const u8){};
    for (sink.items.items) |item| {
        try conclusions.put(work, spanKey(item.span), item.conclusion);
    }

    const built = (try buildReplacement(
        work,
        proof_src,
        target,
        &conclusions,
    )) orelse return null;

    // Gate 2: the rewritten document must analyze cleanly too.
    const spliced = try std.mem.concat(work, u8, &.{
        proof_src[0..target.line.span.start],
        built.replacement,
        proof_src[target.line.span.end..],
    });
    if (!try analyzesCleanly(work, mm0_src, spliced, null)) return null;

    const title = if (built.count == 1)
        try allocator.dupe(u8, "Unpack inline application")
    else
        try std.fmt.allocPrint(
            allocator,
            "Unpack {d} inline applications",
            .{built.count},
        );
    errdefer allocator.free(title);
    return .{
        .title = title,
        .replacement = try allocator.dupe(u8, built.replacement),
        .replace_span = target.line.span,
    };
}

const Target = struct {
    block: ProofBlock,
    line: ProofLine,
};

fn findTarget(
    allocator: std.mem.Allocator,
    proof_src: []const u8,
    offset: usize,
) !?Target {
    var parser = ProofScript.Parser.init(allocator, proof_src);
    while (try parser.nextBlock()) |block| {
        for (block.lines) |line| {
            if (offset < line.span.start or offset > line.span.end) continue;
            if (countInlineApplications(line.application) == 0) return null;
            // A search placeholder anywhere in the line means the proof is
            // still being written there; search actions own that surface.
            if (containsSearchPlaceholder(line.application)) return null;
            return .{ .block = block, .line = line };
        }
    }
    return null;
}

fn countInlineApplications(app: RuleApplication) usize {
    var count: usize = 0;
    for (app.refs) |ref| switch (ref) {
        .application => |child| {
            count += 1 + countInlineApplications(child);
        },
        else => {},
    };
    return count;
}

fn containsSearchPlaceholder(app: RuleApplication) bool {
    if (ProofScript.isSearchPlaceholderRuleName(app.rule_name)) return true;
    for (app.refs) |ref| switch (ref) {
        .application => |child| {
            if (containsSearchPlaceholder(child)) return true;
        },
        else => {},
    };
    return false;
}

/// Run the LSP-path analysis and report whether it produced no primary
/// diagnostics. Search placeholders are tolerated the way the LSP analysis
/// tolerates them, so a placeholder elsewhere in the document does not
/// disqualify an unrelated line from unpacking.
fn analyzesCleanly(
    allocator: std.mem.Allocator,
    mm0_src: []const u8,
    proof_src: []const u8,
    sink: ?*InlineConclusionSink,
) std.mem.Allocator.Error!bool {
    var compiler = Compiler.initWithProof(allocator, mm0_src, proof_src);
    compiler.allow_search_placeholders = true;
    compiler.inline_conclusion_sink = sink;
    compiler.analyze() catch |err| switch (err) {
        error.OutOfMemory => return error.OutOfMemory,
        else => return false,
    };
    return compiler.primaryDiagnostics().len == 0;
}

fn spanKey(span: Span) u128 {
    return (@as(u128, span.start) << 64) | span.end;
}

const Built = struct {
    replacement: []const u8,
    count: usize,
};

const Emitter = struct {
    allocator: std.mem.Allocator,
    proof_src: []const u8,
    conclusions: *const std.AutoHashMapUnmanaged(u128, []const u8),
    /// Leading whitespace of the original physical line, applied to every
    /// emitted line (`ProofLine.span` starts at the physical line start, so
    /// the replacement re-supplies the indentation it replaces).
    indent: []const u8,
    /// Label base for fresh labels: `<base>_1`, `<base>_2`, ...
    base: []const u8,
    used_labels: std.StringHashMapUnmanaged(void),
    label_counter: usize = 0,
    out: std.ArrayListUnmanaged(u8) = .{},
    count: usize = 0,

    /// Render `app` as source text: rule name, explicit bindings verbatim,
    /// and refs with `.application` children replaced by the labels of
    /// freshly emitted lines (children land in `out` before any line that
    /// references them). Null when a conclusion is unavailable.
    fn renderApp(
        self: *Emitter,
        app: RuleApplication,
    ) std.mem.Allocator.Error!?[]const u8 {
        const allocator = self.allocator;
        var buf = std.ArrayListUnmanaged(u8){};
        try buf.appendSlice(allocator, app.rule_name);
        if (app.arg_bindings.len != 0) {
            try buf.appendSlice(allocator, " (");
            for (app.arg_bindings, 0..) |binding, idx| {
                if (idx != 0) try buf.appendSlice(allocator, ", ");
                try buf.appendSlice(
                    allocator,
                    self.proof_src[binding.span.start..binding.span.end],
                );
            }
            try buf.append(allocator, ')');
        }
        if (app.refs.len != 0) {
            try buf.appendSlice(allocator, " [");
            for (app.refs, 0..) |ref, idx| {
                if (idx != 0) try buf.appendSlice(allocator, ", ");
                switch (ref) {
                    .hyp => |hyp| if (hyp.name) |name|
                        try buf.writer(allocator).print("#{s}", .{name})
                    else
                        try buf.writer(allocator).print("#{d}", .{hyp.index}),
                    .line => |line| try buf.appendSlice(
                        allocator,
                        line.label,
                    ),
                    .application => |child| {
                        const label = (try self.emitLine(child)) orelse
                            return null;
                        try buf.appendSlice(allocator, label);
                    },
                }
            }
            try buf.append(allocator, ']');
        }
        return try buf.toOwnedSlice(allocator);
    }

    /// Materialize `app` as its own proof line and return its fresh label.
    fn emitLine(
        self: *Emitter,
        app: RuleApplication,
    ) std.mem.Allocator.Error!?[]const u8 {
        const app_text = (try self.renderApp(app)) orelse return null;
        const conclusion = self.conclusions.get(spanKey(app.span)) orelse
            return null;
        const label = try self.freshLabel();
        try self.out.writer(self.allocator).print(
            "{s}{s}: $ {s} $ by {s}\n",
            .{ self.indent, label, conclusion, app_text },
        );
        self.count += 1;
        return label;
    }

    fn freshLabel(self: *Emitter) ![]const u8 {
        while (true) {
            self.label_counter += 1;
            const candidate = try std.fmt.allocPrint(
                self.allocator,
                "{s}_{d}",
                .{ self.base, self.label_counter },
            );
            const entry = try self.used_labels.getOrPut(
                self.allocator,
                candidate,
            );
            if (!entry.found_existing) return candidate;
        }
    }
};

fn buildReplacement(
    allocator: std.mem.Allocator,
    proof_src: []const u8,
    target: Target,
    conclusions: *const std.AutoHashMapUnmanaged(u128, []const u8),
) !?Built {
    var used_labels = std.StringHashMapUnmanaged(void){};
    for (target.block.lines) |line| {
        try used_labels.put(allocator, line.label, {});
    }

    const line = target.line;
    var emitter = Emitter{
        .allocator = allocator,
        .proof_src = proof_src,
        .conclusions = conclusions,
        .indent = proof_src[line.span.start..line.label_span.start],
        .base = line.label,
        .used_labels = used_labels,
    };

    const top_text = (try emitter.renderApp(line.application)) orelse
        return null;

    // Rebuild the original line: label and assertion verbatim, the
    // application re-rendered with its inline children replaced by labels,
    // and the original tail (trailing comment and newline) preserved.
    const writer = emitter.out.writer(allocator);
    try writer.print("{s}{s}: {s} by {s}", .{
        emitter.indent,
        line.label,
        proof_src[line.assertion.span.start..line.assertion.span.end],
        top_text,
    });
    try writer.writeAll(
        proof_src[line.application.span.end..line.span.end],
    );

    return .{
        .replacement = try emitter.out.toOwnedSlice(allocator),
        .count = emitter.count,
    };
}
