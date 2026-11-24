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
const ArenaAllocator = @import("./arena_allocator.zig").ArenaAllocator;
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

/// Compute the unpack rewrite for the proof line at `offset`, or null when
/// there is nothing to unpack there or the rewrite cannot be validated.
/// `block` is the block touching `offset` (`ProofScript.blockTouching`);
/// without a target in it, nothing is analyzed.
/// The returned strings are owned by `allocator`. `work_allocator` backs the
/// working memory, which the two analyses free theorem by theorem: a caller
/// whose `allocator` is an arena (the LSP's per-request one) passes the
/// allocator under it, or those frees reclaim nothing.
pub fn unpackAtSourceOffset(
    allocator: std.mem.Allocator,
    work_allocator: std.mem.Allocator,
    mm0_src: []const u8,
    proof_src: []const u8,
    block: ProofBlock,
    offset: usize,
) std.mem.Allocator.Error!?UnpackSuggestion {
    const line = findTarget(block, offset) orelse return null;

    var work_arena = ArenaAllocator.init(work_allocator);
    defer work_arena.deinit();
    const work = work_arena.allocator();

    // Gate 1 + conclusion capture: the document as written must analyze
    // cleanly, with the sink recording every inline application's
    // elaborated conclusion.
    var sink = InlineConclusionSink{ .allocator = work };
    if (!try analyzesCleanly(work_allocator, mm0_src, proof_src, &sink)) return null;

    // Aborted fallback/retry attempts roll their entries back (see
    // `InlineConclusionSink`), so every entry comes from the surviving
    // elaboration; later inserts overwrite.
    var conclusions = std.AutoHashMapUnmanaged(u128, []const u8){};
    for (sink.items.items) |item| {
        try conclusions.put(work, spanKey(item.span), item.conclusion);
    }

    const built = (try buildReplacement(
        work,
        proof_src,
        block,
        line,
        &conclusions,
    )) orelse return null;

    // Gate 2: the rewritten document must analyze cleanly too.
    const spliced = try std.mem.concat(work, u8, &.{
        proof_src[0..line.span.start],
        built.replacement,
        proof_src[line.span.end..],
    });
    if (!try analyzesCleanly(work_allocator, mm0_src, spliced, null)) return null;

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
        .replace_span = line.span,
    };
}

/// The line of `block` at `offset` to unpack.
fn findTarget(block: ProofBlock, offset: usize) ?ProofLine {
    // A block with a broken line does not analyze cleanly.
    for (block.lines) |line| {
        if (line.incomplete) return null;
    }
    for (block.lines) |line| {
        if (offset < line.span.start or offset > line.span.end) continue;
        if (countInlineApplications(line.application) == 0) return null;
        // A search placeholder or open goal anywhere in the line means
        // the proof is still being written there; search actions and
        // open-goal actions own that surface.
        if (containsUnfinishedMarker(line.application)) return null;
        return line;
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

/// A search placeholder or an open goal: an inline application with no
/// conclusion of its own to lift onto a line.
fn containsUnfinishedMarker(app: RuleApplication) bool {
    if (ProofScript.isSearchPlaceholderRuleName(app.rule_name) or
        ProofScript.isOpenGoalRuleName(app.rule_name)) return true;
    for (app.refs) |ref| switch (ref) {
        .application => |child| {
            if (containsUnfinishedMarker(child)) return true;
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
    labels: ProofScript.FreshLabels,
    out: std.ArrayListUnmanaged(u8) = .empty,
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
        var buf = std.ArrayListUnmanaged(u8).empty;
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
                        try buf.print(allocator, "#{s}", .{name})
                    else
                        try buf.print(allocator, "#{d}", .{hyp.index}),
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
        const label = try self.labels.next(self.allocator);
        try self.out.print(
            self.allocator,
            "{s}{s}: $ {s} $ by {s}\n",
            .{ self.indent, label, conclusion, app_text },
        );
        self.count += 1;
        return label;
    }
};

fn buildReplacement(
    allocator: std.mem.Allocator,
    proof_src: []const u8,
    block: ProofBlock,
    line: ProofLine,
    conclusions: *const std.AutoHashMapUnmanaged(u128, []const u8),
) !?Built {
    var emitter = Emitter{
        .allocator = allocator,
        .proof_src = proof_src,
        .conclusions = conclusions,
        .indent = proof_src[line.span.start..line.label_span.start],
        .labels = try .init(allocator, line.label, block.lines),
    };

    const top_text = (try emitter.renderApp(line.application)) orelse
        return null;

    // Rebuild the original line: label and assertion verbatim, the
    // application re-rendered with its inline children replaced by labels,
    // and the original tail (trailing comment and newline) preserved.
    try emitter.out.print(allocator, "{s}{s}: {s} by {s}", .{
        emitter.indent,
        line.label,
        proof_src[line.assertion.span.start..line.assertion.span.end],
        top_text,
    });
    try emitter.out.appendSlice(
        allocator,
        proof_src[line.application.span.end..line.span.end],
    );

    return .{
        .replacement = try emitter.out.toOwnedSlice(allocator),
        .count = emitter.count,
    };
}
