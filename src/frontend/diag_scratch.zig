const std = @import("std");

pub const MissingCongruenceReason = enum {
    missing_rule,
    changed_bound_arg,
    missing_child_relation,
    missing_child_proof,
    missing_parent_relation,
    malformed_rule,
    unknown_term,
};

pub const DepViolationDiagnosticDetail = struct {
    first_arg_idx: usize,
    second_arg_idx: usize,
    first_arg_name: ?[]const u8 = null,
    second_arg_name: ?[]const u8 = null,
    first_deps: u55,
    second_deps: u55,
    first_bound: bool,
    second_bound: bool,
    /// Whether the rule declares each argument as a bound binder ({x} vs
    /// (p)). Distinguishes the two violation shapes: a bound binder's
    /// variable occurring where the rule forbids it (exactly one side
    /// bound) vs two bound binders assigned the same variable (both
    /// bound). False/false means the construction path predates this
    /// field; renderers fall back to the generic wording.
    first_rule_bound: bool = false,
    second_rule_bound: bool = false,
    /// Notation-rendered assigned expressions (truncated), for showing the
    /// student what each conflicting argument actually received. Null when
    /// rendering failed or the argument was not yet assigned.
    first_binding_text: ?[]const u8 = null,
    second_binding_text: ?[]const u8 = null,
};

pub const CapturedDetail = union(enum) {
    missing_congruence_rule: struct {
        reason: MissingCongruenceReason,
        term_id: ?u32 = null,
        sort_name: ?[]const u8 = null,
        arg_index: ?usize = null,
    },
    /// The `@rewrite` rule whose step led back to an expression still
    /// being rewritten.
    rewrite_cycle: struct {
        rule_id: u32,
    },
    /// The `@rewrite` rule whose step would have passed the step limit.
    rewrite_step_limit: struct {
        rule_id: u32,
    },
    /// A congruence step whose `@congr` instance breaks the rule's
    /// dependencies: the rule, the clash, and the two clashing arguments.
    congruence_dep_violation: struct {
        rule_id: u32,
        detail: DepViolationDiagnosticDetail,
        first_expr: u32,
        second_expr: u32,
    },
};

pub const CapturedEntry = struct {
    err: anyerror,
    detail: CapturedDetail,
};

pub const Scratch = struct {
    allocator: std.mem.Allocator,
    entries: std.ArrayListUnmanaged(CapturedEntry) = .empty,

    pub const Mark = struct {
        start: usize,
    };

    pub fn init(allocator: std.mem.Allocator) Scratch {
        return .{ .allocator = allocator };
    }

    pub fn deinit(self: *Scratch) void {
        self.entries.deinit(self.allocator);
    }

    pub fn mark(self: *Scratch) Mark {
        return .{ .start = self.entries.items.len };
    }

    pub fn discard(self: *Scratch, scratch_mark: Mark) void {
        self.entries.shrinkRetainingCapacity(scratch_mark.start);
    }

    pub fn record(
        self: *Scratch,
        err: anyerror,
        detail: CapturedDetail,
    ) void {
        self.entries.append(self.allocator, .{
            .err = err,
            .detail = detail,
        }) catch {};
    }

    pub fn takeSince(
        self: *Scratch,
        scratch_mark: Mark,
        err: anyerror,
    ) ?CapturedDetail {
        var i = self.entries.items.len;
        while (i > scratch_mark.start) {
            i -= 1;
            const entry = self.entries.items[i];
            if (entry.err == err) {
                const detail = entry.detail;
                self.entries.shrinkRetainingCapacity(scratch_mark.start);
                return detail;
            }
        }
        self.entries.shrinkRetainingCapacity(scratch_mark.start);
        return null;
    }
};
