//! How a failed search ended, read once from its counters. The status, the
//! failure report and the retry code action (`source.zig`) and the bench's
//! miss causes all read this one classification, so they cannot disagree.
//!
//! The retry rule is measured, not guessed. Over the depth corpus, a miss
//! that a limit cut short almost always hit several limits at once, and
//! raising one of them alone either exposed the next or spent the shared work
//! budget before the search reached the proof. Re-running each of 282 misses
//! with `retryFor`'s retry found 26 of the missed proofs, against 10 for the
//! one-limit advice it replaced. The bench's `--retry-misses` re-measures it.

const std = @import("std");
const types = @import("./types.zig");
const tunables = @import("./tunables.zig");

/// What ended the whole call early, if anything.
pub const Stop = enum { none, budget, stack };

pub const MissReport = struct {
    stop: Stop,
    /// A phase ran out of its own fuel and was retired.
    fuel: bool,
    /// A pass reached the subgoal limit and left subgoals unexpanded.
    nodes: bool,
    /// Forward saturation stopped at its bounds before a fixpoint.
    forward: bool,
    /// Recursive generation ran (an `exact?`, or an `auto?` that never got
    /// to generate, leaves it false).
    generation_ran: bool,
    /// `SearchCounters.gen_core_depth_done`.
    core_depth_done: usize,

    pub fn of(counters: *const types.SearchCounters) MissReport {
        return .{
            .stop = if (counters.stack_guard_exhausted)
                .stack
            else if (counters.gen_budget_exhausted)
                .budget
            else
                .none,
            .fuel = counters.phase_fuel_exhausted,
            .nodes = counters.gen_node_capped_passes > 0,
            .forward = counters.forward_saturation_exhausted,
            .generation_ran = counters.gen_last_phase != 0,
            .core_depth_done = counters.gen_core_depth_done,
        };
    }

    /// A limit cut the search short, so an empty result is inconclusive.
    pub fn truncated(self: MissReport) bool {
        return self.stop != .none or self.fuel or self.nodes or self.forward;
    }

    /// The core ladder searched every depth below `max_depth` in full, so
    /// the proof may be deeper than the limit. A node cap in the core leaves
    /// this false on purpose: on the frontier bench, adding depth to such
    /// misses found no more proofs and lost 12 that the defaults find.
    pub fn searchedBelowDepthLimit(self: MissReport, max_depth: usize) bool {
        return self.core_depth_done + 1 >= max_depth;
    }
};

/// The `auto?` parameters for one retry; null leaves a parameter as it is.
pub const Retry = struct {
    depth: ?u64 = null,
    nodes: ?u64 = null,
    fuel: ?u64 = null,
    budget: ?u64 = null,

    /// True when the retry sets the parameter called `name`.
    pub fn sets(self: Retry, name: []const u8) bool {
        inline for (@typeInfo(Retry).@"struct".fields) |field| {
            if (@field(self, field.name) != null and
                std.mem.eql(u8, field.name, name)) return true;
        }
        return false;
    }

    /// Write the retry as `name: value` pairs joined by ", ".
    pub fn writeParams(self: Retry, w: anytype) !void {
        var first = true;
        inline for (@typeInfo(Retry).@"struct".fields) |field| {
            if (@field(self, field.name)) |value| {
                if (!first) try w.writeAll(", ");
                first = false;
                try w.print(field.name ++ ": {d}", .{value});
            }
        }
    }
};

/// The parameters an `auto?` retry should raise after a miss, or null when
/// no parameter can help: the stack guard stopped it, generation never ran,
/// or every limit that was hit is already at its maximum.
///
/// Each limit that was hit is doubled. Depth grows by 2 after a miss nothing
/// cut short, and after one whose core searched every depth below the limit
/// in full. The budget doubles whenever anything else grows, since the other
/// limits spend it.
pub fn retryFor(report: MissReport, gen: types.GenerateOptions) ?Retry {
    if (report.stop == .stack or !report.generation_ran) return null;
    var retry = Retry{};
    if (!report.truncated() or report.searchedBelowDepthLimit(gen.max_depth)) {
        retry.depth = raised(gen.max_depth + 2, gen.max_depth, tunables.max_depth_value);
    }
    if (report.nodes) {
        retry.nodes = raised(gen.max_nodes * 2, gen.max_nodes, tunables.max_nodes_value);
    }
    if (report.fuel) {
        retry.fuel = raised(gen.fuel * 2, gen.fuel, tunables.max_fuel_value);
    }
    const grows = retry.depth != null or retry.nodes != null or retry.fuel != null;
    if (grows or report.stop == .budget) {
        // No budget (`budget: 0`) stays uncapped.
        if (gen.global_budget) |limit| {
            const units = std.math.divCeil(u64, limit, tunables.ticks_per_budget_unit) catch unreachable;
            retry.budget = raised(units * 2, units, tunables.max_budget_value);
        }
    }
    if (std.meta.eql(retry, Retry{})) return null;
    return retry;
}

/// `proposed` clamped to `max`, or null when that does not raise `current`.
fn raised(proposed: u64, current: u64, max: u64) ?u64 {
    const value = @min(proposed, max);
    return if (value > current) value else null;
}
