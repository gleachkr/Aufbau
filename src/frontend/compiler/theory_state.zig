//! The theory a statement walk has built so far: the parser (which holds the
//! notation), the environment, and the annotation metadata that later
//! statements consult. The compile walk (`pipeline/run.zig`), the editor
//! analysis (`pipeline/analyze.zig`) and the search fixture each own one and
//! hand it to the shared pipeline steps and the checker.

const std = @import("std");
const MM0Parser = @import("../parse_recovery.zig").MM0Parser;
const GlobalEnv = @import("../env.zig").GlobalEnv;
const RewriteRegistry = @import("../rewrite_registry.zig").RewriteRegistry;
const RuleCatalog = @import("./rule_catalog.zig");
const Metadata = @import("./metadata.zig");
const SortVarRegistry = @import("./vars.zig").SortVarRegistry;

pub const FreshBindingMap = std.AutoHashMap(u32, []const Metadata.FreshDecl);
pub const FreshenBindingMap = std.AutoHashMap(u32, []const Metadata.FreshenDecl);
pub const ViewMap = std.AutoHashMap(u32, Metadata.ViewDecl);

pub const TheoryState = struct {
    parser: MM0Parser,
    env: GlobalEnv,
    registry: RewriteRegistry,
    rule_catalog: RuleCatalog.Catalog,
    /// `@fresh`, `@freshen` and `@view` declarations, by rule id.
    fresh_bindings: FreshBindingMap,
    freshen_bindings: FreshenBindingMap,
    views: ViewMap,
    sort_vars: SortVarRegistry,

    /// An empty theory over the `.mm0` text `source`.
    pub fn init(allocator: std.mem.Allocator, source: []const u8) TheoryState {
        return .{
            .parser = MM0Parser.init(source, allocator),
            .env = GlobalEnv.init(allocator),
            .registry = RewriteRegistry.init(allocator),
            .rule_catalog = RuleCatalog.Catalog.init(allocator, source),
            .fresh_bindings = FreshBindingMap.init(allocator),
            .freshen_bindings = FreshenBindingMap.init(allocator),
            .views = ViewMap.init(allocator),
            .sort_vars = SortVarRegistry.init(allocator),
        };
    }
};
