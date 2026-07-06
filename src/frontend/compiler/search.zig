const root = @import("./search/root.zig");
pub const NameExprMap = root.NameExprMap;
pub const LabelIndexMap = root.LabelIndexMap;
pub const FreshDecl = root.FreshDecl;
pub const FreshenDecl = root.FreshenDecl;
pub const ViewDecl = root.ViewDecl;
pub const SortVarRegistry = root.SortVarRegistry;
pub const Goal = root.Goal;
pub const Context = root.Context;
pub const AttemptOptions = root.AttemptOptions;
pub const AttemptResultOwnership = root.AttemptResultOwnership;
pub const AttemptResult = root.AttemptResult;
pub const UnresolvedHypothesis = root.UnresolvedHypothesis;
pub const ApplyCandidate = root.ApplyCandidate;
pub const ApplyResults = root.ApplyResults;
pub const SearchCounters = root.SearchCounters;
pub const HypLookupPhase = root.HypLookupPhase;
pub const HypLookupFallback = root.HypLookupFallback;
pub const ApplyOptions = root.ApplyOptions;
pub const ExactCandidate = root.ExactCandidate;
pub const ExactResults = root.ExactResults;
pub const ExactOptions = root.ExactOptions;
pub const SourceSuggestion = root.SourceSuggestion;
pub const SourceSuggestions = root.SourceSuggestions;
pub const SourceSuggestionOptions = root.SourceSuggestionOptions;
pub const SearchStatus = root.SearchStatus;
pub const SearchPlaceholder = root.SearchPlaceholder;
pub const searchPlaceholders = root.searchPlaceholders;
pub const Span = root.Span;
pub const GenerateOptions = root.GenerateOptions;
pub const weightedTicks = root.weightedTicks;
pub const SearchSession = root.SearchSession;

pub const tryCandidate = root.tryCandidate;
pub const apply = root.apply;
pub const applyWithSession = root.applyWithSession;
pub const exact = root.exact;
pub const exactWithSession = root.exactWithSession;
pub const suggestionsAtSourceOffset = root.suggestionsAtSourceOffset;
pub const clipper = root.clipper;
pub const shape = root.shape;

comptime {
    if (@import("builtin").is_test) {
        _ = @import("./search/tests.zig");
        _ = @import("./search/clipper.zig");
        _ = @import("./search/shape.zig");
        _ = @import("./search/ref_index.zig");
    }
}
