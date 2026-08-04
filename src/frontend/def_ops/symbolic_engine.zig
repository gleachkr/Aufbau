const SharedContext = @import("./shared_context.zig").SharedContext;
const TransparentMatch =
    @import("./symbolic_engine/transparent_match.zig");
const SemanticSearch =
    @import("./symbolic_engine/semantic_search.zig");
const RewriteApplication =
    @import("./symbolic_engine/rewrite_application.zig");
const DirectedNormalize =
    @import("./symbolic_engine/directed_normalize.zig");
const WitnessState = @import("./symbolic_engine/witness_state.zig");

const Types = @import("./types.zig");
const SymbolicExpr = Types.SymbolicExpr;
const expr_mod = @import("../expr.zig");

pub const SemanticStepCandidate = SemanticSearch.SemanticStepCandidate;

pub const SymbolicEngine = struct {
    shared: *SharedContext,

    pub const defCoversItem = TransparentMatch.defCoversItem;
    pub const planDefCoversItem = TransparentMatch.planDefCoversItem;
    pub const instantiateDefTowardAcuiItem =
        TransparentMatch.instantiateDefTowardAcuiItem;
    pub const planDefToTarget = TransparentMatch.planDefToTarget;
    pub const compareTransparent = TransparentMatch.compareTransparent;
    pub const matchTemplateTransparent =
        TransparentMatch.matchTemplateTransparent;
    pub const instantiateDefTowardExpr =
        TransparentMatch.instantiateDefTowardExpr;
    pub const instantiateDefTowardExprWithProvider =
        TransparentMatch.instantiateDefTowardExprWithProvider;
    pub const expandConcreteDef = TransparentMatch.expandConcreteDef;
    pub const matchTemplateRecState =
        TransparentMatch.matchTemplateRecState;
    pub const tryMatchTemplateStateDirect =
        TransparentMatch.tryMatchTemplateStateDirect;
    pub const matchTemplateSemantic = SemanticSearch.matchTemplateSemantic;
    pub const collectSemanticStepCandidatesExpr =
        SemanticSearch.collectSemanticStepCandidatesExpr;
    pub const collectSemanticStepCandidatesSymbolic =
        SemanticSearch.collectSemanticStepCandidatesSymbolic;
    pub const matchTemplateSemanticState =
        SemanticSearch.matchTemplateSemanticState;
    pub const matchSymbolicToExprSemantic =
        SemanticSearch.matchSymbolicToExprSemantic;
    pub const matchSymbolicToSymbolicSemantic =
        SemanticSearch.matchSymbolicToSymbolicSemantic;
    pub const matchSymbolicAcuiLeafToExprSemantic =
        SemanticSearch.matchSymbolicAcuiLeafToExprSemantic;
    pub const applyRewriteRuleToExpr =
        RewriteApplication.applyRewriteRuleToExpr;
    pub const applyRewriteRuleToSymbolic =
        RewriteApplication.applyRewriteRuleToSymbolic;
    pub const matchTemplateRewriteNormalized =
        DirectedNormalize.matchTemplateRewriteNormalized;

    pub const boundValueFromSeed = WitnessState.boundValueFromSeed;
    pub const chooseRepresentative = WitnessState.chooseRepresentative;
    pub const chooseRepresentativeSymbolic =
        WitnessState.chooseRepresentativeSymbolic;
    pub const symbolicExprEql = WitnessState.symbolicExprEql;
    pub const assignBinderValue = WitnessState.assignBinderValue;
    pub const finalizeBoundValue = WitnessState.finalizeBoundValue;
    pub const concreteBindingMatchExpr =
        WitnessState.concreteBindingMatchExpr;
    pub const materializeResolvedBoundValue =
        WitnessState.materializeResolvedBoundValue;
    pub const projectMaterializedExpr =
        WitnessState.projectMaterializedExpr;
    pub const collectUnresolvedRootsInBoundValue =
        WitnessState.collectUnresolvedRootsInBoundValue;
    pub const collectUnresolvedRootsInSymbolicOwned =
        WitnessState.collectUnresolvedRootsInSymbolicOwned;
    pub const collectConcreteDepsInBoundValue =
        WitnessState.collectConcreteDepsInBoundValue;
    pub const collectConcreteDepsInSymbolicRoot =
        WitnessState.collectConcreteDepsInSymbolicRoot;
    pub const applyMaterializedDummyAssignments =
        WitnessState.applyMaterializedDummyAssignments;
    pub const resolveDummySlot = WitnessState.resolveDummySlot;
    pub const currentWitnessExpr = WitnessState.currentWitnessExpr;
    pub const isProvisionalWitnessExpr =
        WitnessState.isProvisionalWitnessExpr;
    pub const makeConcreteBoundValue =
        WitnessState.makeConcreteBoundValue;
    pub const makeSymbolicBoundValue =
        WitnessState.makeSymbolicBoundValue;
    pub const concreteExprsMatchMode =
        WitnessState.concreteExprsMatchMode;
    pub const invalidateRepresentativeCaches =
        WitnessState.invalidateRepresentativeCaches;
    pub const matchSymbolicDummyState =
        WitnessState.matchSymbolicDummyState;
    pub const matchDummyToSymbolic = WitnessState.matchDummyToSymbolic;

    pub fn allocSymbolic(
        self: *SymbolicEngine,
        symbolic: SymbolicExpr,
    ) anyerror!*const SymbolicExpr {
        // Symbolic node creation is the def-eq engine's work chokepoint, the
        // way intern attempts are the concrete side's; count it toward the
        // per-call cost budget (see `expr.zig` `work_ticks_sym`).
        expr_mod.work_ticks_sym +%= 1;
        // Populate the cached structural hash once, so search-memo keys and the
        // intern probe read it in O(1) instead of re-walking the subtree
        // (children are already cached, so this is O(arity)).
        var value = symbolic;
        switch (value) {
            .app => |*app| app.hash = Types.computeAppHash(app.term_id, app.args),
            else => {},
        }
        // Hash-cons: structurally identical nodes share one scratch-arena
        // allocation, collapsing the exponential re-expansion of def-unfold
        // (church/martin_lof) that otherwise churns the allocator and defeats
        // memo dedup by producing distinct pointers for equal subtrees. Nodes
        // still live in the per-context scratch arena (reclaimed at
        // `SharedContext.deinit`); they never escape and are never individually
        // freed. See `SharedContext.internSymbolic` for the soundness argument.
        return self.shared.internSymbolic(value);
    }
};
