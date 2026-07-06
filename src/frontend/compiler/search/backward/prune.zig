const acui = @import("./acui.zig");
const def_match = @import("./def_match.zig");

pub const recoverDefiniteMismatch = def_match.recoverDefiniteMismatch;
pub const templateDefiniteMismatch = def_match.templateDefiniteMismatch;
pub const rigidExprMismatch = def_match.rigidExprMismatch;
pub const UnfoldDefInfo = def_match.UnfoldDefInfo;
pub const defBodyForUnfold = def_match.defBodyForUnfold;
pub const unfoldDefBody = def_match.unfoldDefBody;
pub const projectViewBindingsIntoRule = def_match.projectViewBindingsIntoRule;
pub const extractHypPartialBindings = def_match.extractHypPartialBindings;
pub const templateNeedsSemantic = def_match.templateNeedsSemantic;
pub const exprNeedsSemantic = def_match.exprNeedsSemantic;
pub const bindingsNeedSemantic = def_match.bindingsNeedSemantic;

pub const acuiBoundMembersPlausible = acui.acuiBoundMembersPlausible;
pub const acuiUnitIdForHead = acui.acuiUnitIdForHead;
pub const isAcuiUnitExpr = acui.isAcuiUnitExpr;
pub const bindAcuiSpineToUnit = acui.bindAcuiSpineToUnit;
pub const normalizeAcuiUnits = acui.normalizeAcuiUnits;
pub const acuiClosedRegionPlausible = acui.acuiClosedRegionPlausible;
pub const exprUnifiesModuloMeta = acui.exprUnifiesModuloMeta;
