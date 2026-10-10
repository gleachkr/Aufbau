const std = @import("std");
const MM0Stmt = @import("../../parse_recovery.zig").MM0Stmt;
const ProofScript = @import("../../proof_script.zig");
const Span = ProofScript.Span;
const CompilerEmit = @import("../emit.zig");
const CompilerVars = @import("../vars.zig");
const CompilerDiag = @import("../../diag.zig");
const CompilerContext = @import("../context.zig").CompilerContext;
const Common = @import("common.zig");
const TheoryState = @import("../theory_state.zig").TheoryState;

const Output = Common.Output;
const ProofItemStream = Common.ProofItemStream;
const DiagnosticSource = CompilerDiag.DiagnosticSource;
const drainAnchoredLocalProofItems = Common.drainAnchoredLocalProofItems;
const drainTrailingLocalProofItems = Common.drainTrailingLocalProofItems;
const fillPublicDefBody = Common.fillPublicDefBody;
const processAssertion = Common.processAssertion;
const rejectLocalTermReferences = Common.rejectLocalTermReferences;
const validateDefinitionBody = Common.validateDefinitionBody;

pub fn run(
    self: *CompilerContext,
    allocator: std.mem.Allocator,
    emit: ?*Output,
) !void {
    var theory = TheoryState.init(allocator, self.source);
    const parser = &theory.parser;
    const env = &theory.env;
    // Snapshot pretty-printed statements on every exit path, while the parser
    // (the notation provider) and env still live in this call's arena.
    defer if (self.statement_sink) |sink| sink.capture(parser, env);
    var proof_stream = if (self.proof_source) |proof|
        ProofItemStream.init(allocator, proof)
    else
        null;
    var last_stmt: ?MM0Stmt = null;

    while (true) {
        try Common.prepareNextPublicStatement(self, parser, env);
        try drainAnchoredLocalProofItems(
            self,
            allocator,
            &theory,
            &proof_stream,
            emit,
        );

        const stmt = try Common.nextPublicStatement(self, parser, env) orelse
            break;
        last_stmt = stmt;
        CompilerVars.validateSortVarCollisions(parser, &theory.sort_vars) catch |err| {
            self.setIfMissing(
                CompilerDiag.mm0StatementDiagnostic(parser, stmt, err),
            );
            return err;
        };
        try rejectLocalTermReferences(self, env, stmt);
        switch (stmt) {
            .sort => |sort_stmt| {
                if (emit) |out| {
                    try out.sort_names.append(allocator, sort_stmt.name);
                    try out.sorts.append(allocator, sort_stmt.modifiers);
                    try out.statements.append(allocator, .{
                        .cmd = .Sort,
                        .body = &.{},
                    });
                }
                Common.registerSort(
                    self,
                    parser,
                    env,
                    sort_stmt,
                    &theory.sort_vars,
                ) catch |err| {
                    self.setIfMissing(
                        CompilerDiag.mm0StatementDiagnostic(
                            parser,
                            stmt,
                            CompilerDiag.narrowDiagnosticError(err),
                        ),
                    );
                    return err;
                };
            },
            .term => |term_stmt| {
                var filled_term_stmt = term_stmt;
                var filled_body_span: ?Span = null;
                if (term_stmt.is_def and term_stmt.body == null) {
                    const filled = try fillPublicDefBody(
                        self,
                        allocator,
                        parser,
                        &proof_stream,
                        term_stmt,
                    );
                    filled_term_stmt = filled.stmt;
                    filled_body_span = filled.body_span;
                }

                const term_stmt_copy = filled_term_stmt;
                const term_diag_source: DiagnosticSource = if (filled_body_span != null)
                    .proof
                else
                    .mm0;
                const term_diag_span = filled_body_span;
                validateDefinitionBody(
                    self,
                    allocator,
                    parser,
                    env,
                    filled_term_stmt,
                    term_diag_source,
                    term_diag_span,
                ) catch |err| {
                    return err;
                };
                if (emit) |out| {
                    const term_record = CompilerEmit.compileTermRecord(
                        allocator,
                        parser,
                        filled_term_stmt,
                    ) catch |err| {
                        self.setIfMissing(
                            CompilerDiag.mm0StatementDiagnostic(
                                parser,
                                MM0Stmt{ .term = term_stmt_copy },
                                err,
                            ),
                        );
                        return err;
                    };
                    try out.terms.append(allocator, term_record);
                    const body = if (filled_term_stmt.is_def)
                        CompilerEmit.buildDefProofBody(
                            allocator,
                            parser,
                            filled_term_stmt,
                        ) catch |err| {
                            self.setIfMissing(
                                CompilerDiag.mm0StatementDiagnostic(
                                    parser,
                                    MM0Stmt{ .term = term_stmt_copy },
                                    err,
                                ),
                            );
                            return err;
                        }
                    else
                        &.{};
                    try out.statements.append(allocator, .{
                        .cmd = .TermDef,
                        .body = body,
                    });
                }
                Common.registerTerm(
                    self,
                    allocator,
                    parser,
                    env,
                    &theory.registry,
                    filled_term_stmt,
                    .mm0,
                ) catch |err| {
                    self.setIfMissing(
                        CompilerDiag.mm0StatementDiagnostic(
                            parser,
                            MM0Stmt{ .term = term_stmt_copy },
                            CompilerDiag.narrowDiagnosticError(err),
                        ),
                    );
                    return err;
                };
            },
            .assertion => |assertion| {
                processAssertion(
                    self,
                    allocator,
                    &theory,
                    &proof_stream,
                    assertion,
                    emit,
                ) catch |err| {
                    self.setIfMissing(
                        CompilerDiag.mm0StatementDiagnostic(
                            parser,
                            MM0Stmt{ .assertion = assertion },
                            CompilerDiag.narrowDiagnosticError(err),
                        ),
                    );
                    return err;
                };
            },
        }
    }

    CompilerVars.validateSortVarCollisions(parser, &theory.sort_vars) catch |err| {
        if (last_stmt) |stmt| {
            self.setIfMissing(
                CompilerDiag.mm0StatementDiagnostic(parser, stmt, err),
            );
        }
        return err;
    };

    if (proof_stream) |*proofs| {
        try drainTrailingLocalProofItems(
            self,
            allocator,
            &theory,
            proofs,
            emit,
        );
    }
}
