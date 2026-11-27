//! What the client said it supports.

const lsp = @import("lsp");

const types = lsp.types.flat;

pub fn snippets(capabilities: types.ClientCapabilities) bool {
    const text_document = capabilities.textDocument orelse return false;
    const completion = text_document.completion orelse return false;
    const item = completion.completionItem orelse return false;
    return item.snippetSupport orelse false;
}

pub fn workDoneProgress(capabilities: types.ClientCapabilities) bool {
    const window = capabilities.window orelse return false;
    return window.workDoneProgress orelse false;
}

pub fn showDocument(capabilities: types.ClientCapabilities) bool {
    const window = capabilities.window orelse return false;
    const show_document = window.showDocument orelse return false;
    return show_document.support;
}

pub fn prepareRename(capabilities: types.ClientCapabilities) bool {
    const text_document = capabilities.textDocument orelse return false;
    const rename = text_document.rename orelse return false;
    return rename.prepareSupport orelse false;
}

pub fn hierarchicalDocumentSymbols(
    capabilities: types.ClientCapabilities,
) bool {
    const text_document = capabilities.textDocument orelse return false;
    const document_symbol = text_document.documentSymbol orelse return false;
    return document_symbol.hierarchicalDocumentSymbolSupport orelse false;
}
