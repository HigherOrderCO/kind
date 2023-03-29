//! Diagnostics for the parser.

use kind_diagnostic::Diagnostic;
use kind_lexer::tokens::Token;
use kind_span::Span;

#[derive(Debug)]
pub enum SyntaxDiagnosticKind {
    UnexpectedToken(Token),
}

#[derive(Debug)]
pub struct SyntaxDiagnostic {
    pub data: SyntaxDiagnosticKind,
    pub span: Span,
}

impl SyntaxDiagnosticKind {
    pub fn with(self, span: Span) -> SyntaxDiagnostic {
        SyntaxDiagnostic { data: self, span }
    }
}

impl From<SyntaxDiagnostic> for Diagnostic {
    fn from(_val: SyntaxDiagnostic) -> Self {
        todo!()
    }
}