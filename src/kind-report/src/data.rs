use std::path::PathBuf;

use kind_span::{Range, SyntaxCtxIndex};

#[derive(Debug, Clone)]
pub enum Severity {
    Error,
    Warning,
    Info,
}

#[derive(Debug, Clone)]
pub enum Color {
    Fst,
    Snd,
    Thr,
    For,
    Fft,
}

#[derive(Debug, Clone)]
pub enum Word {
    White(String),
    Painted(Color, String),
}

#[derive(Debug, Clone)]
pub enum Subtitle {
    Normal(Color, String),
    Phrase(Color, Vec<Word>),
}

#[derive(Debug, Clone)]
pub struct Marking {
    pub position: Range,
    pub color: Color,
    pub text: String,
    pub ctx: SyntaxCtxIndex,
}

#[derive(Debug, Clone)]
pub struct DiagnosticFrame {
    pub code: u32,
    pub severity: Severity,
    pub title: String,
    pub subtitles: Vec<Subtitle>,
    pub hints: Vec<String>,
    pub positions: Vec<Marking>,
}

#[derive(Debug, Clone)]
pub struct Diagnostic {
    pub file_name: PathBuf,
    pub position: Range,
    pub frame: DiagnosticFrame,
}