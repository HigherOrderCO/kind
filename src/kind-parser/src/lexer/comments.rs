use kind_span::Span;

use crate::errors::SyntaxError;
use crate::lexer::tokens::Token;
use crate::Lexer;

impl<'a> Lexer<'a> {
    /// Single line comments
    pub fn lex_comment(&mut self, start: usize) -> (Token, Span) {
        self.next_char();
        let mut is_doc = false;
        if let Some('/') = self.peekable.peek() {
            self.next_char();
            is_doc = true;
        }
        let cmt = self.accumulate_while(&|x| x != '\n');
        (Token::Comment(is_doc, cmt.to_string()), self.mk_span(start))
    }

    /// Parses multi line comments with nested comments
    /// really useful
    pub fn lex_multiline_comment(&mut self, start: usize) -> (Token, Span) {
        let mut size = 0;
        self.next_char();

        let mut next = |p: &mut Lexer<'a>, x: char| {
            size += x.len_utf8();
            p.peekable.next();
        };

        self.comment_depth += 1;

        while let Some(&x) = self.peekable.peek() {
            match x {
                '*' => {
                    next(self, x);
                    if let Some('/') = self.peekable.peek() {
                        self.comment_depth -= 1;
                        if self.comment_depth == 0 {
                            next(self, '/');
                            break;
                        }
                    }
                }
                '/' => {
                    next(self, x);
                    if let Some('*') = self.peekable.peek() {
                        self.comment_depth += 1;
                    }
                }
                _ => (),
            }
            next(self, x);
        }
        self.pos += size;
        if self.comment_depth != 0 {
            (Token::Error(Box::new(SyntaxError::UnfinishedComment(self.mk_span(start)))), self.mk_span(start))
        } else {
            let str = &self.input[..size - 2];
            self.input = &self.input[size..];
            (Token::Comment(false, str.to_string()), self.mk_span(start))
        }
    }
}