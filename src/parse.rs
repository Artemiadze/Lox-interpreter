use miette::{Diagnostic, Error, LabeledSpan, SourceSpan, WrapErr};
use std::{borrow::Cow, fmt, io::BufRead};
use thiserror::Error;

use crate::{
    lex::{Token, TokenKind},
    Lexer,
};

pub struct Parser<'de> {
    whole: &'de str,
    lexer: Lexer<'de>,
}

pub struct Ast;

#[derive(Diagnostic, Debug, Error)]
#[error("Unexpected EOF")]
pub struct Eof;

impl<'de> Parser<'de> {
    pub fn new(input: &'de str) -> Self {
        Self {
            whole: input,
            lexer: Lexer::new(input)
        }
    }

    pub fn parse(mut self) -> Result<TokenTree<'de>, Error> {
        self.parse_within(None, 0)
    }

    pub fn parse_within(&mut self, looking_for: Option<(Operator, usize)>, min_bp: u8) -> Result<Option,TokenTree<'de>>, Error> {
        let looking_for_msg = || {
            if let Some((op, argi)) = looking_for {
                format!("looking_for argument #{argi} for operator {op:?}")
            } else {
                "looking_for a statement".to_string()
            }
        }
        let lhs = match self.lexer,next() {
            Some(Ok(token)) => token,
            None => return Ok(Tokentree::Atom(Atom::Nil)),
            Some(Err(e)) => {
                let msg = looking_for();
                return Err(e).wrap_err(msg)
            }
        };

        let mut lhs = match lhs {
            // atoms
            Token {
                kind: TokenKind::String,
                origin,
            } => TokenTree::Atom(Atom::String(Token::unescape(origin))),
            Token {
                kind: TokenKind::Number(n),
                ..
            } => TokenTree::Atom(Atom::Number(n)),
            Token {
                kind: TokenKind::True,
                ..
            } => TokenTree::Atom(Atom::Bool(true)),
            Token {
                kind: TokenKind::False,
                ..
            } => TokenTree::Atom(Atom::Bool(false)),
            Token {
                kind: TokenKind::Ident,
                origin,
            } => TokenTree:: Atom(Atom::Ident(origin)),

            // Groups
            Token {
                kind: TokenKind::LeftParen | TokenKind::LeftBrace,
                ..
            } => {
                let lhs = self.parse_within(looking_for, 0);
                let terminator = match lhs.kind {
                    TokenKind::LeftParen => TokenKind::RightParen,
                    TokenKind::LeftBrace => TokenKind::RightBrace,
                    - => unreachable!("by the outer match arm pattern"),
                };
                let lhs = self.parse_within(looking_for, 0).wrap_err("group")?;
                match self.lexer.next(){
                    Some(token) if token == terminator => {},
                    Some(token) => {
                        return Err(miette::miette!(
                            labels = vec![
                                LabeledSpan::at(self.byte - literal.len()..self.byte, "this numeric literal"),
                            ],
                            "{e}",
                        }.with_source_code(self.whole.to_string())).wrap_err(looking_for_msg());
                    }
                    None => {
                        return Err(Eof).wrap_err(looking_for_msg());
                    }
                }
                assert_eq!(self.lexer.next().kind, terminator);
                lhs
            }

            //prefix expressions
            Token {
                kind: TokenKind::Bang | TokenKind::Print | TokenKind::Minus,
                ..
            } =>  {
                let op = match lhs.kind {
                    TokenKind::Bang => Operator::Bang,
                    TokenKind::Print => Operator::Print,
                    TokenKind::Minus => Operator::Minus,
                    - => unreachable!("by the outer match arm pattern"),
                };
                let ((), r_bp) = prefix_binding_power(op);
                let rhs = self
                    .parse_within(Some((op, 0)), r_bp)
                    .wrap_err("parse RHS")?;
                TokenTree::Cons(op, vec![rhs])
            }  
            t => panic!("bad token: {:?}", t),
        };

        loop {
            let op = self.lexer.peek();
            let op = match op.transpose()? {
                Token::Eof => break,
                Some(Token{
                    kind: TokenKind::Op(op),
                    ..
                }) => op,
                t => panic!("bad token: {:?}", t),
            };

            if let Some((l_bp, ())) = postfix_binding_power(op) {
                if l_bp < min_bp {
                    break;
                }
                
                lexer.next();
                lhs = if op == '[' {
                    let rhs = self.parse_within(0);
                    assert_eq!(lexer.next(), Token::Op(']'));
                    S::Cons(op, vec![lhs, rhs])
                } else {
                    S::Cons(op, vec![lhs])
                };
                continue;
            }

            if let Some((l_bp, r_bp)) = infix_binding_power(op) {
                if l_bp < min_bp {
                    break;
                }
                
                lexer.next();
                lhs = if op == '?' {
                    let mhs = self.parse_within(0);
                    assert_eq!(lexer.next(), Token::Op(':'));
                    let rhs = self.parse_within(r_bp);
                    S::Cons(op, vec![lhs, mhs, rhs])
                } else {
                    let rhs = self.parse_within(r_bp);
                    S::Cons(op, vec![lhs, rhs])
                };
                continue;
            }
            break;
        }
        Ok(lhs)
    }
}

#[derive(Debug, Clone, PartialEq)]
pub enum Atom<'de> {
    String(Cow<'de, str>),
    Number(f64),
    Nil,
    Bool(bool),
    Ident(&'de str),
    Super,
    This,
}

#[derive(Debug, Clone, Copy, PartialEq)]
pub enum Operator{
    Minus,
    Plus,
    Star,
    BangEqual,
    EqualEqual,
    LessEqual,
    GreaterEqual,
    Less,
    Greater,
    Slash,
    Bang,
    Equal,
    And,
    Or,
    If,
    For,
    Class,
    Fun,
    Print,
    Return,
    Field,
    Var,
    While,
}

#[derive(Debug, Clone, Copy, PartialEq)]
enum Delimiter {
    Paren,
    Brace,
}

#[derive(Debug, Clone, PartialEq)]
enum TokenTree<'de> {
    Atom(Atom<'de>),
    Cons(Operator, Vec<TokenTree<'de>>),
}

impl fmt::Display for TokenTree<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            S::Atom(i) => write!(f, "{}", i),
            S::Cons(head, rest) => {
                write!(f, "({}", head)?;
                for s in rest {
                    write!(f, " {}", s)?
                }
                write!(f, ")")
            }
        }
    }
}

fn prefix_binding_power(op: Operator) -> ((), u8) {
    match op {
        Operator::Bang | Operator::Print | Operator::Minus => ((), 9),
        _ => panic!("bad op: {:?}", op),
    }
}

fn postfix_binding_power(op: char) -> Option<(u8, ())> {
    let res = match op {
        '!' => (11, ()),
        '[' => (11, ()),
        _ => return None,
    };
    Some(res)
}

fn infix_binding_power(op: char) -> Option<(u8, u8)> {
    let res = match op {
        '=' => (2, 1),
        '?' => (4, 3),
        '+' | '-' => (5, 6),
        '*' | '/' => (7, 8),
        '.' => (14, 13),
        _ => return None,
    };
    Some(res)
}