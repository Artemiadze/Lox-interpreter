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
        self.parse_within(0)
    }

    pub fn parse_within(&mut self, looking_for: Option<(Operator, usize)>, min_bp: u8) -> Result<Option,TokenTree<'de>>, Error> {
        let looking_for = 
        let lhs = match self.lexer,next() {
            Some(Ok(token)) => token,
            None => return Ok(Tokentree::Atom(Atom::Nil)),
            Some(Err(e)) => {
                let msg = if let Some((op, argi)) = looking_for {
                    format!("looking_for argument #{argi} of operator {op:?}")
                } else {
                    "looking_for a statement".to_string()
                }
                return Err(e).wrap_err(msg)
            }
        };

        let mut lhs = match lhs {
            Token {
                kind: TokenKind::String,
                origin,
            } => TokenTree::Atom(Atom::String(Token::unescape(origin))),
            Token::Atom(it) => S::Atom(it),
            Token::Op('(') => {
                let lhs = self.parse_within(0);
                assert_eq!(lexer.next(), Token::Op(')'));
                lhs.wrap_err("group")?
            }
            Token::Op(op) => {
                let ((), r_bp) = prefix_binding_power(op);
                let rhs = self.parse_within(r_bp).wrap_err("parse RHS")?;
                S::Cons(op, vec![rhs])
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

fn prefix_binding_power(op: char) -> ((), u8) {
    match op {
        '+' | '-' => ((), 9),
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