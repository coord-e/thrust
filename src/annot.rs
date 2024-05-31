use rustc_ast::ast::Attribute;
use rustc_ast::token::{BinOpToken, Delimiter, LitKind, Token, TokenKind};
use rustc_ast::tokenstream::{RefTokenTreeCursor, TokenTree};
use rustc_span::symbol::Ident;

use crate::chc;

#[derive(Debug, Clone)]
pub enum AnnotAtom<T> {
    Auto,
    Atom(chc::Atom<T>),
}

#[derive(Debug, Clone)]
pub enum TermKind {
    Box(Box<TermKind>),
    Mut(Box<TermKind>),
    Other,
}

impl TermKind {
    pub fn box_(inner: TermKind) -> Self {
        TermKind::Box(Box::new(inner))
    }

    pub fn mut_(inner: TermKind) -> Self {
        TermKind::Mut(Box::new(inner))
    }

    pub fn other() -> Self {
        TermKind::Other
    }
}

pub trait Resolver {
    type Output;
    fn resolve(&self, ident: Ident) -> Option<(Self::Output, TermKind)>;
}

impl<'a, T> Resolver for &'a T
where
    T: Resolver,
{
    type Output = T::Output;
    fn resolve(&self, ident: Ident) -> Option<(Self::Output, TermKind)> {
        (*self).resolve(ident)
    }
}

#[derive(Debug, Clone)]
pub struct ParseAttrError {
    kind: ParseAttrErrorKind,
}

impl ParseAttrError {
    fn unexpected_end(expected: &'static str) -> Self {
        Self {
            kind: ParseAttrErrorKind::UnexpectedEnd { expected },
        }
    }

    fn unexpected_token(expected: &'static str, got: Token) -> Self {
        Self {
            kind: ParseAttrErrorKind::UnexpectedToken { expected, got },
        }
    }

    fn invalid_attribute() -> Self {
        Self {
            kind: ParseAttrErrorKind::InvalidAttribute,
        }
    }

    fn unknown_ident(ident: Ident) -> Self {
        Self {
            kind: ParseAttrErrorKind::UnknownIdent { ident },
        }
    }

    pub fn kind(&self) -> &ParseAttrErrorKind {
        &self.kind
    }
}

#[derive(Debug, Clone)]
pub enum ParseAttrErrorKind {
    InvalidAttribute,
    UnexpectedEnd { expected: &'static str },
    UnexpectedToken { expected: &'static str, got: Token },
    UnknownIdent { ident: Ident },
}

type Result<T> = std::result::Result<T, ParseAttrError>;

struct Parser<'a, T> {
    resolver: T,
    cursor: RefTokenTreeCursor<'a>,
}

impl<'a, T> Parser<'a, T>
where
    T: Resolver,
{
    fn next_token(&mut self, expected: &'static str) -> Result<&Token> {
        let Some(t) = self.cursor.next() else {
            return Err(ParseAttrError::unexpected_end(expected));
        };
        match t {
            TokenTree::Token(t, _) => Ok(t),
            TokenTree::Delimited { .. } => unimplemented!(),
        }
    }

    fn look_ahead(&mut self) -> Option<&Token> {
        self.cursor.look_ahead(0).map(|t| match t {
            TokenTree::Token(t, _) => t,
            TokenTree::Delimited { .. } => unimplemented!(),
        })
    }

    fn consume(&mut self) {
        self.cursor.next().unwrap();
    }

    fn end_of_input(&mut self) -> Result<()> {
        if let Ok(t) = self.next_token("") {
            Err(ParseAttrError::unexpected_token("end of input", t.clone()))
        } else {
            Ok(())
        }
    }

    fn resolve(&self, ident: Ident) -> Result<(T::Output, TermKind)> {
        match self.resolver.resolve(ident) {
            Some(res) => Ok(res),
            None => Err(ParseAttrError::unknown_ident(ident)),
        }
    }

    fn parse_atom_term(&mut self) -> Result<(chc::Term<T::Output>, TermKind)> {
        let t = self.next_token("term")?.clone();

        if let Some((ident, _)) = t.ident() {
            let (v, kind) = self.resolve(ident)?;
            return Ok((chc::Term::var(v), kind));
        }
        let (term, kind) = match t.kind {
            TokenKind::Literal(lit) => match lit.kind {
                LitKind::Integer => (
                    chc::Term::int(lit.symbol.as_str().parse().unwrap()),
                    TermKind::Other,
                ),
                _ => unimplemented!(),
            },
            TokenKind::BinOp(BinOpToken::Star) => {
                let (operand, kind) = self.parse_atom_term()?;
                match kind {
                    TermKind::Box(inner) => (chc::Term::box_current(operand), *inner),
                    TermKind::Mut(inner) => (chc::Term::mut_current(operand), *inner),
                    TermKind::Other => panic!("unexpected term kind"),
                }
            }
            TokenKind::BinOp(BinOpToken::Caret) => {
                let (operand, kind) = self.parse_atom_term()?;
                if let TermKind::Mut(inner) = kind {
                    (chc::Term::mut_final(operand), *inner)
                } else {
                    panic!("unexpected term kind");
                }
            }
            TokenKind::OpenDelim(Delimiter::Parenthesis) => {
                let (term, kind) = self.parse_term()?;
                if self.next_token(")")?.kind != TokenKind::CloseDelim(Delimiter::Parenthesis) {
                    return Err(ParseAttrError::unexpected_token(")", t.clone()));
                }
                (term, kind)
            }
            _ => {
                return Err(ParseAttrError::unexpected_token(
                    "*, ^, (, identifier, or literal",
                    t.clone(),
                ))
            }
        };
        Ok((term, kind))
    }

    fn parse_term(&mut self) -> Result<(chc::Term<T::Output>, TermKind)> {
        let (lhs, lhs_kind) = self.parse_atom_term()?;

        let term = match self.look_ahead().map(|t| &t.kind) {
            Some(TokenKind::BinOp(BinOpToken::Plus)) => {
                self.consume();
                let (rhs, _) = self.parse_atom_term()?;
                lhs.add(rhs)
            }
            Some(TokenKind::BinOp(BinOpToken::Minus)) => {
                self.consume();
                let (rhs, _) = self.parse_atom_term()?;
                lhs.sub(rhs)
            }
            _ => return Ok((lhs, lhs_kind)),
        };

        Ok((term, TermKind::Other))
    }

    fn parse_atom(&mut self) -> Result<chc::Atom<T::Output>> {
        match self.look_ahead().and_then(|t| t.ident()) {
            Some((ident, _)) => {
                if ident.as_str() == "true" {
                    self.consume();
                    return Ok(chc::Atom::top());
                }
                if ident.as_str() == "false" {
                    self.consume();
                    return Ok(chc::Atom::bottom());
                }
            }
            _ => {}
        }

        let (lhs, _) = self.parse_atom_term()?;
        let pred = match self.next_token("== or !=")? {
            Token {
                kind: TokenKind::EqEq,
                ..
            } => chc::KnownPred::EQUAL,
            Token {
                kind: TokenKind::Ne,
                ..
            } => chc::KnownPred::NOT_EQUAL,
            t => return Err(ParseAttrError::unexpected_token("==", t.clone())),
        };
        let (rhs, _) = self.parse_term()?;
        self.end_of_input()?;
        Ok(chc::Atom::new(pred.into(), vec![lhs, rhs]))
    }

    pub fn parse(&mut self) -> Result<AnnotAtom<T::Output>> {
        match self.look_ahead().and_then(|t| t.ident()) {
            Some((ident, _)) => {
                if ident.as_str() == "auto" {
                    return Ok(AnnotAtom::Auto);
                }
            }
            _ => {}
        }
        self.parse_atom().map(AnnotAtom::Atom)
    }
}

pub fn parse<T: Resolver>(resolver: T, attr: &Attribute) -> Result<AnnotAtom<T::Output>> {
    use rustc_ast::{AttrArgs, AttrKind, DelimArgs};

    // TODO: Maybe we should move this to analyze and only accept TokenStream
    let AttrKind::Normal(attr) = &attr.kind else {
        return Err(ParseAttrError::invalid_attribute());
    };

    let AttrArgs::Delimited(DelimArgs { tokens, .. }, ..) = &attr.item.args else {
        return Err(ParseAttrError::invalid_attribute());
    };

    let cursor = tokens.trees();
    let mut parser = Parser { resolver, cursor };
    parser.parse()
}

pub struct StackedResolver<'a, T> {
    resolvers: Vec<Box<dyn Resolver<Output = T> + 'a>>,
}

impl<'a, T> Default for StackedResolver<'a, T> {
    fn default() -> Self {
        Self { resolvers: vec![] }
    }
}

impl<'a, T> Resolver for StackedResolver<'a, T> {
    type Output = T;
    fn resolve(&self, ident: Ident) -> Option<(Self::Output, TermKind)> {
        for resolver in &self.resolvers {
            if let Some(res) = resolver.resolve(ident) {
                return Some(res);
            }
        }
        None
    }
}

impl<'a, T> StackedResolver<'a, T> {
    pub fn resolver(mut self, resolver: impl Resolver<Output = T> + 'a) -> Self {
        self.resolvers.push(Box::new(resolver));
        self
    }

    pub fn parse(self, attr: &Attribute) -> Result<AnnotAtom<T>> {
        parse(self, attr)
    }
}

pub type AnnotParser<'a, T> = StackedResolver<'a, T>;
