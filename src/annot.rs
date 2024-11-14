use rustc_ast::ast::Attribute;
use rustc_ast::token::{BinOpToken, Delimiter, LitKind, Token, TokenKind};
use rustc_ast::tokenstream::{RefTokenTreeCursor, Spacing, TokenTree};
use rustc_index::IndexVec;
use rustc_span::symbol::Ident;

use crate::chc;
use crate::rty;

#[derive(Debug, Clone)]
pub enum AnnotAtom<T> {
    Auto,
    Param(Ident, rty::RefinedType<T>),
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

    pub fn from_sort(sort: &chc::Sort) -> Self {
        match sort {
            chc::Sort::Box(s) => TermKind::Box(Box::new(TermKind::from_sort(s))),
            chc::Sort::Mut(s) => TermKind::Mut(Box::new(TermKind::from_sort(s))),
            _ => TermKind::Other,
        }
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

impl<T> Resolver for Box<T>
where
    T: Resolver + ?Sized,
{
    type Output = T::Output;
    fn resolve(&self, ident: Ident) -> Option<(Self::Output, TermKind)> {
        (**self).resolve(ident)
    }
}

pub trait ResolverExt: Resolver {
    fn map<'a, U, F>(self, f: F) -> MappedResolver<'a, <Self as Resolver>::Output, F>
    where
        F: Fn(Self::Output) -> U,
        Self: Sized + 'a,
    {
        MappedResolver::new(self, f)
    }
}

impl<T> ResolverExt for T where T: Resolver {}

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
        let got = TokenTree::Token(got, Spacing::Alone);
        Self {
            kind: ParseAttrErrorKind::UnexpectedToken { expected, got },
        }
    }

    fn unexpected_token_tree(expected: &'static str, got: TokenTree) -> Self {
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
    UnexpectedEnd {
        expected: &'static str,
    },
    UnexpectedToken {
        expected: &'static str,
        got: TokenTree,
    },
    UnknownIdent {
        ident: Ident,
    },
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
    fn boxed_resolver<'b>(&'b self) -> Box<dyn Resolver<Output = T::Output> + 'b> {
        Box::new(&self.resolver)
    }

    fn next_token_tree(&mut self, expected: &'static str) -> Result<&TokenTree> {
        let Some(t) = self.cursor.next() else {
            return Err(ParseAttrError::unexpected_end(expected));
        };
        Ok(t)
    }

    fn next_token(&mut self, expected: &'static str) -> Result<&Token> {
        let tt = self.next_token_tree(expected)?;
        if let TokenTree::Token(t, _) = tt {
            Ok(t)
        } else {
            Err(ParseAttrError::unexpected_token_tree(expected, tt.clone()))
        }
    }

    fn look_ahead_token_tree(&mut self, n: usize) -> Option<&TokenTree> {
        self.cursor.look_ahead(n)
    }

    fn look_ahead_token(&mut self, n: usize) -> Option<&Token> {
        if let Some(TokenTree::Token(t, _)) = self.look_ahead_token_tree(n) {
            Some(t)
        } else {
            None
        }
    }

    fn expect_next_token(&mut self, expected: TokenKind, expected_str: &'static str) -> Result<()> {
        let t = self.next_token(expected_str)?;
        if t.kind == expected {
            Ok(())
        } else {
            Err(ParseAttrError::unexpected_token(expected_str, t.clone()))
        }
    }

    fn consume(&mut self) {
        self.cursor.next().unwrap();
    }

    fn end_of_input(&mut self) -> Result<()> {
        if let Ok(t) = self.next_token_tree("") {
            Err(ParseAttrError::unexpected_token_tree(
                "end of input",
                t.clone(),
            ))
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
        let tt = self.next_token_tree("term")?.clone();

        let t = match &tt {
            TokenTree::Token(t, _) => t,
            TokenTree::Delimited(_, _, Delimiter::Parenthesis, s) => {
                let mut parser = Parser {
                    resolver: self.boxed_resolver(),
                    cursor: s.trees(),
                };
                return parser.parse_term();
            }
            _ => unimplemented!(),
        };

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
            _ => {
                return Err(ParseAttrError::unexpected_token_tree(
                    "*, ^, (, identifier, or literal",
                    tt,
                ))
            }
        };
        Ok((term, kind))
    }

    fn parse_term(&mut self) -> Result<(chc::Term<T::Output>, TermKind)> {
        let (lhs, lhs_kind) = self.parse_atom_term()?;

        let term = match self.look_ahead_token(0).map(|t| &t.kind) {
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
            Some(TokenKind::BinOp(BinOpToken::Star)) => {
                self.consume();
                let (rhs, _) = self.parse_atom_term()?;
                lhs.mul(rhs)
            }
            Some(TokenKind::Ge) => {
                self.consume();
                let (rhs, _) = self.parse_atom_term()?;
                lhs.ge(rhs)
            }
            _ => return Ok((lhs, lhs_kind)),
        };

        Ok((term, TermKind::Other))
    }

    fn parse_atom(&mut self) -> Result<chc::Atom<T::Output>> {
        match self.look_ahead_token(0).and_then(|t| t.ident()) {
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
        let pred = match self.next_token("<=, >=, == or !=")? {
            Token {
                kind: TokenKind::EqEq,
                ..
            } => chc::KnownPred::EQUAL,
            Token {
                kind: TokenKind::Ne,
                ..
            } => chc::KnownPred::NOT_EQUAL,
            Token {
                kind: TokenKind::Ge,
                ..
            } => chc::KnownPred::GREATER_THAN_OR_EQUAL,
            Token {
                kind: TokenKind::Le,
                ..
            } => chc::KnownPred::LESS_THAN_OR_EQUAL,
            t => return Err(ParseAttrError::unexpected_token("==", t.clone())),
        };
        let (rhs, _) = self.parse_term()?;
        self.end_of_input()?;
        Ok(chc::Atom::new(pred.into(), vec![lhs, rhs]))
    }

    fn parse_ty(&mut self) -> Result<rty::Type<T::Output>> {
        let tt = self.next_token_tree("ty")?.clone();
        match tt {
            TokenTree::Token(
                Token {
                    kind: TokenKind::Ident(sym, _),
                    ..
                },
                _,
            ) => {
                let ty = match sym.as_str() {
                    "bool" => rty::Type::bool(),
                    "int" => rty::Type::int(),
                    "string" => rty::Type::string(),
                    "fn" => unimplemented!(),
                    "Box" => {
                        self.expect_next_token(TokenKind::Lt, "<")?;
                        let ty = self.parse_ty()?;
                        self.expect_next_token(TokenKind::Gt, ">")?;
                        rty::PointerType::own(ty).into()
                    }
                    s => {
                        let sym = chc::DatatypeSymbol::new(s.to_owned());
                        let tys =
                            if self.look_ahead_token(0).map(|t| &t.kind) == Some(&TokenKind::Lt) {
                                self.consume();
                                let mut tys = IndexVec::new();
                                loop {
                                    tys.push(self.parse_rty()?);
                                    match self.next_token("> or ,")? {
                                        Token {
                                            kind: TokenKind::Comma,
                                            ..
                                        } => {}
                                        Token {
                                            kind: TokenKind::Gt,
                                            ..
                                        } => break,
                                        t => {
                                            return Err(ParseAttrError::unexpected_token(
                                                ">, or ,",
                                                t.clone(),
                                            ))
                                        }
                                    }
                                }
                                tys
                            } else {
                                Default::default()
                            };
                        rty::EnumType::new(sym, tys).into()
                    }
                };
                Ok(ty)
            }
            TokenTree::Token(
                Token {
                    kind: TokenKind::Not,
                    ..
                },
                _,
            ) => Ok(rty::Type::never()),
            TokenTree::Token(
                Token {
                    kind: TokenKind::BinOp(BinOpToken::And),
                    ..
                },
                _,
            ) => {
                let ref_kind = if matches!(self.look_ahead_token(0), Some(Token { kind: TokenKind::Ident(sym, _), .. }) if sym.as_str() == "mut")
                {
                    self.consume();
                    rty::RefKind::Mut
                } else {
                    rty::RefKind::Immut
                };
                let ty = self.parse_ty()?;
                Ok(rty::PointerType::new(ref_kind.into(), ty).into())
            }
            TokenTree::Delimited(_, _, Delimiter::Parenthesis, ts) => {
                let mut parser = Parser {
                    resolver: self.boxed_resolver(),
                    cursor: ts.trees(),
                };
                let mut rtys = Vec::new();
                loop {
                    rtys.push(parser.parse_ty()?);
                    match parser.look_ahead_token(0) {
                        Some(Token {
                            kind: TokenKind::Comma,
                            ..
                        }) => {
                            parser.consume();
                        }
                        None => break,
                        Some(t) => return Err(ParseAttrError::unexpected_token(",", t.clone())),
                    }
                }
                Ok(rty::TupleType::new(rtys).into())
            }
            t => Err(ParseAttrError::unexpected_token_tree("ty", t.clone())),
        }
    }

    fn parse_rty(&mut self) -> Result<rty::RefinedType<T::Output>> {
        let ts = match self.look_ahead_token_tree(0) {
            Some(TokenTree::Delimited(_, _, Delimiter::Brace, ts)) => ts.clone(),
            _ => {
                let ty = self.parse_ty()?;
                return Ok(rty::RefinedType::unrefined(ty));
            }
        };
        self.consume();

        let mut parser = Parser {
            resolver: self.boxed_resolver(),
            cursor: ts.trees(),
        };
        let self_ident = if matches!(
            parser.look_ahead_token(1),
            Some(Token {
                kind: TokenKind::Colon,
                ..
            })
        ) {
            let h = parser.next_token("ident")?;
            let Some((ident, _)) = h.ident() else {
                return Err(ParseAttrError::unexpected_token("ident", h.clone()));
            };
            parser.consume();
            Some(ident)
        } else {
            None
        };
        let ty = parser.parse_ty()?;
        parser.expect_next_token(TokenKind::BinOp(BinOpToken::Or), "|")?;

        let mut parser = Parser {
            resolver: RefinementResolver::new(self.boxed_resolver()),
            cursor: parser.cursor,
        };
        if let Some(self_ident) = self_ident {
            parser
                .resolver
                .set_self(self_ident, TermKind::from_sort(&ty.to_sort()));
        }
        let atom = parser.parse_atom()?;
        Ok(rty::RefinedType::new(ty, atom.into()))
    }

    fn parse_param(&mut self) -> Result<(Ident, rty::RefinedType<T::Output>)> {
        let h = self.next_token("param")?;
        let Some((ident, _)) = h.ident() else {
            return Err(ParseAttrError::unexpected_token("param", h.clone()));
        };
        self.expect_next_token(TokenKind::Colon, ":")?;
        let rty = self.parse_rty()?;
        Ok((ident, rty))
    }

    pub fn parse(&mut self) -> Result<AnnotAtom<T::Output>> {
        match self.look_ahead_token(0).and_then(|t| t.ident()) {
            Some((ident, _)) => {
                if ident.as_str() == "auto" {
                    return Ok(AnnotAtom::Auto);
                }
                if matches!(
                    self.look_ahead_token(1),
                    Some(Token {
                        kind: TokenKind::Colon,
                        ..
                    })
                ) {
                    return self
                        .parse_param()
                        .map(|(ident, rty)| AnnotAtom::Param(ident, rty));
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

struct RefinementResolver<'a, T> {
    resolver: Box<dyn Resolver<Output = T> + 'a>,
    self_: Option<(Ident, TermKind)>,
}

impl<'a, T> Resolver for RefinementResolver<'a, T> {
    type Output = rty::RefinedTypeVar<T>;
    fn resolve(&self, ident: Ident) -> Option<(Self::Output, TermKind)> {
        if let Some((self_ident, kind)) = &self.self_ {
            if ident == *self_ident {
                return Some((rty::RefinedTypeVar::Value, kind.clone()));
            }
        }
        self.resolver
            .resolve(ident)
            .map(|(v, kind)| (rty::RefinedTypeVar::Free(v), kind))
    }
}

impl<'a, T> RefinementResolver<'a, T> {
    fn new(resolver: impl Resolver<Output = T> + 'a) -> Self {
        Self {
            resolver: Box::new(resolver),
            self_: None,
        }
    }

    fn set_self(&mut self, ident: Ident, kind: TermKind) -> &mut Self {
        self.self_ = Some((ident, kind));
        self
    }
}

pub struct MappedResolver<'a, T, F> {
    resolver: Box<dyn Resolver<Output = T> + 'a>,
    map: F,
}

impl<'a, T, F, U> Resolver for MappedResolver<'a, T, F>
where
    F: Fn(T) -> U,
{
    type Output = U;
    fn resolve(&self, ident: Ident) -> Option<(Self::Output, TermKind)> {
        self.resolver
            .resolve(ident)
            .map(|(v, kind)| ((self.map)(v), kind))
    }
}

impl<'a, T, F> MappedResolver<'a, T, F> {
    pub fn new(resolver: impl Resolver<Output = T> + 'a, map: F) -> Self {
        Self {
            resolver: Box::new(resolver),
            map,
        }
    }
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
