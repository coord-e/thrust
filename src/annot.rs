//! A parser for refinement type and formula annotations.
//!
//! This module provides a parser for `#[thrust::...]` attributes in Thrust. The parser is
//! parameterized by the [`Resolver`] trait, which abstracts over the resolution of variable
//! names. This allows the parser to be used in different contexts with different sets of
//! available variables.
//!
//! The main entry point is [`AnnotParser`], which parses a [`TokenStream`] into a
//! [`rty::RefinedType`] or a [`chc::Formula`].

use rustc_ast::token::{BinOpToken, Delimiter, LitKind, Token, TokenKind};
use rustc_ast::tokenstream::{RefTokenTreeCursor, Spacing, TokenStream, TokenTree};
use rustc_index::IndexVec;
use rustc_span::symbol::Ident;

use crate::chc;
use crate::pretty::PrettyDisplayExt as _;
use crate::rty;

/// A formula in an annotation.
///
/// This can be either a logical formula or the special value `auto` which tells Thrust to infer it.
#[derive(Debug, Clone)]
pub enum AnnotFormula<T> {
    Auto,
    Formula(chc::Formula<T>),
}

impl<T> AnnotFormula<T> {
    pub fn top() -> Self {
        AnnotFormula::Formula(chc::Formula::top())
    }
}

/// A trait for resolving variables in annotations to their logical representation and their sorts.
pub trait Resolver {
    type Output;
    fn resolve(&self, ident: Ident) -> Option<(Self::Output, chc::Sort)>;
}

impl<'a, T> Resolver for &'a T
where
    T: Resolver,
{
    type Output = T::Output;
    fn resolve(&self, ident: Ident) -> Option<(Self::Output, chc::Sort)> {
        (*self).resolve(ident)
    }
}

impl<T> Resolver for Box<T>
where
    T: Resolver + ?Sized,
{
    type Output = T::Output;
    fn resolve(&self, ident: Ident) -> Option<(Self::Output, chc::Sort)> {
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

/// An error that can occur when parsing an attribute.
#[derive(Debug, Clone, thiserror::Error)]
pub enum ParseAttrError {
    #[error("unexpected end of input (expected {expected:?})")]
    UnexpectedEnd { expected: &'static str },
    #[error("unexpected token (expected {expected:?}, got {got:?})")]
    UnexpectedToken {
        expected: &'static str,
        got: TokenTree,
    },
    #[error("unknown identifier {ident:?}")]
    UnknownIdent { ident: Ident },
    #[error("operator {op:?} cannot be applied to a term of sort {}", .sort.display())]
    UnsortedOp { op: &'static str, sort: chc::Sort },
    #[error("unexpected term {context}")]
    UnexpectedTerm { context: &'static str },
    #[error("unexpected formula {context}")]
    UnexpectedFormula { context: &'static str },
}

impl ParseAttrError {
    fn unexpected_end(expected: &'static str) -> Self {
        ParseAttrError::UnexpectedEnd { expected }
    }

    fn unexpected_token(expected: &'static str, got: Token) -> Self {
        let got = TokenTree::Token(got, Spacing::Alone);
        ParseAttrError::UnexpectedToken { expected, got }
    }

    fn unexpected_token_tree(expected: &'static str, got: TokenTree) -> Self {
        ParseAttrError::UnexpectedToken { expected, got }
    }

    fn unknown_ident(ident: Ident) -> Self {
        ParseAttrError::UnknownIdent { ident }
    }

    fn unsorted_op(op: &'static str, sort: chc::Sort) -> Self {
        ParseAttrError::UnsortedOp { op, sort }
    }

    fn unexpected_term(context: &'static str) -> Self {
        ParseAttrError::UnexpectedTerm { context }
    }

    fn unexpected_formula(context: &'static str) -> Self {
        ParseAttrError::UnexpectedFormula { context }
    }
}

type Result<T> = std::result::Result<T, ParseAttrError>;

#[derive(Debug, Clone, Copy)]
enum AmbiguousBinOp {
    Eq,
    Ne,
    Ge,
    Le,
    Gt,
    Lt,
}

#[derive(Debug, Clone)]
enum FormulaOrTerm<T> {
    Formula(chc::Formula<T>),
    Term(chc::Term<T>, chc::Sort),
    BinOp(chc::Term<T>, AmbiguousBinOp, chc::Term<T>),
    Not(Box<FormulaOrTerm<T>>),
}

impl<T> FormulaOrTerm<T> {
    fn into_formula(self) -> Option<chc::Formula<T>> {
        let fo = match self {
            FormulaOrTerm::Formula(fo) => fo,
            FormulaOrTerm::Term { .. } => return None,
            FormulaOrTerm::BinOp(lhs, binop, rhs) => {
                let pred = match binop {
                    AmbiguousBinOp::Eq => chc::KnownPred::EQUAL,
                    AmbiguousBinOp::Ne => chc::KnownPred::NOT_EQUAL,
                    AmbiguousBinOp::Ge => chc::KnownPred::GREATER_THAN_OR_EQUAL,
                    AmbiguousBinOp::Le => chc::KnownPred::LESS_THAN_OR_EQUAL,
                    AmbiguousBinOp::Gt => chc::KnownPred::GREATER_THAN,
                    AmbiguousBinOp::Lt => chc::KnownPred::LESS_THAN,
                };
                chc::Formula::Atom(chc::Atom::new(pred.into(), vec![lhs, rhs]))
            }
            FormulaOrTerm::Not(formula_or_term) => formula_or_term.into_formula()?.not(),
        };
        Some(fo)
    }

    fn into_term(self) -> Option<(chc::Term<T>, chc::Sort)> {
        let (t, s) = match self {
            FormulaOrTerm::Formula { .. } => return None,
            FormulaOrTerm::Term(t, s) => (t, s),
            FormulaOrTerm::BinOp(lhs, AmbiguousBinOp::Eq, rhs) => (lhs.eq(rhs), chc::Sort::bool()),
            FormulaOrTerm::BinOp(lhs, AmbiguousBinOp::Ne, rhs) => (lhs.ne(rhs), chc::Sort::bool()),
            FormulaOrTerm::BinOp(lhs, AmbiguousBinOp::Ge, rhs) => (lhs.ge(rhs), chc::Sort::bool()),
            FormulaOrTerm::BinOp(lhs, AmbiguousBinOp::Le, rhs) => (lhs.le(rhs), chc::Sort::bool()),
            FormulaOrTerm::BinOp(lhs, AmbiguousBinOp::Gt, rhs) => (lhs.gt(rhs), chc::Sort::bool()),
            FormulaOrTerm::BinOp(lhs, AmbiguousBinOp::Lt, rhs) => (lhs.lt(rhs), chc::Sort::bool()),
            FormulaOrTerm::Not(formula_or_term) => {
                let (t, _) = formula_or_term.into_term()?;
                (t.not(), chc::Sort::bool())
            }
        };
        Some((t, s))
    }
}

/// A parser for refinement type annotations and formula annotations.
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

    fn resolve(&self, ident: Ident) -> Result<(T::Output, chc::Sort)> {
        match self.resolver.resolve(ident) {
            Some(res) => Ok(res),
            None => Err(ParseAttrError::unknown_ident(ident)),
        }
    }

    fn parse_formula_or_term_or_tuple(&mut self) -> Result<FormulaOrTerm<T::Output>> {
        let mut formula_or_terms = Vec::new();
        loop {
            formula_or_terms.push(self.parse_formula_or_term()?);
            if let Some(Token {
                kind: TokenKind::Comma,
                ..
            }) = self.look_ahead_token(0)
            {
                self.consume();
            } else {
                break;
            }
        }
        if formula_or_terms.len() == 1 {
            Ok(formula_or_terms.pop().unwrap())
        } else {
            let mut terms = Vec::new();
            let mut sorts = Vec::new();
            for ft in formula_or_terms {
                let (t, s) = ft
                    .into_term()
                    .ok_or_else(|| ParseAttrError::unexpected_formula("in tuple"))?;
                terms.push(t);
                sorts.push(s);
            }
            Ok(FormulaOrTerm::Term(
                chc::Term::tuple(terms),
                chc::Sort::tuple(sorts),
            ))
        }
    }

    fn parse_atom(&mut self) -> Result<FormulaOrTerm<T::Output>> {
        let tt = self.next_token_tree("term or formula")?.clone();

        let t = match &tt {
            TokenTree::Token(t, _) => t,
            TokenTree::Delimited(_, _, Delimiter::Parenthesis, s) => {
                let mut parser = Parser {
                    resolver: self.boxed_resolver(),
                    cursor: s.trees(),
                };
                let formula_or_term = parser.parse_formula_or_term_or_tuple()?;
                parser.end_of_input()?;
                return Ok(formula_or_term);
            }
            _ => return Err(ParseAttrError::unexpected_token_tree("token", tt)),
        };

        let formula_or_term = if let Some((ident, _)) = t.ident() {
            match ident.as_str() {
                "true" => FormulaOrTerm::Formula(chc::Formula::top()),
                "false" => FormulaOrTerm::Formula(chc::Formula::bottom()),
                _ => {
                    let (v, sort) = self.resolve(ident)?;
                    FormulaOrTerm::Term(chc::Term::var(v), sort)
                }
            }
        } else {
            match t.kind {
                TokenKind::Literal(lit) => match lit.kind {
                    LitKind::Integer => FormulaOrTerm::Term(
                        chc::Term::int(lit.symbol.as_str().parse().unwrap()),
                        chc::Sort::int(),
                    ),
                    _ => unimplemented!(),
                },
                _ => {
                    return Err(ParseAttrError::unexpected_token(
                        "identifier, or literal",
                        t.clone(),
                    ));
                }
            }
        };

        Ok(formula_or_term)
    }

    fn parse_postfix(&mut self) -> Result<FormulaOrTerm<T::Output>> {
        let formula_or_term = self.parse_atom()?;

        let mut fields = Vec::new();
        while let Some(Token {
            kind: TokenKind::Dot,
            ..
        }) = self.look_ahead_token(0)
        {
            self.consume();
            match self.next_token("field")? {
                Token {
                    kind: TokenKind::Literal(lit),
                    ..
                } if matches!(lit.kind, LitKind::Integer) => {
                    let idx = lit.symbol.as_str().parse().unwrap();
                    fields.push(idx);
                }
                t => return Err(ParseAttrError::unexpected_token("field", t.clone())),
            }
        }

        if fields.is_empty() {
            return Ok(formula_or_term);
        }

        let (term, sort) = formula_or_term
            .into_term()
            .ok_or_else(|| ParseAttrError::unexpected_formula("before projection"))?;
        let term = fields.iter().fold(term, |acc, idx| acc.tuple_proj(*idx));
        let sort = fields.iter().fold(sort, |acc, idx| acc.tuple_elem(*idx));
        Ok(FormulaOrTerm::Term(term, sort))
    }

    fn parse_prefix(&mut self) -> Result<FormulaOrTerm<T::Output>> {
        let formula_or_term =
            match self.look_ahead_token(0).map(|t| &t.kind) {
                Some(TokenKind::BinOp(BinOpToken::Minus)) => {
                    self.consume();
                    let (operand, sort) = self.parse_postfix()?.into_term().ok_or_else(|| {
                        ParseAttrError::unexpected_formula("after unary - operator")
                    })?;
                    FormulaOrTerm::Term(operand.neg(), sort)
                }
                Some(TokenKind::BinOp(BinOpToken::Star)) => {
                    self.consume();
                    let (operand, sort) = self.parse_postfix()?.into_term().ok_or_else(|| {
                        ParseAttrError::unexpected_formula("after unary * operator")
                    })?;
                    let (t, s) = match sort {
                        chc::Sort::Box(inner) => (chc::Term::box_current(operand), *inner),
                        chc::Sort::Mut(inner) => (chc::Term::mut_current(operand), *inner),
                        _ => return Err(ParseAttrError::unsorted_op("*", sort)),
                    };
                    FormulaOrTerm::Term(t, s)
                }
                Some(TokenKind::BinOp(BinOpToken::Caret)) => {
                    self.consume();
                    let (operand, sort) = self.parse_postfix()?.into_term().ok_or_else(|| {
                        ParseAttrError::unexpected_formula("after unary ^ operator")
                    })?;
                    if let chc::Sort::Mut(inner) = sort {
                        FormulaOrTerm::Term(chc::Term::mut_final(operand), *inner)
                    } else {
                        return Err(ParseAttrError::unsorted_op("^", sort));
                    }
                }
                Some(TokenKind::Not) => {
                    self.consume();
                    let formula_or_term = self.parse_postfix()?;
                    FormulaOrTerm::Not(Box::new(formula_or_term))
                }
                _ => self.parse_postfix()?,
            };
        Ok(formula_or_term)
    }

    fn parse_binop_1(&mut self) -> Result<FormulaOrTerm<T::Output>> {
        let mut formula_or_term = self.parse_prefix()?;

        while let Some(TokenKind::BinOp(BinOpToken::Star)) =
            self.look_ahead_token(0).map(|t| &t.kind)
        {
            self.consume();
            let (lhs, _) = formula_or_term
                .into_term()
                .ok_or_else(|| ParseAttrError::unexpected_formula("before * operator"))?;
            let (rhs, _) = self
                .parse_prefix()?
                .into_term()
                .ok_or_else(|| ParseAttrError::unexpected_formula("after * operator"))?;
            formula_or_term = FormulaOrTerm::Term(lhs.mul(rhs), chc::Sort::int())
        }

        Ok(formula_or_term)
    }

    fn parse_binop_2(&mut self) -> Result<FormulaOrTerm<T::Output>> {
        let mut formula_or_term = self.parse_binop_1()?;

        loop {
            match self.look_ahead_token(0).map(|t| &t.kind) {
                Some(TokenKind::BinOp(BinOpToken::Plus)) => {
                    self.consume();
                    let (lhs, _) = formula_or_term
                        .into_term()
                        .ok_or_else(|| ParseAttrError::unexpected_formula("before + operator"))?;
                    let (rhs, _) = self
                        .parse_binop_1()?
                        .into_term()
                        .ok_or_else(|| ParseAttrError::unexpected_formula("after + operator"))?;
                    formula_or_term = FormulaOrTerm::Term(lhs.add(rhs), chc::Sort::int())
                }
                Some(TokenKind::BinOp(BinOpToken::Minus)) => {
                    self.consume();
                    let (lhs, _) = formula_or_term
                        .into_term()
                        .ok_or_else(|| ParseAttrError::unexpected_formula("before - operator"))?;
                    let (rhs, _) = self
                        .parse_binop_1()?
                        .into_term()
                        .ok_or_else(|| ParseAttrError::unexpected_formula("after - operator"))?;
                    formula_or_term = FormulaOrTerm::Term(lhs.sub(rhs), chc::Sort::int())
                }
                _ => return Ok(formula_or_term),
            }
        }
    }

    fn parse_binop_3(&mut self) -> Result<FormulaOrTerm<T::Output>> {
        let lhs = self.parse_binop_2()?;

        let formula_or_term = match self.look_ahead_token(0).map(|t| &t.kind) {
            Some(TokenKind::EqEq) => {
                self.consume();
                let (lhs, _) = lhs
                    .into_term()
                    .ok_or_else(|| ParseAttrError::unexpected_formula("before == operator"))?;
                let (rhs, _) = self
                    .parse_binop_2()?
                    .into_term()
                    .ok_or_else(|| ParseAttrError::unexpected_formula("after == operator"))?;
                FormulaOrTerm::BinOp(lhs, AmbiguousBinOp::Eq, rhs)
            }
            Some(TokenKind::Ne) => {
                self.consume();
                let (lhs, _) = lhs
                    .into_term()
                    .ok_or_else(|| ParseAttrError::unexpected_formula("before != operator"))?;
                let (rhs, _) = self
                    .parse_binop_2()?
                    .into_term()
                    .ok_or_else(|| ParseAttrError::unexpected_formula("after != operator"))?;
                FormulaOrTerm::BinOp(lhs, AmbiguousBinOp::Ne, rhs)
            }
            Some(TokenKind::Ge) => {
                self.consume();
                let (lhs, _) = lhs
                    .into_term()
                    .ok_or_else(|| ParseAttrError::unexpected_formula("before >= operator"))?;
                let (rhs, _) = self
                    .parse_binop_2()?
                    .into_term()
                    .ok_or_else(|| ParseAttrError::unexpected_formula("after >= operator"))?;
                FormulaOrTerm::BinOp(lhs, AmbiguousBinOp::Ge, rhs)
            }
            Some(TokenKind::Le) => {
                self.consume();
                let (lhs, _) = lhs
                    .into_term()
                    .ok_or_else(|| ParseAttrError::unexpected_formula("before <= operator"))?;
                let (rhs, _) = self
                    .parse_binop_2()?
                    .into_term()
                    .ok_or_else(|| ParseAttrError::unexpected_formula("after <= operator"))?;
                FormulaOrTerm::BinOp(lhs, AmbiguousBinOp::Le, rhs)
            }
            Some(TokenKind::Gt) => {
                self.consume();
                let (lhs, _) = lhs
                    .into_term()
                    .ok_or_else(|| ParseAttrError::unexpected_formula("before > operator"))?;
                let (rhs, _) = self
                    .parse_binop_2()?
                    .into_term()
                    .ok_or_else(|| ParseAttrError::unexpected_formula("after > operator"))?;
                FormulaOrTerm::BinOp(lhs, AmbiguousBinOp::Gt, rhs)
            }
            Some(TokenKind::Lt) => {
                self.consume();
                let (lhs, _) = lhs
                    .into_term()
                    .ok_or_else(|| ParseAttrError::unexpected_formula("before < operator"))?;
                let (rhs, _) = self
                    .parse_binop_2()?
                    .into_term()
                    .ok_or_else(|| ParseAttrError::unexpected_formula("after < operator"))?;
                FormulaOrTerm::BinOp(lhs, AmbiguousBinOp::Lt, rhs)
            }
            _ => return Ok(lhs),
        };

        Ok(formula_or_term)
    }

    fn parse_binop_4(&mut self) -> Result<FormulaOrTerm<T::Output>> {
        let mut formula_or_term = self.parse_binop_3()?;

        while let Some(TokenKind::AndAnd) = self.look_ahead_token(0).map(|t| &t.kind) {
            self.consume();
            let lhs = formula_or_term
                .into_formula()
                .ok_or_else(|| ParseAttrError::unexpected_term("before && operator"))?;
            let rhs = self
                .parse_binop_3()?
                .into_formula()
                .ok_or_else(|| ParseAttrError::unexpected_term("after && operator"))?;
            formula_or_term = FormulaOrTerm::Formula(lhs.and(rhs))
        }

        Ok(formula_or_term)
    }

    fn parse_binop_5(&mut self) -> Result<FormulaOrTerm<T::Output>> {
        let mut formula_or_term = self.parse_binop_4()?;

        while let Some(TokenKind::OrOr) = self.look_ahead_token(0).map(|t| &t.kind) {
            self.consume();
            let lhs = formula_or_term
                .into_formula()
                .ok_or_else(|| ParseAttrError::unexpected_term("before || operator"))?;
            let rhs = self
                .parse_binop_4()?
                .into_formula()
                .ok_or_else(|| ParseAttrError::unexpected_term("after || operator"))?;
            formula_or_term = FormulaOrTerm::Formula(lhs.or(rhs))
        }

        Ok(formula_or_term)
    }

    fn parse_formula_or_term(&mut self) -> Result<FormulaOrTerm<T::Output>> {
        self.parse_binop_5()
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
                parser.end_of_input()?;
                Ok(rty::TupleType::new(rtys).into())
            }
            t => Err(ParseAttrError::unexpected_token_tree("ty", t.clone())),
        }
    }

    pub fn parse_rty(&mut self) -> Result<rty::RefinedType<T::Output>> {
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
            parser.resolver.set_self(self_ident, ty.to_sort());
        }
        let formula = parser
            .parse_formula_or_term()?
            .into_formula()
            .ok_or_else(|| ParseAttrError::unexpected_term("in refinement"))?;
        parser.end_of_input()?;
        Ok(rty::RefinedType::new(ty, formula.into()))
    }

    pub fn parse_annot_formula(&mut self) -> Result<AnnotFormula<T::Output>> {
        if let Some((ident, _)) = self.look_ahead_token(0).and_then(|t| t.ident()) {
            if ident.as_str() == "auto" {
                return Ok(AnnotFormula::Auto);
            }
        }
        let formula = self
            .parse_formula_or_term()?
            .into_formula()
            .ok_or_else(|| ParseAttrError::unexpected_term("in annotation"))?;
        Ok(AnnotFormula::Formula(formula))
    }
}

/// A [`Resolver`] implementation for resolving specific variable as [`rty::RefinedTypeVar::Value`].
struct RefinementResolver<'a, T> {
    resolver: Box<dyn Resolver<Output = T> + 'a>,
    self_: Option<(Ident, chc::Sort)>,
}

impl<'a, T> Resolver for RefinementResolver<'a, T> {
    type Output = rty::RefinedTypeVar<T>;
    fn resolve(&self, ident: Ident) -> Option<(Self::Output, chc::Sort)> {
        if let Some((self_ident, sort)) = &self.self_ {
            if ident == *self_ident {
                return Some((rty::RefinedTypeVar::Value, sort.clone()));
            }
        }
        self.resolver
            .resolve(ident)
            .map(|(v, sort)| (rty::RefinedTypeVar::Free(v), sort))
    }
}

impl<'a, T> RefinementResolver<'a, T> {
    fn new(resolver: impl Resolver<Output = T> + 'a) -> Self {
        Self {
            resolver: Box::new(resolver),
            self_: None,
        }
    }

    fn set_self(&mut self, ident: Ident, sort: chc::Sort) -> &mut Self {
        self.self_ = Some((ident, sort));
        self
    }
}

/// A [`Resolver`] that maps the output of another [`Resolver`].
pub struct MappedResolver<'a, T, F> {
    resolver: Box<dyn Resolver<Output = T> + 'a>,
    map: F,
}

impl<'a, T, F, U> Resolver for MappedResolver<'a, T, F>
where
    F: Fn(T) -> U,
{
    type Output = U;
    fn resolve(&self, ident: Ident) -> Option<(Self::Output, chc::Sort)> {
        self.resolver
            .resolve(ident)
            .map(|(v, sort)| ((self.map)(v), sort))
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

/// A [`Resolver`] that stacks multiple [`Resolver`]s.
///
/// This resolver tries to resolve an identifier by querying a list of resolvers in order.
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
    fn resolve(&self, ident: Ident) -> Option<(Self::Output, chc::Sort)> {
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
}

/// A parser for annotations.
#[derive(Debug, Clone)]
pub struct AnnotParser<T> {
    resolver: T,
}

impl<T> AnnotParser<T> {
    pub fn new(resolver: T) -> Self {
        Self { resolver }
    }
}

impl<T> AnnotParser<T>
where
    T: Resolver,
{
    pub fn parse_rty(&self, ts: TokenStream) -> Result<rty::RefinedType<T::Output>> {
        let mut parser = Parser {
            resolver: &self.resolver,
            cursor: ts.trees(),
        };
        let rty = parser.parse_rty()?;
        parser.end_of_input()?;
        Ok(rty)
    }

    pub fn parse_formula(&self, ts: TokenStream) -> Result<AnnotFormula<T::Output>> {
        let mut parser = Parser {
            resolver: &self.resolver,
            cursor: ts.trees(),
        };
        let formula = parser.parse_annot_formula()?;
        parser.end_of_input()?;
        Ok(formula)
    }
}
