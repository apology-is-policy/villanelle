//! The text of certificates (`docs/v2/facts.md`, [V5]). The format is in
//! `docs/v2/oracle.md`, in the section on the certificate text.
//!
//! [`write_body`] writes the tables of one body (history atoms, terms, rows,
//! numbers of fields, diagram nodes) and the questions that were asked of it:
//! for each the goal, the premises that its certificate names, the names of
//! the instances and the lemmas with their proofs. [`read`] makes of a text
//! the bodies it states, and [`Body::validate`] gives every question of a
//! body to a kernel.
//!
//! A text states queries and their certificates, and what reads it needs
//! nothing else: not the program, and not the checker. That the queries are
//! the ones that the program gives rise to is outside it, as it is outside
//! the kernel ([V4]).
//!
//! The reader is on the kernel's side. It uses the integers, the diagram and
//! the data of [`crate::terms`], and nothing of the search.

use crate::bdd::{self, Bdd, Formula};
use crate::int::Int;
use crate::kernel::{Kernel, Query};
use crate::terms::{
    AtomTerm, Certificate, End, Instance, LinearTerm, Part, Proof, Row, Step, TermId, TheoryLemma,
};
use crate::typed::{IntType, StructId};
use std::collections::{BTreeMap, BTreeSet, HashMap};
use std::fmt::Write as _;

/// The first line of a text.
pub const HEADER: &str = "villanelle certificates 1";

/// The number of splits that may nest in a proof that is read. It is the
/// number that the search allows itself (`lia.rs`), and it bounds the depth
/// to which the kernel descends.
pub const NESTED_SPLITS: usize = 256;

// Part 1. Writing.

/// One entailment that was proved in a body, for [`write_body`].
pub struct Asked<'a> {
    pub control: &'a str,
    pub line: u32,
    pub clause: &'a str,
    /// The negated goal, in the diagram of the tables.
    pub goal: Formula,
    pub certificate: &'a Certificate,
}

fn quote(text: &str) -> String {
    let mut out = String::from("\"");
    for character in text.chars() {
        match character {
            '"' => out.push_str("\\\""),
            '\\' => out.push_str("\\\\"),
            '\n' => out.push_str("\\n"),
            '\r' => out.push_str("\\r"),
            '\t' => out.push_str("\\t"),
            other if other.is_control() => {
                let _ = write!(out, "\\u{{{:x}}}", other as u32);
            }
            other => out.push(other),
        }
    }
    out.push('"');
    out
}

fn form_text(constant: Option<&Int>, coeffs: &BTreeMap<TermId, Int>) -> String {
    let mut items = Vec::new();
    if let Some(constant) = constant
        && !constant.is_zero()
    {
        items.push(constant.to_string());
    }
    for (term, coeff) in coeffs {
        items.push(format!("{coeff}*u{term}"));
    }
    format!("{{{}}}", items.join(" "))
}

fn linear_text(term: &LinearTerm) -> String {
    form_text(Some(&term.constant), &term.coeffs)
}

fn list_text(terms: &[LinearTerm]) -> String {
    let items: Vec<String> = terms.iter().map(linear_text).collect();
    format!("[{}]", items.join(" "))
}

fn type_text(ty: Option<IntType>) -> &'static str {
    ty.map_or("none", IntType::name)
}

fn ranged_text(is_value_term: bool) -> &'static str {
    if is_value_term { "ranged" } else { "free" }
}

fn bound_text(bound: &Option<Int>) -> String {
    bound
        .as_ref()
        .map_or_else(|| "none".to_string(), Int::to_string)
}

fn term_text(term: &AtomTerm) -> String {
    match term {
        AtomTerm::Var {
            name,
            ty,
            is_value_term,
        } => format!(
            "var {} {} {}",
            quote(name),
            type_text(*ty),
            ranged_text(*is_value_term)
        ),
        AtomTerm::UsizeMax => "usize-max".to_string(),
        AtomTerm::DivConst(t, k) => format!("div-const {} {k}", linear_text(t)),
        AtomTerm::Div(s, t) => format!("div {} {}", linear_text(s), linear_text(t)),
        AtomTerm::Rem(s, t) => format!("rem {} {}", linear_text(s), linear_text(t)),
        AtomTerm::Mul {
            left,
            right,
            left_bounds,
            right_bounds,
        } => format!(
            "mul {} {} {} {} {} {}",
            linear_text(left),
            linear_text(right),
            bound_text(&left_bounds.0),
            bound_text(&left_bounds.1),
            bound_text(&right_bounds.0),
            bound_text(&right_bounds.1)
        ),
        AtomTerm::PureAlt(control, arguments) => {
            format!("pure-alt {control} {}", list_text(arguments))
        }
        AtomTerm::PurePay(control, alternative, field, arguments) => format!(
            "pure-pay {control} {alternative} {field} {}",
            list_text(arguments)
        ),
        AtomTerm::Len(t) => format!("len {}", linear_text(t)),
        AtomTerm::StrLit(text) => format!("str {}", quote(text)),
        AtomTerm::EmptyMap => "empty-map".to_string(),
        AtomTerm::VecLit(items) => format!("vec {}", list_text(items)),
        AtomTerm::StructCtor(structure, arguments) => {
            format!("struct {structure} {}", list_text(arguments))
        }
        AtomTerm::Field {
            base,
            struct_id,
            field_idx,
            int_ty,
            is_bool,
            is_value_term,
        } => format!(
            "field {} {struct_id} {field_idx} {} {} {}",
            linear_text(base),
            type_text(*int_ty),
            if *is_bool { "bool" } else { "other" },
            ranged_text(*is_value_term)
        ),
        AtomTerm::VariantCtor {
            variant_id,
            ctor_idx,
            fields,
            num_ctors,
        } => format!(
            "ctor {variant_id} {ctor_idx} {num_ctors} {}",
            list_text(fields)
        ),
        AtomTerm::VariantTag {
            base,
            variant_id,
            num_ctors,
        } => format!("tag {} {variant_id} {num_ctors}", linear_text(base)),
        AtomTerm::Index {
            base,
            index,
            int_ty,
            is_bool,
            is_value_term,
        } => format!(
            "index {} {} {} {} {}",
            linear_text(base),
            linear_text(index),
            type_text(*int_ty),
            if *is_bool { "bool" } else { "other" },
            ranged_text(*is_value_term)
        ),
        AtomTerm::Update { base, index, value } => format!(
            "update {} {} {}",
            linear_text(base),
            linear_text(index),
            linear_text(value)
        ),
        AtomTerm::Trim(t) => format!("trim {}", linear_text(t)),
    }
}

fn proof_text(out: &mut String, proof: &Proof, depth: usize) {
    let indent = " ".repeat(depth + 1);
    for step in &proof.steps {
        match step {
            Step::Literal(index) => {
                let _ = writeln!(out, "{indent}literal {index}");
            }
            Step::Combine(rows) => {
                let items: Vec<String> = rows
                    .iter()
                    .map(|(row, multiplier)| format!("{multiplier}*p{row}"))
                    .collect();
                let _ = writeln!(out, "{indent}combine {}", items.join(" "));
            }
            Step::Round { source, divisor } => {
                let _ = writeln!(out, "{indent}round p{source} {divisor}");
            }
        }
    }
    match &proof.end {
        End::Close(row) => {
            let _ = writeln!(out, "{indent}close p{row}");
        }
        End::Split {
            form,
            bound,
            low,
            high,
        } => {
            let _ = writeln!(out, "{indent}split {} <= {bound}", form_text(None, form));
            proof_text(out, low, depth + 1);
            proof_text(out, high, depth + 1);
        }
    }
}

/// Writes one body: the tables of `tables`, and the questions of `asked`
/// with their certificates. `history` names the history atoms. The goal of
/// `tables` is not read; each question has its own.
pub fn write_body(
    out: &mut String,
    tables: &Query,
    history: &[(String, String)],
    asked: &[Asked],
) -> Result<(), String> {
    if history.len() != tables.first_theory_var || tables.given.len() != tables.terms.len() {
        return Err("the tables do not agree with each other".to_string());
    }
    // The premises that the certificates name, and the nodes to write.
    let mut premises: Vec<Vec<Formula>> = Vec::new();
    let mut reached: BTreeSet<Formula> = BTreeSet::new();
    let mut open: Vec<Formula> = Vec::new();
    for question in asked {
        let mut named = Vec::new();
        for part in &question.certificate.parts {
            let premise = match part {
                Part::Structure(index) => tables.structure.get(*index),
                Part::Fact(index) => tables.facts.get(*index),
                Part::Instance(_) | Part::Lemma(_) => continue,
            };
            let Some(premise) = premise else {
                return Err("a certificate names a premise that the body does not have".to_string());
            };
            named.push(*premise);
            open.push(*premise);
        }
        premises.push(named);
        open.push(question.goal);
    }
    while let Some(formula) = open.pop() {
        if formula >= 2 && reached.insert(formula) {
            let node = tables.diagram.node(formula);
            open.push(node.low);
            open.push(node.high);
        }
    }

    out.push_str("body\n");
    for (position, (site, alternative)) in history.iter().enumerate() {
        let _ = writeln!(
            out,
            "history h{position} {} {}",
            quote(site),
            quote(alternative)
        );
    }
    for (position, term) in tables.terms.iter().enumerate() {
        let origin = if tables.given[position] {
            "written"
        } else {
            "added"
        };
        let _ = writeln!(out, "term u{position} {origin} {}", term_text(term));
    }
    for (position, row) in tables.atoms.iter().enumerate() {
        let _ = writeln!(
            out,
            "row a{position} {} <= {}",
            form_text(None, &row.coeffs),
            row.rhs
        );
    }
    for (structure, arity) in tables.arities {
        let _ = writeln!(out, "arity {structure} {arity}");
    }
    // A node has a greater number than the nodes below it, so that this is
    // an order in which every node comes after the two it names.
    for formula in &reached {
        let node = tables.diagram.node(*formula);
        let variable = if node.var < tables.first_theory_var {
            format!("h{}", node.var)
        } else {
            format!("a{}", node.var - tables.first_theory_var)
        };
        let _ = writeln!(
            out,
            "node n{formula} {variable} n{} n{}",
            node.low, node.high
        );
    }
    for (question, premises) in asked.iter().zip(premises) {
        let _ = writeln!(
            out,
            "question {} {} {}",
            quote(question.control),
            question.line,
            quote(question.clause)
        );
        let _ = writeln!(out, "goal n{}", question.goal);
        let mut premises = premises.into_iter();
        for part in &question.certificate.parts {
            match part {
                Part::Structure(_) => {
                    let premise = premises.next().expect("one premise for each part");
                    let _ = writeln!(out, "structure n{premise}");
                }
                Part::Fact(_) => {
                    let premise = premises.next().expect("one premise for each part");
                    let _ = writeln!(out, "fact n{premise}");
                }
                Part::Instance(instance) => {
                    let _ = writeln!(out, "instance {instance}");
                }
                Part::Lemma(lemma) => {
                    let literals: Vec<String> = lemma
                        .literals
                        .iter()
                        .map(|(atom, positive)| {
                            format!("{}a{atom}", if *positive { "" } else { "!" })
                        })
                        .collect();
                    let _ = writeln!(out, "lemma {}", literals.join(" "));
                    proof_text(out, &lemma.proof, 0);
                }
            }
        }
    }
    out.push_str("end\n");
    Ok(())
}

// Part 2. Reading.

/// One question of a text: a goal, the premises, and the certificate, whose
/// parts name the premises by their positions in the two lists here.
#[derive(Clone, Debug)]
pub struct Question {
    pub control: String,
    pub line: u32,
    pub clause: String,
    pub goal: Formula,
    pub structure: Vec<Formula>,
    pub facts: Vec<Formula>,
    pub certificate: Certificate,
}

/// One body of a text: its tables, in a diagram that the reader made, and
/// its questions.
#[derive(Clone, Debug, Default)]
pub struct Body {
    pub diagram: Bdd,
    pub history: Vec<(String, String)>,
    pub terms: Vec<AtomTerm>,
    pub given: Vec<bool>,
    pub arities: BTreeMap<StructId, usize>,
    pub atoms: Vec<Row>,
    pub questions: Vec<Question>,
}

impl Body {
    /// What the kernel is asked for a question of this body.
    pub fn query<'a>(&'a self, question: &'a Question) -> Query<'a> {
        Query {
            diagram: &self.diagram,
            first_theory_var: self.history.len(),
            terms: &self.terms,
            given: &self.given,
            arities: &self.arities,
            atoms: &self.atoms,
            structure: &question.structure,
            facts: &question.facts,
            goal: question.goal,
        }
    }

    /// Validates the certificate of every question, with one kernel that
    /// has seen nothing but this body.
    pub fn validate(&self) -> Result<(), String> {
        let mut kernel = Kernel::new();
        for question in &self.questions {
            kernel
                .validate(&self.query(question), &question.certificate)
                .map_err(|error| {
                    format!(
                        "{}:{} [{}]: {error}",
                        question.control, question.line, question.clause
                    )
                })?;
        }
        Ok(())
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
enum Token {
    /// A word, or one of the brackets `{`, `}`, `[` and `]`.
    Word(String),
    /// A string, without its quotes and with its escapes read.
    Text(String),
}

fn is_bracket(character: char) -> bool {
    matches!(character, '{' | '}' | '[' | ']')
}

fn tokens(line: &str) -> Result<Vec<Token>, String> {
    let mut out = Vec::new();
    let mut rest = line.chars().peekable();
    while let Some(&character) = rest.peek() {
        if character.is_whitespace() {
            rest.next();
        } else if is_bracket(character) {
            rest.next();
            out.push(Token::Word(character.to_string()));
        } else if character == '"' {
            rest.next();
            let mut text = String::new();
            loop {
                match rest.next() {
                    None => return Err("a string has no closing quote".to_string()),
                    Some('"') => break,
                    Some('\\') => match rest.next() {
                        Some('"') => text.push('"'),
                        Some('\\') => text.push('\\'),
                        Some('n') => text.push('\n'),
                        Some('r') => text.push('\r'),
                        Some('t') => text.push('\t'),
                        Some('u') => {
                            let mut digits = String::new();
                            if rest.next() != Some('{') {
                                return Err("`\\u` without `{`".to_string());
                            }
                            loop {
                                match rest.next() {
                                    Some('}') => break,
                                    Some(digit)
                                        if digit.is_ascii_hexdigit() && digits.len() < 6 =>
                                    {
                                        digits.push(digit);
                                    }
                                    _ => return Err("`\\u{…}` is not a character".to_string()),
                                }
                            }
                            let character = u32::from_str_radix(&digits, 16)
                                .ok()
                                .and_then(char::from_u32)
                                .ok_or("`\\u{…}` is not a character")?;
                            text.push(character);
                        }
                        _ => return Err("a string has an escape that is not one".to_string()),
                    },
                    Some(other) => text.push(other),
                }
            }
            out.push(Token::Text(text));
        } else {
            let mut word = String::new();
            while let Some(&character) = rest.peek() {
                if character.is_whitespace() || is_bracket(character) || character == '"' {
                    break;
                }
                word.push(character);
                rest.next();
            }
            out.push(Token::Word(word));
        }
    }
    Ok(out)
}

/// A number written with digits only.
fn digits(text: &str) -> Option<usize> {
    if text.is_empty() || !text.bytes().all(|byte| byte.is_ascii_digit()) {
        return None;
    }
    text.parse().ok()
}

/// The tokens of one line, read from the left.
struct Cursor<'a> {
    tokens: &'a [Token],
    at: usize,
    /// The greatest term that the line names.
    greatest: Option<TermId>,
}

impl<'a> Cursor<'a> {
    fn new(tokens: &'a [Token]) -> Cursor<'a> {
        Cursor {
            tokens,
            at: 0,
            greatest: None,
        }
    }

    fn word(&mut self) -> Result<&'a str, String> {
        match self.tokens.get(self.at) {
            Some(Token::Word(word)) => {
                self.at += 1;
                Ok(word)
            }
            Some(Token::Text(text)) => Err(format!("the string {text:?} is where a word belongs")),
            None => Err("the line ends too soon".to_string()),
        }
    }

    fn text(&mut self) -> Result<String, String> {
        match self.tokens.get(self.at) {
            Some(Token::Text(text)) => {
                self.at += 1;
                Ok(text.clone())
            }
            Some(Token::Word(word)) => Err(format!("`{word}` is where a string belongs")),
            None => Err("the line ends too soon".to_string()),
        }
    }

    fn expect(&mut self, expected: &str) -> Result<(), String> {
        let word = self.word()?;
        if word == expected {
            Ok(())
        } else {
            Err(format!("`{word}` is where `{expected}` belongs"))
        }
    }

    fn next_is(&self, expected: &str) -> bool {
        matches!(self.tokens.get(self.at), Some(Token::Word(word)) if word == expected)
    }

    fn end(&self) -> Result<(), String> {
        if self.at == self.tokens.len() {
            Ok(())
        } else {
            Err("the line goes on after its end".to_string())
        }
    }

    fn count(&mut self) -> Result<usize, String> {
        let word = self.word()?;
        digits(word).ok_or_else(|| format!("`{word}` is not a number"))
    }

    fn int(&mut self) -> Result<Int, String> {
        let word = self.word()?;
        Int::parse(word).ok_or_else(|| format!("`{word}` is not an integer"))
    }

    fn bound(&mut self) -> Result<Option<Int>, String> {
        if self.next_is("none") {
            self.at += 1;
            Ok(None)
        } else {
            self.int().map(Some)
        }
    }

    /// A number after a letter: `u7`, `a3`, `n12`, `h0`, `p4`.
    fn named(&mut self, letter: char) -> Result<usize, String> {
        let word = self.word()?;
        word.strip_prefix(letter)
            .and_then(digits)
            .ok_or_else(|| format!("`{word}` is where `{letter}` and a number belong"))
    }

    fn term(&mut self) -> Result<TermId, String> {
        let term = self.named('u')?;
        self.greatest = self.greatest.max(Some(term));
        Ok(term)
    }

    /// `{c k*u …}`: a constant, which is left out when it is zero and when
    /// `with_constant` is false, and the terms with their coefficients.
    fn form(&mut self, with_constant: bool) -> Result<LinearTerm, String> {
        self.expect("{")?;
        let mut constant = None;
        let mut coeffs = BTreeMap::new();
        loop {
            let word = self.word()?;
            if word == "}" {
                break;
            }
            if let Some((coeff, term)) = word.split_once('*') {
                let coeff =
                    Int::parse(coeff).ok_or_else(|| format!("`{coeff}` is not an integer"))?;
                let term = term
                    .strip_prefix('u')
                    .and_then(digits)
                    .ok_or_else(|| format!("`{term}` is not a term"))?;
                self.greatest = self.greatest.max(Some(term));
                if coeffs.insert(term, coeff).is_some() {
                    return Err(format!("u{term} is there twice"));
                }
            } else if with_constant && constant.is_none() && coeffs.is_empty() {
                constant =
                    Some(Int::parse(word).ok_or_else(|| format!("`{word}` is not an integer"))?);
            } else {
                return Err(format!("`{word}` is where a coefficient and a term belong"));
            }
        }
        Ok(LinearTerm {
            constant: constant.unwrap_or_default(),
            coeffs,
        })
    }

    fn linear(&mut self) -> Result<LinearTerm, String> {
        self.form(true)
    }

    fn linears(&mut self) -> Result<Vec<LinearTerm>, String> {
        self.expect("[")?;
        let mut out = Vec::new();
        while !self.next_is("]") {
            out.push(self.linear()?);
        }
        self.at += 1;
        Ok(out)
    }

    fn terms(&mut self) -> Result<Vec<TermId>, String> {
        self.expect("[")?;
        let mut out = Vec::new();
        while !self.next_is("]") {
            out.push(self.term()?);
        }
        self.at += 1;
        Ok(out)
    }

    fn int_type(&mut self) -> Result<Option<IntType>, String> {
        let word = self.word()?;
        if word == "none" {
            return Ok(None);
        }
        IntType::from_name(word)
            .map(Some)
            .ok_or_else(|| format!("`{word}` is not an integer type"))
    }

    fn one_of(&mut self, yes: &str, no: &str) -> Result<bool, String> {
        let word = self.word()?;
        if word == yes {
            Ok(true)
        } else if word == no {
            Ok(false)
        } else {
            Err(format!("`{word}` is where `{yes}` or `{no}` belongs"))
        }
    }

    fn atom_term(&mut self) -> Result<AtomTerm, String> {
        let form = self.word()?;
        Ok(match form {
            "var" => AtomTerm::Var {
                name: self.text()?,
                ty: self.int_type()?,
                is_value_term: self.one_of("ranged", "free")?,
            },
            "usize-max" => AtomTerm::UsizeMax,
            "div-const" => AtomTerm::DivConst(self.linear()?, self.int()?),
            "div" => AtomTerm::Div(self.linear()?, self.linear()?),
            "rem" => AtomTerm::Rem(self.linear()?, self.linear()?),
            "mul" => AtomTerm::Mul {
                left: self.linear()?,
                right: self.linear()?,
                left_bounds: (self.bound()?, self.bound()?),
                right_bounds: (self.bound()?, self.bound()?),
            },
            "pure-alt" => AtomTerm::PureAlt(self.count()?, self.linears()?),
            "pure-pay" => {
                AtomTerm::PurePay(self.count()?, self.count()?, self.count()?, self.linears()?)
            }
            "len" => AtomTerm::Len(self.linear()?),
            "str" => AtomTerm::StrLit(self.text()?),
            "empty-map" => AtomTerm::EmptyMap,
            "vec" => AtomTerm::VecLit(self.linears()?),
            "struct" => AtomTerm::StructCtor(self.count()?, self.linears()?),
            "field" => AtomTerm::Field {
                base: self.linear()?,
                struct_id: self.count()?,
                field_idx: self.count()?,
                int_ty: self.int_type()?,
                is_bool: self.one_of("bool", "other")?,
                is_value_term: self.one_of("ranged", "free")?,
            },
            "ctor" => {
                let variant_id = self.count()?;
                let ctor_idx = self.count()?;
                let num_ctors = self.count()?;
                AtomTerm::VariantCtor {
                    variant_id,
                    ctor_idx,
                    fields: self.linears()?,
                    num_ctors,
                }
            }
            "tag" => AtomTerm::VariantTag {
                base: self.linear()?,
                variant_id: self.count()?,
                num_ctors: self.count()?,
            },
            "index" => AtomTerm::Index {
                base: self.linear()?,
                index: self.linear()?,
                int_ty: self.int_type()?,
                is_bool: self.one_of("bool", "other")?,
                is_value_term: self.one_of("ranged", "free")?,
            },
            "update" => AtomTerm::Update {
                base: self.linear()?,
                index: self.linear()?,
                value: self.linear()?,
            },
            "trim" => AtomTerm::Trim(self.linear()?),
            other => return Err(format!("`{other}` is not a form of term")),
        })
    }

    fn instance(&mut self) -> Result<Instance, String> {
        let kind = self.word()?;
        Ok(match kind {
            "term" => Instance::Term(self.term()?),
            "pair" => Instance::Pair(self.term()?, self.term()?),
            "frame" => Instance::Frame {
                update: self.term()?,
                element: self.term()?,
                original: self.term()?,
            },
            "extension" => Instance::Extension {
                structure: self.count()?,
                left: self.term()?,
                left_fields: self.terms()?,
                right: self.term()?,
                right_fields: self.terms()?,
            },
            other => return Err(format!("`{other}` is not a kind of instance")),
        })
    }
}

/// The lines of a text that say something, each with its number.
struct Reader<'a> {
    lines: &'a [(usize, Vec<Token>)],
    at: usize,
}

fn on_line<T>(number: usize, result: Result<T, String>) -> Result<T, String> {
    result.map_err(|error| format!("line {number}: {error}"))
}

/// The place of each kind of line in a body. The tables come in this order,
/// and the questions after them.
fn rank(keyword: &str) -> Option<usize> {
    ["history", "term", "row", "arity", "node", "question"]
        .iter()
        .position(|kind| *kind == keyword)
}

impl<'a> Reader<'a> {
    /// The keyword of the next line, when there is one and it is a word.
    fn keyword(&self) -> Option<&'a str> {
        match self.lines.get(self.at)?.1.first()? {
            Token::Word(word) => Some(word),
            Token::Text(_) => None,
        }
    }

    /// The next line: its number, and its tokens after the keyword.
    fn line(&mut self) -> Option<(usize, Cursor<'a>)> {
        let (number, tokens) = self.lines.get(self.at)?;
        self.at += 1;
        let mut cursor = Cursor::new(tokens);
        cursor.at = 1;
        Some((*number, cursor))
    }

    fn body(&mut self) -> Result<Body, String> {
        let mut body = Body::default();
        let mut nodes: HashMap<usize, Formula> = HashMap::from([(0, bdd::FALSE), (1, bdd::TRUE)]);
        let mut greatest: Option<TermId> = None;
        let mut stage = 0;
        let mut closed = false;
        while let Some(keyword) = self.keyword() {
            let (number, mut line) = self.line().expect("a line with a keyword");
            if keyword == "end" {
                on_line(number, line.end())?;
                closed = true;
                break;
            }
            let Some(rank) = rank(keyword) else {
                return Err(format!(
                    "line {number}: `{keyword}` is not a line of a body"
                ));
            };
            if rank < stage {
                return Err(format!(
                    "line {number}: a `{keyword}` line comes before the lines after it"
                ));
            }
            stage = rank;
            let read = match keyword {
                "history" => self.history(&mut body, &mut line),
                "term" => self.term(&mut body, &mut line),
                "row" => self.row(&mut body, &mut line),
                "arity" => self.arity(&mut body, &mut line),
                "node" => self.node(&mut body, &mut nodes, &mut line),
                _ => {
                    let question = self.question(&nodes, number, &mut line)?;
                    body.questions.push(question);
                    continue;
                }
            };
            on_line(number, read.and_then(|()| line.end()))?;
            greatest = greatest.max(line.greatest);
        }
        if !closed {
            return Err(match self.lines.get(self.at) {
                Some((number, _)) => format!("line {number}: the line has no keyword"),
                None => "the text ends inside a body".to_string(),
            });
        }
        if let Some(term) = greatest
            && term >= body.terms.len()
        {
            return Err(format!(
                "the tables name the term u{term}, which is not there"
            ));
        }
        Ok(body)
    }

    fn history(&self, body: &mut Body, line: &mut Cursor) -> Result<(), String> {
        if line.named('h')? != body.history.len() {
            return Err("the history atoms are not in their order".to_string());
        }
        body.history.push((line.text()?, line.text()?));
        Ok(())
    }

    fn term(&self, body: &mut Body, line: &mut Cursor) -> Result<(), String> {
        if line.named('u')? != body.terms.len() {
            return Err("the terms are not in their order".to_string());
        }
        body.given.push(line.one_of("written", "added")?);
        body.terms.push(line.atom_term()?);
        Ok(())
    }

    fn row(&self, body: &mut Body, line: &mut Cursor) -> Result<(), String> {
        if line.named('a')? != body.atoms.len() {
            return Err("the rows are not in their order".to_string());
        }
        let form = line.form(false)?;
        line.expect("<=")?;
        body.atoms.push(Row {
            coeffs: form.coeffs,
            rhs: line.int()?,
        });
        Ok(())
    }

    fn arity(&self, body: &mut Body, line: &mut Cursor) -> Result<(), String> {
        let structure = line.count()?;
        if body.arities.insert(structure, line.count()?).is_some() {
            return Err(format!("struct {structure} is there twice"));
        }
        Ok(())
    }

    /// `node n v l h` is the formula "if `v` then `h`, else `l`".
    fn node(
        &self,
        body: &mut Body,
        nodes: &mut HashMap<usize, Formula>,
        line: &mut Cursor,
    ) -> Result<(), String> {
        let name = line.named('n')?;
        let word = line.word()?;
        let variable = if let Some(atom) = word.strip_prefix('h').and_then(digits) {
            (atom < body.history.len()).then_some(atom)
        } else if let Some(row) = word.strip_prefix('a').and_then(digits) {
            (row < body.atoms.len()).then(|| body.history.len() + row)
        } else {
            None
        };
        let Some(variable) = variable else {
            return Err(format!("`{word}` is not a history atom or a row"));
        };
        let low = known(nodes, line.named('n')?)?;
        let high = known(nodes, line.named('n')?)?;
        let test = body.diagram.variable(variable);
        let when = body.diagram.and(test, high);
        let unless = body.diagram.minus(low, test);
        let formula = body.diagram.or(when, unless);
        if nodes.insert(name, formula).is_some() {
            return Err(format!("the node n{name} is there twice"));
        }
        Ok(())
    }

    fn question(
        &mut self,
        nodes: &HashMap<usize, Formula>,
        number: usize,
        line: &mut Cursor,
    ) -> Result<Question, String> {
        let head = (|| {
            let control = line.text()?;
            let at = line.count()?;
            let at = u32::try_from(at).map_err(|_| format!("`{at}` is not a line"))?;
            let clause = line.text()?;
            line.end()?;
            Ok((control, at, clause))
        })();
        let (control, at, clause) = on_line(number, head)?;
        let goal = match self.keyword() {
            Some("goal") => {
                let (number, mut line) = self.line().expect("a line with a keyword");
                let goal = line
                    .named('n')
                    .and_then(|node| known(nodes, node))
                    .and_then(|goal| line.end().map(|()| goal));
                on_line(number, goal)?
            }
            _ => return Err(format!("line {number}: the question has no goal")),
        };
        let mut question = Question {
            control,
            line: at,
            clause,
            goal,
            structure: Vec::new(),
            facts: Vec::new(),
            certificate: Certificate::default(),
        };
        while let Some(keyword) = self.keyword() {
            if !matches!(keyword, "structure" | "fact" | "instance" | "lemma") {
                break;
            }
            let (number, mut line) = self.line().expect("a line with a keyword");
            let part = match keyword {
                "structure" => line.named('n').and_then(|node| {
                    question.structure.push(known(nodes, node)?);
                    Ok(Part::Structure(question.structure.len() - 1))
                }),
                "fact" => line.named('n').and_then(|node| {
                    question.facts.push(known(nodes, node)?);
                    Ok(Part::Fact(question.facts.len() - 1))
                }),
                "instance" => line.instance().map(Part::Instance),
                _ => {
                    let literals = on_line(number, literals(&mut line))?;
                    let proof = self.proof(number)?;
                    question
                        .certificate
                        .parts
                        .push(Part::Lemma(TheoryLemma { literals, proof }));
                    continue;
                }
            };
            let part = on_line(number, part.and_then(|part| line.end().map(|()| part)))?;
            question.certificate.parts.push(part);
        }
        Ok(question)
    }

    /// A proof: its steps, each on a line, and its end. After a split come
    /// the proof of the low branch and then that of the high branch. The
    /// splits whose branches are being read are kept in a list, so that a
    /// proof of any depth is read in the same space of the stack.
    fn proof(&mut self, after: usize) -> Result<Proof, String> {
        /// A split, the steps before it, and its low branch once that is
        /// read.
        struct Open {
            steps: Vec<Step>,
            form: BTreeMap<TermId, Int>,
            bound: Int,
            low: Option<Proof>,
        }
        let mut open: Vec<Open> = Vec::new();
        let mut steps = Vec::new();
        loop {
            let keyword = self.keyword().filter(|keyword| {
                matches!(
                    *keyword,
                    "literal" | "combine" | "round" | "close" | "split"
                )
            });
            let Some(keyword) = keyword else {
                return Err(format!(
                    "the proof that begins after line {after} has no end"
                ));
            };
            let (number, mut line) = self.line().expect("a line with a keyword");
            match on_line(number, proof_line(keyword, &mut line))? {
                ProofLine::Step(step) => steps.push(step),
                ProofLine::Split(form, bound) => {
                    if open.len() == NESTED_SPLITS {
                        return Err(format!(
                            "line {number}: more than {NESTED_SPLITS} splits nest"
                        ));
                    }
                    open.push(Open {
                        steps: std::mem::take(&mut steps),
                        form,
                        bound,
                        low: None,
                    });
                }
                ProofLine::Close(row) => {
                    // A branch is whole. It is the low branch of the split
                    // above it, or the high one, and then that split is
                    // whole too.
                    let mut whole = Proof {
                        steps: std::mem::take(&mut steps),
                        end: End::Close(row),
                    };
                    loop {
                        let Some(mut split) = open.pop() else {
                            return Ok(whole);
                        };
                        let Some(low) = split.low.take() else {
                            split.low = Some(whole);
                            open.push(split);
                            break;
                        };
                        whole = Proof {
                            steps: split.steps,
                            end: End::Split {
                                form: split.form,
                                bound: split.bound,
                                low: Box::new(low),
                                high: Box::new(whole),
                            },
                        };
                    }
                }
            }
        }
    }
}

/// What one line of a proof says.
enum ProofLine {
    Step(Step),
    Split(BTreeMap<TermId, Int>, Int),
    Close(usize),
}

fn proof_line(keyword: &str, line: &mut Cursor) -> Result<ProofLine, String> {
    let said = match keyword {
        "literal" => ProofLine::Step(Step::Literal(line.count()?)),
        "combine" => {
            let mut rows = Vec::new();
            while line.at < line.tokens.len() {
                let word = line.word()?;
                let item = word.split_once('*').and_then(|(multiplier, row)| {
                    Some((
                        row.strip_prefix('p').and_then(digits)?,
                        Int::parse(multiplier)?,
                    ))
                });
                rows.push(
                    item.ok_or_else(|| format!("`{word}` is where a multiplier and a row belong"))?,
                );
            }
            ProofLine::Step(Step::Combine(rows))
        }
        "round" => ProofLine::Step(Step::Round {
            source: line.named('p')?,
            divisor: line.int()?,
        }),
        "split" => {
            let form = line.form(false)?;
            line.expect("<=")?;
            ProofLine::Split(form.coeffs, line.int()?)
        }
        _ => ProofLine::Close(line.named('p')?),
    };
    line.end()?;
    Ok(said)
}

fn known(nodes: &HashMap<usize, Formula>, node: usize) -> Result<Formula, String> {
    nodes
        .get(&node)
        .copied()
        .ok_or_else(|| format!("the node n{node} is named before it is there"))
}

/// The literals of a lemma: `a3` for the row, `!a3` for its negation.
fn literals(line: &mut Cursor) -> Result<Vec<(usize, bool)>, String> {
    let mut out = Vec::new();
    while line.at < line.tokens.len() {
        let word = line.word()?;
        let (positive, atom) = match word.strip_prefix('!') {
            Some(atom) => (false, atom),
            None => (true, word),
        };
        let atom = atom
            .strip_prefix('a')
            .and_then(digits)
            .ok_or_else(|| format!("`{word}` is not a literal"))?;
        out.push((atom, positive));
    }
    Ok(out)
}

/// Reads a text: the header, and then every body. A line that begins with
/// `#` says nothing, and neither does an empty one.
pub fn read(text: &str) -> Result<Vec<Body>, String> {
    let mut lines = Vec::new();
    for (position, line) in text.lines().enumerate() {
        let line = line.trim();
        if line.is_empty() || line.starts_with('#') {
            continue;
        }
        lines.push((position + 1, on_line(position + 1, tokens(line))?));
    }
    let header: Vec<Token> = HEADER
        .split(' ')
        .map(|word| Token::Word(word.to_string()))
        .collect();
    if lines.first().map(|(_, tokens)| tokens) != Some(&header) {
        return Err(format!("the text does not begin with `{HEADER}`"));
    }
    let mut reader = Reader {
        lines: &lines,
        at: 1,
    };
    let mut bodies = Vec::new();
    while let Some((number, tokens)) = lines.get(reader.at) {
        if tokens.as_slice() != [Token::Word("body".to_string())] {
            return Err(format!("line {number}: a body begins with `body`"));
        }
        reader.at += 1;
        bodies.push(reader.body()?);
    }
    Ok(bodies)
}

/// Reads a text and validates every certificate in it. Returns the number
/// of certificates.
pub fn validate(text: &str) -> Result<usize, String> {
    let mut validated = 0;
    for body in read(text)? {
        body.validate()?;
        validated += body.questions.len();
    }
    Ok(validated)
}
