//! The text of certificates (`docs/v2/facts.md`, [V5]; the format is in
//! `docs/v2/oracle.md`).
//!
//! [V5] asks that a second checker can read a certificate. The reader of
//! `certificate` is that second way in: it makes the tables, the goals and
//! the premises from the text alone and gives them to a kernel. These tests
//! hold the text against the check that wrote it, give the reader texts that
//! were changed after they were written, and give it one that no checker
//! wrote.

use std::collections::HashMap;
use villanelle_v2::bdd::{self, Bdd, Formula};
use villanelle_v2::certificate::{self, Body};
use villanelle_v2::check::{self, CheckedProgram};
use villanelle_v2::facts::Solver;
use villanelle_v2::terms::{AtomTerm, Part};
use villanelle_v2::{fuzz, load, load_surface};

/// Copies a formula of `from` into `into`. Two formulas over the same
/// variables are equivalent exactly when their copies in one diagram are one
/// node.
fn copy(
    into: &mut Bdd,
    seen: &mut HashMap<Formula, Formula>,
    from: &Bdd,
    formula: Formula,
) -> Formula {
    if formula < 2 {
        return formula;
    }
    if let Some(copied) = seen.get(&formula) {
        return *copied;
    }
    let node = from.node(formula);
    let low = copy(into, seen, from, node.low);
    let high = copy(into, seen, from, node.high);
    let test = into.variable(node.var);
    let when = into.and(test, high);
    let unless = into.minus(low, test);
    let copied = into.or(when, unless);
    seen.insert(formula, copied);
    copied
}

/// That the bodies read from a text state what the check proved: the same
/// tables, and for every question the same goal, the same premises and the
/// same certificate.
fn agrees(name: &str, report: &CheckedProgram, bodies: &[Body]) {
    let mut read = bodies.iter();
    for (position, solver) in report.bodies.iter().enumerate() {
        let proved: Vec<_> = report
            .certificates
            .iter()
            .filter(|proved| proved.body == position)
            .collect();
        if proved.is_empty() {
            continue;
        }
        let body = read
            .next()
            .unwrap_or_else(|| panic!("{name}: the text has no body {position}"));
        assert_eq!(body.history, solver.history_names, "{name}: history atoms");
        assert_eq!(body.terms, solver.terms, "{name}: terms");
        assert_eq!(body.given, solver.given, "{name}: who wrote each term");
        assert_eq!(body.atoms, solver.theory_atoms, "{name}: rows");
        assert_eq!(body.arities, solver.struct_arities, "{name}: fields");
        assert_eq!(body.questions.len(), proved.len(), "{name}: questions");

        let mut both = Bdd::new();
        let mut of_check = HashMap::new();
        let mut of_text = HashMap::new();
        for (question, proved) in body.questions.iter().zip(proved) {
            let place = format!("{name}: {}:{}", proved.control, proved.line);
            assert_eq!(question.control, proved.control, "{place}");
            assert_eq!(question.line, proved.line, "{place}");
            assert_eq!(question.clause, proved.clause, "{place}");
            let mut same = |checked: Formula, stated: Formula, what: &str| {
                assert_eq!(
                    copy(&mut both, &mut of_check, &solver.bdd, checked),
                    copy(&mut both, &mut of_text, &body.diagram, stated),
                    "{place}: {what}"
                );
            };
            same(proved.goal, question.goal, "the goal");
            assert_eq!(
                question.certificate.parts.len(),
                proved.certificate.parts.len(),
                "{place}: parts"
            );
            for (stated, checked) in question
                .certificate
                .parts
                .iter()
                .zip(&proved.certificate.parts)
            {
                match (stated, checked) {
                    (Part::Structure(stated), Part::Structure(checked)) => same(
                        solver.structure[*checked],
                        question.structure[*stated],
                        "a formula of the structure",
                    ),
                    (Part::Fact(stated), Part::Fact(checked)) => {
                        same(solver.facts[*checked], question.facts[*stated], "a fact");
                    }
                    (stated, checked) => assert_eq!(stated, checked, "{place}: a part"),
                }
            }
        }
    }
    assert!(
        read.next().is_none(),
        "{name}: the text has a body too many"
    );
}

/// Writes the certificates of a check, reads them back and validates them
/// from the text alone. Returns the number of certificates.
fn round_trip(name: &str, report: &CheckedProgram) -> usize {
    let text = report
        .certificate_text()
        .unwrap_or_else(|error| panic!("{name}: {error}"));
    let bodies = certificate::read(&text).unwrap_or_else(|error| panic!("{name}: {error}"));
    agrees(name, report, &bodies);
    for body in &bodies {
        body.validate()
            .unwrap_or_else(|error| panic!("{name}: {error}"));
    }
    let validated = certificate::validate(&text).unwrap_or_else(|error| panic!("{name}: {error}"));
    assert_eq!(validated, report.certificates.len(), "{name}");
    validated
}

#[test]
fn the_text_of_the_surface_programs_reads_back_and_validates() {
    let mut programs = 0;
    let mut certificates = 0;
    for directory in ["slice1_surface", "slice2_surface", "slice3_surface"] {
        let directory = format!("{}/tests/{directory}", env!("CARGO_MANIFEST_DIR"));
        let mut paths: Vec<_> = std::fs::read_dir(&directory)
            .unwrap_or_else(|error| panic!("{directory}: {error}"))
            .map(|entry| entry.expect("a directory entry").path())
            .filter(|path| {
                path.extension()
                    .is_some_and(|extension| extension == "rails")
            })
            .collect();
        paths.sort();
        for path in paths {
            let name = path.display().to_string();
            let source = std::fs::read_to_string(&path).expect("a readable program");
            let program = load_surface(&source).unwrap_or_else(|error| panic!("{name}: {error}"));
            let report = check::check(&program).unwrap_or_else(|error| panic!("{name}: {error}"));
            programs += 1;
            certificates += round_trip(&name, &report);
        }
    }
    assert!(programs >= 10, "{programs} programs");
    assert!(certificates >= 400, "{certificates} certificates");
}

#[test]
fn the_text_of_generated_programs_reads_back_and_validates() {
    let mut certificates = 0;
    let mut lemmas = 0;
    for seed in 1..=12 {
        let name = format!("seed {seed}");
        let source = fuzz::program_of(seed).print();
        let program = load(&source).unwrap_or_else(|error| panic!("{name}: {error}"));
        let report = check::check(&program).unwrap_or_else(|error| panic!("{name}: {error}"));
        certificates += round_trip(&name, &report);
        lemmas += report
            .certificates
            .iter()
            .map(|proved| proved.certificate.lemmas().count())
            .sum::<usize>();
    }
    assert!(certificates >= 100, "{certificates} certificates");
    assert!(lemmas >= 10, "{lemmas} lemmas");
}

/// A text that no checker wrote. It states: for `x` of type `u8`, there is
/// no value with `x > 300`. The range of `x` is an instance of [A1], and
/// the lemma says that `x ≤ 255` and `x ≥ 301` do not hold together.
fn by_hand(goal_bound: &str) -> String {
    format!(
        "villanelle certificates 1
# One body, with one name and three rows.
body
term u0 written usize-max
term u1 written var \"x\" u8 ranged
row a0 {{1*u1}} <= -1
row a1 {{1*u1}} <= 255
row a2 {{1*u1}} <= {goal_bound}

# The negated goal: the row a2 does not hold.
node n2 a2 n1 n0
question \"by hand\" 1 \"N2\"
goal n2
instance term u1
lemma a1 !a2
 literal 0
 literal 1
 combine 1*p0 1*p1
 close p2
end
"
    )
}

#[test]
fn a_text_written_by_hand_validates() {
    assert_eq!(certificate::validate(&by_hand("300")), Ok(1));
    // `x ≤ 255` holds for every `x` of the type, and the same proof gives it.
    assert_eq!(certificate::validate(&by_hand("255")), Ok(1));

    // `x ≤ 200` does not: the two rows of the lemma have a value in common.
    let error = certificate::validate(&by_hand("200")).expect_err("x can be 201");
    assert!(error.contains("by hand:1 [N2]"), "{error}");

    // Without the lemma, the range of `x` and the goal are two rows that
    // nothing connects.
    let text = by_hand("300");
    let lemma = text.find("lemma").expect("the lemma");
    let without = format!("{}end\n", &text[..lemma]);
    let error = certificate::validate(&without).expect_err("no lemma");
    assert!(error.contains("leave a case open"), "{error}");

    // The range is granted because the checker wrote `x`.
    let added = text.replace("term u1 written", "term u1 added");
    let error = certificate::validate(&added).expect_err("a term that was added");
    assert!(error.contains("did not write the term u1"), "{error}");

    // A name without a range has none.
    let free = text.replace("u8 ranged", "u8 free");
    let error = certificate::validate(&free).expect_err("a free name");
    assert!(error.contains("says nothing of the term u1"), "{error}");
}

/// The lines of the question that has an instance and a lemma: the first
/// and the line after the last.
fn question_with_instance_and_lemma(lines: &[&str]) -> (usize, usize) {
    let starts: Vec<usize> = (0..lines.len())
        .filter(|line| lines[*line].starts_with("question ") || lines[*line] == "end")
        .collect();
    starts
        .windows(2)
        .map(|pair| (pair[0], pair[1]))
        .find(|(first, after)| {
            let has = |keyword: &str| {
                lines[*first..*after]
                    .iter()
                    .any(|line| line.starts_with(keyword))
            };
            has("instance term ") && has("lemma ") && has("fact ")
        })
        .expect("a question with an instance, a fact and a lemma")
}

#[test]
fn a_text_that_was_changed_is_refused() {
    let program = load(
        "
        extern control checked_sub(a : u32, b : u32)
            ■ { difference {value : u32} ⇐ value = a - b │ underflow ⇐ a < b }

        pub control spend(total : u32, used : u32) ■ { left {value : u32} │ over } :=
            ⊤ ▷ t : ? used > total
            t.true ▷ ■ over
            t.false ▷ d : Δ checked_sub(total, used) ▸ difference {value} │ underflow
            t.false ∧ d.underflow ▷ ⊥
            t.false ∧ d.difference ▷ ⊢ value ≤ total
            t.false ∧ d.difference ▷ ■ left {value}
        ",
    )
    .expect("a program");
    let report = check::check(&program).expect("an accepted program");
    let text = report.certificate_text().expect("a text");
    assert_eq!(
        certificate::validate(&text),
        Ok(report.certificates.len()),
        "the text as it was written"
    );
    let lines: Vec<&str> = text.lines().collect();
    let (first, after) = question_with_instance_and_lemma(&lines);
    let changed = |change: &dyn Fn(usize, &str) -> Option<String>| {
        let mut out = String::new();
        for (position, line) in lines.iter().enumerate() {
            if let Some(line) = change(position, line) {
                out.push_str(&line);
                out.push('\n');
            }
        }
        assert_ne!(out, text, "the change changes nothing");
        certificate::validate(&out).expect_err("a text that was changed")
    };
    let inside = |position: usize| (first..after).contains(&position);
    let keep = |line: &str| Some(line.to_string());

    // The question without its facts.
    let error = changed(&|position, line| {
        if inside(position) && line.starts_with("fact ") {
            None
        } else {
            keep(line)
        }
    });
    assert!(error.contains("leave a case open"), "{error}");

    // Another goal: "true" in the place of the negated goal.
    let error = changed(&|position, line| {
        if inside(position) && line.starts_with("goal ") {
            Some("goal n1".to_string())
        } else {
            keep(line)
        }
    });
    assert!(error.contains("leave a case open"), "{error}");

    // The greatest value of the type of a name, raised by one. The instance
    // of [A1] for the name has a row that is no longer in the table.
    let instance = lines[first..after]
        .iter()
        .find_map(|line| line.strip_prefix("instance term "))
        .expect("an instance of a term");
    let greatest = format!("{{1*{instance}}} <= 4294967295");
    assert!(
        lines
            .iter()
            .any(|line| line.starts_with("row ") && line.ends_with(&greatest)),
        "the row of the greatest value of {instance}"
    );
    let error = changed(&|_, line| {
        if line.starts_with("row ") && line.ends_with(&greatest) {
            Some(line.replace("4294967295", "4294967296"))
        } else {
            keep(line)
        }
    });
    assert!(
        error.contains("a row that the query does not have"),
        "{error}"
    );

    // The same name, as a term that the search added.
    let written = format!("term {instance} written ");
    let error =
        changed(&|_, line| Some(line.replace(&written, &format!("term {instance} added "))));
    assert!(error.contains("did not write the term"), "{error}");

    // An instance that is none.
    let error = changed(&|position, line| {
        if inside(position) && line.starts_with("instance term ") {
            Some(format!("instance pair {instance} {instance}"))
        } else {
            keep(line)
        }
    });
    assert!(error.contains("says nothing of the terms"), "{error}");

    // A proof that closes with a row that is no contradiction.
    let error = changed(&|position, line| {
        if inside(position) && line.trim_start().starts_with("close ") {
            Some(" close p0".to_string())
        } else {
            keep(line)
        }
    });
    assert!(error.contains("part "), "{error}");

    // A proof without its end.
    let error = changed(&|position, line| {
        if inside(position) && line.trim_start().starts_with("close ") {
            None
        } else {
            keep(line)
        }
    });
    assert!(error.contains("has no end"), "{error}");

    // A lemma with every literal negated. The proof may refute those too
    // (`x ≤ 5` and `x ≥ 6` are each the negation of the other), and then it
    // is another lemma, which does not close the question.
    let error = changed(&|position, line| {
        if inside(position) && line.starts_with("lemma ") {
            let literals: Vec<&str> = line.split(' ').skip(1).collect();
            let flipped: Vec<String> = literals
                .iter()
                .map(|literal| match literal.strip_prefix('!') {
                    Some(atom) => atom.to_string(),
                    None => format!("!{literal}"),
                })
                .collect();
            Some(format!("lemma {}", flipped.join(" ")))
        } else {
            keep(line)
        }
    });
    assert!(
        error.contains("part ") || error.contains("leave a case open"),
        "{error}"
    );
}

#[test]
fn the_reader_refuses_what_is_not_a_text() {
    let body = |lines: &str| format!("villanelle certificates 1\nbody\n{lines}\nend\n");
    let deep = format!(
        "term u0 written usize-max\nrow a0 {{1*u0}} <= 0\nquestion \"c\" 1 \"N1\"\ngoal n0\nlemma a0\n{}",
        " split {1*u0} <= 0\n".repeat(certificate::NESTED_SPLITS + 1)
    );
    let cases: Vec<(String, &str)> = vec![
        (String::new(), "does not begin with"),
        (
            "villanelle certificates 2\n".to_string(),
            "does not begin with",
        ),
        (
            "villanelle certificates 1\nterm u0 written usize-max\n".to_string(),
            "a body begins with `body`",
        ),
        (
            "villanelle certificates 1\nbody\nterm u0 written usize-max\n".to_string(),
            "the text ends inside a body",
        ),
        (body("term u1 written usize-max"), "not in their order"),
        (body("term u0 given usize-max"), "`written` or `added`"),
        (body("term u0 written sum {} {}"), "not a form of term"),
        (body("term u0 written usize-max {}"), "goes on after"),
        (body("term u0 written var \"x u8 ranged"), "closing quote"),
        (body("term u0 written var x u8 ranged"), "a string belongs"),
        (body("term u0 written var \"x\" u7 ranged"), "integer type"),
        (body("term u0 written len {1*u3}"), "the term u3"),
        (
            body("term u0 written len {1*u0 2}"),
            "a coefficient and a term",
        ),
        (body("term u0 written len {1*u0 1*u0}"), "u0 is there twice"),
        (body("term u0 written len {1*u0"), "ends too soon"),
        (
            body("term u0 written usize-max\nrow a0 {5 1*u0} <= 1"),
            "a coefficient and a term",
        ),
        (
            body("term u0 written usize-max\nrow a0 {1*u0} < 1"),
            "`<=` belongs",
        ),
        (
            body("term u0 written usize-max\nrow a0 {1*u0} <= x"),
            "not an integer",
        ),
        (
            body("row a0 {} <= 1\nterm u0 written usize-max"),
            "comes before",
        ),
        (body("arity 1 2\narity 1 3"), "struct 1 is there twice"),
        (body("node n2 a0 n0 n1"), "not a history atom or a row"),
        (body("node n2 h0 n0 n1"), "not a history atom or a row"),
        (
            body("history h0 \"s\" \"a\"\nnode n2 h0 n0 n3"),
            "the node n3 is named before",
        ),
        (
            body("history h0 \"s\" \"a\"\nnode n1 h0 n0 n1"),
            "the node n1 is there twice",
        ),
        (body("question \"c\" 1 \"N1\""), "has no goal"),
        (body("question \"c\" 1 \"N1\"\ngoal n2"), "the node n2"),
        (
            body("question \"c\" 1 \"N1\"\ngoal n0\ngoal n0"),
            "not a line of a body",
        ),
        (
            body("question \"c\" 1 \"N1\"\ngoal n0\ninstance sum u0"),
            "not a kind of instance",
        ),
        (
            body("question \"c\" 1 \"N1\"\ngoal n0\nlemma b0\n close p0"),
            "not a literal",
        ),
        (
            body("question \"c\" 1 \"N1\"\ngoal n0\nlemma\n combine 1*0\n close p0"),
            "a multiplier and a row",
        ),
        (
            body("question \"c\" 1 \"N1\"\ngoal n0\nlemma\n split {} <= 0\n close p0"),
            "has no end",
        ),
        (body(&deep), "more than 256 splits nest"),
        (body("\"a string\""), "has no keyword"),
        (body("theorem 1"), "not a line of a body"),
    ];
    for (text, expected) in cases {
        match certificate::read(&text) {
            Ok(_) => panic!("the reader took this text:\n{text}"),
            Err(error) => assert!(
                error.contains(expected),
                "expected `{expected}`, got `{error}` for:\n{text}"
            ),
        }
    }

    // What the reader takes and the kernel refuses: a certificate that
    // names what the tables do not have.
    let refused = [
        ("question \"c\" 1 \"N1\"\ngoal n1", "leave a case open"),
        (
            "question \"c\" 1 \"N1\"\ngoal n0\ninstance term u5",
            "there is no term u5",
        ),
        (
            "question \"c\" 1 \"N1\"\ngoal n0\nlemma a4\n literal 0\n close p0",
            "part 0",
        ),
        (
            "question \"c\" 1 \"N1\"\ngoal n0\nlemma\n close p3",
            "part 0",
        ),
    ];
    for (lines, expected) in refused {
        let text = body(lines);
        let error = certificate::validate(&text).expect_err("a certificate that is none");
        assert!(
            error.contains(expected),
            "expected `{expected}`, got `{error}` for:\n{text}"
        );
    }

    // The least text, and one with a question that asks nothing.
    assert_eq!(certificate::validate("villanelle certificates 1\n"), Ok(0));
    assert_eq!(
        certificate::validate(&body("question \"c\" 1 \"N1\"\ngoal n0")),
        Ok(1)
    );
}

#[test]
fn a_string_is_read_as_it_was_written() {
    // What the writer writes of names and literals that have quotes, line
    // breaks, brackets and the sign of a comment in them.
    let odd = "line\nbreak \\ \"quoted\" \t \r \u{7f} \u{0} é {} [] # end";
    let mut solver = Solver::new(vec![("a \"site\"".to_string(), odd.to_string())]);
    solver.intern_term(AtomTerm::StrLit(odd.to_string()));
    solver.intern_term(AtomTerm::Var {
        name: odd.to_string(),
        ty: None,
        is_value_term: false,
    });
    let mut text = format!("{}\n", certificate::HEADER);
    let tables = solver.query(bdd::TRUE);
    certificate::write_body(&mut text, &tables, &solver.history_names, &[]).expect("a body");
    assert_eq!(
        text.lines().count(),
        solver.terms.len() + 4,
        "one line for each term, the history atom, and three more:\n{text}"
    );
    let bodies = certificate::read(&text).expect("a text");
    assert_eq!(bodies[0].history, solver.history_names);
    assert_eq!(bodies[0].terms, solver.terms);
    assert_eq!(bodies[0].given, solver.given);

    // And what the reader makes of escapes that a hand wrote.
    let text = "villanelle certificates 1\nbody\n\
        history h0 \"a \\\"site\\\"\" \"tab\\there\"\n\
        term u0 written str \"line\\nbreak \\\\ \\u{7f} é {} [] #\"\n\
        end\n";
    let bodies = certificate::read(text).expect("a text");
    assert_eq!(
        bodies[0].history,
        vec![("a \"site\"".to_string(), "tab\there".to_string())]
    );
    assert_eq!(
        bodies[0].terms,
        vec![AtomTerm::StrLit(
            "line\nbreak \\ \u{7f} é {} [] #".to_string()
        )]
    );
}

/// A text with a proof in which `depth` splits nest. Its lemma says that
/// `x ≤ 0` and `x ≥ 1` do not hold together, and every branch says so again.
fn nested(depth: usize) -> String {
    let mut text = String::from(
        "villanelle certificates 1\nbody\nterm u0 written var \"x\" none free\n\
         row a0 {1*u0} <= 0\nquestion \"deep\" 1 \"N1\"\ngoal n0\n\
         lemma a0 !a0\n literal 0\n literal 1\n",
    );
    for _ in 0..depth {
        text.push_str(" split {1*u0} <= 5\n");
    }
    // The low branch of the last split, and then the high branches from the
    // last split to the first. A branch below `above` splits has the rows of
    // the two literals and one row for each split before its own steps.
    text.push_str(&format!(" combine 1*p0 1*p1\n close p{}\n", depth + 2));
    for above in (1..=depth).rev() {
        text.push_str(&format!(" combine 1*p0 1*p1\n close p{}\n", above + 2));
    }
    text.push_str("end\n");
    text
}

#[test]
fn a_proof_as_deep_as_the_search_goes_is_read_and_validated() {
    assert_eq!(certificate::validate(&nested(0)), Ok(1));
    assert_eq!(certificate::validate(&nested(3)), Ok(1));
    assert_eq!(
        certificate::validate(&nested(certificate::NESTED_SPLITS)),
        Ok(1)
    );
    let error = certificate::validate(&nested(certificate::NESTED_SPLITS + 1))
        .expect_err("a proof that is too deep");
    assert!(error.contains("splits nest"), "{error}");

    // The branches are checked each by itself: the innermost one closed by
    // the row of its split, which is no contradiction.
    let wrong = nested(3).replacen("close p5", "close p4", 1);
    let error = certificate::validate(&wrong).expect_err("a branch that is open");
    assert!(error.contains("part 0"), "{error}");
    // And a branch that is not there.
    let cut = nested(3).replacen(" combine 1*p0 1*p1\n close p3\n", "", 1);
    let error = certificate::validate(&cut).expect_err("a split with one branch");
    assert!(error.contains("has no end"), "{error}");
}
