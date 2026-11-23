//! The certificate kernel (`docs/v2/facts.md`, section 8): what it grants as
//! an instance of the theory, and what it refuses.
//!
//! [V2] has the kernel check that an instance is an instance. A certificate
//! names its instances, and the kernel makes the formula of each from the
//! name and the terms of the query. These tests hold that matcher against
//! the real operations (section 5.3: every axiom is also a property test),
//! against the instances that the search makes, and against names that name
//! no instance. The proofs of lemmas and the Boolean step are tested with
//! the checker, in `tests/checker.rs`.

use std::collections::BTreeMap;
use villanelle_v2::bdd;
use villanelle_v2::facts::Solver;
use villanelle_v2::int::Int;
use villanelle_v2::kernel::Kernel;
use villanelle_v2::rng::Rng;
use villanelle_v2::terms::{AtomTerm, Instance, LinearTerm, TermId};
use villanelle_v2::typed::IntType;

fn int(value: i128) -> Int {
    Int::from_i128(value)
}

fn var(term: TermId) -> LinearTerm {
    LinearTerm::var(term)
}

/// A value in `[low, high]`, often at an end or near zero.
fn sample(rng: &mut Rng, low: i128, high: i128) -> i128 {
    match rng.below(5) {
        0 => low,
        1 => high,
        2 => rng.range(-3, 3).clamp(low, high),
        _ => rng.range(low, high),
    }
}

/// A name of an integer type with a value of that type.
struct Name {
    term: TermId,
    value: i128,
    /// The ends of its declared interval ([A9]): the bounds of its type that
    /// are literals.
    declared: (Option<i128>, Option<i128>),
}

/// A solver with `usize.max` and a name of every integer type, and the
/// values of a run.
fn names(rng: &mut Rng) -> (Solver, Vec<Name>, BTreeMap<TermId, Int>) {
    let mut solver = Solver::new(Vec::new());
    let mut values = BTreeMap::new();
    let usize_max = sample(rng, (1 << 32) - 1, (1 << 64) - 1);
    values.insert(solver.usize_max_term, int(usize_max));
    let mut names = Vec::new();
    for ty in IntType::ALL {
        let term = solver.fresh_var(ty.name().to_string(), Some(ty), true);
        let (low, high) = ty.bounds(&int(usize_max));
        let (low, high) = (
            low.to_i128().expect("a bound of a type"),
            high.to_i128().expect("a bound of a type"),
        );
        let value = sample(rng, low, high);
        values.insert(term, int(value));
        let declared = if ty == IntType::Usize {
            (Some(0), None)
        } else {
            (Some(low), Some(high))
        };
        names.push(Name {
            term,
            value,
            declared,
        });
    }
    (solver, names, values)
}

/// `name + shift`, with its value and its declared interval. The value may
/// be one that no type holds ([I2]).
fn operand(rng: &mut Rng, names: &[Name]) -> (LinearTerm, i128, (Option<i128>, Option<i128>)) {
    let name = rng.pick(names);
    let shift = if rng.chance(1, 2) {
        0
    } else {
        rng.range(-9, 9)
    };
    (
        var(name.term).add(&LinearTerm::from_i128(shift)),
        name.value + shift,
        (
            name.declared.0.map(|end| end + shift),
            name.declared.1.map(|end| end + shift),
        ),
    )
}

/// Section 5.3 of the fact logic: every instance of [A1], [A2] and [A7] to
/// [A9] that the kernel grants is true of the real operations, at the ends
/// of every type and for operands that no type holds.
#[test]
fn the_instances_of_the_arithmetic_axioms_hold_for_the_real_operations() {
    let mut rng = Rng::new(0x6b65_726e);
    let mut seen: BTreeMap<&str, usize> = BTreeMap::new();
    for _ in 0..400 {
        let (mut solver, names, mut values) = names(&mut rng);
        let mut kinds: BTreeMap<TermId, &str> = BTreeMap::new();
        kinds.insert(solver.usize_max_term, "A2");
        for name in &names {
            kinds.insert(name.term, "A1");
        }
        for _ in 0..3 {
            // [A7]: `t ÷ k` for a literal `k ≥ 1`.
            let (t, t_value, _) = operand(&mut rng, &names);
            let k = *rng.pick(&[1, 2, 3, 7, 10, 255, 256, 1 << 31, (1 << 64) - 1]);
            let quotient = solver.intern_term(AtomTerm::DivConst(t, int(k)));
            values.insert(quotient, int(t_value / k));
            kinds.insert(quotient, "A7");

            // [A8]: `div(s, t)` and `rem(s, t)`. For a divisor that is zero
            // the axiom says nothing, and the terms are some value.
            let (s, s_value, _) = operand(&mut rng, &names);
            let (t, t_value, _) = operand(&mut rng, &names);
            let (q_value, r_value) = if t_value == 0 {
                (17, 17)
            } else {
                (s_value / t_value, s_value % t_value)
            };
            let quotient = solver.intern_term(AtomTerm::Div(s.clone(), t.clone()));
            values.insert(quotient, int(q_value));
            kinds.insert(quotient, "A8 div");
            let remainder = solver.intern_term(AtomTerm::Rem(s, t));
            values.insert(remainder, int(r_value));
            kinds.insert(remainder, "A8 rem");

            // [A9]: `mul(s, t)`, bounded by the declared intervals. An end
            // may be absent, and then the planes that need it are.
            let (s, s_value, s_declared) = operand(&mut rng, &names);
            let (t, t_value, t_declared) = operand(&mut rng, &names);
            let mut end = |end: Option<i128>| end.filter(|_| rng.chance(3, 4)).map(int);
            let product = solver.intern_term(AtomTerm::Mul {
                left: s,
                right: t,
                left_bounds: (end(s_declared.0), end(s_declared.1)),
                right_bounds: (end(t_declared.0), end(t_declared.1)),
            });
            values.insert(product, int(s_value).times(&int(t_value)));
            kinds.insert(product, "A9");
        }
        solver.instantiate_all();

        let mut kernel = Kernel::new();
        let query = solver.query(bdd::TRUE);
        for instance in &solver.instances {
            let holds = kernel
                .instance_holds(&query, &instance.name, &values)
                .unwrap_or_else(|error| {
                    panic!("the kernel refuses the instance {}: {error}", instance.name)
                });
            assert!(
                holds,
                "the instance {} is false for the values {values:?} of the terms {:?}",
                instance.name, solver.terms
            );
            let kind = match &instance.name {
                Instance::Term(term) => kinds[term],
                Instance::Pair(_, _) => "S5",
                other => panic!("an instance {other} of terms that are numbers"),
            };
            *seen.entry(kind).or_default() += 1;
        }
    }
    for kind in ["A1", "A2", "A7", "A8 div", "A8 rem", "A9", "S5"] {
        assert!(
            seen.get(kind).copied().unwrap_or(0) >= 400,
            "{kind}: {seen:?}"
        );
    }
}

/// The test above can fail: a quotient that is one too large makes the
/// instance of [A7] false.
#[test]
fn a_wrong_quotient_makes_its_instance_false() {
    let mut solver = Solver::new(Vec::new());
    let t = solver.fresh_var("t".to_string(), Some(IntType::U32), true);
    let quotient = solver.intern_term(AtomTerm::DivConst(var(t), int(7)));
    solver.instantiate_all();
    let mut kernel = Kernel::new();
    let query = solver.query(bdd::TRUE);
    let holds = |kernel: &mut Kernel, q: i128| {
        let values = BTreeMap::from([(t, int(30)), (quotient, int(q))]);
        kernel
            .instance_holds(&query, &Instance::Term(quotient), &values)
            .expect("an instance of [A7]")
    };
    assert!(holds(&mut kernel, 4));
    assert!(!holds(&mut kernel, 5));
    assert!(!holds(&mut kernel, 3));
}

/// A solver with terms of every form of slices 2 and 3.
struct Forms {
    solver: Solver,
    p: TermId,
    q: TermId,
    p_fields: Vec<TermId>,
    q_fields: Vec<TermId>,
    pair: TermId,
    short_pair: TermId,
    update: TermId,
    other_element: TermId,
    x: TermId,
}

fn forms() -> Forms {
    let mut solver = Solver::new(Vec::new());
    // Struct 0 has two fields, a `u8` and a `bool`.
    solver.register_struct_arity(0, 2);
    let name = |solver: &mut Solver, text: &str, ty: Option<IntType>| {
        solver.fresh_var(text.to_string(), ty, true)
    };
    let x = name(&mut solver, "x", Some(IntType::U8));
    let y = name(&mut solver, "y", Some(IntType::U8));
    let i = name(&mut solver, "i", Some(IntType::Usize));
    let j = name(&mut solver, "j", Some(IntType::Usize));
    let [p, q, v, w, s, t, o] =
        ["p", "q", "v", "w", "s", "t", "o"].map(|text| name(&mut solver, text, None));
    let field = |base: TermId, field_idx: usize| AtomTerm::Field {
        base: var(base),
        struct_id: 0,
        field_idx,
        int_ty: (field_idx == 0).then_some(IntType::U8),
        is_bool: field_idx == 1,
        is_value_term: true,
    };
    // [A4].
    let pair = solver.intern_term(AtomTerm::StructCtor(0, vec![var(x), var(y)]));
    solver.intern_term(AtomTerm::StructCtor(0, vec![var(y), var(x)]));
    let short_pair = solver.intern_term(AtomTerm::StructCtor(0, vec![var(x)]));
    let p_fields = vec![
        solver.intern_term(field(p, 0)),
        solver.intern_term(field(p, 1)),
    ];
    let q_fields = vec![
        solver.intern_term(field(q, 0)),
        solver.intern_term(field(q, 1)),
    ];
    // [A5].
    let constructor = |ctor_idx: usize, fields: Vec<LinearTerm>| AtomTerm::VariantCtor {
        variant_id: 0,
        ctor_idx,
        fields,
        num_ctors: 2,
    };
    solver.intern_term(constructor(0, Vec::new()));
    solver.intern_term(constructor(1, vec![var(x)]));
    solver.intern_term(constructor(1, vec![var(y)]));
    solver.intern_term(AtomTerm::VariantTag {
        base: var(o),
        variant_id: 0,
        num_ctors: 2,
    });
    // [A3].
    solver.intern_term(AtomTerm::VecLit(vec![var(x), var(y)]));
    solver.intern_term(AtomTerm::EmptyMap);
    solver.intern_term(AtomTerm::Len(var(v)));
    solver.intern_term(AtomTerm::Len(var(s)));
    solver.intern_term(AtomTerm::StrLit("a".to_string()));
    solver.intern_term(AtomTerm::StrLit("b".to_string()));
    // [A6].
    let update = solver.intern_term(AtomTerm::Update {
        base: var(v),
        index: var(i),
        value: var(x),
    });
    solver.intern_term(AtomTerm::Update {
        base: var(w),
        index: var(j),
        value: var(y),
    });
    let other_element = solver.intern_term(AtomTerm::Index {
        base: var(w),
        index: var(j),
        int_ty: Some(IntType::U8),
        is_bool: false,
        is_value_term: true,
    });
    // [S5], [I10].
    solver.intern_term(AtomTerm::Trim(var(s)));
    solver.intern_term(AtomTerm::Trim(var(t)));
    solver.intern_term(AtomTerm::PureAlt(3, vec![var(x), var(i)]));
    solver.intern_term(AtomTerm::PureAlt(3, vec![var(y), var(j)]));
    solver.intern_term(AtomTerm::PurePay(3, 0, 0, vec![var(x), var(i)]));
    solver.intern_term(AtomTerm::PurePay(3, 0, 0, vec![var(y), var(j)]));
    solver.instantiate_all();
    Forms {
        solver,
        p,
        q,
        p_fields,
        q_fields,
        pair,
        short_pair,
        update,
        other_element,
        x,
    }
}

/// The kernel and the search state the theory separately, and they agree:
/// the kernel grants every instance that the search makes, for terms of
/// every form. Every kind of instance is among them.
#[test]
fn the_kernel_grants_every_instance_that_the_search_makes() {
    let forms = forms();
    let solver = &forms.solver;
    let mut kernel = Kernel::new();
    let query = solver.query(bdd::TRUE);
    let mut kinds = [0usize; 4];
    for instance in &solver.instances {
        if let Err(error) = kernel.instance(&query, &instance.name) {
            panic!(
                "the kernel refuses the instance {} of the search: {error}",
                instance.name
            );
        }
        kinds[match instance.name {
            Instance::Term(_) => 0,
            Instance::Pair(_, _) => 1,
            Instance::Frame { .. } => 2,
            Instance::Extension { .. } => 3,
        }] += 1;
    }
    assert!(kinds.iter().all(|count| *count > 0), "{kinds:?}");
    // The forms that have an instance of their own, each at least once.
    let has = |form: fn(&AtomTerm) -> bool| {
        solver.instances.iter().any(
            |instance| matches!(instance.name, Instance::Term(term) if form(&solver.terms[term])),
        )
    };
    assert!(has(|term| matches!(term, AtomTerm::Field { .. })));
    assert!(has(|term| matches!(term, AtomTerm::Index { .. })));
    assert!(has(|term| matches!(term, AtomTerm::Len(_))));
    assert!(has(|term| matches!(term, AtomTerm::VecLit(_))));
    assert!(has(|term| matches!(term, AtomTerm::EmptyMap)));
    assert!(has(|term| matches!(term, AtomTerm::VariantCtor { .. })));
    assert!(has(|term| matches!(term, AtomTerm::VariantTag { .. })));
    assert!(has(|term| matches!(term, AtomTerm::Update { .. })));
}

/// A name that is not the name of an instance is refused ([V2], review
/// finding RC9), for every kind of name.
#[test]
fn the_kernel_refuses_what_is_not_an_instance() {
    let mut forms = forms();
    let mut kernel = Kernel::new();
    let Forms {
        p,
        q,
        pair,
        short_pair,
        update,
        other_element,
        x,
        ..
    } = forms;
    let (p_fields, q_fields) = (forms.p_fields.clone(), forms.q_fields.clone());

    // Terms that the checker could write and of which the theory says
    // nothing, or nothing of that kind.
    let no_type = forms.solver.fresh_var("z".to_string(), None, true);
    let by_zero = forms.solver.intern_term(AtomTerm::DivConst(var(x), int(0)));
    let by_less = forms
        .solver
        .intern_term(AtomTerm::DivConst(var(x), int(-3)));
    let no_constructor = forms.solver.intern_term(AtomTerm::VariantCtor {
        variant_id: 0,
        ctor_idx: 2,
        fields: Vec::new(),
        num_ctors: 2,
    });
    // A field of a constructor term is whatever was put there ([A1]), even
    // when the term is marked as a part of a value.
    let field_of_made = forms.solver.intern_term(AtomTerm::Field {
        base: var(pair),
        struct_id: 0,
        field_idx: 0,
        int_ty: Some(IntType::U8),
        is_bool: false,
        is_value_term: true,
    });
    forms.solver.instantiate_all();
    assert!(
        forms
            .solver
            .instances
            .iter()
            .all(|instance| instance.name != Instance::Term(field_of_made)),
        "the search gives no range to a field of a constructor term"
    );

    let query = forms.solver.query(bdd::TRUE);
    let extension =
        |left: TermId, left_fields: &[TermId], right: TermId, right_fields: &[TermId]| {
            Instance::Extension {
                structure: 0,
                left,
                left_fields: left_fields.to_vec(),
                right,
                right_fields: right_fields.to_vec(),
            }
        };
    let refused = [
        (
            "a term that the query does not have",
            Instance::Term(usize::MAX),
        ),
        (
            "the range of a name without a type",
            Instance::Term(no_type),
        ),
        ("a quotient by zero", Instance::Term(by_zero)),
        ("a quotient by a negative literal", Instance::Term(by_less)),
        (
            "a constructor that the variant does not have",
            Instance::Term(no_constructor),
        ),
        (
            "the range of a field of a constructor term",
            Instance::Term(field_of_made),
        ),
        ("a struct constructor by itself", Instance::Term(pair)),
        ("two names together", Instance::Pair(p, q)),
        ("a name and an update together", Instance::Pair(p, update)),
        (
            "two constructor terms that differ in length",
            Instance::Pair(pair, short_pair),
        ),
        (
            "a frame for a term that is no update",
            Instance::Frame {
                update: p,
                element: other_element,
                original: other_element,
            },
        ),
        (
            "a frame for an element of another vector",
            Instance::Frame {
                update,
                element: other_element,
                original: other_element,
            },
        ),
        (
            "an extension without the fields of a side",
            extension(p, &[], q, &q_fields),
        ),
        (
            "an extension with one field of two",
            extension(p, &p_fields[..1], q, &q_fields),
        ),
        (
            "an extension with the fields of another term",
            extension(p, &q_fields, q, &q_fields),
        ),
        (
            "an extension with the fields in another order",
            extension(p, &[p_fields[1], p_fields[0]], q, &q_fields),
        ),
        (
            "an extension that names fields of a constructor term",
            extension(pair, &p_fields, q, &q_fields),
        ),
        (
            "an extension for a struct that is not known",
            Instance::Extension {
                structure: 9,
                left: p,
                left_fields: p_fields.clone(),
                right: q,
                right_fields: q_fields.clone(),
            },
        ),
    ];
    for (what, instance) in refused {
        assert!(
            kernel.instance(&query, &instance).is_err(),
            "the kernel must refuse {what}: {instance}"
        );
    }
    // The same names with the right terms are instances.
    assert!(
        kernel
            .instance(&query, &extension(p, &p_fields, q, &q_fields))
            .is_ok()
    );
    assert!(
        kernel
            .instance(&query, &extension(pair, &[], q, &q_fields))
            .is_ok()
    );
}

/// What stands beside a term is the checker's to say. The frame instance of
/// [A6] speaks of an element `v[j]` that the checker did not write. The
/// search adds it, with the element type of another vector on which `j` is
/// an index, since the solver does not know the sort of every vector. The
/// kernel takes the term as a name and gives it no range, until the checker
/// writes the same term.
#[test]
fn a_term_that_the_search_added_has_no_range() {
    let mut solver = Solver::new(Vec::new());
    let [v, w] = ["v", "w"].map(|text| solver.fresh_var(text.to_string(), None, true));
    let [i, j] =
        ["i", "j"].map(|text| solver.fresh_var(text.to_string(), Some(IntType::Usize), true));
    let e = solver.fresh_var("e".to_string(), Some(IntType::U32), true);
    solver.intern_term(AtomTerm::Update {
        base: var(v),
        index: var(i),
        value: var(e),
    });
    let element = |base: TermId| AtomTerm::Index {
        base: var(base),
        index: var(j),
        int_ty: Some(IntType::U8),
        is_bool: false,
        is_value_term: true,
    };
    solver.intern_term(element(w));
    solver.instantiate_all();

    let added = solver
        .terms
        .iter()
        .position(|term| *term == element(v))
        .expect("the frame instance speaks of `v[j]`");
    assert!(!solver.given[added]);
    let has_range = |solver: &Solver| {
        solver
            .instances
            .iter()
            .any(|instance| instance.name == Instance::Term(added))
    };
    assert!(!has_range(&solver), "the search gives the term no range");
    let mut kernel = Kernel::new();
    assert!(
        kernel
            .instance(&solver.query(bdd::TRUE), &Instance::Term(added))
            .is_err(),
        "the kernel gives no range to a term that the checker did not write"
    );
    // The frame instance itself is one: it needs no type.
    let frame = solver
        .instances
        .iter()
        .find(|instance| matches!(instance.name, Instance::Frame { original, .. } if original == added))
        .expect("the frame instance");
    assert!(
        kernel
            .instance(&solver.query(bdd::TRUE), &frame.name)
            .is_ok()
    );

    assert_eq!(solver.intern_term(element(v)), added);
    solver.instantiate_all();
    assert!(solver.given[added] && has_range(&solver));
    assert!(
        kernel
            .instance(&solver.query(bdd::TRUE), &Instance::Term(added))
            .is_ok(),
        "the checker wrote the term, and it has the range of its type"
    );
}
