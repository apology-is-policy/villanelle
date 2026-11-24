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
use villanelle_v2::oracle::Value;
use villanelle_v2::rng::Rng;
use villanelle_v2::terms::{AtomTerm, Instance, LinearTerm, SortTag, TermId};
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
    solver.intern_term(AtomTerm::VecLit("u8".to_string(), vec![var(x), var(y)]));
    solver.intern_term(AtomTerm::EmptyMap("string".to_string(), "u8".to_string()));
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
    assert!(has(|term| matches!(term, AtomTerm::VecLit(_, _))));
    assert!(has(|term| matches!(term, AtomTerm::EmptyMap(_, _))));
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

// The axioms of the data ([A3] to [A6]) against real values.
//
// A term of a data type has no arithmetic: in a row it is a number that says
// which value it is ([J1]). The tests below give every term the number of
// its real value, the same number for equal values of one type and another
// for any other value, and ask that every instance is then true. The values
// are the oracle's, and a term has the value that the oracle's operations
// give: a field, an element, a length, a write of one element.

/// The types of the data in these tests.
#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Debug)]
enum Ty {
    U8,
    I8,
    Usize,
    Bool,
    Text,
    /// `struct pair {a : u8, b : bool}`.
    Pair,
    /// `struct label {name : string, at : pair, marks : [u8]}`.
    Label,
    /// `variant shape {dot │ circle {r : u8} │ named {l : label, on : bool}}`.
    Shape,
    Bytes,
    Signed,
    Flags,
    Pairs,
    Rows,
    Shapes,
    /// `string ⇀ u8`.
    Table,
    /// `u8 ⇀ bool`.
    Marks,
}

const PAIR: usize = 0;
const LABEL: usize = 1;
const SHAPE: usize = 0;

/// The constructors of `shape`, with the types of their fields.
const CONSTRUCTORS: [(&str, &[Ty]); 3] = [
    ("dot", &[]),
    ("circle", &[Ty::U8]),
    ("named", &[Ty::Label, Ty::Bool]),
];

fn structure(id: usize, name: &str, fields: Vec<Value>) -> Value {
    Value::Struct {
        ty: id,
        name: name.to_string(),
        fields,
    }
}

fn shape(constructor: usize, fields: Vec<Value>) -> Value {
    Value::Variant {
        ty: SHAPE,
        name: "shape".to_string(),
        constructor,
        constructor_name: CONSTRUCTORS[constructor].0.to_string(),
        fields,
    }
}

fn number_value(value: i128) -> Value {
    Value::Int(int(value))
}

impl Ty {
    const ALL: [Ty; 16] = [
        Ty::U8,
        Ty::I8,
        Ty::Usize,
        Ty::Bool,
        Ty::Text,
        Ty::Pair,
        Ty::Label,
        Ty::Shape,
        Ty::Bytes,
        Ty::Signed,
        Ty::Flags,
        Ty::Pairs,
        Ty::Rows,
        Ty::Shapes,
        Ty::Table,
        Ty::Marks,
    ];
    const VECTORS: [Ty; 6] = [
        Ty::Bytes,
        Ty::Signed,
        Ty::Flags,
        Ty::Pairs,
        Ty::Rows,
        Ty::Shapes,
    ];
    const MEASURED: [Ty; 9] = [
        Ty::Bytes,
        Ty::Signed,
        Ty::Flags,
        Ty::Pairs,
        Ty::Rows,
        Ty::Shapes,
        Ty::Text,
        Ty::Table,
        Ty::Marks,
    ];

    /// The type as the checker writes it beside a literal.
    fn text(self) -> &'static str {
        match self {
            Ty::U8 => "u8",
            Ty::I8 => "i8",
            Ty::Usize => "usize",
            Ty::Bool => "bool",
            Ty::Text => "string",
            Ty::Pair => "pair",
            Ty::Label => "label",
            Ty::Shape => "shape",
            Ty::Bytes => "[u8]",
            Ty::Signed => "[i8]",
            Ty::Flags => "[bool]",
            Ty::Pairs => "[pair]",
            Ty::Rows => "[[u8]]",
            Ty::Shapes => "[shape]",
            Ty::Table => "string ⇀ u8",
            Ty::Marks => "u8 ⇀ bool",
        }
    }

    fn int(self) -> Option<IntType> {
        match self {
            Ty::U8 => Some(IntType::U8),
            Ty::I8 => Some(IntType::I8),
            Ty::Usize => Some(IntType::Usize),
            _ => None,
        }
    }

    fn element(self) -> Option<Ty> {
        match self {
            Ty::Bytes => Some(Ty::U8),
            Ty::Signed => Some(Ty::I8),
            Ty::Flags => Some(Ty::Bool),
            Ty::Pairs => Some(Ty::Pair),
            Ty::Rows => Some(Ty::Bytes),
            Ty::Shapes => Some(Ty::Shape),
            _ => None,
        }
    }

    /// The types of the keys and of the values of a map.
    fn entries(self) -> Option<(Ty, Ty)> {
        match self {
            Ty::Table => Some((Ty::Text, Ty::U8)),
            Ty::Marks => Some((Ty::U8, Ty::Bool)),
            _ => None,
        }
    }

    /// The number, the name and the types of the fields of a struct.
    fn fields(self) -> Option<(usize, &'static str, &'static [Ty])> {
        match self {
            Ty::Pair => Some((PAIR, "pair", &[Ty::U8, Ty::Bool])),
            Ty::Label => Some((LABEL, "label", &[Ty::Text, Ty::Pair, Ty::Bytes])),
            _ => None,
        }
    }

    /// The sort that the checker writes beside a term of the type.
    fn sort(self) -> SortTag {
        match self {
            Ty::U8 | Ty::I8 | Ty::Usize => SortTag::Int,
            Ty::Bool => SortTag::Bool,
            Ty::Text => SortTag::String,
            Ty::Pair => SortTag::Struct(PAIR),
            Ty::Label => SortTag::Struct(LABEL),
            Ty::Shape => SortTag::Variant(SHAPE),
            Ty::Table | Ty::Marks => {
                let (key, value) = self.entries().expect("a map");
                SortTag::Map(key.text().to_string(), value.text().to_string())
            }
            vector => SortTag::Vector(vector.element().expect("a vector").text().to_string()),
        }
    }

    /// What an element out of range is in a formula ([E-Formula]): the
    /// oracle's value for the type.
    fn default(self) -> Value {
        match self {
            Ty::U8 | Ty::I8 | Ty::Usize => number_value(0),
            Ty::Bool => Value::Bool(false),
            Ty::Text => Value::String(String::new()),
            Ty::Pair | Ty::Label => {
                let (id, name, fields) = self.fields().expect("a struct");
                structure(
                    id,
                    name,
                    fields.iter().map(|field| field.default()).collect(),
                )
            }
            Ty::Shape => shape(0, Vec::new()),
            Ty::Table | Ty::Marks => Value::Map(BTreeMap::new()),
            _ => Value::Vector(Vec::new()),
        }
    }

    /// A value of the type, from few enough that two are often equal.
    fn draw(self, rng: &mut Rng) -> Value {
        match self {
            Ty::U8 => number_value(*rng.pick(&[0, 1, 2, 255])),
            Ty::I8 => number_value(*rng.pick(&[-128, -1, 0, 1, 127])),
            Ty::Usize => number_value(*rng.pick(&[0, 0, 1, 1, 2, 3, 4, (1 << 32) - 1])),
            Ty::Bool => Value::Bool(rng.chance(1, 2)),
            Ty::Text => Value::String(rng.pick(&["", "a", " a", "b "]).to_string()),
            Ty::Pair | Ty::Label => {
                let (id, name, fields) = self.fields().expect("a struct");
                structure(
                    id,
                    name,
                    fields.iter().map(|field| field.draw(rng)).collect(),
                )
            }
            Ty::Shape => {
                let constructor = rng.below(3) as usize;
                let fields = CONSTRUCTORS[constructor].1;
                shape(
                    constructor,
                    fields.iter().map(|field| field.draw(rng)).collect(),
                )
            }
            Ty::Table | Ty::Marks => {
                let (key, value) = self.entries().expect("a map");
                let entries = (0..rng.below(3)).map(|_| (key.draw(rng), value.draw(rng)));
                Value::Map(entries.collect())
            }
            vector => {
                let element = vector.element().expect("a vector");
                Value::Vector((0..rng.below(4)).map(|_| element.draw(rng)).collect())
            }
        }
    }

    /// Whether a value is one of the type: its numbers lie in their ranges.
    /// A constructor term of a formula may hold a number that does not.
    fn holds(self, value: &Value) -> bool {
        let within = |low: i128, high: i128| matches!(value, Value::Int(n) if n.to_i128().is_some_and(|n| low <= n && n <= high));
        match (self, value) {
            (Ty::U8, _) => within(0, 255),
            (Ty::I8, _) => within(-128, 127),
            (Ty::Usize, _) => within(0, (1 << 32) - 1),
            (Ty::Pair | Ty::Label, Value::Struct { fields, .. }) => {
                let (_, _, types) = self.fields().expect("a struct");
                types.iter().zip(fields).all(|(ty, field)| ty.holds(field))
            }
            (
                Ty::Shape,
                Value::Variant {
                    constructor,
                    fields,
                    ..
                },
            ) => {
                let types = CONSTRUCTORS[*constructor].1;
                types.iter().zip(fields).all(|(ty, field)| ty.holds(field))
            }
            (vector, Value::Vector(items)) => {
                let element = vector.element().expect("a vector");
                items.iter().all(|item| element.holds(item))
            }
            _ => true,
        }
    }
}

/// Terms as the checker writes them, with the real value of each.
struct World {
    solver: Solver,
    /// The type of every term that the test wrote.
    types: BTreeMap<TermId, Ty>,
    /// The value that each name holds.
    held: BTreeMap<TermId, Value>,
    /// The value of each term, once asked.
    values: BTreeMap<TermId, Value>,
    /// The terms that the test wrote, by type.
    pool: BTreeMap<Ty, Vec<TermId>>,
    /// The number of each value that is no number itself.
    numbers: BTreeMap<(Ty, Value), usize>,
}

impl World {
    fn new(usize_max: Int) -> World {
        let mut solver = Solver::new(Vec::new());
        solver.register_struct_arity(PAIR, 2);
        solver.register_struct_arity(LABEL, 3);
        let greatest = solver.usize_max_term;
        World {
            solver,
            types: BTreeMap::from([(greatest, Ty::Usize)]),
            held: BTreeMap::from([(greatest, Value::Int(usize_max))]),
            values: BTreeMap::new(),
            pool: BTreeMap::new(),
            numbers: BTreeMap::new(),
        }
    }

    /// Notes a term that the test wrote, and writes its sort beside it as
    /// the checker does. A term has one type.
    fn wrote(&mut self, id: TermId, ty: Ty) -> TermId {
        if let Some(before) = self.types.insert(id, ty) {
            assert_eq!(
                before, ty,
                "the term {:?} at two types",
                self.solver.terms[id]
            );
        }
        self.solver.term_sorts.insert(id, ty.sort());
        let pool = self.pool.entry(ty).or_default();
        if !pool.contains(&id) {
            pool.push(id);
        }
        id
    }

    fn write(&mut self, term: AtomTerm, ty: Ty) -> TermId {
        let id = self.solver.intern_term(term);
        self.wrote(id, ty)
    }

    /// A name that holds a value of its type.
    fn name(&mut self, ty: Ty, value: Value) -> TermId {
        assert!(ty.holds(&value), "{value:?} is no value of {ty:?}");
        let id = self.solver.fresh_var(ty.text().to_string(), ty.int(), true);
        self.held.insert(id, value);
        self.wrote(id, ty)
    }

    /// `base.x`, as the checker writes it: for a constructor term it is the
    /// argument.
    fn field(&mut self, base: TermId, field_idx: usize) -> LinearTerm {
        let (struct_id, _, fields) = self.type_of(base).fields().expect("a struct");
        if let AtomTerm::StructCtor(_, arguments) = &self.solver.terms[base] {
            return arguments[field_idx].clone();
        }
        let ty = fields[field_idx];
        let is_value_term = self.solver.is_value_term_linear(&var(base));
        var(self.write(
            AtomTerm::Field {
                base: var(base),
                struct_id,
                field_idx,
                int_ty: ty.int(),
                is_bool: ty == Ty::Bool,
                is_value_term,
            },
            ty,
        ))
    }

    /// `base[index]`.
    fn element(&mut self, base: TermId, index: LinearTerm) -> TermId {
        let ty = self.type_of(base).element().expect("a vector");
        let is_value_term = self.solver.is_value_term_linear(&var(base));
        self.write(
            AtomTerm::Index {
                base: var(base),
                index,
                int_ty: ty.int(),
                is_bool: ty == Ty::Bool,
                is_value_term,
            },
            ty,
        )
    }

    /// `base[index ↦ value]`, as a write of one element makes it ([I9]).
    fn update(&mut self, base: TermId, index: LinearTerm, value: LinearTerm) -> TermId {
        let ty = self.type_of(base);
        self.element(base, index.clone());
        self.write(
            AtomTerm::Update {
                base: var(base),
                index,
                value,
            },
            ty,
        )
    }

    fn length(&mut self, of: TermId) -> TermId {
        self.write(AtomTerm::Len(var(of)), Ty::Usize)
    }

    fn pair(&mut self, a: LinearTerm, b: LinearTerm) -> TermId {
        self.write(AtomTerm::StructCtor(PAIR, vec![a, b]), Ty::Pair)
    }

    fn constructor(&mut self, ctor_idx: usize, fields: Vec<LinearTerm>) -> TermId {
        self.write(
            AtomTerm::VariantCtor {
                variant_id: SHAPE,
                ctor_idx,
                fields,
                num_ctors: CONSTRUCTORS.len(),
            },
            Ty::Shape,
        )
    }

    fn tag(&mut self, of: TermId) -> TermId {
        self.write(
            AtomTerm::VariantTag {
                base: var(of),
                variant_id: SHAPE,
                num_ctors: CONSTRUCTORS.len(),
            },
            Ty::Usize,
        )
    }

    fn vector(&mut self, ty: Ty, items: Vec<LinearTerm>) -> TermId {
        let element = ty.element().expect("a vector");
        self.write(AtomTerm::VecLit(element.text().to_string(), items), ty)
    }

    fn empty_map(&mut self, ty: Ty) -> TermId {
        let (key, value) = ty.entries().expect("a map");
        self.write(
            AtomTerm::EmptyMap(key.text().to_string(), value.text().to_string()),
            ty,
        )
    }

    /// The position of a term that the search added.
    fn id_of(&self, term: &AtomTerm) -> TermId {
        let found = self.solver.terms.iter().position(|other| other == term);
        found.unwrap_or_else(|| panic!("there is no term {term:?}"))
    }

    /// The type of a term: what the test wrote, and for a term that the
    /// search added what its form says.
    fn type_of(&self, id: TermId) -> Ty {
        if let Some(ty) = self.types.get(&id) {
            return *ty;
        }
        match &self.solver.terms[id] {
            AtomTerm::Len(_) | AtomTerm::VariantTag { .. } => Ty::Usize,
            AtomTerm::Index { base, .. } => {
                let base = base.as_var().expect("an element of a term");
                self.type_of(base).element().expect("a vector")
            }
            other => panic!("the search added the term {other:?}"),
        }
    }

    /// The value of an operand of the type: a term, or a sum of numbers.
    fn operand(&mut self, term: &LinearTerm, ty: Ty) -> Value {
        if let Some(id) = term.as_var() {
            return self.value(id);
        }
        let mut total = term.constant.clone();
        for (id, coeff) in &term.coeffs {
            let Value::Int(part) = self.value(*id) else {
                panic!("a sum over a value that is no number");
            };
            total = total.plus(&coeff.times(&part));
        }
        if ty == Ty::Bool {
            Value::Bool(!total.is_zero())
        } else {
            Value::Int(total)
        }
    }

    /// The real value of a term.
    fn value(&mut self, id: TermId) -> Value {
        if let Some(value) = self.values.get(&id) {
            return value.clone();
        }
        let ty = self.type_of(id);
        let of = |term: &LinearTerm| term.as_var().expect("a part of a term");
        let value = match self.solver.terms[id].clone() {
            AtomTerm::Var { .. } | AtomTerm::UsizeMax => self.held[&id].clone(),
            AtomTerm::StrLit(text) => Value::String(text),
            AtomTerm::Trim(text) => match self.value(of(&text)) {
                Value::String(text) => Value::String(text.trim().to_string()),
                other => panic!("`trim` of {other:?}"),
            },
            AtomTerm::EmptyMap(_, _) => Value::Map(BTreeMap::new()),
            AtomTerm::VecLit(_, items) => {
                let element = ty.element().expect("a vector");
                let items = items.iter().map(|item| self.operand(item, element));
                Value::Vector(items.collect())
            }
            AtomTerm::StructCtor(_, arguments) => {
                let (id, name, fields) = ty.fields().expect("a struct");
                let arguments = arguments.iter().zip(fields);
                let arguments = arguments.map(|(argument, ty)| self.operand(argument, *ty));
                structure(id, name, arguments.collect())
            }
            AtomTerm::VariantCtor {
                ctor_idx, fields, ..
            } => {
                let fields = fields.iter().zip(CONSTRUCTORS[ctor_idx].1);
                let fields = fields.map(|(field, ty)| self.operand(field, *ty));
                shape(ctor_idx, fields.collect())
            }
            AtomTerm::Len(base) => match self.value(of(&base)) {
                Value::Vector(items) => number_value(items.len() as i128),
                Value::String(text) => number_value(text.len() as i128),
                Value::Map(entries) => number_value(entries.len() as i128),
                other => panic!("`len` of {other:?}"),
            },
            AtomTerm::Field {
                base, field_idx, ..
            } => match self.value(of(&base)) {
                Value::Struct { mut fields, .. } => fields.swap_remove(field_idx),
                other => panic!("a field of {other:?}"),
            },
            AtomTerm::VariantTag { base, .. } => match self.value(of(&base)) {
                Value::Variant { constructor, .. } => number_value(constructor as i128),
                other => panic!("the constructor of {other:?}"),
            },
            AtomTerm::Index { base, index, .. } => {
                let Value::Vector(mut items) = self.value(of(&base)) else {
                    panic!("an element of a value that is no vector");
                };
                match self.position(&index, items.len()) {
                    Some(at) => items.swap_remove(at),
                    None => ty.default(),
                }
            }
            AtomTerm::Update { base, index, value } => {
                let Value::Vector(mut items) = self.value(of(&base)) else {
                    panic!("a write to a value that is no vector");
                };
                let written = self.operand(&value, ty.element().expect("a vector"));
                // A write is made only at an index proved in range. For any
                // other index the term is the vector as it was.
                if let Some(at) = self.position(&index, items.len()) {
                    items[at] = written;
                }
                Value::Vector(items)
            }
            other => panic!("a term {other:?} that these tests do not write"),
        };
        self.values.insert(id, value.clone());
        value
    }

    /// The index as a position in a vector of the length, if it is one.
    fn position(&mut self, index: &LinearTerm, length: usize) -> Option<usize> {
        let Value::Int(at) = self.operand(index, Ty::Usize) else {
            panic!("an index that is no number");
        };
        let at = at.to_i128()?;
        (0 <= at && at < length as i128).then_some(at as usize)
    }

    /// The number of the value of a term: the value itself for a number,
    /// zero or one for a truth value, and for any other value a number
    /// that no other value has, of its type or of another.
    fn number(&mut self, id: TermId) -> Int {
        let ty = self.type_of(id);
        match self.value(id) {
            Value::Int(value) => value,
            Value::Bool(value) => int(i128::from(value)),
            value => {
                let next = self.numbers.len();
                int(*self.numbers.entry((ty, value)).or_insert(next) as i128)
            }
        }
    }

    /// Every instance of the search, the numbers of the terms, and the
    /// instances that are false for them, with any numbers of `wrong` in
    /// place of the real ones.
    fn instances(&mut self, wrong: &[(TermId, Int)]) -> (BTreeMap<TermId, Int>, Vec<Instance>) {
        self.solver.instantiate_all();
        let mut numbers = BTreeMap::new();
        for id in 0..self.solver.terms.len() {
            numbers.insert(id, self.number(id));
        }
        numbers.extend(wrong.iter().cloned());
        let query = self.solver.query(bdd::TRUE);
        let rows = Kernel::rows(&query, &numbers);
        let mut kernel = Kernel::new();
        let mut failed = Vec::new();
        for instance in &self.solver.instances {
            let holds = kernel
                .instance_holds_for(&query, &instance.name, &rows)
                .unwrap_or_else(|error| {
                    panic!("the kernel refuses the instance {}: {error}", instance.name)
                });
            if !holds {
                failed.push(instance.name.clone());
            }
        }
        (numbers, failed)
    }

    // What follows writes terms at random.

    fn any(&self, rng: &mut Rng, ty: Ty) -> TermId {
        *rng.pick(&self.pool[&ty])
    }

    /// An operand of a type: a term, and for a number or a truth value a
    /// literal too. A sum of a number and a literal may leave the type, as
    /// an argument in a formula may ([I2]).
    fn some(&mut self, rng: &mut Rng, ty: Ty) -> LinearTerm {
        let term = var(self.any(rng, ty));
        match ty {
            Ty::Bool if rng.chance(1, 4) => LinearTerm::from_i128(rng.range(0, 1)),
            Ty::U8 | Ty::I8 | Ty::Usize => match rng.below(4) {
                0 => LinearTerm::from_i128(rng.range(0, 3)),
                1 => term.add(&LinearTerm::from_i128(rng.range(-1, 1))),
                _ => term,
            },
            _ => term,
        }
    }

    fn step(&mut self, rng: &mut Rng) {
        match rng.below(20) {
            // A field, or every field ([A4]).
            0..=2 => {
                let ty = *rng.pick(&[Ty::Pair, Ty::Label]);
                let base = self.any(rng, ty);
                self.fields_of(rng, base);
            }
            // An element.
            3 | 4 => {
                let ty = *rng.pick(&Ty::VECTORS);
                let base = self.any(rng, ty);
                let index = self.some(rng, Ty::Usize);
                self.element(base, index);
            }
            // A length ([A3]).
            5 => {
                let ty = *rng.pick(&Ty::MEASURED);
                let of = self.any(rng, ty);
                self.length(of);
            }
            // A constructor term of a struct ([A4]), and now and then a
            // name that is bound to it, with its fields.
            6..=8 => {
                let ty = *rng.pick(&[Ty::Pair, Ty::Pair, Ty::Label]);
                let (id, _, fields) = ty.fields().expect("a struct");
                let arguments = fields.iter().map(|field| self.some(rng, *field)).collect();
                let made = self.write(AtomTerm::StructCtor(id, arguments), ty);
                let value = self.value(made);
                if ty.holds(&value) && rng.chance(1, 2) {
                    let name = self.name(ty, value);
                    self.fields_of(rng, name);
                }
            }
            // A constructor term of a variant ([A5]).
            9 | 10 => {
                let ctor_idx = rng.below(3) as usize;
                let fields = CONSTRUCTORS[ctor_idx].1;
                let fields = fields.iter().map(|field| self.some(rng, *field)).collect();
                self.constructor(ctor_idx, fields);
            }
            // Literals ([A3]). `[]` and `∅` are written at every type.
            11 | 12 => {
                let ty = *rng.pick(&Ty::VECTORS);
                let element = ty.element().expect("a vector");
                let items = (0..rng.below(4)).map(|_| self.some(rng, element)).collect();
                self.vector(ty, items);
            }
            13 => {
                let ty = *rng.pick(&[Ty::Table, Ty::Marks]);
                self.empty_map(ty);
            }
            14 => {
                let text = rng.pick(&["", "a", " a", "b "]).to_string();
                self.write(AtomTerm::StrLit(text), Ty::Text);
            }
            15 => {
                let of = self.any(rng, Ty::Text);
                self.write(AtomTerm::Trim(var(of)), Ty::Text);
            }
            // A write of one element ([A6]).
            16 | 17 => {
                let ty = *rng.pick(&Ty::VECTORS);
                let base = self.any(rng, ty);
                let element = self.type_of(base).element().expect("a vector");
                let index = self.some(rng, Ty::Usize);
                let value = self.some(rng, element);
                self.update(base, index, value);
            }
            // The constructor of a variant value, and at a decision the
            // names of its fields ([A5], [I11]).
            18 => {
                let of = self.any(rng, Ty::Shape);
                if rng.chance(1, 2) {
                    self.tag(of);
                }
                let value = self.value(of);
                if let (
                    true,
                    Value::Variant {
                        constructor,
                        fields,
                        ..
                    },
                ) = (Ty::Shape.holds(&value), value)
                {
                    let mut names = Vec::new();
                    for (field, ty) in fields.into_iter().zip(CONSTRUCTORS[constructor].1) {
                        names.push(var(self.name(*ty, field)));
                    }
                    self.constructor(constructor, names);
                }
            }
            // A name for the value of a term, as a bind or an assignment
            // gives one.
            _ => {
                let ty = *rng.pick(&Ty::ALL);
                let of = self.any(rng, ty);
                let value = self.value(of);
                if ty.holds(&value) {
                    self.name(ty, value);
                }
            }
        }
    }

    /// One field of a struct, or every field.
    fn fields_of(&mut self, rng: &mut Rng, base: TermId) {
        let (_, _, fields) = self.type_of(base).fields().expect("a struct");
        if rng.chance(1, 2) {
            for field_idx in 0..fields.len() {
                self.field(base, field_idx);
            }
        } else {
            self.field(base, rng.below(fields.len() as u64) as usize);
        }
    }
}

/// The part of the theory that an instance belongs to.
fn family(solver: &Solver, instance: &Instance) -> &'static str {
    match instance {
        Instance::Term(term) => match &solver.terms[*term] {
            AtomTerm::Var { .. } | AtomTerm::Field { .. } | AtomTerm::Index { .. } => "A1",
            AtomTerm::UsizeMax => "A2",
            AtomTerm::Len(_) => "A3 measure",
            AtomTerm::VecLit(_, _) => "A3 vector literal",
            AtomTerm::EmptyMap(_, _) => "A3 empty map",
            AtomTerm::VariantCtor { .. } => "A5 constructor",
            AtomTerm::VariantTag { .. } => "A5 one constructor",
            AtomTerm::Update { .. } => "A6 length and element",
            other => panic!("an instance of the term {other:?}"),
        },
        Instance::Pair(left, right) => match (&solver.terms[*left], &solver.terms[*right]) {
            (AtomTerm::StrLit(_), AtomTerm::StrLit(_)) => "A3 string literals",
            (AtomTerm::StructCtor(_, _), AtomTerm::StructCtor(_, _)) => "A4 one to one",
            (AtomTerm::Field { .. }, AtomTerm::StructCtor(_, _))
            | (AtomTerm::StructCtor(_, _), AtomTerm::Field { .. }) => "A4 field",
            (
                AtomTerm::VariantCtor { ctor_idx: left, .. },
                AtomTerm::VariantCtor {
                    ctor_idx: right, ..
                },
            ) => {
                if left == right {
                    "A5 one to one"
                } else {
                    "A5 different"
                }
            }
            _ => "S5",
        },
        Instance::Frame { .. } => "A6 frame",
        Instance::Extension { .. } => "A4 extension",
    }
}

/// Whether an instance says something of the values at hand: its condition
/// holds for them. An instance whose condition is false is true of anything.
fn applies(solver: &Solver, numbers: &BTreeMap<TermId, Int>, instance: &Instance) -> bool {
    let same = |left: &TermId, right: &TermId| numbers[left] == numbers[right];
    match instance {
        Instance::Pair(left, right) => match (&solver.terms[*left], &solver.terms[*right]) {
            // Different values, without a condition.
            (AtomTerm::StrLit(_), AtomTerm::StrLit(_)) => true,
            (
                AtomTerm::VariantCtor { ctor_idx: left, .. },
                AtomTerm::VariantCtor {
                    ctor_idx: right, ..
                },
            ) if left != right => true,
            (AtomTerm::Field { base, .. }, AtomTerm::StructCtor(_, _)) => {
                base.eval(numbers) == numbers[right]
            }
            (AtomTerm::StructCtor(_, _), AtomTerm::Field { base, .. }) => {
                base.eval(numbers) == numbers[left]
            }
            _ => same(left, right),
        },
        Instance::Extension { left, right, .. } => same(left, right),
        Instance::Frame {
            update, element, ..
        } => {
            let (AtomTerm::Update { index: i, .. }, AtomTerm::Index { index: j, .. }) =
                (&solver.terms[*update], &solver.terms[*element])
            else {
                panic!("a frame of terms that are no update and no element");
            };
            i.eval(numbers) != j.eval(numbers)
        }
        Instance::Term(term) => match &solver.terms[*term] {
            AtomTerm::Update { base, index, .. } => {
                let length = solver
                    .terms
                    .iter()
                    .position(|other| *other == AtomTerm::Len(base.clone()));
                let length = &numbers[&length.expect("the length of what is written to")];
                let at = index.eval(numbers);
                !at.is_negative() && at < *length
            }
            _ => true,
        },
    }
}

/// Section 5.2 of the fact logic: every instance of [A3] to [A6] that the
/// search makes, and the kernel grants, is true of real values. So is every
/// instance of [S5] for a field, an element, a length, a write and `trim`,
/// and of [A1] for a part of a value that a name holds.
#[test]
fn the_instances_of_the_data_axioms_hold_for_real_values() {
    let mut rng = Rng::new(0x6461_7461);
    let mut seen: BTreeMap<&str, usize> = BTreeMap::new();
    let mut applied: BTreeMap<&str, usize> = BTreeMap::new();
    for _ in 0..200 {
        let usize_max = *rng.pick(&[(1 << 32) - 1, (1 << 64) - 1]);
        let mut world = World::new(int(usize_max));
        for ty in Ty::ALL {
            let value = ty.draw(&mut rng);
            world.name(ty, value.clone());
            // Two names with one value, and a name with another.
            if ty.int().is_none() && rng.chance(1, 2) {
                world.name(ty, value);
            }
            if rng.chance(1, 2) {
                let value = ty.draw(&mut rng);
                world.name(ty, value);
            }
        }
        for _ in 0..rng.range(12, 24) {
            world.step(&mut rng);
        }
        let (numbers, failed) = world.instances(&[]);
        assert!(
            failed.is_empty(),
            "the instances {failed:?} are false for the values {:?} of the terms {:?}",
            world.values,
            world.solver.terms
        );
        for instance in &world.solver.instances {
            let family = family(&world.solver, &instance.name);
            *seen.entry(family).or_default() += 1;
            if applies(&world.solver, &numbers, &instance.name) {
                *applied.entry(family).or_default() += 1;
            }
        }
    }
    // Every part of the theory, and where an instance has a condition, with
    // the condition true.
    for family in [
        "A1",
        "A3 measure",
        "A3 vector literal",
        "A3 empty map",
        "A3 string literals",
        "A4 field",
        "A4 one to one",
        "A4 extension",
        "A5 constructor",
        "A5 one constructor",
        "A5 one to one",
        "A5 different",
        "A6 length and element",
        "A6 frame",
        "S5",
    ] {
        assert!(
            applied.get(family).copied().unwrap_or(0) >= 30,
            "{family}: seen {seen:?}, with the condition true {applied:?}"
        );
    }
}

/// The test above can fail, for every axiom: with one number that is not
/// the number of the real value, the instance of the axiom is false. Where
/// an axiom has a condition, the same number is no error when the condition
/// does not hold.
#[test]
fn a_wrong_value_makes_the_instance_of_its_axiom_false() {
    let mut world = World::new(int((1 << 32) - 1));
    let x = world.name(Ty::U8, number_value(3));
    let y = world.name(Ty::U8, number_value(4));
    let b = world.name(Ty::Bool, Value::Bool(true));
    let i = world.name(Ty::Usize, number_value(1));
    let j = world.name(Ty::Usize, number_value(2));
    let k = world.name(Ty::Usize, number_value(1));
    let far = world.name(Ty::Usize, number_value(9));
    let three_and_true = structure(PAIR, "pair", vec![number_value(3), Value::Bool(true)]);
    let p = world.name(Ty::Pair, three_and_true.clone());
    let q = world.name(Ty::Pair, three_and_true);
    let r = world.name(
        Ty::Pair,
        structure(PAIR, "pair", vec![number_value(9), Value::Bool(false)]),
    );
    let bytes = [5, 6, 7].map(number_value).to_vec();
    let v = world.name(Ty::Bytes, Value::Vector(bytes));
    let t = world.name(Ty::Shape, shape(1, vec![number_value(3)]));

    // [A3].
    let literal = world.vector(Ty::Bytes, vec![var(x), var(y)]);
    let empty = world.empty_map(Ty::Table);
    let length = world.length(v);
    let a = world.write(AtomTerm::StrLit("a".to_string()), Ty::Text);
    let other_text = world.write(AtomTerm::StrLit("b".to_string()), Ty::Text);
    // [A4]: `pair {x, b}` is the value of `p` and of `q`.
    let made = world.pair(var(x), var(b));
    let other = world.pair(var(y), var(b));
    let again = world.pair(var(x), LinearTerm::from_i128(1));
    let mut fields = Vec::new();
    for base in [p, q, r] {
        let a = world.field(base, 0).as_var().expect("a field term");
        let b = world.field(base, 1).as_var().expect("a field term");
        fields.push(vec![a, b]);
    }
    // [A5].
    let dot = world.constructor(0, Vec::new());
    let circle = world.constructor(1, vec![var(x)]);
    let wider = world.constructor(1, vec![var(y)]);
    let tag = world.tag(t);
    // [A6]: a write at `i`, a read at `j`, a read at `k`, which is `i`, and
    // a write out of range.
    let update = world.update(v, var(i), var(x));
    world.element(v, var(j));
    world.element(v, var(k));
    let lost = world.update(v, var(far), var(x));

    let (numbers, failed) = world.instances(&[]);
    assert!(failed.is_empty(), "{failed:?}");
    let element = |world: &World, base: TermId, index: TermId| {
        world.id_of(&AtomTerm::Index {
            base: var(base),
            index: var(index),
            int_ty: None,
            is_bool: false,
            is_value_term: false,
        })
    };
    let read = |world: &World, index: TermId| {
        world.id_of(&AtomTerm::Index {
            base: var(v),
            index: var(index),
            int_ty: Some(IntType::U8),
            is_bool: false,
            is_value_term: true,
        })
    };
    let length_of = |world: &World, of: TermId| world.id_of(&AtomTerm::Len(var(of)));
    let frame = |world: &World, index: TermId| Instance::Frame {
        update,
        element: element(world, update, index),
        original: read(world, index),
    };
    let extension = |left: usize, right: usize| Instance::Extension {
        structure: PAIR,
        left: [p, q, r][left],
        left_fields: fields[left].clone(),
        right: [p, q, r][right],
        right_fields: fields[right].clone(),
    };
    let pair = |left: TermId, right: TermId| Instance::Pair(left.min(right), left.max(right));
    let fresh = int(1000);
    let greatest = &numbers[&world.solver.usize_max_term];

    // What is wrong, the number that is wrong, and the instance that says so.
    let wrong: Vec<(&str, TermId, Int, Instance)> = vec![
        (
            "[A3] a literal of two elements with the length three",
            length_of(&world, literal),
            int(3),
            Instance::Term(literal),
        ),
        (
            "[A3] `∅` with an entry",
            length_of(&world, empty),
            int(1),
            Instance::Term(empty),
        ),
        (
            "[A3] a length below zero",
            length,
            int(-1),
            Instance::Term(length),
        ),
        (
            "[A3] a length above `usize.max`",
            length,
            greatest.plus(&int(1)),
            Instance::Term(length),
        ),
        (
            "[A3] two string literals that are one value",
            other_text,
            numbers[&a].clone(),
            pair(a, other_text),
        ),
        (
            "[A4] a field that is not the argument",
            fields[0][0],
            int(4),
            pair(fields[0][0], made),
        ),
        (
            "[A4] constructor terms with different arguments that are one value",
            other,
            numbers[&made].clone(),
            pair(made, other),
        ),
        (
            "[A4] constructor terms with equal arguments that are two values",
            again,
            fresh.clone(),
            pair(made, again),
        ),
        (
            "[A4] two values with equal fields",
            q,
            fresh.clone(),
            extension(0, 1),
        ),
        (
            "[A5] a constructor term that is of another constructor",
            world.id_of(&AtomTerm::VariantTag {
                base: var(circle),
                variant_id: SHAPE,
                num_ctors: 3,
            }),
            int(2),
            Instance::Term(circle),
        ),
        (
            "[A5] terms of two constructors that are one value",
            dot,
            numbers[&circle].clone(),
            pair(dot, circle),
        ),
        (
            "[A5] terms of one constructor with different arguments that are one value",
            wider,
            numbers[&circle].clone(),
            pair(circle, wider),
        ),
        (
            "[A5] a value of no constructor",
            tag,
            int(3),
            Instance::Term(tag),
        ),
        (
            "[A6] a write that changes the length",
            length_of(&world, update),
            int(4),
            Instance::Term(update),
        ),
        (
            "[A6] a written element that is not what was written",
            element(&world, update, i),
            int(4),
            Instance::Term(update),
        ),
        (
            "[A6] a write that changes another element",
            element(&world, update, j),
            int(9),
            frame(&world, j),
        ),
    ];
    for (what, term, number, instance) in wrong {
        assert_ne!(numbers[&term], number, "{what}: the number is the real one");
        let (_, failed) = world.instances(&[(term, number)]);
        assert!(
            failed.contains(&instance),
            "{what}: the instance {instance} holds, and {failed:?} do not"
        );
    }

    // The same numbers where the condition of the instance does not hold.
    let free: Vec<(&str, TermId, Int, Instance)> = vec![
        (
            "[A4] a field of a value that is not the constructor term",
            fields[2][0],
            int(4),
            pair(fields[2][0], made),
        ),
        (
            "[A4] two values with different fields",
            r,
            fresh.clone(),
            extension(0, 2),
        ),
        (
            "[A6] the element of a write out of range",
            element(&world, lost, far),
            int(4),
            Instance::Term(lost),
        ),
        (
            "[A6] the element at the index of the write",
            element(&world, update, k),
            int(9),
            frame(&world, k),
        ),
    ];
    for (what, term, number, instance) in free {
        assert_ne!(numbers[&term], number, "{what}: the number is the real one");
        let (_, failed) = world.instances(&[(term, number)]);
        assert!(
            world
                .solver
                .instances
                .iter()
                .any(|made| made.name == instance),
            "{what}: there is no instance {instance}"
        );
        assert!(
            !failed.contains(&instance),
            "{what}: the instance {instance} does not hold"
        );
    }
}

/// A literal is a term of its type. `[]` at two types is two terms, and so
/// is `∅`; `[1, 0]` is another term than `[true, false]`, though both are
/// written with the numbers one and zero. With one term for both, a value of
/// one type would be equal to a value of another.
#[test]
fn a_literal_at_two_types_is_two_terms() {
    let mut world = World::new(int((1 << 32) - 1));
    let i = world.name(Ty::Usize, number_value(0));
    let numbers = vec![LinearTerm::from_i128(1), LinearTerm::from_i128(0)];
    let bytes = world.vector(Ty::Bytes, numbers.clone());
    let flags = world.vector(Ty::Flags, numbers);
    assert_ne!(bytes, flags);
    let mut empty = Vec::new();
    for ty in Ty::VECTORS {
        let literal = world.vector(ty, Vec::new());
        world.element(literal, var(i));
        empty.push(literal);
    }
    empty.push(world.empty_map(Ty::Table));
    empty.push(world.empty_map(Ty::Marks));
    world.element(bytes, var(i));
    world.element(flags, var(i));
    let (numbers, failed) = world.instances(&[]);
    assert!(failed.is_empty(), "{failed:?}");
    // The elements out of range are the values of their types, and those
    // of a struct, a variant and a vector are no number of a `u8`.
    empty.sort();
    empty.dedup();
    assert_eq!(empty.len(), Ty::VECTORS.len() + 2);
    let mut values: Vec<&Int> = empty.iter().map(|literal| &numbers[literal]).collect();
    values.sort();
    values.dedup();
    assert_eq!(values.len(), empty.len(), "a value of two types");
}
