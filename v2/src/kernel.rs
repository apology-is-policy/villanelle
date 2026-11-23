//! The independent certificate kernel (`docs/v2/facts.md`, section 8,
//! `[V1]` to `[V4]`).
//!
//! The compiler accepts an entailment only after [`validate`] checks its
//! [`Certificate`]. This module shares no search code with [`crate::facts`]:
//! it checks that every [`ProofStep`] in every [`TheoryLemma`] is sound by
//! exact integer arithmetic and that the conjunction of the query, the axiom
//! instances and the lemmas reduces to `FALSE` in the binary decision diagram.

use crate::bdd;
use crate::facts::Certificate;
use crate::int::Int;
use crate::terms::{End, Proof, Row, Step, TheoryLemma};
use std::collections::BTreeMap;

/// The row that holds exactly when `row` does not, over the integers.
fn complement(row: &Row) -> Row {
    Row {
        coeffs: row
            .coeffs
            .iter()
            .map(|(term, coeff)| (*term, coeff.negate()))
            .collect(),
        rhs: row.rhs.negate().minus(&Int::from_u64(1)),
    }
}

/// `⌊a / d⌋` for `d ≥ 1`.
fn floor(a: &Int, d: &Int) -> Int {
    let (quotient, remainder) = a.divide(d).expect("the divisor is positive");
    if a.is_negative() && !remainder.is_zero() {
        quotient.minus(&Int::from_u64(1))
    } else {
        quotient
    }
}

/// The row that a step derives from the rows of its path.
fn derive(
    step: &Step,
    literals: &[(usize, bool)],
    atoms: &[Row],
    path: &[Row],
) -> Result<Row, String> {
    match step {
        Step::Literal(index) => {
            let Some(&(atom, positive)) = literals.get(*index) else {
                return Err(format!("the lemma has no literal {index}"));
            };
            let Some(row) = atoms.get(atom) else {
                return Err(format!("there is no theory atom {atom}"));
            };
            Ok(if positive {
                row.clone()
            } else {
                complement(row)
            })
        }
        Step::Combine(parts) => {
            if parts.is_empty() {
                return Err("a sum of no rows".to_string());
            }
            let mut coeffs: BTreeMap<usize, Int> = BTreeMap::new();
            let mut rhs = Int::zero();
            for (source, multiplier) in parts {
                let Some(row) = path.get(*source) else {
                    return Err(format!("row {source} is not on the path"));
                };
                if multiplier.is_negative() || multiplier.is_zero() {
                    return Err(format!("the multiplier {multiplier} is not positive"));
                }
                for (term, coeff) in &row.coeffs {
                    let sum = coeffs
                        .get(term)
                        .cloned()
                        .unwrap_or_default()
                        .plus(&coeff.times(multiplier));
                    if sum.is_zero() {
                        coeffs.remove(term);
                    } else {
                        coeffs.insert(*term, sum);
                    }
                }
                rhs = rhs.plus(&row.rhs.times(multiplier));
            }
            Ok(Row { coeffs, rhs })
        }
        Step::Round { source, divisor } => {
            let Some(row) = path.get(*source) else {
                return Err(format!("row {source} is not on the path"));
            };
            if *divisor < Int::from_u64(1) {
                return Err(format!("the divisor {divisor} is not positive"));
            }
            let mut coeffs = BTreeMap::new();
            for (term, coeff) in &row.coeffs {
                let (quotient, remainder) = coeff.divide(divisor).expect("a positive divisor");
                if !remainder.is_zero() {
                    return Err(format!(
                        "the divisor {divisor} does not divide the coefficient {coeff}"
                    ));
                }
                coeffs.insert(*term, quotient);
            }
            Ok(Row {
                coeffs,
                rhs: floor(&row.rhs, divisor),
            })
        }
    }
}

/// Validates one branch of a proof, and the branches below it. `path` holds
/// the rows of the branches above.
fn branch(
    proof: &Proof,
    literals: &[(usize, bool)],
    atoms: &[Row],
    path: &mut Vec<Row>,
) -> Result<(), String> {
    let base = path.len();
    for (index, step) in proof.steps.iter().enumerate() {
        let row = derive(step, literals, atoms, path)
            .map_err(|error| format!("row {}: {error}", base + index))?;
        path.push(row);
    }
    match &proof.end {
        End::Close(row) => {
            let Some(row) = path.get(*row) else {
                return Err(format!("the closing row {row} is not on the path"));
            };
            if !row.coeffs.is_empty() || !row.rhs.is_negative() {
                return Err("the closing row is not `0 ≤ b` with `b < 0`".to_string());
            }
        }
        End::Split {
            form,
            bound,
            low,
            high,
        } => {
            if form.values().any(Int::is_zero) {
                return Err("a split on a term with the coefficient 0".to_string());
            }
            // `form ≤ bound`, and then `form ≥ bound + 1`: every integer
            // value of the form is in one of the two.
            let split = path.len();
            let at_most = Row {
                coeffs: form.clone(),
                rhs: bound.clone(),
            };
            let above = complement(&at_most);
            path.push(at_most);
            branch(low, literals, atoms, path)?;
            path.truncate(split);
            path.push(above);
            branch(high, literals, atoms, path)?;
        }
    }
    path.truncate(base);
    Ok(())
}

/// Validates the proof of a [`TheoryLemma`] against the atoms that its
/// literals name ([V3]): every branch of the tree ends in a contradiction.
pub fn validate_lemma(lemma: &TheoryLemma, theory_atoms: &[Row]) -> Result<(), String> {
    branch(&lemma.proof, &lemma.literals, theory_atoms, &mut Vec::new())
}

/// Validates a complete [`Certificate`] ([V1] to [V4]).
pub fn validate(certificate: &Certificate) -> Result<(), String> {
    const VALID_CLAUSES: [&str; 10] = ["A1", "A2", "A3", "A4", "A5", "A6", "A7", "A8", "A9", "I10"];
    for instance in &certificate.instances {
        if !VALID_CLAUSES.contains(&instance.clause) {
            return Err(format!(
                "`{}` is not a recognized axiom clause",
                instance.clause
            ));
        }
    }

    for (index, lemma) in certificate.lemmas.iter().enumerate() {
        validate_lemma(lemma, &certificate.theory_atoms)
            .map_err(|err| format!("lemma {index}: {err}"))?;
    }

    // [V2]: Recompute the Boolean step: the conjunction of the query, the
    // instances and the negated lemmas must be FALSE.
    let mut bdd = certificate.bdd.clone();
    let mut total = certificate.query;
    for instance in &certificate.instances {
        total = bdd.and(total, instance.formula);
    }
    for lemma in &certificate.lemmas {
        let mut conj = bdd::TRUE;
        for &(atom_id, polarity) in &lemma.literals {
            let lit = bdd.literal(certificate.first_theory_var + atom_id, polarity);
            conj = bdd.and(conj, lit);
        }
        let not_conj = bdd.not(conj);
        total = bdd.and(total, not_conj);
    }
    if total != bdd::FALSE {
        return Err("the conjunction of the query, instances and lemmas is not FALSE".to_string());
    }
    Ok(())
}
