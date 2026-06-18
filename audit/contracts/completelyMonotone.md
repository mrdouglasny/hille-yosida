---
object: IsCompletelyMonotone (and bernstein_theorem)
informal: >
  A function f : ℝ → ℝ is completely monotone on (0,∞) when (−1)ⁿ f⁽ⁿ⁾ ≥ 0 for all n.
  Bernstein's theorem: every completely monotone f is the Laplace transform of a unique
  finite positive measure supported on [0,∞).
sources:
  - "Widder, The Laplace Transform (Princeton, 1941), Ch. IV — Bernstein's theorem"
lean:
  name: IsCompletelyMonotone
  signature: "(f : ℝ → ℝ) : Prop   -- (−1)ⁿ · iterated derivative of f ≥ 0 on (0,∞)"
  body: "∀ n, ∀ x > 0, 0 ≤ (-1)^n * (iteratedDeriv n f x)"
characterization:
  - id: C1-representation
    claim: "Completely monotone ⇒ f t = ∫ e^{−t x} dμ for a finite positive measure μ on [0,∞)."
  - id: C2-uniqueness
    anti_degeneracy: true
    claim: >
      The representing measure is UNIQUE and FINITE and supported on [0,∞). A "Bernstein"
      yielding a non-unique, signed, or non-finite measure is the wrong theorem — uniqueness
      is what makes the Laplace representation a bijection onto completely monotone functions.
known_values:
  - instance: "f completely monotone (existence)"
    expected: "∃ finite μ on [0,∞), f t = ∫ e^{−tx} dμ"
    theorem: bernstein_theorem
    status: PROVEN_CORE_AXIOMS
    note: "status from #print axioms (audit/axiom_report.lean); standard three"
  - instance: "representing measure (uniqueness)"
    expected: "two finite measures with equal Laplace transforms are equal"
    theorem: laplace_measure_unique
    status: PROVEN_CORE_AXIOMS
    note: "Laplace-transform injectivity — the uniqueness half"
  - instance: "Taylor remainder of f (the analytic engine)"
    expected: "integral remainder identity"
    theorem: taylor_integral_remainder
    status: PROVEN_CORE_AXIOMS
    note: "BernsteinBasic; sorry-free per the file header"
  - instance: "f t = e^{−a t} (a ≥ 0)"
    expected: "completely monotone; representing measure δ_a"
    theorem: "(acceptance check; see VALIDATION.md)"
    status: PROVEN_CORE_AXIOMS
    note: "non-vacuity exemplar"
well_definedness: >
  Complete monotonicity is stated via `iteratedDeriv` on `(0,∞)`; the representing measure is
  extracted via the Chafái change-of-variables + Prokhorov tightness (`BernsteinChafai`).
anti_degeneracy:
  history: >
    Dropping uniqueness or finiteness gives a strictly weaker (and false-as-stated) "Bernstein";
    the Laplace map would no longer be injective on completely monotone functions.
  current_guard: "bernstein_theorem proves existence of a finite measure on [0,∞); laplace_measure_unique proves uniqueness."
status: "All rows PROVEN_CORE_AXIOMS (axiom-free); confirm via the generated audit/axiom-report.txt."
---

# Contract — `IsCompletelyMonotone` / `bernstein_theorem`

Completely monotone functions and their Laplace representation. Anti-degeneracy clause **C2**
(uniqueness + finiteness of the representing measure) is what makes Bernstein a genuine
bijection, not a one-way existence claim. The `known_values` rows are checkable without
reading the proofs.
