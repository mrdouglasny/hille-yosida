---
object: ContractingSemigroup.resolvent
informal: >
  The resolvent of a contraction C₀-semigroup at λ > 0: R(λ) = ∫₀^∞ e^{−λt} S(t) dt, a
  bounded operator that inverts (λ − A) on the generator's domain and satisfies the
  Hille–Yosida bound ‖R(λ)‖ ≤ 1/λ.
sources:
  - "Engel & Nagel, One-Parameter Semigroups for Linear Evolution Equations (GTM 194, 2000) — Hille–Yosida"
lean:
  name: ContractingSemigroup.resolvent
  signature: "(S : ContractingSemigroup X) (l : ℝ) : X →L[ℝ] X   -- for 0 < l"
  body: "the Bochner integral ∫₀^∞ e^{−l t} S(t) x dt"
characterization:
  - id: C1-right-inverse
    anti_degeneracy: true
    claim: >
      R(λ) inverts the generator: (λ − A) R(λ) = I on the domain. THIS is what makes it the
      resolvent, not merely a bounded operator — a "resolvent" that doesn't satisfy this is the
      wrong object.
  - id: C2-bound
    claim: "‖R(λ)‖ ≤ 1/λ (the Hille–Yosida contraction-scale bound)."
  - id: C3-maps-to-domain
    claim: "R(λ) maps X into the generator's domain D(A)."
known_values:
  - instance: "(λ − A) R(λ)"
    expected: "I (on the domain)"
    theorem: ContractingSemigroup.resolventRightInv
    status: PROVEN_CORE_AXIOMS
    note: "status from #print axioms (audit/axiom_report.lean); standard three"
  - instance: "‖R(λ)‖"
    expected: "≤ 1/λ"
    theorem: hilleYosidaResolventBound
    status: PROVEN_CORE_AXIOMS
  - instance: "range of R(λ)"
    expected: "⊆ D(A)"
    theorem: ContractingSemigroup.resolventMapsToDomain
    status: PROVEN_CORE_AXIOMS
well_definedness: >
  The integrand `t ↦ e^{−λt} S(t) x` is Bochner-integrable on `[0,∞)` for a contraction
  semigroup (`integrable_resolvent_integrand`); λ > 0 is required for convergence.
anti_degeneracy:
  history: >
    The wrong object is "some bounded operator of norm ≤ 1/λ"; without the inversion identity
    it is not the resolvent and the Hille–Yosida theory collapses.
  current_guard: "resolventRightInv pins (λ−A)R(λ)=I; resolventMapsToDomain pins the range."
status: "All rows PROVEN_CORE_AXIOMS (axiom-free); confirm via the generated audit/axiom-report.txt."
---

# Contract — `ContractingSemigroup.resolvent`

The Hille–Yosida resolvent. Anti-degeneracy clause **C1** (it *inverts* `(λ−A)`, witnessed by
`resolventRightInv`) is the whole point: a bounded operator with the right norm is not the
resolvent unless it inverts the generator. Check the `known_values` rows without reading proofs.
