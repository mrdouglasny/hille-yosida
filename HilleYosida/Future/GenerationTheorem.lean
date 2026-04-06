/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license.

# Hille-Yosida Generation Theorem (Converse Direction) — Axioms

This file states the converse direction of the Hille-Yosida theorem as axioms.
The forward direction (semigroup → resolvent bound) is fully proved in
`StronglyContinuousSemigroup.lean`. The converse (operator → semigroup) requires
the Yosida approximation and is stated here for use by downstream projects.

## Mathematical Content

**Generation Theorem** ([EN] Thm. II.3.8, Feller-Miyadera-Phillips 1952).
A linear operator `(A, D(A))` generates a C₀-semigroup `{T(t)}` with
`‖T(t)‖ ≤ M e^{ωt}` if and only if:
(a) `A` is closed and `D(A)` is dense in `X`,
(b) every `λ > ω` is in the resolvent set `ρ(A)`, and
    `‖[(λ - ω) R(λ, A)]^n‖ ≤ M` for all `n ∈ ℕ`.

For **contraction semigroups** (`M = 1, ω = 0`), this simplifies to the
classical Hille-Yosida theorem ([EN] Cor. 3.6):
(a) `A` is closed and `D(A)` is dense,
(b) `(0, ∞) ⊂ ρ(A)` and `‖R(λ, A)‖ ≤ 1/λ` for all `λ > 0`.

An equivalent characterization uses **dissipative operators** ([EN] Def. 3.13):
`A` is dissipative iff `‖(λ - A)x‖ ≥ λ ‖x‖` for all `λ > 0, x ∈ D(A)`.
The Lumer-Phillips theorem ([EN] Thm. 3.15) states: a dissipative operator `A`
generates a contraction semigroup iff `rg(λ₀ - A) = X` for some `λ₀ > 0`.

## References

* [EN] Engel-Nagel, Ch. II §3: Generation Theorems (pp. 70–95)
* [Linares] Theorem 6 (Hille-Yosida, both directions)
-/

import HilleYosida.StronglyContinuousSemigroup

noncomputable section

open scoped Topology NNReal

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]

/-! ## Generator Properties

These properties of the generator are proved in [EN] Thm. II.1.4. They should
eventually be theorems; stated as axioms until the proofs are formalized. -/

/-- The generator domain `D(A)` is dense in `X`.
([EN] Thm. II.1.4). The proof uses the "smoothed" elements
`xₜ = (1/t) ∫₀ᵗ T(s)x ds ∈ D(A)` which converge to `x` as `t → 0`. -/
-- Stated as axiom in earlier versions; commented out pending formalization.
-- axiom StronglyContinuousSemigroup.domain_isDense
--     (S : StronglyContinuousSemigroup X) :
--     Dense (S.domain : Set X)
example : True := trivial -- placeholder

/-! ## Hille-Yosida Generation Theorem (Contraction Case)

The converse direction: an operator satisfying the resolvent bound generates
a contraction semigroup. The proof constructs the semigroup via the
**Yosida approximation** `Aλ = λ² R(λ, A) - λI`
([EN] eq. (3.7), [Linares] eq. 0.19). -/

/-- A densely defined linear operator `A` on a Banach space `X`. -/
structure DenseLinearOperator (X : Type*) [NormedAddCommGroup X]
    [NormedSpace ℝ X] where
  /-- The domain of `A`, a submodule of `X`. -/
  domain : Submodule ℝ X
  /-- The operator `A : D(A) → X`. -/
  op : domain →ₗ[ℝ] X
  /-- `D(A)` is dense in `X`. -/
  dense : Dense (domain : Set X)

/-- A densely defined operator is **dissipative** if `‖(λI - A)x‖ ≥ λ ‖x‖`
for all `λ > 0` and `x ∈ D(A)` ([EN] Def. II.3.13). Equivalently,
`Re ⟨Ax, x⟩ ≤ 0` for all `x ∈ D(A)` on Hilbert spaces. -/
def DenseLinearOperator.IsDissipative (A : DenseLinearOperator X) : Prop :=
  ∀ (lambda : ℝ), 0 < lambda → ∀ (x : A.domain),
    lambda * ‖(x : X)‖ ≤ ‖lambda • (x : X) - A.op x‖

/-- **Hille-Yosida generation theorem** (contraction case, converse direction).

A densely defined, dissipative operator `A` with `rg(λ₀ - A) = X`
for some `λ₀ > 0` generates a contraction semigroup.

This is the Lumer-Phillips theorem ([EN] Thm. II.3.15), equivalent to the
classical Hille-Yosida characterization for contractions ([EN] Cor. II.3.6).

The proof constructs the semigroup via the Yosida approximation
`Aλ = λ² R(λ, A) - λI`, shows `e^{tAλ}` converges strongly as `λ → ∞`,
and verifies the semigroup properties of the limit.

Note: The dissipativity condition `‖(λ - A)x‖ ≥ λ‖x‖` implies that
`A` is closable, and its closure generates the semigroup. We state the
conclusion for the closure.

Ref: [EN] Thm. II.3.5, Cor. II.3.6, Thm. II.3.15; [Linares] Thm. 6. -/
-- Stated as axiom in earlier versions; commented out pending formalization.
-- axiom hilleYosidaGeneration
--     (A : DenseLinearOperator X)
--     (hdiss : A.IsDissipative)
--     (hsurj : ∃ (lambda₀ : ℝ), 0 < lambda₀ ∧
--       ∀ (y : X), ∃ (x : A.domain), lambda₀ • (x : X) - A.op x = y) :
--     ∃ (S : ContractingSemigroup X),
--       (∀ (x : A.domain), (x : X) ∈ S.toStronglyContinuousSemigroup.domain) ∧
--       (∀ (x : A.domain) (hx : (x : X) ∈ S.toStronglyContinuousSemigroup.domain),
--         S.toStronglyContinuousSemigroup.generatorMap ⟨x, hx⟩ = A.op x)

end
