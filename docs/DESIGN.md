# Design records — hille-yosida

Settled design choices for this development, in the design-record format of
[`math-commons/formalization-assurance`](https://github.com/math-commons/formalization-assurance)
(`DESIGN_RECORDS.md`): context → decision → alternatives → consequences → bridging. Each
records *why* an object is encoded as it is, so the choice is not rediscovered or silently
reversed (notably during the Tau Ceti port; see the bridging notes).

Index:
1. [Generator as `Submodule` + `LinearMap`](#1-generator-encoding)
2. [Time is total `ℝ`, guarded by `t ≥ 0`](#2-time-parameter)
3. [Contraction-first resolvent](#3-resolvent-generality)
4. [Pointwise `X`-valued resolvent integral](#4-resolvent-integral)
5. [BCR Laplace–Fourier representation](#5-bcr-encoding)

---

## 1. Generator encoding

- **Status:** accepted (this repo); **superseded in the Mathlib-facing port** by a `LinearPMap`.
- **Date:** 2026-06-21
- **Affects:** `StronglyContinuousSemigroup.{generator, domain, generatorMap}`.

**Context.** The generator `A` of a C₀-semigroup is an unbounded operator with a dense domain
`D(A) ⊆ X`; it must be modelled as a partial linear operator.

**Decision.** Model it as two pieces: a `domain : Submodule ℝ X` (the predicate "the
difference quotient converges") and `generatorMap : domain →ₗ[ℝ] X` (the limit value).

**Alternatives.** Mathlib's `LinearPMap` (`X →ₗ.[ℝ] X`) bundles exactly a domain submodule + a
linear map on it.

| | this repo | `LinearPMap` |
|---|---|---|
| Object | `domain` + `generatorMap` (two decls) | one `X →ₗ.[ℝ] X` |
| Mathlib unbounded-operator API (graph, closure, adjoint) | not directly | composes for free |

**Consequences.** The two-piece form is simple and direct for the resolvent identities proved
here, but it is a parallel API for something Mathlib already provides.

**Bridging.** The Tau Ceti port (`FormalFrontier/TauCeti`, `Analysis/Semigroups/Basic.lean`)
re-encodes the generator as a `LinearPMap` with `domain := S.domain` and `generatorMap` as the
underlying map, on review feedback — the canonical form for downstream resolvent-set / closure
work. Prefer `LinearPMap` for any Mathlib-facing reuse.

## 2. Time parameter

- **Status:** accepted
- **Date:** 2026-06-21
- **Affects:** `StronglyContinuousSemigroup.operator` and every law/lemma over `t`.

**Context.** A C₀-semigroup is a family `(S t)_{t ≥ 0}`; Lean needs a concrete index type.

**Decision.** `operator : ℝ → X →L[ℝ] X` is **total on `ℝ`**, with the semigroup law, `S 0 = id`,
strong continuity, and bounds all **quantified over `t ≥ 0`**. Values `S t` for `t < 0` are
unconstrained and carry no information.

**Alternatives.** Index by `ℝ≥0` (or a `Set.Ici 0` subtype) so non-negative time is intrinsic.

**Consequences.** Buys: `t` is a plain real, so the analytic lemmas (Bochner integrals over
`Set.Ioi 0`, the FTC, `Real.exp`) need no `ℝ≥0 → ℝ` coercion on every step. Costs: two
extensionally-equal semigroups on `[0,∞)` can differ on `t < 0` junk, so equality of
`operator` is finer than equality on the half-line. No stated result is affected (all assume
`t ≥ 0`). The `ℝ≥0` alternative makes that extensional equality automatic at the coercion cost.

## 3. Resolvent generality

- **Status:** accepted (this repo: contraction-first); **generalized in the port**.
- **Date:** 2026-06-21
- **Affects:** `ContractingSemigroup.resolvent`, `hilleYosidaResolventBound`, `resolventRightInv`.

**Context.** The Laplace-transform resolvent `R λ = ∫₀^∞ e^{-λt} S t dt` converges for `λ`
beyond the semigroup's growth bound `ω`.

**Decision.** Define it here on the **contraction** subclass (`‖S t‖ ≤ 1`, `λ > 0`, bound
`‖R λ‖ ≤ 1/λ`) — the case needed for the Hille–Yosida headline.

**Alternatives.** State it for a general C₀-semigroup with growth bound `(ω, M)` and `λ > ω`,
bound `‖R λ‖ ≤ M/(λ-ω)`, with contraction as the corollary.

**Consequences.** Contraction-first is the shortest path to the named theorem, but specializes
the resolvent API.

**Bridging.** The port lifts the whole resolvent stack to the general `(ω, M)` level (the
roadmap's generality bar), with contraction as the `M=1, ω=0` corollary. The proofs are the
same modulo the growth-bound estimate replacing `‖S t‖ ≤ 1`.

## 4. Resolvent integral

- **Status:** accepted
- **Date:** 2026-06-21
- **Affects:** `ContractingSemigroup.resolvent`.

**Context.** `R λ x = ∫₀^∞ e^{-λt} S t x dt` needs a Bochner integral.

**Decision.** Define it **pointwise in `x`** (`x ↦ ∫ e^{-λt} S t x dt`), then bundle into a
`ContinuousLinearMap` via `LinearMap.mkContinuous`.

**Alternatives.** An operator-valued integral `∫ e^{-λt} S t dt` directly in `X →L[ℝ] X`.

**Consequences.** The operator-valued form fails: a general C₀-semigroup is only *strongly*
continuous, so `t ↦ S t` is not strongly measurable into the (generally non-separable)
`X →L[ℝ] X`, and its Bochner integral is unavailable. The pointwise map `t ↦ S t x` *is*
strongly measurable, so the pointwise integral is well-defined; bundling recovers the operator.

## 5. BCR encoding

- **Status:** accepted
- **Date:** 2026-06-21
- **Affects:** `IsSemigroupGroupPD`, `semigroupGroupBochner`, `laplaceFourier_unique`.

**Context.** The Berg–Christensen–Ressel representation (Thm 4.1.13) for bounded continuous
positive-definite functions on the involutive semigroup `[0,∞) × ℝᵈ`.

**Decision.** Kernel is **Laplace in time, Fourier in space** (`e^{-tp} · e^{i⟨a,q⟩}`); support
on `[0,∞)×ℝᵈ` is encoded as `μ (Set.Iio 0 ×ˢ Set.univ) = 0`; the spatial dimension is `Fin d`;
**existence** (`semigroupGroupBochner`) and **uniqueness** (`laplaceFourier_unique`) are
separate theorems.

**Alternatives.** A general finite-dimensional inner-product space `V` instead of `Fin d`
coordinates; a `Measure ℝ≥0` (or subtype) instead of the `μ(Iio 0 …)=0` side condition.

**Consequences.** `Fin d` + the side-condition encoding matched the available infrastructure
and the BCR existence proof's dependency on a separate Bochner–Minlos package. Costs: a user
with `ℝ²` as `ℝ × ℝ`, a torus, etc. cannot apply it directly.

**Bridging.** The roadmap targets the general inner-product-space `V` form (with `ℝ≥0` time);
the Tau Ceti port will state it there, with `Fin d` as a corollary.
