# Roadmap: one-parameter semigroups, completely monotone functions, and BCR Bochner

Operator semigroups are the analytic backbone of evolution equations (heat, Fokker–Planck,
Schrödinger) and of Markov-process theory. Mathlib has the *static* functional-analysis
stack — Banach/Hilbert spaces, bounded operators, spectrum, the holomorphic functional
calculus, the Bochner integral, Fourier theory, unbounded operators via `LinearPMap` — but
**not the dynamical layer**: strongly continuous (C₀) semigroups, their generators and
resolvents, the **Hille–Yosida** generation theorem, **Bernstein's theorem** on completely
monotone functions, or the **Berg–Christensen–Ressel (BCR)** Bochner theorem for
positive-definite functions on involutive semigroups.

The bar for "done": a researcher in evolution equations or Markov semigroups looks at this
material and says *"the C₀-semigroup / generator / resolvent API is here, in reusable form,
and the Hille–Yosida and Bochner-type representation theorems are available."*

Suggested home: `TauCeti/Analysis/Semigroups/` (the C₀ API, resolvent, generation),
`TauCeti/Analysis/CompletelyMonotone/` (Bernstein), `TauCeti/Analysis/BCR/` (the
Bochner-type representations).

## The end goal (v1)

The three pillars, each a standalone, reusable theorem (stated in `Targets.lean` with
`sorry`/`def_wanted` as the supporting types land).

```lean
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]

-- 1. Hille–Yosida resolvent: for a contraction C₀-semigroup, R λ = ∫₀^∞ e^{-λt} S t dt
--    inverts (λ − A) on the domain, with the contraction-scale bound.
-- theorem resolvent_right_inverse (S : ContractionC0Semigroup X) {l : ℝ} (hl : 0 < l) :
--     (l • 1 − S.generator) ∘L S.resolvent l = 1
-- theorem resolvent_norm_le (S : ContractionC0Semigroup X) {l : ℝ} (hl : 0 < l) :
--     ‖S.resolvent l‖ ≤ 1 / l

-- 2. Hille–Yosida generation (converse / Lumer–Phillips): densely-defined dissipative +
--    a range condition ⇒ generates a contraction C₀-semigroup.
-- theorem generates_of_dissipative (A : DenseLinearOperator X)
--     (hd : A.IsDissipative) (hr : ∀ l > 0, Surjective (l • 1 − A)) :
--     ∃ S : ContractionC0Semigroup X, S.generator = A

-- 3a. Bernstein: a completely monotone function on [0,∞) is the Laplace transform of a
--     unique finite positive measure.
-- theorem bernstein (f : ℝ → ℝ) (hcm : IsCompletelyMonotone f) :
--     ∃! μ : Measure ℝ, IsFiniteMeasure μ ∧ μ.support ⊆ Ici 0 ∧
--       ∀ t ≥ 0, f t = ∫ x, Real.exp (-t * x) ∂μ

-- 3b. BCR Bochner (Berg–Christensen–Ressel 4.1.13): a bounded continuous positive-definite
--     function on [0,∞) × ℝᵈ is the Laplace–Fourier transform of a unique finite measure.
-- theorem bcr_semigroup_bochner (d : ℕ) (F : ℝ × EuclideanSpace ℝ (Fin d) → ℂ)
--     (hpd : IsSemigroupGroupPD d F) :
--     ∃! μ : Measure (ℝ × EuclideanSpace ℝ (Fin d)), IsFiniteMeasure μ ∧ … ∧
--       ∀ t ≥ 0, ∀ a, F (t, a) = ∫ (p, q), Real.exp (-t * p) * Complex.exp (I * ⟪a, q⟫) ∂μ
```

## Standing hypotheses (spell them out; never bundle)

- **Contraction vs general C₀.** State the resolvent identities for **contraction**
  semigroups (`‖S t‖ ≤ 1`); the general bounded case (`‖S t‖ ≤ M e^{ωt}`) is a later
  generalization via rescaling — carry `M, ω` explicitly, never assume contraction silently.
- **Unbounded generator.** The generator has a **dense domain**; track it as a genuine
  `LinearPMap` / submodule, never a total operator. ⚠ Do not conflate the operator with its
  closure's domain.
- **Completely monotone** means `(−1)ⁿ f⁽ⁿ⁾ ≥ 0` for all `n` on `(0,∞)`; keep the endpoint
  and finiteness hypotheses explicit (the representing measure is finite, supported on
  `[0,∞)`).
- **Positive-definite on a semigroup-with-involution.** State the BCR hypothesis as a named
  predicate (`IsSemigroupGroupPD`), not bundled into the conclusion; fix the involution
  (`(t,a) ↦ (t,−a)`) and the `[0,∞) × ℝᵈ` structure up front.

## What Mathlib already has (consume)

- **Operators & spectrum:** `ContinuousLinearMap`, operator norm, `spectrum`, the
  holomorphic functional calculus; **unbounded operators** via `LinearPMap` (closure,
  adjoint, cores) — the generator and its domain live here.
- **The Bochner integral** (`Mathlib/MeasureTheory/Integral/Bochner/*`): the resolvent
  `∫₀^∞ e^{−λt} S t dt` is a Bochner integral of an operator-valued map; dominated
  convergence, Fubini, the `integral_comp_add_right`/`Ioi` lemmas.
- **Fourier analysis** (`Mathlib/Analysis/Fourier/*`): `FourierTransform`, inversion,
  Plancherel, and characteristic-function uniqueness of finite measures — the spatial half
  of BCR uniqueness.
- **Laplace transforms / `Real.exp`**, the `Measure`/`IsFiniteMeasure` API, and **Prokhorov
  tightness** for the measure-extraction in Bernstein.
- **Completely monotone scaffolding:** Taylor's theorem with integral remainder, monotone
  convergence, `deriv`/iterated derivatives.

## What is missing (build here)

C₀-semigroups, their generators/resolvents, the Hille–Yosida resolvent identities and the
generation theorem, Bernstein's theorem, and the BCR semigroup-Bochner theorem. **None of
this is upstream** (Mathlib has the static stack but no operator-semigroup theory).

## Migration source (existing AI-authored material)

Most of this exists, **sorry-free and with 0 project axioms**, in
[`mrdouglasny/hille-yosida`](https://github.com/mrdouglasny/hille-yosida), pinned at commit
`8fda1863eea60068e32f7ea6c0c27da5dd650957`. A v4.29→v4.31 toolchain bump is prepared on its
`bump/v4.31` branch (the resolvent module compiles clean on Mathlib v4.31 with no code
changes). Credit that source (and the BCR theorem to Berg–Christensen–Ressel) in each ported
file.

⚠ **Bochner-dependency split.** Two files of the source — `BCR_Common.lean`,
`BCR_Existence.lean` — depend on a separate Bochner–Minlos package, so **Layers 0–3 below
are cleanly Mathlib-only**, and the BCR *existence* half (Layer 4) needs a Mathlib-only route
to the spatial Bochner theorem before it can be ported. Port in layer order.

Per-file decls to migrate (in order within each file):
- `StronglyContinuousSemigroup.lean` → `StronglyContinuousSemigroup`, `ContractingSemigroup`,
  `.generator`, `.domain`, `.resolvent`, `resolventMapsToDomain`, `resolventRightInv`,
  `hilleYosidaResolventBound`, `HasGrowthBound`, `existsGrowthBound`.
- `BernsteinBasic.lean` → `IsCompletelyMonotone`, `taylor_integral_remainder`; then
  `BernsteinMeasures.lean`, `BernsteinChafai.lean`, then `Bernstein.lean` → `bernstein_theorem`.
- `FourierPD.lean` → `pd_quadratic_form_of_measure`; `BCR_d0.lean` → `semigroup_pd_laplace`;
  `SemigroupGroupDefs.lean` → `IsSemigroupGroupPD`; `BCR_General.lean` →
  `laplaceFourier_unique` (Mathlib-only) and `semigroupGroupBochner_proof` (needs Bochner);
  `SemigroupGroupExtension.lean` → `semigroupGroupBochner`, `semigroupGroupBochnerExtension`.

## The build, in layers

The ordering is the dependency order, not a strict schedule.

### Layer 0: C₀-semigroup API
`StronglyContinuousSemigroup`, `ContractingSemigroup`, the generator and its dense domain,
strong continuity, the semigroup laws. *(Migrate `StronglyContinuousSemigroup.lean`.)*

### Layer 1: Hille–Yosida resolvent — **suggested first PR**
`resolvent`, `resolventRightInv` ((λ−A)R(λ) = 1 on the domain), `hilleYosidaResolventBound`
(`‖R(λ)‖ ≤ 1/λ`). Cleanly Mathlib-only; the migrated module already compiles on v4.31.

### Layer 2: generation theorem / Lumer–Phillips converse
Densely-defined dissipative + range condition ⇒ generates a contraction semigroup. ⚠ Mostly
**build-here**: the source has the `IsDissipative` scaffold (`Future/GenerationTheorem.lean`)
but not the full converse; this is the genuinely open item.

### Layer 3: Bernstein's theorem
Completely monotone ⇒ Laplace transform of a unique finite measure. *(Migrate the Bernstein
chain.)* Mathlib-only; the measure extraction uses Prokhorov tightness.

### Layer 4: BCR Bochner (d = 0, then general)
Semigroup/Laplace positive-definite representation. **Uniqueness** (`laplaceFourier_unique`)
is Mathlib-only and portable now; **existence** (`semigroupGroupBochner`) ⚠ depends on the
spatial Bochner theorem — defer until there is a Mathlib-only route to it (or until a Bochner
theorem for positive-definite functions on `ℝᵈ` is itself a TauCeti target).

## Worked examples (acceptance criteria, keeping the statements honest)

- **Concrete C₀-semigroup:** the multiplication semigroup `S t f = e^{−t·m} f` on a function
  space (or `e^{tA}` for a bounded `A`) is a `ContractingSemigroup` with generator `−m` (resp.
  `A`); its resolvent is the expected Neumann/integral form.
- **Resolvent bound is non-vacuous:** for the bounded generator `A`, `‖R(λ)‖ ≤ 1/λ` matches
  the Neumann series `R(λ) = (λ − A)⁻¹`.
- **Bernstein on `e^{−t}`:** `f t = e^{−t}` is completely monotone with representing measure
  the Dirac mass `δ₁`; `f t = 1/(1+t)` gives `μ = e^{−x} dx`.
- **BCR d = 0** recovers exactly Bernstein.

## Ordering

Layers 0–1 first: the C₀ API and the Hille–Yosida resolvent are direct migrations that
compile on v4.31 and validate the pipeline (Layer 1 is the suggested first PR). Layer 3
(Bernstein) is an independent Mathlib-only migration that can proceed in parallel. Layer 2
(generation theorem) is the open mathematical item. Layer 4 (BCR) is last: its uniqueness is
portable now, its existence waits on a Mathlib-only spatial Bochner theorem.

## References

- K.-J. Engel, R. Nagel, *One-Parameter Semigroups for Linear Evolution Equations* (GTM 194,
  2000) — C₀-semigroups, generators, Hille–Yosida, Lumer–Phillips.
- R. Schilling, R. Song, Z. Vondraček, *Bernstein Functions: Theory and Applications* (de
  Gruyter, 2nd ed. 2012) — completely monotone / Bernstein functions.
- C. Berg, J. P. R. Christensen, P. Ressel, *Harmonic Analysis on Semigroups* (GTM 100, 1984)
  — Theorem 4.1.13, positive-definite functions on involutive semigroups.
