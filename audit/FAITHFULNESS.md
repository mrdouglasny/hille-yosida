# FAITHFULNESS — a dictionary between the mathematics and the Lean

For a reader who knows the mathematics (Engel–Nagel; Widder; Berg–Christensen–Ressel) but not
Lean: each primary object/theorem is given as the **informal statement next to the exact Lean
statement**, with an **encoding note** wherever the two differ (and the result that reconciles
them). You can decide the formalization is faithful **without reading any proof**. Per-file
prose is under [`../summary/`](../summary/). (Assurance conventions:
[`math-commons/formalization-assurance`](https://github.com/math-commons/formalization-assurance).)

> **Recurring encodings.** "for `t ≥ 0`" is a hypothesis `0 ≤ t`, not a subtype — the
> `operator` is total on `ℝ` and the laws are guarded by non-negativity. "supported on
> `[0,∞)`" is encoded as `μ (Set.Iio 0) = 0`.

---

## 1. Strongly continuous (C₀) semigroup

**Informal.** A family `{S(t)}_{t≥0}` of bounded operators with `S(0)=I`, `S(s+t)=S(s)S(t)`
for `s,t≥0`, and `t ↦ S(t)x` continuous at `0` (Engel–Nagel I.5).

**Lean.**
```lean
structure StronglyContinuousSemigroup where
  operator : ℝ → X →L[ℝ] X
  at_zero  : operator 0 = ContinuousLinearMap.id ℝ X
  semigroup : ∀ s t, 0 ≤ s → 0 ≤ t → operator (s + t) = (operator s).comp (operator t)
  strong_cont : ∀ x, Tendsto (fun t => operator t x) (𝓝[Set.Ici 0] 0) (𝓝 x)
```
*Note.* `operator` is defined on all of `ℝ`; the semigroup law is conditioned on `0 ≤ s, t`,
so it is a `[0,∞)` semigroup. A **contraction** semigroup adds `contracting : ∀ t, 0 ≤ t →
‖operator t‖ ≤ 1` (`ContractingSemigroup extends …`).

## 2. Generator and its domain

**Informal.** `A x = lim_{t↓0} (S(t)x − x)/t`, defined on the dense domain `D(A)` where the
limit exists.

**Lean.**
```lean
def StronglyContinuousSemigroup.generator (S) (x : X) : Prop :=
  ∃ Ax, Tendsto (fun t => (1/t) • (S.operator t x - x)) (𝓝[Set.Ioi 0] 0) (𝓝 Ax)
def StronglyContinuousSemigroup.domain (S) : Submodule ℝ X := { x | S.generator x }   -- (with module proofs)
-- generatorMap : domain → X  picks the value Ax
```
*Note.* `generator x` is the **predicate** "`x ∈ D(A)`" (the limit exists); the **value** `A x`
is `generatorMap`. So `D(A)` is a genuine `Submodule`, and `A` is a partial map on it — not a
total operator.

## 3. Resolvent and the Hille–Yosida identities

**Informal.** `R(λ) = ∫₀^∞ e^{−λt} S(t) dt`, and for a contraction semigroup `(λ−A)R(λ)=I` on
`D(A)` with `‖R(λ)‖ ≤ 1/λ` (λ>0).

**Lean.**
```lean
noncomputable def ContractingSemigroup.resolvent (S) (lambda : ℝ) (hlam : 0 < lambda) : X →L[ℝ] X
  := … fun x => ∫ t in Set.Ioi 0, Real.exp (-(lambda * t)) • S.operator t x …

theorem ContractingSemigroup.resolventRightInv (S) (lambda) (hlam : 0 < lambda) (x) :
    lambda • (S.resolvent lambda hlam x) - S.generatorMap ⟨_, S.resolventMapsToDomain ..⟩ = x

theorem hilleYosidaResolventBound (S) (lambda) (hlam : 0 < lambda) :
    ‖S.resolvent lambda hlam‖ ≤ 1 / lambda
```
*Note.* `resolvent` is literally the Laplace transform `∫_{(0,∞)} e^{−λt} S(t)x dt`.
`resolventRightInv` is `(λ − A)R(λ)x = x` pointwise, with `R(λ)x ∈ D(A)`
(`resolventMapsToDomain`) — i.e. `(λ−A)R(λ)=I`.

## 4. Completely monotone functions and Bernstein's theorem

**Informal.** `f` is completely monotone if `(−1)ⁿ f⁽ⁿ⁾(t) ≥ 0` for all `n`, `t>0`. Bernstein:
such `f` is the Laplace transform of a **unique finite** positive measure on `[0,∞)`.

**Lean.**
```lean
def IsCompletelyMonotone (f : ℝ → ℝ) : Prop :=
  ContDiffOn ℝ (⊤ : ℕ∞) f (Set.Ici 0) ∧
  ∀ n t, 0 ≤ t → 0 ≤ (-1 : ℝ) ^ n * iteratedDerivWithin n f (Set.Ici 0) t

theorem bernstein_theorem (f) (hcm : IsCompletelyMonotone f) :
    ∃ μ : Measure ℝ, IsFiniteMeasure μ ∧ μ (Set.Iio 0) = 0 ∧
      ∀ t, 0 ≤ t → f t = ∫ p, Real.exp (-(t * p)) ∂μ
-- uniqueness of the representing measure: laplace_measure_unique
```
*Note.* `bernstein_theorem` is the **existence** half (finite measure, supported on `[0,∞)` via
`μ (Iio 0) = 0`, with `f =` its Laplace transform). **Uniqueness** is the separate
`laplace_measure_unique` (Laplace-transform injectivity). Smoothness is on the *closed* `Ici 0`
via `iteratedDerivWithin`.

## 5. BCR semigroup-Bochner (Theorem 4.1.13) and uniqueness

**Informal.** A bounded continuous positive-definite `F` on `[0,∞)×ℝᵈ` is the Laplace–Fourier
transform `∫ e^{−tp} e^{i⟨a,q⟩} dμ` of a unique finite measure on `[0,∞)×ℝᵈ`.

**Lean.**
```lean
def IsSemigroupGroupPD (d) (F : ℝ → (Fin d → ℝ) → ℂ) : Prop :=
  ∀ n (c : Fin n → ℂ) (ts) (as), (∀ i, 0 ≤ ts i) →
    let q := ∑ i, ∑ j, star (c i) * c j * F (ts i + ts j) (as j - as i)
    q.im = 0 ∧ 0 ≤ q.re

theorem semigroupGroupBochner (d) (F) (hcont) (hbdd) (hpd : IsSemigroupGroupPD d F) :
    ∃ μ : Measure (ℝ × (Fin d → ℝ)), IsFiniteMeasure μ ∧ μ (Set.Iio 0 ×ˢ Set.univ) = 0 ∧
      ∀ t a, 0 ≤ t → F t a = ∫ p, Complex.exp (-(↑(t*p.1):ℂ)) *
        Complex.exp (Complex.I * ↑(∑ i, p.2 i * a i)) ∂μ

theorem laplaceFourier_unique {d} (μ₁ μ₂) [IsFiniteMeasure μ₁] [IsFiniteMeasure μ₂]
    (…support on [0,∞)…) (heq : equal Laplace–Fourier transforms for all t>0, a) : μ₁ = μ₂
```
*Note.* Positive-definiteness is the standard quadratic-form condition (`q.im = 0 ∧ 0 ≤ q.re`),
with the involution as `as j - as i`. The kernel is **Laplace in time** (`e^{−tp}`) and
**Fourier in space** (`e^{i⟨a,q⟩}`); support on `[0,∞)×ℝᵈ` is `μ (Iio 0 ×ˢ univ) = 0`.
Existence (`semigroupGroupBochner`) and uniqueness (`laplaceFourier_unique`) are separate.

---

## Audit recipe

`lake build` clean · `main` sorry-free (`audit/sorry-allowlist.txt` empty) · `lake env lean
audit/axiom_report.lean` shows the standard three for every headline above. Value/acceptance
checks: [`VALIDATION.md`](VALIDATION.md). Per-object contracts: [`contracts/`](contracts/).
