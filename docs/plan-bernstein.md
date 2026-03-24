# Plan: Proving Bernstein's Theorem

## Goal

Replace the `bernstein_theorem` axiom in `Bernstein.lean` with a proof:

```
If f : [0,∞) → ℝ is completely monotone, then f(t) = ∫₀^∞ e^{-tp} dμ(p)
for a unique finite positive measure μ.
```

## Estimated effort: ~200 lines, similar to `bochner_theorem` in the bochner repo

## Proof strategy: Hausdorff moments + Prokhorov

The proof reduces Bernstein to the **Hausdorff moment problem** on [0,1],
then changes variables. This parallels the bochner repo's strategy
(Gaussian regularization → Prokhorov → weak limit) but is simpler
because [0,1] is compact.

### Phase 1: CM properties (~30 lines)

Extract basic properties from `IsCompletelyMonotone`:
- `f(t) ≥ 0` for all `t ≥ 0` (n=0 in the forward difference)
- `f` is non-increasing: `f(t) ≥ f(t+h)` (n=1)
- `f` is convex (n=2)
- `f` is bounded: `0 ≤ f(t) ≤ f(0)` for all `t ≥ 0`

These follow directly from the forward difference definition by
specializing to small `n`.

### Phase 2: Discrete approximation (~60 lines)

For each `n`, define a discrete measure `μ_n` on `[0, ∞)`:

The **Widder-Stieltjes** approximation: define

```
w_{n,k} = (-1)^k · C(n,k) · Δ^{n-k}_{1} f(k)    (CHECK EXACT FORMULA)
```

where `Δ^m_h f(t) = ∑_{j=0}^m (-1)^j C(m,j) f(t + jh)` is the forward
difference. The CM condition guarantees `w_{n,k} ≥ 0`.

Set `μ_n = ∑_{k=0}^{n} w_{n,k} · δ_{k/n}` (sum of weighted Diracs).

**Key property**: `∫ e^{-tp} dμ_n(p) → f(t)` as `n → ∞`.

This is the **Bernstein polynomial approximation** for the function
`g(x) = f(-log x)` on `[0,1]`, transferred to the Laplace domain.

**Alternative**: Use the simpler formula from Feller (1971):
define `α_n(p)` as the step function whose Laplace-Stieltjes transform
approximates `f`. The exact formula needs to be verified against
Widder Ch. IV or Feller Vol. II Ch. XIII.

**ACTION ITEM**: Look up the exact discrete approximation formula in
Widder or Feller and verify it works. This is the critical step.

### Phase 3: Tightness (~30 lines)

Show `{μ_n}` is tight on `[0, ∞)`:
- Total mass: `μ_n([0,∞)) = f(0)` (bounded, independent of n)
- Tail bound: since `f` is non-increasing with `f(t) → L ≥ 0` as `t → ∞`,
  and `∫ e^{-tp} dμ_n ≈ f(t) → L`, the mass of `μ_n` on `[K, ∞)` is
  controlled by `f(0) - f(K/n)` or similar
- For `K` large enough, `μ_n([K, ∞)) < ε` uniformly in `n`

**Mathlib has**: `IsTightMeasureSet` and `isCompact_closure_of_isTightMeasureSet`
(Prokhorov's theorem). The bochner repo already uses this machinery.

### Phase 4: Weak limit (~40 lines)

Extract convergent subsequence and verify:
- `μ_{n_k} → μ` weakly (from Prokhorov/sequential compactness)
- For each `t ≥ 0`: `f(t) = lim_k ∫ e^{-tp} dμ_{n_k}(p) = ∫ e^{-tp} dμ(p)`
  - The function `p ↦ e^{-tp}` is bounded and continuous on `[0, ∞)` for `t ≥ 0`
  - Weak convergence + bounded continuous test functions → integral convergence
  - This uses the **Portmanteau theorem** (in Mathlib)
- `μ` is supported on `[0, ∞)`: inherited from `μ_n`
- `μ` is finite: `μ([0,∞)) = lim μ_n([0,∞)) = f(0)`

### Phase 5: Packaging (~10 lines)

Match the conclusion format of `bernstein_theorem`:
- `IsFiniteMeasure μ`: from Phase 4
- `μ((-∞, 0)) = 0`: from support condition
- `f(t) = ∫ e^{-tp} dμ(p)`: from Phase 4

## Key Mathlib dependencies

| Lemma | Role | Status |
|-------|------|--------|
| `isCompact_closure_of_isTightMeasureSet` | Prokhorov's theorem | In Mathlib |
| Portmanteau (`tendsto_of_forall_isOpen_le_liminf'`) | Weak convergence → integral convergence | In Mathlib |
| `ProbabilityMeasure` | Tight families of probability measures | In Mathlib |
| `MeasureTheory.Measure.sum` / `MeasureTheory.Measure.dirac` | Discrete measure construction | In Mathlib |
| `exp_neg_integrableOn_Ioi` | Laplace integrand is integrable | In Mathlib (already used in resolvent) |

## Key risks

1. **Exact discrete formula**: The Widder/Feller approximation formula needs
   to be verified. If the formula is wrong, Phase 2 fails.

2. **Bernstein polynomial convergence**: Showing `∫ e^{-tp} dμ_n → f(t)` may
   require Bernstein's approximation theorem for polynomials, which may or
   may not be in Mathlib.

3. **Non-integer t**: The weak limit gives `f(t) = ∫ e^{-tp} dμ` for rational
   t first, then extending to all real t ≥ 0 by continuity of both sides.

## Alternative approaches

**A. Direct Widder inversion**: Define μ via the inversion formula
`dμ/dp = lim_{n→∞} (-1)^n/n! (n/p)^{n+1} f^{(n)}(n/p)`.
Requires: f is C^∞ (derivable from CM), convergence of the inversion.
Pro: explicit formula. Con: needs derivatives, convergence is harder.

**B. Via bochner_theorem**: Transform the problem to a PD function on ℝ
and apply the already-proved Bochner theorem. Define g(t) = f(e^{|t|})
or similar. Con: the transformation is non-trivial and may not preserve PD.

**C. Via Choquet's theorem**: The set of CM functions with f(0) = 1 is a
Choquet simplex with extreme points `e^{-tp}`. By Choquet, f = ∫ e^{-tp} dμ.
Con: Choquet's theorem is not in Mathlib.

## Recommendation

Use the Hausdorff moment approach (Phases 1–5). It's the most elementary,
parallels the bochner repo proof structure, and uses Mathlib's existing
Prokhorov/Portmanteau infrastructure.

Before starting: **verify the exact discrete approximation formula** from
Widder Ch. IV §4 or Feller Vol. II Ch. XIII §4.
