# Hille-Yosida Project Status

**Date:** 2026-03-27
**Branch:** reorg
**Lean:** v4.29.0-rc6 | **Mathlib:** v4.29.0-rc6
**Build:** passing, 0 sorry warnings (linter style warnings present)

---

## Trust Boundary

**All main theorems are fully proved with 0 axioms and 0 sorry's.**

| File | Contents | Status |
|------|----------|--------|
| `StronglyContinuousSemigroup.lean` | C0-semigroups, Hille-Yosida forward | **Fully proved** (0 axioms, 0 sorry's) |
| `Bernstein.lean` | Completely monotone → Laplace | **Fully proved** (0 axioms, 0 sorry's) |
| `FourierPD.lean` | `pd_quadratic_form_of_measure` | **Fully proved** (0 axioms, 0 sorry's) |
| `BCR_d0.lean` | `semigroup_pd_laplace` (BCR d=0) | **Fully proved** (0 axioms, 0 sorry's) |
| `BCR_General.lean` | `semigroupGroupBochner_proof` (BCR general d) | **Fully proved** (0 axioms, 0 sorry's) |
| `SemigroupGroupExtension.lean` | `semigroupGroupBochner` + group extension | **Fully proved** (0 axioms, 0 sorry's) |

### Axioms (only in Future/ — not used by main proof chain)

| Axiom | File | Purpose |
|-------|------|---------|
| `domain_isDense` | `Future/GenerationTheorem.lean` | Generator domain dense (HY converse, future work) |
| `hilleYosidaGeneration` | `Future/GenerationTheorem.lean` | Lumer-Phillips generation (HY converse, future work) |

---

## Dependency Chain

```
bernstein_theorem [PROVED, 2444 lines]
  └── IsCompletelyMonotone → Laplace transform
      Uses: taylor_integral_remainder, Prokhorov, Portmanteau

semigroup_pd_laplace [PROVED, 1503 lines]
  ├── PD → alternating differences → CM (Vandermonde + convexity)
  ├── Mollifier smoothing → apply bernstein_theorem
  └── Prokhorov extraction → Laplace representation

semigroupGroupBochner_proof [PROVED, 2822 lines]
  ├── Spatial Bochner: bochner_theorem (from mrdouglasny/bochner)
  ├── Temporal BCR d=0: semigroup_pd_laplace
  └── Product measure assembly

semigroupGroupBochner [PROVED, delegates to semigroupGroupBochner_proof]

semigroupGroupBochnerExtension [PROVED]
  ├── Bounded, continuous, PD from Fourier-Laplace representation
  └── Uses pd_quadratic_form_of_measure [PROVED]
```

---

## Source Files

| File | Lines | Key theorems | Axioms | Sorry's |
|------|-------|-------------|--------|---------|
| `StronglyContinuousSemigroup.lean` | 867 | `hilleYosidaResolventBound` | 0 | 0 |
| `SemigroupGroupDefs.lean` | 26 | `IsSemigroupGroupPD` | 0 | 0 |
| `Bernstein.lean` | 2444 | `bernstein_theorem` | 0 | 0 |
| `FourierPD.lean` | 72 | `pd_quadratic_form_of_measure` | 0 | 0 |
| `BCR_d0.lean` | 1503 | `semigroup_pd_laplace` | 0 | 0 |
| `BCR_General.lean` | 2822 | `semigroupGroupBochner_proof` | 0 | 0 |
| `SemigroupGroupExtension.lean` | 271 | `semigroupGroupBochner`, `semigroupGroupBochnerExtension` | 0 | 0 |
| `Future/GenerationTheorem.lean` | 109 | — | 2 | 0 |
| **Total** | **~8100** | | **0 (main)** | **0** |

---

## External Dependencies

- **Mathlib** (v4.29.0-rc6)
- **[BochnerMinlos](https://github.com/mrdouglasny/bochner)** — Bochner's theorem for PD functions on $\mathbb{R}^d$

## References

- **[BCR]** Berg-Christensen-Ressel, *Harmonic Analysis on Semigroups* (1984), Theorem 4.1.13
- **[EN]** Engel-Nagel, *One-Parameter Semigroups for Linear Evolution Equations*, GTM 194 (2000)
- **[Widder]** Widder, *The Laplace Transform* (1941), Chapter IV
- **[Chafaï]** Chafaï, Blog post on Bernstein's theorem (2013)
