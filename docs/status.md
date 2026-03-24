# Hille-Yosida Project Status

**Date:** 2026-03-24
**Branch:** main
**Lean:** v4.29.0-rc6 | **Mathlib:** v4.29.0-rc6
**Build:** passing, 0 sorry warnings

---

## Trust Boundary

The project has two layers with different proof status:

| Layer | File | Status |
|-------|------|--------|
| **Semigroup theory** | `StronglyContinuousSemigroup.lean` | **Fully proved** — 0 sorries, 0 axioms |
| **BCR extension** | `SemigroupGroupExtension.lean`, `Bernstein.lean`, `FourierPD.lean` | **Axiom-dependent** — 0 sorries, 3 axioms |

Downstream users importing `HilleYosida` get both layers. The semigroup theory
(forward Hille-Yosida theorem) is self-contained. The BCR extension layer
depends on three axioms that are NOT proved in this project or in Mathlib.

### Axioms in the main library

| Axiom | File | What it assumes |
|-------|------|-----------------|
| `bernstein_theorem` | `Bernstein.lean:47` | Completely monotone functions on $[0,\infty)$ are Laplace transforms of finite positive measures |
| `pd_quadratic_form_of_measure` | `FourierPD.lean:32` | $\sum_{ij} \bar c_i c_j \int \bar\chi_i \chi_j\, d\mu \geq 0$ for finite positive $\mu$ (Fourier PD, "easy Bochner") |
| `semigroupGroupBochner` | `SemigroupGroupExtension.lean:79` | BCR Theorem 4.1.13: bounded continuous PD functions on $[0,\infty) \times \mathbb{R}^d$ are Fourier-Laplace transforms |

### Axioms in Future/ (not imported by main library)

| Axiom | File | What it assumes |
|-------|------|-----------------|
| `domain_isDense` | `Future/GenerationTheorem.lean:53` | Generator domain $D(A)$ is dense in $X$ |
| `hilleYosidaGeneration` | `Future/GenerationTheorem.lean:98` | Converse Hille-Yosida / Lumer-Phillips generation theorem |
| `bernstein_theorem` | `Future/BernsteinTheorem.lean:101` | Duplicate of main `bernstein_theorem` |

### Dependency chain

```
semigroupGroupBochner [AXIOM]
  ├── spatial_slice_pd [PROVED] (bridge to bochner repo)
  │     └── bochner_theorem [PROVED, imported from mrdouglasny/bochner]
  ├── bernstein_theorem [AXIOM]
  └── product measure construction [not written, ~100 lines]

semigroupGroupBochnerExtension [PROVED, given semigroupGroupBochner]
  ├── bounded [PROVED]
  ├── continuous [PROVED]
  └── PD [PROVED, uses pd_quadratic_form_of_measure AXIOM]
```

---

## What is fully proved (no axioms)

### StronglyContinuousSemigroup.lean — 0 sorries, 0 axioms

| Theorem | Reference |
|---------|-----------|
| `StronglyContinuousSemigroup` | [EN] Def. I.5.1 |
| `ContractingSemigroup` | [EN] Def. I.5.6 |
| `normBoundedOnUnitInterval` | [EN] Prop. I.5.3, Banach-Steinhaus |
| `normBoundedOnInterval` | Induction on $\mathbb{N}$ |
| `strongContAt` | [EN] Prop. I.5.3 |
| `generator`, `domain`, `generatorMap` | [EN] Def. II.1.2 |
| `existsGrowthBound` | [EN] Prop. I.5.5 |
| `integrable_resolvent_integrand` | Contraction + exponential decay |
| `ContractingSemigroup.resolvent` | [EN] eq. II.(1.14), Bochner integral |
| `resolvent_generator_tendsto` | [EN] Thm. II.1.10, integral shift trick |
| `resolventMapsToDomain` | [EN] Thm. II.1.10(i) |
| `resolventRightInv` | $(\lambda I - A)R(\lambda) = I$ |
| `hilleYosidaResolventBound` | $\lVert R(\lambda) \rVert \leq 1/\lambda$ |

### SemigroupGroupExtension.lean — proved modulo axioms

| Theorem | Depends on axioms? |
|---------|-------------------|
| `spatial_slice_pd` | No (fully proved) |
| `semigroupGroupBochnerExtension.bounded` | Yes (`semigroupGroupBochner`) |
| `semigroupGroupBochnerExtension.continuous` | Yes (`semigroupGroupBochner`) |
| `semigroupGroupBochnerExtension.PD` | Yes (`semigroupGroupBochner`, `pd_quadratic_form_of_measure`) |

---

## Source files

| File | Lines | Theorems | Axioms | Sorries |
|------|-------|----------|--------|---------|
| `StronglyContinuousSemigroup.lean` | ~860 | 13 | 0 | 0 |
| `SemigroupGroupExtension.lean` | ~210 | 2 | 1 | 0 |
| `Bernstein.lean` | ~55 | 0 | 1 | 0 |
| `FourierPD.lean` | ~45 | 0 | 1 | 0 |
| `Future/GenerationTheorem.lean` | ~100 | 0 | 2 | 0 |
| `Future/BernsteinTheorem.lean` | ~150 | 2 | 1 | 0 |

---

## References

- **[EN]** Engel-Nagel, *One-Parameter Semigroups for Linear Evolution Equations*, GTM 194 (2000)
- **[Linares]** F. Linares, "The Hille-Yosida Theorem", IMPA lecture notes (2021)
- **[BCR]** Berg-Christensen-Ressel, *Harmonic Analysis on Semigroups* (1984), Thm 4.1.13
