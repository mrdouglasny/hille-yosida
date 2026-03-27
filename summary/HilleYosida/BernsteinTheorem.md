# `BernsteinTheorem.lean` — Informal Summary

> **Source**: [`HilleYosida/Future/BernsteinTheorem.lean`](../../HilleYosida/Future/BernsteinTheorem.lean)
> **Generated**: 2026-03-27
> **Note**: Hand-written summary of the final proved version.

## Overview

This file proves the semigroup Bochner representation theorem used in the
Hille-Yosida / Osterwalder-Schrader pipeline.

For a bounded continuous function
$$
F : [0,\infty) \times \mathbb{R}^d \to \mathbb{C}
$$
that is positive-definite for the involutive semigroup
$$
([0,\infty) \times \mathbb{R}^d,\; (t,a)^* = (t,-a)),
$$
the file constructs a finite positive measure
$$
\mu \text{ on } [0,\infty) \times \mathbb{R}^d
$$
such that
$$
F(t,a) = \int e^{-tp} e^{i\langle a,q\rangle}\, d\mu(p,q)
\qquad (t \ge 0).
$$

This is BCR Theorem 4.1.13 in the formulation needed for the project.

## Status

**Main result**: Proven

**Main theorem**:
- [`semigroupGroupBochner_proof`](../../HilleYosida/Future/BernsteinTheorem.lean#L2778)

**Internal assembly theorem**:
- [`product_measure_assembly`](../../HilleYosida/Future/BernsteinTheorem.lean#L2722)

**Length**: theorem-sized development combining Fourier analysis, Bernstein/Laplace
representation, uniqueness, and a discrete-grid Prokhorov construction.

## Main Statement

### [`semigroupGroupBochner_proof`](../../HilleYosida/Future/BernsteinTheorem.lean#L2778)

If `F` is:
- continuous on `Ici 0 × univ`,
- bounded for `t ≥ 0`,
- semigroup positive-definite,

then there exists a finite measure `μ` on `ℝ × (Fin d → ℝ)` such that:
- `μ ((Set.Iio 0).prod Set.univ) = 0`,
- for every `t ≥ 0` and `a : Fin d → ℝ`,
  $$
  F(t,a) = \int e^{-tp} e^{i\langle a,q\rangle}\, d\mu(p,q).
  $$

The support condition says the temporal variable `p` lives in `[0,\infty)`.

## Proof Structure

The proof is organized in three stages.

### 1. Spatial Bochner at fixed time

For each fixed `t ≥ 0`, the function
$$
a \mapsto F(t,a)
$$
is an ordinary positive-definite function on `ℝ^d`.

Bochner's theorem produces a finite spatial measure `ν_t` with
$$
F(t,a) = \int e^{i\langle a,q\rangle}\, d\nu_t(q).
$$

This is formalized by:
- [`spatial_bochner_measures`](../../HilleYosida/Future/BernsteinTheorem.lean#L740)

### 2. Temporal Laplace representation on slices

For each measurable spatial set `B`, define
$$
f_B(t) := \nu_t(B).
$$

The file proves that `t ↦ f_B(t)` is semigroup positive-definite, bounded, and
continuous on `[0,\infty)`. Then `semigroup_pd_laplace` from `BCR_d0` gives a finite
measure `σ_B` on `ℝ`, supported on `[0,\infty)`, such that
$$
f_B(t) = \int e^{-tp}\, d\sigma_B(p).
$$

This stage also proves uniqueness of the temporal slice measure via Laplace
uniqueness:
- first on `[0,1]` using moment equality and Weierstrass approximation,
- then on `[0,\infty)` by pushing forward along `p \mapsto e^{-p}`.

Relevant lemmas include:
- [`spatial_measures_pd`](../../HilleYosida/Future/BernsteinTheorem.lean#L1365)
- [`laplace_measure_unique`](../../HilleYosida/Future/BernsteinTheorem.lean#L286)
- [`temporalSliceRepOf`](../../HilleYosida/Future/BernsteinTheorem.lean#L1565)

### 3. Assemble the joint measure

This is the hard part of the file.

Instead of trying to extend an abstract bimeasure by Caratheodory, the proof uses
a concrete approximation by discrete product measures on finer and finer spatial
grids.

For each grid size `n`:
- partition `ℝ^d` into measurable cubes `gridCube n v`,
- attach the temporal slice `σ_(gridCube n v)` to each cube,
- place the spatial mass at the grid anchor `gridAnchor n v`,
- sum the resulting product measures over `v : Fin d → ℤ`.

This gives an approximating measure
$$
\mu_n = \sum_v \sigma_{Q_{n,v}} \otimes \delta_{\mathrm{anchor}(v)}.
$$

The file then proves:
- exact mass control of `μ_n`,
- support in `p ≥ 0`,
- spatial tail bounds from the grid geometry,
- temporal tail bounds from the slice family,
- tightness of the normalized approximants,
- extraction of a weakly convergent subsequence by Prokhorov,
- identification of the limit by comparing the Fourier-Laplace transform of `μ_n`
  with the step-function approximation
  $$
  q \mapsto e^{i\langle a, \mathrm{gridStep}_n(q)\rangle},
  $$
  and applying dominated convergence.

This construction is packaged in:
- [`joint_measure_from_temporal_slices`](../../HilleYosida/Future/BernsteinTheorem.lean#L2249)
- [`product_measure_assembly`](../../HilleYosida/Future/BernsteinTheorem.lean#L2722)

## Why this proof works well in Lean

The final version avoids two bad routes:
- global Stone-Weierstrass approximation of indicators on noncompact spaces,
- abstract bimeasure extension on arbitrary measurable spaces.

Instead it stays close to Mathlib's strengths:
- Bochner representation for fixed-time spatial measures,
- Bernstein/Laplace representation in one real variable,
- uniqueness by integral identities,
- tightness and subsequence extraction for finite measures,
- bounded continuous test functions plus dominated convergence.

## Remaining project axioms

This file no longer contains a live `sorry` or `axiom`.

The remaining project axioms are currently in:
- [`HilleYosida/Future/GenerationTheorem.lean`](../../HilleYosida/Future/GenerationTheorem.lean#L53)
- [`HilleYosida/Future/GenerationTheorem.lean`](../../HilleYosida/Future/GenerationTheorem.lean#L98)
