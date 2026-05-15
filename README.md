# Hille-Yosida and BCR Semigroup Theory

A Lean 4 formalization of contraction semigroups (Hille-Yosida), Bernstein's theorem for completely monotone functions, and the BCR Bochner theorem (Theorem 4.1.13) for positive-definite functions on involutive semigroups.

## Main Results

### Hille-Yosida Resolvent Theorem (fully proved, 0 axioms)

For a contraction semigroup $\{S(t)\}_{t \geq 0}$ on a Banach space, the resolvent $R(\lambda) = \int_0^\infty e^{-\lambda t} S(t) dt$ satisfies $(\lambda I - A) R(\lambda) = I$ and $\|R(\lambda)\| \leq 1/\lambda$.

### Bernstein's Theorem (fully proved, 0 axioms)

A completely monotone function on $[0,\infty)$ is the Laplace transform of a unique finite positive measure supported on $[0,\infty)$.

### BCR Theorem 4.1.13 -- Semigroup Bochner (fully proved, 0 axioms)

Bounded continuous positive-definite functions on $[0,\infty) \times \mathbb{R}^d$ are Fourier-Laplace transforms of a unique finite positive measure:

$$F(t, a) = \int_{[0,\infty) \times \mathbb{R}^d} e^{-tp} \, e^{i\langle a, q\rangle} \, d\mu(p, q) \quad \text{for } t \geq 0$$

**Existence** (`semigroup_group_bochner`): decomposes into spatial Bochner + temporal BCR d=0 + product measure assembly.

**Uniqueness** (`laplace_fourier_unique`): finite measures on $[0,\infty) \times \mathbb{R}^d$ with equal Laplace-Fourier transforms are equal. Proved via Fourier uniqueness on spatial slices, Laplace uniqueness on temporal slices, and rectangular measure extension.

## File Structure

Sources are grouped into three pillars matching the proof structure.

### `Semigroup/` — operator semigroups (Hille-Yosida)

| File | Contents |
|------|----------|
| [Semigroup/StronglyContinuous.lean](HilleYosida/Semigroup/StronglyContinuous.lean) | [C₀-semigroups, generators, resolvent, Hille-Yosida](summary/HilleYosida/Semigroup/StronglyContinuous.md) |
| [Semigroup/GeneratorDerivative.lean](HilleYosida/Semigroup/GeneratorDerivative.lean) | Semigroup-generator commutation (EN Prop II.1.4c) |

### `Bernstein/` — completely-monotone functions

| File | Contents |
|------|----------|
| [Bernstein/Basic.lean](HilleYosida/Bernstein/Basic.lean) | [`IsCompletelyMonotone`, `taylor_integral_remainder`](summary/HilleYosida/Bernstein/Basic.md) |
| [Bernstein/Measures.lean](HilleYosida/Bernstein/Measures.lean) | [Density, IBP, kernel, packaging](summary/HilleYosida/Bernstein/Measures.md) |
| [Bernstein/Chafai.lean](HilleYosida/Bernstein/Chafai.lean) | [Chafai identity, Prokhorov extraction](summary/HilleYosida/Bernstein/Chafai.md) |
| [Bernstein/Theorem.lean](HilleYosida/Bernstein/Theorem.lean) | [`bernstein_theorem`](summary/HilleYosida/Bernstein/Theorem.md) |

### `BCR/` — BCR 4.1.13 (semigroup Bochner)

| File | Contents |
|------|----------|
| [BCR/d0.lean](HilleYosida/BCR/d0.lean) | [BCR 4.1.13 for d=0: `semigroup_pd_laplace`](summary/HilleYosida/BCR/d0.md) |
| [BCR/Common.lean](HilleYosida/BCR/Common.lean) | Laplace-uniqueness toolkit + `TemporalSliceRep` (shared by Existence and Uniqueness) |
| [BCR/Existence.lean](HilleYosida/BCR/Existence.lean) | BCR 4.1.13 existence: Steps 1/2/3 + `semigroup_group_bochner_proof` |
| [BCR/Uniqueness.lean](HilleYosida/BCR/Uniqueness.lean) | BCR 4.1.13 uniqueness: `laplace_fourier_unique` |
| [BCR/General.lean](HilleYosida/BCR/General.lean) | Re-export shim — imports Common + Existence + Uniqueness |
| [BCR/FourierPD.lean](HilleYosida/BCR/FourierPD.lean) | [Fourier PD: `pd_quadratic_form_of_measure`](summary/HilleYosida/BCR/FourierPD.md) |
| [BCR/SemigroupGroupDefs.lean](HilleYosida/BCR/SemigroupGroupDefs.lean) | [`IsSemigroupGroupPD` definition](summary/HilleYosida/BCR/SemigroupGroupDefs.md) |
| [BCR/SemigroupGroupExtension.lean](HilleYosida/BCR/SemigroupGroupExtension.lean) | [`semigroup_group_bochner` + group extension](summary/HilleYosida/BCR/SemigroupGroupExtension.md) |

### `Future/` — out-of-chain axiomatized future work

| File | Contents |
|------|----------|
| [Future/GenerationTheorem.lean](HilleYosida/Future/GenerationTheorem.lean) | [HY converse (Lumer-Phillips)](summary/HilleYosida/Future/GenerationTheorem.md) |

## Axiom Inventory

**All main theorems are fully proved with 0 axioms and 0 sorry's.** The only axioms in the project are in `Future/GenerationTheorem.lean` for the converse Hille-Yosida theorem (future work, not imported by the BCR proof chain):

| Axiom | File | Purpose |
|-------|------|---------|
| `domain_isDense` | `Future/GenerationTheorem.lean` | Generator domain dense in X |
| `hilleYosidaGeneration` | `Future/GenerationTheorem.lean` | Lumer-Phillips generation theorem |

## BCR d=0: Proof Architecture (1503 lines)

The core engine `semigroup_pd_laplace` in `BCR/d0.lean` proves that bounded continuous semigroup-PD functions on $[0,\infty)$ are Laplace transforms. The proof:

1. **PD to alternating differences:** Vandermonde convolution for even order, convexity bootstrap for odd order
2. **Iterated integral bridge:** The n-th forward difference equals the n-th iterated integral of the n-th derivative (bypasses Widder IV.12a)
3. **Mollifier trick:** Smooth approximation inherits alternating differences, hence is `IsCompletelyMonotone`
4. **Bernstein to measures:** Apply `bernstein_theorem` to each mollified function
5. **Prokhorov extraction:** Uniform mass bound + tightness gives weak limit
6. **Verification:** Pointwise convergence + Laplace convergence gives the representation

## Application: QFT Reconstruction

This project provides the `semigroup_group_bochner` theorem needed by [OSreconstruction](https://github.com/xiyin137/OSreconstruction) for the E-to-R direction of Osterwalder-Schrader reconstruction. The Fourier-Laplace measure representation connects Euclidean contraction semigroups $e^{-tH}$ to Lorentzian unitary groups $e^{itH}$ via analytic continuation.

## Dependencies

- **Mathlib** (v4.29.0-rc6)
- **[BochnerMinlos](https://github.com/mrdouglasny/bochner)** -- Bochner's theorem for finite-dimensional PD functions

## Downstream Migration Notes

The module reorganization into `Semigroup/`, `Bernstein/`, and `BCR/` subfolders renames public module paths. Downstream consumers must update their imports.

**Preferred: import via pillar facades.** Three top-level files re-export each pillar's contents, so downstream code is insulated from further internal reshuffling:

- `import HilleYosida.Semigroup` — Hille-Yosida semigroup material
- `import HilleYosida.Bernstein` — Bernstein's theorem
- `import HilleYosida.BCR` — BCR Theorem 4.1.13 (semigroup Bochner)

Or `import HilleYosida` for the whole library.

**Known consumers requiring an update:**

- [OSreconstruction](https://github.com/xiyin137/OSreconstruction) — `OSReconstruction/SCV/SemigroupGroupBochner.lean`:
  - `import HilleYosida.SemigroupGroupExtension` → `import HilleYosida.BCR` (or deep path `HilleYosida.BCR.SemigroupGroupExtension`)
  - `import HilleYosida.BCR_General` → `import HilleYosida.BCR` (or deep path `HilleYosida.BCR.General`)

**Full deep-path remapping** (use if you need a specific sub-module rather than the pillar facade):

| Old module path | New module path |
|---|---|
| `HilleYosida.StronglyContinuousSemigroup` | `HilleYosida.Semigroup.StronglyContinuous` |
| `HilleYosida.GeneratorDerivative` | `HilleYosida.Semigroup.GeneratorDerivative` |
| `HilleYosida.BernsteinBasic` | `HilleYosida.Bernstein.Basic` |
| `HilleYosida.BernsteinMeasures` | `HilleYosida.Bernstein.Measures` |
| `HilleYosida.BernsteinChafai` | `HilleYosida.Bernstein.Chafai` |
| `HilleYosida.Bernstein` | `HilleYosida.Bernstein.Theorem` |
| `HilleYosida.BCR_d0` | `HilleYosida.BCR.d0` |
| `HilleYosida.BCR_Common` | `HilleYosida.BCR.Common` |
| `HilleYosida.BCR_Existence` | `HilleYosida.BCR.Existence` |
| `HilleYosida.BCR_Uniqueness` | `HilleYosida.BCR.Uniqueness` |
| `HilleYosida.BCR_General` | `HilleYosida.BCR.General` |
| `HilleYosida.SemigroupGroupDefs` | `HilleYosida.BCR.SemigroupGroupDefs` |
| `HilleYosida.SemigroupGroupExtension` | `HilleYosida.BCR.SemigroupGroupExtension` |
| `HilleYosida.FourierPD` | `HilleYosida.BCR.FourierPD` |

`HilleYosida.Future.GenerationTheorem` is unchanged.

### Theorem renames (mathlib-ready snake_case sweep)

Six public theorems in `HilleYosida.Semigroup.StronglyContinuous` renamed to match Mathlib's `snake_case` convention for `Prop`-valued declarations:

| Old | New |
|---|---|
| `operatorZeroApply` | `operator_zero_apply` |
| `strongContAt` | `strong_cont_at` |
| `resolventMapsToDomain` | `resolvent_mapsTo_domain` |
| `resolventRightInv` | `resolvent_right_inv` |
| `hilleYosidaResolventBound` | `hille_yosida_resolvent_bound` |
| `existsGrowthBound` | `exists_growth_bound` |

(Two additional private renames, `normBoundedOn*` → `norm_bounded_on_*`, don't affect downstream.)

A `CoeFun` instance was also added so `S t x` works directly for `S : StronglyContinuousSemigroup X`. Existing `.operator t x` call sites are unchanged.

Update downstream call site references. The structural facade imports (`import HilleYosida.Semigroup`) are unchanged.

### Generator API: `HasDerivWithinAt` and predicate elimination

For Mathlib API compatibility, the C₀-semigroup generator API was refactored to use Mathlib's `HasDerivWithinAt` calculus infrastructure instead of a bespoke `Tendsto` predicate. Two breaking changes for downstream:

- **`StronglyContinuousSemigroup.generator (x : X) : Prop` is removed.** Use `x ∈ S.domain` (Submodule membership) instead. The domain's carrier is now `{ x | ∃ Ax, HasDerivWithinAt (fun t => S.operator t x) Ax (Set.Ici 0) 0 }`.
- **`StronglyContinuousSemigroup.generatorMap` is renamed to `StronglyContinuousSemigroup.generator`**, now meaning the actual generator operator `A : S.domain →ₗ[ℝ] X` (consistent with textbook notation).

A bridge lemma `StronglyContinuousSemigroup.hasDerivWithinAt_iff_tendsto_zero` is provided for callers that still want the `Tendsto`-flavored form.

### BCR theorem renames (mathlib-ready audit, Bernstein/BCR/Future pass)

Additional public renames in the BCR pillar, same snake_case convention:

| Old | New | File |
|---|---|---|
| `semigroupGroupBochner` | `semigroup_group_bochner` | `BCR/SemigroupGroupExtension.lean` |
| `semigroupGroupBochnerExtension` | `semigroup_group_bochner_extension` | `BCR/SemigroupGroupExtension.lean` |
| `semigroupGroupBochner_proof` | `semigroup_group_bochner_proof` | `BCR/Existence.lean` |
| `laplaceFourier_unique` | `laplace_fourier_unique` | `BCR/Uniqueness.lean` |

(One private rename, `weightedSpatial_eq_of_laplaceFourier_eq` → `weightedSpatial_eq_of_laplace_fourier_eq`, does not affect downstream.)

`@[ext]` lemmas were added for `Mollifier` (BCR/d0.lean) and `TemporalSliceRep` (BCR/Common.lean).

After merging this branch, regenerate the catalog entries:

```
cd ~/Documents/GitHub/catalogs
./gen_catalog.sh ~/Documents/GitHub/hille-yosida hille-yosida
./build_index.sh
```

## References

- Berg-Christensen-Ressel, *Harmonic Analysis on Semigroups* (1984), Theorem 4.1.13
- Engel-Nagel, *One-Parameter Semigroups for Linear Evolution Equations*, GTM 194 (2000)
- Widder, *The Laplace Transform* (1941), Chapter IV
- Reed-Simon I-II (1972-1975)

## Author

Michael R. Douglas

## License

Copyright (c) 2026 Michael R. Douglas. Released under the Apache 2.0 license.
