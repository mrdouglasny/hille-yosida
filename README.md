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

**Existence** (`semigroupGroupBochner`): decomposes into spatial Bochner + temporal BCR d=0 + product measure assembly.

**Uniqueness** (`laplaceFourier_unique`): finite measures on $[0,\infty) \times \mathbb{R}^d$ with equal Laplace-Fourier transforms are equal. Proved via Fourier uniqueness on spatial slices, Laplace uniqueness on temporal slices, and rectangular measure extension.

## File Structure

| File | Contents |
|------|----------|
| [StronglyContinuousSemigroup.lean](HilleYosida/StronglyContinuousSemigroup.lean) | [C₀-semigroups, generators, resolvent, Hille-Yosida](summary/HilleYosida/StronglyContinuousSemigroup.md) |
| [BernsteinBasic.lean](HilleYosida/BernsteinBasic.lean) | [`IsCompletelyMonotone`, `taylor_integral_remainder`](summary/HilleYosida/BernsteinBasic.md) |
| [BernsteinMeasures.lean](HilleYosida/BernsteinMeasures.lean) | [Density, IBP, kernel, packaging](summary/HilleYosida/BernsteinMeasures.md) |
| [BernsteinChafai.lean](HilleYosida/BernsteinChafai.lean) | [Chafai identity, Prokhorov extraction](summary/HilleYosida/BernsteinChafai.md) |
| [Bernstein.lean](HilleYosida/Bernstein.lean) | [`bernstein_theorem`](summary/HilleYosida/Bernstein.md) |
| [FourierPD.lean](HilleYosida/FourierPD.lean) | [Fourier PD: `pd_quadratic_form_of_measure`](summary/HilleYosida/FourierPD.md) |
| [BCR_d0.lean](HilleYosida/BCR_d0.lean) | [BCR 4.1.13 for d=0: `semigroup_pd_laplace`](summary/HilleYosida/BCR_d0.md) |
| [BCR_General.lean](HilleYosida/BCR_General.lean) | [BCR 4.1.13: `semigroupGroupBochner_proof` + `laplaceFourier_unique`](summary/HilleYosida/BCR_General.md) |
| [SemigroupGroupExtension.lean](HilleYosida/SemigroupGroupExtension.lean) | [`semigroupGroupBochner` + group extension](summary/HilleYosida/SemigroupGroupExtension.md) |
| [SemigroupGroupDefs.lean](HilleYosida/SemigroupGroupDefs.lean) | [`IsSemigroupGroupPD` definition](summary/HilleYosida/SemigroupGroupDefs.md) |
| [Future/GenerationTheorem.lean](HilleYosida/Future/GenerationTheorem.lean) | [HY converse (Lumer-Phillips)](summary/HilleYosida/Future/GenerationTheorem.md) |

## Axiom Inventory

**All main theorems are fully proved with 0 axioms and 0 sorry's — the library is now
axiom-free.** (`Future/GenerationTheorem.lean`, the converse Hille–Yosida / Lumer–Phillips
direction, holds only scaffolding — the `IsDissipative` setup — and no longer declares
axioms.) The kernel-authoritative audit is in [`AXIOM_AUDIT.md`](AXIOM_AUDIT.md); generate the
live trace with `lake env lean audit/axiom_report.lean`.

## Assurance conventions

This project follows
[`math-commons/formalization-assurance`](https://github.com/math-commons/formalization-assurance)
(verification / validation / faithfulness, axiom vetting, `formalization.yaml`, object
contracts). Local settings:

| Setting | Where |
|---|---|
| Project card | [`formalization.yaml`](formalization.yaml) |
| Axiom audit | [`AXIOM_AUDIT.md`](AXIOM_AUDIT.md) — **0 axioms** |
| Vetting strictness | [`audit/vetting/policy.yml`](audit/vetting/policy.yml) — `L1` |
| Faithfulness (informal↔formal) | [`audit/FAITHFULNESS.md`](audit/FAITHFULNESS.md) |
| Acceptance / characterization | [`audit/VALIDATION.md`](audit/VALIDATION.md) |
| Object contracts | [`audit/contracts/`](audit/contracts/) — `known_values` cards (`resolvent`, `completelyMonotone`) |
| Kernel axiom report | [`audit/axiom_report.lean`](audit/axiom_report.lean) (generator) |
| CI assurance gate | [`.github/workflows/assurance.yml`](.github/workflows/assurance.yml) → the hub's reusable `assure.yml` (build + axiom-report-in-sync + sorry-confinement; warn-only at `L1`) |

> Machine-gate TODO: commit the golden `audit/axiom-report.txt` from a build
> (`lake env lean audit/axiom_report.lean > audit/axiom-report.txt`) and raise the policy to
> `L2` to enforce.

## BCR d=0: Proof Architecture (1503 lines)

The core engine `semigroup_pd_laplace` in `BCR_d0.lean` proves that bounded continuous semigroup-PD functions on $[0,\infty)$ are Laplace transforms. The proof:

1. **PD to alternating differences:** Vandermonde convolution for even order, convexity bootstrap for odd order
2. **Iterated integral bridge:** The n-th forward difference equals the n-th iterated integral of the n-th derivative (bypasses Widder IV.12a)
3. **Mollifier trick:** Smooth approximation inherits alternating differences, hence is `IsCompletelyMonotone`
4. **Bernstein to measures:** Apply `bernstein_theorem` to each mollified function
5. **Prokhorov extraction:** Uniform mass bound + tightness gives weak limit
6. **Verification:** Pointwise convergence + Laplace convergence gives the representation

## Application: QFT Reconstruction

This project provides the `semigroupGroupBochner` theorem needed by [OSreconstruction](https://github.com/xiyin137/OSreconstruction) for the E-to-R direction of Osterwalder-Schrader reconstruction. The Fourier-Laplace measure representation connects Euclidean contraction semigroups $e^{-tH}$ to Lorentzian unitary groups $e^{itH}$ via analytic continuation.

## Dependencies

- **Mathlib** (v4.29.0-rc6)
- **[BochnerMinlos](https://github.com/mrdouglasny/bochner)** -- Bochner's theorem for finite-dimensional PD functions

## References

- Berg-Christensen-Ressel, *Harmonic Analysis on Semigroups* (1984), Theorem 4.1.13
- Engel-Nagel, *One-Parameter Semigroups for Linear Evolution Equations*, GTM 194 (2000)
- Widder, *The Laplace Transform* (1941), Chapter IV
- Reed-Simon I-II (1972-1975)

## Author

Michael R. Douglas

## License

Copyright (c) 2026 Michael R. Douglas. Released under the Apache 2.0 license.
