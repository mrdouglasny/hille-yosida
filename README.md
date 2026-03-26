# Hille-Yosida and BCR Semigroup Theory

A Lean 4 formalization of contraction semigroups (Hille-Yosida), Bernstein's theorem for completely monotone functions, and the BCR Bochner theorem (Theorem 4.1.13) for positive-definite functions on involutive semigroups.

## Main Results

### Hille-Yosida Resolvent Theorem (fully proved, 0 axioms)

For a contraction semigroup $\{S(t)\}_{t \geq 0}$ on a Banach space, the resolvent $R(\lambda) = \int_0^\infty e^{-\lambda t} S(t) dt$ satisfies $(\lambda I - A) R(\lambda) = I$ and $\|R(\lambda)\| \leq 1/\lambda$.

### Bernstein's Theorem (fully proved, 0 axioms)

A completely monotone function on $[0,\infty)$ is the Laplace transform of a unique finite positive measure supported on $[0,\infty)$.

### BCR Theorem 4.1.13 -- Semigroup Bochner (proved, 4 classical axioms)

Bounded continuous positive-definite functions on $[0,\infty) \times \mathbb{R}^d$ are Fourier-Laplace transforms of finite positive measures:

$$F(t, a) = \int_{[0,\infty) \times \mathbb{R}^d} e^{-tp} \, e^{i\langle a, q\rangle} \, d\mu(p, q) \quad \text{for } t \geq 0$$

The proof decomposes into:
- **Spatial Bochner:** For each $t$, apply Bochner's theorem to $a \mapsto F(t,a)$
- **Temporal BCR d=0:** For each Borel set $B$, apply `semigroup_pd_laplace` to $t \mapsto \nu_t(B)$
- **Product assembly:** Combine into a single measure on $[0,\infty) \times \mathbb{R}^d$

## File Structure

| File | Contents | Status |
|------|----------|--------|
| `StronglyContinuousSemigroup.lean` | C0-semigroups, generators, resolvent, Hille-Yosida | **Fully proved** (0 axioms, 0 sorrys) |
| `Bernstein.lean` | Completely monotone functions, Bernstein's theorem | **Fully proved** (0 axioms, 0 sorrys) |
| `FourierPD.lean` | `pd_quadratic_form_of_measure`: Fourier PD | **Fully proved** (0 axioms, 0 sorrys) |
| `BCR_d0.lean` | BCR 4.1.13 for d=0: `semigroup_pd_laplace` | **Proved** (2 classical axioms) |
| `SemigroupGroupExtension.lean` | BCR 4.1.13 general d, group extension | **Proved** (references BCR_d0 + 2 axioms) |
| `Future/BernsteinTheorem.lean` | BCR proof assembly | **Proved** (0 sorrys, wires everything) |

## Axiom Inventory

The core theorems (Hille-Yosida, Bernstein, `pd_quadratic_form_of_measure`) are **fully proved with 0 axioms**. The BCR 4.1.13 proof relies on 4 axioms, all standard analysis facts orthogonal to the PD/semigroup theory:

| Axiom | File | What it says |
|-------|------|-------------|
| `mollifier_exists` | `BCR_d0.lean` | Smooth bump functions exist (standard construction) |
| `mollify_smooth` | `BCR_d0.lean` | Convolution with smooth bump is C^infinity (Leibniz integral rule) |
| `spatial_measures_pd` | `Future/BernsteinTheorem.lean` | nu_t(B) is PD for Borel B (Fourier approximation of indicators) |
| `product_measure_assembly` | `Future/BernsteinTheorem.lean` | Measure kernel construction from Laplace family |

Two additional axioms in `Future/GenerationTheorem.lean` (`domain_isDense`, `hilleYosidaGeneration`) are for future work on the generation theorem and are not used by the BCR proof.

## BCR d=0: Proof Architecture (1326 lines)

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
