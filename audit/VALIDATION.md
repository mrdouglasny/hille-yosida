# VALIDATION — acceptance and characterization

Evidence that the formalization is **the real thing**, not a look-alike: the named theorems
of the theory hold, the objects pass concrete acceptance checks, and the headlines are
axiom-clean. The companion [`FAITHFULNESS.md`](FAITHFULNESS.md) is the dictionary;
[`contracts/`](contracts/) carries the per-object `known_values` cards. (Assurance
conventions: [`math-commons/formalization-assurance`](https://github.com/math-commons/formalization-assurance).)

## The named theorems (acceptance)

These tie several objects together; proving them certifies that `StronglyContinuousSemigroup`,
the generator/resolvent, `IsCompletelyMonotone`, and the BCR objects are the intended ones.

1. **Hille–Yosida resolvent** — `ContractingSemigroup.resolventRightInv` (`(λ−A)R(λ)=I` on the
   domain) + `hilleYosidaResolventBound` (`‖R(λ)‖ ≤ 1/λ`). ✅ axiom-free. The resolvent is the
   actual Laplace transform `∫₀^∞ e^{−λt}S(t)dt`, so this is a genuine identity, not a rename.
2. **Bernstein's theorem** — `bernstein_theorem`: a completely monotone function is the Laplace
   transform of a **unique finite** positive measure on `[0,∞)`. ✅ axiom-free. Existence
   (Chafái/Prokhorov extraction) **and** uniqueness.
3. **BCR semigroup-Bochner (Thm 4.1.13)** — `semigroupGroupBochner` (existence) +
   `laplaceFourier_unique` (uniqueness): bounded continuous positive-definite functions on
   `[0,∞)×ℝᵈ` are Laplace–Fourier transforms of a unique finite measure. ✅ axiom-free (the
   consumed Bochner results are finite-dimensional and axiom-free).

## Acceptance checks (keeping the statements honest)

- **Resolvent inverts the generator** on a concrete contraction semigroup (e.g. a
  multiplication / uniformly-continuous semigroup): `(λ−A)R(λ) = I` and `‖R(λ)‖ ≤ 1/λ`.
- **Bernstein is non-vacuous**: `e^{−at}` (`a ≥ 0`) is completely monotone and its representing
  measure is the Dirac mass `δ_a`; `t ↦ 1/(1+t)` gives `e^{−x}dx`.
- **BCR reduces to Bernstein at `d = 0`** (`semigroup_pd_laplace`), the consistency check.
- **Uniqueness bites**: two finite measures with equal Laplace–Fourier transforms are equal
  (`laplaceFourier_unique`) — so the representation is well-defined, not just existent.

## Honest limitations

- The **generation theorem / Lumer–Phillips converse** (a dissipative densely-defined operator
  with the range condition *generates* a contraction semigroup) is **not** in the headline set;
  scaffolding is under `HilleYosida/Future/`.
- Results live at the stated generality (contraction semigroups; finite-dimensional spatial
  BCR); the general `M, ω` bounded case and infinite-dimensional spatial Bochner are future work.

## Status

`lake build` clean; `main` sorry-free; **0 project axioms** (`AXIOM_AUDIT.md`); the three
named theorems above are the acceptance certificate.
