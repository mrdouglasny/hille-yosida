# FAITHFULNESS — a dictionary between semigroup/Bochner theory and the Lean formalization

For a reader who knows the mathematics (Engel–Nagel; Berg–Christensen–Ressel; Widder) but
not Lean: what each Lean object/theorem means, where the formal statement differs from the
textbook, and the theorem that reconciles them — so you can trust the statements **without
reading the proofs**. Per-file informal write-ups live under [`../summary/`](../summary/);
this is the cross-cutting map. (Assurance conventions:
[`math-commons/formalization-assurance`](https://github.com/math-commons/formalization-assurance).)

## The objects

| Concept (textbook) | Lean | Notes |
|---|---|---|
| C₀-semigroup `{S(t)}_{t≥0}` on a Banach space | `StronglyContinuousSemigroup` | `S 0 = id`, `S (s+t) = S s ∘ S t`, strong continuity (`strongContAt`). |
| Contraction semigroup (`‖S t‖ ≤ 1`) | `ContractingSemigroup extends StronglyContinuousSemigroup` | the contraction bound is a field; the resolvent theory lives here. |
| Generator `A`, domain `D(A)` | `StronglyContinuousSemigroup.generator` / `.domain` | `A u = lim_{t→0} (S t u − u)/t`; the (unbounded) generator on its dense domain. |
| Resolvent `R(λ) = ∫₀^∞ e^{−λt} S(t) dt` | `ContractingSemigroup.resolvent` | a Bochner integral of the operator-valued map. |
| Completely monotone `f` (`(−1)ⁿ f⁽ⁿ⁾ ≥ 0`) | `IsCompletelyMonotone` | on `(0,∞)`; the hypothesis of Bernstein's theorem. |
| Positive-definite on `[0,∞)×ℝᵈ` (BCR) | `IsSemigroupGroupPD` | the involutive-semigroup positive-definiteness of BCR §4.1. |

## The theorems

| Statement (textbook) | Lean | Reference |
|---|---|---|
| `(λ − A) R(λ) = I` on `D(A)` | `ContractingSemigroup.resolventRightInv` (+ `resolventMapsToDomain`) | Engel–Nagel (Hille–Yosida) |
| `‖R(λ)‖ ≤ 1/λ` | `hilleYosidaResolventBound` | Engel–Nagel |
| Completely monotone ⇒ Laplace transform of a unique finite positive measure | `bernstein_theorem` | Widder, Ch. IV; Bernstein |
| BCR 4.1.13 existence (Laplace–Fourier representation) | `semigroupGroupBochner` (+ `semigroupGroupBochnerExtension`) | Berg–Christensen–Ressel, Thm 4.1.13 |
| BCR uniqueness of the representing measure | `laplaceFourier_unique` | Berg–Christensen–Ressel |

## Encoding notes (where formal ≠ casual)

- **Unbounded generator.** `A` is a partial/`LinearPMap`-style operator on a dense domain,
  not a total map; statements quantify over `D(A)`.
- **Resolvent as a Bochner integral.** `R(λ)` is the genuine `∫₀^∞ e^{−λt} S(t) dt`, so the
  identities are integral computations, not formal manipulations.
- **BCR Bochner uses a finite-dimensional Bochner theorem** from the `BochnerMinlos`
  dependency; the consumed results are **axiom-free** (the package's axioms are in its
  infinite-dimensional Minlos part). Net: the headlines' `#print axioms` is the standard three.

## Audit recipe

`lake build` clean + `main` sorry-free (`audit/sorry-allowlist.txt` is empty);
`lake env lean audit/axiom_report.lean` shows the standard three for every headline; the
acceptance/value checks are in [`VALIDATION.md`](VALIDATION.md) and the object contracts in
[`contracts/`](contracts/).
