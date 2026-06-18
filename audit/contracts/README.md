# Object contracts

One card per **constructed object** (not per theorem). A contract lets a reviewer judge the
object is the right, non-degenerate one — and where it is *proven* vs *asserted* — **without
reading any Lean proof**. Format + rationale:
[`math-commons/formalization-assurance/OBJECT_CONTRACTS.md`](https://github.com/math-commons/formalization-assurance/blob/main/OBJECT_CONTRACTS.md).

Each card: informal description + source, the Lean *signature only*, a `characterization`
(id'd claims incl. ≥1 **anti-degeneracy** clause), and a `known_values` **test matrix**
(`instance → expected → theorem → status`) with status read from `#print axioms`.

> This library is **axiom-free**, so every `known_values` row is `PROVEN_CORE_AXIOMS`
> (no `proven_mod_axioms` hedging). Axioms: none — see [`../../AXIOM_AUDIT.md`](../../AXIOM_AUDIT.md).

## Cards

- [`resolvent.md`](resolvent.md) — the Hille–Yosida resolvent `R(λ)`. Anti-degeneracy: it
  *inverts* `(λ−A)` (`resolventRightInv`), not merely a bounded operator of the right norm.
- [`completelyMonotone.md`](completelyMonotone.md) — `IsCompletelyMonotone` + Bernstein's
  theorem. Anti-degeneracy: the representing measure is unique + finite + on `[0,∞)`.

## Backlog (objects still worth a card)

`StronglyContinuousSemigroup` / generator, `IsSemigroupGroupPD`, the BCR Laplace–Fourier
representation.
