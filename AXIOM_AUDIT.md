# Axiom audit — hille-yosida

*Last updated 2026-06-18.*

## Purpose

Format + conventions:
[`math-commons/formalization-assurance/AXIOM_AUDIT_FORMAT.md`](https://github.com/math-commons/formalization-assurance/blob/main/AXIOM_AUDIT_FORMAT.md).

---

**Active axioms in build: 0.** This library is **axiom-free** — every headline result
(the Hille–Yosida resolvent identities, Bernstein's theorem, the BCR semigroup-Bochner
theorem and its uniqueness) depends only on Lean's standard three (`propext`,
`Classical.choice`, `Quot.sound`). There are no project axioms to vet, discharge, or track,
so there are no per-axiom records under `audit/vetting/` and no closure-status rows.

*(The `BochnerMinlos` dependency carries its own axioms for the infinite-dimensional
Minlos theory, but the **finite-dimensional Bochner results consumed here are axiom-free**;
the headlines' `#print axioms` is the standard three — see `audit/axiom-report.txt` once
generated, and `Future/` for results deliberately deferred outside the headline set.)*

---

## Active axioms

*(none)*

## Verification

```bash
# the live axiom set (ground truth) — extract once, set-match tracked names:
git grep -hE "^(noncomputable )?axiom " -- 'HilleYosida' \
  | sed -E 's/^(noncomputable )?axiom +([A-Za-z0-9_]+).*/\2/' | sort -u   # → empty
# authoritative: #print axioms of the headlines, via audit/axiom_report.lean
```

> **Machine-gate status.** The reusable assurance gate is wired
> (`.github/workflows/assurance.yml` → the hub's `assure.yml`): build →
> axiom-report-in-sync → sorry-confinement, warn-only at strictness `L1`. Remaining
> (needs a build): commit the golden `audit/axiom-report.txt`
> (`lake env lean audit/axiom_report.lean > audit/axiom-report.txt`) — expected to show the
> standard three for every headline — then raise the policy to `L2` to enforce.
