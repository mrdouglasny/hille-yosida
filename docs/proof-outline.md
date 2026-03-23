# Proof Outline: Forward Hille-Yosida Theorem

This document gives an informal summary of the proof of the forward direction of the Hille-Yosida theorem as formalized in [`HilleYosida/StronglyContinuousSemigroup.lean`](../HilleYosida/StronglyContinuousSemigroup.lean).

## The Theorem

**Hille-Yosida (forward direction).** Let {S(t)} be a contraction semigroup on a Banach space X (i.e., S(0) = I, S(s+t) = S(s)S(t), S(t)x -> x as t -> 0+, and ||S(t)|| <= 1). Then for every lambda > 0:

1. The **resolvent** R(lambda)x = integral from 0 to infinity of e^{-lambda t} S(t)x dt defines a bounded linear operator on X.
2. R(lambda) maps X into the domain D(A) of the infinitesimal generator A.
3. (lambda I - A) R(lambda) = I (the resolvent identity).
4. ||R(lambda)|| <= 1/lambda (the resolvent bound).

## Proof Structure

The proof proceeds in four stages, following Engel-Nagel [EN] Ch. I-II and Linares [Linares].

### Stage 1: Semigroup foundations

**Uniform boundedness on [0,1]** ([EN] Prop. I.5.3). For each x in X, the orbit {S(t)x : t in [0,1]} is bounded: strong continuity at 0 gives a bound near 0, and the semigroup property extends it via iteration. The **Banach-Steinhaus theorem** (uniform boundedness principle) then gives a uniform operator norm bound M >= 1 with ||S(t)|| <= M for t in [0,1].

**Strong continuity everywhere** ([EN] Prop. I.5.3). Right continuity at t_0 follows from S(t_0 + h)x = S(t_0)(S(h)x) -> S(t_0)x. Left continuity uses the operator norm bound: ||S(t)x - S(t_0)x|| = ||S(t)(x - S(t_0-t)x)|| <= ||S(t)|| * ||x - S(t_0-t)x|| -> 0.

**Exponential growth bound** ([EN] Prop. I.5.5). Write t = floor(t) + frac(t), then ||S(t)|| <= M^{floor(t)+1} <= M * e^{(log M) * t}. This gives ||S(t)|| <= M * e^{omega * t} with omega = log M.

### Stage 2: The resolvent as a Bochner integral

**Integrability.** For a contraction semigroup, ||e^{-lambda t} S(t)x|| <= e^{-lambda t} ||x||, which is integrable on (0, infinity) for lambda > 0. The integrand is also strongly measurable (the map t -> S(t)x is continuous by Stage 1, hence measurable).

**Linearity.** R(lambda) is linear because the Bochner integral commutes with addition (by `integral_add`, using integrability) and scalar multiplication (by `integral_smul`).

**Operator norm bound.** ||R(lambda)x|| <= integral of ||e^{-lambda t} S(t)x|| dt <= ||x|| * integral of e^{-lambda t} dt = ||x||/lambda. The integral evaluation uses substitution u = lambda * t (via `integral_comp_mul_left_Ioi`) and integral of e^{-t} on (0, infinity) = 1 (via `integral_exp_neg_Ioi_zero`). The resolvent is constructed via `LinearMap.mkContinuous` with bound 1/lambda, making the Hille-Yosida bound `hilleYosidaResolventBound` automatic.

### Stage 3: The integral shift trick

This is the core computation ([EN] Thm. II.1.10, [Linares] eq. 0.15). We show that the generator difference quotient (1/h)(S(h) R(lambda)x - R(lambda)x) converges to lambda * R(lambda)x - x as h -> 0+.

**Step 1: Push S(h) inside the integral.** By `ContinuousLinearMap.integral_comp_comm`:

S(h)(R(lambda)x) = integral of e^{-lambda t} S(h)(S(t)x) dt = integral of e^{-lambda t} S(t+h)x dt.

**Step 2: Factor the exponential.** Using e^{-lambda t} = e^{lambda h} * e^{-lambda(t+h)}, the integral becomes e^{lambda h} * integral of e^{-lambda(t+h)} S(t+h)x dt.

**Step 3: Translate the variable.** By translation invariance of Lebesgue measure (`integral_add_right_eq_self`): integral over (0, infinity) of f(t+h) dt = integral over (h, infinity) of f(u) du.

**Step 4: Split the integral.** integral over (h, infinity) = integral over (0, infinity) - integral over (0, h] = R(lambda)x - integral over (0, h].

**Step 5: Combine.** S(h) R(lambda)x - R(lambda)x = (e^{lambda h} - 1) * R(lambda)x - e^{lambda h} * integral from 0 to h of f.

**Step 6: Divide by h and take the limit.** As h -> 0+:
- (e^{lambda h} - 1)/h -> lambda (derivative of exp at 0, via `HasDerivAt.tendsto_slope_zero_right`)
- e^{lambda h} -> 1 (continuity of exp)
- (1/h) * integral from 0 to h of f -> f(0) = x (FTC for Bochner integrals, via `integral_hasDerivAt_of_tendsto_ae_right`; requires showing f is continuous at 0 from both sides, which uses `continuous_piecewise` with the frontier condition f(0) = x)

Therefore the limit is lambda * R(lambda)x - x.

### Stage 4: Resolvent identity

**Domain membership.** The existence of the limit in Stage 3 shows R(lambda)x is in D(A), with A(R(lambda)x) = lambda * R(lambda)x - x.

**Resolvent identity.** By `tendsto_nhds_unique`, the generator value Classical.choose equals our explicit limit, giving A(R(lambda)x) = lambda * R(lambda)x - x. Rearranging: lambda * R(lambda)x - A(R(lambda)x) = x, i.e., (lambda I - A) R(lambda) = I.

## Key Mathlib lemmas used

| Lemma | Role |
|-------|------|
| `banach_steinhaus` | Uniform boundedness principle for operator norms |
| `ContinuousLinearMap.integral_comp_comm` | Push CLM inside Bochner integral |
| `exp_neg_integrableOn_Ioi` | Exponential decay is integrable |
| `integral_comp_mul_left_Ioi` | Substitution u = lambda * t in set integrals |
| `integral_exp_neg_Ioi_zero` | Evaluate integral of e^{-t} = 1 |
| `integral_add_right_eq_self` | Translation invariance of Lebesgue measure |
| `norm_integral_le_of_norm_le` | Norm bound for Bochner integrals |
| `HasDerivAt.tendsto_slope_zero_right` | One-sided derivative gives slope limit |
| `integral_hasDerivAt_of_tendsto_ae_right` | FTC for Bochner integrals |
| `continuous_piecewise` | Piecewise function is continuous |
| `tendsto_nhds_unique` | Uniqueness of limits in Hausdorff spaces |
| `LinearMap.mkContinuous_norm_le` | Operator norm from construction bound |

## References

- [EN] Engel-Nagel, *One-Parameter Semigroups for Linear Evolution Equations*, GTM 194, Springer (2000). Ch. I §5, Ch. II §1.
- [Linares] F. Linares, "The Hille-Yosida Theorem", IMPA lecture notes (2021).
