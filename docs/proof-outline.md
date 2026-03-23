# Proof Outline: Forward Hille-Yosida Theorem

This document gives an informal summary of the proof of the forward direction of the Hille-Yosida theorem as formalized in [`HilleYosida/StronglyContinuousSemigroup.lean`](../HilleYosida/StronglyContinuousSemigroup.lean).

## The Theorem

**Hille-Yosida (forward direction).** Let $\{S(t)\}_{t \geq 0}$ be a contraction semigroup on a Banach space $X$:
- $S(0) = I$
- $S(s+t) = S(s) \circ S(t)$ for all $s, t \geq 0$
- $S(t)x \to x$ as $t \to 0^+$ for each $x \in X$
- $\lVert S(t) \rVert \leq 1$ for all $t \geq 0$

Then for every $\lambda > 0$:

1. The **resolvent** $R(\lambda)x = \int_0^\infty e^{-\lambda t} S(t)x \, dt$ defines a bounded linear operator on $X$.
2. $R(\lambda)$ maps $X$ into the domain $D(A)$ of the infinitesimal generator $A$.
3. $(\lambda I - A) R(\lambda) = I$ (the resolvent identity).
4. $\lVert R(\lambda) \rVert \leq 1/\lambda$ (the resolvent bound).

## Proof Structure

The proof proceeds in four stages, following [EN] Ch. I–II and [Linares].

### Stage 1: Semigroup foundations

**Uniform boundedness on $[0,1]$** ([EN] Prop. I.5.3). For each $x \in X$, the orbit $\{S(t)x : t \in [0,1]\}$ is bounded: strong continuity at $0$ gives a bound near $0$, and the semigroup property extends it via iteration. The **Banach-Steinhaus theorem** then gives a uniform operator norm bound $M \geq 1$ with $\lVert S(t) \rVert \leq M$ for $t \in [0,1]$.

**Strong continuity everywhere** ([EN] Prop. I.5.3). Right continuity at $t_0$ follows from $S(t_0 + h)x = S(t_0)(S(h)x) \to S(t_0)x$. Left continuity uses the norm bound:

$$\lVert S(t)x - S(t_0)x \rVert = \lVert S(t)(x - S(t_0 - t)x) \rVert \leq \lVert S(t) \rVert \cdot \lVert x - S(t_0 - t)x \rVert \to 0.$$

**Exponential growth bound** ([EN] Prop. I.5.5). Write $t = \lfloor t \rfloor + \mathrm{frac}(t)$, then

$$\lVert S(t) \rVert \leq M^{\lfloor t \rfloor + 1} \leq M \cdot e^{(\log M) \cdot t}.$$

### Stage 2: The resolvent as a Bochner integral

**Integrability.** For a contraction semigroup, $\lVert e^{-\lambda t} S(t)x \rVert \leq e^{-\lambda t} \lVert x \rVert$, which is integrable on $(0, \infty)$ for $\lambda > 0$. Measurability follows from continuity of $t \mapsto S(t)x$ (Stage 1).

**Linearity.** $R(\lambda)$ is linear because the Bochner integral commutes with addition and scalar multiplication.

**Operator norm bound.**

$$\lVert R(\lambda)x \rVert \leq \int_0^\infty e^{-\lambda t} \lVert x \rVert \, dt = \frac{\lVert x \rVert}{\lambda}.$$

The integral is evaluated via substitution $u = \lambda t$ and $\int_0^\infty e^{-t} \, dt = 1$. The resolvent is constructed via `LinearMap.mkContinuous` with bound $1/\lambda$, making `hilleYosidaResolventBound` automatic.

### Stage 3: The integral shift trick

This is the core computation ([EN] Thm. II.1.10, [Linares] eq. 0.15). We show:

$$\lim_{h \to 0^+} \frac{1}{h}\bigl(S(h) R(\lambda)x - R(\lambda)x\bigr) = \lambda R(\lambda)x - x.$$

**Step 1: Push $S(h)$ inside the integral.** By linearity of $S(h)$ and `integral_comp_comm`:

$$S(h)\bigl(R(\lambda)x\bigr) = \int_0^\infty e^{-\lambda t} S(t+h)x \, dt.$$

**Step 2: Factor the exponential.** Using $e^{-\lambda t} = e^{\lambda h} \cdot e^{-\lambda(t+h)}$:

$$= e^{\lambda h} \int_0^\infty e^{-\lambda(t+h)} S(t+h)x \, dt.$$

**Step 3: Translate the variable.** By translation invariance of Lebesgue measure:

$$\int_0^\infty f(t+h) \, dt = \int_h^\infty f(u) \, du.$$

**Step 4: Split the integral.**

$$\int_h^\infty = \int_0^\infty - \int_0^h = R(\lambda)x - \int_0^h e^{-\lambda u} S(u)x \, du.$$

**Step 5: Combine.**

$$S(h) R(\lambda)x - R(\lambda)x = (e^{\lambda h} - 1) \cdot R(\lambda)x - e^{\lambda h} \int_0^h e^{-\lambda u} S(u)x \, du.$$

**Step 6: Divide by $h$ and take $h \to 0^+$.**
- $(e^{\lambda h} - 1)/h \to \lambda$ (derivative of $\exp$ at $0$)
- $e^{\lambda h} \to 1$ (continuity)
- $(1/h) \int_0^h e^{-\lambda u} S(u)x \, du \to e^0 \cdot S(0)x = x$ (FTC for Bochner integrals)

Therefore the limit is $\lambda R(\lambda)x - x$.

### Stage 4: Resolvent identity

**Domain membership.** The existence of the limit in Stage 3 shows $R(\lambda)x \in D(A)$, with $A(R(\lambda)x) = \lambda R(\lambda)x - x$.

**Resolvent identity.** By uniqueness of limits in Hausdorff spaces (`tendsto_nhds_unique`):

$$A\bigl(R(\lambda)x\bigr) = \lambda R(\lambda)x - x \quad \Longrightarrow \quad (\lambda I - A) R(\lambda) x = x.$$

## Key Mathlib lemmas used

| Lemma | Role |
|-------|------|
| `banach_steinhaus` | Uniform boundedness principle for operator norms |
| `ContinuousLinearMap.integral_comp_comm` | Push CLM inside Bochner integral |
| `exp_neg_integrableOn_Ioi` | Exponential decay is integrable |
| `integral_comp_mul_left_Ioi` | Substitution $u = \lambda t$ in set integrals |
| `integral_exp_neg_Ioi_zero` | $\int_0^\infty e^{-t} \, dt = 1$ |
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
