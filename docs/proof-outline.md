# Proof Outline

This document summarizes the proofs formalized in this project. All theorems are fully proved with 0 sorry's and 0 axioms.

## 1. Hille-Yosida Forward Theorem

**File:** `StronglyContinuousSemigroup.lean` (867 lines)

For a contraction semigroup $\{S(t)\}_{t \geq 0}$ on a Banach space $X$:

1. **Banach-Steinhaus** → uniform operator norm bound on $[0,1]$
2. **Strong continuity** at all $t_0 \geq 0$ from strong continuity at $0$
3. **Generator** $Ax = \lim_{t \to 0^+} (S(t)x - x)/t$ on domain $D(A)$
4. **Resolvent** $R(\lambda) = \int_0^\infty e^{-\lambda t} S(t)x\, dt$ via Bochner integral
5. **$R(\lambda)$ maps to $D(A)$** via integral shift trick
6. **$(\lambda I - A)R(\lambda) = I$** from FTC
7. **$\lVert R(\lambda) \rVert \leq 1/\lambda$** from contraction bound under integral

## 2. Bernstein's Theorem

**File:** `Bernstein.lean` (2444 lines)

**Statement:** If $f : [0,\infty) \to \mathbb{R}$ is completely monotone, then $f(t) = \int_0^\infty e^{-tp}\, d\mu(p)$ for a unique finite positive measure $\mu$.

**Proof (Chafaï 2013):**
1. **Taylor integral remainder** (new, not in Mathlib): $f(b) - T_n(a,b) = \int_a^b \frac{(b-t)^n}{n!} f^{(n+1)}(t)\, dt$
2. **CM properties + IBP recursion:** $f \geq 0$, $f' \leq 0$, $f(t) \leq f(0)$, boundary decay $T^k f^{(k)}(T) \to 0$
3. **Chafaï identity:** $f(x) - L = \int \varphi_n(xp)\, d\tilde\sigma_n(p)$ where $\varphi_n \to e^{-xp}$
4. **Prokhorov extraction:** normalize to `ProbabilityMeasure`, use `isCompact_iff_isSeqCompact`
5. **Diagonal convergence + packaging:** $\mu = \mu_0 + L \cdot \delta_0$

## 3. BCR d=0: Semigroup PD → Laplace

**File:** `BCR_d0.lean` (1503 lines)

**Statement:** Bounded continuous semigroup-PD functions on $[0,\infty)$ are Laplace transforms.

**Proof:**
1. **PD → alternating differences** (Vandermonde convolution + convexity bootstrap)
2. **Iterated integral bridge:** forward differences = iterated integrals of derivatives
3. **Mollifier smoothing** → `IsCompletelyMonotone`
4. **Apply `bernstein_theorem`** to each mollified function
5. **Prokhorov extraction** → weak limit measure
6. **Verification** → Laplace representation

## 4. BCR 4.1.13 General d

**File:** `BCR_General.lean` (2822 lines)

**Statement:** Bounded continuous PD functions on $[0,\infty) \times \mathbb{R}^d$ are Fourier-Laplace transforms.

**Proof (decomposition):**
1. **Spatial Bochner:** for each $t$, apply `bochner_theorem` to $a \mapsto F(t,a)$
2. **Temporal BCR d=0:** for each Borel $B \subseteq \mathbb{R}^d$, apply `semigroup_pd_laplace` to $t \mapsto \nu_t(B)$
3. **Product measure assembly:** combine into $\mu$ on $[0,\infty) \times \mathbb{R}^d$

## 5. Group Extension

**File:** `SemigroupGroupExtension.lean` (271 lines)

Given $\mu$ from BCR, define $G(t,a) = \int e^{itp} e^{i\langle a,q\rangle}\, d\mu(p,q)$ (Fourier kernel). Show: bounded, continuous, positive-definite on $\mathbb{R} \times \mathbb{R}^d$.
