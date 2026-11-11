# rv-lit log

## Step 1: Mathlib definitions read (LFunction.lean, Reduction.lean, ArithmeticFunction/LFunction.lean)
- localPolynomial: minimal model over completion R; q = Nat.card residue field; a = q+1-Nat.card (reduction).toAffine.Point
  (Point = zero | some nonsingular, so the count includes infinity); good: 1-aT+qT^2; split mult: 1-T; nonsplit: 1+T; else 1.
- IsMinimal: Δ-valuation maximal (multiplicative valuation) among integral models = Silverman minimal.
- HasGoodReduction: v(Δ)=1 (unit). Multiplicative: v(Δ)<1, v(c4)=1. Additive: v(Δ)<1, v(c4)<1. = Silverman VII.5.1 (all residue chars).
- Split: c4 T^2 + a1 c4 T - (54 b6 - 3 b2 b4 + a2 c4) splits over residue field.
  Hand check: node (x0,y0) tangent slopes solve T^2 + a1 T - (3x0+a2) = 0 (any char); with node translated from (0,0)
  (a3=a4=a6=0, b4=b6=0, c4=b2^2) by x = x'+r: c4*(-r) = -r b2^2 = 18 b6' - b2' b4' identically over Z, so
  c4 x0 = 18 b6 - b2 b4 at the node in every characteristic (the node is rational: unique singular point, F_p perfect).
- localPowerSeries = invOfUnit poly 1 (constant coeff 1 in all four cases). ofPowerSeries q f: n = q^k -> coeff k, else 0 (q>1).
  q = p for HeightOneSpectrum (𝓞 ℚ) (residue field of Z_p is F_p): no Nat.card junk.
- eulerProduct = tprod in the pointwise-discrete topology (private instance); Multipliable since each coefficient
  stabilizes (tendsTo_eulerProduct_ofPowerSeries, Northcott q). So LFunction = formal ∏_p (1/f_p(p^-s)).
- LSeries = Mathlib LSeries (tsum of f n / n^s, term 0 = 0); absolutely summable for Re s > 3/2 (Hasse).

## Step 2: a_n check (scratch/rv-lit/an_check.py) — VERIFIED
- Mathlib recipe transcribed (global minimal model, Δ/c4 valuations, Mathlib's split polynomial, point count with infinity,
  1/f_p expansion) vs PARI ellan, n <= 300, 29 curves: C_d for d = 5,13,21,29,37,53,1,6,7,15,34 (all bad primes additive,
  conductors 32d^2 for odd d, 64·17^2 for d=34) and 18 others with split AND nonsplit multiplicative reduction at p=2
  (26b1, 34a1, [1,1,1,1,1] split; 14a1, 26a1, 30a1 nonsplit) and p=3 (21a1, 30a1 split; 15a1, 24a1, 33a1 nonsplit),
  plus non-minimal models. 0 mismatches.

## Step 3: functional equation data (scratch/rv-lit/fe_check.py) — VERIFIED (numerically)
- First 30 squarefree d ≡ 5 (mod 8) up to 285: conductor 32d^2 and ellrootno -1 for all 30.
- d = 5, 13, 21: |Λ(2-s)+Λ(s)| < 2e-17 at s = 0.3+0.7i, 1.2-2i, 0.9 with Λ = N^{s/2}(2π)^{-s}Γ(s)L(s) (PARI lfun).
- L(C_d, 2) = 0.911, 1.024, 0.904 ≠ 0: the unrestricted FunctionalEquation5 at s = 0 (Mathlib Γ(0) = 0 so Λ(0) = 0,
  Λ(2) ≠ 0) is false; confirms the lit-adopt restriction is needed.
