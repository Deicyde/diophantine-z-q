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
