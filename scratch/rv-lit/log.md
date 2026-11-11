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

## Step 4: CR3 Props vs definitions and nt-tyz (by reading)
- shortCurve A = [0,0,0,A,0]; argument -(d:ℚ)^2 = -(d^2) (Literature.lean proves ≠ 0 by neg_ne_zero.mpr (pow_ne_zero ..)),
  so the curve is C_d: y^2 = x^3 - d^2 x (the curve of an_check.py). E_n : n y^2 = x^3 - x ≅ C_n over ℚ, same L.
- gCl n = Nat.card (range of squaring on ClassGroup (𝓞 ℚ(√-n))) = #2Cl = TYZ g (nt-tyz Notation). T5bCl = Σ over set
  partitions with one block ≡7, one ≡3, rest ≡1 of Π gCl(d_B) = nt-tyz T_5b. T5aCl (draft) = nt-tyz T_5a.
- nt-tyz Prop N: 𝓛(n)=0 ⇒ T_5a, T_5b even; "in particular T_5b odd ⇒ 𝓛(n) ≠ 0 and ord = 1". I7: 𝓛(n) = 0 iff ord > 1.
  TYZRow5b (ord ≤ 1, ∃F) = contrapositive of Prop N's T_5b half + I7 + Hecke continuation; weaker than Prop N (≤1 not =1).
  TYZThm35ReadingA (∀F, 2 ≤ ord ⇒ T5aCl = 0 ∧ T5bCl = 0) = Prop N first sentence with 𝓛(n)=0 read as ord ≥ 2. Exact.
- Quantifiers: ∃F in TYZRow5b/HeckeContinuation, ∀F elsewhere; harmless by IsLContinuation.eq (F unique).
- lit-adopt: no origin/wip/lit-adopt ref yet.

## Step 5: H side, JHeightBound vs N5 (diophantine_zq.tex) and h-trust Parts E, F
- N5 L381-383: F(u) = u(u+15)(u+20)(u+24)(u+30)(u+60), G(u) = 7u^2+300u+3600 = Fh, Gh of BackToU.lean.
- N5 L510: pullback by J(u) = -57600F(u)^2/G(u)^6 = Jmap; N5 L949-950: "j = a/b, -57600bF(X)^2 - aG(X)^6 has u as a root"
  so the j of F1-F2 is J(u) (the fibre over u). j finite: G has no rational root; j ≠ 0: u ∉ 𝒞.
- Chain: F2 h(j) ≤ 40 h([z_m]) + 22 (L928-932); F3 h([z_m]) ≤ 10^4·2^24·X, X = max(1,h_F(A)) (L934-947);
  E4 X ≤ max(1,C_cm,Q_R^17) M^24 (L900-905, both branches). X ≥ 1 gives h(J(u)) ≤ (40·10^4·2^24+22)·max(1,C_cm,Q_R^17)·M^24
  = JHeightBound at R = D (heightX D = max 1 (max C_cm (Q_D^17)), Q_R = R^(R E0)), S = S_mul. Exact; nothing beyond A1-F3.
- twelve_mul_ratHeight_le: Lean proof does not use u ∉ 𝒞 (true for all u); sample check scratch/rv-lit/f4_check.py:
  30 u (6 contact values, 24 others), max 12h(u)-h(J(u)) = 49.1 ≤ 450, every gcd(57600F_h^2, G_h^6) divides C0. VERIFIED (sample).

## Step 6: Lean runs (load < 21)
- lake build ZInQKernel.RouteK.RankVariants ZInQKernel.Hypotheses.HeightMin: success (9841 jobs).
- lake env lean scratch/wk-cr3/Literature.lean: compiles; all five #print axioms = [propext, Classical.choice, Quot.sound].
- lake env lean scratch/wk-h/BackToU.lean: compiles; sixContactMin_of_jHeightBound axioms standard three.
  (twelve_mul_ratHeight_le is thus a Lean theorem.) SixContactMinAt S_mul = SixContactMin not checked there (scratch does
  not import Mult.S_mul); the adoption must prove it (rfl claimed).
- scratch/rv-lit/Probe.lean compiles: (shortCurve (-(d:ℚ)^2)).a₄ = -(d^2) by rfl; Complex.Gamma 0 = 0;
  analyticOrderAt f z = 0 when f not analytic at z.
