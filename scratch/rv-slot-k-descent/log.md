# rv-slot-k-descent log

## Step 1 (read slot-k.md in full, descent-alt §§1-4.7, pc-audit §2, RK1, RK3, RK8, RK9, rv-route-k §4.1-4.3)

## Step 2 (Proposition 0 from first principles, by hand)
Setup: C_d: y^2 = x(x-d)(x+d), e1=0, e2=d, e3=-d, d>0 odd squarefree. Kummer (x-e1, x-e2) = (x, x-d)
(Silverman X.1.4). Torsion images: (0,0) -> ((e1-e2)(e1-e3), e1-e2) = (-d^2, -d) ~ (-1,-d);
(d,0) -> (d, (e2-e1)(e2-e3)) = (d, 2d^2) ~ (d,2); (-d,0) -> (-d,-2d). CORRECT.
- p odd, p ∤ d: good reduction, local image = unramified classes; classes built from -1,2,primes of d are
  units at p. CORRECT (standard).
- p | d odd: #E(Q_p)/2E(Q_p) = #E(Q_p)[2] = 4. Valuation vectors of (d,2),(-1,-d) are (1,0),(0,1): independent,
  so the image is exactly the torsion span. Matching unit parts gives
  E1_p: sum_{y≠p}[y/p](u_y+u_p) + λ_p v_p = a0 λ_p + a1 μ_p,
  E2_p: μ_p u_p + sum_{y≠p}[y/p](v_y+v_p) + λ_p v_p = b0 λ_p + b1 μ_p.  Matches slot-k (E1),(E2) and descent-alt
  A u + Dλ v, Dμ u + (A+Dλ) v. CORRECT.
- ∞: d>0, E(R)/2E(R) order 2, image {(+,+),(-,-)} -> a0=b0. CORRECT.
- 2: #E(Q2)/2E(Q2) = 4*2 = 8 (dim 3). Bits (v, ε, ω) with ε=(w-1)/2, ω=(w^2-1)/8: -1=(0,1,0), 2=(1,0,0),
  p=(0,λ_p,μ_p). Class of a = (a1, a0+λ·u, μ·u). Image depends on d mod Q2*^2 (scaling (t^2x,t^3y) preserves
  Kummer classes). Third generator, uniform in d odd: x=1/4: x(x^2-d^2) = (1-16d^2)/64, 1-16d^2 ≡ 1 (16) so a
  2-adic square; x-d = (1-4d)/4 ≡ 5. So (1,5) = (0,0,0|0,0,1) always in the image.
  d≡1: gens (0,0,0|1,0,0),(0,1,0|0,1,0),(0,0,0|0,0,1): a_v=0, a_ω=0, a_ε=b_ε  -> a1=0, μ·u=0, λ·u=λ·v (with R).
  d≡3: (0,1,1|1,0,0),(0,1,0|0,0,1),(0,0,0|0,0,1): a_v=0, b_ε=0, a_ω=b_v -> a1=0, b0=λ·v, b1=μ·u.
  d≡5: (0,0,1|1,0,0),(0,1,0|0,1,1),(0,0,0|0,0,1): a_v=0, a_ε=b_ε, b_v=a_ω -> a1=0, λ·u=λ·v, b1=μ·u.
  d≡7: (0,1,0|1,0,0),(0,1,0|0,0,0),(0,0,0|0,0,1): a_v=0, a_ω=0, b_ε=0 -> a1=0, μ·u=0, b0=λ·v.
  All four rows agree with descent-alt §4.1 and slot-k §2.1 (D). CORRECT. Note: the rows for c=1,5 use (R) to
  rewrite a_ε=b_ε as λ·u=λ·v; legitimate since (R) is part of the system.

## Step 3 (own exact descent sel2.py; own Prop 0 system prop0.py; differential test t_prop0.py)
- sel2.py: local images at oo, 2, p|d from sampled genuine local points (x with x(x^2-d^2) a Q_v-square),
  stopping at the known size (1, 3, 2); no use of Prop 0 or of the torsion-span argument.
- prop0.py: the system as derived in step 2.
- t_prop0.py (out_t_prop0.txt): 30 random odd squarefree d, 1-5 primes < 400, 8/8/7/7 in classes 1,3,5,7 mod 8.
  Same Selmer space (not just dimension) and same pi_1 membership for every signed divisor of d: 0 mismatches.
  PARI ellrank on the first 10: C = 2 + r2 + s equals dim Sel_2 in 10/10.
  => Prop 0 CORRECT (hand proof step 2 + computation).

## Step 4 (certificate vs Kriz / corank lemma / RK9)
- lem:corank (manuscript l.1072) is stated for any E/Q with full rational 2-torsion: dim Sel2 = 3 => corank 1.
  Its proof (r + dim Sha[2] = 1; Sha[2^oo] = div + F, F[2] even-dim by Cassels-Tate) is CORRECT and applies to C_d.
- Kriz Thm 10.13 (CM by Z[i] over Q(i), p = 2 ramified): corank 1 => rank 1, Sha finite. f0 >= 4 holds since
  |n| has >= 2 odd primes (beta and q0), |n| >= 21. Then r + dim Sha[2] = 1 gives Sha[2]=0 and
  E(Q)/2E(Q) = Sel2 (dim 3). RK9: the class with first coordinate beta is the image of a non-torsion point
  (P + 2Q), whose abscissa is in beta Q*^2. CORRECT.
- Minor: slot-k 1.2 cites "Theorems 10.13 and 10.17(2)"; pc-audit RK1 recommends 10.13 alone (10.17 sits under
  part-(1) header hypotheses). slot-k does not state the f0 >= 4 check (trivial here). Cosmetic.
- Torsion certificate never used by the construction (n/beta != +-1). Fine.

## Step 5 (slot-k 1.1, 2.2-2.5 by hand)
- (theta1)-(theta4) from theta c^2 = 1 - beta t^2, v_p(B/m) >= 3 on S0: CORRECT.
- Step 0 multiplier: v2(m) = v2(B) mod 2, |beta| = m_odd*b mod 8 (odd squares = 1 mod 8), odd parts 1,3,5,7 and
  2,6,10,14 all divide 2730: CORRECT.
- Lemma 1: CORRECT (E1_r, E2_r give u_r=u_y, v_r=v_y; only rows y contain r-terms, which vanish).
- Lemma 2: steps 1-4 CORRECT. Checked E2-sum: sum_x mu_x u_x = mu_{g*} u_g after gluing; r-terms in
  sum_{x in X}(Kv)_x are sum_l ([r_l/g](v_r+v_g) + [r_l/l](v_r+v_l)) = 0; X-internal terms vanish. (2.1), (2.2)
  rederived from E1_l, E2_l. Reciprocity of C*: lambda, mu are characters of (Z/8)*. CORRECT.
- Lemma 3: rows rederived, c = 21 = 5, dim 3, sigma_0. CORRECT.
- Theorem steps 1-6: symbol bookkeeping checked (r_l only linked to q0 inside S1; r_p conditions = Lemma 2
  hypotheses incl. later slots by reciprocity; q0* class 3*theta = 3; Jacobi (p/theta) = (theta/p) since
  theta = 1 mod 4, theta > 0; u_{r_p} = [q0/p]+1+lam_p x = 0; u_{r_l} = lam_l (s+x+1) = 0). CORRECT.
