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
