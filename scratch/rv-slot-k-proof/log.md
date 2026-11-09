# rv-slot-k-proof log

## Step 1 (hand check of slot-k §1, §2.1–2.5)

Read slot-k.md §1–2, descent-alt §1–4.1, rv-route-k §2, §4.1–4.3, pc-audit §2, RK1, RK8, RK9,
manuscript lines 975–1070.

- (θ1)–(θ4) proof (§1.1): CORRECT. Re-derived each local case from θc² = 1 − βt², βt² = B/m.
- Prop 0, odd places: CORRECT. Torsion images (−1,−d), (d,2), (−d,−2d); valuation patterns give
  ρ_p(a) = u_p[d_p/p] + v_p λ_p, ρ_p(b) = u_p μ_p + v_p[−d_p/p]; expanding the unit parts gives
  exactly E1_p, E2_p with Monsky's K.
- Prop 0, real place: CORRECT (a₀ = b₀).
- Prop 0, place 2 for c = 5: CORRECT. Recomputed the bits of 5, 2, 7, 3, 1; the point x = 1/4 on
  C_5 (x³ − 25x = −399/64, −399 ≡ 1 mod 16); span = {a_v = 0, a_ε = b_ε, b_v = a_ω}; with (R)
  gives the c = 5 row. 2-adic class of a is (a₁, a₀ + λ·u, μ·u).
- Every actual curve (d₁, d₂) and every virtual configuration in the proof has c = 5, so only the
  c = 5 row is needed: CORRECT.
- Lemma 1: CORRECT.
- Lemma 2 steps 1–4, (2.1), (2.2), reciprocity of 𝒞*, bijectivity: CORRECT. The cancellation in
  step 3 is 2u_{r_ℓ} + u_ℓ + u_g = 0 using step 1; X-internal terms vanish since u_X constant.
- Lemma 3: CORRECT (re-solved; free a₀, u_{p*}, u_{q₀}).
- Step 0 (multiplier): CORRECT.
- Steps 1–6: CORRECT. Step 5: [θ/p] = 0 by (θ4); [p/θ] = [θ/p] + λ_p λ_θ = 0 (θ ≡ 1 mod 4);
  symbols r_p–T vanish by the r_p condition; c_{q₀*} = 3θ ≡ 3, μ_{q₀*} = 1. Step 6:
  u_{r_ℓ} = [|β|/ℓ] + λ_ℓ(x+1), and (θ3) for the signed β gives [|β|/ℓ] = sλ_ℓ.
- Statement vs Route K: manuscript Q_pole with x+ℓ needs e with a point of abscissa exactly
  A = mB on C_e, and a point (Az², ·) on C_{eH}, H = A(A − B²) ≡ m(m − B). Points on C_n, C_{nθ}
  with abscissa in βℚ*² rescale to these (e = n t²/s²): CORRECT.
