# rv-nt22p-proof log

## Step 1 (reading)
- Read docs/research/nt-22p.md in full; manuscript 1170-1300, 1700-1760.
- Lean read: GoodSlope (PatternSlopes.lean:26), slope_complete, weak_approx_q, tests_integral_old.
- tests_integral_old hypotheses: n, h, M0|h, h≠0, h≠c*, p∈S_b, π|p. No t. CORRECT.
  D g j = testValues (h g) (z g) c depends on h, n only. Unassigned groups use h = 2c*. CORRECT.
  Valuation there is vP π (normalized at prime π of Z[√2]; for p=2, π=√2 so v_π(2)=2), not v_ℓ-extending.

## Step 2 (Lean definitions, pole input)
- PoleCompleteness (Hypotheses/Pole.lean:62): IsSquare B.den, 0<B<1/2, v_p(B)≥4 on S0. As note says. CORRECT.
- SlopePred: q enters only through a = slopeA R0 q. CORRECT (no other constraint on q).
- pole_input_valuations: part1 (S_b) uses ht.old and hq_old (Cp ≤ v_p(q)) to get v(a)=0;
  part2 (selected) uses hq_sel; part3 (others) uses even_padicValRat_contactQuot, independent of q. CORRECT.
- ht.old used only in PoleValuations.lean:126 and GoodSlope.old_le_Cp (no other users found).
- IsOddContactPrime = some v_p(t-c) positive AND odd.
- Lemma P(1): R0 = v^2 ∏(u-cv)/(u-v)^8, v_ℓ(R0)=2e, unit part ∏(1-cv/u) ≡ 1 mod ℓ^e. CORRECT.
  Observation: hypothesis "seven numbers prime to ℓ" is automatic from lowest terms and e ≥ 1
  (u-cv ≡ u, u-v ≡ u mod ℓ). Field 2′ alternative = v_ℓ(t)<0, F(t)>0, (ℓ odd or v_2(t) ≤ -3).
- Lemma P(2): v(1-R0q^2) = e + v_ℓ(2) + v(q-q0) near q0. CORRECT.
- Lemma P(3): v(C) = v(D) - e(k-1); v(RC^2) ≥ 2E+2α+4e-2ek; k=25 gives 2E+2α-46e. CORRECT.
  Θ = 12 + Tr(y), v(Tr y) ≥ min over places > v(12) (split: two embeddings; ramified/inert: σ preserves v). CORRECT.
  v(B) = 2E+2α+2e-2v(12) ≥ 46e+4. CORRECT. With E = E_p it even gives ≥ 103C_p+8 (Lean part1 bound survives).
- ℓ=2: e=1: ∏ ≡ 1+2w mod 8 (w odd) -> 3 or 7; e=2: ≡ 5 mod 8. Never a 2-adic square with η=1 (to verify numerically).
  Note's "often not a square" understates: never.

## Step 3 (computation, scratch/rv-nt22p-proof/lemmaP_check.py, own implementation)
- Part A (exhaustive, u mod 2^(e+6), v = 2^e w, w odd < 64): class of ∏(u-cv) mod 8:
  e=1: {3,7}; e=2: {5}; e≥3: {1}. So with η=1, R0 is NEVER a 2-adic square for e=1,2
  (the note says "often not"). For e=1 and class 7, η=-1 would make it a square; irrelevant since η is fixed by sign.
  CONFIRMS Lemma P(1) at 2 and the necessity of e ≥ 3; e ≤ 2 ≤ B_2 = 4 is covered by field 2.

## Step 4 (Lean consumers of GoodSlope / SlopeRepresentation)
- GoodSlope built in: PatternSlopes.goodSlope_of_values (l.118), pattern_slopes; TwoSlope.goodSlope_of_primeValues
  (l.41, hypothesis hold: v_q(v), v_q(u-v) ≤ B_q), goodSlope_neg_ten (l.199).
- GoodSlope.old consumed only in pole_input_valuations part1 (PoleValuations.lean:126). old_le_Cp has no users.
- SlopeRepresentation consumed by Core, Template, Exact, Assembly, ValueRelation as an opaque hypothesis: unchanged
  if the definition of GoodSlope changes (they never destructure it).

## Step 5 (computation Part B/C; output in lemmaP_check.out)
- Own implementation: exact arithmetic in Q(√2); t=u/v with poles at all of S0 (e_2 in [3,8], others [1,5]), F(t)>0;
  q = m/∏ℓ^e built by CRT from Hensel roots of (R0 ℓ^{-2e})^{-1} mod ℓ^{N+4}, N = 23e+v(12)+2;
  D_gj random in Z[√2] (72 values), ℓ0 = 1 (worst case E=0).
- Part B, 30 samples: α ≥ N at all five primes 30/30; v(Θ)=v(12) 30/30; v(B) ≥ 4 30/30; v(B)=2α+2e-2v(12) exactly 30/30.
- Part C control (root perturbed so α = 19e < 23e): v(B) ≥ 4 fails at every prime in 30/30 (v(B) very negative):
  the threshold 2α-46e > v(12) is really used (when E = 0).
- First run had a bug in my CRT (q*ℓ^e residue inverted); fixed, rerun as above.
- Observation: with the actual ℓ0, E_ℓ = 52C_ℓ+v(12)+4 (=2916+v(12) on S_ht, 732 on catalogue), so the OLD
  argument (q small, α=0) already works for e with 2E_ℓ-46e > v(12): e ≤ 126 on S_ht, e ≤ 31 on catalogue.
  Lemma P is needed only for larger e. Field-2 bounds B_p are far from sharp, but no fixed bound suffices for Green–Tao.
