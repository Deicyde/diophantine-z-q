# d2-check log

## Step 1 (pairs)
- Lean facts to check (RouteK/RankDL.lean `slots_d₂_facts`, `sel_of_selmerCertified`; Slots/Construction.lean `Slots`):
  d₁ = |β q₀ ∏r_p ∏r_ℓ|, d₂ = d₁ θ; d % 8 = 5, squarefree, β | d, SelmerCertified d β (#Σ(𝒞_d)=8, class of β a first coordinate).
  Aux primes in Lean only need: prime, residue mod 8, ∤ 2βθ, distinct, prescribed Legendre bits (no S0 restriction).
- pairs.py: β odd sqf, ω ≤ 3, primes < 200, |β| ≡ 7 (8); θ sqf ≡ 1 (8), prime to 2730β, square mod 3,5,7,13, log-uniform in [17,10^6);
  primitive solution of D² − θY² = β(2730²c')² (qfsolve/qfparam, u/v near a real root of c(u,v)); m random signed divisor of 2730, sign(m)=sign(β);
  B = mβc²/D². Rechecked: descent_search.admissible(B), sqfQ(mB)=β, sqfQ(m(m−B))=θ.
- Run: `pairs.py 30 2026` → pairs.json (30 pairs, ~6 min). θ range 15649..897121 (conic solvability + local conditions push θ up). Output out_pairs.txt.

## Step 2 (slots)
- slots.py: slotk.construct with prime_with replaced by the smallest prime q ≡ cls (8) meeting slotk's symbol constraints; p0 = min P.
  Each slot choice re-checked against every field of Lean `RouteK.Slots` (legBit p a = bit of (a/p)): 30/30 OK (14–62 field checks each).
- d₁ = |β|q₀∏r, d₂ = d₁θ. Kept (d₁, d₂ < 10^12): 10 of 30 pairs (#3,4,5,7,11,15,17,18,22,23), all with ω(β)=ω(θ)=1 (one slot r_ℓ, no r_p);
  #4 and #18 share β=−191, d₁=9741 (different θ). 20 curves, 19 distinct d.
- Slot facts on kept curves (20 curves): d % 8 = 5, squarefree, β | d, exact 2-descent dim Sel₂ = 3 with β ∈ π₁: all 20 OK.
- Output slots.json, out_slots.txt.
