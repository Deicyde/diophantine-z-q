# d2-check log

## Step 1 (pairs)
- Lean facts to check (RouteK/RankDL.lean `slots_d₂_facts`, `sel_of_selmerCertified`; Slots/Construction.lean `Slots`):
  d₁ = |β q₀ ∏r_p ∏r_ℓ|, d₂ = d₁ θ; d % 8 = 5, squarefree, β | d, SelmerCertified d β (#Σ(𝒞_d)=8, class of β a first coordinate).
  Aux primes in Lean only need: prime, residue mod 8, ∤ 2βθ, distinct, prescribed Legendre bits (no S0 restriction).
- pairs.py: β odd sqf, ω ≤ 3, primes < 200, |β| ≡ 7 (8); θ sqf ≡ 1 (8), prime to 2730β, square mod 3,5,7,13, log-uniform in [17,10^6);
  primitive solution of D² − θY² = β(2730²c')² (qfsolve/qfparam, u/v near a real root of c(u,v)); m random signed divisor of 2730, sign(m)=sign(β);
  B = mβc²/D². Rechecked: descent_search.admissible(B), sqfQ(mB)=β, sqfQ(m(m−B))=θ.
- Run: `pairs.py 30 2026` → pairs.json (30 pairs, ~6 min). θ range 15649..897121 (conic solvability + local conditions push θ up). Output out_pairs.txt.
