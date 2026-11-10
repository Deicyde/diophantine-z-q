# pd-sieve log
- Leaf 1: vendored AuxResults, Basic, Selberg, SelbergBounds from PNT v4.35.0 (only import lines changed). Builds. `#print axioms SelbergSieve.selberg_bound_simple`: propext, Classical.choice, Quot.sound.
- Leaf 2 plan (run 2): pd-lean-1/2 have no Lean yet, so the bound is stated for a self-contained set
  `GaussBad ℓ = {p prime | ∃ c e : ℤ, p = c²+e², ℓ ∣ c, ℓ ∣ p+1}` (BadSet ⊆ GaussBad by Prop 1.6).
  Modules ZInQKernel/Density/GaussSieve/{Harmonic,SelbergSum,Local,Box}.lean + Density/GaussSieve.lean.
  S lower bound route (simpler than note): S ≥ Σ_{m≤w, rad m | P} τ(m)/m (Euler expansion; g(q) = Σ_{k≥1}(k+1)/q^k exactly)
  ≥ (3/5) Σ_{m≤w, 𝒮m} τ(m)/m ≥ (3/5)(1/4) R(w), R(w)=Σ r(n)/n ≥ (2/3) log w by pairing χ₄ terms (no Euler–Mascheroni);
  r = h∗v with h = τ·1_𝒮, v = r·1_𝒯, Σ v(m)/m ≤ 4 (v supported on 2^a s², v ≤ 1). So S ≥ log w / 10.
- Harmonic (Claims A,B), SelbergSum (S ≥ Στ/m), Local (Lemma 4.3) compile.
