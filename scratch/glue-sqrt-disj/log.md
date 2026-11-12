# glue-sqrt-disj results log

## Ram.lean (compiled 00:48 PST; axioms propext, Classical.choice, Quot.sound)
- `prime_mem_pow_totient`: R domain, Q prime, z primitive p^k-th root, p ∈ Q ⇒ p ∈ Q^φ(p^k). VERIFIED.
  (p = Φ_{p^k}(1) = ∏_{μ primitive}(1-μ); some 1-μ₀ ∈ Q by primality; every μ = μ₀^i so 1-μ ∈ (1-μ₀).)
- `totient_mul_orderOf_le_finrank`: L/ℚ_p finite Galois containing a primitive p^k-th root ζ and a
  primitive m-th root η, p coprime to m ⇒ φ(p^k)·ord_m(p) ≤ [L:ℚ_p]. VERIFIED.
  Proof: Mathlib's Galois fundamental identity `Ideal.ncard_primesOver_mul_ramificationIdxIn_mul_inertiaDegIn`
  for S = integralClosure ℤ_p L (Dedekind: `integralClosure.isDedekindDomain`; flat: instance);
  e = multiplicity Q (pS) ≥ φ(p^k) by `prime_mem_pow_totient`; f ≥ ord_m(p) since #(S/Q) = p^f
  (`Ideal.cardQuot_pow_inertiaDeg`), so η^(p^f) ≡ η mod Q, and m-th roots of unity separate mod Q.
  Locality of S is NOT needed for this bound.
