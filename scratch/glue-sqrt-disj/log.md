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

## Level.lean (compiled 00:50 PST; axioms propext, Classical.choice, Quot.sound)
- `coprime_pow_sub_one`: p ≥ 2, n ≥ 1 ⇒ p coprime to p^n - 1. VERIFIED.
- `orderOf_unit_pow_sub_one`: p ≥ 2, n ≥ 1 ⇒ ord_{p^n-1}(p) = n. VERIFIED. (With n = 2f: m' = p^{2f}-1 has ord = 2f.)
- `dvd_pow_orderOf_sub_one`: p coprime m ⇒ m ∣ p^{t·ord_m(p)} - 1 for every t (t = 2: m ∣ p^{2f}-1). VERIFIED.

## Disj.lean (compiled 00:48 PST; axioms propext, Classical.choice, Quot.sound; = glue-sqrt-local Unramified.lean + Ram.lean + section Disj)
Ambient: [Algebra ℤ_[p] L] [IsScalarTower ℤ_[p] ℚ_[p] L] [FiniteDimensional ℚ_[p] L] [IsGalois ℚ_[p] L], [NeZero m], hcop : p.Coprime m,
[IsCyclotomicExtension {p^k * m} ℚ_[p] L].
- `galToProd k m : Gal(L/ℚ_p) →* (ZMod p^k)ˣ × (ZMod m)ˣ`: autToPow on ζ^m (primitive p^k-th) and on ζ^{p^k} (primitive m-th), ζ = zeta (p^k m).
- `galToProd_injective`: VERIFIED (Bezout: ζ = (ζ^m)^A (ζ^{p^k})^B; autToPow_injective for ζ).
- `range_galToProd`: range = ⊤ × zpowers(p mod m). VERIFIED (≤ from range_autToPow_eq_zpowers'; card from totient_mul_orderOf_le_finrank).
- `galEquivProd : Gal(L/ℚ_p) ≃* (⊤ : Subgroup (ZMod p^k)ˣ).prod (zpowers (p mod m))`. VERIFIED.
- `finrank_eq_totient_mul_orderOf`: [L:ℚ_p] = φ(p^k)·ord_m(p). VERIFIED.
