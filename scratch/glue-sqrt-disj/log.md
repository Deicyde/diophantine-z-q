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
- `galToProd_fst_spec` / `galToProd_snd_spec`: g x = x^{a.val} for all x with x^{p^k} = 1 (a = first component); g y = y^{b.val} for y^m = 1. VERIFIED.
- `galToProd_restrict`: K of level p^{k'} m' (own ambient instances, [Algebra K L] [IsScalarTower ℚ_[p] K L]), k' ≤ k, m' ∣ m:
  galToProd_K (g.restrictNormal K) = (castHom of first comp, castHom of second comp) of galToProd_L g. VERIFIED (compiled 00:50 PST).
- `galCommGroup k m hcop`: CommGroup on Gal(ℚ_p(μ_{p^k m})/ℚ_p) (embeds in (ZMod p^k)ˣ × (ZMod m)ˣ).
- **`sqrt_criterion_level`** (compiled 00:52 PST; axioms propext, Classical.choice, Quot.sound): every prime p incl. 2.
  K level p^k m, L level p^{k+1} m' (both IsCyclotomicExtension, own ambient instances), [Algebra K L] [IsScalarTower ℚ_[p] K L],
  p coprime m, m', m ∣ m', ord_{m'}(p) = 2·ord_m(p); τ ∈ Gal(K/ℚ_p) with galToProd τ = (-1, 1); χ : Additive Gal(K/ℚ_p) →+ ℚ/ℤ.
  Then (∃ ψ : Additive Gal(L/ℚ_p) →+ ℚ/ℤ, ∀ g, 2•ψ(g) = χ(g|_K)) ↔ χ(τ) = 0. VERIFIED.
  Proof: exists_half_iff on Additive Gal(L); a 2-torsion g has galToProd g = (a, b), a² = 1 ⇒ a ≡ ±1 mod p^k (redU_sq_eq_one),
  b = u'^j with 2f ∣ 2j ⇒ b ↦ 1 mod m; so g|_K ∈ {1, τ} by galToProd_restrict + injectivity; conversely g0 = galToProd⁻¹(-1,1) restricts to τ.
- Copied verbatim into Disj.lean from glue-sqrt-local SqrtLocal.lean lines 84-242 (exists_half_iff, redU, redU_sq_eq_one and helpers), namespace GlueSqrtLocal.
