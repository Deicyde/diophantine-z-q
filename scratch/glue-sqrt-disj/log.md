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
- `exists_tau`: ∃ τ ∈ Gal(ℚ_p(μ_{p^k m})/ℚ_p) with galToProd τ = (-1, 1). VERIFIED.
- `sqrt_criterion_level_pow`: sqrt_criterion_level with m' = p^{2f} - 1, f = ord_m(p); hypotheses m ∣ m', ord_{m'}(p) = 2f discharged
  by the Level.lean lemmas (copied into Disj.lean). Remaining instance hypotheses: [NeZero (p^{2f}-1)], cyclotomic K ⊆ L. VERIFIED (compiled 00:53 PST).

## Plumb.lean (standalone, compiled 00:56 PST) and its merge into Disj.lean (compiled 00:57 PST; all axioms propext, Classical.choice, Quot.sound)
- `PkgI6.LocalKroneckerWeber` copied verbatim from scratch/pkg-I6/I6.lean.
- `muField p n := IntermediateField.adjoin ℚ_[p] {x : PadicAlgCl p | x ^ n = 1}` (exactly I6.3's field).
- `isCyclotomicExtension_muField`: [NeZero n] ⇒ IsCyclotomicExtension {n} ℚ_[p] (muField p n). VERIFIED.
- `muField_mono`: a ∣ b ⇒ muField a ≤ muField b. VERIFIED.
- `le_muField_of_lkw`: LocalKroneckerWeber p ⇒ every finite abelian M ⊆ PadicAlgCl p lies in muField (p^k m), 0 < m, p coprime m. VERIFIED.
- `muField_le_level`, `level_dvd`: p^k m ∣ p^{k+1}(p^{2f}-1). VERIFIED.
- Instances (Disj.lean, section MuField): IsCyclotomicExtension/FiniteDimensional/IsGalois on muField; Algebra ℤ_[p] and
  IsScalarTower ℤ_[p] ℚ_[p] found by inferInstance (IntermediateField.algebra'); `muAlgebra a b [Fact (a ∣ b)]` + IsScalarTower.
- **`sqrt_criterion_muField`**: the criterion on K = muField (p^k m) ⊆ L = muField (p^{k+1}(p^{2f}-1)) inside PadicAlgCl p,
  every p incl. 2; hypotheses [NeZero m], p coprime m, [NeZero (p^{2f}-1)], [Fact (level divisibility)] (discharged by level_dvd),
  τ with galToProd τ = (-1,1) (exists by exists_tau). VERIFIED.

## G_{ℚ_p}-level attempt (01:00-01:14 PST): NOT COMPILED, not claimed
- `sqrt_criterion_absolute` ("if" direction over Gal(PadicAlgCl p/ℚ_p), from LocalKroneckerWeber): draft saved as
  scratch/glue-sqrt-disj/AbsoluteAttempt.lean.txt. Blocker: `restrictNormal_muField_trans`
  ((g|_{muField b})|_{muField a} = g|_{muField a}) gave a kernel deterministic timeout; with maxHeartbeats 2000000 the
  run was stopped by the 10-minute background limit. Disj.lean reverted to the 00:57 version (re-checked 01:15 PST:
  no errors, no sorryAx).
