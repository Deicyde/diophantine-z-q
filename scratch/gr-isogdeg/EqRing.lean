import Mathlib

namespace ZInQ.GRIsogDeg

open TensorProduct

universe u

/-- Ring maps `S → L` over `ψ₀` into a field are finitely many when `S` is finite over `R`. -/
theorem finite_ringHom {R S L : Type*} [CommRing R] [CommRing S] [Algebra R S] [Module.Finite R S]
    [Field L] (ψ₀ : R →+* L) : Finite {ψ : S →+* L // ψ.comp (algebraMap R S) = ψ₀} := by
  letI : Algebra R L := ψ₀.toAlgebra
  let toA : {ψ : S →+* L // ψ.comp (algebraMap R S) = ψ₀} → (S →ₐ[R] L) := fun ψ =>
    AlgHom.mk ψ.1 (fun r => congrArg (fun g : R →+* L => g r) ψ.2)
  have hinj : Function.Injective toA := fun a b h => Subtype.ext (congrArg AlgHom.toRingHom h)
  have : Finite (S →ₐ[R] L) := Finite.of_equiv _ (AlgHom.liftEquiv R L S L).symm
  exact Finite.of_injective toA hinj

/-- Equality in the ring-level count (characteristic `0`, `Ω` algebraically closed, `S` a domain
finite over `R`, `R → S` injective): the ring maps over `ψ₀` number exactly the rank at `⊥`. -/
theorem card_ringHom_eq_rankAtStalk {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    [IsDomain R] [IsDomain S] [Module.Finite R S] (hinj : Function.Injective (algebraMap R S))
    {Ω : Type*} [Field Ω] [IsAlgClosed Ω] [CharZero Ω]
    (ψ₀ : R →+* Ω) (hψ₀ : Function.Injective ψ₀) (p : PrimeSpectrum R) (hp : p.asIdeal = ⊥) :
    Nat.card {ψ : S →+* Ω // ψ.comp (algebraMap R S) = ψ₀} = Module.rankAtStalk S p := by
  obtain ⟨P, hP⟩ := p
  dsimp only at hp
  subst hp
  let Rp := Localization.AtPrime (⊥ : Ideal R)
  have : IsFractionRing R Rp := by
    simpa [Ideal.primeCompl_bot] using Localization.isLocalization (M := (⊥ : Ideal R).primeCompl)
  letI : Algebra R Ω := ψ₀.toAlgebra
  have hunit : ∀ y : (⊥ : Ideal R).primeCompl, IsUnit (ψ₀ y) := fun y => by
    have hy : (y : R) ≠ 0 := fun h => y.2 (by rw [h]; exact Ideal.zero_mem _)
    exact ((map_ne_zero_iff ψ₀ hψ₀).mpr hy).isUnit
  let ψp : Rp →+* Ω := IsLocalization.lift hunit
  letI : Algebra Rp Ω := ψp.toAlgebra
  haveI : IsScalarTower R Rp Ω := IsScalarTower.of_algebraMap_eq fun r => by
    change ψ₀ r = ψp (algebraMap R Rp r)
    exact (IsLocalization.lift_eq hunit r).symm
  let toA : {ψ : S →+* Ω // ψ.comp (algebraMap R S) = ψ₀} → (S →ₐ[R] Ω) := fun ψ =>
    AlgHom.mk ψ.1 (fun r => congrArg (fun g : R →+* Ω => g r) ψ.2)
  let e₁ : {ψ : S →+* Ω // ψ.comp (algebraMap R S) = ψ₀} ≃ (S →ₐ[R] Ω) :=
    { toFun := toA
      invFun := fun f => ⟨f.toRingHom, RingHom.ext fun r => f.commutes r⟩
      left_inv := fun ψ => rfl
      right_inv := fun f => rfl }
  rw [Nat.card_congr (e₁.trans (AlgHom.liftEquiv R Rp S Ω)),
    Module.rankAtStalk_eq_finrank_tensorProduct]
  -- `Rp ⊗[R] S` is a localization of the domain `S`, finite over the field `Rp`: a field
  have hdom : IsDomain (Rp ⊗[R] S) := by
    letI : Algebra S (Rp ⊗[R] S) := Algebra.TensorProduct.rightAlgebra
    haveI : IsLocalization (Algebra.algebraMapSubmonoid S (⊥ : Ideal R).primeCompl) (Rp ⊗[R] S) :=
      IsLocalization.tensorRight _ _
    refine IsLocalization.isDomain_of_le_nonZeroDivisors (R := S)
      (M := Algebra.algebraMapSubmonoid S (⊥ : Ideal R).primeCompl) _ ?_
    rintro _ ⟨r, hr, rfl⟩
    refine mem_nonZeroDivisors_of_ne_zero ?_
    intro h0
    apply hr
    have : r = 0 := hinj (by rw [h0, map_zero])
    rw [this]; exact Ideal.zero_mem _
  letI : Field Rp := IsFractionRing.toField R
  have hfield : IsField (Rp ⊗[R] S) := isField_of_isIntegral_of_isField' (R := Rp) (Field.toIsField Rp)
  letI : Field (Rp ⊗[R] S) := hfield.toField
  haveI : CharZero Rp := (RingHom.charZero_iff ψp.injective).mpr inferInstance
  haveI : Algebra.IsSeparable Rp (Rp ⊗[R] S) := Algebra.IsAlgebraic.isSeparable_of_perfectField
  rw [← AlgHom.card Rp (Rp ⊗[R] S) Ω, Fintype.card_eq_nat_card]

/-- Descent of ring maps from `Ω` to an algebraically closed subfield `k`: for `S` integral over
`R`, every ring map `S → Ω` over `emb ∘ ψ'` factors through `emb : k → Ω`. -/
theorem card_ringHom_le_of_isAlgClosed {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    [Algebra.IsIntegral R S] {k Ω : Type*} [Field k] [IsAlgClosed k] [Field Ω] (emb : k →+* Ω)
    (ψ' : R →+* k) [Finite {χ' : S →+* k // χ'.comp (algebraMap R S) = ψ'}] :
    Nat.card {χ : S →+* Ω // χ.comp (algebraMap R S) = emb.comp ψ'} ≤
      Nat.card {χ' : S →+* k // χ'.comp (algebraMap R S) = ψ'} := by
  letI : Algebra k Ω := emb.toAlgebra
  letI : Algebra R k := ψ'.toAlgebra
  letI : Algebra R Ω := (emb.comp ψ').toAlgebra
  haveI : IsScalarTower R k Ω := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  have hmem : ∀ χ : {χ : S →+* Ω // χ.comp (algebraMap R S) = emb.comp ψ'}, ∀ s, χ.1 s ∈ emb.range := by
    intro χ s
    let χa : S →ₐ[R] Ω := AlgHom.mk χ.1 (fun r => congrArg (fun g : R →+* Ω => g r) χ.2)
    have h1 : IsIntegral R (χ.1 s) := (Algebra.IsIntegral.isIntegral s).map χa
    have h2 : IsIntegral k (χ.1 s) := h1.tower_top
    obtain ⟨c, hc⟩ := (IsAlgClosed.algebraMap_bijective_of_isIntegral (k := k)
      (K := integralClosure k Ω)).2 ⟨χ.1 s, h2⟩
    exact ⟨c, congrArg Subtype.val hc⟩
  let eR : k ≃+* emb.range := RingEquiv.ofBijective emb.rangeRestrict
    ⟨fun a b h => emb.injective (congrArg Subtype.val h), emb.rangeRestrict_surjective⟩
  have heR : ∀ y : emb.range, emb (eR.symm y) = y := fun y => by
    have := congrArg Subtype.val (eR.apply_symm_apply y)
    exact this
  let down : {χ : S →+* Ω // χ.comp (algebraMap R S) = emb.comp ψ'} →
      {χ' : S →+* k // χ'.comp (algebraMap R S) = ψ'} := fun χ =>
    ⟨eR.symm.toRingHom.comp (χ.1.codRestrict emb.range (hmem χ)), by
      ext r
      apply emb.injective
      change emb (eR.symm _) = emb (ψ' r)
      rw [heR]
      exact congrArg (fun g : R →+* Ω => g r) χ.2⟩
  have hdown : Function.Injective down := fun a b h => Subtype.ext (RingHom.ext fun s => by
    have := congrArg (fun χ' : {χ' : S →+* k // χ'.comp (algebraMap R S) = ψ'} => emb (χ'.1 s)) h
    simpa [down, heR] using this)
  exact Nat.card_le_card_of_injective down hdown

end ZInQ.GRIsogDeg
