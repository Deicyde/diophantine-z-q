/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: P2M.Sol.S_CuspForm_IsEigenformWith_exists_galoisRepAdic_charpoly_frobenius_eq_and_isUnramifiedAt (git blob c291b33117c90308ec6e92c85e64d706fc087c5c, sha256 f7681c9388f07c1cb3631d4eeb48ee0a94a07f30aa24293ff55a299267d7a2de).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_CuspForm_PrimitiveFormGamma1
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_GaloisRep_Adic
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_EllipticCurve_TateModule
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_ModularCurve_X1HeckeModule
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_ModularCurve_heckeDiamondInputsAll
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_ModularCurve_heckeDiamondCommuteBar
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_ModularCurve_moduleFinite_padicInt_tateModule_jOne
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_CuspForm_IsEigenformWith_exists_ringHom_rationalHeckeAlgebraOne_mul_eq
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_ModularCurve_exists_galoisRepAdic_charpoly_frobenius_of_heckeDiamondChar
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_RingHom_finiteDimensional_adjoin_range_of_finite_of_forall_mem_range
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_integralClosure_finite_and_isDiscreteValuationRing_and_isAdicComplete_maximalIdeal

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

namespace P2MW.S_CuspForm_IsEigenformWith_exists_galoisRepAdic_charpoly_frobenius_eq_and_isUnramifiedAt

open Polynomial

noncomputable section

namespace E1G1

theorem padicIntToRing_injective (p : ℕ) [Fact p.Prime] (𝒪 : Type) [CommRing 𝒪] [IsDomain 𝒪]
    [IsLocalRing 𝒪] [IsAdicComplete (IsLocalRing.maximalIdeal 𝒪) 𝒪] [CharZero 𝒪]
    (hp : (p : 𝒪) ∈ IsLocalRing.maximalIdeal 𝒪) :
    Function.Injective (GaloisRep.padicIntToRing 𝒪 p hp) := by
  rw [RingHom.injective_iff_ker_eq_bot]
  by_contra hne
  obtain ⟨n, hn⟩ := PadicInt.ideal_eq_span_pow_p hne
  have hmem : (p : ℤ_[p]) ^ n ∈ RingHom.ker (GaloisRep.padicIntToRing 𝒪 p hp) := by
    rw [hn]; exact Ideal.mem_span_singleton_self _
  rw [RingHom.mem_ker, map_pow, map_natCast] at hmem
  exact pow_ne_zero n (Nat.cast_ne_zero.2 (Fact.out : p.Prime).ne_zero) hmem

theorem coefficientRing (𝒪 : Type) [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪]
    [IsAdicComplete (IsLocalRing.maximalIdeal 𝒪) 𝒪] [Finite (IsLocalRing.ResidueField 𝒪)]
    [CharZero 𝒪]
    (L' : Type) [Field L'] [Algebra 𝒪 L'] [Algebra (FractionRing 𝒪) L']
    [IsScalarTower 𝒪 (FractionRing 𝒪) L'] [FiniteDimensional (FractionRing 𝒪) L'] :
    ∃ (_ : IsDiscreteValuationRing ↥(integralClosure 𝒪 L')),
      IsAdicComplete (IsLocalRing.maximalIdeal ↥(integralClosure 𝒪 L')) ↥(integralClosure 𝒪 L') ∧
      Finite (IsLocalRing.ResidueField ↥(integralClosure 𝒪 L')) ∧
      CharZero ↥(integralClosure 𝒪 L') ∧
      Module.Finite 𝒪 ↥(integralClosure 𝒪 L') ∧
      IsLocalHom (algebraMap 𝒪 ↥(integralClosure 𝒪 L')) ∧
      Function.Injective (algebraMap 𝒪 ↥(integralClosure 𝒪 L')) ∧
      IsFractionRing ↥(integralClosure 𝒪 L') L' := by
  haveI : Algebra.IsSeparable (FractionRing 𝒪) L' := inferInstance
  obtain ⟨hfin, hdvr, hcomp⟩ :=
    integralClosure.finite_and_isDiscreteValuationRing_and_isAdicComplete_maximalIdeal 𝒪
      (FractionRing 𝒪) L'
  haveI := hfin
  haveI := hdvr
  have hinjL : Function.Injective (algebraMap 𝒪 L') := by
    rw [IsScalarTower.algebraMap_eq 𝒪 (FractionRing 𝒪) L']
    exact (algebraMap (FractionRing 𝒪) L').injective.comp (IsFractionRing.injective 𝒪 _)
  have hinj : Function.Injective (algebraMap 𝒪 ↥(integralClosure 𝒪 L')) := fun x y h =>
    hinjL (by
      have h' := congrArg (fun z : ↥(integralClosure 𝒪 L') => (z : L')) h
      simpa only [Subalgebra.coe_algebraMap] using h')
  haveI : FaithfulSMul 𝒪 ↥(integralClosure 𝒪 L') :=
    (faithfulSMul_iff_algebraMap_injective 𝒪 _).2 hinj
  have hloc : IsLocalHom (algebraMap 𝒪 ↥(integralClosure 𝒪 L')) :=
    Algebra.IsIntegral.isLocalHom 𝒪 _
  haveI := hloc
  have hres : Finite (IsLocalRing.ResidueField ↥(integralClosure 𝒪 L')) :=
    IsLocalRing.ResidueField.finite_of_finite (R := 𝒪) inferInstance
  haveI : CharZero L' :=
    (RingHom.charZero_iff (algebraMap (FractionRing 𝒪) L').injective).1 inferInstance
  have hcz : CharZero ↥(integralClosure 𝒪 L') := (algebraMap ↥(integralClosure 𝒪 L') L').charZero
  have hfrac : IsFractionRing ↥(integralClosure 𝒪 L') L' :=
    integralClosure.isFractionRing_of_finite_extension (FractionRing 𝒪) L'
  exact ⟨hdvr, hcomp, hres, hcz, hfin, hloc, hinj, hfrac⟩

theorem exists_pow_eq_one {M : ℕ} [NeZero M] (ε : DirichletCharacter ℂ M)
    {R : Type} [CommRing R] (toC : R →+* ℂ) (htoC : Function.Injective toC)
    {ℓ : ℕ} (hℓ : ℓ.Prime) (hℓM : ¬ ℓ ∣ M) (x : R) (hx : toC x = ε (ℓ : ZMod M)) :
    ∃ n : ℕ, 0 < n ∧ x ^ n = 1 := by
  obtain ⟨u, hu⟩ := (ZMod.isUnit_prime_iff_not_dvd hℓ).2 hℓM
  refine ⟨Fintype.card (ZMod M)ˣ, Fintype.card_pos, htoC ?_⟩
  rw [map_pow, hx, map_one, ← hu, ← map_pow, ← Units.val_pow_eq_pow_val, pow_card_eq_one,
    Units.val_one, map_one]

theorem isUnit_map_of_pow_eq_one {R S : Type} [CommRing R] [CommRing S] (f : R →+* S) {x : R} {n : ℕ}
    (hn : 0 < n) (hx : x ^ n = 1) : IsUnit (f x) := by
  have : (f x) ^ n = 1 := by rw [← map_pow, hx, map_one]
  exact IsUnit.of_pow_eq_one this (Nat.pos_iff_ne_zero.1 hn)

section Instances

variable (p : ℕ) [Fact p.Prime] (J : Type) [AddCommGroup J] [Module ModularCurve.HeckeAlgOne J]

scoped instance isMulCommutative_A : IsMulCommutative (ModularCurve.rationalHeckeAlgebraOne p J) :=
  Algebra.isMulCommutative_adjoin ℚ_[p] (by
    rintro _ ⟨s, rfl⟩ _ ⟨t, rfl⟩ _ -- [port]
    show _ * _ = _ * _
    rw [← map_mul, ← map_mul, mul_comm])

open scoped IsMulCommutative in
scoped instance instCommRingA : CommRing (ModularCurve.rationalHeckeAlgebraOne p J) := inferInstance

end Instances

set_option maxHeartbeats 16000000 in

theorem main
    {M : ℕ} [NeZero M] {ε : DirichletCharacter ℂ M} {h : CuspForm (CongruenceSubgroup.Gamma1 M) 2}
    (hh : CuspForm.IsEigenformWith ε h)
    (lam : ℕ) [Fact lam.Prime] (S : Finset ℕ) (hlamS : lam ∈ S)
    (O' : Type) [CommRing O'] [IsDomain O'] [IsDiscreteValuationRing O']
    [IsAdicComplete (IsLocalRing.maximalIdeal O') O'] [Finite (IsLocalRing.ResidueField O')]
    [CharZero O'] (hlamO' : (lam : O') ∈ IsLocalRing.maximalIdeal O')
    (R : Type) [CommRing R] (toC : R →+* ℂ) (htoC : Function.Injective toC) (φ : R →+* O')
    (b e : ℕ → R)
    (hb : ∀ ℓ : ℕ, ℓ.Prime → ¬ ℓ ∣ M → ℓ ∉ S → toC (b ℓ) = ModularFormClass.qCoeff h ℓ)
    (he : ∀ ℓ : ℕ, ℓ.Prime → ¬ ℓ ∣ M → ℓ ∉ S → toC (e ℓ) = ε (ℓ : ZMod M)) :
    ∃ (O'' : Type) (_ : CommRing O'') (_ : IsDomain O'') (_ : IsDiscreteValuationRing O'')
        (_ : IsAdicComplete (IsLocalRing.maximalIdeal O'') O'')
        (_ : Finite (IsLocalRing.ResidueField O'')) (_ : CharZero O'')
        (_ : Algebra O' O'') (_ : Module.Finite O' O'') (_ : IsLocalHom (algebraMap O' O'')),
      Function.Injective (algebraMap O' O'') ∧
      ∃ ρ : GaloisRepAdic O'',
        (∀ (ℓ : ℕ), ℓ.Prime → ¬ ℓ ∣ M → ℓ ∉ S →
          ∀ A : ValuationSubring (AlgebraicClosure ℚ), A.LiesOverPrime ℓ →
            ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, A.IsFrobeniusAt σ ℓ →
              LinearMap.charpoly (ρ.ρ σ) =
                X ^ 2 - C (algebraMap O' O'' (φ (b ℓ))) * X
                  + C (algebraMap O' O'' (φ (e ℓ) * (ℓ : O')))) ∧
        (∀ ℓ : ℕ, ℓ.Prime → ¬ ℓ ∣ M → ℓ ≠ lam → ρ.IsUnramifiedAt ℓ) := by
  letI := ModularCurve.heckeModuleOneBar M
  have hin : ModularCurve.HeckeDiamondInputsAll M := ModularCurve.heckeDiamondInputsAll M
  have hcomm : ModularCurve.HeckeDiamondCommuteBar M := ModularCurve.heckeDiamondCommuteBar M

  set i𝒪 : ℤ_[lam] →+* O' := GaloisRep.padicIntToRing O' lam hlamO' with hi𝒪
  have hi_inj : Function.Injective i𝒪 := E1G1.padicIntToRing_injective lam O' hlamO'
  have hg_inj : Function.Injective ((algebraMap O' (FractionRing O')).comp i𝒪) :=
    (IsFractionRing.injective O' (FractionRing O')).comp hi_inj
  set jL : ℚ_[lam] →+* FractionRing O' := IsFractionRing.lift hg_inj with hjL
  have hjL : ∀ c : ℤ_[lam], jL (c : ℚ_[lam]) = algebraMap O' (FractionRing O') (i𝒪 c) := fun c => by
    rw [← PadicInt.algebraMap_apply, hjL, IsFractionRing.lift_algebraMap]
    rfl
  letI : Algebra ℚ_[lam] (AlgebraicClosure (FractionRing O')) :=
    ((algebraMap (FractionRing O') (AlgebraicClosure (FractionRing O'))).comp jL).toAlgebra
  have halg : ∀ c : ℚ_[lam], algebraMap ℚ_[lam] (AlgebraicClosure (FractionRing O')) c
      = algebraMap (FractionRing O') (AlgebraicClosure (FractionRing O')) (jL c) := fun _ => rfl

  set ψ : R →+* AlgebraicClosure (FractionRing O') :=
    (algebraMap O' (AlgebraicClosure (FractionRing O'))).comp φ with hψ
  obtain ⟨Λ, hc, hT⟩ := hh.exists_ringHom_rationalHeckeAlgebraOne_mul_eq lam hin hcomm
    (↑S : Set ℕ) (AlgebraicClosure (FractionRing O')) R toC htoC ψ b e
    (fun ℓ hℓ hℓM hℓS => hb ℓ hℓ hℓM (fun h' => hℓS (Finset.mem_coe.2 h')))
    (fun ℓ hℓ hℓM hℓS => he ℓ hℓ hℓM (fun h' => hℓS (Finset.mem_coe.2 h')))

  haveI : Module.Finite ℤ_[lam] (TateModule lam (ModularCurve.JOne M)) :=
    ModularCurve.moduleFinite_padicInt_tateModule_jOne M lam
  haveI : Module.Finite ℚ_[lam] (ModularCurve.RationalTateModule lam (ModularCurve.JOne M)) :=
    inferInstance
  haveI : Module.Finite ℚ_[lam]
      (Module.End ℚ_[lam] (ModularCurve.RationalTateModule lam (ModularCurve.JOne M))) := inferInstance
  haveI : Module.Finite ℚ_[lam] ↥(ModularCurve.rationalHeckeAlgebraOne lam (ModularCurve.JOne M)) :=
    Module.Finite.of_injective (Subalgebra.val _).toLinearMap Subtype.val_injective
  obtain ⟨L', hL'⟩ : ∃ L' : IntermediateField (FractionRing O') (AlgebraicClosure (FractionRing O')),
      L' = IntermediateField.adjoin (FractionRing O') (Set.range Λ) := ⟨_, rfl⟩
  haveI : FiniteDimensional (FractionRing O') ↥L' := by
    rw [hL']
    exact RingHom.finiteDimensional_adjoin_range_of_finite_of_forall_mem_range (R := ℚ_[lam]) Λ
      (fun r => ⟨jL r, by rw [hc r, halg]⟩)
  have hΛmem : ∀ x, Λ x ∈ L' := fun x => by
    rw [hL']
    exact IntermediateField.subset_adjoin (FractionRing O') _ (Set.mem_range_self x)

  obtain ⟨hdvr, hcomp, hres, hcz, hfin, hloc, hinj, hfrac⟩ := E1G1.coefficientRing O' ↥L'
  haveI := hdvr
  haveI := hfrac
  haveI := hloc
  have hp'' : (lam : ↥(integralClosure O' ↥L')) ∈
      IsLocalRing.maximalIdeal ↥(integralClosure O' ↥L') := by
    rw [IsLocalRing.mem_maximalIdeal, ← map_natCast (algebraMap O' ↥(integralClosure O' ↥L')) lam,
      map_mem_nonunits_iff, ← IsLocalRing.mem_maximalIdeal]
    exact hlamO'

  let Λ' : ↥(ModularCurve.rationalHeckeAlgebraOne lam (ModularCurve.JOne M)) →+* ↥L' :=
    { toFun := fun x => ⟨Λ x, hΛmem x⟩
      map_one' := Subtype.ext (map_one Λ)
      map_mul' := fun x y => Subtype.ext (map_mul Λ x y)
      map_zero' := Subtype.ext (map_zero Λ)
      map_add' := fun x y => Subtype.ext (map_add Λ x y) }
  have hΛ'val : ∀ x, ((Λ' x : ↥L') : AlgebraicClosure (FractionRing O')) = Λ x := fun _ => rfl
  have hcoe𝒪 : ∀ y : O',
      ((algebraMap ↥(integralClosure O' ↥L') ↥L' (algebraMap O' ↥(integralClosure O' ↥L') y) : ↥L') :
        AlgebraicClosure (FractionRing O'))
        = algebraMap (FractionRing O') (AlgebraicClosure (FractionRing O'))
            (algebraMap O' (FractionRing O') y) := fun y => by
    rw [← IsScalarTower.algebraMap_apply O' ↥(integralClosure O' ↥L') ↥L']
    change algebraMap O' (AlgebraicClosure (FractionRing O')) y = _
    exact IsScalarTower.algebraMap_apply O' (FractionRing O') _ y
  have hcoe𝒪' : ∀ y : O',
      ((algebraMap ↥(integralClosure O' ↥L') ↥L' (algebraMap O' ↥(integralClosure O' ↥L') y) : ↥L') :
        AlgebraicClosure (FractionRing O'))
        = algebraMap O' (AlgebraicClosure (FractionRing O')) y := fun y => by
    rw [hcoe𝒪]
    exact (IsScalarTower.algebraMap_apply O' (FractionRing O') _ y).symm
  have hΛ'c : ∀ c : ℤ_[lam],
      Λ' (algebraMap ℚ_[lam] ↥(ModularCurve.rationalHeckeAlgebraOne lam (ModularCurve.JOne M)) (c : ℚ_[lam]))
        = algebraMap ↥(integralClosure O' ↥L') ↥L'
            (((algebraMap O' ↥(integralClosure O' ↥L')).comp i𝒪) c) := fun c => by
    apply Subtype.ext
    rw [hΛ'val, hc, halg, hjL, RingHom.comp_apply, hcoe𝒪]

  have E1 := ModularCurve.exists_galoisRepAdic_charpoly_frobenius_of_heckeDiamondChar M lam
    ↥(integralClosure O' ↥L') ↥L' ((algebraMap O' ↥(integralClosure O' ↥L')).comp i𝒪) hp''
  obtain ⟨ρ, hchar, hunr⟩ := E1 Λ' hΛ'c

  have hp : lam.Prime := Fact.out
  have hMp : ∀ ℓ : ℕ, ℓ.Prime → ¬ ℓ ∣ M → ℓ ≠ lam → ¬ ℓ ∣ M * lam := fun ℓ hℓ hℓM hℓp h' =>
    (hℓ.dvd_mul.1 h').elim hℓM (fun h'' => hℓp ((Nat.prime_dvd_prime_iff_eq hℓ hp).1 h''))

  have hunits : ∀ ℓ : ℕ, ℓ.Prime → ¬ ℓ ∣ M → ℓ ∉ S → IsUnit (φ (e ℓ)) := by
    intro ℓ hℓ hℓM hℓS
    obtain ⟨n, hn, hpow⟩ := E1G1.exists_pow_eq_one ε toC htoC hℓ hℓM (e ℓ) (he ℓ hℓ hℓM hℓS)
    exact E1G1.isUnit_map_of_pow_eq_one φ hn hpow
  refine ⟨↥(integralClosure O' ↥L'), inferInstance, inferInstance, hdvr, hcomp, hres, hcz,
    inferInstance, hfin, hloc, hinj, ρ, ?_, fun q hq hqM hqp => hunr q hq (hMp q hq hqM hqp)⟩
  intro ℓ hℓ hℓM hℓS A hA σ hσ
  have hℓp : ℓ ≠ lam := fun h' => hℓS (by rw [h']; exact hlamS)
  have hℓS' : ℓ ∉ (↑S : Set ℕ) := fun h' => hℓS (Finset.mem_coe.1 h')
  have hT' := hT ℓ hℓ hℓM hℓS'
  have hTℓ := hT'.1
  have hDℓ := hT'.2
  have hu := hunits ℓ hℓ hℓM hℓS

  have hψe : ψ (e ℓ) = algebraMap O' (AlgebraicClosure (FractionRing O')) (φ (e ℓ)) := rfl
  have hψb : ψ (b ℓ) = algebraMap O' (AlgebraicClosure (FractionRing O')) (φ (b ℓ)) := rfl
  have hd' : Λ' (ModularCurve.rationalDiamondOne lam (ModularCurve.JOne M) ℓ)
      * algebraMap ↥(integralClosure O' ↥L') ↥L'
          (algebraMap O' ↥(integralClosure O' ↥L') (φ (e ℓ))) = 1 := by
    apply (algebraMap ↥L' (AlgebraicClosure (FractionRing O'))).injective
    rw [map_mul, map_one, IntermediateField.algebraMap_apply, IntermediateField.algebraMap_apply,
      hΛ'val, hcoe𝒪', ← hψe]
    exact hDℓ
  have hunit : algebraMap O' (AlgebraicClosure (FractionRing O')) (φ (e ℓ))
      * algebraMap O' (AlgebraicClosure (FractionRing O')) ((hu.unit⁻¹ : O'ˣ) : O') = 1 := by
    rw [← map_mul, IsUnit.mul_val_inv, map_one]
  have hΛT : Λ (ModularCurve.rationalHeckeOne lam (ModularCurve.JOne M) ⟨ℓ, hℓ⟩)
      = algebraMap O' (AlgebraicClosure (FractionRing O')) ((hu.unit⁻¹ : O'ˣ) : O')
          * algebraMap O' (AlgebraicClosure (FractionRing O')) (φ (b ℓ)) := by
    calc Λ (ModularCurve.rationalHeckeOne lam (ModularCurve.JOne M) ⟨ℓ, hℓ⟩)
        = Λ (ModularCurve.rationalHeckeOne lam (ModularCurve.JOne M) ⟨ℓ, hℓ⟩)
            * (algebraMap O' (AlgebraicClosure (FractionRing O')) (φ (e ℓ))
              * algebraMap O' (AlgebraicClosure (FractionRing O')) ((hu.unit⁻¹ : O'ˣ) : O')) := by
          rw [hunit, mul_one]
      _ = (Λ (ModularCurve.rationalHeckeOne lam (ModularCurve.JOne M) ⟨ℓ, hℓ⟩) * ψ (e ℓ))
            * algebraMap O' (AlgebraicClosure (FractionRing O')) ((hu.unit⁻¹ : O'ˣ) : O') := by
          rw [hψe, mul_assoc]
      _ = algebraMap O' (AlgebraicClosure (FractionRing O')) ((hu.unit⁻¹ : O'ˣ) : O')
            * algebraMap O' (AlgebraicClosure (FractionRing O')) (φ (b ℓ)) := by
          rw [hTℓ, hψb, mul_comm]
  have ha' : Λ' (ModularCurve.rationalHeckeOne lam (ModularCurve.JOne M) ⟨ℓ, hℓ⟩)
      = algebraMap ↥(integralClosure O' ↥L') ↥L'
          (algebraMap O' ↥(integralClosure O' ↥L') (((hu.unit⁻¹ : O'ˣ) : O') * φ (b ℓ))) := by
    apply Subtype.ext
    rw [hΛ'val, hcoe𝒪', map_mul]
    exact hΛT
  have hmain := hchar ℓ hℓ (hMp ℓ hℓ hℓM hℓp) _ _ ha' hd' A hA σ hσ
  rw [hmain]
  have hda : algebraMap O' ↥(integralClosure O' ↥L') (φ (e ℓ))
        * algebraMap O' ↥(integralClosure O' ↥L') (((hu.unit⁻¹ : O'ˣ) : O') * φ (b ℓ))
      = algebraMap O' ↥(integralClosure O' ↥L') (φ (b ℓ)) := by
    rw [← map_mul, ← mul_assoc, IsUnit.mul_val_inv, one_mul]
  have hdℓ : algebraMap O' ↥(integralClosure O' ↥L') (φ (e ℓ)) * (ℓ : ↥(integralClosure O' ↥L'))
      = algebraMap O' ↥(integralClosure O' ↥L') (φ (e ℓ) * (ℓ : O')) := by
    rw [map_mul, map_natCast]
  rw [hda, hdℓ]

end E1G1

theorem solution
    {M : ℕ} [NeZero M] {ε : DirichletCharacter ℂ M} {h : CuspForm (CongruenceSubgroup.Gamma1 M) 2}
    (hh : CuspForm.IsEigenformWith ε h)
    (lam : ℕ) [Fact lam.Prime] (S : Finset ℕ) (hlamS : lam ∈ S)
    (O' : Type) [CommRing O'] [IsDomain O'] [IsDiscreteValuationRing O']
    [IsAdicComplete (IsLocalRing.maximalIdeal O') O'] [Finite (IsLocalRing.ResidueField O')]
    [CharZero O'] (hlamO' : (lam : O') ∈ IsLocalRing.maximalIdeal O')
    (R : Type) [CommRing R] (toC : R →+* ℂ) (htoC : Function.Injective toC) (φ : R →+* O')
    (b e : ℕ → R)
    (hb : ∀ ℓ : ℕ, ℓ.Prime → ¬ ℓ ∣ M → ℓ ∉ S → toC (b ℓ) = ModularFormClass.qCoeff h ℓ)
    (he : ∀ ℓ : ℕ, ℓ.Prime → ¬ ℓ ∣ M → ℓ ∉ S → toC (e ℓ) = ε (ℓ : ZMod M)) :
    ∃ (O'' : Type) (_ : CommRing O'') (_ : IsDomain O'') (_ : IsDiscreteValuationRing O'')
        (_ : IsAdicComplete (IsLocalRing.maximalIdeal O'') O'')
        (_ : Finite (IsLocalRing.ResidueField O'')) (_ : CharZero O'')
        (_ : Algebra O' O'') (_ : Module.Finite O' O'') (_ : IsLocalHom (algebraMap O' O'')),
      Function.Injective (algebraMap O' O'') ∧
      ∃ ρ : GaloisRepAdic O'',
        (∀ (ℓ : ℕ), ℓ.Prime → ¬ ℓ ∣ M → ℓ ∉ S →
          ∀ A : ValuationSubring (AlgebraicClosure ℚ), A.LiesOverPrime ℓ →
            ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, A.IsFrobeniusAt σ ℓ →
              LinearMap.charpoly (ρ.ρ σ) =
                X ^ 2 - C (algebraMap O' O'' (φ (b ℓ))) * X
                  + C (algebraMap O' O'' (φ (e ℓ) * (ℓ : O')))) ∧
        (∀ ℓ : ℕ, ℓ.Prime → ¬ ℓ ∣ M → ℓ ≠ lam → ρ.IsUnramifiedAt ℓ) :=
  E1G1.main hh lam S hlamS O' hlamO' R toC htoC φ b e hb he
