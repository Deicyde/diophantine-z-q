/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: P2M.Sol.S_CuspForm_IsEigenformWith_exists_ringHom_rationalHeckeAlgebraOne_mul_eq (git blob 49e4337e5cd0d62d87e082d3d53d40d6a4962049, sha256 28f6bebcde2f642e3ba18094f5ca2bbd3dbfb7b85e5e49dcee3f521066bc10b1).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_CuspForm_PrimitiveFormGamma1
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_ModularCurve_X1HeckeModule
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_CuspForm_Gamma1HeckeOperators
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_ModularCurve_exists_injective_ringHom_adjoin_heckeDiamondGenBar_cuspForm
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_ModularCurve_linearIndependent_rationalHeckeRepOne_of_linearIndependent
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_ModularCurve_moduleFinite_padicInt_tateModule_jOne
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_RingHom_exists_comp_algebraMap_eq_of_isIntegral_of_isAlgClosed
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_CuspForm_conj_heckeEigenvalue_eq_of_hasNebentypus
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_CuspForm_HasNebentypus_diamondLinOne_apply_eq_smul
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_CuspForm_qCoeff_heckeTLinOne
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_UpperHalfPlane_eq_of_forall_qCoeff_eq

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

namespace ModularCurve
end ModularCurve

namespace P2MW.S_CuspForm_IsEigenformWith_exists_ringHom_rationalHeckeAlgebraOne_mul_eq

set_option autoImplicit false

open scoped TensorProduct

noncomputable section

namespace H2G1TR

open Submodule in

theorem transfer_relation
    {P T E Ω F : Type} [Field F] [CharZero F]
    [AddCommGroup P] [AddCommGroup T] [AddCommGroup E] [Module F E]
    [AddCommGroup Ω] [Module F Ω]
    (α : P →+ T) (β : P →+ Ω) (hαβ : ∀ g, α g = 0 → β g = 0)
    (γ : T →+ E)
    (hγ : ∀ {ι : Type} (u : ι → T), LinearIndependent ℤ u → LinearIndependent F (fun i => γ (u i)))
    {κ : Type} [Fintype κ] (x : κ → P) (c : κ → F)
    (hf : ∑ k, c k • γ (α (x k)) = 0) :
    ∑ k, c k • β (x k) = 0 := by
  classical
  obtain ⟨s, hs, hmax⟩ := exists_maximal_linearIndepOn ℤ (fun k => α (x k))
  have hrel : ∀ k, ∃ r : ℤ, r ≠ 0 ∧ ∃ a : s → ℤ, ∑ j : s, a j • α (x j) = r • α (x k) := by
    intro k
    by_cases hk : k ∈ s
    · refine ⟨1, one_ne_zero, Pi.single ⟨k, hk⟩ 1, ?_⟩
      rw [one_smul, Finset.sum_eq_single ⟨k, hk⟩ (fun j _ hj => by rw [Pi.single_eq_of_ne hj, zero_smul])
        (fun h => absurd (Finset.mem_univ _) h), Pi.single_eq_same, one_smul]
    · obtain ⟨r, hr, hmem⟩ := hmax k hk
      rw [Set.image_eq_range] at hmem
      obtain ⟨a, ha⟩ := (Submodule.mem_span_range_iff_exists_fun ℤ).1 hmem
      exact ⟨r, hr, a, ha⟩
  choose r hr a ha using hrel
  have hli : LinearIndependent F (fun j : s => γ (α (x j))) := hγ _ hs
  have hr' : ∀ k, (r k : F) ≠ 0 := fun k => Int.cast_ne_zero.2 (hr k)
  have hvan : ∀ k, α (∑ j : s, a k j • x j - r k • x k) = 0 := fun k => by
    rw [map_sub, map_sum, map_zsmul]
    simp_rw [map_zsmul]
    rw [ha, sub_self]
  have hγrel : ∀ k, γ (α (x k)) = (r k : F)⁻¹ • ∑ j : s, (a k j : F) • γ (α (x j)) := fun k => by
    rw [eq_inv_smul_iff₀ (hr' k), Int.cast_smul_eq_zsmul, ← map_zsmul, ← ha k, map_sum]
    simp_rw [map_zsmul, Int.cast_smul_eq_zsmul]
  have hβrel : ∀ k, β (x k) = (r k : F)⁻¹ • ∑ j : s, (a k j : F) • β (x j) := fun k => by
    have h := hαβ _ (hvan k)
    rw [map_sub, sub_eq_zero, map_sum, map_zsmul] at h
    rw [eq_inv_smul_iff₀ (hr' k), Int.cast_smul_eq_zsmul, ← h]
    simp_rw [map_zsmul, Int.cast_smul_eq_zsmul]
  set d : s → F := fun j => ∑ k, c k * ((r k : F)⁻¹ * (a k j : F)) with hd
  have key : ∀ {X : Type} [AddCommGroup X] [Module F X] (φ : κ → X) (ψ : s → X),
      (∀ k, φ k = (r k : F)⁻¹ • ∑ j : s, (a k j : F) • ψ j) →
        ∑ k, c k • φ k = ∑ j, d j • ψ j := by
    intro X _ _ φ ψ h
    calc ∑ k, c k • φ k = ∑ k, ∑ j, (c k * ((r k : F)⁻¹ * (a k j : F))) • ψ j := by
            refine Finset.sum_congr rfl fun k _ => ?_
            rw [h k, Finset.smul_sum, Finset.smul_sum]
            refine Finset.sum_congr rfl fun j _ => ?_
            rw [smul_smul, smul_smul, mul_assoc]
      _ = ∑ j, ∑ k, (c k * ((r k : F)⁻¹ * (a k j : F))) • ψ j := Finset.sum_comm
      _ = ∑ j, d j • ψ j := by
            refine Finset.sum_congr rfl fun j _ => ?_
            rw [hd, Finset.sum_smul]
  have hd0 : ∀ j, d j = 0 := by
    have h0 : ∑ j, d j • γ (α (x j)) = 0 := by
      rw [← key (fun k => γ (α (x k))) (fun j => γ (α (x j))) hγrel]
      exact hf
    exact Fintype.linearIndependent_iff.1 hli d h0
  rw [key (fun k => β (x k)) (fun j => β (x j)) hβrel]
  simp [hd0]

theorem aeval_eq_sum_coeff_smul {I F C : Type} [Field F] [CommRing C] [Algebra F C]
    (e : MvPolynomial I F →ₐ[F] C) (f : MvPolynomial I F) :
    e f = ∑ m ∈ f.support,
      (f).coeff m • e (MvPolynomial.map (Int.castRingHom F) (MvPolynomial.monomial m 1)) := by
  conv_lhs => rw [f.as_sum, map_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [MvPolynomial.map_monomial, map_one, ← map_smul, MvPolynomial.smul_monomial, smul_eq_mul,
    mul_one]

open _root_.ModularCurve hiding IsCusp

section Engine

variable (p : ℕ) [Fact p.Prime] (J : Type) [AddCommGroup J] [Module HeckeAlgOne J]





scoped instance isMulCommutative_A : IsMulCommutative (rationalHeckeAlgebraOne p J) :=
  Algebra.isMulCommutative_adjoin ℚ_[p] (by
    rintro _ ⟨s, rfl⟩ _ ⟨t, rfl⟩ _ -- [port]
    show _ * _ = _ * _
    rw [← map_mul, ← map_mul, mul_comm])

open scoped IsMulCommutative in
scoped instance instCommRingA : CommRing (rationalHeckeAlgebraOne p J) := inferInstance

theorem rationalHeckeRepOne_eq_zero_of_mem {t : HeckeAlgOne} (ht : t ∈ (Module.annihilator HeckeAlgOne J)) :
    rationalHeckeRepOne p J t = 0 := by
  have h0 : tateHeckeRepOne p J t = 0 := by
    refine LinearMap.ext fun x => Subtype.ext (funext fun n => ?_)
    rw [coe_tateHeckeRepOne_apply_apply, LinearMap.zero_apply, TateModule.coe_zero, Pi.zero_apply]
    exact Module.mem_annihilator.1 ht _
  rw [rationalHeckeRepOne_apply, h0, LinearMap.baseChange_zero]

def gam : (HeckeAlgOne ⧸ (Module.annihilator HeckeAlgOne J)) →+* (Module.End ℚ_[p] (RationalTateModule p J)) :=
  Ideal.Quotient.lift (Module.annihilator HeckeAlgOne J) (rationalHeckeRepOne p J) (fun _ ht => rationalHeckeRepOne_eq_zero_of_mem p J ht)

theorem gam_mk (t : HeckeAlgOne) : gam p J (Ideal.Quotient.mk (Module.annihilator HeckeAlgOne J) t) = rationalHeckeRepOne p J t :=
  Ideal.Quotient.lift_mk _ _ _

variable [Module.Finite ℤ_[p] (TateModule p J)]

scoped instance instFiniteV : Module.Finite ℚ_[p] (RationalTateModule p J) := inferInstance

scoped instance instFiniteEndV : Module.Finite ℚ_[p] (Module.End ℚ_[p] (RationalTateModule p J)) := inferInstance

scoped instance instFiniteA : Module.Finite ℚ_[p] (rationalHeckeAlgebraOne p J) :=
  Module.Finite.of_injective (Subalgebra.val (rationalHeckeAlgebraOne p J)).toLinearMap Subtype.val_injective

theorem engine {I : Type} (v : I → Nat.Primes ⊕ ℕ) (TS : Type) [CommRing TS] (g : I → TS)
    (hrel : ∀ f : MvPolynomial I ℤ,
      MvPolynomial.eval₂Hom (Int.castRingHom HeckeAlgOne) (fun i => MvPolynomial.X (v i)) f ∈ (Module.annihilator HeckeAlgOne J) →
        MvPolynomial.eval₂Hom (Int.castRingHom TS) g f = 0)
    (hfaith : ∀ {ι : Type} (t : ι → HeckeAlgOne),
      LinearIndependent ℤ (fun i => Ideal.Quotient.mk (Module.annihilator HeckeAlgOne J) (t i)) →
        LinearIndependent ℚ_[p] (fun i => rationalHeckeRepOne p J (t i)))
    (Ω : Type) [Field Ω] [IsAlgClosed Ω] [Algebra ℚ_[p] Ω] (χ : TS →+* Ω) :
    ∃ Λ : (rationalHeckeAlgebraOne p J) →+* Ω, (∀ c : ℚ_[p], Λ (algebraMap ℚ_[p] (rationalHeckeAlgebraOne p J) c) = algebraMap ℚ_[p] Ω c) ∧
      ∀ i : I, Λ ⟨rationalHeckeRepOne p J (MvPolynomial.X (v i)),
        rationalHeckeRepOne_mem_rationalHeckeAlgebraOne p J _⟩ = χ (g i) := by
  classical

  let rJ : MvPolynomial I ℤ →+* HeckeAlgOne :=
    MvPolynomial.eval₂Hom (Int.castRingHom HeckeAlgOne) (fun i => MvPolynomial.X (v i))
  let rS : MvPolynomial I ℤ →+* TS := MvPolynomial.eval₂Hom (Int.castRingHom TS) g
  let TV : I → (rationalHeckeAlgebraOne p J) := fun i =>
    ⟨rationalHeckeRepOne p J (MvPolynomial.X (v i)), rationalHeckeRepOne_mem_rationalHeckeAlgebraOne p J _⟩
  let eV : MvPolynomial I ℚ_[p] →ₐ[ℚ_[p]] (rationalHeckeAlgebraOne p J) := MvPolynomial.aeval TV
  let eχ : MvPolynomial I ℚ_[p] →ₐ[ℚ_[p]] Ω := MvPolynomial.aeval (fun i => χ (g i))
  have hrJ_X : ∀ i, rJ (MvPolynomial.X i) = MvPolynomial.X (v i) := fun i => MvPolynomial.eval₂_X _ _ _
  have hrS_X : ∀ i, rS (MvPolynomial.X i) = g i := fun i => MvPolynomial.eval₂_X _ _ _
  have heV_X : ∀ i, eV (MvPolynomial.X i) = TV i := fun i => MvPolynomial.aeval_X _ _
  have heχ_X : ∀ i, eχ (MvPolynomial.X i) = χ (g i) := fun i => MvPolynomial.aeval_X _ _

  have hE1 : ∀ f : MvPolynomial I ℤ,
      ((eV (MvPolynomial.map (Int.castRingHom ℚ_[p]) f) : (rationalHeckeAlgebraOne p J)) : (Module.End ℚ_[p] (RationalTateModule p J)))
        = rationalHeckeRepOne p J (rJ f) := by
    have key : ((Subalgebra.val (rationalHeckeAlgebraOne p J)).toRingHom.comp
        (eV.toRingHom.comp (MvPolynomial.map (Int.castRingHom ℚ_[p]))))
          = (rationalHeckeRepOne p J).comp rJ := by
      refine MvPolynomial.ringHom_ext (fun r => ?_) (fun i => ?_)
      · rw [eq_intCast, map_intCast, map_intCast]
      · show ((eV (MvPolynomial.map (Int.castRingHom ℚ_[p]) (MvPolynomial.X i)) : (rationalHeckeAlgebraOne p J)) : (Module.End ℚ_[p] (RationalTateModule p J)))
          = rationalHeckeRepOne p J (rJ (MvPolynomial.X i))
        rw [MvPolynomial.map_X, heV_X, hrJ_X]
    intro f
    exact RingHom.congr_fun key f

  have hE2 : ∀ f : MvPolynomial I ℤ,
      eχ (MvPolynomial.map (Int.castRingHom ℚ_[p]) f) = χ (rS f) := by
    have key : (eχ.toRingHom.comp (MvPolynomial.map (Int.castRingHom ℚ_[p])))
        = χ.comp rS := by
      refine MvPolynomial.ringHom_ext (fun r => ?_) (fun i => ?_)
      · rw [eq_intCast, map_intCast, map_intCast]
      · show eχ (MvPolynomial.map (Int.castRingHom ℚ_[p]) (MvPolynomial.X i))
          = χ (rS (MvPolynomial.X i))
        rw [MvPolynomial.map_X, heχ_X, hrS_X]
    intro f
    exact RingHom.congr_fun key f

  have hker : ∀ f : MvPolynomial I ℚ_[p], eV f = 0 → eχ f = 0 := by
    intro f hf
    have hT := transfer_relation (F := ℚ_[p])
      (((Ideal.Quotient.mk (Module.annihilator HeckeAlgOne J)).comp rJ).toAddMonoidHom) ((χ.comp rS).toAddMonoidHom)
      (fun q hq => by
        have hq' : rJ q ∈ (Module.annihilator HeckeAlgOne J) := Ideal.Quotient.eq_zero_iff_mem.1 hq
        show χ (rS q) = 0
        rw [hrel q hq', map_zero])
      (gam p J).toAddMonoidHom
      (fun {ι} u hu => by
        choose t ht using fun i => Ideal.Quotient.mk_surjective (u i)
        have hu' : LinearIndependent ℤ (fun i => Ideal.Quotient.mk (Module.annihilator HeckeAlgOne J) (t i)) := by
          have : (fun i => Ideal.Quotient.mk (Module.annihilator HeckeAlgOne J) (t i)) = u := funext ht
          rw [this]; exact hu
        have h := hfaith t hu'
        have e : (fun i => (gam p J).toAddMonoidHom (u i)) = fun i => rationalHeckeRepOne p J (t i) := by
          funext i
          show gam p J (u i) = rationalHeckeRepOne p J (t i)
          rw [← ht i, gam_mk]
        rw [e]; exact h)
      (fun m : ↥f.support => (MvPolynomial.monomial (m : I →₀ ℕ) (1 : ℤ) : MvPolynomial I ℤ))
      (fun m => (f).coeff (m : I →₀ ℕ))
      (by
        have h1 : ∀ m : ↥f.support,
            (gam p J).toAddMonoidHom ((((Ideal.Quotient.mk (Module.annihilator HeckeAlgOne J)).comp rJ).toAddMonoidHom)
              (MvPolynomial.monomial (m : I →₀ ℕ) (1 : ℤ)))
              = ((eV (MvPolynomial.map (Int.castRingHom ℚ_[p])
                  (MvPolynomial.monomial (m : I →₀ ℕ) 1)) : (rationalHeckeAlgebraOne p J)) : (Module.End ℚ_[p] (RationalTateModule p J))) := fun m => by
          show gam p J (Ideal.Quotient.mk (Module.annihilator HeckeAlgOne J) (rJ _)) = _
          rw [gam_mk, hE1]
        simp_rw [h1]
        rw [Finset.sum_coe_sort f.support (fun m => (f).coeff m •
          ((eV (MvPolynomial.map (Int.castRingHom ℚ_[p]) (MvPolynomial.monomial m 1)) : (rationalHeckeAlgebraOne p J)) : (Module.End ℚ_[p] (RationalTateModule p J))))]
        have h2 : ((eV f : (rationalHeckeAlgebraOne p J)) : (Module.End ℚ_[p] (RationalTateModule p J))) = 0 := by rw [hf]; rfl
        rw [aeval_eq_sum_coeff_smul eV f, AddSubmonoidClass.coe_finsetSum] at h2
        simpa only [Subalgebra.coe_smul] using h2)

    rw [aeval_eq_sum_coeff_smul eχ f, ← Finset.sum_coe_sort]
    refine Eq.trans (Finset.sum_congr rfl fun m _ => ?_) hT
    rw [hE2]
    rfl

  letI : Algebra (MvPolynomial I ℚ_[p]) (rationalHeckeAlgebraOne p J) := eV.toRingHom.toAlgebra
  haveI : IsScalarTower ℚ_[p] (MvPolynomial I ℚ_[p]) (rationalHeckeAlgebraOne p J) :=
    IsScalarTower.of_algebraMap_eq (fun c => (eV.commutes c).symm)
  haveI : Algebra.IsIntegral ℚ_[p] (rationalHeckeAlgebraOne p J) := Algebra.IsIntegral.of_finite ℚ_[p] (rationalHeckeAlgebraOne p J)
  haveI : Algebra.IsIntegral (MvPolynomial I ℚ_[p]) (rationalHeckeAlgebraOne p J) := Algebra.IsIntegral.tower_top (R := ℚ_[p])
  have hker' : RingHom.ker (algebraMap (MvPolynomial I ℚ_[p]) (rationalHeckeAlgebraOne p J))
      ≤ RingHom.ker eχ.toRingHom := fun f hf => by
    rw [RingHom.mem_ker] at hf ⊢
    exact hker f hf
  obtain ⟨Λ, hΛ⟩ := RingHom.exists_comp_algebraMap_eq_of_isIntegral_of_isAlgClosed eχ.toRingHom hker'
  have hΛ' : ∀ f, Λ (eV f) = eχ f := fun f => RingHom.congr_fun hΛ f
  refine ⟨Λ, fun c => ?_, fun i => ?_⟩
  · rw [← eV.commutes c, hΛ', eχ.commutes]
  · rw [← heχ_X i, ← hΛ', heV_X]

end Engine

section QExp

open CongruenceSubgroup ModularForm ModularFormClass UpperHalfPlane Filter Function
open scoped MatrixGroups ModularForm



variable {M : ℕ} {k : ℤ}

theorem one_mem_strictPeriods (M : ℕ) : (1 : ℝ) ∈ (((Gamma1 M : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ))).strictPeriods := by
  rw [CongruenceSubgroup.strictPeriods_Gamma1]; exact AddSubgroup.mem_zmultiples _

theorem cusp_periodic (F : CuspForm (((Gamma1 M : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ))) k) : Periodic (⇑F ∘ ofComplex) 1 :=
  SlashInvariantFormClass.periodic_comp_ofComplex F (one_mem_strictPeriods M)

theorem cusp_holo (F : CuspForm (((Gamma1 M : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ))) k) :
    MDifferentiable (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ) (⇑F) := F.holo'

theorem cusp_bdd (F : CuspForm (((Gamma1 M : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ))) k) : IsBoundedAtImInfty (⇑F : ℍ → ℂ) := by
  haveI : Fact (IsCusp OnePoint.infty (((Gamma1 M : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)))) :=
    ⟨(((Gamma1 M : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ))).isCusp_of_mem_strictPeriods one_pos (one_mem_strictPeriods M)⟩
  exact ModularFormClass.bdd_at_infty F

theorem cusp_ext_of_qCoeff {F G : CuspForm (((Gamma1 M : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ))) k} (h : ∀ n : ℕ, qCoeff (⇑F) n = qCoeff (⇑G) n) :
    F = G :=
  DFunLike.coe_injective (UpperHalfPlane.eq_of_forall_qCoeff_eq (cusp_periodic F) (cusp_holo F)
    (cusp_bdd F) (cusp_periodic G) (cusp_holo G) (cusp_bdd G) h)

theorem qCoeff_smul (c : ℂ) (F : CuspForm (((Gamma1 M : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ))) k) (n : ℕ) :
    qCoeff (⇑(c • F)) n = c * qCoeff (⇑F) n := by
  have han : AnalyticAt ℂ (cuspFunction 1 (⇑F)) 0 :=
    analyticAt_cuspFunction_zero one_pos (cusp_periodic F) (cusp_holo F) (cusp_bdd F)
  rw [qCoeff, qCoeff, CuspForm.IsGLPos.coe_smul, qExpansion_smul han c, map_smul, smul_eq_mul]

theorem ne_zero_of_qCoeff_one (F : CuspForm (((Gamma1 M : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ))) k) (h1 : qCoeff (⇑F) 1 = 1) : F ≠ 0 := by
  rintro rfl
  rw [qCoeff, CuspForm.coe_zero, qExpansion_zero, map_zero] at h1
  exact zero_ne_one h1

end QExp

section Eigen

open CongruenceSubgroup ModularFormClass

variable {M : ℕ} {k : ℤ} {ε : DirichletCharacter ℂ M} {h : CuspForm (Gamma1 M) k}

theorem diamond_eigen (hh : CuspForm.IsEigenformWith ε h) {ℓ : ℕ} (hℓ : ℓ.Prime) (hℓM : ¬ ℓ ∣ M) :
    CuspForm.diamondLinOne M k ℓ h = ε (ℓ : ZMod M) • h :=
  hh.hasNebentypus.diamondLinOne_apply_eq_smul ((Nat.Prime.coprime_iff_not_dvd hℓ).2 hℓM)

theorem hecke_eigen (hh : CuspForm.IsEigenformWith ε h) {ℓ : ℕ} (hℓ : ℓ.Prime) (hℓM : ¬ ℓ ∣ M) :
    CuspForm.heckeTLinOne k hℓ hℓM h = qCoeff (⇑h) ℓ • h := by
  refine cusp_ext_of_qCoeff fun n => ?_
  rw [CuspForm.qCoeff_heckeTLinOne k hℓ hℓM h n, diamond_eigen hh hℓ hℓM, qCoeff_smul, qCoeff_smul,
    ← hh.hecke_of_not_dvd hℓ hℓM n]
  split_ifs <;> ring

theorem apply_eq_eval_smul {I : Type} (ρ : MvPolynomial I ℤ →+* Module.End ℂ (CuspForm (Gamma1 M) k))
    (lam : I → ℂ) (hX : ∀ i, ρ (MvPolynomial.X i) h = lam i • h) (f : MvPolynomial I ℤ) :
    ρ f h = MvPolynomial.eval₂ (Int.castRingHom ℂ) lam f • h := by
  induction f using MvPolynomial.induction_on with
  | C a =>
    rw [MvPolynomial.eval₂_C, eq_intCast (Int.castRingHom ℂ), Int.cast_smul_eq_zsmul,
      eq_intCast MvPolynomial.C, map_intCast, Module.End.intCast_apply]
  | add f g hf hg => rw [map_add, LinearMap.add_apply, hf, hg, MvPolynomial.eval₂_add, add_smul]
  | mul_X f i hf =>
    rw [map_mul, Module.End.mul_apply, hX i, map_smul, hf, MvPolynomial.eval₂_mul,
      MvPolynomial.eval₂_X, smul_smul, mul_comm]

end Eigen

section Packet

open CongruenceSubgroup ModularFormClass
open scoped ComplexConjugate

variable {M : ℕ} [NeZero M]

omit [NeZero M] in

theorem dirichlet_pow_totient (ε : DirichletCharacter ℂ M) {ℓ : ℕ} (hℓ : Nat.Coprime ℓ M) :
    ε (ℓ : ZMod M) ^ Nat.totient M = 1 := by
  rw [← ZMod.coe_unitOfCoprime ℓ hℓ, ← map_pow, ← Units.val_pow_eq_pow_val, ZMod.pow_totient,
    Units.val_one, map_one]

theorem totient_ne_zero : Nat.totient M ≠ 0 := (Nat.totient_pos.2 (NeZero.pos M)).ne'

theorem dirichlet_ne_zero (ε : DirichletCharacter ℂ M) {ℓ : ℕ} (hℓ : Nat.Coprime ℓ M) :
    ε (ℓ : ZMod M) ≠ 0 := fun h0 => by
  have h := dirichlet_pow_totient ε hℓ
  rw [h0, zero_pow totient_ne_zero] at h
  exact zero_ne_one h

theorem conj_dirichlet (ε : DirichletCharacter ℂ M) {ℓ : ℕ} (hℓ : Nat.Coprime ℓ M) :
    conj (ε (ℓ : ZMod M)) = (ε (ℓ : ZMod M))⁻¹ :=
  (Complex.inv_eq_conj (Complex.norm_eq_one_of_pow_eq_one (dirichlet_pow_totient ε hℓ)
    totient_ne_zero)).symm

theorem inv_dirichlet_eq_pow (ε : DirichletCharacter ℂ M) {ℓ : ℕ} (hℓ : Nat.Coprime ℓ M) :
    (ε (ℓ : ZMod M))⁻¹ = ε (ℓ : ZMod M) ^ (Nat.totient M - 1) := by
  exact inv_eq_of_mul_eq_one_left (by rw [pow_sub_one_mul totient_ne_zero, dirichlet_pow_totient ε hℓ])

variable {ε : DirichletCharacter ℂ M} {h : CuspForm (Gamma1 M) 2}
  {R : Type} [CommRing R] (toC : R →+* ℂ) (b e : ℕ → R)

def eInv (M : ℕ) (e : ℕ → R) (ℓ : ℕ) : R := e ℓ ^ (Nat.totient M - 1)

theorem e_mul_eInv (htoC : Function.Injective toC) {ℓ : ℕ} (hℓ : Nat.Coprime ℓ M)
    (he : toC (e ℓ) = ε (ℓ : ZMod M)) : e ℓ * eInv M e ℓ = 1 := by
  apply htoC
  rw [map_mul, eInv, map_pow, he, map_one, mul_comm, pow_sub_one_mul totient_ne_zero,
    dirichlet_pow_totient ε hℓ]

theorem toC_eInv {ℓ : ℕ} (hℓ : Nat.Coprime ℓ M) (he : toC (e ℓ) = ε (ℓ : ZMod M)) :
    toC (eInv M e ℓ) = conj (ε (ℓ : ZMod M)) := by
  rw [eInv, map_pow, he, conj_dirichlet ε hℓ, inv_dirichlet_eq_pow ε hℓ]

theorem toC_eInv_mul_b (hh : CuspForm.IsEigenformWith ε h) {ℓ : ℕ} (hℓp : ℓ.Prime) (hℓM : ¬ ℓ ∣ M)
    (hb : toC (b ℓ) = qCoeff (⇑h) ℓ) (he : toC (e ℓ) = ε (ℓ : ZMod M)) :
    toC (eInv M e ℓ * b ℓ) = conj (qCoeff (⇑h) ℓ) := by
  have hℓ : Nat.Coprime ℓ M := (Nat.Prime.coprime_iff_not_dvd hℓp).2 hℓM
  have hadj := CuspForm.conj_heckeEigenvalue_eq_of_hasNebentypus M 2 ε h
    (ne_zero_of_qCoeff_one h hh.qCoeff_one) hh.hasNebentypus ℓ hℓp hℓM (qCoeff (⇑h) ℓ)
    (fun n => hh.hecke_of_not_dvd hℓp hℓM n)
  rw [map_mul, hb, toC_eInv toC e hℓ he, hadj, MulChar.inv_apply_eq_inv', conj_dirichlet ε hℓ]

end Packet

section Concrete

open CongruenceSubgroup ModularFormClass
open scoped ComplexConjugate

def Idx (M : ℕ) (S : Set ℕ) : Type := {ℓ : Nat.Primes // ¬ (ℓ : ℕ) ∣ M ∧ (ℓ : ℕ) ∉ S}

def vGen (M : ℕ) (S : Set ℕ) : Idx M S ⊕ Idx M S → Nat.Primes ⊕ ℕ :=
  Sum.elim (fun i => Sum.inl i.1) (fun i => Sum.inr (i.1 : ℕ))

def gDev (M : ℕ) (S : Set ℕ) {R : Type} [CommRing R] (b e : ℕ → R) : Idx M S ⊕ Idx M S → R :=
  Sum.elim (fun i => eInv M e i.1 * b i.1) (fun i => eInv M e i.1)

def lamC (M : ℕ) (S : Set ℕ) (ε : DirichletCharacter ℂ M) (h : CuspForm (Gamma1 M) 2) :
    Idx M S ⊕ Idx M S → ℂ :=
  Sum.elim (fun i => qCoeff (⇑h) i.1) (fun i => ε ((i.1 : ℕ) : ZMod M))

variable (M : ℕ) [NeZero M] {ε : DirichletCharacter ℂ M} {h : CuspForm (Gamma1 M) 2}

set_option maxHeartbeats 6400000 in

theorem hrel_jOne (hh : CuspForm.IsEigenformWith ε h)
    (hin : HeckeDiamondInputsAll M) (hcomm : HeckeDiamondCommuteBar M) (S : Set ℕ)
    (R : Type) [CommRing R] (toC : R →+* ℂ) (htoC : Function.Injective toC) (b e : ℕ → R)
    (hb : ∀ ℓ : ℕ, ℓ.Prime → ¬ ℓ ∣ M → ℓ ∉ S → toC (b ℓ) = qCoeff h ℓ)
    (he : ∀ ℓ : ℕ, ℓ.Prime → ¬ ℓ ∣ M → ℓ ∉ S → toC (e ℓ) = ε (ℓ : ZMod M))
    (f : MvPolynomial (Idx M S ⊕ Idx M S) ℤ)
    (hf : letI := heckeModuleOneBar M
      MvPolynomial.eval₂Hom (Int.castRingHom HeckeAlgOne) (fun i => MvPolynomial.X (vGen M S i)) f
        ∈ Module.annihilator HeckeAlgOne (JOne M)) :
    MvPolynomial.eval₂Hom (Int.castRingHom R) (gDev M S b e) f = 0 := by
  letI := heckeModuleOneBar M
  obtain ⟨Φ, -, hΦT, hΦD⟩ := exists_injective_ringHom_adjoin_heckeDiamondGenBar_cuspForm M hin hcomm

  obtain ⟨rJ, hrJ⟩ : ∃ rJ : MvPolynomial (Idx M S ⊕ Idx M S) ℤ →+* HeckeAlgOne,
      rJ = MvPolynomial.eval₂Hom (Int.castRingHom HeckeAlgOne)
        (fun i => MvPolynomial.X (vGen M S i)) := ⟨_, rfl⟩
  rw [← hrJ] at hf
  have hrJ_X : ∀ i, rJ (MvPolynomial.X i) = MvPolynomial.X (vGen M S i) := fun i => by
    rw [hrJ]; exact MvPolynomial.eval₂_X _ _ _

  obtain ⟨ρ, hρ⟩ : ∃ ρ : MvPolynomial (Idx M S ⊕ Idx M S) ℤ →+*
      Module.End ℂ (CuspForm (Gamma1 M) 2), ∀ q, ρ q = Φ (heckeEvalOneBarAux hcomm (rJ q)) :=
    ⟨Φ.comp ((heckeEvalOneBarAux hcomm).toRingHom.comp rJ), fun _ => rfl⟩

  have hρX : ∀ i, ρ (MvPolynomial.X i) h = lamC M S ε h i • h := by
    rintro (⟨ℓ, hℓM, hℓS⟩ | ⟨ℓ, hℓM, hℓS⟩)
    · rw [hρ, hrJ_X]
      show Φ (heckeEvalOneBarAux hcomm (MvPolynomial.X (Sum.inl ℓ))) h = qCoeff (⇑h) ℓ • h
      rw [heckeEvalOneBarAux_X]
      have e0 : (⟨heckeDiamondGenBar M (Sum.inl ℓ), Algebra.subset_adjoin (Set.mem_range_self _)⟩ :
            ↥(Algebra.adjoin ℤ (Set.range (heckeDiamondGenBar M))))
          = ⟨heckeOperatorOneBar M ℓ, Algebra.subset_adjoin (Set.mem_range_self (Sum.inl ℓ))⟩ :=
        Subtype.ext (heckeDiamondGenBar_inl M ℓ)
      rw [e0, hΦT ℓ hℓM, hecke_eigen hh ℓ.prop hℓM]
    · rw [hρ, hrJ_X]
      show Φ (heckeEvalOneBarAux hcomm (MvPolynomial.X (Sum.inr (ℓ : ℕ)))) h = ε ((ℓ : ℕ) : ZMod M) • h
      rw [heckeEvalOneBarAux_X]
      have e0 : (⟨heckeDiamondGenBar M (Sum.inr (ℓ : ℕ)), Algebra.subset_adjoin (Set.mem_range_self _)⟩ :
            ↥(Algebra.adjoin ℤ (Set.range (heckeDiamondGenBar M))))
          = ⟨diamondOneBar M ℓ, Algebra.subset_adjoin (Set.mem_range_self (Sum.inr (ℓ : ℕ)))⟩ :=
        Subtype.ext (heckeDiamondGenBar_inr M ℓ)
      rw [e0, hΦD ℓ ((Nat.Prime.coprime_iff_not_dvd ℓ.prop).2 hℓM), diamond_eigen hh ℓ.prop hℓM]

  have h1 : heckeEvalOneBar hcomm (rJ f) = 0 := by
    refine LinearMap.ext fun x => ?_
    rw [← heckeModuleOneBar_smul_def hcomm, LinearMap.zero_apply]
    exact Module.mem_annihilator.1 hf x
  have h2 : heckeEvalOneBarAux hcomm (rJ f) = 0 :=
    Subtype.ext ((heckeEvalOneBar_apply hcomm (rJ f)).symm.trans
      (h1.trans (ZeroMemClass.coe_zero _).symm))
  have h3 : ρ f = 0 := by rw [hρ, h2, map_zero]

  have h4 : MvPolynomial.eval₂ (Int.castRingHom ℂ) (lamC M S ε h) f = 0 := by
    have e1 := apply_eq_eval_smul ρ (lamC M S ε h) hρX f
    rw [h3, LinearMap.zero_apply] at e1
    by_contra hne
    apply ne_zero_of_qCoeff_one h hh.qCoeff_one
    calc h = (MvPolynomial.eval₂ (Int.castRingHom ℂ) (lamC M S ε h) f)⁻¹ •
          (MvPolynomial.eval₂ (Int.castRingHom ℂ) (lamC M S ε h) f • h) := by
            rw [smul_smul, inv_mul_cancel₀ hne, one_smul]
      _ = 0 := by rw [← e1, smul_zero]

  have h5 : MvPolynomial.eval₂ (Int.castRingHom ℂ) (conj ∘ lamC M S ε h) f = 0 := by
    have e1 := MvPolynomial.eval₂_comp_left (starRingEnd ℂ) (Int.castRingHom ℂ) (lamC M S ε h) f
    rw [h4, map_zero, RingHom.ext_int ((starRingEnd ℂ).comp (Int.castRingHom ℂ)) (Int.castRingHom ℂ)]
      at e1
    exact e1.symm

  have h6 : conj ∘ lamC M S ε h = toC ∘ gDev M S b e := by
    funext i
    rcases i with ⟨ℓ, hℓM, hℓS⟩ | ⟨ℓ, hℓM, hℓS⟩
    · show conj (qCoeff (⇑h) ℓ) = toC (eInv M e ℓ * b ℓ)
      exact (toC_eInv_mul_b toC b e hh ℓ.prop hℓM (hb ℓ ℓ.prop hℓM hℓS) (he ℓ ℓ.prop hℓM hℓS)).symm
    · show conj (ε ((ℓ : ℕ) : ZMod M)) = toC (eInv M e ℓ)
      exact (toC_eInv toC e ((Nat.Prime.coprime_iff_not_dvd ℓ.prop).2 hℓM)
        (he ℓ ℓ.prop hℓM hℓS)).symm

  have h7 : toC (MvPolynomial.eval₂ (Int.castRingHom R) (gDev M S b e) f) = 0 := by
    rw [MvPolynomial.eval₂_comp_left toC (Int.castRingHom R) (gDev M S b e) f,
      RingHom.ext_int (toC.comp (Int.castRingHom R)) (Int.castRingHom ℂ), ← h6, h5]
  have h8 : MvPolynomial.eval₂ (Int.castRingHom R) (gDev M S b e) f = 0 :=
    htoC (h7.trans (map_zero toC).symm)
  rw [MvPolynomial.coe_eval₂Hom]
  exact h8

end Concrete

end H2G1TR

open _root_.ModularCurve hiding IsCusp in
theorem solution
    {M : ℕ} [NeZero M] {ε : DirichletCharacter ℂ M} {h : CuspForm (CongruenceSubgroup.Gamma1 M) 2}
    (hh : CuspForm.IsEigenformWith ε h) (p : ℕ) [Fact p.Prime]
    (hin : ModularCurve.HeckeDiamondInputsAll M) (hcomm : ModularCurve.HeckeDiamondCommuteBar M)
    (S : Set ℕ) (Ω : Type) [Field Ω] [IsAlgClosed Ω] [Algebra ℚ_[p] Ω]
    (R : Type) [CommRing R] (toC : R →+* ℂ) (htoC : Function.Injective toC) (ψ : R →+* Ω)
    (b e : ℕ → R)
    (hb : ∀ ℓ : ℕ, ℓ.Prime → ¬ ℓ ∣ M → ℓ ∉ S → toC (b ℓ) = ModularFormClass.qCoeff h ℓ)
    (he : ∀ ℓ : ℕ, ℓ.Prime → ¬ ℓ ∣ M → ℓ ∉ S → toC (e ℓ) = ε (ℓ : ZMod M)) :
    letI := ModularCurve.heckeModuleOneBar M
    ∃ Λ : ↥(ModularCurve.rationalHeckeAlgebraOne p (ModularCurve.JOne M)) →+* Ω,
      (∀ c : ℚ_[p],
        Λ (algebraMap ℚ_[p] ↥(ModularCurve.rationalHeckeAlgebraOne p (ModularCurve.JOne M)) c)
          = algebraMap ℚ_[p] Ω c) ∧
      ∀ (ℓ : ℕ) (hℓ : ℓ.Prime), ¬ ℓ ∣ M → ℓ ∉ S →
        Λ (ModularCurve.rationalHeckeOne p (ModularCurve.JOne M) ⟨ℓ, hℓ⟩) * ψ (e ℓ) = ψ (b ℓ) ∧
        Λ (ModularCurve.rationalDiamondOne p (ModularCurve.JOne M) ℓ) * ψ (e ℓ) = 1 := by
  letI := ModularCurve.heckeModuleOneBar M
  haveI : Module.Finite ℤ_[p] (TateModule p (ModularCurve.JOne M)) :=
    ModularCurve.moduleFinite_padicInt_tateModule_jOne M p

  have E1 := H2G1TR.engine p (ModularCurve.JOne M) (I := H2G1TR.Idx M S ⊕ H2G1TR.Idx M S)
    (H2G1TR.vGen M S) R (H2G1TR.gDev M S b e)
  have E2 := E1 (fun f hf => H2G1TR.hrel_jOne M hh hin hcomm S R toC htoC b e hb he f hf)
  have E3 := E2 (fun t ht =>
    ModularCurve.linearIndependent_rationalHeckeRepOne_of_linearIndependent M p hin hcomm t ht)
  have E4 := E3 Ω ψ
  cases E4 with
  | intro Λ hΛ =>
    have hc := hΛ.1
    have hgen := hΛ.2
    refine ⟨Λ, hc, ?_⟩
    intro ℓ hℓ hℓM hℓS
    have hcop : Nat.Coprime ℓ M := (Nat.Prime.coprime_iff_not_dvd hℓ).2 hℓM
    have hunit : e ℓ * H2G1TR.eInv M e ℓ = 1 :=
      H2G1TR.e_mul_eInv toC e htoC hcop (he ℓ hℓ hℓM hℓS)
    have h1 : Λ (ModularCurve.rationalHeckeOne p (ModularCurve.JOne M) ⟨ℓ, hℓ⟩)
        = ψ (H2G1TR.eInv M e ℓ * b ℓ) := hgen (Sum.inl ⟨⟨ℓ, hℓ⟩, hℓM, hℓS⟩)
    have h2 : Λ (ModularCurve.rationalDiamondOne p (ModularCurve.JOne M) ℓ)
        = ψ (H2G1TR.eInv M e ℓ) := hgen (Sum.inr ⟨⟨ℓ, hℓ⟩, hℓM, hℓS⟩)
    refine ⟨?_, ?_⟩
    · rw [h1, ← map_mul, mul_comm, ← mul_assoc, hunit, one_mul]
    · rw [h2, ← map_mul, mul_comm, hunit, map_one]
