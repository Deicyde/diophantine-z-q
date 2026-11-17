/-
Vendored from anthropics/fermats-last-theorem @ 6e837e75355538c7f80bab5b956861e86c4eacc2.
Original module: P2M.Sol.S_AlgebraicGeometry_Scheme_TwoAffineOpenCover_finrank_H1_sectionsOf_unit_eq_and_finrank_H0_eq_one. Apache-2.0.
Modification notice (CloudB3 Worker16, 2026-11-16): relocated imports; removed
nonessential negative-attribute and reactivation scaffolding; expanded namespace/open/export
helpers to ordinary commands and resolved metadata aliases directly. Mathematical proof
bodies retained, subject to documented Lean 4.35 API adaptations.
Full original notices/credits: NOTICE.upstream, ATTRIBUTION.upstream.md, LICENSE in this vendor root.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_NeronModelPropertyBundleCarrier
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_SmoothProperCurveBase
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_TwoChartCechSectionsOf
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_AlgebraicCurve_CurveModel
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_AlgebraicCurve_AdelicIndex
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_AlgebraicCurve_Repartitions
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_Scheme_TwoAffineOpenCover_finrank_cechDiff_baseChange_of_isAlgClosed
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicCurve_CurveModel_eq_genusFF_of_forall_ell_sub_ell_eq
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicCurve_nonempty_algEquiv_functionField_of_iso
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicCurve_genusFF_eq_of_algEquiv
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_SmoothProperCurve_exists_curveModel_riemannRoch_of_isAlgClosed
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_geometricallyIntegral_of_isAlgClosed
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.P2M.Util

set_option backward.isDefEq.respectTransparency false

namespace P2MW.S_AlgebraicGeometry_Scheme_TwoAffineOpenCover_finrank_H1_sectionsOf_unit_eq_and_finrank_H0_eq_one

set_option autoImplicit false

universe u

open scoped TensorProduct
open CategoryTheory
open CategoryTheory.Limits
open AlgebraicGeometry
open AlgebraicGeometry.SmoothProperCurve
open NeronModelInfra
open AlgebraicCurve hiding genus cechDiff

namespace GenusH1

section Generic

variable {R : Type u} [CommRing R] {𝒰 𝒰' : TwoChartCech.Cover.{u, u} R}
  (S : TwoChartCech.Sections.{u, u, u} 𝒰) (S' : TwoChartCech.Sections.{u, u, u} 𝒰')

theorem h0h1_of_equiv (g0 : S.M0 ≃ₗ[R] S'.M0) (g1 : S.M1 ≃ₗ[R] S'.M1) (g01 : S.M01 ≃ₗ[R] S'.M01)
    (h0 : ∀ m, S'.r0 (g0 m) = g01 (S.r0 m)) (h1 : ∀ m, S'.r1 (g1 m) = g01 (S.r1 m)) :
    Nonempty (S.H0 ≃ₗ[R] S'.H0) ∧ Nonempty (S.H1 ≃ₗ[R] S'.H1) := by
  let G : (S.M0 × S.M1) ≃ₗ[R] (S'.M0 × S'.M1) := g0.prodCongr g1
  have hG : ∀ p : S.M0 × S.M1, G p = (g0 p.1, g1 p.2) := fun p => rfl
  have hd : ∀ p, S'.cechDiff (G p) = g01 (S.cechDiff p) := by
    intro p
    rw [hG, TwoChartCech.Sections.cechDiff_apply, TwoChartCech.Sections.cechDiff_apply, map_sub, h0, h1]
  refine ⟨⟨LinearEquiv.ofSubmodules G S.H0 S'.H0 ?_⟩, ⟨Submodule.Quotient.equiv _ _ g01 ?_⟩⟩
  · ext q
    simp only [Submodule.mem_map, LinearMap.mem_ker, LinearEquiv.coe_coe]
    constructor
    · rintro ⟨p, hp, rfl⟩
      rw [hd, hp, map_zero]
    · intro hq
      refine ⟨G.symm q, ?_, G.apply_symm_apply q⟩
      apply g01.injective
      rw [← hd, G.apply_symm_apply, hq, map_zero]
  · ext y
    simp only [Submodule.mem_map, LinearMap.mem_range, LinearEquiv.coe_coe]
    constructor
    · rintro ⟨_, ⟨p, rfl⟩, rfl⟩
      exact ⟨G p, hd p⟩
    · rintro ⟨q, rfl⟩
      exact ⟨S.cechDiff (G.symm q), ⟨_, rfl⟩, by rw [← hd, G.apply_symm_apply]⟩

end Generic

section UnitEq

variable {R : Type u} [CommRing R] {X : Scheme.{u}} (𝒱 : X.TwoAffineOpenCover) (x : X ⟶ Spec (.of R))

noncomputable def idEquiv0 :
    (𝒱.sectionsOf x (SheafOfModules.unit X.ringCatSheaf : X.Modules)).M0 ≃ₗ[R] (𝒱.structureSheafSections x).M0 :=
  { toFun := fun m => (show Γ(X, 𝒱.U0) from m)
    invFun := fun a => (show Γ((SheafOfModules.unit X.ringCatSheaf : X.Modules), 𝒱.U0) from a)
    map_add' := fun a b => rfl
    map_smul' := fun r m => rfl
    left_inv := fun m => rfl
    right_inv := fun a => rfl }

noncomputable def idEquiv1 :
    (𝒱.sectionsOf x (SheafOfModules.unit X.ringCatSheaf : X.Modules)).M1 ≃ₗ[R] (𝒱.structureSheafSections x).M1 :=
  { toFun := fun m => (show Γ(X, 𝒱.U1) from m)
    invFun := fun a => (show Γ((SheafOfModules.unit X.ringCatSheaf : X.Modules), 𝒱.U1) from a)
    map_add' := fun a b => rfl
    map_smul' := fun r m => rfl
    left_inv := fun m => rfl
    right_inv := fun a => rfl }

noncomputable def idEquiv01 :
    (𝒱.sectionsOf x (SheafOfModules.unit X.ringCatSheaf : X.Modules)).M01 ≃ₗ[R]
      (𝒱.structureSheafSections x).M01 :=
  { toFun := fun m => (show Γ(X, 𝒱.U0 ⊓ 𝒱.U1) from m)
    invFun := fun a => (show Γ((SheafOfModules.unit X.ringCatSheaf : X.Modules), 𝒱.U0 ⊓ 𝒱.U1) from a)
    map_add' := fun a b => rfl
    map_smul' := fun r m => rfl
    left_inv := fun m => rfl
    right_inv := fun a => rfl }

theorem unit_equiv :
    Nonempty ((𝒱.sectionsOf x (SheafOfModules.unit X.ringCatSheaf : X.Modules)).H0 ≃ₗ[R]
        (𝒱.structureSheafSections x).H0) ∧
      Nonempty ((𝒱.sectionsOf x (SheafOfModules.unit X.ringCatSheaf : X.Modules)).H1 ≃ₗ[R]
        (𝒱.structureSheafSections x).H1) := by
  refine h0h1_of_equiv _ _ (idEquiv0 𝒱 x) (idEquiv1 𝒱 x)
    (idEquiv01 𝒱 x) ?_ ?_
  · intro m; rfl
  · intro m
    show (1 : Γ(X, 𝒱.U0 ⊓ 𝒱.U1)) * _ = _
    rw [one_mul]; rfl

end UnitEq

theorem finrank_baseChange_self {K : Type u} [Field K] {A B : Type u} [AddCommGroup A] [Module K A]
    [AddCommGroup B] [Module K B] (d : A →ₗ[K] B) :
    Module.finrank K (LinearMap.ker (d.baseChange K)) = Module.finrank K (LinearMap.ker d) ∧
      Module.finrank K ((K ⊗[K] B) ⧸ LinearMap.range (d.baseChange K)) =
        Module.finrank K (B ⧸ LinearMap.range d) := by
  let eA := TensorProduct.lid K A
  let eB := TensorProduct.lid K B
  have hd : ∀ z, eB (d.baseChange K z) = d (eA z) := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul a m => simp [eA, eB, LinearMap.baseChange_tmul, TensorProduct.lid_tmul]
    | add z w hz hw => rw [map_add, map_add, hz, hw, map_add, map_add]
  constructor
  · refine (LinearEquiv.ofSubmodules eA (LinearMap.ker (d.baseChange K)) (LinearMap.ker d) ?_).finrank_eq
    ext q
    simp only [Submodule.mem_map, LinearMap.mem_ker, LinearEquiv.coe_coe]
    constructor
    · rintro ⟨p, hp, rfl⟩
      rw [← hd, hp, map_zero]
    · intro hq
      refine ⟨eA.symm q, ?_, eA.apply_symm_apply q⟩
      apply eB.injective
      rw [hd, eA.apply_symm_apply, hq, map_zero]
  · refine (Submodule.Quotient.equiv _ _ eB ?_).finrank_eq
    ext y
    simp only [Submodule.mem_map, LinearMap.mem_range, LinearEquiv.coe_coe]
    constructor
    · rintro ⟨_, ⟨p, rfl⟩, rfl⟩
      exact ⟨eA p, (hd p).symm⟩
    · rintro ⟨q, rfl⟩
      exact ⟨d.baseChange K (eA.symm q), ⟨_, rfl⟩, by rw [hd, eA.apply_symm_apply]⟩

theorem main
    (K : Type u) [Field K] [IsAlgClosed K] {X : Scheme.{u}} (x : X ⟶ Spec (CommRingCat.of K))
    [IsIntegral X] [IsProper x] [SmoothOfRelativeDimension 1 x]
    (g : ℕ)
    (hg : ∀ (L : Type u) [Field L] [Algebra K L] (M : CurveModel K L) (e : M.C ≅ X)
      (_ : e.hom ≫ x = M.toBase) (Kc : Divisor K L) (g' : ℕ),
      (∀ D : Divisor K L, (ell D : ℤ) - ell (Kc - D) = Divisor.degree D + 1 - g') → g' = g)
    (𝒱 : X.TwoAffineOpenCover) :
    Module.finrank K (𝒱.sectionsOf x (SheafOfModules.unit X.ringCatSheaf : X.Modules)).H1 = g ∧
      Module.finrank K (𝒱.sectionsOf x (SheafOfModules.unit X.ringCatSheaf : X.Modules)).H0 = 1 := by
  classical

  obtain ⟨⟨eH0⟩, ⟨eH1⟩⟩ := unit_equiv 𝒱 x
  rw [eH1.finrank_eq, eH0.finrank_eq]

  haveI : GeometricallyIntegral x := AlgebraicGeometry.geometricallyIntegral_of_isAlgClosed x
  haveI : IsIntegral (pullback x (Scheme.TwoAffineOpenCover.specMap K K)) := inferInstance
  obtain ⟨-, hk0, hk1⟩ := Scheme.TwoAffineOpenCover.finrank_cechDiff_baseChange_of_isAlgClosed 𝒱 x K
  obtain ⟨hb0, hb1⟩ := finrank_baseChange_self (𝒱.structureSheafSections x).cechDiff

  obtain ⟨L, _, _, M, e, he, Kc, g₀, hRR⟩ :=
    exists_curveModel_riemannRoch_of_isAlgClosed K x K (Scheme.TwoAffineOpenCover.specMap K K)
  have h1 : g₀ = genusFF K L := CurveModel.eq_genusFF_of_forall_ell_sub_ell_eq M hRR
  have h2 : genusFF K L = (by
      letI := (baseToFunctionField
        (pullback.snd x (Scheme.TwoAffineOpenCover.specMap K K))).toAlgebra
      exact genusFF K (pullback x (Scheme.TwoAffineOpenCover.specMap K K)).functionField) := by
    letI := M.functionFieldAlgebra
    letI := (baseToFunctionField
      (pullback.snd x (Scheme.TwoAffineOpenCover.specMap K K))).toAlgebra
    obtain ⟨φ⟩ := nonempty_algEquiv_functionField_of_iso M.toBase
      (pullback.snd x (Scheme.TwoAffineOpenCover.specMap K K)) e he
    exact (genusFF_eq_of_algEquiv M.ffAlgEquiv).trans (genusFF_eq_of_algEquiv φ)

  have hspec : Scheme.TwoAffineOpenCover.specMap K K = 𝟙 _ := by
    show Spec.map (CommRingCat.ofHom (algebraMap K K)) = 𝟙 _
    rw [Algebra.algebraMap_self, CommRingCat.ofHom_id]
    exact Spec.map_id _
  have sq : IsPullback (𝟙 X) x x (Scheme.TwoAffineOpenCover.specMap K K) := by
    rw [hspec]; exact IsPullback.of_horiz_isIso ⟨by simp⟩
  let eX : X ≅ pullback x (Scheme.TwoAffineOpenCover.specMap K K) := sq.isoPullback
  have heX : eX.hom ≫ pullback.snd x (Scheme.TwoAffineOpenCover.specMap K K) = x := sq.isoPullback_hom_snd
  have heX' : eX.inv ≫ x = pullback.snd x (Scheme.TwoAffineOpenCover.specMap K K) := by
    rw [Iso.inv_comp_eq]; exact heX.symm
  have he' : (e ≪≫ eX.symm).hom ≫ x = M.toBase := by
    simp only [Iso.trans_hom, Iso.symm_hom, Category.assoc]
    rw [heX']; exact he
  have h3 : g₀ = g := hg L M (e ≪≫ eX.symm) he' Kc g₀ hRR

  constructor
  · show Module.finrank K ((𝒱.structureSheafSections x).M01 ⧸ LinearMap.range (𝒱.structureSheafSections x).cechDiff) = g
    rw [← hb1, hk1, ← h2, ← h1, h3]
  · show Module.finrank K (LinearMap.ker (𝒱.structureSheafSections x).cechDiff) = 1
    rw [← hb0, hk0]

end GenusH1

theorem solution
    (K : Type u) [Field K] [IsAlgClosed K] {X : Scheme.{u}} (x : X ⟶ Spec (CommRingCat.of K))
    [IsIntegral X] [IsProper x] [SmoothOfRelativeDimension 1 x]
    (g : ℕ)
    (hg : ∀ (L : Type u) [Field L] [Algebra K L] (M : CurveModel K L) (e : M.C ≅ X)
      (_ : e.hom ≫ x = M.toBase) (Kc : Divisor K L) (g' : ℕ),
      (∀ D : Divisor K L, (ell D : ℤ) - ell (Kc - D) = Divisor.degree D + 1 - g') → g' = g)
    (𝒱 : X.TwoAffineOpenCover) :
    Module.finrank K (𝒱.sectionsOf x (SheafOfModules.unit X.ringCatSheaf : X.Modules)).H1 = g ∧
      Module.finrank K (𝒱.sectionsOf x (SheafOfModules.unit X.ringCatSheaf : X.Modules)).H0 = 1 :=
  GenusH1.main K x g hg 𝒱
