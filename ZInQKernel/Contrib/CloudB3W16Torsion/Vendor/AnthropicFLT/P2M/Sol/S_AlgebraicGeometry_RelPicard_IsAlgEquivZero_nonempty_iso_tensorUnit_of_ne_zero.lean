/-
Vendored from anthropics/fermats-last-theorem @ 6e837e75355538c7f80bab5b956861e86c4eacc2.
Original module: P2M.Sol.S_AlgebraicGeometry_RelPicard_IsAlgEquivZero_nonempty_iso_tensorUnit_of_ne_zero. Apache-2.0.
Modification notice (CloudB3 Worker16, 2026-11-16): relocated imports; removed
nonessential negative-attribute and reactivation scaffolding; expanded namespace/open/export
helpers to ordinary commands and resolved metadata aliases directly. Mathematical proof
bodies retained, subject to documented Lean 4.35 API adaptations.
Full original notices/credits: NOTICE.upstream, ATTRIBUTION.upstream.md, LICENSE in this vendor root.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroCut
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_SheafOfModules_Monoidal
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_TwoChartCechSectionsOf
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_ModulesSectionZeroScheme
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_IdealSheafModule
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_RelEffCartierDiv
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_RelEffCartierDivSum
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_AlgebraicCurve_RelCartier
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_RelEffCartierDiv_exists_I_eq_zeroSchemeIdeal_of_eulerChar_eq
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_RelPicard_IsAlgEquivZero_eulerChar_sectionsOf_tensor_eq
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_Scheme_TwoAffineOpenCover_exists_linearEquiv_sectionsOf_of_iso
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_IsInvertible_nonempty_mul_invModule_iso_tensor
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_IsInvertible_isInvertible_invModule
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_isIso_ev_app_tensorUnit
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.P2M.Util

set_option backward.isDefEq.respectTransparency false

namespace P2MW.S_AlgebraicGeometry_RelPicard_IsAlgEquivZero_nonempty_iso_tensorUnit_of_ne_zero

set_option autoImplicit false

universe u
open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.MonoidalCategory
open AlgebraicGeometry
open AlgebraicGeometry.RelPicard

namespace AlgZeroTrivGlue

set_option maxHeartbeats 6400000 in
set_option synthInstance.maxHeartbeats 1600000 in

noncomputable def isoUnitOfIdempotentOfInverse {C : Type*} [Category C] [MonoidalCategory C] {N M : C}
    (e : N ≅ N ⊗ N) (p : N ⊗ M ≅ 𝟙_ C) : N ≅ 𝟙_ C :=
  (ρ_ N).symm ≪≫ whiskerLeftIso N p.symm ≪≫ (α_ N N M).symm ≪≫ whiskerRightIso e.symm M ≪≫ p

set_option maxHeartbeats 6400000 in
set_option synthInstance.maxHeartbeats 1600000 in

theorem nonempty_invModule_top_iso (Y : Scheme.{u}) :
    Nonempty ((⊤ : Y.IdealSheafData).invModule ≅ 𝟙_ Y.Modules) := by
  have hT : (⊤ : Y.IdealSheafData).IsCartierFLT := Scheme.IdealSheafData.isInvertible_topFLT

  obtain ⟨m⟩ := Scheme.IdealSheafData.IsCartierFLT.nonempty_mul_invModule_iso_tensor hT hT
  have e : (⊤ : Y.IdealSheafData).invModule ≅ (⊤ : Y.IdealSheafData).invModule ⊗ (⊤ : Y.IdealSheafData).invModule :=
    eqToIso (congrArg Scheme.IdealSheafData.invModule (Scheme.IdealSheafData.mul_top ⊤).symm) ≪≫ m

  have hN : Scheme.Modules.IsInvertible (⊤ : Y.IdealSheafData).invModule :=
    Scheme.IdealSheafData.IsCartierFLT.isInvertible_invModule hT
  have hev := Scheme.Modules.IsInvertible.isIso_ev_app_tensorUnit hN
  exact ⟨isoUnitOfIdempotentOfInverse e (@asIso _ _ _ _ ((ihom.ev (⊤ : Y.IdealSheafData).invModule).app (𝟙_ Y.Modules)) hev)⟩

set_option maxHeartbeats 6400000 in
set_option synthInstance.maxHeartbeats 1600000 in

theorem nonempty_lineBundle_iso_of_degree_zero {𝒞 S : Scheme.{u}} {f : 𝒞 ⟶ S} {T : Scheme.{u}} {g : T ⟶ S}
    (D : RelEffCartierDiv f 0 g) : Nonempty (D.lineBundle ≅ 𝟙_ (pullback f g).Modules) := by
  obtain ⟨e⟩ := nonempty_invModule_top_iso (pullback f g)
  exact ⟨eqToIso (congrArg Scheme.IdealSheafData.invModule D.I_eq_top_of_degree_zero) ≪≫ e⟩

set_option maxHeartbeats 6400000 in
set_option synthInstance.maxHeartbeats 1600000 in

noncomputable def isoPullbackInvPullbackObj {X Y : Scheme.{u}} (p : X ⟶ Y) [IsIso p] (L : Y.Modules) :
    L ≅ (Scheme.Modules.pullback (inv p)).obj ((Scheme.Modules.pullback p).obj L) :=
  ((Scheme.Modules.pullbackComp (inv p) p ≪≫ Scheme.Modules.pullbackCongr (IsIso.inv_hom_id p) ≪≫
      Scheme.Modules.pullbackId Y).app L).symm

set_option maxHeartbeats 6400000 in
set_option synthInstance.maxHeartbeats 1600000 in

theorem eq_zero_of_pullback_map_eq_zero {X Y : Scheme.{u}} (p : X ⟶ Y) [IsIso p]
    {A B : Y.Modules} (φ : A ⟶ B) (h : (Scheme.Modules.pullback p).map φ = 0) : φ = 0 := by

  have hn : (Scheme.Modules.pullback (inv p)).map ((Scheme.Modules.pullback p).map φ) ≫
      (isoPullbackInvPullbackObj p B).inv = (isoPullbackInvPullbackObj p A).inv ≫ φ :=
    (Scheme.Modules.pullbackComp (inv p) p ≪≫ Scheme.Modules.pullbackCongr (IsIso.inv_hom_id p) ≪≫
      Scheme.Modules.pullbackId Y).hom.naturality φ
  rw [h, Functor.map_zero, zero_comp] at hn
  exact (cancel_epi (isoPullbackInvPullbackObj p A).inv).mp (hn.symm.trans (comp_zero).symm)

set_option maxHeartbeats 6400000 in
set_option synthInstance.maxHeartbeats 1600000 in

theorem pullbackSection_ne_zero {X Y : Scheme.{u}} (p : X ⟶ Y) [IsIso p] {M : Y.Modules}
    (s : 𝟙_ Y.Modules ⟶ M) (hs : s ≠ 0) : Scheme.Modules.pullbackSectionFLT p s ≠ 0 := by
  intro h
  apply hs
  apply eq_zero_of_pullback_map_eq_zero p

  exact ((Scheme.Modules.pullbackUnitIso p).hom_inv_id_assoc ((Scheme.Modules.pullback p).map s)).symm.trans
    ((congrArg ((Scheme.Modules.pullbackUnitIso p).hom ≫ ·) h).trans comp_zero)

set_option maxHeartbeats 6400000 in
set_option synthInstance.maxHeartbeats 1600000 in
theorem twoAffineOpenCover_ext {Y : Scheme.{u}} {𝒲 𝒲' : Y.TwoAffineOpenCover}
    (h0 : 𝒲.U0 = 𝒲'.U0) (h1 : 𝒲.U1 = 𝒲'.U1) : 𝒲 = 𝒲' := by
  obtain ⟨U0, U1, _, _, _, _⟩ := 𝒲
  obtain ⟨U0', U1', _, _, _, _⟩ := 𝒲'
  dsimp only at h0 h1
  subst h0
  subst h1
  rfl

set_option maxHeartbeats 6400000 in
set_option synthInstance.maxHeartbeats 1600000 in
theorem preimage_id_opens {Y : Scheme.{u}} (U : Y.Opens) : (𝟙 Y) ⁻¹ᵁ U = U := rfl

set_option maxHeartbeats 6400000 in
set_option synthInstance.maxHeartbeats 1600000 in
theorem eulerChar_congr {k : Type u} [Field k] {Y : Scheme.{u}} (y : Y ⟶ Spec (CommRingCat.of k))
    (𝒲 : Y.TwoAffineOpenCover) {M M' : Y.Modules} (e : M ≅ M') :
    (Module.finrank k (𝒲.sectionsOf y M).H0 : ℤ) - Module.finrank k (𝒲.sectionsOf y M).H1
      = (Module.finrank k (𝒲.sectionsOf y M').H0 : ℤ) - Module.finrank k (𝒲.sectionsOf y M').H1 := by
  obtain ⟨𝒲', h0, h1, ⟨e0⟩, ⟨e1⟩⟩ :=
    Scheme.TwoAffineOpenCover.exists_linearEquiv_sectionsOf_of_iso y y (Iso.refl Y) (Category.id_comp y)
      𝒲 M' M (e ≪≫ ((Scheme.Modules.pullbackId Y).app M').symm)
  have h𝒲 : 𝒲' = 𝒲 :=
    twoAffineOpenCover_ext (h0.trans (preimage_id_opens _)) (h1.trans (preimage_id_opens _))
  subst h𝒲
  exact congrArg₂ (fun m n : ℕ => (m : ℤ) - (n : ℤ)) e0.finrank_eq e1.finrank_eq

set_option maxHeartbeats 6400000 in
set_option synthInstance.maxHeartbeats 1600000 in

theorem nonempty_iso_tensorUnit_fibre {𝒞 S : Scheme.{u}} {f : 𝒞 ⟶ S} [IsProper f]
    [SmoothOfRelativeDimension 1 f] [GeometricallyIrreducible f]
    {k : Type u} [Field k] (x : Spec (CommRingCat.of k) ⟶ S)
    {M : (pullback f x).Modules} (hM : Scheme.Modules.IsInvertible M)
    (h0 : IsAlgEquivZero (pullback.snd f x) M)
    (s : 𝟙_ (pullback f x).Modules ⟶ M) (hs : s ≠ 0) (𝒱 : (pullback f x).TwoAffineOpenCover) :
    Nonempty (M ≅ 𝟙_ (pullback f x).Modules) := by

  have hχ := IsAlgEquivZero.eulerChar_sectionsOf_tensor_eq (pullback.snd f x) 𝒱 M (𝟙_ _) hM
    (Scheme.Modules.isInvertible_unitFLT _) h0

  obtain ⟨D, -, e, -⟩ := RelEffCartierDiv.exists_I_eq_zeroSchemeIdeal_of_eulerChar_eq x hM s hs 𝒱 0
    (by rw [Nat.cast_zero, add_zero]; exact (eulerChar_congr (pullback.snd f x) 𝒱 (ρ_ M).symm).trans hχ)
  obtain ⟨e0⟩ := nonempty_lineBundle_iso_of_degree_zero D
  exact ⟨e ≪≫ e0⟩

end AlgZeroTrivGlue

set_option maxHeartbeats 6400000 in
set_option synthInstance.maxHeartbeats 1600000 in

theorem solution
    {k : Type u} [Field k] {X : Scheme.{u}} (x : X ⟶ Spec (CommRingCat.of k))
    [IsProper x] [SmoothOfRelativeDimension 1 x] [GeometricallyIrreducible x]
    (𝒱 : X.TwoAffineOpenCover) {L : X.Modules} (hL : Scheme.Modules.IsInvertible L)
    (h0 : IsAlgEquivZero x L) (s : 𝟙_ X.Modules ⟶ L) (hs : s ≠ 0) :
    Nonempty (L ≅ 𝟙_ X.Modules) := by

  have hp : pullback.fst x (𝟙 _) ≫ x = pullback.snd x (𝟙 (Spec (CommRingCat.of k))) :=
    pullback.condition.trans (Category.comp_id _)

  obtain ⟨𝒱', -, -, -, -⟩ := Scheme.TwoAffineOpenCover.exists_linearEquiv_sectionsOf_of_iso
    (pullback.snd x (𝟙 (Spec (CommRingCat.of k)))) x (asIso (pullback.fst x (𝟙 _))) hp 𝒱 L
    ((Scheme.Modules.pullback (pullback.fst x (𝟙 _))).obj L) (Iso.refl _)

  obtain ⟨e⟩ := AlgZeroTrivGlue.nonempty_iso_tensorUnit_fibre (f := x) (𝟙 _) (hL.pullback _) (h0.pullback _ hp)
    (Scheme.Modules.pullbackSectionFLT _ s) (AlgZeroTrivGlue.pullbackSection_ne_zero _ s hs) 𝒱'

  exact ⟨AlgZeroTrivGlue.isoPullbackInvPullbackObj (pullback.fst x (𝟙 _)) L ≪≫ (Scheme.Modules.pullback _).mapIso e ≪≫
    Scheme.Modules.pullbackUnitIso _⟩

#print axioms solution
