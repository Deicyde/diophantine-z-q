import ZInQKernel.Contrib.CloudW07JacobiansCurves.Jacobian.AlgebraicGeometry.Modules.ZeroLocusFunctorial
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.Fiber

/-! An ACTUAL line-bundle morphism that is an isomorphism on one fibre is
an isomorphism over a parameter neighborhood: remove the proper image of
its ACTUAL zero scheme. No seesaw or relative Picard representability is
assumed. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace

namespace ZInQ.Contrib.CloudR2Poincare.L1

/-- An actual morphism of invertible sheaves is invertible exactly when its
actual coefficient zero ideal is the unit ideal. -/
theorem zeroLocus_eq_top_iff_isIso
    {X : Scheme.{u}} {M N : X.Modules} [M.IsInvertible] [N.IsInvertible] (φ : M ⟶ N) :
    φ.zeroLocus = ⊤ ↔ IsIso φ := by
  classical
  constructor
  · intro hφ
    apply Scheme.Modules.isIso_of_isFreeGenerator φ
    intro x
    obtain ⟨U, hxU, -, ⟨eM, hM⟩, eN, hN⟩ :=
      Scheme.Modules.exists_isFreeGenerator₂ M N (x := x) (W := ⊤) trivial
    obtain ⟨b, hb⟩ := hN.exists_smul_eq (φ.app U.1 eM)
    have hunit : IsUnit b := by
      apply Ideal.span_singleton_eq_top.mp
      rw [← Scheme.Modules.Hom.ideal_zeroLocus φ U hM hN hb.symm, hφ,
        Scheme.IdealSheafData.ideal_top]
      rfl
    obtain ⟨u, hu⟩ := hunit
    refine ⟨U.1, eM, hxU, hM, ?_⟩
    rw [← hb, ← hu]
    exact hN.units_smul u
  · intro hφ
    haveI := hφ
    choose U hxU hUT e hM using fun x : X ↦
      Scheme.Modules.exists_isFreeGenerator M (x := x) (W := ⊤) trivial
    have hcover : ⨆ x, (U x).1 = ⊤ := eq_top_iff.mpr fun x _ ↦
      TopologicalSpace.Opens.mem_iSup.mpr ⟨x, hxU x⟩
    apply le_antisymm le_top
    apply Scheme.IdealSheafData.le_of_iSup_eq_top U hcover
    intro x
    have hn := (hM x).app_hom (asIso φ)
    rw [Scheme.Modules.Hom.ideal_zeroLocus φ (U x) (hM x) hn (b := 1) (by simp)]
    simp

/-- Properness gives a parameter neighborhood on which an ACTUAL line-bundle
morphism is invertible from its invertibility on the ACTUAL residue fibre. -/
theorem exists_open_isIso_of_residue_fibre_isIso
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsProper f]
    {M N : X.Modules} [M.IsInvertible] [N.IsInvertible] (φ : M ⟶ N)
    (y : Y) (hy : IsIso ((Scheme.Modules.pullback (f.fiberι y)).map φ)) :
    ∃ V : Y.Opens, y ∈ V ∧
      IsIso ((Scheme.Modules.pullback ((f ⁻¹ᵁ V).ι)).map φ) := by
  let I := φ.zeroLocus
  have hzero : (I.comap (f.fiberι y)).support = ⊥ := by
    rw [Scheme.Modules.Hom.comap_zeroLocus,
      (zeroLocus_eq_top_iff_isIso _).mpr hy, Scheme.IdealSheafData.support_top]
  have himage : y ∉ f '' (I.support : Set X) := by
    rintro ⟨x, hx, hxy⟩
    have hxrange : x ∈ Set.range (f.fiberι y) := by
      rw [f.range_fiberι y]
      exact hxy
    obtain ⟨z, hz⟩ := hxrange
    have hzI : z ∈ (I.comap (f.fiberι y)).support := by
      rw [Scheme.IdealSheafData.support_comap]
      change f.fiberι y z ∈ I.support
      rw [hz]
      exact hx
    rw [hzero] at hzI
    exact hzI
  let V : Y.Opens := ⟨(f '' (I.support : Set X))ᶜ,
    (f.isClosedMap _ I.support.isClosed).isOpen_compl⟩
  refine ⟨V, himage, (zeroLocus_eq_top_iff_isIso _).mp ?_⟩
  rw [← Scheme.Modules.Hom.comap_zeroLocus]
  apply (Scheme.IdealSheafData.support_eq_bot_iff _).mp
  ext x
  rw [Scheme.IdealSheafData.support_comap]
  change (x.val ∈ I.support) ↔ False
  constructor
  · intro hx
    exact x.property ⟨x.val, hx, rfl⟩
  · exact False.elim

end ZInQ.Contrib.CloudR2Poincare.L1
