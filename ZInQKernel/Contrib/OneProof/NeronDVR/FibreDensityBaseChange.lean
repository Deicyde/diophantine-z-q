import Mathlib.AlgebraicGeometry.Fiber
import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen
import ZInQKernel.Contrib.CloudW07JacobiansCurves.Jacobian.AlgebraicGeometry.IdealSheaf.RelativeCartierPullback
import ZInQKernel.Contrib.CloudW07JacobiansCurves.Jacobian.AlgebraicGeometry.IdealSheaf.Image

import ZInQKernel.Contrib.CloudW07JacobiansCurves.Jacobian.AlgebraicGeometry.Modules.TensorPower
import ZInQKernel.Contrib.CloudW07JacobiansCurves.Jacobian.AlgebraicGeometry.Modules.ZeroLocusFunctorial

/-!
# Fibre-dense Cartier opens under base change

Base change preserves the fibre-generic points condition. For a flat
base change this transports the Cartier ideal and its affine complement,
and identifies the squared divisor lines on both sides.
-/

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory
open scoped AlgebraicGeometry.Scheme.Modules

universe u

namespace NeronDVR

set_option backward.isDefEq.respectTransparency false in
/-- An open containing all generic points of all fibres retains that property
after arbitrary base change. -/
theorem contains_fibre_generics_preimage_of_isPullback
    {S S' X X' : Scheme.{u}} {p : S' ⟶ S} {f : X ⟶ S}
    {g : X' ⟶ S'} {a : X' ⟶ X} (h : IsPullback a g f p) (U : X.Opens)
    (hU : ∀ x : X, (∀ z, z ⤳ x → f z = f x → z = x) → x ∈ U) :
    ∀ x' : X', (∀ z, z ⤳ x' → g z = g x' → z = x') → x' ∈ a ⁻¹ᵁ U := by
  intro x hx
  change a x ∈ U
  apply hU
  intro z hz hfz
  let s := g x
  let y : g.fiber s := g.asFiber x
  let b : g.fiber s ⟶ f.fiber (p s) :=
    pullback.map _ _ _ _ a (Spec.map (p.residueFieldMap s)) p h.w.symm (by simp)
  have hb : b ≫ f.fiberι (p s) = g.fiberι s ≫ a := by
    simp [b, Scheme.Hom.fiberι]
  have hbapply (v : g.fiber s) : f.fiberι (p s) (b v) = a (g.fiberι s v) :=
    congrArg (fun k : g.fiber s ⟶ X => k v) hb
  have hy : g.fiberι s y = x := g.fiberι_asFiber x
  have hbase : f (a x) = p s := congrArg (fun k : X' ⟶ S => k x) h.w
  let z₀ : f.fiber (p s) := (f.fiberHomeo (p s)).symm ⟨z, hfz.trans hbase⟩
  have hz₀ : f.fiberι (p s) z₀ = z := f.fiberι_fiberHomeo_symm _ _
  have hz₀b : z₀ ⤳ b y := by
    apply (f.fiberι (p s)).isEmbedding.isInducing.specializes_iff.mp
    rw [hz₀, hbapply, hy]
    exact hz
  have : Flat (Spec.map (p.residueFieldMap s)) := by
    rw [Flat.SpecMap_iff]
    let := (p.residueFieldMap s).hom.toAlgebra
    exact RingHom.flat_algebraMap_iff.mpr inferInstance
  have : Flat b := MorphismProperty.of_isPullback
    (isPullback_fiberToSpecResidueField_of_isPullback h s).flip inferInstance
  obtain ⟨w, hw, hbw⟩ := Flat.generalizingMap b hz₀b
  have hwbase : g (g.fiberι s w) = s := by
    have hw' : g.fiberι s w ∈ Set.range (g.fiberι s) := ⟨w, rfl⟩
    rwa [g.range_fiberι] at hw'
  have heqw : g.fiberι s w = x :=
    hx _ (hy ▸ hw.map (g.fiberι s).continuous) hwbase
  rw [← hz₀, ← hbw, hbapply, heqw]

set_option backward.isDefEq.respectTransparency false in
/-- Flat affine base change preserves an effective Cartier divisor, the
affineness of its complement, and the generic points in that complement. -/
theorem effectiveCartier_comap_of_fibre_dense_affine
    {S S' X X' : Scheme.{u}} {p : S' ⟶ S} {f : X ⟶ S}
    {g : X' ⟶ S'} {a : X' ⟶ X} (h : IsPullback a g f p)
    [Flat p] [IsAffineHom p] (D : X.IdealSheafData)
    (hD : D.IsInvertible) (hAffine : IsAffineOpen D.support.compl)
    (hDense : ∀ x : X, (∀ z, z ⤳ x → f z = f x → z = x) → x ∈ D.support.compl) :
    (D.comap a).IsInvertible ∧ IsAffineOpen (D.comap a).support.compl ∧
      ∀ x' : X', (∀ z, z ⤳ x' → g z = g x' → z = x') → x' ∈ (D.comap a).support.compl := by
  have : Flat a := MorphismProperty.of_isPullback h.flip inferInstance
  have : IsAffineHom a := MorphismProperty.of_isPullback h.flip inferInstance
  have heq : (D.comap a).support.compl = (a ⁻¹ᵁ (D.support.compl : X.Opens)) := by
    ext x
    change x ∉ ((D.comap a).support : Set X') ↔ x ∉ a ⁻¹' (D.support : Set X)
    rw [Scheme.IdealSheafData.coe_support_comap]
  refine ⟨hD.comap_of_flat a, ?_, ?_⟩
  · rw [heq]
    exact hAffine.preimage a
  · rw [heq]
    exact contains_fibre_generics_preimage_of_isPullback h _ hDense

set_option backward.isDefEq.respectTransparency false in
/-- The square of the Cartier line pulls back to the square of the
line attached to the pulled-back divisor. -/
theorem nonempty_pullback_squared_dual_toModules_iso
    {X Y : Scheme.{u}} (a : Y ⟶ X) (D : X.IdealSheafData)
    (hD : D.IsInvertible) (hPull : (D.comap a).IsInvertible) :
    Nonempty ((Scheme.Modules.pullback a).obj (D.toModulesᵛ.tensorPow 2) ≅
      (D.comap a).toModulesᵛ.tensorPow 2) := by
  let L := D.toModulesᵛ
  let M := (D.comap a).toModulesᵛ
  obtain ⟨e⟩ := hD.nonempty_pullback_dual_toModules_iso a hPull
  let eL : L.tensorPow 2 ≅ L ⊗ L := Iso.refl L ⊗ᵢ ρ_ L
  let eM : M.tensorPow 2 ≅ M ⊗ M := Iso.refl M ⊗ᵢ ρ_ M
  exact ⟨(Scheme.Modules.pullback a).mapIso eL ≪≫
    Scheme.Modules.pullbackTensorObjIso a L L ≪≫ (e ⊗ᵢ e) ≪≫ eM.symm⟩

/-- Isomorphic invertible modules have the same nonvanishing opens. -/
theorem affine_nonvanishing_cover_of_moduleIso
    {X : Scheme.{u}} {L M : X.Modules} [L.IsInvertible] [M.IsInvertible] (e : L ≅ M)
    (hCover : ∀ x : X, ∃ s : 𝟙_ X.Modules ⟶ M,
      x ∈ s.zeroLocus.support.compl ∧ IsAffineOpen s.zeroLocus.support.compl) :
    ∀ x : X, ∃ s : 𝟙_ X.Modules ⟶ L,
      x ∈ s.zeroLocus.support.compl ∧ IsAffineOpen s.zeroLocus.support.compl := by
  intro x
  obtain ⟨s, hxs, hs⟩ := hCover x
  let t := s ≫ e.inv
  have hequal : t.zeroLocus = s.zeroLocus :=
    Scheme.Modules.Hom.zeroLocus_eq_of_arrowIso t s
      (Arrow.isoMk' t s (Iso.refl _) e (by simp [t]))
  exact ⟨t, by rwa [hequal], by rwa [hequal]⟩

/-- An affine nonvanishing cover for the square of a pulled-back Cartier
divisor is a cover for the pullback of the original squared line. -/
theorem affine_nonvanishing_cover_pullback_squared_dual_of_comap
    {X Y : Scheme.{u}} (a : Y ⟶ X) (D : X.IdealSheafData)
    (hD : D.IsInvertible) (hPull : (D.comap a).IsInvertible) :
    letI := hD.isInvertible_dual_toModules
    letI := hPull.isInvertible_dual_toModules
    (∀ x : Y, ∃ s : 𝟙_ Y.Modules ⟶ (D.comap a).toModulesᵛ.tensorPow 2,
      x ∈ s.zeroLocus.support.compl ∧ IsAffineOpen s.zeroLocus.support.compl) →
    ∀ x : Y, ∃ s : 𝟙_ Y.Modules ⟶
        (Scheme.Modules.pullback a).obj (D.toModulesᵛ.tensorPow 2),
      x ∈ s.zeroLocus.support.compl ∧ IsAffineOpen s.zeroLocus.support.compl := by
  let := hD.isInvertible_dual_toModules
  let := hPull.isInvertible_dual_toModules
  obtain ⟨e⟩ := nonempty_pullback_squared_dual_toModules_iso a D hD hPull
  exact affine_nonvanishing_cover_of_moduleIso e

end NeronDVR
