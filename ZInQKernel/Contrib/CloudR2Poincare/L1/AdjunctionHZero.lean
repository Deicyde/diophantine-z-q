import ZInQKernel.Contrib.CloudR2Poincare.L1.CechFaceMaps
import ZInQKernel.Contrib.CloudW07JacobiansCurves.Jacobian.AlgebraicGeometry.Cohomology.SectionsBaseChange

/-!
# Actual native degree-zero adjunction

The existing native H.mapOfAdjunction_zeroLinearEquiv identifies this map
with ACTUAL pushforward sections and the canonical preimage-top transport.
No rank, affine, proper or vanishing premise, and no replacement map.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
open CategoryTheory Limits AlgebraicGeometry Opposite

namespace ZInQ.Contrib.CloudR2Poincare.L1

/-- Canonical equality-of-opens transport is the actual restriction over the
corresponding equality, not an arbitrary group isomorphism. -/
theorem faceOpenEqLinearEquiv_eq_restrict
    {Z T : Scheme.{u}} (p : Z ⟶ T) (M : Z.Modules)
    {U V : Z.Opens} (h : U = V) (s : Scheme.Modules.sectionsModule p M U) :
    faceOpenEqLinearEquiv p M h s = M.presheaf.map (homOfLE h.ge).op s := by
  subst V
  change s = M.presheaf.map (𝟙 (op U)) s
  simp

/-- The ACTUAL global sections adjunction comparison, using the existing H0
comparison and canonical preimage-top transport. -/
def nativeHZeroAdjunctionEquiv {X Y : Scheme.{u}} (j : Y ⟶ X) (N : Y.Modules) :
    ((Scheme.Modules.pushforward j).obj N).H 0 ≃+ N.H 0 :=
  (Scheme.Modules.H.zeroLinearEquiv ((Scheme.Modules.pushforward j).obj N)).toAddEquiv.trans
    (((pushforwardSectionsLinearEquiv (𝟙 X) j N ⊤).toAddEquiv.trans
      (faceOpenEqLinearEquiv (j ≫ 𝟙 X) N j.preimage_top).toAddEquiv).trans
        (Scheme.Modules.H.zeroLinearEquiv N).symm.toAddEquiv)

/-- The comparison above is the EXISTING native H.mapOfAdjunction map,
not merely a bijection of equally sized objects. -/
theorem nativeHZeroAdjunctionEquiv_actual {X Y : Scheme.{u}} (j : Y ⟶ X) (N : Y.Modules)
    (z : ((Scheme.Modules.pushforward j).obj N).H 0) :
    Scheme.Modules.H.mapOfAdjunction j (𝟙 ((Scheme.Modules.pushforward j).obj N)) 0 z =
      nativeHZeroAdjunctionEquiv j N z := by
  let PN := (Scheme.Modules.pushforward j).obj N
  let e := faceOpenEqLinearEquiv (j ≫ 𝟙 X) N j.preimage_top
  apply (Scheme.Modules.H.zeroLinearEquiv N).injective
  change (Scheme.Modules.H.zeroLinearEquiv N)
      (Scheme.Modules.H.mapOfAdjunction j (𝟙 PN) 0 z) =
    (Scheme.Modules.H.zeroLinearEquiv N)
      ((Scheme.Modules.H.zeroLinearEquiv N).symm (e ((Scheme.Modules.H.zeroLinearEquiv PN) z)))
  rw [LinearEquiv.apply_symm_apply]
  have h := Scheme.Modules.H.mapOfAdjunction_zeroLinearEquiv j PN N (𝟙 PN) z
  change (Scheme.Modules.H.zeroLinearEquiv N)
      (Scheme.Modules.H.mapOfAdjunction j (𝟙 PN) 0 z) =
    N.presheaf.map (homOfLE (by simp : ⊤ ≤ j ⁻¹ᵁ ⊤)).op ((Scheme.Modules.H.zeroLinearEquiv PN) z) at h
  exact h.trans (faceOpenEqLinearEquiv_eq_restrict (j ≫ 𝟙 X) N j.preimage_top _).symm

/-- The EXISTING native degree-zero adjunction inflation is actually bijective. -/
theorem bijective_nativeHZeroMapOfAdjunction {X Y : Scheme.{u}} (j : Y ⟶ X) (N : Y.Modules) :
    Function.Bijective (Scheme.Modules.H.mapOfAdjunction j
      (𝟙 ((Scheme.Modules.pushforward j).obj N)) 0) := by
  constructor
  · intro x y h
    apply (nativeHZeroAdjunctionEquiv j N).injective
    simpa only [← nativeHZeroAdjunctionEquiv_actual] using h
  · intro z
    obtain ⟨x, hx⟩ := (nativeHZeroAdjunctionEquiv j N).surjective z
    exact ⟨x, (nativeHZeroAdjunctionEquiv_actual j N x).trans hx⟩

end ZInQ.Contrib.CloudR2Poincare.L1
