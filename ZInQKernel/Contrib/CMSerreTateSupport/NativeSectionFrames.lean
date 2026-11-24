/-
Copyright (c) 2026 H5 contributors. Apache-2.0.

# Local frames from nonvanishing native sections

Outside the actual zero-ideal support, the local coefficient of the given
global section is a unit on its basic open. The section therefore freely
generates on every smaller open, in the same native frame convention.

Restricting through the basic open and then to a smaller open is the same
as the direct restriction of the original global section. All modules,
sections, scalars and tensor powers remain those originally given.
-/
import ZInQKernel.Contrib.CloudR2NOS.ClosedSection.Step3Gaps
import ZInQKernel.Contrib.CMSerreTateSupport.NativePairNonvanishing
import ZInQKernel.Contrib.CloudW07JacobiansCurves.Jacobian.AlgebraicGeometry.Modules.ZeroLocusTensor

set_option autoImplicit false
noncomputable section
universe u
open CategoryTheory AlgebraicGeometry
open scoped AlgebraicGeometry.Scheme.Modules

namespace H5OriginalDVR.Lane2.NativeSectionFrames

/-- Outside the actual zero-support, a local scalar coefficient is a unit
on its basic open. This supplies C4's exact frame convention, on ALL smaller
opens, for the given global section of the given native invertible line. -/
theorem framesNear_of_notMem_zeroLocus
    {X : Scheme.{u}} (M : X.Modules) [M.IsInvertible]
    (σ : Γ(M, ⊤)) (x : X)
    (hx : x ∉ (Scheme.Modules.homOfGlobalSection M σ).zeroLocus.support) :
    ZInQ.Contrib.CloudR2NOS.ClosedSection.FramesNear M σ x := by
  let φ := Scheme.Modules.homOfGlobalSection M σ
  obtain ⟨V, hxV, _, e, he⟩ :=
    Scheme.Modules.exists_isFreeGenerator M (x := x) (W := ⊤) trivial
  obtain ⟨b, hb⟩ := he.exists_smul_eq (φ.app V.1 (1 : Γ(X, V.1)))
  have hcoeff : M.presheaf.map (homOfLE (le_top : V.1 ≤ ⊤)).op σ = b • e := by
    rw [← Scheme.Modules.homOfGlobalSection_app_one M σ V.1]
    exact hb.symm
  have hlocal : x ∉ X.zeroLocus (U := V.1) (Ideal.span {b}) := by
    intro hz
    apply hx
    apply (Scheme.IdealSheafData.mem_support_iff_of_mem hxV).mpr
    rwa [Scheme.Modules.Hom.ideal_zeroLocus φ V
      (Scheme.Modules.isFreeGenerator_one V.1) he hb.symm]
  have hxB : x ∈ X.basicOpen b := by
    by_contra hn
    apply hlocal
    rw [Scheme.mem_zeroLocus_iff]
    intro c hc hxc
    obtain ⟨r, hr⟩ := Ideal.mem_span_singleton'.mp hc
    have hsub : X.basicOpen c ≤ X.basicOpen b := by
      rw [← hr, Scheme.basicOpen_mul]
      exact inf_le_right
    exact hn (hsub hxc)
  let W := X.basicOpen b
  have hWV : W ≤ V.1 := X.basicOpen_le b
  let b' : Γ(X, W) := X.presheaf.map (homOfLE hWV).op b
  have hb' : IsUnit b' := X.toRingedSpace.isUnit_res_basicOpen b
  have hres : M.presheaf.map (homOfLE (le_top : W ≤ ⊤)).op σ =
      b' • M.presheaf.map (homOfLE hWV).op e := by
    have h := congrArg (M.presheaf.map (homOfLE hWV).op) hcoeff
    rw [Scheme.Modules.map_smul, Scheme.Modules.presheaf_map_map_apply] at h
    exact h
  have hgen : Scheme.Modules.IsFreeGenerator
      (M.presheaf.map (homOfLE (le_top : W ≤ ⊤)).op σ) := by
    rw [hres, ← hb'.unit_spec]
    exact (he.map hWV).units_smul hb'.unit
  refine ⟨W, hxB, ?_⟩
  intro U hUW
  have hpath : (homOfLE hUW : U ⟶ W) ≫ homOfLE (le_top : W ≤ ⊤) =
      homOfLE (le_top : U ≤ ⊤) := Subsingleton.elim _ _
  simpa only [Scheme.Modules.presheaf_map_map_apply, hpath] using hgen U hUW

/-- The ACTUAL finite global section family from the native square argument
has pointwise local frames in EXACTLY the consumer's native convention.
This does not manufacture a ProjPresentation or claim finiteness. -/
theorem finite_native_square_frames
    (hSquare : ZInQ.Contrib.CloudR2NOS.Step1.TheoremOfSquare.{u})
    {K : Type u} [Field K] [IsAlgClosed K]
    (A : Grp (Over (Spec (CommRingCat.of K)))) [PkgI2.IsAbelianVariety A]
    (N : A.X.left.Modules) [N.IsInvertible]
    (θ : Scheme.Modules.unit A.X.left ⟶ N) (hθ : θ ≠ 0) :
    ∃ F : Finset Γ(Scheme.Modules.tensorPow N 2, ⊤), F.Nonempty ∧
      ∀ x : A.X.left, ∃ s ∈ F,
        ZInQ.Contrib.CloudR2NOS.ClosedSection.FramesNear (Scheme.Modules.tensorPow N 2) s x := by
  obtain ⟨F, hF, hcover⟩ := H5OriginalDVR.Lane2.NativePairNonvanishing.finite_native_square_sections_no_common_zero
    hSquare A N θ hθ
  refine ⟨F, hF, ?_⟩
  intro x
  obtain ⟨s, hs, hx⟩ := hcover x
  exact ⟨s, hs, framesNear_of_notMem_zeroLocus _ s x hx⟩

end H5OriginalDVR.Lane2.NativeSectionFrames
