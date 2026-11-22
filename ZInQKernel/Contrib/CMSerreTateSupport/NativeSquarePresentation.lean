/-
Copyright (c) 2026 H5 contributors. Apache-2.0.

# Projective presentations from native square frames

Reindex the original nonempty finite family of global sections by Fin(d+1)
and retain its local frame equations. The native frame construction supplies
an actual presentation of the same tensor square using those sections.

Existence of a presentation does not assert finiteness of its projective map.
All fields, points, modules, powers and universe parameters remain those
in the statements below.
-/
import ZInQKernel.Contrib.CMSerreTateSupport.NativeSectionFrames
import ZInQKernel.Contrib.CloudR2NOS.ClosedSection.ProjOfFrames

set_option autoImplicit false
noncomputable section
universe u
open CategoryTheory AlgebraicGeometry
open scoped AlgebraicGeometry.Scheme.Modules

namespace H5OriginalDVR.Lane2.NativeSquarePresentation

/-- Reindex the ACTUAL nonempty finite global section family by Fin(d+1).
No rank/cardinality oracle or new section carrier is assumed. -/
theorem indexed_frames_of_finite_frames
    {X : Scheme.{u}} (M : X.Modules) (F : Finset Γ(M, ⊤)) (hF : F.Nonempty)
    (hcover : ∀ x : X, ∃ s ∈ F,
      ZInQ.Contrib.CloudR2NOS.ClosedSection.FramesNear M s x) :
    ∃ d : ℕ, ∃ σ : Fin (d + 1) → Γ(M, ⊤),
      ∀ x : X, ∃ i, ZInQ.Contrib.CloudR2NOS.ClosedSection.FramesNear M (σ i) x := by
  classical
  let T := {s : Γ(M, ⊤) // s ∈ F}
  obtain ⟨s0, hs0⟩ := hF
  letI : Nonempty T := ⟨⟨s0, hs0⟩⟩
  let e : T ≃ Fin (Fintype.card T) := Fintype.equivFin T
  have hpos : 0 < Fintype.card T := Fintype.card_pos
  let d := Fintype.card T - 1
  have hd : d + 1 = Fintype.card T := Nat.sub_add_cancel (Nat.succ_le_of_lt hpos)
  let σ : Fin (d + 1) → Γ(M, ⊤) := fun i => (e.symm (Fin.cast hd i)).1
  refine ⟨d, σ, ?_⟩
  intro x
  obtain ⟨s, hsF, hsx⟩ := hcover x
  let t : T := ⟨s, hsF⟩
  let i : Fin (d + 1) := Fin.cast hd.symm (e t)
  have hi : Fin.cast hd i = e t := by
    apply Fin.ext
    rfl
  have hσ : σ i = s := by
    dsimp only [σ]
    rw [hi, e.symm_apply_apply]
  refine ⟨i, ?_⟩
  rw [hσ]
  exact hsx

/-- Named pending I5a + SAME nonzero theta -> the actual native square
projective presentation, using C4's actual G5 proof. Finite is not claimed. -/
theorem exists_native_square_projPresentation
    (hSquare : ZInQ.Contrib.CloudR2NOS.Step1.TheoremOfSquare.{u})
    {K : Type u} [Field K] [IsAlgClosed K]
    (A : Grp (Over (Spec (CommRingCat.of K)))) [PkgI2.IsAbelianVariety A]
    (N : A.X.left.Modules) [N.IsInvertible]
    (θ : Scheme.Modules.unit A.X.left ⟶ N) (hθ : θ ≠ 0) :
    ∃ d : ℕ, Nonempty
      (ZInQ.Contrib.CloudW03NeronSurj.FLT.AlgebraicGeometry.Scheme.Modules.ProjPresentation
        (Scheme.Modules.tensorPow N 2) A.X.hom d) := by
  obtain ⟨F, hF, hcover⟩ := H5OriginalDVR.Lane2.NativeSectionFrames.finite_native_square_frames
    hSquare A N θ hθ
  obtain ⟨d, σ, hσ⟩ := indexed_frames_of_finite_frames _ F hF hcover
  obtain ⟨𝔓, _⟩ := ZInQ.Contrib.CloudR2NOS.ClosedSection.ProjOfFrames.presentationOfFramesNear
    A.X.hom (Scheme.Modules.tensorPow N 2) d σ hσ
  exact ⟨d, ⟨𝔓⟩⟩

end H5OriginalDVR.Lane2.NativeSquarePresentation
