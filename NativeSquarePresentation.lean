/-
H5 original-input Step2 / GM8: reuse C4's genuine Source G5 on native square frames.
Copyright (c) 2026 H5 lane2 contributors. Apache-2.0.
SOURCE ONLY / UNCOMPILED. This yields an ACTUAL ProjPresentation of the SAME
native power2 from the NAMED pending I5a and SAME theta. It does NOT establish
IsFinite/toProj, I1/I2/descent or unconditional I5a.

G5 is owned by C4 and read in full: ProjOfFrames.lean36405B/803lines,
ee644b601ebda8372c35830f379f205f0780c4597fa5954e254ef6d2006dddcb.
Its chart gluing/presentation/ratio proof is reused, never duplicated here.
C4's historical prefixed definition/default-limit binding remains separate.
No presentation/FBS/ample/model Fact, no Source/W07 power alias.
-/
import NativeSectionFrames
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
    rfl
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
