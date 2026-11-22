import ZInQKernel.Contrib.OneProof.SZThm33.PicSpecialization.ModelAxisComparison
noncomputable section
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open Scheme.Modules
open scoped CategoryTheory.MonObj
namespace ZInQ.ToricOrthogonality
open PicDict.Transport
variable {S : Scheme.{0}} (G : Over S) [GrpObj G]
set_option backward.isDefEq.respectTransparency false

set_option maxHeartbeats 1200000 in
/-- A representative of the normalized model polarization has axis
trivializations agreeing at the model identity. -/
theorem exists_axis_frames_agree_at_origin
    (L : G.left.Pic) (M : (G ⊗ G).left.Modules) [M.IsInvertible]
    (hM : Scheme.Pic.mk M = productDeltaClass G L) :
    ∃ (e₁ : unit G.left ≅ (pullback (firstAxis G).left).obj M)
      (e₂ : unit G.left ≅ (pullback (secondAxis G).left).obj M),
      pullFramedAlong η[G].left (firstAxis G).left e₁ ≪≫
        (pullbackCongr (congrArg Over.Hom.left (axisOrigin_eq G))).app M =
          pullFramedAlong η[G].left (secondAxis G).left e₂ := by
  let v : S ⟶ G.left := η[G].left
  let f := (firstAxis G).left
  let g := (secondAxis G).left
  have e : v ≫ f = v ≫ g := congrArg Over.Hom.left (axisOrigin_eq G)
  have h : v ≫ G.hom = 𝟙 S := Over.w η[G]
  obtain ⟨ha, hb⟩ := nonempty_iso_axes G L M hM
  let a : unit G.left ≅ (pullback f).obj M := Classical.choice ha
  let b : unit G.left ≅ (pullback g).obj M := Classical.choice hb
  obtain ⟨a', ha'⟩ := exists_frame_matching_origin G.hom v h g f e M b a
  refine ⟨a', b, ?_⟩
  simpa only [pullFramedAlong, Iso.trans_assoc] using ha'

end ZInQ.ToricOrthogonality

#print axioms ZInQ.ToricOrthogonality.exists_axis_frames_agree_at_origin
