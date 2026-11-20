import ZInQKernel.Contrib.OneProof.SZRaynaud

/-!
# Extending a generic point to a Néron section
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReductSplit

namespace SZRaynaud

variable {K : Type} [Field K] {O : ValuationSubring K}
  {A : PkgI3.AbVar K} (M : GroupModelO A O)

/-- A generic section of a Néron model extends uniquely. The given map
lands in the generic fibre of the given model via its unaltered pullback. -/
theorem exists_section_of_neron
    (hN : M.IsNeronModel) (z : Spec (.of K) ⟶ M.G.left)
    (hz : z ≫ M.G.hom = jO O) :
    ∃ a : Spec (.of O) ⟶ M.G.left, a ≫ M.G.hom = 𝟙 _ ∧ jO O ≫ a = z := by
  let S := Spec (.of O)
  let Y := Over.mk (𝟙 S)
  have : Smooth Y.hom := inferInstanceAs (Smooth (𝟙 S))
  let F := Over.pullback (jO O)
  let ofY := pullback.snd (𝟙 S) (jO O)
  let q : (F.obj Y) ⟶ F.obj M.G := Over.homMk
    (pullback.lift (ofY ≫ z) ofY (by rw [Category.assoc, hz]))
    (pullback.lift_snd _ _ _)
  obtain ⟨s, hs⟩ := (hN Y).surjective (q ≫ M.gen.hom)
  have hcomp : F.map s = q := (cancel_mono M.gen.hom).mp hs
  refine ⟨s.left, s.w, ?_⟩
  let i : Spec (.of K) ⟶ (F.obj Y).left :=
    pullback.lift (jO O) (𝟙 _) (by
      change jO O ≫ 𝟙 S = (𝟙 (Spec (.of K))) ≫ jO O
      rw [Category.comp_id, Category.id_comp])
  have hip : i ≫ pullback.fst (𝟙 S) (jO O) = jO O := pullback.lift_fst _ _ _
  have his : i ≫ ofY = 𝟙 _ := pullback.lift_snd _ _ _
  have H := congrArg (fun f : (F.obj Y) ⟶ F.obj M.G =>
    i ≫ f.left ≫ pullback.fst M.G.hom (jO O)) hcomp
  change i ≫ ((Over.pullback (jO O)).map s).left ≫ pullback.fst M.G.hom (jO O) =
    i ≫ q.left ≫ pullback.fst M.G.hom (jO O) at H
  simp only [Over.pullback_map_left, pullback.lift_fst] at H
  change i ≫ (pullback.fst (𝟙 S) (jO O) ≫ s.left) = i ≫
    pullback.lift (ofY ≫ z) ofY _ ≫ pullback.fst M.G.hom (jO O) at H
  rw [pullback.lift_fst, ← Category.assoc, hip, ← Category.assoc i ofY z,
    his, Category.id_comp] at H
  exact H

#print axioms exists_section_of_neron

end SZRaynaud
