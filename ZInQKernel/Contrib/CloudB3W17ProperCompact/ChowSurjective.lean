/-
Copyright (c) 2026 W17 contributors.
Released under Apache 2.0 license as described in the file LICENSE.

The Chow data and their existence proofs are imported from the existing W02 port
of anthropics/fermats-last-theorem, commit
6e837e75355538c7f80bab5b956861e86c4eacc2. This file proves surjectivity from their
properness and dense-open isomorphism fields. No source definitions are changed.
-/
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.P2M.Sol.S_AlgebraicGeometry_ChowDatum_nonempty
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.P2M.Sol.S_AlgebraicGeometry_ChowDatumProj_nonempty_of

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace

universe u

namespace W17ProperCompact

/-- The proper projection of a Chow datum is surjective. -/
theorem chowDatumProj_surjective {R : Type u} [CommRing R] {X : Scheme.{u}}
    {s : X ⟶ Spec (CommRingCat.of R)} (D : ChowDatumProj s) : Surjective D.p := by
  let sectionU : D.U.toScheme ⟶ D.V' :=
    inv (pullback.snd D.p D.U.ι) ≫ pullback.fst D.p D.U.ι
  have hsection : sectionU ≫ D.p = D.U.ι := by
    dsimp only [sectionU]
    rw [Category.assoc, pullback.condition, IsIso.inv_hom_id_assoc]
  have hU : (D.U : Set X) ⊆ Set.range D.p := by
    intro x hx
    refine ⟨sectionU ⟨x, hx⟩, ?_⟩
    exact congrArg (fun f : D.U.toScheme ⟶ X => f ⟨x, hx⟩) hsection
  have hcover : Set.univ ⊆ Set.range D.p := by
    rw [← D.hU_dense.closure_eq]
    exact closure_minimal hU D.p.isClosedMap.isClosed_range
  exact ⟨fun x => hcover (Set.mem_univ x)⟩

/-- Every integral proper scheme over a Noetherian ring has surjective projective Chow data. -/
theorem exists_surjective_chowDatumProj {R : Type u} [CommRing R] [IsNoetherianRing R]
    {X : Scheme.{u}} (s : X ⟶ Spec (CommRingCat.of R)) [IsProper s] [IsIntegral X] :
    ∃ D : ChowDatumProj s, Surjective D.p := by
  obtain ⟨D⟩ :=
    P2MW.S_AlgebraicGeometry_ChowDatumProj_nonempty_of.solution s
      (P2MW.S_AlgebraicGeometry_ChowDatum_nonempty.solution s)
  exact ⟨D, chowDatumProj_surjective D⟩

end W17ProperCompact
