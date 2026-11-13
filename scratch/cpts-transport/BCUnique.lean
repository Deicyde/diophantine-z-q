import TailF

noncomputable section

namespace HSyn.G0Split.FibreQM.PeriodMapH

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ZInQ ZInQ.JHeight LeafQM.AV ZInQ.DefFaltings
open HSyn.G0Split.FibreQM

namespace BCUnique

/-- A base-change morphism carries the identity section to the identity section (from the `η`
clause of `IsBaseChangeOf` at `a = 0`). -/
theorem eta_left_comp {ιe : Qbar →+* ℂ} {P : QML3 Qbar} {R : QML3 ℂ}
    (gR : R.A.X.left ⟶ P.A.X.left)
    (h : ∀ a : LeafQM.O, (Additive.toMul (R.e.eta a)).left ≫ gR =
      Spec.map (CommRingCat.ofHom ιe) ≫ (Additive.toMul (P.e.eta a)).left) :
    η[R.A.X].left ≫ gR = Spec.map (CommRingCat.ofHom ιe) ≫ η[P.A.X].left := by
  have h0 := h 0
  rw [map_zero R.e.eta, map_zero P.e.eta] at h0
  have eC : (PkgI3.AbVar.ptObj (K := ℂ) ℂ).hom = 𝟙 _ := by
    show Spec.map (CommRingCat.ofHom (algebraMap ℂ ℂ)) = _
    rw [show algebraMap ℂ ℂ = RingHom.id ℂ from RingHom.ext fun _ => rfl]
    exact Spec.map_id _
  have eQ : (PkgI3.AbVar.ptObj (K := Qbar) Qbar).hom = 𝟙 _ := by
    show Spec.map (CommRingCat.ofHom (algebraMap Qbar Qbar)) = _
    rw [show algebraMap Qbar Qbar = RingHom.id Qbar from RingHom.ext fun _ => rfl]
    exact Spec.map_id _
  have h1 : (PkgI3.AbVar.ptObj (K := ℂ) ℂ).hom ≫ η[R.A.X].left ≫ gR =
      Spec.map (CommRingCat.ofHom ιe) ≫ (PkgI3.AbVar.ptObj (K := Qbar) Qbar).hom ≫
        η[P.A.X].left := by
    rw [← Category.assoc]
    exact h0
  rw [eC, eQ] at h1
  erw [Category.id_comp, Category.id_comp] at h1
  exact h1

end BCUnique

open BCUnique in
/-- **`BaseChangeClassUnique` holds** (proved): the two pullbacks are isomorphic over `Spec ℂ`
compatibly with the maps to `P.A`; by uniqueness of maps into a pullback the isomorphism commutes
with `ι` and carries `η` to `η'`, and it is a homomorphism by rigidity
(`G0FibreSimple.rigidityHom`). -/
theorem baseChangeClassUnique_proof : BaseChangeClassUnique := by
  intro ιe P Q Q' hQ hQ'
  obtain ⟨g, hpb, hι, hη⟩ := hQ
  obtain ⟨g', hpb', hι', hη'⟩ := hQ'
  let E0 : Q.A.X.left ≅ Q'.A.X.left := hpb.isoIsPullback _ _ hpb'
  have hE0g : E0.hom ≫ g' = g := hpb.isoIsPullback_hom_fst _ _ hpb'
  have hE0s : E0.hom ≫ Q'.A.X.hom = Q.A.X.hom := hpb.isoIsPullback_hom_snd _ _ hpb'
  let E : Q.A.X ≅ Q'.A.X := Over.isoMk E0 hE0s
  have hEl : E.hom.left = E0.hom := rfl
  have h0 : η[Q.A.X] ≫ E.hom = η[Q'.A.X] := by
    apply Over.OverMorphism.ext
    apply hpb'.hom_ext
    · rw [Over.comp_left, hEl, Category.assoc, hE0g, eta_left_comp g hη,
        eta_left_comp g' hη']
    · exact (Over.w _).trans (Over.w _).symm
  have hφ : IsMonHom E.hom := G0FibreSimple.rigidityHom ℂ Q.A Q'.A E.hom h0
  have hψ : IsMonHom E.inv := G0FibreSimple.rigidityHom ℂ Q'.A Q.A E.inv
    (by rw [← h0, Category.assoc, E.hom_inv_id, Category.comp_id])
  refine Quotient.sound ⟨
    { φ := PkgI3.AbVar.Hom.mk' E.hom
      ψ := PkgI3.AbVar.Hom.mk' E.inv
      left := E.hom_inv_id
      right := E.inv_hom_id
      equivariant := fun a => ?_
      level := fun a => ?_ }⟩
  · show (Q.q.iota a).hom ≫ E.hom = E.hom ≫ (Q'.q.iota a).hom
    apply Over.OverMorphism.ext
    apply hpb'.hom_ext
    · rw [Over.comp_left, Over.comp_left, hEl, Category.assoc, hE0g, hι a, Category.assoc,
        hι' a, ← Category.assoc, hE0g]
    · exact (Over.w _).trans (Over.w _).symm
  · show Additive.ofMul (Additive.toMul (Q.e.eta a) ≫ E.hom) =
      Additive.ofMul (Additive.toMul (Q'.e.eta a))
    congr 1
    apply Over.OverMorphism.ext
    apply hpb'.hom_ext
    · rw [Over.comp_left, hEl, Category.assoc, hE0g, hη a, hη' a]
    · exact (Over.w _).trans (Over.w _).symm

end HSyn.G0Split.FibreQM.PeriodMapH

#print axioms HSyn.G0Split.FibreQM.PeriodMapH.baseChangeClassUnique_proof
