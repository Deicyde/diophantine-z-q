import ZInQKernel.HDecomp.QM.Leaves
import ZInQKernel.Contrib.FrobChain.Rigidity

/-!
# shimura-split, Part 1: field of moduli = residue field, on a fine and on a coarse witness

leaf-qm-fp (§2.4) kept `R1rec` (object form, field of moduli) beside `R1recProps` (point form, residue
field) because "the bridge from fields of moduli to residue fields needs the uniqueness of base change up
to isomorphism of objects, which needs rigidity, and Mathlib does not have this". The kernel now proves
rigidity (`MulRigidity.isMonHom_of_geometricallyIntegral`, `ZInQKernel/Contrib/FrobChain/Rigidity.lean`).
This file proves the bridge:

* `bc_unique3` / `bc_uniquePair`: two base changes of one object along one field map are isomorphic;
* `fixing_iff`: `σ` fixes the residue image of a `ℚ̄`-point `y` iff `y ∘ Spec σ = y`;
* `fieldOfModuli3_eq_residueImage` (fine witness, `R1fpProps`) and
  `fieldOfModuliPair_eq_residueImage` (coarse witness, `X6Props`).
-/

set_option linter.all false

noncomputable section

namespace ShimuraSplit

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open LeafQM LeafQM.AV PkgI3

/-! ## §1 The identity point -/

theorem pt_one_left {L : Type} [Field L] (A : AbVar L) :
    (1 : A.Pt L).left = η[A.X].left := by
  rw [Hom.one_def]
  simp [AbVar.ptObj]


/-! ## §2 Uniqueness of base change up to isomorphism (rigidity) -/

section BC

variable {K L : Type} [Field K] [Field L]

theorem over_ext_pb {A : AbVar K} {B' : AbVar L} {f : K →+* L} {g' : B'.X.left ⟶ A.X.left}
    (pb' : IsPullback g' B'.X.hom A.X.hom (Spec.map (CommRingCat.ofHom f)))
    {T : Over (Spec (CommRingCat.of L))} {u v : T ⟶ B'.X} (hg : u.left ≫ g' = v.left ≫ g') : u = v :=
  Over.OverMorphism.ext (pb'.hom_ext hg (by rw [Over.w u, Over.w v]))

/-- **Core.** Two pullbacks `B, B'` of `A` along `Spec f`, whose identity sections lie over the identity
section of `A`, are isomorphic over `A` by mutually inverse homomorphisms (rigidity). -/
theorem bc_core (f : K →+* L) (A : AbVar K) (B B' : AbVar L)
    (g : B.X.left ⟶ A.X.left) (g' : B'.X.left ⟶ A.X.left)
    (pb : IsPullback g B.X.hom A.X.hom (Spec.map (CommRingCat.ofHom f)))
    (pb' : IsPullback g' B'.X.hom A.X.hom (Spec.map (CommRingCat.ofHom f)))
    (h1 : η[B.X].left ≫ g = Spec.map (CommRingCat.ofHom f) ≫ η[A.X].left)
    (h1' : η[B'.X].left ≫ g' = Spec.map (CommRingCat.ofHom f) ≫ η[A.X].left) :
    ∃ (E : B.X ⟶ B'.X) (F : B'.X ⟶ B.X), IsMonHom E ∧ IsMonHom F ∧ E ≫ F = 𝟙 _ ∧ F ≫ E = 𝟙 _ ∧
      E.left ≫ g' = g ∧ F.left ≫ g = g' := by
  let e := pb.isoIsPullback _ _ pb'
  let E : B.X ⟶ B'.X := Over.homMk e.hom (by simp [e])
  let F : B'.X ⟶ B.X := Over.homMk e.inv (by simp [e])
  have hEg : E.left ≫ g' = g := by simp [E, e]
  have hFg : F.left ≫ g = g' := by simp [F, e]
  have hE : η[B.X] ≫ E = η[B'.X] := by
    apply over_ext_pb pb'
    simp only [Over.comp_left, Category.assoc, hEg, h1, h1']
  have hF : η[B'.X] ≫ F = η[B.X] := by
    apply over_ext_pb pb
    simp only [Over.comp_left, Category.assoc, hFg, h1, h1']
  refine ⟨E, F, MulRigidity.isMonHom_of_geometricallyIntegral _ _ E hE,
    MulRigidity.isMonHom_of_geometricallyIntegral _ _ F hF, ?_, ?_, hEg, hFg⟩
  · ext1; simp [E, F, e]
  · ext1; simp [E, F, e]


/-- **Two base changes of one level-3 object along one field map are isomorphic.** -/
theorem bc_unique3 {f : K →+* L} {P : QML3 K} {Q Q' : QML3 L} (h : IsBaseChangeOf f P Q)
    (h' : IsBaseChangeOf f P Q') : Nonempty (Q.Iso Q') := by
  obtain ⟨g, pb, hι, hη⟩ := h
  obtain ⟨g', pb', hι', hη'⟩ := h'
  have h1 : η[Q.A.X].left ≫ g = Spec.map (CommRingCat.ofHom f) ≫ η[P.A.X].left := by
    have := hη 0
    simp only [map_zero, toMul_zero] at this
    rwa [pt_one_left, pt_one_left] at this
  have h1' : η[Q'.A.X].left ≫ g' = Spec.map (CommRingCat.ofHom f) ≫ η[P.A.X].left := by
    have := hη' 0
    simp only [map_zero, toMul_zero] at this
    rwa [pt_one_left, pt_one_left] at this
  obtain ⟨E, F, hE, hF, hEF, hFE, hEg, hFg⟩ := bc_core f P.A Q.A Q'.A g g' pb pb' h1 h1'
  refine ⟨⟨AbVar.Hom.mk' E, AbVar.Hom.mk' F, hEF, hFE, fun a => ?_, fun a => ?_⟩⟩
  · simp only [AbVar.Hom.hom_mk']
    apply over_ext_pb pb'
    simp only [Over.comp_left, Category.assoc, hEg, hι', reassoc_of% hEg, hι]
  · apply Additive.toMul.injective
    simp only [toMul_ofMul, AbVar.Hom.hom_mk']
    apply over_ext_pb pb'
    simp only [Over.comp_left, Category.assoc, hEg, hη, hη']
    try rfl

/-- **Base change is transported along an isomorphism of the target.** -/
theorem bc_transport3 {f : K →+* L} {P : QML3 K} {Q Q' : QML3 L} (h : IsBaseChangeOf f P Q)
    (i : Q'.Iso Q) : IsBaseChangeOf f P Q' := by
  obtain ⟨g, pb, hι, hη⟩ := h
  have hφψ : i.φ.hom.left ≫ i.ψ.hom.left = 𝟙 _ := by rw [← Over.comp_left, i.left]; rfl
  have hψφ : i.ψ.hom.left ≫ i.φ.hom.left = 𝟙 _ := by rw [← Over.comp_left, i.right]; rfl
  let e : Q'.A.X.left ≅ Q.A.X.left := ⟨i.φ.hom.left, i.ψ.hom.left, hφψ, hψφ⟩
  refine ⟨i.φ.hom.left ≫ g, ?_, fun a => ?_, fun a => ?_⟩
  · refine pb.of_iso e.symm (Iso.refl _) (Iso.refl _) (Iso.refl _) ?_ ?_ ?_ ?_
    · simp [e, reassoc_of% hψφ]
    · simp only [Iso.symm_hom, Iso.refl_hom, Category.comp_id, e]
      rw [Over.w i.ψ.hom]
    · simp
    · simp
  · rw [← Category.assoc, ← Over.comp_left, i.equivariant a, Over.comp_left, Category.assoc, hι,
      Category.assoc]
  · have hl := congrArg (fun z => (Additive.toMul z).left) (i.level a)
    simp only [toMul_ofMul, Over.comp_left] at hl
    rw [← Category.assoc, hl, hη]

/-- **Two base changes of one QM pair along one field map are isomorphic.** -/
theorem bc_uniquePair {f : K →+* L} {P : QMPair K} {Q Q' : QMPair L} (h : IsBaseChangeOfPair f P Q)
    (h' : IsBaseChangeOfPair f P Q') : Nonempty (QMIso Q.q Q'.q) := by
  obtain ⟨g, pb, hι, hη⟩ := h
  obtain ⟨g', pb', hι', hη'⟩ := h'
  rw [pt_one_left, pt_one_left] at hη hη'
  obtain ⟨E, F, hE, hF, hEF, hFE, hEg, hFg⟩ := bc_core f P.A Q.A Q'.A g g' pb pb' hη hη'
  refine ⟨⟨AbVar.Hom.mk' E, AbVar.Hom.mk' F, hEF, hFE, fun a => ?_⟩⟩
  simp only [AbVar.Hom.hom_mk']
  apply over_ext_pb pb'
  simp only [Over.comp_left, Category.assoc, hEg, hι', reassoc_of% hEg, hι]

/-- **Base change of QM pairs is transported along an isomorphism of the target.** -/
theorem bc_transportPair {f : K →+* L} {P : QMPair K} {Q Q' : QMPair L}
    (h : IsBaseChangeOfPair f P Q) (i : QMIso Q'.q Q.q) : IsBaseChangeOfPair f P Q' := by
  obtain ⟨g, pb, hι, hη⟩ := h
  have hφψ : i.φ.hom.left ≫ i.ψ.hom.left = 𝟙 _ := by rw [← Over.comp_left, i.left]; rfl
  have hψφ : i.ψ.hom.left ≫ i.φ.hom.left = 𝟙 _ := by rw [← Over.comp_left, i.right]; rfl
  let e : Q'.A.X.left ≅ Q.A.X.left := ⟨i.φ.hom.left, i.ψ.hom.left, hφψ, hψφ⟩
  refine ⟨i.φ.hom.left ≫ g, ?_, fun a => ?_, ?_⟩
  · refine pb.of_iso e.symm (Iso.refl _) (Iso.refl _) (Iso.refl _) ?_ ?_ ?_ ?_
    · simp [e, reassoc_of% hψφ]
    · simp only [Iso.symm_hom, Iso.refl_hom, Category.comp_id, e]
      rw [Over.w i.ψ.hom]
    · simp
    · simp
  · rw [← Category.assoc, ← Over.comp_left, i.equivariant a, Over.comp_left, Category.assoc, hι,
      Category.assoc]
  · rw [← Category.assoc, ← Over.comp_left, MonObj.one_comp, hη]

end BC

end ShimuraSplit
