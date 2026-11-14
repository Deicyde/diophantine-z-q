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


/-! ## §3 The Galois correspondence for residue images -/

section Galois

/-- **`σ` fixes the residue image of a `ℚ̄`-point `y` iff `y ∘ Spec σ = y`.** -/
theorem fixing_iff {X : Scheme.{0}} (y : Spec (CommRingCat.of Qbar) ⟶ X) (σ : Qbar ≃ₐ[ℚ] Qbar) :
    Spec.map (CommRingCat.ofHom (σ : Qbar →+* Qbar)) ≫ y = y ↔
      σ ∈ (residueImage y).fixingSubgroup := by
  rw [IntermediateField.mem_fixingSubgroup_iff]
  unfold residueImage
  generalize hp : Scheme.SpecToEquivOfField Qbar X y = p
  have hfix : (∀ t, σ (p.2 t) = p.2 t) ↔
      ∀ z ∈ IntermediateField.adjoin ℚ (Set.range p.2), σ z = z := by
    constructor
    · intro h z hz
      induction hz using IntermediateField.adjoin_induction with
      | mem x hx => obtain ⟨t, rfl⟩ := hx; exact h t
      | algebraMap r => exact σ.commutes r
      | add x y _ _ hx hy => rw [map_add, hx, hy]
      | inv x _ hx => rw [map_inv₀, hx]
      | mul x y _ _ hx hy => rw [map_mul, hx, hy]
    · intro h t
      exact h _ (IntermediateField.subset_adjoin _ _ ⟨t, rfl⟩)
  rw [← hfix]
  constructor
  · intro h t
    have h2 := congrArg (Scheme.SpecToEquivOfField Qbar X) h
    rw [specToEquivOfField_comp, hp] at h2
    have h3 : p.2 ≫ CommRingCat.ofHom (σ : Qbar →+* Qbar) = p.2 :=
      eq_of_heq (Sigma.mk.inj_iff.mp h2).2
    exact congrArg (fun φ => φ t) (congrArg CommRingCat.Hom.hom h3)
  · intro h
    apply (Scheme.SpecToEquivOfField Qbar X).injective
    rw [specToEquivOfField_comp, hp]
    have h3 : p.2 ≫ CommRingCat.ofHom (σ : Qbar →+* Qbar) = p.2 := by
      ext t; exact h t
    rw [h3]

end Galois

/-! ## §4 Field of moduli = residue field -/

section Bridge

/-- **On a fine witness, the field of moduli of the object at a `ℚ̄`-point is the residue image of the
point.** -/
theorem fieldOfModuli3_eq_residueImage {Y : Over (Spec (CommRingCat.of ℚ))} {Φ : PtEquiv Y}
    (h1 : R1fpProps Y Φ) (y : fieldPt Qbar ⟶ Y) (P : QML3 Qbar) (hP : Φ Qbar y = M3.mk P) :
    fieldOfModuli3 P = residueImage y.left := by
  have hstab : stab3 P = ((residueImage y.left).fixingSubgroup : Set (Qbar ≃ₐ[ℚ] Qbar)) := by
    ext σ
    rw [SetLike.mem_coe]
    refine Iff.trans ?_ (fixing_iff (X := Y.left) y.left σ)
    obtain ⟨-, -, -, hnat, -, -⟩ := h1
    obtain ⟨Q, hQ, hbc⟩ := hnat Qbar Qbar (σ : Qbar →ₐ[ℚ] Qbar) y P hP
    constructor
    · intro hσ
      obtain ⟨i⟩ := bc_unique3 hbc hσ
      have e : Φ Qbar (fieldMap (σ : Qbar →ₐ[ℚ] Qbar) ≫ y) = Φ Qbar y := by
        rw [hQ, hP]; exact Quotient.sound ⟨i⟩
      have e2 := congrArg Over.Hom.left ((Φ Qbar).injective e)
      rw [Over.comp_left] at e2; exact e2
    · intro hy
      have e : fieldMap (σ : Qbar →ₐ[ℚ] Qbar) ≫ y = y := by
        apply Over.OverMorphism.ext
        rw [Over.comp_left]; exact hy
      rw [e, hP] at hQ
      obtain ⟨i⟩ := Quotient.exact hQ
      exact bc_transport3 hbc i
  unfold fieldOfModuli3
  rw [hstab, Subgroup.closure_eq, InfiniteGalois.fixedField_fixingSubgroup]

/-- **On a coarse witness (`X6Props`), the field of moduli of the QM pair at a `ℚ̄`-point is the residue
image of the point.** -/
theorem fieldOfModuliPair_eq_residueImage {Y : Over (Spec (CommRingCat.of ℚ))} {Φ : PtEquiv Y}
    {X : Over (Spec (CommRingCat.of ℚ))} {Ψ : (fieldPt Qbar ⟶ X) ≃ Quotient (pairSetoid Qbar)}
    {fY : Y ⟶ X} (h6 : X6Props Y Φ X Ψ fY) (x : fieldPt Qbar ⟶ X) (P : QMPair Qbar)
    (hP : Ψ x = Quotient.mk _ P) :
    fieldOfModuliPair P = residueImage x.left := by
  have hstab : stabPair P = ((residueImage x.left).fixingSubgroup : Set (Qbar ≃ₐ[ℚ] Qbar)) := by
    ext σ
    rw [SetLike.mem_coe]
    refine Iff.trans ?_ (fixing_iff (X := X.left) x.left σ)
    obtain ⟨-, -, -, hgal, -, -⟩ := h6
    obtain ⟨Q, hQ, hbc⟩ := hgal σ x P hP
    constructor
    · intro hσ
      obtain ⟨i⟩ := bc_uniquePair hbc hσ
      have e : Ψ (fieldMap (σ : Qbar →ₐ[ℚ] Qbar) ≫ x) = Ψ x := by
        rw [hQ, hP]; exact Quotient.sound ⟨i⟩
      have e2 := congrArg Over.Hom.left (Ψ.injective e)
      rw [Over.comp_left] at e2; exact e2
    · intro hy
      have e : fieldMap (σ : Qbar →ₐ[ℚ] Qbar) ≫ x = x := by
        apply Over.OverMorphism.ext
        rw [Over.comp_left]; exact hy
      rw [e, hP] at hQ
      obtain ⟨i⟩ := Quotient.exact hQ
      exact bc_transportPair hbc i
  unfold fieldOfModuliPair
  rw [hstab, Subgroup.closure_eq, InfiniteGalois.fixedField_fixingSubgroup]


/-! ## §5 The object forms `R1rec`, `R5fp` from the point forms on one witness -/

/-- **`R1rec` (object form) from the point form `R1recProps` on one fine witness.** -/
theorem r1rec_of_point (h : ∃ (Y : Over (Spec (CommRingCat.of ℚ))) (Φ : PtEquiv Y),
    R1fpProps Y Φ ∧ R1recProps Y Φ) : R1rec := by
  obtain ⟨Y, Φ, h1, hr⟩ := h
  intro P hcm
  obtain ⟨y, hy⟩ := (Φ Qbar).surjective (M3.mk P)
  rw [fieldOfModuli3_eq_residueImage h1 y P hy]
  exact hr y P hy hcm

/-- Conversely, on a fine witness the object form gives the point form. -/
theorem point_of_r1rec (h : R1rec) {Y : Over (Spec (CommRingCat.of ℚ))} {Φ : PtEquiv Y}
    (h1 : R1fpProps Y Φ) : R1recProps Y Φ := by
  intro y P hy hcm
  rw [← fieldOfModuli3_eq_residueImage h1 y P hy]
  exact h P hcm

/-- **`R5fp` (object form) from the point form `R5ptProps` on one coarse witness.** -/
theorem r5fp_of_point (h : ∃ (Y : Over (Spec (CommRingCat.of ℚ))) (Φ : PtEquiv Y)
    (X : Over (Spec (CommRingCat.of ℚ))) (Ψ : (fieldPt Qbar ⟶ X) ≃ Quotient (pairSetoid Qbar))
    (fY : Y ⟶ X), X6Props Y Φ X Ψ fY ∧ R5ptProps X Ψ) : R5fp := by
  obtain ⟨Y, Φ, X, Ψ, fY, h6, h5⟩ := h
  intro k _ _ _ hk R hR hc P hP
  have hx : Ψ (Ψ.symm (Quotient.mk _ P)) = Quotient.mk _ P := Ψ.apply_symm_apply _
  have key : ∀ A B : IntermediateField ℚ Qbar, A = B →
      (Module.finrank ℚ A = (if inertCount6 k = 0 then 1 else 2) * Nat.card (CommRing.Pic R) ∧
        (inertCount6 k ≠ 0 → Nonempty (k →ₐ[ℚ] A))) →
      (Module.finrank ℚ B = (if inertCount6 k = 0 then 1 else 2) * Nat.card (CommRing.Pic R) ∧
        (inertCount6 k ≠ 0 → Nonempty (k →ₐ[ℚ] B))) := by
    rintro A B rfl h; exact h
  exact key _ _ (fieldOfModuliPair_eq_residueImage h6 _ P hx).symm (h5 k hk R hR hc _ P hx hP)

/-- Conversely, on a coarse witness the object form gives the point form. -/
theorem point_of_r5fp (h : R5fp) {Y : Over (Spec (CommRingCat.of ℚ))} {Φ : PtEquiv Y}
    {X : Over (Spec (CommRingCat.of ℚ))} {Ψ : (fieldPt Qbar ⟶ X) ≃ Quotient (pairSetoid Qbar)}
    {fY : Y ⟶ X} (h6 : X6Props Y Φ X Ψ fY) : R5ptProps X Ψ := by
  intro k _ _ _ hk R hR hc x P hx hP
  have key : ∀ A B : IntermediateField ℚ Qbar, A = B →
      (Module.finrank ℚ A = (if inertCount6 k = 0 then 1 else 2) * Nat.card (CommRing.Pic R) ∧
        (inertCount6 k ≠ 0 → Nonempty (k →ₐ[ℚ] A))) →
      (Module.finrank ℚ B = (if inertCount6 k = 0 then 1 else 2) * Nat.card (CommRing.Pic R) ∧
        (inertCount6 k ≠ 0 → Nonempty (k →ₐ[ℚ] B))) := by
    rintro A B rfl h; exact h
  exact key _ _ (fieldOfModuliPair_eq_residueImage h6 x P hx) (h k hk R hR hc P hP)

end Bridge

end ShimuraSplit

#print axioms ShimuraSplit.fieldOfModuli3_eq_residueImage
#print axioms ShimuraSplit.fieldOfModuliPair_eq_residueImage
#print axioms ShimuraSplit.r1rec_of_point
#print axioms ShimuraSplit.r5fp_of_point
#print axioms ShimuraSplit.point_of_r1rec
#print axioms ShimuraSplit.point_of_r5fp
