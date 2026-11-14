import ZInQKernel.OneProof.H.TailZ4
import ZInQKernel.Contrib.FrobChain.Rigidity
import ZInQKernel.Contrib.CloudW07JacobiansCurves.JacobianExists
import ZInQKernel.Contrib.CloudW07JacobiansCurves.NormalModel
import Mathlib.FieldTheory.Galois.Infinite
import Mathlib.NumberTheory.NumberField.Discriminant.Different

/-! # OneProof H, leaf-fold9: the next bundle generation

`HDec.HSyn.sixContactMin_of_open9 (r : OpenResearchLeaves9) (t : OpenTextbookLeaves9) (l : OpenAddedLeaves8)
(g : OpenGlue7)` proves `ZInQ.SixContactMin` by filling leaf-fold8's bundles (`sixContactMin_of_open8`, `TailZ4`)
from the new ones; the bundles and that theorem are in `TailZ6`, this module has the proofs. Folded (docs/research/leaf-fold9.md lists every field):

* the research fields `r1rec` (R1(d), `LeafQM.AV.R1rec`) and `r5` (R5, `LeafQM.AV.R5fp`) are **proved from the
  research field `r1r2`** (`LeafAdopt.R1R2fpRep`), whose witness carries the same statements on residue fields of
  points (`R1recProps`, `R5ptProps`). The bridge is proved here (`ZInQ.LeafFold9`): on the fine witness the field of
  moduli of an object lies in the residue field of its point (`fieldOfModuli3_le`), and on the coarse witness the
  residue field of a point is the field of moduli of its pair (`residueImage_eq_fieldOfModuliPair`; uniqueness of
  base change by the kernel's rigidity `G0FibreSimple.rigidityHom`), with infinite Galois theory for `ℚ̄/ℚ` and
  `NumberField.discr_dvd_discr` for subfields;
* modular-split (`TailZ6`): the research field `r15` from the field `dsThm966`;
* cloud PR #11 (`ZInQKernel/Contrib/CloudW07JacobiansCurves/`): the textbook fields `t33`
  (`JacobianExists_proof`) and `normalModelOfFunctionFieldQ` (`NormalModelOfFunctionFieldQ_proof`).

No existing module is edited; every field that is not folded keeps leaf-fold8's type. -/
namespace ZInQ.LeafFold9

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj LeafQM LeafQM.AV

/-- A `ℚ̄`-point `y` of a scheme is fixed by `σ ∈ Aut(ℚ̄/ℚ)` iff `σ` fixes its residue field `ℚ(y)`
(`residueImage y`) pointwise. -/
theorem specMap_comp_eq_self_iff {X : Scheme.{0}} (y : Spec (CommRingCat.of Qbar) ⟶ X)
    (σ : Qbar ≃ₐ[ℚ] Qbar) :
    Spec.map (CommRingCat.ofHom (σ : Qbar →+* Qbar)) ≫ y = y ↔
      ∀ a ∈ residueImage (X := X) y, σ a = a := by
  rw [← (Scheme.SpecToEquivOfField Qbar X).injective.eq_iff, specToEquivOfField_comp]
  set p := Scheme.SpecToEquivOfField Qbar X y with hp
  have key : (⟨p.1, p.2 ≫ CommRingCat.ofHom (σ : Qbar →+* Qbar)⟩ :
      (x : X) × (X.residueField x ⟶ CommRingCat.of Qbar)) = p ↔
      ∀ b, σ (p.2 b) = p.2 b := by
    constructor
    · intro h b
      have h2 : p.2 ≫ CommRingCat.ofHom (σ : Qbar →+* Qbar) = p.2 := by
        have := (Sigma.mk.inj_iff.mp h).2
        exact eq_of_heq this
      exact congrArg (fun f => f b) (congrArg (fun f => (CommRingCat.Hom.hom f)) h2)
    · intro h
      ext
      · rfl
      · refine heq_of_eq ?_
        ext b
        exact h b
  rw [key]
  constructor
  · intro h a ha
    unfold residueImage at ha
    have hle : IntermediateField.adjoin ℚ (Set.range p.2) ≤
        IntermediateField.fixedField (Subgroup.zpowers σ) := by
      rw [IntermediateField.adjoin_le_iff]
      rintro _ ⟨b, rfl⟩
      rw [SetLike.mem_coe, IntermediateField.mem_fixedField_iff]
      rintro τ ⟨n, rfl⟩
      induction n using Int.induction_on with
      | zero => simp
      | succ n ih =>
        dsimp only at ih ⊢
        rw [zpow_add_one, AlgEquiv.mul_apply, h b]
        exact ih
      | pred n ih =>
        dsimp only at ih ⊢
        rw [zpow_sub_one, AlgEquiv.mul_apply]
        have : σ⁻¹ (p.2 b) = p.2 b := by
          rw [AlgEquiv.aut_inv, AlgEquiv.symm_apply_eq]; exact (h b).symm
        rw [this]; exact ih
    have := hle ha
    rw [IntermediateField.mem_fixedField_iff] at this
    exact this σ (Subgroup.mem_zpowers σ)
  · intro h b
    apply h
    exact IntermediateField.subset_adjoin ℚ _ ⟨b, rfl⟩

/-- Galois correspondence for `ℚ̄/ℚ` (infinite Galois theory): an intermediate field is the fixed field
of a subgroup containing its fixing subgroup... in the form used below. -/
theorem fixedField_le_of_le {E : IntermediateField ℚ Qbar} {H : Subgroup (Qbar ≃ₐ[ℚ] Qbar)}
    (h : E.fixingSubgroup ≤ H) : IntermediateField.fixedField H ≤ E := by
  conv_rhs => rw [← InfiniteGalois.fixedField_fixingSubgroup E]
  intro x hx
  rw [IntermediateField.mem_fixedField_iff] at hx ⊢
  intro τ hτ
  exact hx τ (h hτ)

/-- `UnramifiedAbove5` passes to subfields (`NumberField.discr_dvd_discr`). -/
theorem unramifiedAbove5_mono {F E : IntermediateField ℚ Qbar} (hFE : F ≤ E)
    (h : UnramifiedAbove5 E) : UnramifiedAbove5 F := by
  obtain ⟨hE, hd⟩ := h
  have hF : FiniteDimensional ℚ F :=
    Submodule.finiteDimensional_of_le (show F.toSubalgebra.toSubmodule ≤ E.toSubalgebra.toSubmodule
      from hFE)
  refine ⟨hF, fun p hp h5 hdvd => hd p hp h5 ?_⟩
  let _iF : NumberField F := @NumberField.mk F _ _ hF
  let _iE : NumberField E := @NumberField.mk E _ _ hE
  let _iA : Algebra F E := (IntermediateField.inclusion hFE).toRingHom.toAlgebra
  exact hdvd.trans (NumberField.discr_dvd_discr F E)

/-- Transport of a base change along an isomorphism of the target object. -/
theorem isBaseChangeOf_of_iso {K L : Type} [Field K] [Field L] {f : K →+* L} {P : QML3 K}
    {Q Q' : QML3 L} (h : IsBaseChangeOf f P Q) (e : Q'.Iso Q) : IsBaseChangeOf f P Q' := by
  obtain ⟨g, hpb, hι, hη⟩ := h
  refine ⟨e.φ.hom.left ≫ g, ?_, ?_, ?_⟩
  · have hsq : IsPullback e.φ.hom.left Q'.A.X.hom Q.A.X.hom (𝟙 _) := by
      have : IsIso e.φ.hom.left := ⟨⟨e.ψ.hom.left, by
        rw [← Over.comp_left, e.left]; rfl, by rw [← Over.comp_left, e.right]; rfl⟩⟩
      refine IsPullback.of_horiz_isIso ⟨?_⟩
      rw [Over.w, Category.comp_id]
    have := hsq.paste_horiz hpb
    simpa using this
  · intro a
    rw [← Category.assoc, ← Over.comp_left, e.equivariant a, Over.comp_left, Category.assoc, hι a,
      Category.assoc]
  · intro a
    have hl := congrArg Additive.toMul (e.level a)
    simp only [toMul_ofMul] at hl
    rw [← Category.assoc, ← Over.comp_left, hl, hη a]

/-- **On a fine witness, the field of moduli of an object is contained in the residue field of its
point.** -/
theorem fieldOfModuli3_le {Y : Over (Spec (CommRingCat.of ℚ))} {Φ : PtEquiv Y}
    (h1 : R1fpProps Y Φ) (y : fieldPt Qbar ⟶ Y) (P : QML3 Qbar) (hP : Φ Qbar y = M3.mk P) :
    fieldOfModuli3 P ≤ residueImage (X := Y.left) y.left := by
  apply fixedField_le_of_le
  intro σ hσ
  apply Subgroup.subset_closure
  have hfix : ∀ a ∈ residueImage (X := Y.left) y.left, σ a = a := fun a ha =>
    (IntermediateField.mem_fixingSubgroup_iff _ _).mp hσ a ha
  have hy : fieldMap (σ : Qbar →ₐ[ℚ] Qbar) ≫ y = y := by
    apply Over.OverMorphism.ext
    exact (specMap_comp_eq_self_iff y.left σ).mpr hfix
  obtain ⟨Q, hQ, hbc⟩ := h1.2.2.2.1 Qbar Qbar (σ : Qbar →ₐ[ℚ] Qbar) y P hP
  rw [hy, hP] at hQ
  obtain ⟨e⟩ := Quotient.exact hQ
  exact isBaseChangeOf_of_iso hbc e

/-! ## Pairs: transport and uniqueness of base change (rigidity) -/

/-- Transport of a base change of QM pairs along an isomorphism of the target pair. -/
theorem isBaseChangeOfPair_of_iso {K L : Type} [Field K] [Field L] {f : K →+* L} {P : QMPair K}
    {Q Q' : QMPair L} (h : IsBaseChangeOfPair f P Q) (e : QMIso Q'.q Q.q) :
    IsBaseChangeOfPair f P Q' := by
  obtain ⟨g, hpb, hι, h1⟩ := h
  refine ⟨e.φ.hom.left ≫ g, ?_, ?_, ?_⟩
  · have hsq : IsPullback e.φ.hom.left Q'.A.X.hom Q.A.X.hom (𝟙 _) := by
      have : IsIso e.φ.hom.left := ⟨⟨e.ψ.hom.left, by
        rw [← Over.comp_left, e.left]; rfl, by rw [← Over.comp_left, e.right]; rfl⟩⟩
      refine IsPullback.of_horiz_isIso ⟨?_⟩
      rw [Over.w, Category.comp_id]
    have := hsq.paste_horiz hpb
    simpa using this
  · intro a
    rw [← Category.assoc, ← Over.comp_left, e.equivariant a, Over.comp_left, Category.assoc, hι a,
      Category.assoc]
  · rw [← Category.assoc, ← Over.comp_left, MonObj.one_comp, h1]

/-- The section `Spec L → ptObj L` over `L` (the inverse of the point `ptObj L → 𝟙_`). -/
noncomputable def unitPt (L : Type) [Field L] : 𝟙_ (Over (Spec (CommRingCat.of L))) ⟶ PkgI3.AbVar.ptObj (K := L) L :=
  Over.homMk (𝟙 _) (by
    change 𝟙 _ ≫ Spec.map (CommRingCat.ofHom (algebraMap L L)) = 𝟙 _
    rw [Algebra.algebraMap_self, CommRingCat.ofHom_id, Spec.map_id, Category.comp_id])

/-- **Uniqueness of base change of QM pairs** (rigidity, `G0FibreSimple.rigidityHom`): two base changes of
the same pair along the same `f` are isomorphic. -/
theorem qmIso_of_isBaseChangeOfPair {K L : Type} [Field K] [Field L] {f : K →+* L} {P : QMPair K}
    {Q₁ Q₂ : QMPair L} (h₁ : IsBaseChangeOfPair f P Q₁) (h₂ : IsBaseChangeOfPair f P Q₂) :
    Nonempty (QMIso Q₁.q Q₂.q) := by
  obtain ⟨g₁, pb₁, ι₁, e₁⟩ := h₁
  obtain ⟨g₂, pb₂, ι₂, e₂⟩ := h₂
  let i := IsPullback.isoIsPullback _ _ pb₁ pb₂
  let H : Q₁.A.X ⟶ Q₂.A.X := Over.homMk i.hom (IsPullback.isoIsPullback_hom_snd _ _ pb₁ pb₂)
  let H' : Q₂.A.X ⟶ Q₁.A.X := Over.homMk i.inv (IsPullback.isoIsPullback_inv_snd _ _ pb₁ pb₂)
  have hinv₁ : H ≫ H' = 𝟙 _ := by
    apply Over.OverMorphism.ext; simp [H, H']
  have hinv₂ : H' ≫ H = 𝟙 _ := by
    apply Over.OverMorphism.ext; simp [H, H']
  -- the identity point is preserved
  have hpt : (1 : Q₁.A.Pt L) ≫ H = (1 : Q₂.A.Pt L) := by
    apply Over.OverMorphism.ext
    apply pb₂.hom_ext
    · simp only [Over.comp_left, Category.assoc, H, i, Over.homMk_left,
        IsPullback.isoIsPullback_hom_fst]
      rw [e₁, e₂]
    · simp only [Over.comp_left, Category.assoc, H, i, Over.homMk_left,
        IsPullback.isoIsPullback_hom_snd, Over.w]
  have hη : η[Q₁.A.X] ≫ H = η[Q₂.A.X] := by
    have hs : unitPt L ≫ toUnit (PkgI3.AbVar.ptObj (K := L) L) = 𝟙 _ := toUnit_unique _ _
    calc η[Q₁.A.X] ≫ H = unitPt L ≫ ((1 : Q₁.A.Pt L) ≫ H) := by
          rw [Hom.one_def, ← Category.assoc, ← Category.assoc, hs, Category.id_comp]
      _ = η[Q₂.A.X] := by
          rw [hpt, Hom.one_def, ← Category.assoc, hs, Category.id_comp]
  have hη' : η[Q₂.A.X] ≫ H' = η[Q₁.A.X] := by
    rw [← hη, Category.assoc, hinv₁, Category.comp_id]
  haveI : IsMonHom H := G0FibreSimple.rigidityHom L Q₁.A Q₂.A H hη
  haveI : IsMonHom H' := G0FibreSimple.rigidityHom L Q₂.A Q₁.A H' hη'
  refine ⟨⟨PkgI3.AbVar.Hom.mk' H, PkgI3.AbVar.Hom.mk' H', hinv₁, hinv₂, fun a => ?_⟩⟩
  simp only [PkgI3.AbVar.Hom.hom_mk']
  apply Over.OverMorphism.ext
  apply pb₂.hom_ext
  · simp only [Over.comp_left, Category.assoc, H, i, Over.homMk_left,
      IsPullback.isoIsPullback_hom_fst, ι₂]
    rw [ι₁]
    simp only [← Category.assoc, IsPullback.isoIsPullback_hom_fst]
  · simp only [Over.comp_left, Category.assoc, H, i, Over.homMk_left,
      IsPullback.isoIsPullback_hom_snd, Over.w]

/-- **On a coarse witness, the residue field of a point is the field of moduli of its pair.** -/
theorem residueImage_eq_fieldOfModuliPair {Y : Over (Spec (CommRingCat.of ℚ))} {Φ : PtEquiv Y}
    {X : Over (Spec (CommRingCat.of ℚ))} {Ψ : (fieldPt Qbar ⟶ X) ≃ Quotient (pairSetoid Qbar)}
    {fY : Y ⟶ X} (h6 : X6Props Y Φ X Ψ fY) (x : fieldPt Qbar ⟶ X) (P : QMPair Qbar)
    (hP : Ψ x = Quotient.mk _ P) :
    residueImage (X := X.left) x.left = fieldOfModuliPair P := by
  apply le_antisymm
  · intro a ha
    rw [fieldOfModuliPair, IntermediateField.mem_fixedField_iff]
    intro τ hτ
    have hcl : Subgroup.closure (stabPair P) ≤ (residueImage (X := X.left) x.left).fixingSubgroup := by
      rw [Subgroup.closure_le]
      intro σ hσ
      obtain ⟨Q, hQ, hbc⟩ := h6.2.2.2.1 σ x P hP
      obtain ⟨e⟩ := qmIso_of_isBaseChangeOfPair hσ hbc
      have hx : fieldMap (σ : Qbar →ₐ[ℚ] Qbar) ≫ x = x := by
        apply Ψ.injective
        rw [hQ, hP]
        exact Quotient.sound ⟨e.symm⟩
      have hfix := (specMap_comp_eq_self_iff x.left σ).mp (congrArg CommaMorphism.left hx)
      exact (IntermediateField.mem_fixingSubgroup_iff _ _).mpr hfix
    exact (IntermediateField.mem_fixingSubgroup_iff _ _).mp (hcl hτ) a ha
  · apply fixedField_le_of_le
    intro σ hσ
    apply Subgroup.subset_closure
    have hfix : ∀ a ∈ residueImage (X := X.left) x.left, σ a = a := fun a ha =>
      (IntermediateField.mem_fixingSubgroup_iff _ _).mp hσ a ha
    have hx : fieldMap (σ : Qbar →ₐ[ℚ] Qbar) ≫ x = x := by
      apply Over.OverMorphism.ext
      exact (specMap_comp_eq_self_iff x.left σ).mpr hfix
    obtain ⟨Q, hQ, hbc⟩ := h6.2.2.2.1 σ x P hP
    rw [hx, hP] at hQ
    obtain ⟨e⟩ := Quotient.exact hQ
    exact isBaseChangeOfPair_of_iso hbc e

end ZInQ.LeafFold9

namespace HDec

namespace HSyn

open CategoryTheory AlgebraicGeometry Limits

/-! ## R1(d) and R5 from the witness of `r1r2` -/

/-- **`R1rec` from `R1R2fpRep`**: the object `P` is the object at a point `y` of the fine witness (`Φ` is a
bijection), the witness's reciprocity clause makes `ℚ(y)` unramified above 5, and `fieldOfModuli3 P ⊆ ℚ(y)`. -/
theorem r1rec_of_rep (h : LeafAdopt.R1R2fpRep) : LeafQM.AV.R1rec := by
  obtain ⟨Y, Φ, X, Ψ, fY, π₆, h1, -, -, -, hrec, -, -, -⟩ := h
  intro P hcm
  have hy : Φ _ ((Φ _).symm (LeafQM.AV.M3.mk P)) = LeafQM.AV.M3.mk P := Equiv.apply_symm_apply _ _
  exact _root_.ZInQ.LeafFold9.unramifiedAbove5_mono (_root_.ZInQ.LeafFold9.fieldOfModuli3_le h1 _ P hy)
    (hrec _ P hy hcm)

/-- **`R5fp` from `R1R2fpRep`**: the pair `P` is the pair at a point `x` of the coarse witness (`Ψ` is a
bijection), the witness's González–Rotger clause is about `ℚ(x)`, and `ℚ(x)` is the field of moduli of `P`. -/
theorem r5fp_of_rep (h : LeafAdopt.R1R2fpRep) : LeafQM.AV.R5fp := by
  obtain ⟨Y, Φ, X, Ψ, fY, π₆, -, -, h6, -, -, -, h5, -⟩ := h
  intro k _ _ _ hk R hR hc P hP
  have hx : Ψ (Ψ.symm (Quotient.mk _ P)) = Quotient.mk _ P := Equiv.apply_symm_apply _ _
  obtain ⟨h5a, h5b⟩ := h5 k hk R hR hc _ P hx hP
  have e := _root_.ZInQ.LeafFold9.residueImage_eq_fieldOfModuliPair h6 _ P hx
  refine ⟨?_, fun hne => (h5b hne).map fun φ => (IntermediateField.equivOfEq e).toAlgHom.comp φ⟩
  rw [← h5a]
  exact (IntermediateField.equivOfEq e).toLinearEquiv.finrank_eq.symm

end HSyn

end HDec
