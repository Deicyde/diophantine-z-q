/- Additional modification notice, 2026-11-16: Cloud Batch 3 Worker 13
retargeted only repository module paths into the task-owned CloudB3W13
directories. Canonical mathematical declaration names and statements
are retained. Recovery and later compatibility changes are documented
in the accompanying source manifest and NOTICE. -/
import ZInQKernel.Contrib.CloudB3W13.Dictionary.D10.Twist
import ZInQKernel.Contrib.CloudB3W13.Source.Theorems.Thm_CerednikDrinfeld_QM_IsFineModuli_exists_iso_of_isFineModuli

/-!
# D10: the `twist` clause (W13)

The automorphism of `M` is the FLT comparison isomorphism between the fine-moduli structures
`ptF` and `ptF ∘ twist α` (`IsFineModuli.exists_iso_of_isFineModuli`); fibres are compared as in D9.
-/

noncomputable section

namespace ZInQ.Contrib.CloudB2Shimura.Dictionary

open CategoryTheory AlgebraicGeometry Limits
open scoped Quaternion
open ZInQ.Contrib.CloudW03NeronSurj

namespace D10

theorem fltLevelPoint_twistW {K : Type} [Field K] (α : LeafQM.O ≃+* LeafQM.O) (u : FLTL3 K) (a : LeafQM.O) :
    fltLevelPoint (twistW α u) a = fltLevelPoint u (α a) := rfl

end D10

open D10 in
theorem d10_obligation : D10_Obligation := by
  intro 𝒪 _ _ _ M πM ptF hM 𝒜 hF α
  obtain ⟨e, he, hpt, -⟩ :=
    FLT.CerednikDrinfeld.QM.IsFineModuli.exists_iso_of_isFineModuli Λ 1 3 hM (isFineModuli_twist α hM)
  let gI : Over.mk πM ≅ Over.mk πM := Over.isoMk e he
  refine ⟨gI, ?_⟩
  intro yy P P' hP hP'
  obtain ⟨u0, hu0⟩ := hM.ptF_surjective LeafQM.AV.Qbar (yy ≫ πM) ⟨yy, rfl⟩
  let u1 : FLTL3 LeafQM.AV.Qbar := twistW α u0
  have hy1 : (ptF LeafQM.AV.Qbar (yy ≫ πM) u1).1 = yy ≫ gI.hom.left := by
    rw [← hpt LeafQM.AV.Qbar (yy ≫ πM) u0, hu0]
    rfl
  obtain ⟨h0, hs0⟩ := D2_Obligation_proof LeafQM.AV.Qbar u0.1
  obtain ⟨h1, hs1⟩ := D2_Obligation_proof LeafQM.AV.Qbar u1.1
  obtain ⟨q0, hq0, e0, he0⟩ := D34.d34_obligation LeafQM.AV.Qbar u0 h0
  obtain ⟨q1, hq1, e1, he1⟩ := D34.d34_obligation LeafQM.AV.Qbar u1 h1
  have f0 := hF LeafQM.AV.Qbar (yy ≫ πM) u0 h0 hs0 q0 e0 ⟨hq0, he0⟩
  have f1 := hF LeafQM.AV.Qbar (yy ≫ πM) u1 h1 hs1 q1 e1 ⟨hq1, he1⟩
  rw [hu0] at f0
  rw [hy1] at f1
  rw [fibreUnique_obligation M 𝒜 LeafQM.AV.Qbar yy P _ hP f0,
    fibreUnique_obligation M 𝒜 LeafQM.AV.Qbar _ P' _ hP' f1]
  -- the identity is an isomorphism `(A, q1, e1) ≅ (A, q0 ∘ α, e0 ∘ α)`
  apply Quotient.sound
  show Nonempty (LeafQM.AV.QML3.Iso ⟨abVarOfFakeEC u0.1 h0, hs0, q1, e1⟩
    ⟨abVarOfFakeEC u0.1 h0, hs0, q0.twist α, e0.twist α⟩)
  refine ⟨⟨1, 1, ?_, ?_, ?_, ?_⟩⟩
  · simp [PkgI3.AbVar.Hom.hom_mk', OfNat.ofNat, One.one]
  · simp [PkgI3.AbVar.Hom.hom_mk', OfNat.ofNat, One.one]
  · intro a
    change _ ≫ 𝟙 _ = 𝟙 _ ≫ _
    rw [Category.comp_id, Category.id_comp]
    apply Over.OverMorphism.ext
    exact (hq1 a).trans (hq0 (α a)).symm
  · intro a
    change Additive.ofMul (Additive.toMul (e1.eta a) ≫ 𝟙 _) = e0.eta (α a)
    rw [Category.comp_id]
    change e1.eta a = e0.eta (α a)
    apply Additive.toMul.injective
    apply Over.OverMorphism.ext
    rw [he1]
    exact (fltLevelPoint_twistW α u0 a).trans (he0 (α a)).symm

end ZInQ.Contrib.CloudB2Shimura.Dictionary

#print axioms ZInQ.Contrib.CloudB2Shimura.Dictionary.d10_obligation
