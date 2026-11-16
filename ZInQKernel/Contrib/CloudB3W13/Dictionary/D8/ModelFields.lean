/- Additional modification notice, 2026-11-16: Cloud Batch 3 Worker 13
retargeted only repository module paths into the task-owned CloudB3W13
directories. Canonical mathematical declaration names and statements
are retained. Recovery and later compatibility changes are documented
in the accompanying source manifest and NOTICE. -/
import ZInQKernel.Contrib.CloudB3W13.Dictionary.D8.FieldClauses

/-!
# D8: conditional assembly of the SEVEN ORIGINAL model clauses

Original W01/Metamate proof, 2026-11-15. No new model predicate/axiom/Fact is
introduced: the conclusion is the literal original seven-clause list on the
actual Over.mk πM and QMFamily. Pending native dictionary statements remain
EXPLICIT arguments, and actual companion-provided proper/smooth/fine-moduli
geometry stays explicit. This is NOT an unconditional H119 certificate.
The final TailW wrapper rewrites only the unchanged original target definition.
-/

noncomputable section
namespace ZInQ.Contrib.CloudB2Shimura.Dictionary.D8
open CategoryTheory AlgebraicGeometry Limits
open ZInQ.Contrib.CloudW03NeronSurj
open LeafQM.AV

/-- Literal seven-clause model statement, assembled from the ACTUAL caller
family and native dictionaries. No hypothesis is hidden inside a constructor. -/
theorem model_fields_of_data (hD2 : D2_Obligation) (hD34 : D34_Obligation)
    (hD5 : D5_Obligation) (hD6 : D6_Obligation) (hD9 : D9_Obligation)
    (hD10 : D10_Obligation) (hUnique : FibreUnique_Obligation)
    (𝒪 : Type) [CommRing 𝒪] (h2 : IsUnit ((2 : ℕ) : 𝒪)) (h3 : IsUnit ((3 : ℕ) : 𝒪))
    (M : Scheme.{0}) (πM : M ⟶ Spec (CommRingCat.of 𝒪)) (ptF : PtF 𝒪 πM)
    (hM : FLT.CerednikDrinfeld.QM.IsFineModuli Λ 1 3 M πM ptF)
    (𝒜 : QMFamily M) (hF : HasFLTFibres 𝒪 πM ptF 𝒜)
    (hproper : IsProper πM) (hsmooth : SmoothOfRelativeDimension 1 πM)
    (hbase : ∀ s s' : Spec (CommRingCat.of Qbar) ⟶ Spec (CommRingCat.of 𝒪), s = s')
    (s0 : Spec (CommRingCat.of Qbar) ⟶ Spec (CommRingCat.of 𝒪)) :
    IsProper (Over.mk πM).hom ∧ SmoothOfRelativeDimension 1 (Over.mk πM).hom ∧
    (∀ (K : Type) [Field K] [Algebra ℚ K] (y : Spec (CommRingCat.of K) ⟶ M),
      ∃ P : QML3 K, IsFibreOf 𝒜 y P) ∧
    (∀ (y y' : Spec (CommRingCat.of Qbar) ⟶ M) (P P' : QML3 Qbar),
      IsFibreOf 𝒜 y P → IsFibreOf 𝒜 y' P' → M3.mk P = M3.mk P' → y = y') ∧
    (∀ P : QML3 Qbar, ∃ y : Spec (CommRingCat.of Qbar) ⟶ M, IsFibreOf 𝒜 y P) ∧
    (∀ α : LeafQM.O ≃+* LeafQM.O, ∃ g : Over.mk πM ≅ Over.mk πM,
      ∀ (y : Spec (CommRingCat.of Qbar) ⟶ M) (P P' : QML3 Qbar),
        IsFibreOf 𝒜 y P → IsFibreOf 𝒜 (y ≫ g.hom.left) P' → M3.mk P' = M3.twist α (M3.mk P)) ∧
    (∀ u : (LeafQM.O)ˣ, ∃ g : Over.mk πM ≅ Over.mk πM,
      ∀ (y : Spec (CommRingCat.of Qbar) ⟶ M) (P P' : QML3 Qbar),
        IsFibreOf 𝒜 y P → IsFibreOf 𝒜 (y ≫ g.hom.left) P' → M3.mk P' = M3.rightMul u (M3.mk P)) := by
  refine ⟨hproper, hsmooth, ?_, ?_, ?_, ?_, ?_⟩
  · exact object_at_field_point 𝒪 πM ptF hM 𝒜 hF hD2 hD34
  · exact point_eq_of_fibre_class 𝒪 πM ptF hM 𝒜 hF hD2 hD34 hD6 hUnique hbase
  · exact every_Qbar_object_occurs 𝒪 πM ptF 𝒜 hF hD5 s0
  · exact hD10 𝒪 h2 h3 M πM ptF hM 𝒜 hF
  · exact hD9 𝒪 h2 h3 M πM ptF hM 𝒜 hF

/-- Construct the ACTUAL family by the native D7 statement, then assemble the
literal seven clauses. D7 is still visible as an explicit conditional input. -/
theorem model_exists_of_dict (hD2 : D2_Obligation) (hD34 : D34_Obligation)
    (hD5 : D5_Obligation) (hD6 : D6_Obligation) (hD7 : D7_Obligation)
    (hD9 : D9_Obligation) (hD10 : D10_Obligation) (hUnique : FibreUnique_Obligation)
    (𝒪 : Type) [CommRing 𝒪] (h2 : IsUnit ((2 : ℕ) : 𝒪)) (h3 : IsUnit ((3 : ℕ) : 𝒪))
    (M : Scheme.{0}) (πM : M ⟶ Spec (CommRingCat.of 𝒪)) (ptF : PtF 𝒪 πM)
    (hM : FLT.CerednikDrinfeld.QM.IsFineModuli Λ 1 3 M πM ptF)
    (hsep : IsSeparated πM) (hqc : QuasiCompact πM) (hlft : LocallyOfFiniteType πM)
    (hAF : ∀ F : Finset M, ∃ U : M.Opens, IsAffineOpen U ∧ ∀ x ∈ F, x ∈ U)
    (hproper : IsProper πM) (hsmooth : SmoothOfRelativeDimension 1 πM)
    (hbase : ∀ s s' : Spec (CommRingCat.of Qbar) ⟶ Spec (CommRingCat.of 𝒪), s = s')
    (s0 : Spec (CommRingCat.of Qbar) ⟶ Spec (CommRingCat.of 𝒪)) :
    ∃ 𝒜 : QMFamily M,
      IsProper (Over.mk πM).hom ∧ SmoothOfRelativeDimension 1 (Over.mk πM).hom ∧
      (∀ (K : Type) [Field K] [Algebra ℚ K] (y : Spec (CommRingCat.of K) ⟶ M),
        ∃ P : QML3 K, IsFibreOf 𝒜 y P) ∧
      (∀ (y y' : Spec (CommRingCat.of Qbar) ⟶ M) (P P' : QML3 Qbar),
        IsFibreOf 𝒜 y P → IsFibreOf 𝒜 y' P' → M3.mk P = M3.mk P' → y = y') ∧
      (∀ P : QML3 Qbar, ∃ y : Spec (CommRingCat.of Qbar) ⟶ M, IsFibreOf 𝒜 y P) ∧
      (∀ α : LeafQM.O ≃+* LeafQM.O, ∃ g : Over.mk πM ≅ Over.mk πM,
        ∀ (y : Spec (CommRingCat.of Qbar) ⟶ M) (P P' : QML3 Qbar),
          IsFibreOf 𝒜 y P → IsFibreOf 𝒜 (y ≫ g.hom.left) P' → M3.mk P' = M3.twist α (M3.mk P)) ∧
      (∀ u : (LeafQM.O)ˣ, ∃ g : Over.mk πM ≅ Over.mk πM,
        ∀ (y : Spec (CommRingCat.of Qbar) ⟶ M) (P P' : QML3 Qbar),
          IsFibreOf 𝒜 y P → IsFibreOf 𝒜 (y ≫ g.hom.left) P' → M3.mk P' = M3.rightMul u (M3.mk P)) := by
  obtain ⟨𝒜, hF⟩ := hD7 𝒪 h2 h3 M πM ptF hM hsep hqc hlft hAF
  exact ⟨𝒜, model_fields_of_data hD2 hD34 hD5 hD6 hD9 hD10 hUnique
    𝒪 h2 h3 M πM ptF hM 𝒜 hF hproper hsmooth hbase s0⟩

#print axioms model_fields_of_data
#print axioms model_exists_of_dict

end ZInQ.Contrib.CloudB2Shimura.Dictionary.D8
