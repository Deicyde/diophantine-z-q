/- Additional modification notice, 2026-11-16: Cloud Batch 3 Worker 13
retargeted only repository module paths into the task-owned CloudB3W13
directories. Canonical mathematical declaration names and statements
are retained. Recovery and later compatibility changes are documented
in the accompanying source manifest and NOTICE. -/
import ZInQKernel.Contrib.CloudB3W13.Dictionary.D8.FibreTransport
import ZInQKernel.Contrib.CloudB3W13.Dictionary.D8.BasePoint

/-!
# D8: honest point/fibre clauses of the ORIGINAL model, with explicit dictionary inputs

Original W01/Metamate source, 2026-11-15. These are CONDITIONAL intermediates:
hD2/hD34/hD5/hD6/hUnique are the actual existing native obligation statements,
not hidden constructor Facts or replacements for H119. The final unconditioned
H119 supplier is not claimed until all actual proofs/companions and final
kernel/non-author checks close. Actual PtF, family, packaging and maps are kept.
-/

noncomputable section
namespace ZInQ.Contrib.CloudB2Shimura.Dictionary.D8
open CategoryTheory AlgebraicGeometry Limits
open ZInQ.Contrib.CloudW03NeronSurj
open LeafQM.AV

/-- Package any ORIGINAL FLT level object using the ORIGINAL D2/D34 statements.
Both exact action and level-point equalities are returned as IsPackaging. -/
theorem exists_packaging (hD2 : D2_Obligation) (hD34 : D34_Obligation)
    {K : Type} [Field K] [CharZero K] (u : FLTL3 K) :
    ∃ (h : AbVarProps u.1) (hs : (abVarOfFakeEC u.1 h).dim = 2)
      (q : LeafQM.AV.QMStr (abVarOfFakeEC u.1 h)) (e : LeafQM.AV.Level3 q),
      IsPackaging u h q e := by
  obtain ⟨h, hs⟩ := hD2 K u.1
  obtain ⟨q, hact, e, heta⟩ := hD34 K u h
  exact ⟨h, hs, q, e, hact, heta⟩

section FineModel
variable (𝒪 : Type) [CommRing 𝒪] {M : Scheme.{0}}
  (πM : M ⟶ Spec (CommRingCat.of 𝒪)) (ptF : PtF 𝒪 πM)
  (hM : FLT.CerednikDrinfeld.QM.IsFineModuli Λ 1 3 M πM ptF)
  (𝒜 : QMFamily M) (hF : HasFLTFibres 𝒪 πM ptF 𝒜)

include hM hF in
/-- Clause 3: the ORIGINAL family has an actual object at EVERY field point.
A Q-algebra field is characteristic zero natively, not a new caller premise. -/
theorem object_at_field_point (hD2 : D2_Obligation) (hD34 : D34_Obligation)
    (K : Type) [Field K] [Algebra ℚ K] (y : Spec (CommRingCat.of K) ⟶ M) :
    ∃ P : QML3 K, IsFibreOf 𝒜 y P := by
  haveI : CharZero K := Algebra.charZero_of_charZero (R := ℚ) (A := K)
  let s := y ≫ πM
  obtain ⟨u, hu⟩ := hM.ptF_surjective K s ⟨y, rfl⟩
  obtain ⟨h, hs, q, e, hp⟩ := exists_packaging hD2 hD34 u
  have hf := hF K s u h hs q e hp
  have hy : (ptF K s u).1 = y := congrArg Subtype.val hu
  rw [hy] at hf
  exact ⟨⟨abVarOfFakeEC u.1 h, hs, q, e⟩, hf⟩

include hM hF in
/-- Clause 4: the ORIGINAL moduli field points are separated by actual fibre
isomorphism classes. Base-map uniqueness is explicit here; final Zloc assembly
uses the already-proved HDec.ModelGlue.spec_to_zloc_eq, not a new Fact. -/
theorem point_eq_of_fibre_class (hD2 : D2_Obligation) (hD34 : D34_Obligation)
    (hD6 : D6_Obligation) (hUnique : FibreUnique_Obligation)
    (hbase : ∀ s s' : Spec (CommRingCat.of Qbar) ⟶ Spec (CommRingCat.of 𝒪), s = s')
    (y y' : Spec (CommRingCat.of Qbar) ⟶ M) (P P' : QML3 Qbar)
    (hP : IsFibreOf 𝒜 y P) (hP' : IsFibreOf 𝒜 y' P') (hPP' : M3.mk P = M3.mk P') :
    y = y' := by
  let s := y ≫ πM
  obtain ⟨u, hu⟩ := hM.ptF_surjective Qbar s ⟨y, rfl⟩
  obtain ⟨u', hu'⟩ := hM.ptF_surjective Qbar s ⟨y', hbase (y' ≫ πM) s⟩
  obtain ⟨h, hs, q, e, hp⟩ := exists_packaging hD2 hD34 u
  obtain ⟨h', hs', q', e', hp'⟩ := exists_packaging hD2 hD34 u'
  have hf := hF Qbar s u h hs q e hp
  have hf' := hF Qbar s u' h' hs' q' e' hp'
  have hy : (ptF Qbar s u).1 = y := congrArg Subtype.val hu
  have hy' : (ptF Qbar s u').1 = y' := congrArg Subtype.val hu'
  rw [hy] at hf
  rw [hy'] at hf'
  have hPR := hUnique M 𝒜 Qbar y P ⟨abVarOfFakeEC u.1 h, hs, q, e⟩ hP hf
  have hP'R' := hUnique M 𝒜 Qbar y' P' ⟨abVarOfFakeEC u'.1 h', hs', q', e'⟩ hP' hf'
  have hRR' : M3.mk (⟨abVarOfFakeEC u.1 h, hs, q, e⟩ : QML3 Qbar) =
      M3.mk (⟨abVarOfFakeEC u'.1 h', hs', q', e'⟩ : QML3 Qbar) :=
    hPR.symm.trans (hPP'.trans hP'R')
  have hIso := (hD6 Qbar u u' h h' hs hs' q e q' e' hp hp').mpr (Quotient.exact hRR')
  have hpteq := hM.ptF_iso Qbar s u u' hIso
  exact hy.symm.trans ((congrArg Subtype.val hpteq).trans hy')

include hF in
/-- Clause 5: every ORIGINAL Qbar object occurs in the ACTUAL family.
The source D5 witness is packaged→P, so its ψ map transports the fibre to P. -/
theorem every_Qbar_object_occurs (hD5 : D5_Obligation)
    (s0 : Spec (CommRingCat.of Qbar) ⟶ Spec (CommRingCat.of 𝒪)) (P : QML3 Qbar) :
    ∃ y : Spec (CommRingCat.of Qbar) ⟶ M, IsFibreOf 𝒜 y P := by
  obtain ⟨u, h, hs, q, e, hact, heta, ⟨I⟩⟩ := hD5 P
  have hf := hF Qbar s0 u h hs q e ⟨hact, heta⟩
  exact ⟨(ptF Qbar s0 u).1, isFibreOf_of_iso 𝒜 I hf⟩

end FineModel

#print axioms object_at_field_point
#print axioms point_eq_of_fibre_class
#print axioms every_Qbar_object_occurs

end ZInQ.Contrib.CloudB2Shimura.Dictionary.D8
