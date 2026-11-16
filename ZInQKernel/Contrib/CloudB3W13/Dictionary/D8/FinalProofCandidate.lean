/- Additional modification notice, 2026-11-16: Cloud Batch 3 Worker 13
retargeted only repository module paths into the task-owned CloudB3W13
directories. Canonical mathematical declaration names and statements
are retained. Recovery and later compatibility changes are documented
in the accompanying source manifest and NOTICE. -/
import ZInQKernel.Contrib.CloudB3W13.Dictionary.D8.Assembly
import ZInQKernel.Contrib.CloudB3W13.Dictionary.D2.Proof
import ZInQKernel.Contrib.CloudB3W13.Dictionary.D34.Obligation
import ZInQKernel.Contrib.CloudB3W13.Dictionary.D5.Count
import ZInQKernel.Contrib.CloudB3W13.Dictionary.D6.Iso
import ZInQKernel.Contrib.CloudB3W13.Dictionary.D7.Obligation
import ZInQKernel.Contrib.CloudB3W13.Dictionary.D9.Proof
import ZInQKernel.Contrib.CloudB3W13.Dictionary.D10.Proof
import ZInQKernel.Contrib.CloudB3W13.Source.Theorems.Thm_CerednikDrinfeld_QM_exists_isFineModuli_of_isUnit_two_of_isUnit_three
import ZInQKernel.Contrib.CloudB3W13.Source.Theorems.Thm_CerednikDrinfeld_QM_IsFineModuli_isProper_of_isUnit_two_of_isUnit_three

/-!
# D8: NEW SOURCE-ONLY final proof candidate for the exact original H119

Original W01/Metamate candidate, 2026-11-15, written on the retained node only.
This file has NOT been compiled, kernel checked or accepted as an H119 proof.
Parent authorized SOURCE mathematics/review only, not compiler/Root staging.

The unchanged Assembly.e174 implication is applied to the actual accepted
D2/D34/D5/D6/D7/D9/D10/FibreUnique theorem constants. Its two remaining factory
arguments are supplied by the unchanged canonical existence/properness
companions at the actual order_bridge, N=1, m=3. There is no final dictionary,
factory, Root/world, model, base-point or base-uniqueness hypothesis.

Assembly chooses ONE M/πM/PtF tuple, applies properness to the same hM, and
uses its smooth-at-6 clause, D0 units and the original TailL base data to
return the seven original clauses. Component4c0d, Assembly.e174, Interfaces,
Root, pins and all proof suppliers remain byte-for-byte unchanged. No new
model/alias/datatype/axiom or numerical proof option is introduced here.
-/

noncomputable section

namespace ZInQ.Contrib.CloudB2Shimura.Dictionary.D8

open CategoryTheory AlgebraicGeometry
open ZInQ.Contrib.CloudW03NeronSurj

/-- UNCOMPILED SOURCE candidate: the declaration has exactly the original H119
as its target, with no final assumptions. A proof grade still requires the
parent-selected coherent environment, actual native checks and Source review. -/
theorem shimuraGoodReductionNoGuard_proof :
    HDec.CurveSplitGR.ShimuraGoodReductionNoGuard := by
  refine shimuraGoodReductionNoGuard_of_dict
    D2_Obligation_proof D34.d34_obligation D5.d5_obligation
    D6.d6_obligation D7.d7_obligation d9_obligation d10_obligation
    fibreUnique_obligation ?_ ?_
  · intro 𝒪 _ hN hm h2 h3
    letI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    letI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    letI : NeZero (1 : ℕ) := ⟨by decide⟩
    exact FLT.CerednikDrinfeld.QM.exists_isFineModuli_of_isUnit_two_of_isUnit_three
      (q := 2) (q' := 3) (a := 2) (b := -3)
      (by decide) ZInQ.Contrib.CloudB2Shimura.order_bridge.1
      Λ ZInQ.Contrib.CloudB2Shimura.order_bridge.2.1
      1 3 (by decide) 𝒪 hN hm h2 h3
  · intro 𝒪 _ _ _ hN hm h2 h3 M πM ptF hM
    letI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    letI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    letI : NeZero (1 : ℕ) := ⟨by decide⟩
    exact FLT.CerednikDrinfeld.QM.IsFineModuli.isProper_of_isUnit_two_of_isUnit_three
      (q := 2) (q' := 3) (a := 2) (b := -3)
      (M := M) (πM := πM) (ptF := ptF)
      (by decide) ZInQ.Contrib.CloudB2Shimura.order_bridge.1
      Λ ZInQ.Contrib.CloudB2Shimura.order_bridge.2.1
      1 3 (by decide) 𝒪 hN hm h2 h3 hM

end ZInQ.Contrib.CloudB2Shimura.Dictionary.D8
