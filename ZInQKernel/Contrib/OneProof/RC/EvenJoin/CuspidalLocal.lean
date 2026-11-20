import ZInQKernel.Contrib.OneProof.RC.EvenJoin.Scoped

/-! The actual rows are cuspidal. A local stage therefore has an empty
Eisenstein sector; no Eisenstein local comparison is needed. -/

noncomputable section

namespace ZInQ.Manuscript.RC.EvenJoin

open AddressGenuine O12 O12Local PrintsArith
open ZInQ.Contrib.CloudB3RC53.CoefficientDictionary

variable {L : Type} [AddCommGroup L] {ε : L →+ ZMod 2} {T : TypeData L ε}
variable {R : Finset ℕ → ZMod 2} {ap : ℕ → ℤ} {B : ℕ}
variable {χ : GalQ →* Multiplicative L} {X : GaloisConstituentModel T R ap B χ}
variable {p : ℕ} {P : LocalPair p}

private def emptySector : Sector X P where
  active := ∅
  ramified := ∅
  ramified_active := Set.Subset.rfl
  Up := 0
  active_stable := by simp [SupportedOn]
  ramified_stable := by simp [SupportedOn]
  old := by simp
  newLine := by simp

private theorem emptySector_shift (A : FourierData X) (hp : p ≠ 0) :
    (emptySector (X := X) (P := P)).UpAtOne A hp := by
  intro v hv
  have he : v = 0 := funext (fun i => hv i (Set.notMem_empty i))
  simp [emptySector, he]

/-- Only the cuspidal representation and its Whittaker comparison at the
tested prime are needed for the actual seed. -/
def cuspidalStage [Fact p.Prime] (A : FourierData X) (U : Finset ℕ) (hp : p ≠ 0)
    (C : CuspidalData X P) (hF : SupportedOn C.active (X.F U : X.I → X.K))
    (hW : WhittakerComparison p hp {v | SupportedOn C.active v} C.up
      (fun n v => X.coefK v (A.index n))) : Stage A U P hp where
  cusp := C
  eisenstein := emptySector
  disjoint := by simp [emptySector]
  support := by simpa only [emptySector, Set.union_empty] using hF
  whittaker := hW
  eisenstein_shift := emptySector_shift A hp

end ZInQ.Manuscript.RC.EvenJoin
