import ZInQKernel.Contrib.OneProof.RaynaudSemistableOr
import ZInQKernel.OneProof.H.TailZ23
import ZInQKernel.Contrib.OneProof.GeomConnOfRationalPoint

/-!
# raynaud-narrow: Raynaud's criterion in the printed form the live proof consumes

Task raynaud-narrow (docs/research/raynaud-narrow.md). The live chain to `ZInQ.OneProof.frozenTarget` reads the
research field `raynaudSemistableSHOr` (dict-models, TailZ45) only through `raynaudSemistable_of14` (TailZ23), whose
two readers apply SGA 7 IX 4.7 at a DVR of a number field after passing to a strictly henselian extension
(`ReductB.raynaudSemistableCP_of_SH`): characteristic `0`, algebraically closed residue field. So the chain needs
only `ReductB.RaynaudSemistableSHcp` (TailZ23; raynaud-proof's `RaynaudCP.consumers_of_cp_leaves`).

This file states the new LEAF `RaynaudSemistableSHcpOr`: dict-models' `RaynaudSemistableSHOr` restricted to
`[CharZero K]` and `[PerfectField κ(O)]` (with `IsStrictlyHenselianDVR O`, `κ(O)` is then algebraically closed), and
proves

* `cpOr_of_or : RaynaudSemistableSHOr → RaynaudSemistableSHcpOr` (the new leaf is never stronger than the current
  bundle leaf);
* `raynaudSemistableSHcp_of_cpOr : RaynaudSemistableSHcpOr → GeomConnOfRationalPoint → RaynaudSemistableSHcp` (the
  `k(s)` reading ascends to the geometric one by dict-models' `isSemistable_of_resT`, Stacks 04KV, proved:
  `geomConnOfRationalPoint_proof`);
* `raynaudSemistableSHcp_of_cpOr' : RaynaudSemistableSHcpOr → RaynaudSemistableSHcp` with that input discharged.

No `sorry`, no `axiom`.
-/

noncomputable section

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReductSplit ReductGlue ZInQ.HeightSplit

namespace RaynaudNarrow

open DictModels.RaynaudOr

/-- **LEAF `RaynaudSemistableSHcpOr`** (Raynaud's criterion, SGA 7 I (LNM 288), Exp. IX, Prop. 4.7; number
UNVERIFIED, no network), restricted to a strictly henselian DVR `O` of a field `K` of characteristic `0` whose
residue field is perfect, hence algebraically closed. *Printed* (as recalled): `S` a trait, `m ≥ 3` invertible on
`S`, `A_K` an abelian variety all of whose points of order `m` are rational over `K`: then `A_K` has semistable
reduction. *Lean form*: dict-models' `RaynaudSemistableSHOr` word for word with `[CharZero K]` and
`[PerfectField (IsLocalRing.ResidueField O)]` added: hypotheses those of `ReductGlue.RaynaudSemistableSH`, conclusion
the disjunction of semistability over `k(s)` (general torus, `IsSemistableResT`) for every Néron model and
semistability on the geometric special fibre (`SemistableNeronModels`). Either reading of "semistable reduction"
gives it by or-introduction; if the print assumes an algebraically closed residue field, or a base of
characteristic `0`, this is still a specialization of it. Remaining reading risk (UNVERIFIED): the print may require
`m > 3` (locators.md R6); a Galois-form conclusion (low risk: SGA 7 IX defines semistable reduction by the Néron
model). -/
def RaynaudSemistableSHcpOr : Prop :=
  ∀ (K : Type) [Field K] [CharZero K] (O : ValuationSubring K) [IsDiscreteValuationRing O]
    [PerfectField (IsLocalRing.ResidueField O)],
    IsStrictlyHenselianDVR O → ∀ (A : PkgI3.AbVar K) (m : ℕ), 3 ≤ m → IsUnit (m : O) →
    (∀ x : A.Pt (AlgebraicClosure K), x ^ m = 1 →
      ∃ y : A.Pt K, ZInQ.Contrib.AbVarBC.extPt A (Algebra.ofId K (AlgebraicClosure K)) y = x) →
    (∀ 𝒩 : GroupModelO A O, 𝒩.IsNeronModel → IsSemistableResT 𝒩) ∨ SemistableNeronModels A O

/-- The current bundle leaf implies the new one (a specialization): the new leaf is not stronger. -/
theorem cpOr_of_or (h : RaynaudSemistableSHOr) : RaynaudSemistableSHcpOr :=
  fun K _ _ O _ _ hS A m hm hu ht => h K O hS A m hm hu ht

/-- `ReductB.RaynaudSemistableSHcp` implies the new leaf (`Or.inr`). -/
theorem cpOr_of_cp (h : ReductB.RaynaudSemistableSHcp) : RaynaudSemistableSHcpOr :=
  fun K _ _ O _ _ hS A m hm hu ht => Or.inr (h K O hS A m hm hu ht)

/-- **The narrowed form the chain consumes, exactly** (`ReductB.RaynaudSemistableSHcp`), from the new leaf and
`GeomConnOfRationalPoint` (Stacks 04KV; ascent `k(s)` → `k̄` by dict-models' `isSemistable_of_resT`). -/
theorem raynaudSemistableSHcp_of_cpOr (h : RaynaudSemistableSHcpOr) (hGC : AVGlue.GeomConnOfRationalPoint) :
    ReductB.RaynaudSemistableSHcp := by
  intro K _ _ O _ _ hS A m hm hu ht
  rcases h K O hS A m hm hu ht with h1 | h2
  · exact fun 𝒩 h𝒩 => isSemistable_of_resT hGC 𝒩 (h1 𝒩 h𝒩)
  · exact h2

/-- The same with `GeomConnOfRationalPoint` discharged by its proof in the tree. -/
theorem raynaudSemistableSHcp_of_cpOr' (h : RaynaudSemistableSHcpOr) : ReductB.RaynaudSemistableSHcp :=
  raynaudSemistableSHcp_of_cpOr h _root_.geomConnOfRationalPoint_proof

end RaynaudNarrow

end

#print axioms RaynaudNarrow.raynaudSemistableSHcp_of_cpOr'
#print axioms RaynaudNarrow.cpOr_of_or
