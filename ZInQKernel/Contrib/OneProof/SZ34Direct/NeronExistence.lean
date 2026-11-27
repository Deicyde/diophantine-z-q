import ZInQKernel.Contrib.OneProof.NeronDVR
import ZInQKernel.Contrib.OneProof.NeronDVR.RelativeSquare

/-!
# Néron models over every discrete valuation ring, proved

The existence half of `SZRaynaud.SilverbergZarhinThm34` needs no printed row: the tree proves
Néron-model existence over an arbitrary discrete valuation ring, with no hypotheses
(`NeronDVR.exists_neron_model_strict_henselization` builds a Néron model over a strict
henselization, `NeronDVR.strictHenselizationDescent_of_relativeSquare` with the proved
`NeronDVR.relativeSquareStrictNeron` descends it). This file repackages that result in the two
forms the Silverberg–Zarhin glue reads:

* `neronSchemeModelExistsDVR_proof : ReductSplit.NeronSchemeModelExistsDVR` (the scheme-level
  statement over a valuation subring, Néron mapping property composed with the generic-fibre
  identification);
* `exists_neron_groupModelO`: a Néron model which is a group model
  (`ReductSplit.GroupModelO` with `IsNeronModel`), through `ReductSplit.exists_neron_groupModel`.

The notion of Néron model is the mapping property of Bosch–Lütkebohmert–Raynaud, *Néron Models*
(1990), §1.2 Def. 1 (`CToPrinted.IsNeronModelOver`: smooth, separated, of finite type, unique
extension of morphisms from generic fibres of smooth schemes), which is the definition
Silverberg–Zarhin print on p. 405 together with finite type.
-/

noncomputable section

open CategoryTheory AlgebraicGeometry

namespace SZ34Direct

/-- A Néron model over a discrete valuation ring presented as a valuation subring, with its
generic fibre identified with `A` (proved in the tree, no hypotheses). -/
theorem exists_isNeronModelOver (K : Type) [Field K] (O : ValuationSubring K)
    [IsDiscreteValuationRing O] (A : PkgI3.AbVar K) :
    ∃ M : Over (Spec (CommRingCat.of O)), CToPrinted.IsNeronModelOver O K M ∧
      Nonempty ((Over.pullback (ZInQ.Contrib.GroupLawNeron.genMap O K)).obj M ≅ A.X) := by
  obtain ⟨E, _, _, P, hP, hSH, N, hN, eN⟩ :=
    NeronDVR.exists_neron_model_strict_henselization O A
  exact NeronDVR.strictHenselizationDescent_of_relativeSquare NeronDVR.relativeSquareStrictNeron
    K O E P hP hSH A N hN eN

/-- **Néron's existence theorem over a discrete valuation ring**, in the form of the former
research field `ReductSplit.NeronSchemeModelExistsDVR`, proved. -/
theorem neronSchemeModelExistsDVR_proof : ReductSplit.NeronSchemeModelExistsDVR := by
  intro K _ O _ A
  obtain ⟨M, ⟨hS, hSep, _, hQC, hB⟩, ⟨ε⟩⟩ := exists_isNeronModelOver K O A
  exact ⟨M, hS, hSep, hQC, ε, fun Y hY =>
    (GapNeron.bijective_comp_iso' _ ε).mpr (@hB Y hY)⟩

/-- A Néron model of `A` over `O` which is a group model (group law from the mapping property). -/
theorem exists_neron_groupModelO {K : Type} [Field K] (O : ValuationSubring K)
    [IsDiscreteValuationRing O] (A : PkgI3.AbVar K) :
    ∃ 𝒩 : ReductSplit.GroupModelO A O, 𝒩.IsNeronModel :=
  ReductSplit.exists_neron_groupModel neronSchemeModelExistsDVR_proof O A

end SZ34Direct
