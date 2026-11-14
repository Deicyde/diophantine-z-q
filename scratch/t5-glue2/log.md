# t5-glue2 results log

## Setup
- `.lake/build`, `lean/.lake/build` reflink-copied from ~/dzq-wt/t5-glue (built from ~/dzq-check2 13fe43c4;
  vs this base aef254ec only `ZInQKernel/OneProof/H/*`, `OneProof/Main.lean` differ, not imported here).

## Step 1: AbsArtin.lean — `AbsArtinSurjectiveQNeg` PROVED — COMPILED, 0 errors (~9 s after import cache)
- Verbatim copies of t5-glue `AbsArtinSurjective`, `AbsArtinSurjectiveQNeg` (text compared by script: identical).
- `absArtinSurjective_of_noReal : (∀ w : InfinitePlace K, ¬ w.IsReal) → AbsArtinSurjective K` (any number field).
  Ingredients (all Tau Ceti/Mathlib, VERIFIED read + compiled):
  `ClassFormation.abelianizationRestrict_absoluteArtinMap_eq_zero_iff` + `mem_globalNormSubgroup_iff` (kernel of
  the finite projection = global norm subgroup), `isOpen_globalNormSubgroup`, `surjective_artinMap`,
  `exists_raySubgroup_le_of_isOpen`, `finiteIndex_raySubgroup`, `mem_ideleCongruenceSubgroup_one_iff`,
  `FiniteAdeleRing.isCompact_integralAdeles` + `Submonoid.units_isCompact` (Ô^× compact),
  `LayerRefinement.quotientHom_abelianizationRestrict` (directedness),
  `NormalLayer.eq_of_forall_abelianizationRestrict_eq`, `IsCompact.inter_iInter_nonempty`.
- `qneg_not_isReal` (φ(ω)² = −m < 0), **`absArtinSurjectiveQNeg : AbsArtinSurjectiveQNeg`**.
- #print axioms: both [propext, Classical.choice, Quot.sound].
