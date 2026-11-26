# rc-hcm-v21g-fixup results log

## Setup
- merge-base check: 94cd18fe ancestor of 796582ac: OK; GoodRowWire/Assembly.lean and SamePlace.lean present at 796582ac: OK.
- merged 796582ac into wip/rc-hcm-v21g (commit 641c9eccc).

## Item 1 (O threading)
- RC/GoodRowWire/Assembly.lean: binder `O : ∀ i, PMAdelic.OperatorComparison … (J i)` after `J`; `Reference … J O …`, `referenceComparisons … J O …`; `(fun i => adaptOperators (O i))` after each `adaptComparison` (actualRows, actualRowFamily, pointInputs, actualFamily); `(O := O)` in hCuspAt and oddStagedOfGoodRows. Locator :220 -> :222.
- build GoodRowWire.Assembly: OK (13747 jobs), oddStagedOfSamePlace typechecks; axioms propext, Classical.choice, Quot.sound.

## Item 2 (reach premises; order lemma without hCor)
- VoightCandidates: representations IsNonconstant, IsSeparableMor (generic stalks), IsSeparableIsogeny, SeparableReach; lemmas exists_ne_of_dim_eq_one, isNonconstant_id, isSeparableMor_id (stalkMap_id + isSeparable_self), isSeparableIsogeny_id.
- VoightThm4232Etale: reach premises for E, E′ inserted; VoightCor4237: reach premise inserted; conclusions unchanged.
- SeparableIsogenyExists restated with IsSeparableIsogeny; separableReach_of_separableIsogenyExists.
- nonempty_enhancedIso_of_translate takes rX rY; levelDeuringClass_injective takes hR : SeparableReach E₀.
- Order lemma (non-fallback branch): exists_algEquiv_extend (Basis.constr on SE.full.ratBasis, mult on basis pairs, AlgEquiv.ofBijective), exists_endRight_eq_of_mem_rightRing (frame of E, transportOrder, maximality). mem_rightRing_iff_mem_mirror_leftRing moved to LevelOrderLemma. hCor dropped from 6 declarations; exists_endRight_eq_level gains hT hV hq; stated at a = -1, b = -q.
- Build fixes: isSeparableMor_id first try (rw Over.id_left inside algebraMap) failed + whnf timeout; fixed by generalizing f = 𝟙 then rw stalkMap_id. extendOfIsLattice_apply needs Module. prefix and a letI IsLattice instance.
- build LevelDeuringInjective: OK (13568 jobs).
