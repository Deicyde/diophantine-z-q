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

## Item 3 (reach from a prime model)
- New file RC/HCMV21/PrimeModelReach.lean: frO (absolute Frobenius over Spec F_q, Over condition from fr_naturality + fr_Spec_zmod), frO_naturality, frO_unit (toUnit_unique), frO_tensor (hom_ext + naturality), IsMonHom instance, primeFrob, primeFrobBC = bcHom; primeFrobBC_left_fst, primeFrobBC_pt (q-power map on k-points via fr_naturality + fr_Spec).
- Surjectivity: surjective_frO (base = id), surjective_primeFrobBC (MorphismProperty.overPullbackMap), surjective_pow_hom, surjective_tensorHom (MorphismProperty.pullbackMap; IsStableUnderComposition @Surjective.{0} not found by instance search, supplied from IsMultiplicative).
- isNonconstant_of_ne_zero via Mathlib ext_of_apply_eq (alg. closed k; no copy of the private overHom_ext_geometricPoints needed).
- Teeth (a) base_genericPoint_of_isNonconstant: chain closure{w} < closure{ζ} < univ in IrreducibleCloseds, length 2 > dim 1.
- Teeth (b) (primeFrobBC not IsSeparableMor): OPEN. Needs the stalk map of primeFrobBC at the generic point (absolute Frobenius = primeFrobBC ∘ (id × Fr_k), id × Fr_k an iso) and non-perfectness of the function field of a curve (a uniformizer at a closed point with DVR stalk is not a q-th power); DVR stalks need SmoothOfRelativeDimension 1 from Smooth + dim = 1. Large.
- SilvermanII212PrimeModel (candidate, UNVERIFIED, UNCERTAIN); isMonHom_of_frob_comp (factor lemma; A×A reduced via isReduced_of_flat_of_finite_irreducibleComponents on pullback.fst; ext_of_isDominant_of_isSeparated); isNonconstant_of_comp.
- separableReach_of_primeModel: proved. levelDeuringClass_injective_primeModel: proved.
- isSeparableIsogeny_of_isEtaleIsogeny: not attempted (open).
- builds: LevelDeuringInjective OK (13568), PrimeModelReach OK (13571), Odd.Statements OK (9058).

## Item 6
- builds (one at a time): LevelDeuringInjective OK, PrimeModelReach OK, Odd.Statements OK, GoodRowWire.Assembly OK (first attempt stopped by a 10-minute tool limit; rerun OK).
- Check.lean: 61 #print axioms, all [propext, Classical.choice, Quot.sound]; scratch/rc-hcm-v21g-fixup/axioms.txt.
