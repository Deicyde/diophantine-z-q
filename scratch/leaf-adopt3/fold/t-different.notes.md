# fold notes: t-different

Fragment: `scratch/leaf-adopt3/fold/t-different.lean` (1794 lines, `section TDifferentSec ... end
TDifferentSec`, no imports). Source: `scratch/t-different/All.lean` (the deduplicated all-in-one
file; reported to compile in 52 s on Mathlib only).

## Bundle fields / glue rows
- `HSyn.TextbookLeaves.t22a : PkgI6.HerbrandQuotient` and `t22b : PkgI6.HerbrandTransitivity` are
  now proved; the fields can be dropped or filled in.
- `PkgI6.HilbertDifferentFormula` (I6.7) and `PkgI6.DifferentBound` (I6.6) are proved. The bundle
  fields `t20`/`t21` are the *global* forms `GlueConductor.HilbertDifferentFormula` /
  `GlueConductor.SerreDifferentBound`. Those are NOT proved; this fragment does not change them
  (unless the integrator switches t20/t21 to the local forms, as the report suggests).

## Bridging theorems (types exactly the Leaves.lean Props; the task's own theorems)
- `PkgI6.hilbertDifferentFormula : PkgI6.HilbertDifferentFormula`
- `PkgI6.differentBound : PkgI6.DifferentBound`
- `PkgI6.herbrandQuotient : PkgI6.HerbrandQuotient`
- `PkgI6.herbrandTransitivity : PkgI6.HerbrandTransitivity`
These are stated inside `namespace PkgI6`, so after deleting the task's copies, `HilbertDifferentFormula`
etc. resolve to the Leaves.lean defs. No extra alias theorems added.

## New Props (in the fragment; intermediate, not leaves, each proved)
- `PkgI6.MonogenicDVR` (B = A[x], Serre III §6 Prop. 12): proved by `PkgI6.monogenicDVR`.
- `PkgI6.TraceContainsRamificationIdx` (e ∈ Tr_{B/A}(B)): proved by
  `PkgI6.traceContainsRamificationIdx`.

## Deleted as duplicates (character-identical to Leaves.lean, checked with python)
Whole `section Ramification` of All.lean lines 17-54 = Leaves.lean 5036-5073 (diff empty):
`PkgI6.lowerRam`, `PkgI6.mem_lowerRam`, `PkgI6.lowerRamR`, `PkgI6.herbrandPhi`, `PkgI6.upperRam`,
`PkgI6.lowerRam_tower`. Leaf defs (code from `def` to the end of the block substring-identical to
Leaves.lean): `PkgI6.HilbertDifferentFormula` (Leaves 5099), `PkgI6.DifferentBound` (5087),
`PkgI6.HerbrandQuotient` (5112), `PkgI6.HerbrandTransitivity` (5129). The only differences are
docstrings: All.lean's docstrings for HilbertDifferentFormula/DifferentBound read "Verbatim copy of
..."; the code is identical. Context matches too: Leaves' `LocalLeaves` section has the same `open
IsLocalRing` and `attribute [local instance] FractionRing.liftAlgebra
FractionRing.isScalarTower_liftAlgebra` as All.lean's final `namespace PkgI6` block.
No kernel declarations needed (Mathlib only).

## Name clashes (checked)
- None of the new `PkgI6` names (`MonogenicDVR`, `hilbertDifferentFormula_of_monogenicDVR`,
  `monogenicDVR`, `hilbertDifferentFormula_of_dvr`, `hilbertDifferentFormula`,
  `TraceContainsRamificationIdx`, `differentBound_of_trace`, `traceContainsRamificationIdx`,
  `differentBound`, `herbrandQuotient`, `herbrandTransitivity`) appears anywhere in Leaves.lean.
- Namespace `TDifferent` does not occur in Leaves.lean.
- `TDifferent` opens `PkgI6` (All.lean line 1246). None of Leaves' other 48 `PkgI6.*` short names
  (`hInt`, `phi_zero`, `g0_pos`, `loc`, `Z2`, `codimInv`, ...) appears as an identifier in the
  fragment after that `open`, or in the final `namespace PkgI6` block. So no new ambiguity or
  shadowing.
- Leaves.lean has no top-level `open`. No declarations in `IsLocalRing.`/`Polynomial.`/
  `MeasureTheory.`/`Set.` namespaces, and no `_root_` declarations in those namespaces.

## Dropped
`#print axioms PkgI6.hilbertDifferentFormula`, `... PkgI6.differentBound`,
`... PkgI6.herbrandQuotient`, `... PkgI6.herbrandTransitivity` (the report says: propext,
Classical.choice, Quot.sound only).

## Final top-level declarations defined by the fragment
`TDifferent.`: integral_indicator_Iic, filtR, phiF, filtR_zero, card_eq_sum, phiF_formula, phiF_ge,
phiF_mono, phiF_zero, fiber_sum, coset_min, phiF_trans, ceil_toNat_lt_iff, phiExpl,
phiF_eq_phiExpl, phiF_strictMono, phiF_neg_one, exists_phiF_eq, sInf_phiF, sInf_phiF_of_le, nQ_eq,
herbrand_lemma, upper_map, mem_inertia_iff_of_adjoin, span_eq_maximalIdeal_pow,
maximalIdeal_pow_le_iff, maximalIdeal_eq_span_of_mem_of_notMem, exists_adjoin_eq_top,
map_maximalIdeal_eq_pow, isGaloisGroup_algEquiv, finite_algEquiv, resHom, resHom_apply,
resHom_surjective, resHom_eq_one_iff, isGaloisGroup_tower, minpoly_map_eq_prod,
adjoin_tower_eq_top, finite_tower, card_tower_eq, span_sub_eq_span_prod, card_lowerRam_zero,
herbrandPhi_eq_phiF, tower_data, herbrand_trans, herbrand_quotient, card_sub_one_eq,
sum_card_sub_one, adjoin_fractionRing_eq_top, aeval_derivative_minpoly_eq_prod,
hilbertDifferentFormula_of_adjoin_eq_top, repr_mem_of_mem_smul_top, exists_limit,
exists_root_of_residue, exists_intTrace_eq_ramificationIdx.
`PkgI6.`: MonogenicDVR, hilbertDifferentFormula_of_monogenicDVR, monogenicDVR,
hilbertDifferentFormula_of_dvr, hilbertDifferentFormula, TraceContainsRamificationIdx,
differentBound_of_trace, traceContainsRamificationIdx, differentBound, herbrandQuotient,
herbrandTransitivity.

## Expected trouble spots
- `TDifferent.exists_intTrace_eq_ramificationIdx` carries `set_option maxHeartbeats 1000000`,
  `synthInstance.maxHeartbeats 400000` and `linter.deprecated false` (as `... in`). It uses
  `Ideal.ramificationIdx_mul_inertiaDeg_of_isLocalRing`, which is deprecated but present in v4.35.
- Leaves.lean adds global instances and 14 global `@[simp]` lemmas before the insertion point.
  None looks related to DVRs, ideals or ramification, but the `simp` calls can only be checked by
  compiling.
- `TDifferent.herbrandPhi_eq_phiF` is `rfl` through `PkgI6.herbrandPhi`/`lowerRamR`. The defs are
  identical, so it should still go through.
