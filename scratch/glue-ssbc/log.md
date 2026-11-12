# glue-ssbc results log

## Mathlib v4.35.0 search (VERIFIED, grep of .lake/packages/mathlib)
- 16 files mention `IsSemisimpleModule`/`IsSemisimpleRing`/`IsSemisimpleRepresentation`; none mentions
  `TensorProduct`. No base-change theorem for semisimple modules/rings/representations exists.
- Only perfect-field result: `Module.End.IsSemisimple` for single (commuting) endomorphisms
  (`Mathlib/LinearAlgebra/Semisimple.lean`), not applicable.
- Used: `IsArtinianRing.isSemisimpleRing_iff_jacobson`, `IsArtinianRing.isNilpotent_jacobson_bot`,
  `Ideal.jacobson_bot`, `IsSemisimpleRing.ideal_eq_span_idempotent`,
  `LinearMap.IsIdempotentElem.trace_eq_zero_iff` (char 0), `LinearMap.isNilpotent_trace_of_isNilpotent`,
  `LinearMap.trace_baseChange`, `LinearMap.baseChange_mul`, `Algebra.TensorProduct.basis(_repr_tmul)`,
  `Module.forall_dual_apply_eq_zero_iff`, `LinearMap.isSemisimpleModule_iff_of_bijective`,
  `isSemisimpleRepresentation_iff_isSemisimpleModule_asModule`, `asModuleEquiv_map_smul`.

## scratch/glue-ssbc/SSBC.lean (VERIFIED: compiles, no sorry; axioms propext, Classical.choice, Quot.sound)
- `TraceNondeg B` (def): trace form `tr_W(xy)` nondegenerate on a subalgebra `B ⊆ End_F W`.
- `isSemisimpleRing_of_traceNondeg`: fin-dim `W`, `TraceNondeg B` ⇒ `IsSemisimpleRing B`.
- `isSemisimpleRing_of_isSemisimpleModule`: `W` semisimple over `B ⊆ End W` ⇒ `IsSemisimpleRing B`.
- `traceNondeg_of_isSemisimpleModule` [CharZero F]: `W` semisimple over `B` ⇒ `TraceNondeg B`.
- `isSemisimpleRepresentation_iff_range`: `ρ` semisimple ⇔ `V` semisimple over `(asAlgebraHom ρ).range`.
- `baseChange_mem_range`, `traceNondeg_baseChange` (any field extension `E/k`, `V` fin-dim).
- `isSemisimpleRepresentation_baseChange` [CharZero k]: `ρ` semisimple ⇒ `repBaseChange E ρ` semisimple.
- `semisimpleBaseChange : SemisimpleBaseChange` (glue-I3-linalg's Prop, verbatim).
- compile: `lake env lean scratch/glue-ssbc/SSBC.lean` ~20 s.

## scratch/glue-ssbc/C2.lean (VERIFIED: compiles, no errors; axioms propext, Classical.choice, Quot.sound)
- = scratch/glue-I3-linalg/C2.lean + the SSBC lemmas inserted in namespace `GlueI3` after
  `def SemisimpleBaseChange` + `GlueI3.semisimpleBaseChange`.
- New: `PkgI3.C2_absolutelyIrreducible'`, `PkgI3.E1_exists_hom_ne_zero'` (no `hSS` argument),
  `GlueI3.absolutelyIrreducible_of_finrank_commOf_prod_le_four'`.
- Remaining hypotheses of C2'/E1' are I3's leaves only (FaltingsSemisimple, FaltingsTate,
  TateModuleFree, HomFreeFinite for C2'; the first three for E1') plus C2's data `e`, `he`.
- compile: ~25 s.

## Not done
- Positive characteristic / separable extensions: not proved (not needed: the project uses `ℚ_ℓ`).
