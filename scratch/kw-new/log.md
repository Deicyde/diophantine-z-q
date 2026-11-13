# kw-new results log

## Setup (2026-11-13 03:05-03:15 PST)
- Vendored the 44 nov01 modules (`tcport.py ~/tc-nov01 … kw-new-nov01.txt`), commit fdf14084. VERIFIED.
- Merged local branch `wip/tc-port` (f22bb604: port1 + 714 oct16 modules of kw-rest + 7 extra);
  origin/wip/tc-port did not exist yet. Copied tc-port's built `.lake/build` TauCeti artifacts
  (identical sources; lake accepted them: `lake build …Algebra.AddCircle` no-op). VERIFIED.
- Local import closure of the vendored KroneckerWeber module (nov01 file + oct16 files): 841
  modules. Only 11 of the 44 nov01 modules are in it: ClassFields.{KroneckerWeber,RaySubgroup},
  Global.AdmissibleModulus.{Basic,Ramification,Reciprocity}, Global.ClassFormation,
  Global.LocalArtin.{Compatibility,Frobenius}, Global.Reciprocity, GlobalExistence.NormLimitation,
  Local.Conductor.Basic. The other 33 are only imported (at nov01) by modules we vendor at oct16.
  VERIFIED (scratch/kw-new/tools/closure_local.py).
- Textual scan (scratch/kw-new/tools/analyze.py): 890 declarations were added between oct16 and
  nov01 to the 905 shared modules; 7 declarations of nov01 modules already exist in oct16 modules
  (moved): TauCeti.groupNorm{,_apply,_smul,Hom,Hom_apply} (oct16 in GroupCohomology.Cocycle,
  nov01 in GroupAction.Norm), IsCyclic.mem_range_powMonoidHom_iff (oct16 Cyclic.Basic, nov01
  Cyclic.PowMonoidHom), NumberField.InfinitePlace.exists_completionNormalizedAbsValue_eq (oct16
  InfinitePlace.Completion.Basic, nov01 Completion.Real). VERIFIED (text).

## Build batch 1: 28 nov01 modules whose imports were built (sequential lake build)
- Build unmodified (22): Algebra.Exact.Pi, Algebra.Order.Floor.Div, GroupTheory.Index.Map,
  RingTheory.LocalRing.Localization, RingTheory.Subring.Torsion,
  Topology.Algebra.ValuativeRel.Nonarchimedean, NumberField.RingOfIntegers.{Basic,Norm},
  RepresentationTheory.FreeOfBasis, LinearAlgebra.End.Basic, Topology.Algebra.Group.Shear,
  Algebra.Homology.ShortComplex.FunctorEquivalence, Analysis.Normed.Ring.Units,
  CategoryTheory.Linear.Endomorphism, Algebra.Colimit.DirectLimit,
  RingTheory.DedekindDomain.FiniteAdeleRing.Away, NumberField.FinitePlace.Basic,
  RingTheory.ZMod.UnitsTwoPow, LocalField.UnitFiltration.Pow.Basic,
  Algebra.Module.Submodule.OrbitRelQuotient, RepresentationTheory.FDRep.Basic,
  GroupAction.Stabilizer.Basic. VERIFIED (compiled).
- Fail (6): GroupAction.Norm, Cyclic.Norm (missing TauCeti.sum_range_orderOf_eq_sum,
  Finset.sum_range_mul_eq_sum_sum); Cyclic.PowMonoidHom (missing TauCeti.pow_pow_div_gcd_eq_one,
  TauCeti.range_powMonoidHom_gcd); InfinitePlace.Completion.Real (duplicate declaration);
  Cyclotomic.PrimePow (missing Polynomial.monic_cyclotomic_comp_X_add_one,
  IsDistinguishedAt.natCast_dvd_pow_of_aeval_eq_zero); Star.Completion (heartbeat timeout in
  `fun_prop`, line 79). VERIFIED (compiled).

## KW closure build 1 (03:12)
- Several oct16 modules fail at our Mathlib pin (tc-port's files; not edited here):
  GroupCohomology.PrimeIndex, TateCohomology.TrivialityCriterion, Formation.InvariantKernel
  (`Sylow.isPGroup` absent), Profinite.Generation, ContCohomology.Coinduced.Discrete. VERIFIED.

## Backport approach (03:15-03:45)
- Helpers: `ZInQKernel/Contrib/TauCeti/Backport/<oct16 module path>.lean`, each `public import`s the
  oct16 module and adds the declarations the nov01 modules use that were added to it after
  5a01f5fe (generated from the nov01 source by scratch/kw-new/tools/genbackport.py, fixed by hand).
- Findings (VERIFIED, compiled):
  * Helper imports into nov01 modules must be `public import`: with a private `import`, a helper
    declaration is invisible in the statement of a public theorem (Lean module system), and dot
    notation silently falls back to a parent-structure declaration (e.g.
    `ContinuousMonoidHom.subgroupComap` -> `MonoidHom.subgroupComap`).
  * `rfl` proofs about oct16 definitions fail across modules (bodies not exposed): fixed with
    `import all <oct16 module>` (Kummer.Ideles, Mackey.Basic) or an oct16 `_def` lemma
    (LiftingObstruction, RayClass.Rat).
  * Three shared modules were reworked after oct16 and are imported in the KW closure only by
    nov01 modules, so their whole nov01 text is vendored as a *replacement* under Backport/ (same
    declaration names; must not be imported together with the oct16 version):
    Global.PrescribedInvariant (generalized from layers V ◁ G_K to all normal layers),
    Global.Kummer.Norm, Global.Kummer.AuxiliaryPlaces (strengthened conclusions).
  * The oct16 second inequality (Global.IdeleClass.SecondInequality) is conditional on the Kummer
    index bound; at nov01 it is discharged by the new module Global.Kummer.Index, which is
    therefore in the closure (via the SecondInequality helper).
  * Mathlib lemma `Polynomial.X_pow_sub_X_ne_zero` (later Mathlib) backported in
    Backport/Mathlib/Polynomial.lean with a new proof.
  * Fixes inside nov01 files: PrescribedInvariant line ~978 (`by simpa using hu` for a
    `Subgroup.toAddSubgroup` membership).

## KW BUILD SUCCESS (~03:41)
- `lake build ZInQKernel.Contrib.TauCeti.NumberTheory.ClassFieldTheory.ClassFields.KroneckerWeber`:
  "Build completed successfully (5260 jobs)". VERIFIED.
- Coordination: duplicate sessions kw-new-9f (stopped; its merges of origin/main and
  origin/wip/tc-port and its Leaves.lean rewrite kept) and kw-new-e3 (standing by).

## Bridge (03:41-03:44)
- ZInQKernel/Contrib/KroneckerWeber/Leaves.lean (rewritten by duplicate session kw-new-9f to use
  the importable ZInQKernel.HDecomp.Textbook.KroneckerWeberUse from fork main c303557d; compiled
  here): hSynKroneckerWeber : HSynKroneckerWeber, glueKroneckerWeber : GlueKroneckerWeber,
  tSkolemKW_kroneckerWeber : TSkolemKW.KW.KroneckerWeber, kroneckerWeberCyclic :
  TSkolemKW.KW.KroneckerWeberCyclic, dirichletCharacter_of_openKer, dirichletCharacter_of_continuous,
  ker_ge_of_openKer, eq_of_agree_on_roots. All: [propext, Classical.choice, Quot.sound]. VERIFIED
  (scratch/kw-new/Axioms.lean -> axioms-output.txt).
- HSynKroneckerWeber / GlueKroneckerWeber texts checked verbatim against
  scratch/h-decomposition/Leaves.lean:21206 and scratch/glue-assembly/Leaves.lean:19. VERIFIED.
- ZInQKernel/Contrib/KroneckerWeber/DirichletCharacter.lean (my earlier draft) removed: the
  Textbook module provides the same declarations.

## All 44 nov01 modules build (03:44)
- Last fixes: Backport AbsoluteGaloisGroup.Congr helper removed (declarations already in oct16);
  Completion.Real omits its copy of exists_completionNormalizedAbsValue_eq (in oct16
  Completion.Basic); Cyclotomic.Basic helper gains natDegree_cyclotomic_comp_X_add_one;
  Star.Completion `fun_prop` replaced by explicit continuity. VERIFIED (buildlist, 44/44 rc=0).
- Co-import: 5 moved-file modules clash with their oct16 predecessors (Stabilizer.Basic,
  Cyclic.PowMonoidHom, UnitFiltration.Pow.Basic, FinitePlace.Basic, FDRep.Basic); the other 39 load
  together with the bridge (scratch/kw-new/AllNov01.lean compiles). VERIFIED.
