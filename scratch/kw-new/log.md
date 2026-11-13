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
