# stab-clash results log

- 21:20 VERIFIED (diff): vendored TauCeti/GroupTheory/GroupAction/Stabilizer/Basic.lean (97a5b235) contains
  every declaration of Stabilizer.lean (5a01f5fe) with identical statement text, plus MonoidHom.stabilizerMap
  (+3 lemmas), TauCeti.mem_stabilizer_set_iff_mapsTo, TauCeti.conj_smul_eq_conj_smul_of_smul_eq,
  TauCeti.natCard_smul_mem_eq_natCard_mul_natCard_stabilizer. Stabilizer/Basic does not import Stabilizer.
- 21:20 FIX: Stabilizer.lean reduced to `public import ...Stabilizer.Basic` (+ Modified line, docstring);
  NOTICE modified list updated. diffcheck2: MOD-UNNOTED 0, NOTE-ONLY 0 (VERIFIED).
- 21:20 VERIFIED (lake build): Stabilizer, DoubleCoset.Orbits, TateCohomology.Permutation.Basic (its only
  importers) build.
- static scan (scratch/stab-clash/dupscan.py, dupscan-before.txt): 71 duplicated names in 8 file pairs:
  FDRep vs FDRep/Basic (26), Stabilizer vs Stabilizer/Basic (21), UnitFiltration/Pow vs Pow/Basic (9),
  Backport vs vendored Global/PrescribedInvariant (6), Backport vs vendored Global/Kummer/Norm (5),
  FinitePlace vs FinitePlace/Basic (2), Cyclic/Basic vs Cyclic/PowMonoidHom (1),
  Backport vs vendored Global/Kummer/AuxiliaryPlaces (1).
