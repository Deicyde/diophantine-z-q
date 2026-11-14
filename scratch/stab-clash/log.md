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
- 21:22 VERIFIED (diff): FDRep/Basic, UnitFiltration/Pow/Basic, NumberField/FinitePlace/Basic (all 97a5b235)
  contain every line of the corresponding 5a01f5fe FDRep, UnitFiltration/Pow, FinitePlace (Pow: one proof
  differs); none imports its 5a01f5fe counterpart. Fix: the 5a01f5fe file re-exports the 97a5b235 one.
- 21:22 VERIFIED (grep): vendored 5a01f5fe Global/PrescribedInvariant, Global/Kummer/Norm,
  Global/Kummer/AuxiliaryPlaces are imported by no Lean file of ZInQKernel; their Backport/ replacements
  (whole 97a5b235 modules, some statements generalized) declare every name they declare. Fix: the 5a01f5fe
  file re-exports the Backport replacement (its 6+5+1 old statements are dropped, unused).
- 21:23 IsCyclic.mem_range_powMonoidHom_iff: Cyclic/Basic (5a01f5fe, hyp n ∣ card) vs Cyclic/PowMonoidHom
  (97a5b235, gcd form). Only user: FieldTheory/Finite/EulerCriterion. Fix as Tau Ceti did at 97a5b235:
  removed from Cyclic/Basic; EulerCriterion imports Cyclic.PowMonoidHom and uses the 97a5b235 proof lines.
- second scan (names.py incl. instances, no comment filter; dupscan2-before.txt): no further real
  duplicates (remaining hits are docstring words: of, map, group, field, ...).
- diffcheck2 after all edits: MOD-UNNOTED 0, NOTE-ONLY 0, MOD-NOTED 45 (VERIFIED).
- 21:25 AllContrib.lean (2064 imports from git ls-files 'ZInQKernel/Contrib/*.lean'); build started.
- 22:47 (resumed run, other host) VERIFIED: `lake build ZInQKernel.Contrib.AllContrib` succeeds
  ("Build completed successfully (11974 jobs)", 0 errors). AllContrib's 2064 imports are identical to
  the git ls-files list (VERIFIED, diff).
- 22:50 diffcheck2.py is not available on this host (~/dzq-runs/tc and ~/tc-* missing). Substitute
  check (VERIFIED): all 9 files changed since 998b4f79 have one stab-clash Modified line at line 7
  (right under the provenance line) and one "(task stab-clash" NOTICE entry.
- VERIFIED (git grep): no ZInQKernel module outside Contrib imports an edited module; only
  scratch/tc-port/AllKW.lean and scratch/t40-clash/AllContrib.lean do.
