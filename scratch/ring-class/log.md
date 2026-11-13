# ring-class results log

## 2026-11-13 06:41 start (fresh; no earlier log)

### Vendoring Tau Ceti's ring class fields (VERIFIED, compiled)
- Closure of TauCeti.NumberTheory.ClassFieldTheory.ClassFields.RingClass.Field at ~/tc-nov01: 961 modules,
  24 not yet vendored (scratch/ring-class/vendor-new.txt).
- Vendored 22 from commit 97a5b235; KummerLayer and Orders/Quadratic/Conductor from 5a01f5fe (their nov01
  versions use `le_fixedField_iff_le_fixingSubgroup`, `Ideal.absNorm_eq_natCard`, absent from our Mathlib).
- nov01-only declarations needed, backported (9 new Backport/ files, see NOTICE): idealClassLift (RayClass/Integral),
  normal_globalNormSubgroup + index_globalGroundOrderIso (NormSubgroup), auxiliaryKummerIdeleClassSubgroup_le_of_raySubgroup_le
  (Kummer/Ideles), levelNorm_top_ideleClassLevelEquiv + levelNorm_ideleClassLevelEquiv (IdeleClass/Norm),
  coe_norm_eq_prod_quotient_out (AbsoluteGaloisGroup/Norm), exists_le_hasEnoughRootsOfUnity (FiniteExtension),
  the adele/idele norm transfer (Adeles/Norm/Galois, Ideles/Norm/Galois), IdeleClassGroup.instIsMulCommutative (Ideles/Basic).
- Five vendored files modified (imports only, noted): Orders/RayClass, GlobalExistence/{AbelianLayer,Correspondence,Existence,Kummer}.
- `lake build ZInQKernel.Contrib.TauCeti.NumberTheory.ClassFieldTheory.ClassFields.RingClass.Field`: success, no sorry (07:00).
- diffcheck2: MOD-UNNOTED 0, NOTE-ONLY 0.
