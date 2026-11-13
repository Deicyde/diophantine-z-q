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

## 07:20 statements file
- ZInQKernel/Contrib/TYZGenus/RingClass.lean: conductorOrder K f (ℤ + f𝓞_K, NumberFieldOrder), picSquares,
  picTwoTorsion, genusField O (fixed field of Pic(O)² in ringClassField O), sqrtNeg, O4 d, H4 d (H_{d,4}),
  hilbertField d, artin4, alpha d = 3+2√−d, sigmaClass d (class of σ_{1+2ϖ}, ϖ = 1+√−d), Hprime d (H'_d),
  embed d (K_dˢ → Qbar), H4bar, Hprimebar, Lni n (L_n(i)), HHprime n (ℍ'_n); target Props FinrankH4,
  GClEqPicSquares, GClEqRelfinrank, FinrankGenusField, HilbertLeH4, SigmaClassOrderTwo.
- `lake build ZInQKernel.Contrib.TYZGenus.RingClass`: success (VERIFIED, compiled). Note: `lake env lean` on this
  file fails with "unknown module prefix 'ZInQ'"; use lake build.
- Orders TYZ uses (from notes; Period7.tex not on host): d ≡ 5: ℤ[4√−d] = ℤ + 4𝓞_K, disc −64d (tyz-t1 §3.1,
  TYZ L1203–1205); d ≡ 7: maximal order, disc −d (tyz-t1 §3.1). H_{d,4}, H'_d: Prop 3.2(1) L1253–1258.
  ℍ'_n = L_n(i)·Π H'_{d₀} (L1320), L_n(i) = ℚ(i, √d : d|n) (L1322) — all as quoted in rv-nt-tyz/rv-pn-encoding.
