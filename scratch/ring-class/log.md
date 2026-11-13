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

## 08:00 proofs, round 1 (VERIFIED, `lake build ZInQKernel.Contrib.TYZGenus.RingClass` success)
- Vendored (nov01) RayClassField, RayClass/Narrow/Basic, NarrowClassGroup/{Basic,TotallyComplex}; Backport
  ClassFieldTheory/ClassField (classField_fixingOpenNormalSubgroup with a rewritten proof: `classField` does not unfold
  outside its module); RayClassField.lean imports it (noted). diffcheck2: MOD-UNNOTED 0, NOTE-ONLY 0.
- Proved: relfinrank_genusField (= #Pic²), finrank_genusField (= #Pic[2]), finrank_genusField_mul, finrankGenusField,
  finrankH4, gCl_eq_card_picSquares (by rfl: ClassGroup (𝓞 K) and Pic of maximalNumberFieldOrder are defeq),
  ker_le_ker_maximal, ringClassField_maximal_le (H_K ≤ ring class field of any order), 
  ringClassField_maximal_eq_hilbertClassField, unit_eq (units of 𝓞_{ℚ(√−d)} are ±1 for d ≡ 5 mod 8, via
  d m² + k² = 4d mod 8/32), alphaIdeal_mem, sigmaClass_sq, not_mem_O4, sigmaClass_ne_one, orderOf_sigmaClass = 2.
  #print axioms orderOf_sigmaClass: [propext, Classical.choice, Quot.sound].

## 08:25 proofs, round 2 (VERIFIED, lake build success)
- Hprime_le_H4, relfinrank_Hprime ([H_{d,4} : H'_d] = 2 for d ≡ 5 mod 8), sigmaClassOrderTwo, hilbertLeH4,
  gClEqPicSquares, gCl_eq_relfinrank, gClEqRelfinrank, finrank_hilbertField (= classNumber, via vendored
  finrank_hilbertClassField), finrank_genusField_eq ([G_n : K_n] = 2^{#ramSet n − 1}, odd squarefree n > 1, from
  RouteK.Redei.card_ker_sq_eq), picSquares_eq_iInf_ker_chi, genusField_eq_fixedField_chi (genus field = field cut
  out by the genus characters RouteK.Redei.chi), gNat_eq_relfinrank, gRingClass, gNat_eq_gRingClass (function
  equality), gCl_eq_gRingClass, T5aCl_eq_gRingClass, T5bCl_eq_gRingClass, GenusData.beta_seven_ringClass,
  GenusData.beta_five_ringClass.
