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

## ~07:12 statements file
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

## ~07:25 proofs, round 1 (VERIFIED, `lake build ZInQKernel.Contrib.TYZGenus.RingClass` success)
- Vendored (nov01) RayClassField, RayClass/Narrow/Basic, NarrowClassGroup/{Basic,TotallyComplex}; Backport
  ClassFieldTheory/ClassField (classField_fixingOpenNormalSubgroup with a rewritten proof: `classField` does not unfold
  outside its module); RayClassField.lean imports it (noted). diffcheck2: MOD-UNNOTED 0, NOTE-ONLY 0.
- Proved: relfinrank_genusField (= #Pic²), finrank_genusField (= #Pic[2]), finrank_genusField_mul, finrankGenusField,
  finrankH4, gCl_eq_card_picSquares (by rfl: ClassGroup (𝓞 K) and Pic of maximalNumberFieldOrder are defeq),
  ker_le_ker_maximal, ringClassField_maximal_le (H_K ≤ ring class field of any order), 
  ringClassField_maximal_eq_hilbertClassField, unit_eq (units of 𝓞_{ℚ(√−d)} are ±1 for d ≡ 5 mod 8, via
  d m² + k² = 4d mod 8/32), alphaIdeal_mem, sigmaClass_sq, not_mem_O4, sigmaClass_ne_one, orderOf_sigmaClass = 2.
  #print axioms orderOf_sigmaClass: [propext, Classical.choice, Quot.sound].

## ~07:30 proofs, round 2 (VERIFIED, lake build success)
- Hprime_le_H4, relfinrank_Hprime ([H_{d,4} : H'_d] = 2 for d ≡ 5 mod 8), sigmaClassOrderTwo, hilbertLeH4,
  gClEqPicSquares, gCl_eq_relfinrank, gClEqRelfinrank, finrank_hilbertField (= classNumber, via vendored
  finrank_hilbertClassField), finrank_genusField_eq ([G_n : K_n] = 2^{#ramSet n − 1}, odd squarefree n > 1, from
  RouteK.Redei.card_ker_sq_eq), picSquares_eq_iInf_ker_chi, genusField_eq_fixedField_chi (genus field = field cut
  out by the genus characters RouteK.Redei.chi), gNat_eq_relfinrank, gRingClass, gNat_eq_gRingClass (function
  equality), gCl_eq_gRingClass, T5aCl_eq_gRingClass, T5bCl_eq_gRingClass, GenusData.beta_seven_ringClass,
  GenusData.beta_five_ringClass.

## ~07:39 proofs, round 3 (VERIFIED, lake build success)
- ideleClassArtinMap_restrict (Tau Ceti's idele-class Artin maps commute with restriction between abelian
  subfields of Kˢ; from globalArtinMap_comp + of_ideleClassArtinMap), picToMax O : Pic O →* Cl(K) (= Q_max ∘ Q_O⁻¹),
  picToMax_ringClassIdeleQuotient, picToMax_surjective, picToMax_picClass_span (principal ideals ↦ 1),
  picToMax_sigmaClass, restrictNormalHom_inclusion_apply, restrict_ringClassArtinEquiv (Artin symbol in ring class
  field of O restricted to H_K = Artin symbol of picToMax c), ringClassArtinEquiv_apply_of_picToMax_eq_one,
  mem_lift_fixedField_zpowers, hilbertField_le_Hprime (H_d ⊆ H'_d; needs maxRecDepth 10000).

(Note: earlier headings were mis-estimated clock times; corrected to `date` readings, ±5 min.)

## 08:00–08:35 round 4 (VERIFIED, `lake build ZInQKernel.Contrib.TYZGenus.RingClassBridge` success)
- Merged origin/main, origin/wip/cm-points, origin/wip/x0-32 (no conflicts); Package builds.
- cm-points' report asks ring-class to prove `Package.HprimeNormal` and `Package.IInH4`.
- New ZInQKernel/Contrib/TYZGenus/RingClassGalois.lean (from scratch G1/G2): splitSet, Bauer's theorem
  `le_of_splitSet_diff_subset` (Tau Ceti Chebotarev), splitting law `mem_splitSet_iff` (via
  `isArithFrobAt_ringClassArtinEquiv_picClass`), `picClass_conj` (conjugation inverts Pic(O_{d,4})),
  `normal_ringSubfield` (every E_S ⊆ H_{d,4}, S ≤ Pic, normal over ℚ), `normal_Hprime`, `normal_H4`,
  `normal_Hprimebar`, `normal_H4bar` (all d), `adjI` = K(√−1), `isUnramifiedAt_of_two_notMem`,
  `eq_one_of_isArithFrobAt`, `mem_splitSet_adjI`, `norm_of_mem_O4` (N(a+4y) = a² + 4c),
  `adjI_le_H4` (K_d(√−1) ⊆ H_{d,4}, every d ≥ 1), `iQ_mem_H4bar`.
- Pitfall: a `set w := …` inside the normality proof made later uses of `τ` time out at isDefEq
  (200000 heartbeats); splitting the two cases into separate lemmas fixed it.
- New ZInQKernel/Contrib/TYZGenus/RingClassBridge.lean: `hprimeNormal : HprimeNormal`, `iInH4 : IInH4`,
  `tyzThm35ReadingA_of_cmLeaves_ringClass` (cm-points' finest main theorem minus these two hypotheses).
- #print axioms (scratch/ring-class/AuditBridge.lean): all [propext, Classical.choice, Quot.sound].

## ~08:50 round 5 (VERIFIED, lake build RingClassBridge success; axioms standard three)
- ConjInverse/Normality sections generalized from O4 d to every `conductorOrder (QNeg d) f`.
- Ring class fields by discriminant: `ringClassFieldBar m f`, `normal_ringClassFieldBar` (every order
  ℤ + f𝓞_K of an imaginary quadratic field: ring class field normal over ℚ), `sqfPart` (squarefree part,
  `squarefree_eq_of_sq_mul_eq` uniqueness), `condD` (conductor), `condD_spec` (|D| = f²|d_K| for D < 0,
  D ≡ 0,1 mod 4), `ringClassFieldD D`, `normal_ringClassFieldD`, `ringClassFieldD_tyz`
  (ringClassFieldD (−64n) = H4bar n for squarefree n ≡ 5 mod 8).
- Bridge: `cmFieldTYZ_of_ringClassD` (CM.CMFieldOfDefinition ringClassFieldD → CMFieldOfDefinitionTYZ),
  `tyzThm35ReadingA_of_cmLeaves_ringClassD`, `normalFields_HHprime'`.
- ~09:05 embedding independence (VERIFIED, build success): `map_eq_map_of_normal`, `ringClassFieldBar_eq_map`,
  `H4bar_eq_map'`, `Hprimebar_eq_map'` (the images in ℚ̄ of ring class fields, H_{d,4}, H'_d do not depend
  on the ℚ-embedding K_dˢ → ℚ̄).

## ~09:35 round 6 (VERIFIED, `lake build ZInQKernel.Contrib.TYZGenus.RingClassTwo` success; axioms standard)
- New ZInQKernel/Contrib/TYZGenus/RingClassTwo.lean (from scratch G3): K(√a) machinery (`sqrtK`, `adjSqrt`,
  `sqrtO`, `isUnramifiedAt_sqrt` for Q ∌ 2a, `smul_sqrtO_eq_iff` Euler-criterion Frobenius,
  `mem_splitSet_adjSqrt_iff`: 𝔭 ∌ 2a splits in K(√a) ⇔ a square mod 𝔭), `even_two_re` (d ≡ 1 mod 4 ⇒ Tr 𝓞 ⊆ 2ℤ),
  `norm_of_mem_O4_mod8`, `adjSqrt_two_le_H4` (√2 ∈ H_{d,4}, d ≡ 1 mod 4), `splitSet_anti`, `normZ_alpha`
  (N(3+2√−d) = 9+4d), `exists_prime_picClass_eq` (Chebotarev: every Pic(O_{d,4}) class has primes outside any
  finite set), `not_adjSqrt_two_le_Hprime` (√2 ∉ H'_d, d ≡ 5 mod 8), `Hprime_sup_sqrt_two`
  (H'_d ⊔ K_d(√2) = H_{d,4}: TYZ Prop 3.2(1)'s first assertion, a faithfulness check of `Hprime`).
