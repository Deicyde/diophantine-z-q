# prop-ts-glue results log

Task: reduce `PropTSRed.SpecNonMeeting`, `PropTSRed.KummerMeetGlue`, `PropTSRed.CoverModelOfHecke`
(scratch/prop-ts/PropTS.lean, merged from origin/wip/prop-ts) to smaller named Props or prove them.

## Step 1: file and first reduction, compiled
- `scratch/prop-ts-glue/PropTSGlue.lean` = `scratch/prop-ts/PropTS.lean` verbatim (prefix check:
  `check_identical.py` prints PREFIX IDENTICAL, VERIFIED) + `Appendix.lean.part` (namespace `PropTSGlue`).
- Build: `lake build ZInQKernel.HDecomp.QM.Pin ZInQKernel.HDecomp.Descent.B2Glue` OK; then
  `lake env lean scratch/prop-ts-glue/PropTSGlue.lean`: 0 errors, 6 linter warnings (prefix and
  appendix style), all `#print axioms` = [propext, Classical.choice, Quot.sound] (VERIFIED,
  compile_out.txt).
- Part A: `specNonMeeting_of_pieces : PurityGlobalDim2 → SNLocalData → SNHeightOne → SNSpecialize →
  SpecNonMeeting` (PurityGlobalDim2 copied verbatim from t-purity3, proved there). Proved helpers:
  `exists_secIdeal` (the maximal ideal (p, dX − a) as a kernel to 𝔽_p), `not_dvd_den_of_nonneg`,
  `regular_dim2_intPoly` (copied from prop-ts/ZXRegular.lean), `locAlg` (ℤ[X]_m → E).
- Part B: `kummerMeet_of_cases : KummerMeetFin → KummerMeetInf → KummerMeet`;
  `kummerMeetFin_of_pieces : KummerCompositum → KummerAbhyankarFin → KummerOtherBranchFin →
  KummerVerticalFin → KummerMeetFin` (the p-adic bookkeeping t − b = p^M u, c = u^{n−1},
  s₀ = p^{M/n} u is proved); `kummerMeetGlue_of_pieces`.
- Part C: `coverModelOfHecke_of_pieces : HeckeNormalization → HeckeDegree → HeckeBranch →
  HeckeNoVertRam → CoverModelOfHecke` (via prop-ts's `coverModel_of_N`).
- Part D: `propTSAll_of_pieces` (the composite).

## Step 2: the case at ∞, compiled
- Added `KummerAbhyankarInf`(+`Glue`), `KummerOtherBranchInf`, `KummerVerticalInf` and
  `kummerMeetInf_of_pieces` (t = p^{−M} u, c = u^{1−n}, s₀ = p^{M/n}/u, c/s₀^n = t; the meeting
  polynomial `b' s^n − c` has f(s₀) = c(b' − t)/t, a p-unit), `kummerMeetGlue_of_pieces'`
  (eight pieces, T2 only through the two Abhyankar steps). `propTSAll_of_pieces` now uses it.
- Compile: 0 errors; 14 PropTSGlue `#print axioms` lines, all standard (VERIFIED).

## Step 3: SNLocalData PROVED, compiled
- `isFractionRing_zx`: ℚ(X) is the fraction field of ℤ[X] (via `IsLocalization.integerNormalization_spec`).
- `snLocalData : SNLocalData`: for E/ℚ(X) finite and m maximal in ℤ[X], the integral closure of
  ℤ[X]_m in E is integrally closed (`integralClosure.isIntegrallyClosedOfFiniteExtension`),
  module-finite (`IsIntegralClosure.finite`; ℤ[X]_m Noetherian and normal via
  `isIntegrallyClosed_of_isLocalization`), and contains ℤ[X]_m (`IsFractionRing.injective`).
  Developed in `LocalData.lean` (Mathlib only; compiled, standard axioms), pasted into the appendix.
- `specNonMeeting_of_pieces' : PurityGlobalDim2 → SNHeightOne → SNSpecialize → SpecNonMeeting`.
- Compile of PropTSGlue.lean: 0 errors, 17 PropTSGlue axiom lines all standard (VERIFIED);
  prefix still IDENTICAL.

## Step 4: SNHeightOne reduced; horizontal arithmetic PROVED, compiled
- Proved (Mathlib only, developed in LocalData.lean, pasted): `exists_int_multiple` (N f ∈ ℤ[X]
  with p ∤ N for p-integral f), `C_notMem` (C n ∉ m if C p ∈ m, p ∤ n), `homog_mem`
  (d^k F ≡ Σ c_i a^i d^{k−i} mod any ideal ∋ dX − a), `notMem_of_val_zero` (F ∈ ℤ[X] with
  F(s₀) a p-unit is not in any proper m ∋ p, dX − a).
- New glue: `SNVertical` (the prime (p) of ℤ[X]_m is unramified; from NoVerticalRam and
  [E:ℚ(X)] < p), `SNHorizontalTransfer` (a ramified horizontal height-one prime P of ℤ[X]_m
  comes from a ramified prime Q of B with ℤ[X] ∩ Q ⊆ P; localization of primes, char 0).
- `snHeightOne_of_pieces : SNVertical → SNHorizontalTransfer → SNHeightOne` (compiled);
  `specNonMeeting_of_pieces'' : PurityGlobalDim2 → SNVertical → SNHorizontalTransfer →
  SNSpecialize → SpecNonMeeting`. Composite `propTSAll_of_pieces` updated.
- Compile: 0 errors, 21 PropTSGlue axiom lines all standard; prefix IDENTICAL (VERIFIED).

## Step 5: witness form of CoverModelOfHecke; sanity examples, compiled
- `functionFieldModel_transfer`, `coverModel_transfer` (along `Pin.SameTripleMor`, via prop-ts's
  `residueImage_comp_eq_of_pt`), `CoverModelWitness` (glue: one triple with R1fp, R1hecke, R2fp
  and a cover model), `coverModelOfHecke_of_witness : MobiusGlue → R1R2fp → CoverModelWitness →
  CoverModelOfHecke`.
- Sanity `example`s: the binders of SNSpecialize, SNVertical, SNHorizontalTransfer,
  KummerCompositum, KummerAbhyankarFin, KummerOtherBranchFin, KummerVerticalFin accept the
  genuine `RatFunc ℚ` (elaborates).
- Compile: 0 errors, 24 PropTSGlue axiom lines all standard; prefix IDENTICAL (VERIFIED).
- Independent review agent launched (read-only, no Lean) on the truth of the open Props.

## Step 6a: purity inlined, compiled
- `PropTSGlue.lean` = PropTS.lean (verbatim) + `PurityCopy.lean.part` (t-purity3's
  PurityDim2.lean from origin/wip/t-purity3 7e4d4dd0, verbatim minus import/#print lines, in a
  section; original saved as `t-purity3-PurityDim2.orig.txt`) + `Appendix.lean.part`.
  `check_identical.py`: PREFIX IDENTICAL, PURITY COPY CONTAINED (VERIFIED).
- `purityGlobalDim2 : PurityGlobalDim2.{0} := TPurity3.purityGlobalDim2`;
  `propTSAll_of_pieces'` = the composite without the purity hypothesis.
- Compile (23 s): 0 errors; 26 PropTSGlue axiom lines all standard (VERIFIED).

## Step 6b: independent review result (read-only model agent, no Lean)
- Verdict: no false, vacuous or trivial Prop. All open glue Props TRUE as stated in Lean
  (SNVertical, SNHorizontalTransfer, SNSpecialize, KummerCompositum, KummerAbhyankarFin/Inf,
  KummerOtherBranchFin/Inf (the latter true even with 0 ∈ S), KummerVerticalFin/Inf,
  HeckeDegree/Branch/NoVertRam). HeckeNormalization TRUE iff Y₃ is ℚ-irreducible (SPECULATIVE
  input, as in the docstring); if Y₃ were ℚ-reducible it would be false and the other Hecke Props
  vacuous. Suggestion: split ℚ-irreducibility out as its own named Prop (done in step 8).
- "∀ E with NormalizationModel" is a property of the cover (E determined up to iso; Jacobson
  argument), so the Hecke "∀ E" pieces are not stronger than their "∃ E" forms.

## Step 7: SNHorizontalTransfer PROVED, compiled
- Developed in `HorizTransfer.lean` (Mathlib only; compiled, standard axioms). Lemmas:
  `isLocalization_field_self`, `int_notMem` (P ∩ ℤ = 0 when p ∉ P), `atPrime_congr`,
  `snHorizontalTransfer_aux`. Route: S and B are localizations of C = integral closure of ℤ[X]
  (`IsLocalization.integralClosure`); S_{Q'} and B_Q are both C_𝔮
  (`isLocalization_isLocalization_atPrime_isLocalization`), hence C-isomorphic
  (`IsLocalization.algEquiv`); e(Q) = 1 ⇒ ℚ[X] → B_Q formally unramified
  (`Ideal.ramificationIdx_eq_one_iff`, char-0 residue fields) ⇒ ℤ[X] → B_Q ⇒ ℤ[X] → S_{Q'} ⇒
  ℤ[X]_m → S_{Q'} (`of_restrictScalars`).
- Lean pitfall: `Localization.AtPrime Q'` (CommSemiring-derived primeCompl) failed to synthesize
  `CommRing` for Q' over the integral closure of ℤ[X]_m; writing `Localization Q'.primeCompl`
  fixed it; `AlgEquiv.restrictScalars` mismatched instances, `AlgEquiv.ofRingEquiv` worked.
- Pasted into the appendix: `snHorizontalTransfer : SNHorizontalTransfer`,
  `specNonMeeting_of_pieces''' : PurityGlobalDim2 → SNVertical → SNSpecialize → SpecNonMeeting`;
  `propTSAll_of_pieces'` no longer takes SNHorizontalTransfer.
- Compile: 0 errors, 28 PropTSGlue axiom lines all standard; prefix IDENTICAL, purity copy
  CONTAINED (VERIFIED).

## Step 8: HeckeNormalization split (reviewer's suggestion), compiled
- `HeckeIrreducible` (SPECULATIVE input: Y is irreducible), `HeckeNormalizationIrr` (the chart for
  irreducible Y), `heckeNormalization_of_irr`. Compile: 0 errors, 29 standard axiom lines.

## Step 9: SNVertical reduced to VerticalResidueSeparable, compiled
- New glue `VerticalResidueSeparable` (field theory: `[E:ℚ(X)] < p ⇒
  HasSeparableResidueFieldsAt ℤ[X] C (pℤ[X])`, C the integral closure of ℤ[X] in E).
- `snVertical_aux`/`snVertical_of_sep : VerticalResidueSeparable → SNVertical` (compiled): P = pℤ[X]_m
  by heights (`IsLocalization.height_under`, `Ideal.height_add_one_le_of_lt_of_isPrime`);
  NoVerticalRam gives e(𝔮) = 1; `Ideal.ramificationIdx_eq_one_iff`; C_𝔮 ≅ S_{Q'}; of_restrictScalars.
- `specNonMeeting_of_pieces4 : PurityGlobalDim2 → VerticalResidueSeparable → SNSpecialize →
  SpecNonMeeting`; `propTSAll_of_pieces'` now takes VerticalResidueSeparable, SNSpecialize.
- Compile: 0 errors, 31 PropTSGlue axiom lines all standard; prefix IDENTICAL (VERIFIED).

## Step 10: final composite, report, fleet summary
- `propTSAll_of_pieces''` (14 open glue Props + T2, R1R2fp, MobiusGlue). Compile: 0 errors,
  32 PropTSGlue axiom lines all standard, 37 linter warnings (VERIFIED).
- docs/research/prop-ts-glue.md rewritten; .fleet/prop-ts-glue.md written.

## Step 11: VerticalResidueSeparable reduced to VerticalResidueDegree, compiled
- `isSeparable_of_finrank_lt` (PROVED: finite extension of degree < p in characteristic p is
  separable; `Polynomial.separable_or`, `natDegree_expand`, `minpoly.natDegree_le`).
- New glue `VerticalResidueDegree` (Σ e f = n inequality: κ(q)/κ(pℤ[X]) finite of degree
  ≤ [E:ℚ(X)] for q over pℤ[X] in C); `verticalResidueSeparable_of_degree` (compiled; κ(pℤ[X]) has
  characteristic p via `Ideal.algebraMap_residueField_eq_zero`).
- `propTSAll_of_pieces'''` (final composite: VerticalResidueDegree in place of
  VerticalResidueSeparable). Compile: 0 errors, 35 PropTSGlue axiom lines all standard (VERIFIED).

## Step 12: intermediate wrap-up (superseded by step 13)
- Docs and fleet summary written at this point; `VerticalResidueDegree` was then proved in step 13.

## Step 13: VerticalResidueDegree PROVED; SpecNonMeeting from SNSpecialize alone, compiled
- Developed in `VRD.lean` (Mathlib only; compiled, standard axioms): `vrd_aux`. Route:
  `Ideal.sum_ramification_inertia_eq_finrank_fiber` for ℤ[X] → C at pℤ[X] (C quasi-finite via
  `IsIntegralClosure.finite`; `Algebra.QuasiFinite.finite_primesOver`); e(q) > 0 from
  `ramificationIdx_pos_of_mem_minimalPrimes` (q minimal over pC by `Ideal.IsIntegral.under_lt_under`);
  `Ideal.inertiaDeg_eq`; fibre dimension = [E:ℚ(X)]: ℤ[X]_{(p)} is a DVR
  (`IsDiscreteValuationRing.TFAE`, principal maximal ideal), C_{(p)} = integral closure of
  ℤ[X]_{(p)} in E is free of rank [E:ℚ(X)] (`IsIntegralClosure.module_free`, `.rank`), and
  κ ⊗_{ℤ[X]} C ≅ κ ⊗_{ℤ[X]_{(p)}} C_{(p)} (`AlgebraTensorModule.cancelBaseChange`,
  `IsLocalizedModule.isBaseChange`, `Module.finrank_baseChange`).
- Appendix: `verticalResidueDegree : VerticalResidueDegree`,
  `specNonMeeting_of_specialize : SNSpecialize → SpecNonMeeting`, `propTSAll_final` (13 open glue
  Props: SNSpecialize, seven Kummer pieces, five Hecke pieces; plus T2, R1R2fp, MobiusGlue).
- Compile: 0 errors, 38 PropTSGlue axiom lines all standard, 48 linter warnings; prefix IDENTICAL,
  purity copy CONTAINED (VERIFIED).

## Step 14: final state
- Final composite `propTSAll_final`: PropTSAll from T2, R1R2fp, MobiusGlue and 13 open glue Props
  (SNSpecialize; KummerCompositum, KummerAbhyankarFinGlue, KummerOtherBranchFin, KummerVerticalFin,
  KummerAbhyankarInfGlue, KummerOtherBranchInf, KummerVerticalInf; HeckeIrreducible,
  HeckeNormalizationIrr, HeckeDegree, HeckeBranch, HeckeNoVertRam).
- Unproved (open glue, not attempted to completion): SNSpecialize (route in report §6), the seven
  Kummer pieces, the five Hecke pieces.

## Step 15: finiteness half of SNSpecialize PROVED, compiled
- `finiteDimensional_residue` (B finite over ℚ[X] via `IsIntegralClosure.finite`; ℚ[X] acts on
  B/𝔓 through X ↦ s₀, `X_sub_C_dvd_sub_C_eval`; adjoin of a finite set of algebraic elements).
- New glue `SNSpecializeUnram` (only the `UnramifiedAt` conclusion); `snSpecialize_of_unram`;
  `propTSAll_final'` (13 open glue Props with SNSpecializeUnram).
- Lean pitfall: `map_add`/`map_zero` on `Ideal.Quotient.mk 𝔓` for 𝔓 an ideal of an
  `integralClosure` timed out in typeclass search; `RingHom.map_add` etc. worked.
- Compile: 0 errors, 41 PropTSGlue axiom lines all standard; prefix IDENTICAL, purity CONTAINED.

## Step 16: SNSpecializeUnram PROVED; SpecNonMeeting is a THEOREM, compiled
- Developed in `SNSpec.lean` (Mathlib only; compiled, standard axioms): `nval`, `nval_cast`,
  `mem_m_iff` (u ∈ m ↔ p ∣ d^k u(s₀)), `secGen`, `evR`, `rbar_isLocalization` (ℤ[X]_m/(dX − a) is
  the localization of ℤ at (p)), `mem_of_isIntegral_of_mem_closure`, `isIntegral_int_of_injective`,
  `isIntegral_int_map`, `snSpecializeUnram_aux`.
- Route: Ψ : S → ℚ̄ extends φ ∘ (C → B/𝔓) (`IsLocalization.lift`; denominators u ∉ m have
  u(s₀) ≠ 0); A := Ψ(S) ⊆ ℚ̄ is formally unramified over R/(dX − a) (étale S, surjection,
  `of_restrictScalars`), hence over ℤ (`rbar_isLocalization`, `of_isLocalization`, `comp`); A is
  Dedekind (`IsDedekindDomain.of_formallyUnramified`); 𝓞_L ⊆ A (integrally closed, L ⊆ Frac A);
  A = (𝓞_L)_{(p)} (`IsIntegral.exists_multiple_integral_of_isLocalization`); for P ∋ p,
  (𝓞_L)_P ≅ A_{PA} formally unramified over ℤ ⇒ e(P) = 1 (`Ideal.ramificationIdx_eq_one`).
- Lean pitfalls: integralClosure over `Localization.AtPrime m` with `locAlg` has two semiring
  paths (OreLocalization.instCommSemiring vs CommRing.toCommSemiring); `RingHom.range` and
  `Ideal` quotients of it failed until `letI : CommSemiring S := CommRing.toCommSemiring` was set
  at the start; ℤ-scalar towers needed `IsScalarTower.of_algebraMap_eq` with explicit (R S A);
  `isIntegral_algHom_iff` hit an int-algebra diamond on `FractionRing A` (replaced by
  `Polynomial.hom_eval₂`); `eval_map` clashes with a CategoryTheory name under the file's opens
  (use `Polynomial.eval_map`).
- Appendix: `snSpecializeUnram : SNSpecializeUnram`, `specNonMeeting : SpecNonMeeting`,
  `propTSAll_final''` (12 open glue Props: seven Kummer pieces, five Hecke pieces; plus T2,
  R1R2fp, MobiusGlue).
- Compile (about 1 min): 0 errors, 45 PropTSGlue axiom lines all standard; prefix IDENTICAL,
  purity copy CONTAINED (VERIFIED).
