# rc-model-generic5 results log

## Setup
- merged main 61e00d45 into wip/rc-model-generic5 (no conflicts), merge commit 4f0328005.

## Item 1: StagePrimes.lean (builds; axioms propext, Classical.choice, Quot.sound)
- EcurveZ_disc : (EcurveZ l).Δ = 2304 * l^6.
- stagePrime_not_dvd_disc (s : Setup I L) i : ¬ (p_i : ℤ) ∣ Δ(EcurveZ ℓ)   [StageKummer.stageGood]
- stagePrime_five_le s i : 5 ≤ p_i   (h₅)   [p ≡ 3 mod 4 (stage_mod_four), 3 ∣ 2304]
- stagePrime_not_dvd_tame s (hN : 0 < N) (hB : (N*φ(N)).primeFactors ⊆ s.B) i : ¬ p_i ∣ N*φ(N)  (htame)
- subset_stageExclusions, not_dvd_tame_of_not_mem_stageExclusions (exists_detector_stages sequences are over stageExclusions ℓ Dw hstar B ⊇ B)
- two_le_newformLevel (hN : 0 < CST.newformLevel E) : 2 ≤ CST.newformLevel E  [S₂(SL₂ℤ)=0 via Mathlib CuspForm.rank_eq_zero_of_weight_lt_twelve; a₁(E)=1 via lFunction_one]
- two_le_level (hN : 0 < StageKummer.level ℓ) : 2 ≤ StageKummer.level ℓ  (h₂ from the hN hypothesis of oddStagedOfGoodRows)

## Item 2 pieces
- IntegralTransfer.lean (builds; standard axioms): isIntegral_of_finite (θ : D →+* B finite, φ : B →+* C, φ∘θ lands in integral elements over A ⇒ φ b integral over A); mem_range_of_isIntegral (κ = algebraMap A B injective, κ π unit, span{π} radical, b integral, κ(π)^n b ∈ range ⇒ b ∈ range).
- AtkinField.lean (builds; standard axioms): pullback_jq (hQ : Q ∥ N) : AtkinRational.pullback hQ ⟨jq,_⟩ = ⟨jqN Q,_⟩; modularPolynomial_eval_field (M ∣ N) data : data.Φ.eval₂ (eval₂RingHom (Int.castRingHom F) jq) (jqN M) = 0 in F = modularFunctionField N.
- RationalChart.lean (builds; standard axioms): ratToField h₂ : Y0RationalAlgebra h₂ →+* modularFunctionField N (= genericModularFieldEquiv ∘ Y0RationalGenericJInclusion, the comparison inside ModelNeron.chartField); ratToField_J (j ↦ jq); ratToField_isFractionRing; isIntegral_jqN; isIntegral_pullback_ratToField; atkinRat h₂ hQ : ring endo of Y0RationalAlgebra with ratToField_atkinRat : ratToField (atkinRat a) = AtkinRational.pullback hQ (ratToField a); atkinRat_J; genericMap_eq_chart (generic point of the rational open = generic point of X0); atkinRat_openImmersion : Spec.map (atkinRat) ≫ rationalOpenImmersion = rationalOpenImmersion ≫ (rationalAtkin hQ).hom.
  => item 2(a) (W_Q preserves the finite chart) is proved by the function-field route (integral closure over ℚ[j]), not the closed-point route.
- IntegralTransfer.lean additions: exists_eq_of_isIntegralElem, isRadical_span_of_residue_reduced (k ⊗_R A reduced, 𝔪 = (π) ⇒ πA radical), restrictRange / restrictRange_spec.
- Extension.lean (builds; standard axioms; no sorry):
  levelToRat : A_R →+* A_ℚ (= Y0RationalBaseChange ∘ includeRight); levelToRat_injective (flatness); exists_pow_mul_mem_range; isRadical_span_ell (special fibre reduced, levelQuotient_fibre_reduced at the residue field);
  isIntegral_atkinRat_levelToRat; atkinLevel hQ : A_R →+* A_R with levelToRat_atkinLevel; Wint h₅ htame h₂ hQ : Pinned.Y0Level ⟶ Pinned.Y0Level (= Over.homMk (Spec.map atkinLevel));
  genericIso_inv_fst; conj_of_pullback; generic_map_Wint;
  extendsAtkin_Wint q : PMWire.ExtendsAtkin (ModelNeron.source h₅ htame h₂) q (Wint … (isExactDivisor_primePow));
  goodRow_extension : ∀ q, q.Prime → 0 < N.factorization q → ∃ W, ExtendsAtkin (ModelNeron.source h₅ htame h₂) q W  (= GoodRow.extension at the pinned model);
  eq_Wint_of_extendsAtkin (uniqueness).
- Pitfall: Pinned.Y0LevelAlgebra's synthesized CommRing instance defeats unification with Subalgebra.toSemiring (whnf timeouts at 1e6 heartbeats); fix: `attribute [local instance 2000] levelCommRing` (= Subalgebra.toCommRing _), generic lemmas over arbitrary rings, and term-mode Spec.map_comp chains instead of rw.
- ComplexPoints.lean (builds; standard axioms): ringHom_eq_of_openImmersion; atkinRat_involutive; atkinLevel_involutive; Wint_comp_self (Wint ≫ Wint = 𝟙); rationalPointAtParameter_atkinRat ((x_τ) ∘ atkinRat = x_{W_Q τ}); atkinRatAlg; rationalPoints_atkinRat_complex (∀ complex y, ∃ τ, rationalPoints y = analyticCyclicPair τ ∧ rationalPoints (y ∘ atkinRat) = analyticCyclicPair (W_Q τ)).

## Item 5: docs/research/rc-model-generic4.md corrected (commit a469b7911).
## Item 3: scoped stop after ComplexPoints (moduli Vélu side open; statements in report). Item 4: not started.
## Report: docs/research/rc-model-generic5.md.
