import ANormalizationExpectedV3

/-!
# Candidate: fixed-place normalization `a σ` over the common `ℚ̄`

PRIVATE CANDIDATE (climb/a-normalization). Proves the six FROZEN targets of
`ClimbANormalizationExpected` (`ANormalizationExpected-v3.lean`, sha256
6f659cf67fbc8ec00a8f46c4ce7a241bfd24b3117de5d523dd1098c4c0adc5f6, 11 defs / 0 proofs,
frozen by the independent reviewer) and nothing else. The Expected file is imported as
frozen; it is NOT edited, and no target is shrunk.

Everything below is conditional on data this lane does not construct: the degree function
`d` is a GIVEN positive rational function (no degree object exists in the canonical tree and
none is fabricated here), `c` is a GIVEN nonvanishing rational cocycle, and the quartic
multiplicativity is a GIVEN hypothesis — exactly the hypotheses the proved real
`GlueDescent.sign_normalization` already carries. The μ/B1 binding, the rationality of the
actual `c`, the common `C`/`ε`/`c` binders of the C10 consumer, the global `A`/`Ψ`/`T`/`E`/`af`
data and local constancy (120c) all remain OPEN.

This module owns its own scope and its own axiom reports; nothing is inherited from the
character or β lanes.
-/

noncomputable section

open Polynomial ClimbANormalizationExpected

namespace ClimbANormalization

/-! ## 1. The actual value: positivity and the quartic equation from `Real.rpow` -/

theorem aReal_pos {q : ℚ} (hq : 0 < q) : 0 < aReal q :=
  Real.rpow_pos_of_pos (by exact_mod_cast hq) _

theorem aReal_quartic {q : ℚ} (hq : 0 < q) : (aReal q) ^ (4 : ℕ) * (q : ℝ) = 1 := by
  have hq0 : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq
  have h : (aReal q) ^ (4 : ℕ) = ((q : ℝ))⁻¹ := by
    rw [aReal, ← Real.rpow_natCast ((q : ℝ) ^ (-(1 / 4 : ℝ))) 4, ← Real.rpow_mul hq0.le]
    norm_num
    rw [Real.rpow_neg_one]
  rw [h, inv_mul_cancel₀ hq0.ne']

theorem quarticFromRpow : ClimbANormalizationExpected.QuarticFromRpow :=
  fun _ hq => ⟨aReal_pos hq, aReal_quartic hq⟩

/-! ## 2. Generalized fixed-place preimage: any value algebraic over `ℚ` is in the image -/

theorem algebraicValueHasPreimage : ClimbANormalizationExpected.AlgebraicValueHasPreimage := by
  intro K _ _ f z hz
  classical
  -- a ring hom into ℂ forces characteristic zero, which is what makes `ℚ` act on `K`
  haveI : CharZero K := RingHom.charZero f
  obtain ⟨p, hp0, hpz⟩ := hz
  set P : K[X] := p.map (algebraMap ℚ K) with hP
  have hinjQK : Function.Injective (algebraMap ℚ K) := (algebraMap ℚ K).injective
  have hP0 : P ≠ 0 := by
    rw [hP]
    exact (Polynomial.map_ne_zero_iff hinjQK).mpr hp0
  have hcard : Multiset.card P.roots = P.natDegree :=
    splits_iff_card_roots.mp (IsAlgClosed.splits P)
  have hmap : P.roots.map f = (P.map f).roots :=
    roots_map_of_injective_of_card_eq_natDegree f.injective hcard
  have hcomp : (f.comp (algebraMap ℚ K)) = algebraMap ℚ ℂ := by
    ext q
    simp [eq_ratCast]
  have hPf : P.map f = p.map (algebraMap ℚ ℂ) := by
    rw [hP, Polynomial.map_map, hcomp]
  have hPf0 : P.map f ≠ 0 := by
    rw [hPf]
    exact (Polynomial.map_ne_zero_iff (algebraMap ℚ ℂ).injective).mpr hp0
  have hroot : z ∈ (P.map f).roots := by
    rw [mem_roots hPf0, IsRoot.def, hPf, Polynomial.eval_map, ← aeval_def]
    exact hpz
  rw [← hmap] at hroot
  obtain ⟨w, -, hw⟩ := Multiset.mem_map.mp hroot
  exact ⟨w, hw⟩

/-! ## 3. The actual value is algebraic, given a rational degree -/

theorem rationalDegreeValueIsAlgebraic :
    ClimbANormalizationExpected.RationalDegreeValueIsAlgebraic := by
  intro q hq
  have hq0 : (q : ℚ) ≠ 0 := ne_of_gt hq
  refine ⟨(X : ℚ[X]) ^ 4 - C q⁻¹, X_pow_sub_C_ne_zero (by norm_num) _, ?_⟩
  have hquart := aReal_quartic hq
  have hqR : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq
  have hreal : (aReal q) ^ (4 : ℕ) - ((q⁻¹ : ℚ) : ℝ) = 0 := by
    have : (aReal q) ^ (4 : ℕ) = ((q : ℝ))⁻¹ := by
      field_simp at hquart ⊢
      linarith [hquart]
    rw [this]
    push_cast
    ring
  have : ((((aReal q) ^ (4 : ℕ) - ((q⁻¹ : ℚ) : ℝ) : ℝ)) : ℂ) = 0 := by
    rw [hreal]; norm_num
  simpa [aComplex, map_sub, map_pow, Complex.ofReal_sub, Complex.ofReal_pow] using this

/-! ## 4. The sign at the identity, from the explicit positivity datum only -/

theorem signAtOneIsOne : ClimbANormalizationExpected.SignAtOneIsOne := by
  intro G _ c hc
  have : SignType.sign (c 1 1) = 1 := sign_pos hc
  simp [qbarSign, ratSign, qbarOfRat, this]

/-! ## 5. Branch rigidity: the `ρ`-image pins exactly one element of `ℚ̄` -/

theorem rho_injective (ρ : GlueC10.Qbar →ₐ[ℚ] ℂ) : Function.Injective ρ :=
  RingHom.injective ρ.toRingHom

theorem exists_preimage_aComplex (ρ : GlueC10.Qbar →ₐ[ℚ] ℂ) {q : ℚ} (hq : 0 < q) :
    ∃ w : GlueC10.Qbar, ρ w = aComplex q :=
  algebraicValueHasPreimage GlueC10.Qbar ρ.toRingHom (aComplex q)
    (rationalDegreeValueIsAlgebraic q hq)

theorem fixedPlaceBranchUnique : ClimbANormalizationExpected.FixedPlaceBranchUnique := by
  intro ρ q hq
  obtain ⟨w, hw⟩ := exists_preimage_aComplex ρ hq
  exact ⟨w, hw, fun y hy => rho_injective ρ (hy.trans hw.symm)⟩

/-! ## 6. The bundle -/

theorem rho_qbarOfRat (ρ : GlueC10.Qbar →ₐ[ℚ] ℂ) (r : ℚ) :
    ρ (qbarOfRat r) = (r : ℂ) := by
  rw [qbarOfRat, map_ratCast]

/-- The real sign of a rational cast agrees with the cast of its rational sign. -/
theorem ratSign_cast {r : ℚ} (hr : r ≠ 0) :
    ((ratSign r : ℚ) : ℝ) = (SignType.sign ((r : ℝ)) : ℝ) := by
  rcases lt_or_gt_of_ne hr with h | h
  · have hR : ((r : ℝ)) < 0 := by exact_mod_cast h
    rw [ratSign, sign_neg h, sign_neg hR]
    norm_num
  · have hR : (0 : ℝ) < (r : ℝ) := by exact_mod_cast h
    rw [ratSign, sign_pos h, sign_pos hR]
    norm_num

theorem bundledFixedPlaceNormalization :
    ClimbANormalizationExpected.BundledFixedPlaceNormalization := by
  intro G _ ρ d c hd hc hmul
  have hpre : ∀ g : G, ∃ w : GlueC10.Qbar, ρ w = aComplex (d g) := fun g =>
    exists_preimage_aComplex ρ (hd g)
  choose aQ haQ using hpre
  refine ⟨aQ, haQ, fun g h => ?_, fun h1 => ?_⟩
  · -- the `ha`-shaped cochain equation, transported from the proved real normalization
    have hdg : (0 : ℝ) < (d g : ℝ) := by exact_mod_cast hd g
    have hdh : (0 : ℝ) < (d h : ℝ) := by exact_mod_cast hd h
    have hdgh : (0 : ℝ) < (d (g * h) : ℝ) := by exact_mod_cast hd (g * h)
    have hcne : ((c g h : ℚ) : ℝ) ≠ 0 := by exact_mod_cast hc g h
    have hdeg : (d g : ℝ) * (d h : ℝ) = ((c g h : ℚ) : ℝ) ^ 4 * (d (g * h) : ℝ) := by
      exact_mod_cast hmul g h
    have hreal := GlueDescent.sign_normalization hdg hdh hdgh hcne hdeg
    have hsign : ((ratSign (c g h) : ℚ) : ℝ) = (SignType.sign ((c g h : ℚ) : ℝ) : ℝ) :=
      ratSign_cast (hc g h)
    have hR : aReal (d g) * aReal (d h) * ((c g h : ℚ) : ℝ)
        = ((ratSign (c g h) : ℚ) : ℝ) * aReal (d (g * h)) := by
      rw [hsign, aReal, aReal, aReal]
      exact hreal
    refine rho_injective ρ ?_
    rw [map_mul, map_mul, map_mul, haQ, haQ, haQ, qbarSign, rho_qbarOfRat, rho_qbarOfRat]
    have := congrArg (fun x : ℝ => (x : ℂ)) hR
    push_cast [aComplex] at this ⊢
    exact this
  · -- normalization at `1`, only from the explicit datum `d 1 = 1`
    refine rho_injective ρ ?_
    rw [haQ, h1, map_one]
    simp [aComplex, aReal]

end ClimbANormalization

/-! ## Reports -/

#print axioms ClimbANormalization.aReal_pos
#print axioms ClimbANormalization.aReal_quartic
#print axioms ClimbANormalization.quarticFromRpow
#print axioms ClimbANormalization.algebraicValueHasPreimage
#print axioms ClimbANormalization.rationalDegreeValueIsAlgebraic
#print axioms ClimbANormalization.signAtOneIsOne
#print axioms ClimbANormalization.rho_injective
#print axioms ClimbANormalization.exists_preimage_aComplex
#print axioms ClimbANormalization.fixedPlaceBranchUnique
#print axioms ClimbANormalization.rho_qbarOfRat
#print axioms ClimbANormalization.ratSign_cast
#print axioms ClimbANormalization.bundledFixedPlaceNormalization

#check @ClimbANormalization.quarticFromRpow
#check @ClimbANormalization.algebraicValueHasPreimage
#check @ClimbANormalization.rationalDegreeValueIsAlgebraic
#check @ClimbANormalization.signAtOneIsOne
#check @ClimbANormalization.fixedPlaceBranchUnique
#check @ClimbANormalization.bundledFixedPlaceNormalization
