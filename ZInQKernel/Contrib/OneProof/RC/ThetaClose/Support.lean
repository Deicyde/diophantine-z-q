import ZInQKernel.Contrib.OneProof.RC.ThetaClose.Roots
import ZInQKernel.Contrib.OneProof.RC.ThetaJoin.Support

/-! The exceptional-place support tests on the manuscript's odd filter. -/

noncomputable section

namespace ZInQ.Manuscript.RC.ThetaClose

open Adelic Eichler LocalWeights ThetaJoin Matrix
open scoped Quaternion

variable {O : Type} [CommRing O] [IsDomain O]

omit [IsDomain O] in
private theorem extend_nonzero {X A : Type*} (i : A → X) (hi : Function.Injective i)
    (f : A → O) (x : X) :
    extendWeight i f x ≠ 0 ↔ ∃ y, i y = x ∧ f y ≠ 0 := by
  constructor
  · intro h
    have hx : x ∈ Set.range i := by
      by_contra hn
      exact h ((extendWeight_spec _ _ hi).2 x hn)
    obtain ⟨y, rfl⟩ := hx
    exact ⟨y, rfl, by simpa only [(extendWeight_spec _ _ hi).1] using h⟩
  · rintro ⟨y, rfl, hy⟩
    simpa only [(extendWeight_spec _ _ hi).1] using hy

private theorem affine_det {K : Type*} [Field K] (A : Mat K) (ht : A.trace = 1) :
    ((2 : K) • A - 1).det = 4 * A.det - 1 := by
  rw [Matrix.trace_fin_two] at ht
  simp [Matrix.det_fin_two, Matrix.smul_apply, Matrix.sub_apply]
  linear_combination -2 * ht

private theorem positive_level_split (p : ℕ) [Fact p.Prime] {e : ℕ} (he : 0 < e)
    (y : AffineOrder p e) (h : PadicInt.toZModPow 1 (1 - 4 * y.val.val.det) ≠ 0) :
    SplitSupport y.val := by
  let f : ℤ_[p] →+* ZMod (p ^ 1) := PadicInt.toZModPow 1
  have hmod := level_residue_root y.val y.prop
  have hr : f ((y.val.val 1 1) ^ 2 - y.val.val 1 1 + y.val.val.det) = 0 := by
    rw [show f = PadicInt.toZModPow 1 from rfl,
      ← PadicInt.cast_toZModPow 1 e he, hmod, ZMod.cast_zero]
  have hs : f ((2 * y.val.val 1 1 - 1) ^ 2) = f (1 - 4 * y.val.val.det) := by
    rw [← sub_eq_zero, ← map_sub,
      show (2 * y.val.val 1 1 - 1) ^ 2 - (1 - 4 * y.val.val.det) =
        4 * ((y.val.val 1 1) ^ 2 - y.val.val 1 1 + y.val.val.det) by ring,
      map_mul, hr, mul_zero]
  have hu : IsUnit (2 * y.val.val 1 1 - 1) := by
    rw [unit_iff_red_ne_zero]
    change f _ ≠ 0
    intro hz
    rw [map_pow, hz, zero_pow (by decide : (2 : ℕ) ≠ 0)] at hs
    exact h hs.symm
  obtain ⟨a, ha, -⟩ := (levelRoot_existsUnique he y.val y.prop).mpr hu
  exact ⟨a, ha.1, ha.2.1⟩

variable {ell N m : ℕ} [Fact ell.Prime] (h : ell % 4 = 3) (hN : 0 < N)
variable (z : FiniteUnits (levelRing h hN)) (x : B (-1) (-(ell : ℚ))) (hx : x.re = 0)

private def splitVector (q : Prime) (hq : q.val ≠ ell) : TraceZero ℚ_[q.val] :=
  ⟨splitChart ell h q hq (atRep z q x), by
    rw [(split_invariants _ _ (splitChart ell h q hq) _).1, atRep_re, hx, Rat.cast_zero,
      mul_zero]⟩

private theorem affine_range (q : Prime) (hq : q.val ≠ ell) :
    (splitVector h hN z x hx q hq ∈ Set.range (affineZero q.val (e := N.factorization q.val))) ↔
      atRep z q (affineGenerator x) ∈ (levelRing h hN).completion q.val := by
  let E := splitChart ell h q hq
  have hs : (2 : ℚ_[q.val]) • E (atRep z q (affineGenerator x)) - 1 =
      (splitVector h hN z x hx q hq).val := by
    change (2 : ℚ_[q.val]) • E (atRep z q (affineGenerator x)) - 1 = E (atRep z q x)
    have h₂ : E (2 • atRep z q (affineGenerator x)) = E (atRep z q x + 1) :=
      congrArg (fun t => E t) (atRep_affine_twice z q x)
    rw [map_nsmul, map_add, map_one] at h₂
    apply sub_eq_of_eq_add
    rw [show (2 : ℚ_[q.val]) = ((2 : ℕ) : ℚ_[q.val]) by norm_num, Nat.cast_smul_eq_nsmul]
    exact h₂
  constructor
  · rintro ⟨y, hy⟩
    let Y := (splitOrderEquiv ell h N hN q hq).symm y.val
    have hY : integralMat q.val y.val.val = E Y.val := by
      simpa only [Y, AlgEquiv.apply_symm_apply] using splitOrderEquiv_apply ell h N hN q hq Y
    have he : Y.val = atRep z q (affineGenerator x) := by
      apply E.injective
      apply smul_right_injective _ (by norm_num : (2 : ℚ_[q.val]) ≠ 0)
      have hh : (2 : ℚ_[q.val]) • integralMat q.val y.val.val - 1 =
          (2 : ℚ_[q.val]) • E (atRep z q (affineGenerator x)) - 1 :=
        (congrArg Subtype.val hy).trans hs.symm
      rw [hY] at hh
      exact sub_left_inj.mp hh
    exact he ▸ Y.prop
  · intro ht
    let Y := splitOrderEquiv ell h N hN q hq ⟨_, ht⟩
    have hy : affineInclusion q.val Y = (splitVector h hN z x hx q hq).val := by
      unfold affineInclusion
      rw [splitOrderEquiv_apply]
      exact hs
    refine ⟨⟨Y, (affineInclusion_trace_iff q.val Y).mp ?_⟩, Subtype.ext hy⟩
    rw [hy]
    exact (splitVector h hN z x hx q hq).prop

private theorem affine_det_on_sphere {D : ℕ} {k : ℤ} (hn : Visibility.nrd x = (m * D : ℕ))
    (hk : (D : ℤ) * -(m : ℤ) = 4 * k + 1)
    (q : Prime) (hq : q.val ≠ ell) {e : ℕ} (y : AffineOrder q.val e)
    (hy : affineZero q.val y = splitVector h hN z x hx q hq) :
    y.val.val.det = (-k : ℤ) := by
  have ht : (integralMat q.val y.val.val).trace = 1 := by
    rw [integralMat_trace, y.prop, PadicInt.coe_one]
  have hn' : (splitVector h hN z x hx q hq).val.det = (m * D : ℕ) := by
    change (splitChart ell h q hq (atRep z q x)).det = _
    rw [(split_invariants _ _ (splitChart ell h q hq) _).2]
    change reducedNorm _ _ (atRep z q x) = _
    calc
      _ = (Visibility.nrd x : ℚ_[_]) := norm_atRep z _ x
      _ = _ := by rw [hn, Rat.cast_natCast]
  have hd := congrArg (fun X : TraceZero ℚ_[q.val] => X.val.det) hy
  change ((2 : ℚ_[q.val]) • integralMat q.val y.val.val - 1).det = _ at hd
  have hmap : (integralMat q.val y.val.val).det = (y.val.val.det : ℚ_[q.val]) :=
    (RingHom.map_det (PadicInt.Coe.ringHom (p := q.val)) y.val.val).symm
  rw [affine_det _ ht, hn', hmap] at hd
  have hc := congrArg (fun t : ℤ => (t : ℚ_[q.val])) hk
  push_cast at hc hd
  apply Subtype.val_injective
  push_cast
  linear_combination (hd - hc) / 4

private theorem levelSupport (C : LevelRoots O N) {D : ℕ} {k : ℤ}
    (hn : Visibility.nrd x = (m * D : ℕ))
    (hk : (D : ℤ) * -(m : ℤ) = 4 * k + 1)
    (q : Prime) (hq : q.val ≠ ell) (hqN : q.val ∣ N) (hunit : ¬ q.val ∣ m * D) :
    levelSchwartz q.val (e := N.factorization q.val) (C.alpha q hqN)
      (splitVector h hN z x hx q hq) ≠ 0 ↔
      atRep z q (affineGenerator x) ∈ (levelRing h hN).completion q.val := by
  let e := N.factorization q.val
  let α := (C.alpha q hqN).comp (Units.map (PadicInt.toZModPow _).toMonoidHom)
  have he : 0 < e := q.prop.factorization_pos_of_dvd hN.ne' hqN
  rw [← affine_range h hN z x hx q hq]
  change extendWeight (affineZero q.val (e := e)) (fun y => levelWeight α y.val) _ ≠ 0 ↔ _
  rw [extend_nonzero _ (affineZero_openEmbedding q.val e).injective]
  constructor
  · rintro ⟨y, hy, -⟩
    exact ⟨y, hy⟩
  · rintro ⟨y, hy⟩
    refine ⟨y, hy, (levelWeight_nonzero_iff he α y.val y.prop).mpr ?_⟩
    apply positive_level_split q.val he
    rw [affine_det_on_sphere h hN z x hx hn hk q hq y hy]
    have hcast := congrArg (fun t : ℤ => (t : ℤ_[q.val])) hk
    push_cast at hcast
    rw [show (1 : ℤ_[q.val]) - 4 * ((-k : ℤ) : ℤ_[q.val]) =
      -((m * D : ℕ) : ℤ_[q.val]) by push_cast; linear_combination -hcast]
    rw [map_neg, neg_ne_zero, ← unit_iff_red_ne_zero]
    exact PadicInt.isUnit_iff.mpr (PadicInt.norm_natCast_eq_one_iff.mpr
      (q.prop.coprime_iff_not_dvd.mpr hunit))

private theorem dyadicSupport {D : ℕ} {k : ℤ}
    (hn : Visibility.nrd x = (m * D : ℕ))
    (hk : (D : ℤ) * -(m : ℤ) = 4 * k + 1)
    (h₈ : Int.ModEq 8 ((D : ℤ) * -(m : ℤ)) 1)
    (h₂N : ¬ 2 ∣ N) (h₂ell : 2 ≠ ell) :
    (dyadicSchwartz (splitVector h hN z x hx ⟨2, Nat.prime_two⟩ h₂ell) : O) ≠ 0 ↔
      atRep z ⟨2, Nat.prime_two⟩ (affineGenerator x) ∈ (levelRing h hN).completion 2 := by
  rw [← affine_range h hN z x hx ⟨2, Nat.prime_two⟩ h₂ell]
  change _ ↔ _ ∈ Set.range (affineZero 2 (e := N.factorization 2))
  rw [Nat.factorization_eq_zero_of_not_dvd h₂N]
  unfold dyadicSchwartz
  rw [extend_nonzero _ (affineZero_openEmbedding 2 0).injective]
  constructor
  · rintro ⟨y, hy, -⟩
    exact ⟨y, hy⟩
  · rintro ⟨y, hy⟩
    refine ⟨y, hy, ?_⟩
    rw [dyadicWeight, affine_det_on_sphere h hN z x hx hn hk ⟨2, Nat.prime_two⟩ h₂ell y hy]
    have hmod : 2 ∣ -k := by
      rw [Int.ModEq] at h₈
      omega
    have hred : (PadicInt.toZModPow 1 : ℤ_[2] →+* ZMod (2 ^ 1)) ((-k : ℤ) : ℤ_[2]) = 0 := by
      rw [map_intCast, ZMod.intCast_zmod_eq_zero_iff_dvd]
      exact hmod
    rw [ite_eq_left hred]
    exact one_ne_zero

private theorem nilSupport {D : ℕ} (hD : 0 < D) (hc : D.Coprime m) (hm : 0 < m)
    (hms : Squarefree m) (hn : Visibility.nrd x = (m * D : ℕ))
    (q : Prime) (hq : q.val ≠ ell) (hq₂ : q.val ≠ 2) (hqN : ¬ q.val ∣ N) (hqm : q.val ∣ m) :
    (nilSchwartz q.val (splitVector h hN z x hx q hq) : O) ≠ 0 ↔
      atRep z q (affineGenerator x) ∈ (levelRing h hN).completion q.val := by
  let E := splitChart ell h q hq
  let X := splitVector h hN z x hx q hq
  have hE : X.val = E (atRep z q x) := rfl
  have hcast : ∀ A : Mat ℤ_[q.val], integralMat q.val A = X.val →
      (A.det : ℚ_[q.val]) = (m * D : ℕ) := by
    intro A hA
    have hmap : (A.det : ℚ_[q.val]) = (integralMat q.val A).det :=
      RingHom.map_det (PadicInt.Coe.ringHom (p := q.val)) A
    rw [hmap, hA, hE, (split_invariants _ _ E _).2]
    change reducedNorm _ _ (atRep z q x) = _
    calc
      _ = (Visibility.nrd x : ℚ_[_]) := norm_atRep z _ x
      _ = _ := by rw [hn, Rat.cast_natCast]
  rw [← affine_mem_at_odd z q hq₂ x]
  unfold nilSchwartz
  rw [extend_nonzero _ (integralZero_openEmbedding q.val).injective]
  rw [levelOrder_completion, levelLocal_mem_split ell h N q hq]
  constructor
  · rintro ⟨A, hA, -⟩
    refine ⟨A.val, ?_, congrArg Subtype.val hA⟩
    change (q.val : ℤ_[q.val]) ^ N.factorization q.val ∣ A.val 1 0
    simp [Nat.factorization_eq_zero_of_not_dvd hqN]
  · rintro ⟨A, -, hA⟩
    have htr : A.trace = 0 := PadicInt.coe_eq_zero.mp (by
      rw [← integralMat_trace, show integralMat q.val A = X.val from hA, X.prop])
    let Y : TraceZero ℤ_[q.val] := ⟨A, htr⟩
    refine ⟨Y, Subtype.ext hA, (nilWeight_nonzero_iff Y).mpr ((nilSupport_valuation Y).mpr ?_)⟩
    have hd : ¬ q.val ∣ D := by
      intro hd
      have hn := Nat.dvd_gcd hd hqm
      rw [hc.gcd_eq_one] at hn
      exact q.prop.not_dvd_one hn
    have hval : padicValNat q.val m = 1 := by
      have h₁ := one_le_padicValNat_of_dvd hm.ne' hqm
      have h₂ : ¬ 2 ≤ padicValNat q.val m := by
        intro h₂
        have hs := (padicValNat_dvd_iff_le hm.ne').mpr h₂
        exact q.prop.ne_one (Nat.isUnit_iff.mp (hms q.val (by simpa only [pow_two] using hs)))
      omega
    have hy : A.det = ((m * D : ℕ) : ℤ_[q.val]) := by
      apply Subtype.val_injective
      exact hcast A hA
    change A.det.valuation = 1
    apply Nat.cast_injective (R := ℤ)
    rw [← PadicInt.valuation_coe, hy, PadicInt.coe_natCast, Padic.valuation_natCast,
      padicValNat.mul hm.ne' hD.ne', hval, padicValNat.eq_zero_of_not_dvd hd, add_zero]

include hx in
private theorem divisionSupport {D : ℕ} (hn : Visibility.nrd x = (m * D : ℕ))
    (hu : ¬ ell ∣ m * D) :
    (divisionFactor h (atRep z ⟨ell, Fact.out⟩ x) : O) ≠ 0 ↔
      atRep z ⟨ell, Fact.out⟩ (affineGenerator x) ∈ (levelRing h hN).completion ell := by
  let : Fact (ell % 4 = 3) := ⟨h⟩
  let q : Prime := ⟨ell, Fact.out⟩
  have hne : ell ≠ 2 := by intro he; rw [he] at h; norm_num at h
  rw [← affine_mem_at_odd z q hne x]
  let t := atRep z q x
  have ht : t.re = 0 := by rw [atRep_re, hx, Rat.cast_zero]
  let E := DivisionJoin.ambientEquiv ell
  let C := LocalDivision.coordinates ell
  let X : C.RationalZero := ⟨E t, by
    change LocalDivision.tr (E t) = 0
    rw [DivisionJoin.ambient_trace, DivisionJoin.reducedTrace, ht, mul_zero]⟩
  have he : LocalDivision.nrd (E t) = (m * D : ℕ) := by
    rw [DivisionJoin.ambient_norm]
    change reducedNorm _ _ (atRep z q x) = _
    calc
      _ = (Visibility.nrd x : ℚ_[_]) := norm_atRep z _ x
      _ = _ := by rw [hn, Rat.cast_natCast]
  have hnorm : ‖LocalDivision.nrd (E t)‖ = 1 := by
    rw [he]
    exact Padic.norm_natCast_eq_one_iff.mpr
      ((Fact.out : ell.Prime).coprime_iff_not_dvd.mpr hu)
  have hmem : t ∈ (levelRing h hN).completion ell := by
    rw [divisionCompletion ell h N hN]
    have hm : E t ∈ LocalDivision.order ell :=
      (LocalDivision.mem_order_iff_nrd _).mpr hnorm.le
    rw [← DivisionJoin.completion_map ell h] at hm
    obtain ⟨y, hy, hy'⟩ := hm
    exact E.injective hy' ▸ hy
  change (divisionFactor h t : O) ≠ 0 ↔ t ∈ _
  refine ⟨fun _ => hmem, fun _ => ?_⟩
  simp only [divisionFactor, dite_eq_left ht]
  change C.divisionSchwartz X ≠ 0
  let y : C.IntegralZero := ⟨⟨E t, (LocalDivision.mem_order_iff_nrd _).mpr hnorm.le⟩, X.prop⟩
  unfold DivisionCoordinates.divisionSchwartz
  rw [extend_nonzero _ C.zeroInclusion_openEmbedding.injective]
  refine ⟨y, rfl, (LocalDivision.divisionWeight_nonzero_iff y.val y.prop).mpr ?_⟩
  intro hz
  exact (LocalDivision.red_nonunit y.val).mp hz
    ((LocalDivision.orderUnit_iff_norm y.val).mpr hnorm)

variable (C : LevelRoots O N) (hne : 2 * m * N * ell ≠ 0)

/-- The sphere hypotheses govern both directions of the support test.
The parentheses put the equivalence in the consequent of both implications. -/
def FilteredSupport : Prop :=
  ∀ (i : ClassSet (levelRing h hN)) (D : ℕ) (k : ℤ),
    RequestedIndices (ell := ell) (m := m) D k → LevelFilter (N := N) (m := m) D →
    ∀ (x : B (-1) (-(ell : ℚ))), x.re = 0 → Visibility.nrd x = (m * D : ℕ) →
      (schwartz h C m hN hne i x ≠ 0 ↔
        HalfIntegral ((representative i).val.leftOrder (by norm_num) level_neg) x)

set_option maxHeartbeats 800000 in
/-- The unmodified odd filter gives the exact exceptional-place support tests,
hence support of the actual global product is half-integrality. -/
theorem filteredSupport (H : DiscriminantData m N ell) :
    FilteredSupport h hN C hne := by
  intro i D k hD hF x hx hn
  obtain ⟨hD, hDs, hc, hell, hk, h₈⟩ := hD
  obtain ⟨hcN, hsplit⟩ := hF
  let z := classRepresentative i
  have hm : 0 < m := by have := H.odd; omega
  have h₂ell : 2 ≠ ell := by intro he; rw [← he] at h; norm_num at h
  have h_ellD : ¬ ell ∣ D :=
    prime_not_dvd_of_symbol_ne_zero ⟨ell, Fact.out⟩ D (by
      change jacobiSym (-(D : ℤ)) ell ≠ 0
      rw [show -(D : ℤ) = -1 * (D : ℤ) by ring, jacobiSym.mul_left, hell, mul_one]
      apply jacobiSym.ne_zero
      simp)
  have h_ellm : ¬ ell ∣ m := prime_not_dvd_of_symbol_ne_zero ⟨ell, Fact.out⟩ m
    (by change jacobiSym (-(m : ℤ)) ell ≠ 0; rw [H.inert]; decide)
  apply weight_support_iff_halfIntegral (by norm_num) level_neg
  · apply (mem_exceptionalPlaces m N ell hne _).mpr
    exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_left (dvd_mul_right 2 m) N) ell
  · intro q hq
    change localFactor h C m q (atRep z q x) ≠ 0 ↔ _
    by_cases he : q.val = ell
    · have he' : q = ⟨ell, Fact.out⟩ := Subtype.ext he
      subst q
      simp only [localFactor, dite_true]
      exact divisionSupport h hN z x hx hn
        (fun hd => ((Fact.out : ell.Prime).dvd_mul.mp hd).elim h_ellm h_ellD)
    · have htr : (atRep z q x).re = 0 := by rw [atRep_re, hx, Rat.cast_zero]
      simp only [localFactor, dite_eq_right he, splitFactor, dite_eq_left htr]
      by_cases hqN : q.val ∣ N
      · rw [dite_eq_left hqN]
        apply levelSupport h hN z x hx C hn hk q he hqN
        intro hd
        rcases q.prop.dvd_mul.mp hd with hd | hd
        · exact (discriminantDisjoint H q hd).2.1 hqN
        · exact q.prop.not_dvd_one (hcN.gcd_eq_one ▸ Nat.dvd_gcd hd hqN)
      · rw [dite_eq_right hqN]
        by_cases h₂ : q.val = 2
        · have he' : q = ⟨2, Nat.prime_two⟩ := Subtype.ext h₂
          subst q
          simp only [dite_true]
          exact dyadicSupport h hN z x hx hn hk h₈ hqN h₂ell
        · simp only [dite_eq_right h₂]
          have hqm : q.val ∣ m := by
            have hh := (mem_exceptionalPlaces m N ell hne q).mp hq
            have hh' := (q.prop.dvd_mul.mp hh).resolve_right
              (fun he' => he ((Nat.prime_dvd_prime_iff_eq q.prop Fact.out).mp he'))
            have hh'' := (q.prop.dvd_mul.mp hh').resolve_right hqN
            exact (q.prop.dvd_mul.mp hh'').resolve_left
              (fun he' => h₂ ((Nat.prime_dvd_prime_iff_eq q.prop Nat.prime_two).mp he'))
          rw [ite_eq_left hqm]
          exact nilSupport h hN z x hx hD hc hm H.squarefree hn q he h₂ hqN hqm

end ZInQ.Manuscript.RC.ThetaClose
