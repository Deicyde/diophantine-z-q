import ZInQKernel.Contrib.OneProof.RC.LocalWeights.Level
import ZInQKernel.Contrib.OneProof.RC.LocalWeights.Compact

/-! Unit conjugation, affine scaling and the congruence bound, tex 8502–8504,
8512–8515, 8525–8531. The congruence bound in affine coordinates is provenance (c). -/

namespace ZInQ.Manuscript.RC.LocalWeights

open Matrix

variable {p : ℕ} [Fact p.Prime] {e : ℕ}
variable {O : Type*} [CommRing O]

local notation "red" => PadicInt.toZModPow

/-- Precision at most (k) in the affine coordinate: every selected root branch
has the same value modulo (p^k) whenever the two matrices do. -/
theorem levelRoot_congr {y z : eichler p e} {a b : ℤ_[p]} (ha : LevelRoot y a)
    (hb : LevelRoot z b) (he : 0 < e) {k : ℕ} (hk : 0 < k)
    (h : redMat p k y.val = redMat p k z.val) : red k a = red k b := by
  have hentries (i j : Fin 2) : red k (y.val i j) = red k (z.val i j) :=
    congrFun (congrFun h i) j
  have hdet : red k y.val.det = red k z.val.det := by
    simp only [Matrix.det_fin_two, map_mul, map_sub]
    rw [hentries 0 0, hentries 1 1, hentries 0 1, hentries 1 0]
  have hOne (a b : ℤ_[p]) (n : ℕ) (hn : 0 < n) (hh : red n a = red n b) :
      red 1 a = red 1 b := by
    rw [← PadicInt.cast_toZModPow 1 n hn a, ← PadicInt.cast_toZModPow 1 n hn b, hh]
  refine branch_congr k ha.1 hb.1 ha.2.1 ?_ hdet
  exact (hOne _ _ e he ha.2.2).trans
    ((hOne _ _ k hk (hentries 1 1)).trans (hOne _ _ e he hb.2.2).symm)

/-- A character modulo (p^k) gives a weight modulo (p^k) on the affine order
((k=1) for odd level primes and (k=2) for dyadic level). -/
theorem levelWeight_congr (he : 0 < e) {k : ℕ} (hk : 0 < k)
    (χ : (ZMod (p ^ k))ˣ →* Oˣ) {y z : eichler p e}
    (hy : y.val.trace = 1) (hz : z.val.trace = 1)
    (h : redMat p k y.val = redMat p k z.val) :
    levelWeight (χ.comp (Units.map (red k).toMonoidHom)) y =
      levelWeight (χ.comp (Units.map (red k).toMonoidHom)) z := by
  have h11 : red 1 (y.val 1 1) = red 1 (z.val 1 1) := by
    have heq := congrFun (congrFun h 1) 1
    change red k (y.val 1 1) = red k (z.val 1 1) at heq
    rw [← PadicInt.cast_toZModPow 1 k hk (y.val 1 1),
      ← PadicInt.cast_toZModPow 1 k hk (z.val 1 1), heq]
  have hu : IsUnit (2 * y.val 1 1 - 1) ↔ IsUnit (2 * z.val 1 1 - 1) := by
    simp only [unit_iff_red_ne_zero, map_sub, map_mul, h11]
  by_cases hunit : IsUnit (2 * y.val 1 1 - 1)
  · obtain ⟨a, ha, -⟩ := (levelRoot_existsUnique he y hy).mpr hunit
    obtain ⟨b, hb, -⟩ := (levelRoot_existsUnique he z hz).mpr (hu.mp hunit)
    rw [levelWeight_eq he _ hy ha, levelWeight_eq he _ hz hb]
    have hroot := levelRoot_congr ha hb he hk h
    have hm : Units.map (red k).toMonoidHom ha.2.1.unit =
        Units.map (red k).toMonoidHom hb.2.1.unit := by
      apply Units.ext
      change red k ha.2.1.unit.val = red k hb.2.1.unit.val
      simp only [IsUnit.unit_spec, map_sub, map_mul, hroot]
    simp only [MonoidHom.comp_apply, hm]
  · have hp (u : eichler p e) (htr : u.val.trace = 1) (hn : ¬ IsUnit (2 * u.val 1 1 - 1)) :
        ¬ ∃ a, LevelRoot u a ∧ u.val.trace = 1 := by
      rintro ⟨a, ha, -⟩
      have heq : red 1 a = red 1 (u.val 1 1) := by
        rw [← PadicInt.cast_toZModPow 1 e he a, ← PadicInt.cast_toZModPow 1 e he (u.val 1 1),
          ha.2.2]
        rfl
      apply hn
      simpa only [unit_iff_red_ne_zero, map_sub, map_mul, heq] using ha.2.1
    rw [levelWeight, dite_eq_right (hp y hy hunit), levelWeight,
      dite_eq_right (hp z hz (mt hu.mpr hunit))]

/-- Unit conjugation fixes the positive-level weight. -/
theorem levelWeight_conj (he : 0 < e) (χ : ℤ_[p]ˣ →* Oˣ)
    (u : (eichler p e)ˣ) (y : eichler p e) :
    levelWeight χ ((↑u⁻¹ : eichler p e) * y * (↑u : eichler p e)) = levelWeight χ y := by
  let z := (↑u⁻¹ : eichler p e) * y * (↑u : eichler p e)
  change levelWeight χ z = levelWeight χ y
  let v : (Mat ℤ_[p])ˣ := Units.map (eichler p e).val.toMonoidHom u
  have ht : z.val.trace = y.val.trace := Matrix.trace_units_conj' v y.val
  by_cases h : ∃ a, LevelRoot y a ∧ y.val.trace = 1
  · obtain ⟨a, ha, hy⟩ := h
    have hz : LevelRoot z a := (levelRoot_conj u y a).mpr ha
    rw [levelWeight_eq he χ (ht.trans hy) hz, levelWeight_eq he χ hy ha]
  · have hz : ¬ ∃ a, LevelRoot z a ∧ z.val.trace = 1 := by
      rintro ⟨a, ha, htr⟩
      exact h ⟨a, (levelRoot_conj u y a).mp ha, ht.symm.trans htr⟩
    rw [levelWeight, dite_eq_right hz, levelWeight, dite_eq_right h]

/-- The affine offset for unit scaling exists at every prime, including 2. -/
theorem affine_offset (v : ℤ_[p]ˣ) : ∃ t : ℤ_[p], (2 : ℤ_[p]) * t = 1 - v.val := by
  by_cases h : p = 2
  · subst p
    have hv : PadicInt.toZMod v.val = 1 := by
      have hu := (v.isUnit.map (PadicInt.toZMod : ℤ_[2] →+* ZMod 2)).ne_zero
      generalize PadicInt.toZMod v.val = a at *
      fin_cases a
      · exact False.elim (hu rfl)
      · rfl
    have hd : ((2 : ℕ) : ℤ_[2]) ∣ 1 - v.val := by
      rw [← Ideal.mem_span_singleton, ← PadicInt.maximalIdeal_eq_span_p, ← PadicInt.ker_toZMod,
        RingHom.mem_ker, map_sub, map_one, hv, sub_self]
    obtain ⟨t, ht⟩ := hd
    exact ⟨t, ht.symm⟩
  · have hu : IsUnit (2 : ℤ_[p]) := by
      rw [PadicInt.isUnit_iff]
      exact (PadicInt.norm_natCast_eq_one_iff (p := p) (n := 2)).mpr
        (((Fact.out : p.Prime).coprime_iff_not_dvd).mpr
          (fun h' => h (le_antisymm (Nat.le_of_dvd (by decide) h') (Fact.out : p.Prime).two_le)))
    obtain ⟨t, ht⟩ := (hu.dvd : (2 : ℤ_[p]) ∣ 1 - v.val)
    exact ⟨t, ht.symm⟩

/-- Affine form of (e_{vx}=v e_x+(1-v)/2). -/
noncomputable def affine (v t : ℤ_[p]) (y : eichler p e) : eichler p e :=
  v • y + algebraMap ℤ_[p] _ t

theorem affine_trace (v t : ℤ_[p]) (hv : 2 * t = 1 - v) (y : eichler p e)
    (hy : y.val.trace = 1) : (affine v t y).val.trace = 1 := by
  change (v • y.val + algebraMap ℤ_[p] (Mat ℤ_[p]) t).trace = 1
  rw [Matrix.trace_add, Matrix.trace_smul, hy, smul_eq_mul, mul_one]
  simp only [Matrix.trace_fin_two, Matrix.algebraMap_matrix_apply, ↓reduceIte]
  linear_combination hv

theorem affine_det (v t : ℤ_[p]) {y : eichler p e} (hy : y.val.trace = 1) :
    (affine v t y).val.det = v ^ 2 * y.val.det + v * t + t ^ 2 := by
  change (v • y.val + algebraMap ℤ_[p] (Mat ℤ_[p]) t).det = _
  rw [Matrix.trace_fin_two] at hy
  simp only [Matrix.det_fin_two, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul,
    Matrix.algebraMap_matrix_apply, Fin.zero_ne_one, Ne.symm (Fin.zero_ne_one : (0 : Fin 2) ≠ 1),
    ↓reduceIte, add_zero]
  linear_combination v * t * hy

theorem affine_root (v : ℤ_[p]ˣ) (t : ℤ_[p]) (hv : 2 * t = 1 - v.val)
    {y : eichler p e} (hy : y.val.trace = 1)
    {a : ℤ_[p]} (ha : LevelRoot y a) :
    LevelRoot (affine v.val t y) (v.val * a + t) := by
  have hgap : 2 * (v.val * a + t) - 1 = v.val * (2 * a - 1) := by
    linear_combination hv
  refine ⟨?_, hgap ▸ v.isUnit.mul ha.2.1, ?_⟩
  · rw [affine_det _ _ hy]
    linear_combination v.val ^ 2 * ha.1 + (v.val * a + t) * hv
  · change red e (v.val * a + t) = red e (v.val * y.val 1 1 + t)
    simp only [map_add, map_mul]
    rw [ha.2.2]
    rfl

/-- The scaling rule, where the offset is the integral half of (1-v). -/
theorem levelWeight_scale (he : 0 < e) (χ : ℤ_[p]ˣ →* Oˣ)
    (v : ℤ_[p]ˣ) (t : ℤ_[p]) (hv : 2 * t = 1 - v.val)
    (y : eichler p e) (hy : y.val.trace = 1) :
    levelWeight χ (affine v.val t y) = (χ v : O) * levelWeight χ y := by
  have hz := affine_trace v.val t hv y hy
  by_cases h : ∃ a, LevelRoot y a ∧ y.val.trace = 1
  · obtain ⟨a, ha, -⟩ := h
    have ha' := affine_root v t hv hy ha
    have hu : ha'.2.1.unit = v * ha.2.1.unit := by
      apply Units.ext
      simp only [IsUnit.unit_spec, Units.val_mul]
      linear_combination hv
    rw [levelWeight_eq he χ hz ha', levelWeight_eq he χ hy ha, hu, map_mul, Units.val_mul]
  · have hinv : (v⁻¹ : ℤ_[p]ˣ).val * v.val = 1 := Units.inv_mul v
    let t' := -(v⁻¹ : ℤ_[p]ˣ).val * t
    have hv' : 2 * t' = 1 - (v⁻¹ : ℤ_[p]ˣ).val := by
      change 2 * (-(v⁻¹ : ℤ_[p]ˣ).val * t) = _
      linear_combination -(v⁻¹ : ℤ_[p]ˣ).val * hv + hinv
    have hback : affine (v⁻¹ : ℤ_[p]ˣ).val t' (affine v.val t y) = y := by
      unfold affine
      rw [smul_add, smul_smul, hinv, one_smul, Algebra.smul_def (v⁻¹ : ℤ_[p]ˣ).val
          (algebraMap ℤ_[p] _ t), ← map_mul, add_assoc, ← map_add]
      simp [t']
    have hz' : ¬ ∃ a, LevelRoot (affine v.val t y) a ∧ (affine v.val t y).val.trace = 1 := by
      rintro ⟨a, ha, -⟩
      have hback' := affine_root v⁻¹ t' hv' hz ha
      rw [hback] at hback'
      exact h ⟨_, hback', hy⟩
    rw [levelWeight, dite_eq_right hz', levelWeight, dite_eq_right h, mul_zero]

/-- The weight modulo (p^k) is locally constant on the affine trace-one order. -/
theorem levelWeight_locallyConstant (he : 0 < e) {k : ℕ} (hk : 0 < k)
    (χ : (ZMod (p ^ k))ˣ →* Oˣ) :
    IsLocallyConstant (fun (y : {y : eichler p e // y.val.trace = 1}) =>
      levelWeight (χ.comp (Units.map (red k).toMonoidHom)) y.val) := by
  refine locallyConstant_of_factors
    ((redMat_locallyConstant p k).comp_continuous
      (continuous_subtype_val.comp continuous_subtype_val)) ?_
  exact fun y z h => levelWeight_congr he hk χ y.property z.property h

end ZInQ.Manuscript.RC.LocalWeights

open ZInQ.Manuscript.RC.LocalWeights
#print axioms levelRoot_congr
#print axioms levelWeight_congr
#print axioms levelWeight_conj
#print axioms affine_offset
#print axioms affine_trace
#print axioms affine_root
#print axioms affine_det
#print axioms levelWeight_scale
#print axioms levelWeight_locallyConstant
