import ZInQKernel.Contrib.OneProof.RC.ThetaClose.Assembly
import ZInQKernel.Contrib.OneProof.RC.PMAdelic.Geometry

/-! The two local normalizers and their signs (tex 9329–9364). -/

noncomputable section

open scoped Quaternion

namespace ZInQ.Manuscript.RC.O7Normalizers

open Adelic Eichler ThetaJoin LocalWeights Matrix

variable {ell N : ℕ} [Fact ell.Prime] (h : ell % 4 = 3) (hN : 0 < N)

abbrev detectingPrime (ell : ℕ) [Fact ell.Prime] : Prime := ⟨ell, Fact.out⟩

/-- Conjugation in the direction arising from right multiplication of an adele. -/
def rightConj {A : Type*} [Ring A] (u : Aˣ) (x : A) : A :=
  (↑u⁻¹ : A) * x * (u : A)

def splitUnit (q : Prime) (hq : q.val ≠ ell) : (Bp q.val (-1) (-(ell : ℚ)))ˣ :=
  Units.map (splitChart ell h q hq).symm.toMonoidHom (atkinMatrix q (N.factorization q.val))

def divisionUnit : (Bp ell (-1) (-(ell : ℚ)))ˣ :=
  letI : Fact (ell % 4 = 3) := ⟨h⟩
  Units.map (DivisionJoin.ambientEquiv ell).symm.toMonoidHom LocalDivision.uniformizer

theorem splitUnit_chart (q : Prime) (hq : q.val ≠ ell) :
    Units.map (splitChart ell h q hq).toMonoidHom (splitUnit (N := N) h q hq) =
      atkinMatrix q (N.factorization q.val) := by
  exact Units.ext ((splitChart ell h q hq).apply_symm_apply _)

theorem divisionUnit_chart :
    letI : Fact (ell % 4 = 3) := ⟨h⟩
    Units.map (DivisionJoin.ambientEquiv ell).toMonoidHom (divisionUnit h) =
      LocalDivision.uniformizer := by
  letI : Fact (ell % 4 = 3) := ⟨h⟩
  exact Units.ext ((DivisionJoin.ambientEquiv ell).apply_symm_apply _)

theorem map_rightConj {A B : Type*} [Ring A] [Ring B]
    (f : A →+* B) (u : Aˣ) (x : A) :
    f (rightConj u x) = rightConj (Units.map f.toMonoidHom u) (f x) := by
  simp only [rightConj, map_mul, Units.coe_map, ← map_inv]
  rfl

theorem splitUnit_mem (q : Prime) (hq : q.val ≠ ell) (x : Bp q.val (-1) (-(ell : ℚ))) :
    rightConj (splitUnit (N := N) h q hq) x ∈ (levelRing h hN).completion q.val ↔
      x ∈ (levelRing h hN).completion q.val := by
  simp only [levelRing, levelOrder_completion, levelLocal_mem_split ell h N q hq]
  let f := splitChart ell h q hq
  have hm := map_rightConj f.toRingHom (splitUnit (N := N) h q hq) x
  change f (rightConj _ x) = _ at hm
  rw [hm]
  have he := splitUnit_chart (N := N) h q hq
  change Units.map f.toRingHom.toMonoidHom _ = _ at he
  rw [he]
  exact atkinMatrix_conj q _ _

theorem divisionUnit_mem (x : Bp ell (-1) (-(ell : ℚ))) :
    rightConj (divisionUnit h) x ∈ (levelRing h hN).completion ell ↔
      x ∈ (levelRing h hN).completion ell :=
  Adelic.divisionUnit_normalizes ell h N hN x

theorem split_class (hcop : N.Coprime ell) (q : Prime) (hq : q.val ≠ ell)
    (he : 0 < N.factorization q.val) :
    rightClassPerm (single (levelRing h hN) q (splitUnit (N := N) h q hq))
      (normalizes_single q _ (splitUnit_mem h hN q hq)) =
        Adelic.atkin ell h N hN hcop q.val q.prop he := by
  rcases q with ⟨p, hp⟩
  rfl

theorem division_class :
    rightClassPerm (single (levelRing h hN) (detectingPrime ell) (divisionUnit h))
      (normalizes_single (detectingPrime ell) _ (divisionUnit_mem h hN)) =
        Adelic.uniformizer ell h N hN := rfl

/-- The split normalizer interchanges the diagonal entries and scales the
two off-diagonal entries by reciprocal powers of the uniformizer. -/
theorem swap_matrix (q : Prime) (e : ℕ) (Y : Mat ℚ_[q.val]) :
    rightConj (atkinMatrix q e) Y =
      !![Y 1 1, ((q.val : ℚ_[q.val]) ^ e)⁻¹ * Y 1 0;
        (q.val : ℚ_[q.val]) ^ e * Y 0 1, Y 0 0] := by
  let d : ℚ_[q.val] := (q.val : ℚ_[q.val]) ^ e
  change !![0, d⁻¹; 1, 0] * Y * !![0, 1; d, 0] =
    !![Y 1 1, d⁻¹ * Y 1 0; d * Y 0 1, Y 0 0]
  have hd : d ≠ 0 := pow_ne_zero _ (Nat.cast_ne_zero.mpr q.prop.ne_zero)
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Matrix.vecMul, dotProduct, Fin.sum_univ_two, ← mul_assoc, hd, mul_comm]

/-- Integral conjugation in the split chart. -/
def splitSwap (q : Prime) (e : ℕ) (Y : eichler q.val e) : eichler q.val e :=
  ⟨!![Y.val 1 1, Y.prop.choose; (q.val : ℤ_[q.val]) ^ e * Y.val 0 1, Y.val 0 0],
    dvd_mul_right _ _⟩

theorem splitSwap_cast (q : Prime) (e : ℕ) (Y : eichler q.val e) :
    matrixCast q.val (splitSwap q e Y).val =
      rightConj (atkinMatrix q e) (matrixCast q.val Y.val) := by
  rw [swap_matrix]
  have hd : (q.val : ℚ_[q.val]) ^ e ≠ 0 :=
    pow_ne_zero _ (Nat.cast_ne_zero.mpr q.prop.ne_zero)
  have hv : (Y.val 1 0 : ℚ_[q.val]) =
      (q.val : ℚ_[q.val]) ^ e * (Y.prop.choose : ℚ_[q.val]) := by
    simpa only [PadicInt.coe_mul, PadicInt.coe_pow, PadicInt.coe_natCast] using
      congrArg (fun z : ℤ_[q.val] => (z : ℚ_[q.val])) Y.prop.choose_spec
  ext i j
  fin_cases i <;> fin_cases j
  · rfl
  · change (Y.prop.choose : ℚ_[q.val]) = ((q.val : ℚ_[q.val]) ^ e)⁻¹ * (Y.val 1 0 : ℚ_[q.val])
    nth_rw 1 [hv]
    rw [← mul_assoc, inv_mul_cancel₀ hd, one_mul]
  · change (((q.val : ℤ_[q.val]) ^ e * Y.val 0 1 : ℤ_[q.val]) : ℚ_[q.val]) = _
    simp only [PadicInt.coe_mul, PadicInt.coe_pow, PadicInt.coe_natCast]
    rfl
  · rfl

theorem splitSwap_trace (q : Prime) (e : ℕ) (Y : eichler q.val e) :
    (splitSwap q e Y).val.trace = Y.val.trace := by
  simp [splitSwap, Matrix.trace_fin_two, add_comm]

theorem splitSwap_det (q : Prime) (e : ℕ) (Y : eichler q.val e) :
    (splitSwap q e Y).val.det = Y.val.det := by
  have hv : Y.val 1 0 = (q.val : ℤ_[q.val]) ^ e * Y.prop.choose := Y.prop.choose_spec
  rw [Matrix.det_fin_two, Matrix.det_fin_two]
  change Y.val 1 1 * Y.val 0 0 - Y.prop.choose * ((q.val : ℤ_[q.val]) ^ e * Y.val 0 1) =
    Y.val 0 0 * Y.val 1 1 - Y.val 0 1 * Y.val 1 0
  linear_combination Y.val 0 1 * hv

theorem splitSwap_level (q : Prime) (e : ℕ) (Y : eichler q.val e)
    (ht : Y.val.trace = 1) :
    level q.val e (splitSwap q e Y) = 1 - level q.val e Y := by
  rw [trace_fin_two] at ht
  have hdiag : Y.val 0 0 = 1 - Y.val 1 1 := eq_sub_of_add_eq ht
  change PadicInt.toZModPow e (Y.val 0 0) = 1 - PadicInt.toZModPow e (Y.val 1 1)
  rw [hdiag, map_sub, map_one]

theorem splitSwap_weight {O : Type*} [CommRing O] (q : Prime) (e : ℕ) (he : 0 < e)
    (χ : ℤ_[q.val]ˣ →* Oˣ) (Y : eichler q.val e) (ht : Y.val.trace = 1) :
    levelWeight χ (splitSwap q e Y) = (χ (-1) : O) * levelWeight χ Y := by
  have ht' := (splitSwap_trace q e Y).trans ht
  have hroot (a : ℤ_[q.val]) :
      LevelRoot (splitSwap q e Y) (1 - a) ↔ LevelRoot Y a := by
    have hg : 2 * (1 - a) - 1 = -(2 * a - 1) := by ring
    unfold LevelRoot
    rw [splitSwap_det, splitSwap_level q e Y ht, map_sub, map_one, hg, IsUnit.neg_iff,
      sub_right_inj, show (1 - a) ^ 2 - (1 - a) = a ^ 2 - a by ring]
  by_cases hs : ∃ a, LevelRoot Y a ∧ Y.val.trace = 1
  · obtain ⟨a, ha, -⟩ := hs
    have hb := (hroot a).mpr ha
    have hu : hb.2.1.unit = (-1) * ha.2.1.unit := by
      apply Units.ext
      simp only [Units.val_neg, IsUnit.unit_spec, neg_one_mul]
      ring
    rw [levelWeight_eq he χ ht' hb, levelWeight_eq he χ ht ha, hu, map_mul, Units.val_mul]
  · have hs' : ¬ ∃ a, LevelRoot (splitSwap q e Y) a ∧ (splitSwap q e Y).val.trace = 1 := by
      rintro ⟨a, ha, -⟩
      exact hs ⟨1-a, (hroot (1-a)).mp (by simpa using ha), ht⟩
    simp only [levelWeight, dite_eq_right hs, dite_eq_right hs', mul_zero]

theorem division_red_neg {p : ℕ} [Fact p.Prime] [Fact (p % 4 = 3)]
    (x : LocalDivision.order p) (hx : LocalDivision.tr x.val = 0) :
    LocalDivision.red (LocalDivision.uniformizerOrder x) = -LocalDivision.red x := by
  obtain ⟨t, ht⟩ := LocalDivision.trace_line x hx
  rw [LocalDivision.uniformizer_frobenius, ht, mul_pow, ← map_pow, ZMod.pow_card,
    LocalDivision.beta_frobenius, mul_neg]

end ZInQ.Manuscript.RC.O7Normalizers
