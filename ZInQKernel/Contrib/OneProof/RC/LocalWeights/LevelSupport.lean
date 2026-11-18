import ZInQKernel.Contrib.OneProof.RC.LocalWeights.LevelRules

/-!
# The split support and its projectors in the order

The equalities verify tex 8499–8504 and 8517–8531 in the affine coordinate.
The matrix calculations are provenance (c).
-/

namespace ZInQ.Manuscript.RC.LocalWeights

open Matrix

variable {p : ℕ} [Fact p.Prime] {e : ℕ}

local notation "red" => PadicInt.toZModPow

/-- A split unit eigenvalue gap for (y=(1+x)/2). -/
def SplitSupport (y : eichler p e) : Prop :=
  ∃ a : ℤ_[p], a ^ 2 - a + y.val.det = 0 ∧ IsUnit (2 * a - 1)

/-- At odd primes the affine lattice condition is just integral membership
of the trace-zero element in the order. -/
theorem odd_integral_half (hp : p ≠ 2) (x : eichler p e) (hx : x.val.trace = 0) :
    ∃! y : eichler p e, y.val.trace = 1 ∧ (2 : ℤ_[p]) • y - 1 = x := by
  have hu : IsUnit (2 : ℤ_[p]) := by
    rw [PadicInt.isUnit_iff]
    exact (PadicInt.norm_natCast_eq_one_iff (p := p) (n := 2)).mpr
      (((Fact.out : p.Prime).coprime_iff_not_dvd).mpr
        (fun h => hp (le_antisymm (Nat.le_of_dvd (by decide) h) (Fact.out : p.Prime).two_le)))
  let w : ℤ_[p] := (hu.unit⁻¹ : ℤ_[p]ˣ).val
  have hw : (2 : ℤ_[p]) * w = 1 :=
    (congrArg (· * w) hu.unit_spec.symm).trans (Units.mul_inv hu.unit)
  let y : eichler p e := w • (x + 1)
  have hy : (2 : ℤ_[p]) • y - 1 = x := by
    change (2 : ℤ_[p]) • (w • (x + 1)) - 1 = x
    rw [smul_smul, hw, one_smul, add_sub_cancel_right]
  have htr := congrArg (fun a : eichler p e => a.val.trace) hy
  change (((2 : ℤ_[p]) • y.val - 1).trace) = x.val.trace at htr
  rw [hx, Matrix.trace_sub, Matrix.trace_smul, Matrix.trace_one, Fintype.card_fin,
    Nat.cast_ofNat, sub_eq_zero, smul_eq_mul] at htr
  refine ⟨y, ⟨mul_left_cancel₀ (by norm_num : (2 : ℤ_[p]) ≠ 0) (htr.trans (mul_one _).symm),
    hy⟩, fun z hz => ?_⟩
  have hEq : (2 : ℤ_[p]) • z = (2 : ℤ_[p]) • y := sub_left_inj.mp (hz.2.trans hy.symm)
  have hback (a : eichler p e) : w • ((2 : ℤ_[p]) • a) = a := by
    rw [smul_smul, mul_comm, hw, one_smul]
  exact (hback z).symm.trans ((congrArg (w • ·) hEq).trans (hback y))

theorem splitSupport_selected (he : 0 < e) (y : eichler p e) (hy : y.val.trace = 1) :
    SplitSupport y ↔ ∃ a, LevelRoot y a := by
  refine ⟨?_, fun ⟨a, ha⟩ => ⟨a, ha.1, ha.2.1⟩⟩
  rintro ⟨a, ha, hu⟩
  have hd := level_residue_root y hy
  have hd' := congrArg (fun z : ZMod (p ^ e) => (ZMod.cast z : ZMod (p ^ 1))) hd
  rw [PadicInt.cast_toZModPow 1 e he] at hd'
  rw [ZMod.cast_zero] at hd'
  have ha' := congrArg (red 1 : ℤ_[p] →+* ZMod (p ^ 1)) ha
  simp only [map_sub, map_pow, map_add, map_zero] at ha' hd'
  have hsq : red 1 ((2 * y.val 1 1 - 1) ^ 2) = red 1 ((2 * a - 1) ^ 2) := by
    simp only [map_pow, map_mul, map_sub, map_ofNat, map_one]
    linear_combination 4 * hd' - 4 * ha'
  have hunit : IsUnit (2 * y.val 1 1 - 1) := by
    apply (isUnit_pow_iff (by decide : (2 : ℕ) ≠ 0)).mp
    rw [unit_iff_red_ne_zero, hsq, ← unit_iff_red_ne_zero]
    exact hu.pow 2
  obtain ⟨r, hr, -⟩ := (levelRoot_existsUnique he y hy).mpr hunit
  exact ⟨r, hr⟩

/-- The square of (x=2y-1) is the scalar (1-4det y). -/
theorem affine_square (y : eichler p e) (hy : y.val.trace = 1) :
    ((2 : ℤ_[p]) • y.val - 1) ^ 2 =
      algebraMap ℤ_[p] (Mat ℤ_[p]) (1 - 4 * y.val.det) := by
  have h11 : y.val 1 1 = 1 - y.val 0 0 := by
    rw [Matrix.trace_fin_two] at hy
    linear_combination hy
  apply Matrix.ext
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [pow_two, Matrix.mul_apply, Fin.sum_univ_two, Matrix.det_fin_two,
      Matrix.algebraMap_matrix_apply, Matrix.one_apply, h11] <;> ring

/-- The integral projectors come from the factorization of the trace-one
characteristic polynomial. This identity is the numerator identity. -/
theorem projector_numerator (y : eichler p e) (hy : y.val.trace = 1)
    (a : ℤ_[p]) (ha : a ^ 2 - a + y.val.det = 0) :
    let z := y.val - algebraMap ℤ_[p] (Mat ℤ_[p]) (1 - a)
    z * z = (2 * a - 1) • z := by
  have h11 : y.val 1 1 = 1 - y.val 0 0 := by
    rw [Matrix.trace_fin_two] at hy
    linear_combination hy
  simp only [Matrix.det_fin_two, h11] at ha
  dsimp only
  apply Matrix.ext
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.algebraMap_matrix_apply, h11]
  · linear_combination -ha
  · ring
  · ring
  · linear_combination -ha

/-- The projector onto the (a) eigensummand of (y), in the Eichler order. -/
noncomputable def projector {a : ℤ_[p]} (u : IsUnit (2 * a - 1)) (y : eichler p e) :
    eichler p e :=
  (↑u.unit⁻¹ : ℤ_[p]) • (y - algebraMap ℤ_[p] (eichler p e) (1 - a))

theorem projector_idempotent (y : eichler p e) (hy : y.val.trace = 1)
    {a : ℤ_[p]} (ha : a ^ 2 - a + y.val.det = 0) (u : IsUnit (2 * a - 1)) :
    projector u y * projector u y = projector u y := by
  let z := y.val - algebraMap ℤ_[p] (Mat ℤ_[p]) (1 - a)
  apply Subtype.ext
  change ((↑u.unit⁻¹ : ℤ_[p]) • z) * ((↑u.unit⁻¹ : ℤ_[p]) • z) = (↑u.unit⁻¹ : ℤ_[p]) • z
  have h := projector_numerator y hy a ha
  dsimp only at h
  change z * z = (2 * a - 1) • z at h
  have hmul : (↑u.unit⁻¹ : ℤ_[p]) * (2 * a - 1) = 1 :=
    (congrArg (fun x : ℤ_[p] => (↑u.unit⁻¹ : ℤ_[p]) * x) u.unit_spec).symm.trans (Units.inv_mul u.unit)
  rw [smul_mul_assoc, mul_smul_comm, h, smul_smul, smul_smul, mul_assoc, hmul, mul_one]

/-- The integral projector has image in the eigenspace for the chosen root. -/
theorem projector_eigen (y : eichler p e) (hy : y.val.trace = 1)
    {a : ℤ_[p]} (ha : a ^ 2 - a + y.val.det = 0) (u : IsUnit (2 * a - 1)) :
    y * projector u y = a • projector u y := by
  let z := y.val - algebraMap ℤ_[p] (Mat ℤ_[p]) (1 - a)
  have h : z * z = (2 * a - 1) • z := projector_numerator y hy a ha
  have hz : y.val = z + algebraMap ℤ_[p] (Mat ℤ_[p]) (1 - a) := (sub_add_cancel _ _).symm
  have he : y.val * z = a • z := by
    calc
      y.val * z = (z + algebraMap ℤ_[p] (Mat ℤ_[p]) (1 - a)) * z :=
        congrArg (· * z) hz
      _ = (2 * a - 1) • z + (1 - a) • z := by
        rw [add_mul, h, Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul]
      _ = a • z := by rw [← add_smul, show 2 * a - 1 + (1 - a) = a by ring]
  apply Subtype.ext
  change y.val * ((↑u.unit⁻¹ : ℤ_[p]) • z) = a • ((↑u.unit⁻¹ : ℤ_[p]) • z)
  rw [mul_smul_comm, he, smul_comm]

theorem level_scalar (e : ℕ) (a : ℤ_[p]) :
    level p e (algebraMap ℤ_[p] (eichler p e) a) = red e a := by
  change red e ((algebraMap ℤ_[p] (Mat ℤ_[p]) a) 1 1) = _
  rw [Matrix.algebraMap_matrix_apply, ite_eq_left rfl]
  rfl

/-- The chosen projector is the identity on the cyclic quotient; its
complement is zero there. In particular this fixes the dyadic selection. -/
theorem projector_level (y : eichler p e) {a : ℤ_[p]} (ha : LevelRoot y a) :
    level p e (projector ha.2.1 y) = 1 ∧
      level p e (1 - projector ha.2.1 y) = 0 := by
  have h : level p e (projector ha.2.1 y) = 1 := by
    let rinv : ℤ_[p] := ↑ha.2.1.unit⁻¹
    change level p e (rinv • (y - algebraMap ℤ_[p] (eichler p e) (1 - a))) = 1
    rw [Algebra.smul_def, map_mul, level_scalar, map_sub, ← ha.2.2, level_scalar,
      ← map_sub, ← map_mul]
    have he : a - (1 - a) = 2 * a - 1 := by ring
    have hm : rinv * (2 * a - 1) = 1 :=
      (congrArg (fun z : ℤ_[p] => rinv * z) ha.2.1.unit_spec).symm.trans (Units.inv_mul _)
    rw [he, hm, map_one]
  exact ⟨h, by rw [map_sub, map_one, h, sub_self]⟩

/-- The affine scaling preserves the projector itself, hence also its complement
even when the two dyadic eigenvalue parities switch. -/
theorem projector_affine (v : ℤ_[p]ˣ) (t : ℤ_[p]) (hv : 2 * t = 1 - v.val)
    {y : eichler p e} (hy : y.val.trace = 1) {a : ℤ_[p]} (ha : LevelRoot y a) :
    projector (affine_root v t hv hy ha).2.1 (affine v.val t y) = projector ha.2.1 y := by
  let u := (affine_root v t hv hy ha).2.1.unit
  let w := ha.2.1.unit
  have hu : u = v * w := by
    apply Units.ext
    change ((affine_root v t hv hy ha).2.1.unit : ℤ_[p]) = v.val * (ha.2.1.unit : ℤ_[p])
    rw [IsUnit.unit_spec, IsUnit.unit_spec]
    linear_combination hv
  have hnum :
      affine v.val t y - algebraMap ℤ_[p] (eichler p e) (1 - (v.val * a + t)) =
        v.val • (y - algebraMap ℤ_[p] (eichler p e) (1 - a)) := by
    rw [affine, add_sub_assoc, smul_sub, ← map_sub, sub_eq_add_neg
      (v.val • y), Algebra.smul_def v.val (algebraMap ℤ_[p] (eichler p e) (1 - a)),
      ← map_mul, ← map_neg]
    have h : t - (1 - (v.val * a + t)) = -(v.val * (1 - a)) := by linear_combination hv
    rw [h]
  change (u⁻¹ : ℤ_[p]ˣ).val • _ = (w⁻¹ : ℤ_[p]ˣ).val • _
  rw [hnum, smul_smul, hu, _root_.mul_inv_rev, Units.val_mul, mul_assoc, Units.inv_mul, mul_one]

/-- Level support at both odd and even primes is the unit-square condition
on (x=2y-1). The trace-one affine coordinate already imposes its integrality. -/
theorem splitSupport_square (y : eichler p e) (hy : y.val.trace = 1) :
    SplitSupport y ↔ ∃ r : ℤ_[p]ˣ, ((2 : ℤ_[p]) • y.val - 1) ^ 2 =
      algebraMap ℤ_[p] (Mat ℤ_[p]) (r.val ^ 2) := by
  rw [affine_square y hy]
  have hinj : Function.Injective (algebraMap ℤ_[p] (Mat ℤ_[p])) := by
    intro s t hst
    have ht := congrFun (congrFun hst 0) 0
    simpa [Matrix.algebraMap_matrix_apply] using ht
  constructor
  · rintro ⟨a, ha, hr⟩
    refine ⟨hr.unit, congrArg (algebraMap ℤ_[p] (Mat ℤ_[p])) ?_⟩
    rw [hr.unit_spec]
    linear_combination -4 * ha
  · rintro ⟨r, hr⟩
    obtain ⟨a, ha⟩ := affine_offset (-r)
    have hai : 2 * a - 1 = r.val := by
      change 2 * a = 1 - (-r.val) at ha
      linear_combination ha
    refine ⟨a, ?_, hai ▸ r.isUnit⟩
    have h := hinj hr
    rw [← hai] at h
    have hh : (4 : ℤ_[p]) * (a ^ 2 - a + y.val.det) = 0 := by linear_combination -h
    exact (mul_eq_zero.mp hh).resolve_left (by norm_num)

theorem levelWeight_nonzero_iff {O : Type*} [CommRing O] [Nontrivial O]
    (he : 0 < e) (χ : ℤ_[p]ˣ →* Oˣ) (y : eichler p e) (hy : y.val.trace = 1) :
    levelWeight χ y ≠ 0 ↔ SplitSupport y := by
  rw [splitSupport_selected he y hy]
  by_cases h : ∃ a, LevelRoot y a
  · obtain ⟨a, ha⟩ := h
    rw [levelWeight_eq he χ hy ha]
    exact ⟨fun _ => ⟨a, ha⟩, fun _ => (χ ha.2.1.unit).ne_zero⟩
  · rw [levelWeight, dite_eq_right (fun ⟨a, ha, _⟩ => h ⟨a, ha⟩)]
    exact ⟨fun hn => False.elim (hn rfl), fun hh => False.elim (h hh)⟩

end ZInQ.Manuscript.RC.LocalWeights

open ZInQ.Manuscript.RC.LocalWeights
#print axioms splitSupport_selected
#print axioms odd_integral_half
#print axioms affine_square
#print axioms projector_numerator
#print axioms projector_idempotent
#print axioms projector_eigen
#print axioms level_scalar
#print axioms projector_level
#print axioms projector_affine
#print axioms splitSupport_square
#print axioms levelWeight_nonzero_iff
