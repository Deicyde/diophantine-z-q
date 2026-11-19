import Mathlib.Analysis.Complex.UpperHalfPlane.MoebiusAction
import Mathlib.NumberTheory.Divisors
import ZInQKernel.Contrib.TauCeti.NumberTheory.ModularForms.CongruenceSubgroups.Basic

/-! Row reduction for the triangular representatives in `ShimuraSteps.IsXi`. -/

noncomputable section

namespace ShimuraSteps.Orbits

open Matrix Matrix.SpecialLinearGroup CongruenceSubgroup UpperHalfPlane
open scoped MatrixGroups

abbrev Mat := Matrix (Fin 2) (Fin 2) ℤ

def tri (a b d : ℤ) : Mat := !![a, b; 0, d]

@[simp] theorem det_tri (a b d : ℤ) : (tri a b d).det = a * d := by
  simp [tri, Matrix.det_fin_two]

abbrev Div (N n : ℕ) := ↥(n.divisors.filter fun a => a.Coprime N)
abbrev Rep (N n : ℕ) := Σ a : Div N n, Fin (n / a.val)

theorem div_spec {N n : ℕ} (a : Div N n) :
    0 < a.val ∧ 0 < n / a.val ∧ a.val * (n / a.val) = n ∧ a.val.Coprime N := by
  obtain ⟨hd, hc⟩ := Finset.mem_filter.1 a.property
  obtain ⟨hv, hn⟩ := Nat.mem_divisors.1 hd
  have he := Nat.mul_div_cancel' hv
  exact ⟨Nat.pos_of_dvd_of_pos hv (Nat.pos_of_ne_zero hn),
    Nat.pos_of_ne_zero (fun h => hn (by simpa [h] using he.symm)), he, hc⟩

def repOf {N n : ℕ} (hn : n ≠ 0) (a d : ℕ) (h : a * d = n) (hc : a.Coprime N)
    (b : Fin d) : Rep N n :=
  let hv : a ∣ n := ⟨d, h.symm⟩
  let ha : 0 < a := Nat.pos_of_dvd_of_pos hv (Nat.pos_of_ne_zero hn)
  ⟨⟨a, Finset.mem_filter.mpr ⟨Nat.mem_divisors.mpr ⟨hv, hn⟩, hc⟩⟩,
    finCongr (show d = n / a by rw [← h, Nat.mul_div_cancel_left _ ha]) b⟩

def repMat {N n : ℕ} (i : Rep N n) : Mat :=
  tri i.1.val i.2.val (n / i.1.val : ℕ)

@[simp] theorem det_repMat {N n : ℕ} (i : Rep N n) : (repMat i).det = n := by
  rw [repMat, det_tri, ← Nat.cast_mul, (div_spec i.1).2.2.1]

@[simp] theorem repMat_repOf {N n : ℕ} (hn : n ≠ 0) (a d : ℕ) (h : a * d = n)
    (hc : a.Coprime N) (b : Fin d) : repMat (repOf hn a d h hc b) = tri a b.val d := by
  have ha : 0 < a := Nat.pos_of_dvd_of_pos ⟨d, h.symm⟩ (Nat.pos_of_ne_zero hn)
  have hd : n / a = d := by rw [← h, Nat.mul_div_cancel_left _ ha]
  unfold repMat repOf
  simp only [finCongr_apply_coe, hd]

/-- A matrix whose first column reduces to a unit times the first basis vector has
an eligible triangular form. The left factor is in Γ₀(N). -/
theorem exists_reduce {N n : ℕ} {A : Mat} (hn : 0 < n) (hdet : A.det = n)
    (hc : (A 1 0 : ZMod N) = 0) (hu : IsUnit (A 0 0 : ZMod N)) :
    ∃ (l : Gamma0 N) (i : Rep N n), A = (↑(l : SL(2, ℤ)) : Mat) * repMat i := by
  let a := Int.gcd (A 0 0) (A 1 0)
  have ha : 0 < a := by
    by_contra! h
    have hz : a = 0 := by omega
    have h₀ := Int.gcd_dvd_left (A 0 0) (A 1 0)
    have h₁ := Int.gcd_dvd_right (A 0 0) (A 1 0)
    change (a : ℤ) ∣ A 0 0 at h₀
    change (a : ℤ) ∣ A 1 0 at h₁
    rw [hz, Nat.cast_zero, zero_dvd_iff] at h₀ h₁
    rw [Matrix.det_fin_two, h₀, h₁, zero_mul, mul_zero, sub_zero] at hdet
    omega
  obtain ⟨u, hu'⟩ : (a : ℤ) ∣ A 0 0 := Int.gcd_dvd_left _ _
  obtain ⟨v, hv'⟩ : (a : ℤ) ∣ A 1 0 := Int.gcd_dvd_right _ _
  let x := Int.gcdA (A 0 0) (A 1 0)
  let y := Int.gcdB (A 0 0) (A 1 0)
  have hbez : (a : ℤ) = A 0 0 * x + A 1 0 * y := Int.gcd_eq_gcd_ab _ _
  have ha' : (a : ℤ) ≠ 0 := by exact_mod_cast ha.ne'
  have hxy : u * x + v * y = 1 := by
    apply mul_left_cancel₀ ha'
    rw [mul_one]
    linear_combination -hbez - x * hu' - y * hv'
  have hau : IsUnit (a : ZMod N) := by
    have h := congrArg (Int.cast : ℤ → ZMod N) hu'
    push_cast at h
    rw [h] at hu
    exact isUnit_of_mul_isUnit_left hu
  have hv0 : (v : ZMod N) = 0 := by
    have h := congrArg (Int.cast : ℤ → ZMod N) hv'
    push_cast at h
    rw [hc] at h
    exact hau.mul_left_cancel (h.symm.trans (mul_zero _).symm)
  let D : ℤ := u * A 1 1 - v * A 0 1
  let B : ℤ := x * A 0 1 + y * A 1 1
  have hAD : (a : ℤ) * D = n := by
    rw [det_fin_two, hu', hv'] at hdet
    dsimp [D]
    linear_combination hdet
  have hD : 0 < D := by
    have : (0 : ℤ) < n := by exact_mod_cast hn
    exact pos_of_mul_pos_right (hAD ▸ this) (by positivity)
  let d := D.toNat
  have hd : (d : ℤ) = D := Int.toNat_of_nonneg hD.le
  have had : a * d = n := by
    have he : (a : ℤ) * (d : ℤ) = n := by rw [hd, hAD]
    exact_mod_cast he
  let r := B % D
  let q := B / D
  have hq : q * D + r = B := by
    dsimp [q, r]
    rw [mul_comm, add_comm]
    exact Int.emod_add_mul_ediv _ _
  have hr0 : 0 ≤ r := Int.emod_nonneg _ hD.ne'
  have hrD : r < D := Int.emod_lt_of_pos _ hD
  have hr : (r.toNat : ℤ) = r := Int.toNat_of_nonneg hr0
  let b : Fin d := ⟨r.toNat, by omega⟩
  let i := repOf hn.ne' a d had ((ZMod.isUnit_iff_coprime _ _).1 hau) b
  let L : Mat := !![u, u * q - y; v, v * q + x]
  have hL : L.det = 1 := by
    simp only [L, det_fin_two, of_apply, Fin.isValue, cons_val_zero, cons_val_one]
    linear_combination hxy
  let l : Gamma0 N := ⟨⟨L, hL⟩, Gamma0_mem.mpr hv0⟩
  refine ⟨l, i, ?_⟩
  change A = L * repMat i
  rw [show repMat i = tri a b.val d from repMat_repOf _ _ _ _ _ _, show (b.val : ℤ) = r from hr, hd]
  rw [show L = !![u, u * q - y; v, v * q + x] from rfl, tri, Matrix.mul_fin_two]
  ext j k
  dsimp [D, B] at hq
  fin_cases j <;> fin_cases k <;> simp [D]
  · linear_combination hu'
  · linear_combination -u * hq - (A 0 1) * hxy
  · linear_combination hv'
  · linear_combination -v * hq - (A 1 1) * hxy

/-- The positive diagonal and reduced offset are unique under left multiplication by SL₂(ℤ). -/
theorem reduce_unique {N n : ℕ} {i j : Rep N n} (l : SL(2, ℤ))
    (h : (↑l : Mat) * repMat i = repMat j) : i = j := by
  have he (r c : Fin 2) := congrArg (fun M : Mat => M r c) h
  have h₀ : l 0 0 * (i.1.val : ℤ) = j.1.val := by
    simpa [repMat, tri, Matrix.mul_apply, Fin.sum_univ_two] using he 0 0
  have h₁ : l 1 0 * (i.1.val : ℤ) = 0 := by
    simpa [repMat, tri, Matrix.mul_apply, Fin.sum_univ_two] using he 1 0
  have hi := (div_spec i.1).1
  have hj := (div_spec j.1).1
  have hc : l 1 0 = 0 := (mul_eq_zero.mp h₁).resolve_right (by exact_mod_cast hi.ne')
  have hd := l.fin_two_mul_sub_mul_eq_one
  rw [hc, mul_zero, sub_zero] at hd
  have hpos : 0 < l 0 0 := by
    by_contra! hh
    have hi' : (0 : ℤ) ≤ i.1.val := by positivity
    have hj' : (0 : ℤ) < j.1.val := by exact_mod_cast hj
    linarith [mul_nonpos_of_nonpos_of_nonneg hh hi']
  have hl : l 0 0 = 1 := by
    rcases Int.eq_one_or_neg_one_of_mul_eq_one hd with h | h <;> omega
  rw [hl, one_mul] at h₀
  have hfirst : i.1 = j.1 := Subtype.ext (by exact_mod_cast h₀)
  obtain ⟨a, b⟩ := i
  obtain ⟨a', b'⟩ := j
  change a = a' at hfirst
  subst a'
  have hoff : (b.val : ℤ) + l 0 1 * (n / a.val : ℕ) = b'.val := by
    simpa [repMat, tri, Matrix.mul_apply, Fin.sum_univ_two, hl] using he 0 1
  have hdiv : ((n / a.val : ℕ) : ℤ) ∣ (b'.val : ℤ) - b.val :=
    ⟨l 0 1, by linear_combination -hoff⟩
  have hlt : |(b'.val : ℤ) - b.val| < (n / a.val : ℕ) := by
    have := b.isLt
    have := b'.isLt
    rw [abs_lt]
    omega
  have := Int.eq_zero_of_abs_lt_dvd hdiv hlt
  have : b = b' := Fin.ext (by omega)
  subst b'
  rfl

/-- Real linear fractional action of a positive determinant integral matrix. -/
def matGL (A : Mat) (h : 0 < A.det) : GL (Fin 2) ℝ :=
  .mkOfDetNeZero (A.map (Int.cast : ℤ → ℝ)) (by
    change (((Int.castRingHom ℝ).mapMatrix A).det) ≠ 0
    rw [← RingHom.map_det]
    exact Int.cast_ne_zero.mpr h.ne')

theorem matGL_mul (A B : Mat) (ha : 0 < A.det) (hb : 0 < B.det) :
    matGL (A * B) (by rw [Matrix.det_mul]; positivity) = matGL A ha * matGL B hb := by
  apply Units.ext
  exact Matrix.map_mul (f := Int.castRingHom ℝ)

theorem matGL_sl (g : SL(2, ℤ)) :
    matGL (g : Mat) (by rw [g.2]; decide) = mapGL ℝ g := by
  apply Units.ext
  rfl

#print axioms det_tri
#print axioms div_spec
#print axioms det_repMat
#print axioms repMat_repOf
#print axioms exists_reduce
#print axioms reduce_unique
#print axioms matGL_mul
#print axioms matGL_sl

end ShimuraSteps.Orbits
