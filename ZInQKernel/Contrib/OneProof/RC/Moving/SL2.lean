import Mathlib

/-!
# Lane RC4 (moving character): the `SL₂(ℤ₂)` group theory behind (4.4c)

Manuscript (11/5 version), Proposition `ex:arith-moving-character`
("One moving character for the complete active list"), proof, tex lines 3597–3633.

Everything in this file is `PROVED`.  It is the finite and 2-adic matrix group theory with which
Elliot passes from the open image `Γ_d ⊂ J` (Serre) to the subgroup `Γ_ν ⊂ ρ_T(G_{L_∞})` of (4.4c),
with his constants `m = 2d + 2` and `ν = 4m + 2 = 8d + 10`:

* `U_V_U_V`          — the identity `U(a)V(b)U(−a/(1+ab))V(−b(1+ab)) = diag(1+ab,(1+ab)⁻¹)` (3610–3613);
* `gauss_decomp`     — Gaussian decomposition `A = V(c/a) D(a) U(b/a)` when `a` is a unit (3614);
* `Γ_two_mul_le`     — a subgroup containing `U(2^k ℤ₂), V(2^k ℤ₂)` contains `Γ_{2k}` (3614–3615);
* `sq_mem_of_index_le_two` — a subgroup of index at most two contains all squares (3606–3607);
* `Γ_two_mul_add_two_le` — `Γ_m ⊂ J_K` for `m = 2d + 2` (3607–3616);
* `commutator_D_U`, `commutator_D_V`, `Γ_four_mul_add_two_le_commutator` — commuting
  `diag(1+2^m,(1+2^m)⁻¹)` with level-`m` unipotents gives all level-`(2m+1)` unipotents, since
  `v₂((1+2^m)² − 1) = m + 1`, hence `Γ_{4m+2} ⊂ [J_K, J_K]` (3617–3623);
* `four_four_c`      — (4.4c): `Γ_{8d+10} ⊂ ρ(G_{L_∞})` for any group homomorphism `ρ` with
  `Γ_d ⊂ ρ(G)`, `G_{F_∞}` of index at most two and `G_{F_∞}/G_{L_∞}` abelian (3624–3633).

Remark on form.  Elliot writes `Γ_{4m+2} ⊂ \overline{[J_K,J_K]}` and then uses that the image of the
compact group `G_{L_∞}` is closed.  The decomposition argument he cites in fact writes every element
of `Γ_{4m+2}` as a product of six commutators, so the containment holds in the abstract commutator
subgroup itself; Lean proves that stronger form, from which his closure statement follows at once,
and the closedness step is not needed.  No topology enters.

`Γ_d` is the genuine kernel of `SL₂(ℤ₂) → SL₂(ℤ/2^d)` (Mathlib's `PadicInt.toZModPow`).
-/

open Matrix
open scoped MatrixGroups commutatorElement

namespace ZInQ.Manuscript.RC.Moving

noncomputable section

section General

variable {R : Type*} [CommRing R]

/-- The upper unipotent matrix `U(a) = [[1, a], [0, 1]]` (tex 3608). -/
def U (a : R) : SL(2, R) :=
  ⟨!![1, a; 0, 1], by simp [Matrix.det_fin_two_of]⟩

/-- The lower unipotent matrix `V(b) = [[1, 0], [b, 1]]` (tex 3608). -/
def V (b : R) : SL(2, R) :=
  ⟨!![1, 0; b, 1], by simp [Matrix.det_fin_two_of]⟩

/-- The diagonal matrix `D(v) = diag(v, v⁻¹)` (tex 3612, 3636). -/
def D (v : Rˣ) : SL(2, R) :=
  ⟨!![(v : R), 0; 0, ((v⁻¹ : Rˣ) : R)], by simp [Matrix.det_fin_two_of]⟩

/-- The matrix of `U(a)`. -/
@[simp] theorem U_coe (a : R) : ((U a : SL(2, R)) : Matrix (Fin 2) (Fin 2) R) = !![1, a; 0, 1] :=
  rfl

/-- The matrix of `V(b)`. -/
@[simp] theorem V_coe (b : R) : ((V b : SL(2, R)) : Matrix (Fin 2) (Fin 2) R) = !![1, 0; b, 1] :=
  rfl

/-- The matrix of `D(v)`. -/
@[simp] theorem D_coe (v : Rˣ) :
    ((D v : SL(2, R)) : Matrix (Fin 2) (Fin 2) R) = !![(v : R), 0; 0, ((v⁻¹ : Rˣ) : R)] :=
  rfl

/-- `U(a)U(b) = U(a+b)` (helper). -/
theorem U_mul_U (a b : R) : U a * U b = U (a + b) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two, add_comm]

/-- `V(a)V(b) = V(a+b)` (helper). -/
theorem V_mul_V (a b : R) : V a * V b = V (a + b) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two, add_comm]

/-- `U(0) = 1` (helper). -/
theorem U_zero : (U (0 : R)) = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp

/-- `V(0) = 1` (helper). -/
theorem V_zero : (V (0 : R)) = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp

/-- `U(a)⁻¹ = U(−a)` (helper). -/
theorem U_inv (a : R) : (U a)⁻¹ = U (-a) := by
  rw [eq_comm, ← mul_eq_one_iff_eq_inv, U_mul_U, neg_add_cancel, U_zero]

/-- `V(a)⁻¹ = V(−a)` (helper). -/
theorem V_inv (a : R) : (V a)⁻¹ = V (-a) := by
  rw [eq_comm, ← mul_eq_one_iff_eq_inv, V_mul_V, neg_add_cancel, V_zero]

/-- `D(v)D(w) = D(vw)` (helper). -/
theorem D_mul_D (v w : Rˣ) : D v * D w = D (v * w) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two, mul_comm]

/-- `D(1) = 1` (helper). -/
theorem D_one : D (1 : Rˣ) = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp

/-- `D(v)⁻¹ = D(v⁻¹)` (helper). -/
theorem D_inv (v : Rˣ) : (D v)⁻¹ = D v⁻¹ := by
  rw [eq_comm, ← mul_eq_one_iff_eq_inv, D_mul_D, inv_mul_cancel, D_one]

/-- `U(a)² = U(2a)` (tex 3608–3609: squares of level-`d` unipotents have level `d+1`). -/
theorem U_sq (a : R) : U a ^ 2 = U (2 * a) := by
  rw [sq, U_mul_U, two_mul]

/-- `V(a)² = V(2a)` (tex 3608–3609). -/
theorem V_sq (a : R) : V a ^ 2 = V (2 * a) := by
  rw [sq, V_mul_V, two_mul]

/-- Extensionality for `SL₂` by the four entries. -/
theorem SL2_ext {A B : SL(2, R)}
    (h00 : (A : Matrix (Fin 2) (Fin 2) R) 0 0 = (B : Matrix (Fin 2) (Fin 2) R) 0 0)
    (h01 : (A : Matrix (Fin 2) (Fin 2) R) 0 1 = (B : Matrix (Fin 2) (Fin 2) R) 0 1)
    (h10 : (A : Matrix (Fin 2) (Fin 2) R) 1 0 = (B : Matrix (Fin 2) (Fin 2) R) 1 0)
    (h11 : (A : Matrix (Fin 2) (Fin 2) R) 1 1 = (B : Matrix (Fin 2) (Fin 2) R) 1 1) : A = B := by
  ext i j
  fin_cases i <;> fin_cases j
  · exact h00
  · exact h01
  · exact h10
  · exact h11

/-- **The unipotent identity** (tex 3610–3613, PROVED):
`U(a) V(b) U(−a/(1+ab)) V(−b(1+ab)) = diag(1+ab, (1+ab)⁻¹)`, for `1 + ab` a unit `u`. -/
theorem U_V_U_V (a b : R) (u : Rˣ) (hu : (u : R) = 1 + a * b) :
    U a * V b * U (-(a * ((u⁻¹ : Rˣ) : R))) * V (-(b * (u : R))) = D u := by
  have h1 : ((u⁻¹ : Rˣ) : R) * (u : R) = 1 := Units.inv_mul u
  refine SL2_ext ?_ ?_ ?_ ?_ <;>
    simp only [Matrix.SpecialLinearGroup.coe_mul, U_coe, V_coe, D_coe, Matrix.mul_fin_two,
      Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one]
  · linear_combination ((1 + a * b) * (a * b)) * h1 - (1 + a * b) * hu
  · linear_combination (-a) * h1 + (a * ((u⁻¹ : Rˣ) : R)) * hu
  · linear_combination (a * b ^ 2) * h1 - b * hu
  · linear_combination (-1 : R) * h1 + ((u⁻¹ : Rˣ) : R) * hu

/-- **Gaussian decomposition** (tex 3614, PROVED): if the upper left entry of `A ∈ SL₂(R)` is a
unit `a`, then `A = V(c/a) · diag(a, a⁻¹) · U(b/a)`. -/
theorem gauss_decomp (A : SL(2, R)) (ua : Rˣ) (hua : (ua : R) = A 0 0) :
    A = V (A 1 0 * ((ua⁻¹ : Rˣ) : R)) * D ua * U (A 0 1 * ((ua⁻¹ : Rˣ) : R)) := by
  have h1 : ((ua⁻¹ : Rˣ) : R) * (ua : R) = 1 := Units.inv_mul ua
  have hdet : A 0 0 * A 1 1 - A 0 1 * A 1 0 = 1 := by
    have := A.det_coe
    rwa [Matrix.det_fin_two] at this
  refine SL2_ext ?_ ?_ ?_ ?_ <;>
    simp only [Matrix.SpecialLinearGroup.coe_mul, U_coe, V_coe, D_coe, Matrix.mul_fin_two,
      Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one]
  · linear_combination (-1 : R) * hua
  · linear_combination (-(A 0 1)) * h1
  · linear_combination (-(A 1 0)) * h1
  · linear_combination (-(A 1 1) - A 0 1 * A 1 0 * ((ua⁻¹ : Rˣ) : R)) * h1
      + (A 1 1 * ((ua⁻¹ : Rˣ) : R)) * hua + ((ua⁻¹ : Rˣ) : R) * hdet

/-- Conjugating `U(x)` by `D(v)` and taking the commutator (tex 3617–3619, PROVED):
`[D(v), U(x)] = U((v² − 1) x)`. -/
theorem commutator_D_U (v : Rˣ) (x : R) : ⁅D v, U x⁆ = U (((v : R) ^ 2 - 1) * x) := by
  have h1 : ((v⁻¹ : Rˣ) : R) * (v : R) = 1 := Units.inv_mul v
  rw [commutatorElement_def, D_inv, U_inv]
  refine SL2_ext ?_ ?_ ?_ ?_ <;>
    simp only [Matrix.SpecialLinearGroup.coe_mul, U_coe, D_coe, Matrix.mul_fin_two,
      Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one, inv_inv]
  · linear_combination h1
  · linear_combination (-x) * h1
  · linear_combination
  · linear_combination h1

/-- `[D(v), V(y)] = V((v⁻² − 1) y)` (tex 3617–3619, PROVED). -/
theorem commutator_D_V (v : Rˣ) (y : R) :
    ⁅D v, V y⁆ = V (((((v⁻¹ : Rˣ) : R)) ^ 2 - 1) * y) := by
  have h1 : ((v⁻¹ : Rˣ) : R) * (v : R) = 1 := Units.inv_mul v
  rw [commutatorElement_def, D_inv, V_inv]
  refine SL2_ext ?_ ?_ ?_ ?_ <;>
    simp only [Matrix.SpecialLinearGroup.coe_mul, V_coe, D_coe, Matrix.mul_fin_two,
      Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one, inv_inv]
  · linear_combination h1
  · linear_combination
  · linear_combination (-y) * h1
  · linear_combination h1

end General

/-! ### Two-adic facts -/

section TwoAdic

/-- `2` is a prime element of `ℤ₂`. -/
theorem prime_two : Prime (2 : ℤ_[2]) := by
  simpa using (PadicInt.prime_p (p := 2))

/-- `2 ≠ 0` in `ℤ₂` (helper). -/
theorem two_ne_zero' : (2 : ℤ_[2]) ≠ 0 := prime_two.ne_zero

/-- `2` is not a unit of `ℤ₂` (helper). -/
theorem not_isUnit_two : ¬ IsUnit (2 : ℤ_[2]) := prime_two.not_isUnit

/-- An element of `ℤ₂` not divisible by `2` is a unit. -/
theorem isUnit_of_not_two_dvd {x : ℤ_[2]} (h : ¬ (2 : ℤ_[2]) ∣ x) : IsUnit x := by
  refine PadicInt.isUnit_iff.2 (le_antisymm (PadicInt.norm_le_one x) (not_lt.1 fun hlt => h ?_))
  simpa using (PadicInt.norm_lt_one_iff_dvd x).1 hlt

/-- `2 ∤ 1` in `ℤ₂` (helper). -/
theorem not_two_dvd_one : ¬ (2 : ℤ_[2]) ∣ 1 := fun h => not_isUnit_two (isUnit_of_dvd_one h)

/-- If `2 ∣ x − 1` then `x` is a unit of `ℤ₂`. -/
theorem isUnit_of_two_dvd_sub_one {x : ℤ_[2]} (h : (2 : ℤ_[2]) ∣ x - 1) : IsUnit x := by
  refine isUnit_of_not_two_dvd fun hx => not_two_dvd_one ?_
  have := dvd_sub hx h
  simpa using this

/-- Reduction modulo `2^d`, in divisibility form. -/
theorem toZModPow_eq_iff (d : ℕ) (x y : ℤ_[2]) :
    PadicInt.toZModPow d x = PadicInt.toZModPow d y ↔ (2 : ℤ_[2]) ^ d ∣ x - y := by
  rw [← sub_eq_zero, ← map_sub, ← RingHom.mem_ker, PadicInt.ker_toZModPow,
    Ideal.mem_span_singleton]
  norm_num

end TwoAdic

/-! ### The principal congruence subgroups `Γ_d` -/

/-- `Γ_d := ker(SL₂(ℤ₂) → SL₂(ℤ/2^d ℤ))` (tex 3603), the genuine kernel of reduction. -/
def Γ (d : ℕ) : Subgroup SL(2, ℤ_[2]) :=
  (Matrix.SpecialLinearGroup.map (PadicInt.toZModPow (p := 2) d)).ker

/-- Membership in `Γ_d`: all entries of `A − 1` are divisible by `2^d`. -/
theorem mem_Γ_iff (d : ℕ) (A : SL(2, ℤ_[2])) :
    A ∈ Γ d ↔ ∀ i j, (2 : ℤ_[2]) ^ d ∣
      (A : Matrix (Fin 2) (Fin 2) ℤ_[2]) i j - (1 : Matrix (Fin 2) (Fin 2) ℤ_[2]) i j := by
  rw [Γ, MonoidHom.mem_ker]
  constructor
  · intro h i j
    have := congrArg (fun M : SL(2, ZMod (2 ^ d)) =>
      (M : Matrix (Fin 2) (Fin 2) (ZMod (2 ^ d))) i j) h
    simp only [Matrix.SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply, Matrix.map_apply,
      Matrix.SpecialLinearGroup.coe_one] at this
    rw [← toZModPow_eq_iff, this]
    by_cases hij : i = j <;> simp [Matrix.one_apply, hij]
  · intro h
    ext i j
    simp only [Matrix.SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply, Matrix.map_apply,
      Matrix.SpecialLinearGroup.coe_one]
    rw [(toZModPow_eq_iff d _ _).2 (h i j)]
    by_cases hij : i = j <;> simp [Matrix.one_apply, hij]

/-- Membership in `Γ_d`, entrywise. -/
theorem mem_Γ_iff' (d : ℕ) (A : SL(2, ℤ_[2])) :
    A ∈ Γ d ↔ (2 : ℤ_[2]) ^ d ∣ A 0 0 - 1 ∧ (2 : ℤ_[2]) ^ d ∣ A 0 1 ∧
      (2 : ℤ_[2]) ^ d ∣ A 1 0 ∧ (2 : ℤ_[2]) ^ d ∣ A 1 1 - 1 := by
  rw [mem_Γ_iff]
  simp [Fin.forall_fin_two, and_assoc]

/-- `Γ_e ⊂ Γ_d` for `d ≤ e` (helper). -/
theorem Γ_anti {d e : ℕ} (h : d ≤ e) : Γ e ≤ Γ d := by
  intro A hA
  rw [mem_Γ_iff] at hA ⊢
  exact fun i j => (pow_dvd_pow 2 h).trans (hA i j)

/-- `U(x) ∈ Γ_d` when `2^d ∣ x`. -/
theorem U_mem_Γ {d : ℕ} {x : ℤ_[2]} (hx : (2 : ℤ_[2]) ^ d ∣ x) : U x ∈ Γ d := by
  rw [mem_Γ_iff']
  simp [hx]

/-- `V(x) ∈ Γ_d` when `2^d ∣ x`. -/
theorem V_mem_Γ {d : ℕ} {x : ℤ_[2]} (hx : (2 : ℤ_[2]) ^ d ∣ x) : V x ∈ Γ d := by
  rw [mem_Γ_iff']
  simp [hx]

/-- `D(v) ∈ Γ_d` when `2^d ∣ v − 1`. -/
theorem D_mem_Γ {d : ℕ} {v : ℤ_[2]ˣ} (hv : (2 : ℤ_[2]) ^ d ∣ (v : ℤ_[2]) - 1) : D v ∈ Γ d := by
  have h1 : ((v⁻¹ : ℤ_[2]ˣ) : ℤ_[2]) - 1 = -(((v : ℤ_[2]) - 1) * ((v⁻¹ : ℤ_[2]ˣ) : ℤ_[2])) := by
    have := Units.mul_inv v
    linear_combination this
  have h2 : (2 : ℤ_[2]) ^ d ∣ ((v⁻¹ : ℤ_[2]ˣ) : ℤ_[2]) - 1 := by
    rw [h1, dvd_neg]
    exact dvd_mul_of_dvd_left hv _
  rw [mem_Γ_iff']
  simp only [D_coe, Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one]
  exact ⟨hv, dvd_zero _, dvd_zero _, h2⟩

/-! ### The Gaussian decomposition step (tex 3614–3615) -/

/-- **A subgroup containing `U(2^k ℤ₂)` and `V(2^k ℤ₂)` contains `Γ_{2k}`** (tex 3614–3615,
PROVED), for `k ≥ 1`: write `A ∈ Γ_{2k}` as `V(c/a) D(a) U(b/a)`; the outer factors have
level `≥ 2k ≥ k`, and `D(a)`, `a = 1 + 2^k·(2^k z)`, is a product of four level-`k`
unipotents by `U_V_U_V`. -/
theorem Γ_two_mul_le (k : ℕ) (hk : 1 ≤ k) (H : Subgroup SL(2, ℤ_[2]))
    (hU : ∀ x : ℤ_[2], U ((2 : ℤ_[2]) ^ k * x) ∈ H)
    (hV : ∀ y : ℤ_[2], V ((2 : ℤ_[2]) ^ k * y) ∈ H) : Γ (2 * k) ≤ H := by
  intro A hA
  rw [mem_Γ_iff'] at hA
  obtain ⟨⟨z, hz⟩, ⟨b', hb'⟩, ⟨c', hc'⟩, -⟩ := hA
  have h2k : (2 : ℤ_[2]) ^ (2 * k) = 2 ^ k * 2 ^ k := by rw [two_mul, pow_add]
  have ha : IsUnit (A 0 0) := by
    refine isUnit_of_two_dvd_sub_one ⟨2 ^ (2 * k - 1) * z, ?_⟩
    rw [hz, ← mul_assoc, ← pow_succ']
    congr 2
    omega
  set ua := ha.unit with hua_def
  have hua : (ua : ℤ_[2]) = A 0 0 := ha.unit_spec
  have hD : D ua ∈ H := by
    have key := U_V_U_V ((2 : ℤ_[2]) ^ k) (2 ^ k * z) ua (by
      rw [hua]; linear_combination hz + z * h2k)
    rw [← key]
    refine H.mul_mem (H.mul_mem (H.mul_mem ?_ ?_) ?_) ?_
    · simpa using hU 1
    · exact hV z
    · have := hU (-((ua⁻¹ : ℤ_[2]ˣ) : ℤ_[2]))
      convert this using 2
      ring
    · have := hV (-(z * (ua : ℤ_[2])))
      convert this using 2
      ring
  rw [gauss_decomp A ua hua]
  refine H.mul_mem (H.mul_mem ?_ hD) ?_
  · have := hV (2 ^ k * c' * ((ua⁻¹ : ℤ_[2]ˣ) : ℤ_[2]))
    convert this using 2
    rw [hc', h2k]
    ring
  · have := hU (2 ^ k * b' * ((ua⁻¹ : ℤ_[2]ˣ) : ℤ_[2]))
    convert this using 2
    rw [hb', h2k]
    ring

/-! ### Index at most two (tex 3606–3607) -/

/-- **A subgroup of index at most two contains every square** (tex 3606–3607, PROVED). -/
theorem sq_mem_of_index_le_two {G : Type*} [Group G] {H : Subgroup G}
    (h : H.index = 1 ∨ H.index = 2) (g : G) : g ^ 2 ∈ H := by
  rcases h with h | h
  · rw [Subgroup.index_eq_one.1 h]
    exact Subgroup.mem_top _
  · exact Subgroup.sq_mem_of_index_two h g

/-- **`Γ_m ⊂ J_K` for `m = 2d + 2`** (tex 3598–3616, PROVED).  Here `G` plays
`G_{ℚ(μ_{2^∞})}` and `ρ` the Tate representation on it (with values in `SL₂` because the
determinant is the cyclotomic character), so `J = ρ(G)`; `GF` plays `G_{F_∞}`, of index at most
two, and `J_K = ρ(GF)`.  From Serre's `Γ_d ⊂ J`: `U(2^d x) ∈ J`, so its square
`U(2^{d+1} x)` lies in `J_K`; likewise for `V`; then `Γ_two_mul_le` with `k = d + 1`. -/
theorem Γ_two_mul_add_two_le {G : Type*} [Group G] (ρ : G →* SL(2, ℤ_[2])) (GF : Subgroup G)
    (d : ℕ) (hSerre : Γ d ≤ ρ.range) (hidx : GF.index = 1 ∨ GF.index = 2) :
    Γ (2 * d + 2) ≤ GF.map ρ := by
  have hsq : ∀ M ∈ Γ d, M ^ 2 ∈ GF.map ρ := by
    intro M hM
    obtain ⟨g, rfl⟩ := hSerre hM
    exact ⟨g ^ 2, sq_mem_of_index_le_two hidx g, by simp⟩
  have h := Γ_two_mul_le (d + 1) (by omega) (GF.map ρ)
    (fun x => by
      have := hsq (U ((2 : ℤ_[2]) ^ d * x)) (U_mem_Γ (dvd_mul_right _ _))
      rw [U_sq] at this
      convert this using 2
      ring)
    (fun y => by
      have := hsq (V ((2 : ℤ_[2]) ^ d * y)) (V_mem_Γ (dvd_mul_right _ _))
      rw [V_sq] at this
      convert this using 2
      ring)
  have e : 2 * (d + 1) = 2 * d + 2 := by ring
  rwa [e] at h

/-! ### The commutator step (tex 3617–3623) -/

/-- The unit `1 + 2^m` of `ℤ₂` (for `m ≥ 1`). -/
def onePlusTwoPow (m : ℕ) (hm : m ≠ 0) : ℤ_[2]ˣ :=
  (isUnit_of_two_dvd_sub_one (x := 1 + 2 ^ m)
    ⟨2 ^ (m - 1), by rw [add_sub_cancel_left, ← pow_succ']; congr 1; omega⟩).unit

/-- The value of `onePlusTwoPow`. -/
@[simp] theorem onePlusTwoPow_coe (m : ℕ) (hm : m ≠ 0) :
    ((onePlusTwoPow m hm : ℤ_[2]ˣ) : ℤ_[2]) = 1 + 2 ^ m :=
  IsUnit.unit_spec _

/-- `(1 + 2^m)² − 1 = 2^{m+1} (1 + 2^{m−1})` with `1 + 2^{m−1}` a unit when `m ≥ 2`; this is
Elliot's `v₂((1+2^m)² − 1) = m + 1` (tex 3620), PROVED. -/
theorem sq_onePlusTwoPow_sub_one (m : ℕ) (hm : 2 ≤ m) :
    ∃ e : ℤ_[2]ˣ, (1 + 2 ^ m : ℤ_[2]) ^ 2 - 1 = 2 ^ (m + 1) * e := by
  have hm1 : m - 1 ≠ 0 := by omega
  refine ⟨onePlusTwoPow (m - 1) hm1, ?_⟩
  rw [onePlusTwoPow_coe]
  have e1 : (2 : ℤ_[2]) ^ m = 2 * 2 ^ (m - 1) := by rw [← pow_succ']; congr 1; omega
  have e2 : (2 : ℤ_[2]) ^ (m + 1) = 2 * 2 * 2 ^ (m - 1) := by
    rw [mul_assoc, ← e1, pow_succ, mul_comm]
  rw [e2, e1]
  ring

/-- **`Γ_{4m+2} ⊂ [J_K, J_K]`** (tex 3617–3623, PROVED), for `m ≥ 2` and `Γ_m ⊂ J_K`:
`[D(1+2^m), U(2^m x)] = U(((1+2^m)² − 1) 2^m x)` runs through all of `U(2^{2m+1} ℤ₂)`, and
likewise for `V`; then `Γ_two_mul_le` with `k = 2m + 1`.  (The containment is in the abstract
commutator subgroup; Elliot's closure is not needed.) -/
theorem Γ_four_mul_add_two_le_commutator (JK : Subgroup SL(2, ℤ_[2])) (m : ℕ) (hm : 2 ≤ m)
    (hΓ : Γ m ≤ JK) : Γ (4 * m + 2) ≤ ⁅JK, JK⁆ := by
  have hm0 : m ≠ 0 := by omega
  set u := onePlusTwoPow m hm0 with hu_def
  have hu : (u : ℤ_[2]) = 1 + 2 ^ m := onePlusTwoPow_coe m hm0
  have hDmem : D u ∈ JK := hΓ (D_mem_Γ (by rw [hu]; simp))
  obtain ⟨e, he⟩ := sq_onePlusTwoPow_sub_one m hm
  have hpow : (2 : ℤ_[2]) ^ (2 * m + 1) = 2 ^ (m + 1) * 2 ^ m := by
    rw [← pow_add]; congr 1; ring
  have h := Γ_two_mul_le (2 * m + 1) (by omega) ⁅JK, JK⁆
    (fun x => by
      have hc := Subgroup.commutator_mem_commutator hDmem
        (hΓ (U_mem_Γ (dvd_mul_right ((2 : ℤ_[2]) ^ m) (x * ((e⁻¹ : ℤ_[2]ˣ) : ℤ_[2])))))
      rw [commutator_D_U, hu, he] at hc
      convert hc using 2
      have := Units.inv_mul e
      rw [hpow]
      linear_combination (-(2 ^ (m + 1) * 2 ^ m * x : ℤ_[2])) * this)
    (fun y => by
      have hc := Subgroup.commutator_mem_commutator hDmem
        (hΓ (V_mem_Γ (dvd_mul_right ((2 : ℤ_[2]) ^ m)
          (-(y * ((e⁻¹ : ℤ_[2]ˣ) : ℤ_[2]) * (u : ℤ_[2]) ^ 2)))))
      rw [commutator_D_V] at hc
      convert hc using 2
      have h1 := Units.inv_mul e
      have h2 : ((u⁻¹ : ℤ_[2]ˣ) : ℤ_[2]) * (u : ℤ_[2]) = 1 := Units.inv_mul u
      have he' : (u : ℤ_[2]) ^ 2 - 1 = 2 ^ (m + 1) * e := by rw [hu, he]
      rw [hpow]
      linear_combination
        (-(2 ^ (m + 1) * 2 ^ m * y : ℤ_[2])) * h1
        + (2 ^ m * y * ((e⁻¹ : ℤ_[2]ˣ) : ℤ_[2]) *
            (((u⁻¹ : ℤ_[2]ˣ) : ℤ_[2]) * (u : ℤ_[2]) + 1)) * h2
        - (2 ^ m * y * ((e⁻¹ : ℤ_[2]ˣ) : ℤ_[2])) * he')
  have e4 : 2 * (2 * m + 1) = 4 * m + 2 := by ring
  rwa [e4] at h

/-! ### (4.4c) -/

/-- **(4.4c)** (tex 3597–3633, PROVED from its hypotheses):
let `G` play `G_{ℚ(μ_{2^∞})}`, `ρ : G → SL₂(ℤ₂)` the Tate representation on it, `GF` play
`G_{F_∞}` (index at most two), and `HL` play `G_{L_∞}`, with `G_{F_∞}/G_{L_∞}` abelian, i.e.
`[G_{F_∞}, G_{F_∞}] ⊂ G_{L_∞}`.  If `Γ_d ⊂ ρ(G)` (Serre's open image, tex 3600–3605), then
`Γ_ν ⊂ ρ(G_{L_∞})` for `ν = 8d + 10`.  The steps are Elliot's: `m = 2d + 2`, `Γ_m ⊂ J_K`,
`Γ_{4m+2} ⊂ [J_K, J_K] = ρ([G_{F_∞}, G_{F_∞}]) ⊂ ρ(G_{L_∞})`. -/
theorem four_four_c {G : Type*} [Group G] (ρ : G →* SL(2, ℤ_[2])) (GF HL : Subgroup G) (d : ℕ)
    (hSerre : Γ d ≤ ρ.range) (hidx : GF.index = 1 ∨ GF.index = 2) (hab : ⁅GF, GF⁆ ≤ HL) :
    Γ (8 * d + 10) ≤ HL.map ρ := by
  have h1 : Γ (2 * d + 2) ≤ GF.map ρ := Γ_two_mul_add_two_le ρ GF d hSerre hidx
  have h2 := Γ_four_mul_add_two_le_commutator (GF.map ρ) (2 * d + 2) (by omega) h1
  have e : 4 * (2 * d + 2) + 2 = 8 * d + 10 := by ring
  rw [e, ← Subgroup.map_commutator] at h2
  exact h2.trans (Subgroup.map_mono hab)

/-- Elliot's closure form of the commutator step (tex 3621–3622) follows from the abstract one. -/
theorem Γ_le_closure_commutator [TopologicalSpace SL(2, ℤ_[2])] (JK : Subgroup SL(2, ℤ_[2]))
    (m : ℕ) (hm : 2 ≤ m) (hΓ : Γ m ≤ JK) :
    ((Γ (4 * m + 2) : Subgroup SL(2, ℤ_[2])) : Set SL(2, ℤ_[2])) ⊆
      closure ((⁅JK, JK⁆ : Subgroup SL(2, ℤ_[2])) : Set SL(2, ℤ_[2])) :=
  fun _ hx => subset_closure (Γ_four_mul_add_two_le_commutator JK m hm hΓ hx)

/-! ### Non-vacuity checks -/

/-- `Γ_d` is a proper subgroup for `d ≥ 1`: `U(1) ∉ Γ_1`. -/
theorem U_one_not_mem_Γ_one : U (1 : ℤ_[2]) ∉ Γ 1 := by
  intro h
  have h01 := ((mem_Γ_iff' 1 _).1 h).2.1
  rw [pow_one] at h01
  exact not_two_dvd_one (by simpa using h01)

/-- The hypotheses of `four_four_c` are satisfiable (identity representation, `GF = GL = ⊤`). -/
example : Γ (8 * 0 + 10) ≤ (⊤ : Subgroup SL(2, ℤ_[2])).map (MonoidHom.id _) :=
  four_four_c (MonoidHom.id _) ⊤ ⊤ 0 (fun x _ => ⟨x, rfl⟩) (Or.inl Subgroup.index_top)
    le_top

end

end ZInQ.Manuscript.RC.Moving
