import Mathlib

/-!
# Theorem 5.3, Lane RC11-even: membership of the even scalar, (E.4a) and (E.5)

The 11/5 manuscript (`diophantine_zq.tex`), Section 7.1 (tex 1945–1954) and Appendix E, proof of
Proposition `ex:app-even-scalar` (tex 7545–7611). The coefficient rings are
`Λ = ℤ₂[[t]]`, `A = Λ[1/2]` (power series over `ℚ₂` with bounded denominators) and the outer ring
`𝒪 = (Λ_{(2)})^∧`, whose elements have Laurent expansions with `ℤ₂` coefficients; `G = 𝔽₂^b` and
an element of `A[G]` is given by its coefficients in the group basis.

* `InLamHalf`, `InLam` and their closure properties; `inLam_iff` (`u ∈ Λ` iff `u` is the image of a
  power series over `ℤ₂`).
* `charEval`, `fourier_inversion`, `inLamHalf_of_charEval` — "Since `|G|` is a power of two, the
  character idempotents belong to `A[G]` and these memberships give `u^{ev} ∈ A[G]`"
  (tex 7591–7595). This is membership only: inversion divides by `|G| = 2^b`.
* `length_quotient_dvr` — over a DVR `R`, `ℓ_R(R/αR) = v(α)`; `E4a_nonneg` — **(E.4a)**
  (tex 7572–7589): `v_𝔭(u_x) = ℓ_R(H¹/Rz) − ℓ_R H² ≥ 0`, the inequality being (K2).
* `det_integral` — the wedge of two integral vectors of the free rank-two `𝒪[G]`-module (E.3) is
  integral (tex 7596–7599).
* `E5_coefficientwise` — **(E.5)** (tex 7600–7610): `A ∩ 𝒪 = Λ` coefficientwise, so
  `2^{c_E} u ∈ Λ[G]` with the exponent `c_E` retained, without a term `v₂|G|`.

Everything here is PROVED.
-/

namespace ZInQ.Manuscript.RC.Even

open PowerSeries

attribute [local instance] Nat.fact_prime_two

/-! ## `Λ`, `Λ[1/2]` -/

/-- **`u ∈ Λ[1/2]`** for `u ∈ ℚ₂[[t]]`: bounded denominators, `2^e u ∈ ℤ₂[[t]]` for some `e`. -/
def InLamHalf (u : PowerSeries ℚ_[2]) : Prop :=
  ∃ e : ℕ, ∀ n : ℕ, ‖(2 : ℚ_[2]) ^ e * coeff n u‖ ≤ 1

/-- **`u ∈ Λ = ℤ₂[[t]]`** for `u ∈ ℚ₂[[t]]`: all coefficients are `2`-adic integers. -/
def InLam (u : PowerSeries ℚ_[2]) : Prop :=
  ∀ n : ℕ, ‖coeff n u‖ ≤ 1

/-- `u ∈ Λ` iff `u` is the image of a power series over `ℤ₂` (PROVED). -/
theorem inLam_iff (u : PowerSeries ℚ_[2]) :
    InLam u ↔ ∃ U : PowerSeries ℤ_[2], PowerSeries.map PadicInt.Coe.ringHom U = u := by
  constructor
  · intro h
    refine ⟨PowerSeries.mk fun n => Padic.lift (coeff n u) (h n), ?_⟩
    ext n
    rw [PowerSeries.coeff_map, PowerSeries.coeff_mk]
    rfl
  · rintro ⟨U, rfl⟩ n
    rw [PowerSeries.coeff_map]
    exact PadicInt.norm_le_one (coeff n U)

theorem InLam.inLamHalf {u : PowerSeries ℚ_[2]} (h : InLam u) : InLamHalf u :=
  ⟨0, fun n => by simpa using h n⟩

/-- The `2`-adic norm of `2` is at most one. -/
lemma norm_two_le_one : ‖(2 : ℚ_[2])‖ ≤ 1 := by
  simpa using Padic.norm_int_le_one (p := 2) 2

/-- A product of a real number at most one with a nonnegative real number at most one is at most
one. -/
lemma mul_le_one_aux {a b : ℝ} (ha : a ≤ 1) (hb0 : 0 ≤ b) (hb : b ≤ 1) : a * b ≤ 1 :=
  (mul_le_mul_of_nonneg_right ha hb0).trans (by rwa [one_mul])

/-- Raising the exponent `e` keeps the bound `‖2^e x‖ ≤ 1`. -/
lemma norm_two_pow_mul_le_of_le {e e' : ℕ} (h : e ≤ e') {x : ℚ_[2]}
    (hx : ‖(2 : ℚ_[2]) ^ e * x‖ ≤ 1) : ‖(2 : ℚ_[2]) ^ e' * x‖ ≤ 1 := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le h
  rw [pow_add, mul_comm ((2 : ℚ_[2]) ^ e), mul_assoc, norm_mul, norm_pow]
  exact mul_le_one_aux (pow_le_one₀ (norm_nonneg _) norm_two_le_one) (norm_nonneg _) hx

theorem InLamHalf.add {u v : PowerSeries ℚ_[2]} (hu : InLamHalf u) (hv : InLamHalf v) :
    InLamHalf (u + v) := by
  obtain ⟨e, he⟩ := hu
  obtain ⟨f, hf⟩ := hv
  refine ⟨max e f, fun n => ?_⟩
  rw [map_add, mul_add]
  exact (Padic.nonarchimedean _ _).trans
    (max_le (norm_two_pow_mul_le_of_le (le_max_left _ _) (he n))
      (norm_two_pow_mul_le_of_le (le_max_right _ _) (hf n)))

theorem InLamHalf.neg {u : PowerSeries ℚ_[2]} (hu : InLamHalf u) : InLamHalf (-u) := by
  obtain ⟨e, he⟩ := hu
  exact ⟨e, fun n => by simpa [map_neg] using he n⟩

theorem InLamHalf.sum {ι : Type*} (s : Finset ι) {u : ι → PowerSeries ℚ_[2]}
    (hu : ∀ i ∈ s, InLamHalf (u i)) : InLamHalf (∑ i ∈ s, u i) := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨0, fun n => by simp⟩
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact (hu a (Finset.mem_insert_self a s)).add
      (ih fun i hi => hu i (Finset.mem_insert_of_mem hi))

/-- `A = Λ[1/2]` contains `1/2` (PROVED). -/
theorem InLamHalf.smul_inv_two_pow {u : PowerSeries ℚ_[2]} (hu : InLamHalf u) (b : ℕ) :
    InLamHalf (((2 : ℚ_[2])⁻¹) ^ b • u) := by
  obtain ⟨e, he⟩ := hu
  refine ⟨e + b, fun n => ?_⟩
  have h2 : (2 : ℚ_[2]) ≠ 0 := two_ne_zero
  have : (2 : ℚ_[2]) ^ (e + b) * coeff n (((2 : ℚ_[2])⁻¹) ^ b • u) =
      (2 : ℚ_[2]) ^ e * coeff n u := by
    rw [PowerSeries.coeff_smul, smul_eq_mul, pow_add, inv_pow]
    field_simp
  rw [this]
  exact he n

theorem InLamHalf.int_smul {u : PowerSeries ℚ_[2]} (hu : InLamHalf u) (c : ℤ) :
    InLamHalf ((c : ℚ_[2]) • u) := by
  obtain ⟨e, he⟩ := hu
  refine ⟨e, fun n => ?_⟩
  rw [PowerSeries.coeff_smul, smul_eq_mul, mul_left_comm, norm_mul]
  exact mul_le_one_aux (Padic.norm_int_le_one c) (norm_nonneg _) (he n)

/-! ## The group ring `A[G]`, `G = 𝔽₂^b`, and Fourier inversion -/

/-- The sign character `x(g) = (−1)^{x·g}` of `G = 𝔽₂^b` at the address `x`. -/
def chi {b : ℕ} (x g : Fin b → ZMod 2) : ℤ := if dotProduct x g = 0 then 1 else -1

/-- **The constituent `u_x`** of `u ∈ A[G]`: `u_x = Σ_g x(g) u_g`. -/
noncomputable def charEval {b : ℕ} (u : (Fin b → ZMod 2) → PowerSeries ℚ_[2])
    (x : Fin b → ZMod 2) : PowerSeries ℚ_[2] :=
  ∑ g, ((chi x g : ℤ) : ℚ_[2]) • u g

/-- The sign character is multiplicative in its second argument: `x(g − h) = x(g) x(h)`. -/
lemma chi_sub {b : ℕ} (x g h : Fin b → ZMod 2) : chi x (g - h) = chi x g * chi x h := by
  unfold chi
  rw [dotProduct_sub]
  generalize dotProduct x g = s
  generalize dotProduct x h = t
  revert s t
  decide

/-- Translating the address by the basis vector `e_i` flips the sign at `v` when `v i ≠ 0`. -/
lemma chi_add_single {b : ℕ} (x v : Fin b → ZMod 2) (i : Fin b) (hi : v i ≠ 0) :
    chi (x + Pi.single i 1) v = - chi x v := by
  unfold chi
  rw [add_dotProduct, single_dotProduct, one_mul]
  generalize dotProduct x v = s
  revert hi
  generalize v i = t
  revert s t
  decide

/-- **Orthogonality of characters** on `𝔽₂^b`: `Σ_x x(v) = 2^b [v = 0]`. -/
lemma sum_chi {b : ℕ} (v : Fin b → ZMod 2) :
    ∑ x, chi x v = if v = 0 then (2 : ℤ) ^ b else 0 := by
  split_ifs with hv
  · subst hv
    simp [chi]
  · obtain ⟨i, hi⟩ : ∃ i, v i ≠ 0 := Function.ne_iff.mp hv
    have hneg : ∑ x, chi x v = - ∑ x, chi x v := by
      calc ∑ x, chi x v
          = ∑ x, chi ((Equiv.addRight (Pi.single i (1 : ZMod 2))) x) v :=
            (Equiv.sum_comp _ (fun x => chi x v)).symm
        _ = ∑ x, - chi x v := by
            refine Finset.sum_congr rfl fun x _ => ?_
            rw [Equiv.coe_addRight, chi_add_single x v i hi]
        _ = - ∑ x, chi x v := Finset.sum_neg_distrib _
    linarith

/-- **Fourier inversion** on `G = 𝔽₂^b` (PROVED): `u_g = 2^{−b} Σ_x x(g) u_x`. -/
theorem fourier_inversion {b : ℕ} (u : (Fin b → ZMod 2) → PowerSeries ℚ_[2])
    (g : Fin b → ZMod 2) :
    u g = ((2 : ℚ_[2])⁻¹) ^ b • ∑ x, ((chi x g : ℤ) : ℚ_[2]) • charEval u x := by
  have horth : ∀ h, ∑ x, ((chi x g : ℤ) : ℚ_[2]) * ((chi x h : ℤ) : ℚ_[2]) =
      if h = g then (2 : ℚ_[2]) ^ b else 0 := by
    intro h
    have H : ∑ x, chi x g * chi x h = if h = g then (2 : ℤ) ^ b else 0 := by
      rw [← Finset.sum_congr rfl fun x _ => chi_sub x g h, sum_chi]
      by_cases hgh : g = h
      · subst hgh
        simp
      · simp [sub_eq_zero, hgh, Ne.symm hgh]
    have H' := congrArg (fun z : ℤ => (z : ℚ_[2])) H
    simp only [Int.cast_sum, Int.cast_mul] at H'
    rw [H']
    split_ifs <;> simp
  have key : ∑ x, ((chi x g : ℤ) : ℚ_[2]) • charEval u x = (2 : ℚ_[2]) ^ b • u g := by
    unfold charEval
    calc ∑ x, ((chi x g : ℤ) : ℚ_[2]) • ∑ h, ((chi x h : ℤ) : ℚ_[2]) • u h
        = ∑ x, ∑ h, (((chi x g : ℤ) : ℚ_[2]) * ((chi x h : ℤ) : ℚ_[2])) • u h := by
          simp_rw [Finset.smul_sum, smul_smul]
      _ = ∑ h, ∑ x, (((chi x g : ℤ) : ℚ_[2]) * ((chi x h : ℤ) : ℚ_[2])) • u h :=
          Finset.sum_comm
      _ = ∑ h, (∑ x, ((chi x g : ℤ) : ℚ_[2]) * ((chi x h : ℤ) : ℚ_[2])) • u h := by
          simp_rw [Finset.sum_smul]
      _ = ∑ h, (if h = g then (2 : ℚ_[2]) ^ b else 0) • u h := by
          simp_rw [horth]
      _ = (2 : ℚ_[2]) ^ b • u g := by
          simp [ite_smul]
  rw [key, smul_smul, ← mul_pow, inv_mul_cancel₀ (two_ne_zero : (2 : ℚ_[2]) ≠ 0), one_pow,
    one_smul]

/-- **Characterwise membership gives membership in `A[G]`** (tex 7591–7595; PROVED): if every
constituent `u_x` lies in `A = Λ[1/2]`, so does every group-basis coefficient `u_g` (`2` is a unit
in `A`). No bound on the denominator is asserted. -/
theorem inLamHalf_of_charEval {b : ℕ} (u : (Fin b → ZMod 2) → PowerSeries ℚ_[2])
    (h : ∀ x, InLamHalf (charEval u x)) (g : Fin b → ZMod 2) : InLamHalf (u g) := by
  rw [fourier_inversion u g]
  exact (InLamHalf.sum _ fun x _ => (h x).int_smul (chi x g)).smul_inv_two_pow b

/-! ## (E.4a) over a discrete valuation ring -/

/-- **Length of a cyclic quotient of a DVR** (PROVED): `ℓ_R(R/αR) = v(α)` for `α ≠ 0`. -/
theorem length_quotient_dvr {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    {α : R} (hα : α ≠ 0) :
    Module.length R (R ⧸ Ideal.span {α}) = (IsDiscreteValuationRing.addVal R α : ℕ∞) := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible R
  obtain ⟨n, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hα hϖ
  rw [IsDiscreteValuationRing.addVal_def' u hϖ n, Ideal.span_singleton_mul_left_unit u.isUnit,
    ← Ideal.span_singleton_pow, ← hϖ.maximalIdeal_eq,
    IsDiscreteValuationRing.length_quotient_pow_maximalIdeal]

/-- **(E.4a)** (tex 7572–7589; PROVED): at a height-one prime `𝔭` of `A`, over the DVR
`R = A_𝔭`, write the free rank-one degree-one module as `Re` and `z = αe`. If
`v_𝔭(u_x) = v(α) − Σ_i v(d_i)` (the inverse determinant lattice of a finite free model with
nonzero Smith entries `d_i` is generated by `(∏ d_i) a ∧ ẽ`), `Σ_i v(d_i) = ℓ_R H²` and (K2)
`ℓ_R H² ≤ ℓ_R(H¹/Rz)`, then `v_𝔭(u_x) = ℓ_R(H¹/Rz) − ℓ_R H² ≥ 0`. -/
theorem E4a_nonneg {vu vα smith lH2 lquot : ℤ} (hu : vu = vα - smith) (hsmith : smith = lH2)
    (hquot : lquot = vα) (hK2 : lH2 ≤ lquot) : vu = lquot - lH2 ∧ 0 ≤ vu := by
  constructor <;> omega

/-! ## (E.3)–(E.5): the integral wedge and the coefficientwise intersection -/

/-- **The wedge of integral vectors is integral** (tex 7596–7599; PROVED): in the free rank-two
module `B²` over any commutative ring `B` (here `B = 𝒪[G]`, by (E.3)), the wedge `a ∧ b` of two
vectors with coordinates in a subring `S` (the integral elements) has coordinate in `S`. -/
theorem det_integral {B : Type*} [CommRing B] (S : Subring B) (a b : Fin 2 → B)
    (ha : ∀ i, a i ∈ S) (hb : ∀ i, b i ∈ S) : Matrix.det (Matrix.of ![a, b]) ∈ S := by
  rw [Matrix.det_fin_two]
  simp only [Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one]
  exact S.sub_mem (S.mul_mem (ha 0) (hb 1)) (S.mul_mem (ha 1) (hb 0))

/-- **(E.5): `A ∩ 𝒪 = Λ`, coefficientwise** (tex 7600–7610; PROVED). An element `u` of
`A = Λ[1/2]` has bounded denominators; if the same element lies in `𝒪` — its Laurent expansion
`f : ℤ → ℤ₂` agrees with `u` in degrees `≥ 0` and vanishes in negative degrees — then its minimum
coefficient valuation is nonnegative and `u ∈ Λ`. In this coefficient model the deduction is
immediate: the hypothesis `u ∈ A` is what places `u` in `𝒪[1/2]` with the displayed expansion
(no negative-degree terms), and the conclusion is read off coefficientwise, as in the text. -/
theorem inLam_of_inLamHalf_of_outer {u : PowerSeries ℚ_[2]} (_hu : InLamHalf u) (f : ℤ → ℤ_[2])
    (hf : ∀ n : ℕ, ((f n : ℤ_[2]) : ℚ_[2]) = coeff n u) : InLam u := by
  intro n
  rw [← hf n]
  exact PadicInt.norm_le_one (f n)

/-- **(E.5) in `Λ[G]`** (tex 7596–7610; PROVED): if `u ∈ A[G]` and `2^{c_E} u ∈ 𝒪[G]` (each
group-basis coefficient of `2^{c_E} u` has a Laurent expansion over `ℤ₂`), then
`2^{c_E} u ∈ Λ[G]`, with the same exponent `c_E` for every `b`. -/
theorem E5_coefficientwise {b : ℕ} (u : (Fin b → ZMod 2) → PowerSeries ℚ_[2]) (cE : ℕ)
    (hA : ∀ g, InLamHalf (u g)) (f : (Fin b → ZMod 2) → ℤ → ℤ_[2])
    (hf : ∀ g, ∀ n : ℕ, ((f g n : ℤ_[2]) : ℚ_[2]) = coeff n ((2 : ℚ_[2]) ^ cE • u g)) :
    ∀ g, InLam ((2 : ℚ_[2]) ^ cE • u g) := by
  intro g
  have h2 : ((2 : ℚ_[2]) ^ cE) = (((2 ^ cE : ℤ)) : ℚ_[2]) := by push_cast; rfl
  have hAg : InLamHalf ((2 : ℚ_[2]) ^ cE • u g) := by
    rw [h2]
    exact (hA g).int_smul _
  exact inLam_of_inLamHalf_of_outer hAg (f g) (hf g)

/-- **`v₂ u(0) ≥ −c` for `2^c u ∈ Λ`** (PROVED): the central coefficient of an element of
`2^{−c}Λ` has valuation at least `−c`. -/
theorem valuation_central_ge {u : PowerSeries ℚ_[2]} {c : ℕ} (hu : InLam ((2 : ℚ_[2]) ^ c • u))
    (h0 : coeff 0 u ≠ 0) : -(c : ℤ) ≤ (coeff 0 u).valuation := by
  have h := hu 0
  rw [PowerSeries.coeff_smul, smul_eq_mul, Padic.norm_le_one_iff_val_nonneg,
    Padic.valuation_mul (pow_ne_zero _ two_ne_zero) h0, Padic.valuation_pow] at h
  have h2 : (2 : ℚ_[2]).valuation = 1 := by simp
  rw [h2] at h
  linarith

end ZInQ.Manuscript.RC.Even
