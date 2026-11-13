import Mathlib

/-!
# t28-igusa: the `SO(3) = PGL(2)` lemma for binary quadratics (glue for Mestre's route)

Binary quadratics `q = q₀ + q₁x + q₂x²` as vectors `Fin 3 → K`; `qAct q a b c d` is
`(cx+d)² q((ax+b)/(cx+d))`, and `pair` is the polar form of `−disc` (`pair q q = 4q₀q₂ − q₁²`),
which is `2·(q,p)₂` up to a constant for the second transvectant.

`so3`: over an algebraically closed field of characteristic 0, if two bases `(qᵢ)`, `(pᵢ)` of
binary quadratics have the same Gram matrix for `pair`, then one invertible substitution `M`
carries every `qᵢ` to `pᵢ`. This is the step of Mestre's reconstruction that turns "the quadratic
covariants `y₁, y₂, y₃` of `f` and `g` have the same Gram matrix" into "`f` and `g` are
equivalent".
-/

namespace T28SO3

variable {K : Type*} [Field K]

/-- `(cx+d)² q((ax+b)/(cx+d))`. -/
def qAct (q : Fin 3 → K) (a b c d : K) : Fin 3 → K :=
  ![q 0 * d ^ 2 + q 1 * b * d + q 2 * b ^ 2,
    2 * q 0 * c * d + q 1 * (a * d + b * c) + 2 * q 2 * a * b,
    q 0 * c ^ 2 + q 1 * a * c + q 2 * a ^ 2]

/-- The polar form of `−disc`: `pair q q = 4 q₀ q₂ − q₁²`. -/
def pair (q p : Fin 3 → K) : K := 2 * q 0 * p 2 + 2 * q 2 * p 0 - q 1 * p 1

theorem pair_qAct (q p : Fin 3 → K) (a b c d : K) :
    pair (qAct q a b c d) (qAct p a b c d) = (a * d - b * c) ^ 2 * pair q p := by
  simp [pair, qAct]; ring

/-- The Gram matrix of `pair`. -/
def Pm : Matrix (Fin 3) (Fin 3) K := !![0, 0, 2; 0, -1, 0; 2, 0, 0]

theorem gram_apply (A : Matrix (Fin 3) (Fin 3) K) (i j : Fin 3) :
    (A * Pm * A.transpose) i j = pair (A i) (A j) := by
  simp [Matrix.mul_apply, Fin.sum_univ_three, Pm, pair]; ring

/-- A null vector of `pair` is a square `(cx + d)²`. -/
theorem null_sq [IsAlgClosed K] [CharZero K] (u : Fin 3 → K) (hu : pair u u = 0) :
    ∃ c d : K, u 0 = d ^ 2 ∧ u 1 = 2 * c * d ∧ u 2 = c ^ 2 := by
  have h : u 1 ^ 2 = 4 * u 0 * u 2 := by simp [pair] at hu; linear_combination -hu
  obtain ⟨d, hd⟩ := IsAlgClosed.exists_pow_nat_eq (u 0) (by norm_num : 0 < 2)
  by_cases hd0 : d = 0
  · subst hd0
    have h0 : u 0 = 0 := by rw [← hd]; ring
    have h1 : u 1 = 0 := by rw [h0] at h; simpa using h
    obtain ⟨c, hc⟩ := IsAlgClosed.exists_pow_nat_eq (u 2) (by norm_num : 0 < 2)
    exact ⟨c, 0, by rw [h0]; ring, by rw [h1]; ring, hc.symm⟩
  · refine ⟨u 1 / (2 * d), d, hd.symm, by field_simp, ?_⟩
    have h2 : (2 : K) * d ≠ 0 := mul_ne_zero two_ne_zero hd0
    field_simp
    rw [← hd] at h; linear_combination h

/-- The algebraic core: an orthonormal-type frame `u, z, v` (`u, v` null, `pair u v = 2`,
`pair z z = −1`, `z ⊥ u, v`) is the image of the standard frame `1, x, x²` under a substitution. -/
theorem frame [IsAlgClosed K] [CharZero K] (u z v : Fin 3 → K) (huu : pair u u = 0)
    (hvv : pair v v = 0) (huv : pair u v = 2) (hzz : pair z z = -1) (huz : pair u z = 0)
    (hzv : pair z v = 0) :
    ∃ a b c d : K, a * d - b * c ≠ 0 ∧ u = ![d ^ 2, 2 * c * d, c ^ 2] ∧
      z = ![b * d, a * d + b * c, a * c] ∧ v = ![b ^ 2, 2 * a * b, a ^ 2] := by
  obtain ⟨c, d, hu0, hu1, hu2⟩ := null_sq u huu
  obtain ⟨a, b, hv0, hv1, hv2⟩ := null_sq v hvv
  have hH : (a * d - b * c) ^ 2 = 1 := by
    simp only [pair] at huv; rw [hu0, hu1, hu2, hv0, hv1, hv2] at huv
    have : (2 : K) * ((a * d - b * c) ^ 2 - 1) = 0 := by linear_combination huv
    have := (mul_eq_zero.mp this).resolve_left two_ne_zero
    linear_combination this
  have hE1 : c ^ 2 * z 0 - c * d * z 1 + d ^ 2 * z 2 = 0 := by
    simp only [pair] at huz; rw [hu0, hu1, hu2] at huz
    have : (2 : K) * (c ^ 2 * z 0 - c * d * z 1 + d ^ 2 * z 2) = 0 := by linear_combination huz
    exact (mul_eq_zero.mp this).resolve_left two_ne_zero
  have hE2 : a ^ 2 * z 0 - a * b * z 1 + b ^ 2 * z 2 = 0 := by
    simp only [pair] at hzv; rw [hv0, hv1, hv2] at hzv
    have : (2 : K) * (a ^ 2 * z 0 - a * b * z 1 + b ^ 2 * z 2) = 0 := by linear_combination hzv
    exact (mul_eq_zero.mp this).resolve_left two_ne_zero
  set μ := -(2 * z 0 * a * c + 2 * z 2 * b * d - z 1 * (a * d + b * c)) with hμ
  have hz0 : z 0 = μ * (b * d) := by linear_combination b ^ 2 * hE1 + d ^ 2 * hE2 - z 0 * hH
  have hz1 : z 1 = μ * (a * d + b * c) := by
    linear_combination 2 * a * b * hE1 + 2 * c * d * hE2 - z 1 * hH
  have hz2 : z 2 = μ * (a * c) := by linear_combination a ^ 2 * hE1 + c ^ 2 * hE2 - z 2 * hH
  have hμ2 : μ ^ 2 = 1 := by
    simp only [pair] at hzz; rw [hz0, hz1, hz2] at hzz
    linear_combination -hzz + μ ^ 2 * hH
  have hdet : a * d - b * c ≠ 0 := by intro h; rw [h] at hH; simp at hH
  have hvec : v = ![b ^ 2, 2 * a * b, a ^ 2] := by
    funext i; fin_cases i <;> simp [hv0, hv1, hv2]
  have hμ' : (μ - 1) * (μ + 1) = 0 := by linear_combination hμ2
  rcases mul_eq_zero.mp hμ' with h | h
  · have h1 : μ = 1 := by linear_combination h
    refine ⟨a, b, c, d, hdet, ?_, ?_, hvec⟩
    · funext i; fin_cases i <;> simp [hu0, hu1, hu2]
    · funext i; fin_cases i <;> simp [hz0, hz1, hz2, h1]
  · have h1 : μ = -1 := by linear_combination h
    refine ⟨a, b, -c, -d, by intro h'; apply hdet; linear_combination -h', ?_, ?_, hvec⟩
    · funext i; fin_cases i <;> simp [hu0, hu1, hu2]
    · funext i; fin_cases i <;> simp [hz0, hz1, hz2, h1] <;> ring

/-- **`SO(3) = PGL(2)` for binary quadratics.** Two bases of binary quadratics with the same
Gram matrix for the discriminant pairing differ by one invertible substitution. -/
theorem so3 [IsAlgClosed K] [CharZero K] (q p : Fin 3 → Fin 3 → K)
    (hq : (Matrix.of q).det ≠ 0) (hp : ∀ i j, pair (p i) (p j) = pair (q i) (q j)) :
    ∃ a b c d : K, a * d - b * c ≠ 0 ∧ ∀ i, p i = qAct (q i) a b c d := by
  set Q : Matrix (Fin 3) (Fin 3) K := Matrix.of q with hQ
  set P : Matrix (Fin 3) (Fin 3) K := Matrix.of p with hP
  have hG : P * Pm * P.transpose = Q * Pm * Q.transpose := by
    ext i j; rw [gram_apply, gram_apply]; exact hp i j
  have hQu : IsUnit Q.det := isUnit_iff_ne_zero.mpr hq
  have hQtu : IsUnit Q.transpose.det := by rw [Matrix.det_transpose]; exact hQu
  set T := Q⁻¹ * P with hTdef
  have hT : T * Pm * T.transpose = Pm := by
    rw [hTdef, Matrix.transpose_mul, Matrix.transpose_nonsing_inv]
    calc Q⁻¹ * P * Pm * (P.transpose * Q.transpose⁻¹)
        = Q⁻¹ * (P * Pm * P.transpose) * Q.transpose⁻¹ := by simp only [Matrix.mul_assoc]
      _ = Q⁻¹ * Q * Pm * (Q.transpose * Q.transpose⁻¹) := by rw [hG]; simp only [Matrix.mul_assoc]
      _ = Pm := by rw [Matrix.nonsing_inv_mul Q hQu, Matrix.mul_nonsing_inv _ hQtu,
                    Matrix.one_mul, Matrix.mul_one]
  have hQT : Q * T = P := by
    rw [hTdef, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv Q hQu, Matrix.one_mul]
  have e : ∀ k l, pair (T k) (T l) = Pm k l := fun k l =>
    (gram_apply T k l).symm.trans (congrFun (congrFun hT k) l)
  obtain ⟨a, b, c, d, hdet, hu, hz, hv⟩ := frame (T 0) (T 1) (T 2)
    (by simpa [Pm] using e 0 0) (by simpa [Pm] using e 2 2) (by simpa [Pm] using e 0 2)
    (by simpa [Pm] using e 1 1) (by simpa [Pm] using e 0 1) (by simpa [Pm] using e 1 2)
  refine ⟨a, b, c, d, hdet, fun i => ?_⟩
  funext j
  have h := congrFun (congrFun hQT i) j
  simp only [Matrix.mul_apply, Fin.sum_univ_three, hQ, hP, Matrix.of_apply] at h
  rw [← h, hu, hz, hv]
  fin_cases j <;> simp [qAct] <;> ring

end T28SO3
