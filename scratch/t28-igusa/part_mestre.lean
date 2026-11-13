
/-! ## Mestre's argument, abstract form (glue for the generic case of `⇐`)

If two sextics `f, g` admit bases `(yᵢ)`, `(y'ᵢ)` of binary quadratics with the same Gram matrix
for `pair` and with `p6 g (y'ᵢy'ⱼy'ₖ) = p6 f (yᵢyⱼyₖ)` for all `i, j, k`, then `g` is equivalent
to `f`. For the Clebsch covariants `yᵢ = yᵢ(f)`, `y'ᵢ = yᵢ(g)` both families of numbers are
invariants of even degree, hence polynomials in `J₂, J₄, J₆, J₁₀` (identities M3 of the report),
so equal Igusa invariants and `det G ≠ 0` give the equivalence. -/

namespace PkgI1
open T28SO3

section Mestre
variable {K : Type*} [Field K]

/-- The invariant pairing of binary sextics (`60·Σ (-1)ⁱ uᵢ v₆₋ᵢ / C(6,i)`). -/
def p6 (u v : Fin 7 → K) : K :=
  60 * u 0 * v 6 - 10 * u 1 * v 5 + 4 * u 2 * v 4 - 3 * u 3 * v 3 + 4 * u 4 * v 2 -
    10 * u 5 * v 1 + 60 * u 6 * v 0

def cub {K : Type*} [Field K] (u v w : Fin 3 → K) : Fin 7 → K :=
  ![u 0 * v 0 * w 0,
    u 0 * v 0 * w 1 + u 0 * v 1 * w 0 + u 1 * v 0 * w 0,
    u 0 * v 0 * w 2 + u 0 * v 1 * w 1 + u 0 * v 2 * w 0 + u 1 * v 0 * w 1 + u 1 * v 1 * w 0 + u 2 * v 0 * w 0,
    u 0 * v 1 * w 2 + u 0 * v 2 * w 1 + u 1 * v 0 * w 2 + u 1 * v 1 * w 1 + u 1 * v 2 * w 0 + u 2 * v 0 * w 1 + u 2 * v 1 * w 0,
    u 0 * v 2 * w 2 + u 1 * v 1 * w 2 + u 1 * v 2 * w 1 + u 2 * v 0 * w 2 + u 2 * v 1 * w 1 + u 2 * v 2 * w 0,
    u 1 * v 2 * w 2 + u 2 * v 1 * w 2 + u 2 * v 2 * w 1,
    u 2 * v 2 * w 2]

theorem p6_actC (u v : Fin 7 → K) (a b c d : K) :
    p6 (actC u a b c d 1) (actC v a b c d 1) = (a * d - b * c) ^ 6 * p6 u v := by
  simp only [p6, actC, Matrix.cons_val]; ring

theorem cub_qAct (u v w : Fin 3 → K) (a b c d : K) :
    cub (qAct u a b c d) (qAct v a b c d) (qAct w a b c d) = actC (cub u v w) a b c d 1 := by
  funext m; fin_cases m <;> simp [cub, qAct, actC] <;> ring

theorem p6_sub (u v w : Fin 7 → K) (s : K) :
    p6 (fun i => u i - s * v i) w = p6 u w - s * p6 v w := by
  simp only [p6]; ring

theorem p6_cub_lin (h : Fin 7 → K) (y : Fin 3 → Fin 3 → K) (α β γ : Fin 3 → K) :
    p6 h (cub (fun l => ∑ i, α i * y i l) (fun l => ∑ j, β j * y j l) (fun l => ∑ k, γ k * y k l)) =
      ∑ i, ∑ j, ∑ k, α i * β j * γ k * p6 h (cub (y i) (y j) (y k)) := by
  simp only [p6, cub, Fin.sum_univ_three, Matrix.cons_val]; ring

/-- Products of three members of a basis of binary quadratics span the binary sextics, and `p6`
is nondegenerate. -/
theorem eq_zero_of_p6_cub (h : Fin 7 → K) [CharZero K] (y : Fin 3 → Fin 3 → K)
    (hy : (Matrix.of y).det ≠ 0) (H : ∀ i j k, p6 h (cub (y i) (y j) (y k)) = 0) : h = 0 := by
  set Y : Matrix (Fin 3) (Fin 3) K := Matrix.of y with hY
  have hYu : IsUnit Y.det := isUnit_iff_ne_zero.mpr hy
  have hCY : Y⁻¹ * Y = 1 := Matrix.nonsing_inv_mul Y hYu
  have hE : ∀ k l, ∑ i, Y⁻¹ k i * y i l = (1 : Matrix (Fin 3) (Fin 3) K) k l := fun k l => by
    rw [← hCY, Matrix.mul_apply]; rfl
  have key : ∀ k₁ k₂ k₃ : Fin 3, p6 h (cub (fun l => (1 : Matrix (Fin 3) (Fin 3) K) k₁ l)
      (fun l => (1 : Matrix (Fin 3) (Fin 3) K) k₂ l) (fun l => (1 : Matrix (Fin 3) (Fin 3) K) k₃ l))
        = 0 := fun k₁ k₂ k₃ => by
    have := p6_cub_lin h y (Y⁻¹ k₁) (Y⁻¹ k₂) (Y⁻¹ k₃)
    simp only [hE] at this
    rw [this]; simp [H]
  have k0 := key 0 0 0
  have k1 := key 0 0 1
  have k2 := key 0 0 2
  have k3 := key 0 1 2
  have k4 := key 0 2 2
  have k5 := key 1 2 2
  have k6 := key 2 2 2
  simp [p6, cub, Matrix.one_apply] at k0 k1 k2 k3 k4 k5 k6
  funext i; fin_cases i <;> simp_all

theorem det_ne_zero_of_gram (y y' : Fin 3 → Fin 3 → K) [CharZero K] (hy : (Matrix.of y).det ≠ 0)
    (hG : ∀ i j, pair (y' i) (y' j) = pair (y i) (y j)) : (Matrix.of y').det ≠ 0 := by
  have hM : Matrix.of y' * Pm K * (Matrix.of y').transpose =
      Matrix.of y * Pm K * (Matrix.of y).transpose := by
    ext i j; rw [gram_apply, gram_apply]; exact hG i j
  have hd := congrArg Matrix.det hM
  simp only [Matrix.det_mul, Matrix.det_transpose] at hd
  have hP : (Pm K).det = 4 := by
    simp [Pm, Matrix.det_fin_three]; norm_num
  rw [hP] at hd
  intro h0; rw [h0] at hd
  apply hy
  have : (Matrix.of y).det ^ 2 * 4 = 0 := by linear_combination -hd
  simpa using this

/-- **Mestre's separation step (abstract form), proved.** -/
theorem mestre_abstract [IsAlgClosed K] [CharZero K] (f g : Fin 7 → K)
    (y y' : Fin 3 → Fin 3 → K) (hy : (Matrix.of y).det ≠ 0)
    (hG : ∀ i j, pair (y' i) (y' j) = pair (y i) (y j))
    (ha : ∀ i j k, p6 g (cub (y' i) (y' j) (y' k)) = p6 f (cub (y i) (y j) (y k))) :
    ∃ M : Matrix (Fin 2) (Fin 2) K, M.det ≠ 0 ∧ ∃ e : K, e ≠ 0 ∧ g = sexticAct f M e := by
  obtain ⟨a, b, c, d, hdet, hy'⟩ := so3 y y' hy hG
  have hy'det := det_ne_zero_of_gram y y' hy hG
  have hδ : (a * d - b * c) ^ 6 ≠ 0 := pow_ne_zero 6 hdet
  have hz := eq_zero_of_p6_cub (fun i => g i - ((a * d - b * c) ^ 6)⁻¹ * actC f a b c d 1 i) y'
    hy'det (fun i j k => by
      rw [p6_sub, ha, hy' i, hy' j, hy' k, cub_qAct, p6_actC]; field_simp; ring)
  refine ⟨!![a, b; c, d], by rw [Matrix.det_fin_two_of]; exact hdet, ((a * d - b * c) ^ 6)⁻¹,
    inv_ne_zero hδ, ?_⟩
  rw [sexticAct_eq]
  funext i
  have := congrFun hz i
  simp only [Pi.zero_apply] at this
  have e := actC_scale f a b c d ((a * d - b * c) ^ 6)⁻¹
  simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.head_cons, Matrix.head_fin_const] at e ⊢
  rw [e]; linear_combination this

end Mestre

end PkgI1
