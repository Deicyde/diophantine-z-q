import ZInQKernel.HDecomp.Textbook.Igusa.Generic

/-!
# T28, special locus: the family `x⁶ + a x⁴ + b x² + 1` (task igusa-special)

Sextics with an involution `x ↦ -x` besides the hyperelliptic one are, up to `GL₂ × 𝔾_m`,
`E a b = x⁶ + a x⁴ + b x² + 1`. This file proves (`E_sep`) that two members of the family whose
Igusa invariants agree in weighted projective space `P(1,2,3,5)` are equivalent.

Computation (`scratch/igusa-special/t5.py … t13.py`): with `u = ab`, `v = a³ + b³` the Igusa
invariants of `E a b` are `J2 = -32u - 480`, `J4 = J4uv u v`, `J6 = J6uv u v`,
`J10 = J10uv u v`. If `J(E a' b') = r · J(E a b)` (weights `1, 2, 3, 5`), then either `r = 1`,
and `(u', v') = (u, v)`, so `(a', b')` lies in the orbit of `(a, b)` under `x ↦ ωx` (`ω³ = 1`)
and `x ↦ 1/x`; or `r ≠ 1`, and then `r = ρ²` with `u = t²`, `v = 2t³`, `u' = t'²`,
`v' = 2t'³`, `t = 4/ρ - 1`, `t' = 4ρ - 1`: both lie on the `D₄`-sub-family `a = b`
(curves with reduced automorphism group containing `V₄`, whose two non-conjugate involution
classes give two normal forms) and `(1 - X)⁶ E(t,t)((1+X)/(1-X)) = (8/ρ) · E(t',t')`.
No `sorry`, no `axiom`.
-/

namespace T28Special
open PkgI1

section Eqv
variable {K : Type*} [Field K]

/-- Equivalence of binary sextics under `GL₂ × 𝔾_m` (in the coordinates of `PkgI1.actC`). -/
def Eqv (f g : Fin 7 → K) : Prop :=
  ∃ a b c d e : K, a * d - b * c ≠ 0 ∧ e ≠ 0 ∧ g = actC f a b c d e

theorem actC_id (f : Fin 7 → K) : actC f 1 0 0 1 1 = f := by
  funext i; fin_cases i <;> simp [actC]

theorem actC_diag (f : Fin 7 → K) (δ E : K) : actC f δ 0 0 δ E = fun i => E * δ ^ 6 * f i := by
  funext i; fin_cases i <;> simp [actC] <;> ring

theorem Eqv.refl (f : Fin 7 → K) : Eqv f f :=
  ⟨1, 0, 0, 1, 1, by simp, one_ne_zero, (actC_id f).symm⟩

theorem Eqv.trans {f g h : Fin 7 → K} (h1 : Eqv f g) (h2 : Eqv g h) : Eqv f h := by
  obtain ⟨a, b, c, d, e, hd, he, rfl⟩ := h1
  obtain ⟨a', b', c', d', e', hd', he', rfl⟩ := h2
  refine ⟨_, _, _, _, _, ?_, mul_ne_zero he he', actC_actC f a b c d e a' b' c' d' e'⟩
  rw [show (a * a' + b * c') * (c * b' + d * d') - (a * b' + b * d') * (c * a' + d * c') =
    (a * d - b * c) * (a' * d' - b' * c') by ring]
  exact mul_ne_zero hd hd'

theorem Eqv.symm {f g : Fin 7 → K} (h : Eqv f g) : Eqv g f := by
  obtain ⟨a, b, c, d, e, hd, he, rfl⟩ := h
  refine ⟨d, -b, -c, a, (e * (a * d - b * c) ^ 6)⁻¹, ?_,
    inv_ne_zero (mul_ne_zero he (pow_ne_zero 6 hd)), ?_⟩
  · rw [show d * a - -b * -c = a * d - b * c by ring]; exact hd
  · rw [actC_actC, show a * d + b * -c = a * d - b * c by ring, show a * -b + b * a = 0 by ring,
      show c * d + d * -c = 0 by ring, show c * -b + d * a = a * d - b * c by ring, actC_diag]
    funext i
    field_simp

theorem Eqv.of_actC (f : Fin 7 → K) (a b c d e : K) (hd : a * d - b * c ≠ 0) (he : e ≠ 0) :
    Eqv f (actC f a b c d e) := ⟨a, b, c, d, e, hd, he, rfl⟩

theorem Eqv.of_eq {f g h : Fin 7 → K} (h1 : Eqv f g) (h2 : g = h) : Eqv f h := h2 ▸ h1

theorem Eqv.sexticAct {f g : Fin 7 → K} (h : Eqv f g) :
    ∃ M : Matrix (Fin 2) (Fin 2) K, M.det ≠ 0 ∧ ∃ e : K, e ≠ 0 ∧ g = sexticAct f M e := by
  obtain ⟨a, b, c, d, e, hd, he, rfl⟩ := h
  exact ⟨!![a, b; c, d], by rw [Matrix.det_fin_two_of]; exact hd, e, he, by rw [sexticAct_eq]; rfl⟩

/-- The transformation law of the Igusa invariants along an equivalence. -/
theorem Eqv.J [CharZero K] {f g : Fin 7 → K} (h : Eqv f g) :
    ∃ ρ : K, ρ ≠ 0 ∧ J2 g = ρ ^ 2 * J2 f ∧ J4 g = ρ ^ 4 * J4 f ∧ J6 g = ρ ^ 6 * J6 f ∧
      J10 g = ρ ^ 10 * J10 f := by
  obtain ⟨M, hM, e, he, rfl⟩ := h.sexticAct
  exact ⟨e * M.det ^ 3, mul_ne_zero he (pow_ne_zero 3 hM), J2_sexticAct f M hM e,
    J4_sexticAct f M hM e, J6_sexticAct f M hM e, J10_sexticAct f M hM e⟩

theorem Eqv.J10_ne_zero [CharZero K] {f g : Fin 7 → K} (h : Eqv f g) (hf : J10 f ≠ 0) :
    J10 g ≠ 0 := by
  obtain ⟨ρ, hρ, -, -, -, h10⟩ := h.J
  rw [h10]; exact mul_ne_zero (pow_ne_zero 10 hρ) hf

end Eqv

section Family
variable {K : Type*} [Field K]

/-- `x⁶ + a x⁴ + b x² + 1`. -/
def E (a b : K) : Fin 7 → K := ![1, 0, b, 0, a, 0, 1]

def J4uv (u v : K) : K := -128 * v + 32 * u ^ 2 + 2624 * u + 5280

def J6uv (u v : K) : K := 128 * J4uv u v - 131072 * (3 * u + 5)

def J10uv (u v : K) : K :=
  -262144 * (v ^ 2 - 2 * u ^ 3) + 131072 * u ^ 2 * v - 16384 * u ^ 4 + 2359296 * u * v -
    1114112 * u ^ 3 - 3538944 * v - 4423680 * u ^ 2 + 15925248 * u - 11943936

/-- The relation forced by `J₄, J₆` when `r ≠ 1`. -/
def E3uv (u v r : K) : K :=
  r ^ 2 * J4uv u v - 1024 * (3 * r * (u + 15) * (1 + r) - 40 * (1 + r + r ^ 2))

/-- The relation forced by `J₁₀` when `r ≠ 1`. -/
def Qf (u r : K) : K := r ^ 2 * u ^ 2 - 2 * r * (16 + r) * u + (16 - r) ^ 2

theorem J2_E (a b : K) : J2 (E a b) = -32 * (a * b) - 480 := by
  simp [J2, E]; ring

theorem J4_E (a b : K) : J4 (E a b) = J4uv (a * b) (a ^ 3 + b ^ 3) := by
  simp [J4, E, J4uv]; ring

theorem J6_E (a b : K) : J6 (E a b) = J6uv (a * b) (a ^ 3 + b ^ 3) := by
  simp [J6, E, J6uv, J4uv]; ring

set_option maxHeartbeats 4000000 in
theorem J10_E (a b : K) : J10 (E a b) = J10uv (a * b) (a ^ 3 + b ^ 3) := by
  rw [J10_eq]
  simp [J10R, J10R0, J10R1, J10R2, J10R3, J10R4, J10R5, J10R6, J10R7, J10R8, J10R9, E, J10uv]
  ring

/-- The elimination: equal weighted invariants with `r ≠ 1` force `E3uv = 0` and `Qf = 0`. -/
theorem fam_alg [CharZero K] (u v u' v' r : K) (hr : r ≠ 0) (hr1 : r ≠ 1)
    (h2 : -32 * u' - 480 = r * (-32 * u - 480)) (h4 : J4uv u' v' = r ^ 2 * J4uv u v)
    (h6 : J6uv u' v' = r ^ 3 * J6uv u v) (h10 : J10uv u' v' = r ^ 5 * J10uv u v) :
    E3uv u v r = 0 ∧ Qf u r = 0 := by
  have hE : (1 - r) * (128 * E3uv u v r) = 0 := by
    simp only [E3uv, J6uv, J4uv] at h4 h6 ⊢
    linear_combination h6 - 128 * h4 - 12288 * h2
  have hE3 : E3uv u v r = 0 := by
    rcases mul_eq_zero.mp hE with h | h
    · exact absurd (by linear_combination -h) hr1
    · simpa using h
  refine ⟨hE3, ?_⟩
  have hu' : u' = r * (u + 15) - 15 := by linear_combination h2 / (-32)
  have hv' : v' = (32 * u' ^ 2 + 2624 * u' + 5280 - r ^ 2 * J4uv u v) / 128 := by
    simp only [J4uv] at h4 ⊢; linear_combination (-1 / 128 : K) * h4
  subst hv'
  subst hu'
  have key : (-274877906944 : K) * (r ^ 4 * (1 - r) ^ 3 * Qf u r) = 0 := by
    simp only [J10uv, J4uv, E3uv, Qf] at h10 hE3 ⊢
    linear_combination (128 * r ^ 2) ^ 2 * h10 -
      ((8388608 : K) * u ^ 2 * r ^ 7 + (-8388608 : K) * u ^ 2 * r ^ 6 + (419430400 : K) * u * r ^ 7 + (-687865856 : K) * u * r ^ 6 + (268435456 : K) * u * r ^ 5 + (-33554432 : K) * v * r ^ 7 + (33554432 : K) * v * r ^ 6 + (-494927872 : K) * r ^ 7 + (-1384120320 : K) * r ^ 6 + (4026531840 : K) * r ^ 5 + (-2147483648 : K) * r ^ 4) * hE3
  have h1r : (1 - r) ≠ 0 := fun h => hr1 (by linear_combination -h)
  have := pow_ne_zero 4 hr
  have := pow_ne_zero 3 h1r
  simpa [this, hr, h1r] using key

/-- `x ↦ ωx` with `ω³ = 1`. -/
theorem E_rot (a b ω : K) (hω : ω ^ 3 = 1) : Eqv (E a b) (E (a * ω) (b * ω ^ 2)) := by
  have hω0 : ω ≠ 0 := by rintro rfl; norm_num at hω
  have key : actC (E a b) ω 0 0 1 1 = ![1, 0, b * ω ^ 2, 0, a * ω ^ 4, 0, ω ^ 6] := by
    funext i; fin_cases i <;> simp [actC, E, -mul_eq_mul_left_iff, -mul_eq_mul_right_iff] <;> ring
  refine (Eqv.of_actC (E a b) ω 0 0 1 1 (by simpa using hω0) one_ne_zero).of_eq ?_
  rw [key, show ω ^ 4 = ω by linear_combination ω * hω,
    show ω ^ 6 = 1 by linear_combination (ω ^ 3 + 1) * hω]
  rfl

/-- `x ↦ 1/x`. -/
theorem E_swap (a b : K) : Eqv (E a b) (E b a) := by
  refine (Eqv.of_actC (E a b) 0 1 1 0 1 (by norm_num) one_ne_zero).of_eq ?_
  funext i; fin_cases i <;> simp [actC, E]

theorem E_orbit_aux (a b a' b' : K) (hu : a * b = a' * b') (h3 : a' ^ 3 = a ^ 3)
    (hv : a ^ 3 + b ^ 3 = a' ^ 3 + b' ^ 3) : Eqv (E a b) (E a' b') := by
  have hb3 : b' ^ 3 = b ^ 3 := by linear_combination -hv - h3
  by_cases ha : a = 0
  · subst ha
    have ha' : a' = 0 := by simpa using h3
    subst ha'
    by_cases hb : b = 0
    · subst hb
      have hb' : b' = 0 := by simpa using hb3
      subst hb'; exact Eqv.refl _
    · set ω := b' / b with hω
      have hω3 : ω ^ 3 = 1 := by rw [hω, div_pow, hb3, div_self (pow_ne_zero 3 hb)]
      have hbω : b * ω = b' := by rw [hω]; field_simp
      have h23 : (ω ^ 2) ^ 3 = 1 := by rw [← pow_mul, show 2 * 3 = 3 * 2 by rfl, pow_mul, hω3,
        one_pow]
      refine (E_rot 0 b (ω ^ 2) h23).of_eq ?_
      rw [zero_mul, show b * (ω ^ 2) ^ 2 = b * ω * ω ^ 3 by ring, hω3, hbω, mul_one]
  · have ha3 : a' ^ 3 ≠ 0 := by rw [h3]; exact pow_ne_zero 3 ha
    have ha' : a' ≠ 0 := fun h => ha3 (by rw [h]; ring)
    set ω := a' / a with hω
    have hω3 : ω ^ 3 = 1 := by rw [hω, div_pow, h3, div_self (pow_ne_zero 3 ha)]
    have haω : a * ω = a' := by rw [hω]; field_simp
    have hbω : b * ω ^ 2 = b' := by
      have h1 : b = ω * b' := by
        apply mul_left_cancel₀ ha; rw [hu, ← haω]; ring
      rw [h1]; linear_combination b' * hω3
    exact (E_rot a b ω hω3).of_eq (by rw [haω, hbω])

/-- Equal `u = ab`, `v = a³ + b³` give equivalent members of the family. -/
theorem E_orbit (a b a' b' : K) (hu : a * b = a' * b') (hv : a ^ 3 + b ^ 3 = a' ^ 3 + b' ^ 3) :
    Eqv (E a b) (E a' b') := by
  have h : (a' ^ 3 - a ^ 3) * (a' ^ 3 - b ^ 3) = 0 := by
    linear_combination (-a' ^ 3) * hv + ((a * b) ^ 2 + a * b * (a' * b') + (a' * b') ^ 2) * hu
  rcases mul_eq_zero.mp h with h | h
  · exact E_orbit_aux a b a' b' hu (by linear_combination h) hv
  · exact (E_swap a b).trans (E_orbit_aux b a a' b' (by rw [← hu]; ring) (by linear_combination h)
      (by rw [← hv]; ring))

/-- The second involution class on the `D₄`-sub-family `a = b`:
`(1 - X)⁶ E(t,t)((1+X)/(1-X)) = (8/ρ) E(t',t')` for `t = 4/ρ - 1`, `t' = 4ρ - 1`. -/
theorem E_D4 [CharZero K] (ρ : K) (hρ : ρ ≠ 0) :
    Eqv (E (4 / ρ - 1) (4 / ρ - 1)) (E (4 * ρ - 1) (4 * ρ - 1)) := by
  refine (Eqv.of_actC _ 1 1 (-1) 1 (ρ / 8) (by norm_num) (div_ne_zero hρ (by norm_num))).of_eq ?_
  funext i; fin_cases i <;> simp [actC, E] <;> field_simp <;> ring

/-- **Separation inside the family `x⁶ + a x⁴ + b x² + 1`.** -/
theorem E_sep [CharZero K] [IsAlgClosed K] (a b a' b' r : K) (hr : r ≠ 0)
    (h2 : J2 (E a' b') = r * J2 (E a b)) (h4 : J4 (E a' b') = r ^ 2 * J4 (E a b))
    (h6 : J6 (E a' b') = r ^ 3 * J6 (E a b)) (h10 : J10 (E a' b') = r ^ 5 * J10 (E a b)) :
    Eqv (E a b) (E a' b') := by
  rw [J2_E, J2_E] at h2
  rw [J4_E, J4_E] at h4
  rw [J6_E, J6_E] at h6
  rw [J10_E, J10_E] at h10
  by_cases hr1 : r = 1
  · subst hr1
    have hu : a * b = a' * b' := by linear_combination h2 / 32
    have hv : a ^ 3 + b ^ 3 = a' ^ 3 + b' ^ 3 := by
      simp only [J4uv] at h4; rw [← hu] at h4; linear_combination h4 / 128
    exact E_orbit a b a' b' hu hv
  obtain ⟨hE3, hQ⟩ := fam_alg (a * b) (a ^ 3 + b ^ 3) (a' * b') (a' ^ 3 + b' ^ 3) r hr hr1 h2 h4
    h6 h10
  obtain ⟨ρ₀, hρ₀⟩ := IsAlgClosed.exists_pow_nat_eq r (by norm_num : 0 < 2)
  have hfac : (r * (a * b) - (4 - ρ₀) ^ 2) * (r * (a * b) - (4 + ρ₀) ^ 2) = 0 := by
    rw [← hρ₀] at hQ ⊢; simp only [Qf] at hQ; linear_combination hQ
  obtain ⟨ρ, hρ, hu⟩ : ∃ ρ : K, ρ ^ 2 = r ∧ r * (a * b) = (4 - ρ) ^ 2 := by
    rcases mul_eq_zero.mp hfac with h | h
    · exact ⟨ρ₀, hρ₀, by linear_combination h⟩
    · exact ⟨-ρ₀, by rw [← hρ₀]; ring, by linear_combination h⟩
  have hρ0 : ρ ≠ 0 := by rintro rfl; apply hr; rw [← hρ]; ring
  subst hρ
  set u := a * b with hu_def
  set v := a ^ 3 + b ^ 3 with hv_def
  have hv3 : ρ ^ 3 * v = 2 * (4 - ρ) ^ 3 := by
    have h1 : ρ * (ρ ^ 3 * v - 2 * (4 - ρ) ^ 3) = 0 := by
      simp only [E3uv, J4uv] at hE3
      linear_combination (-1 / 128 : K) * hE3 + (-1 / 128 : K) *
        ((-32 : K) * u * ρ ^ 2 + (416 : K) * ρ ^ 2 + (256 : K) * ρ + (2560 : K)) * hu
    rcases mul_eq_zero.mp h1 with h | h
    · exact absurd h hρ0
    · linear_combination h
  have hU : a' * b' = ρ ^ 2 * (u + 15) - 15 := by linear_combination -h2 / 32
  have hu' : a' * b' = (4 * ρ - 1) ^ 2 := by linear_combination hU + hu
  have hv' : a' ^ 3 + b' ^ 3 = 2 * (4 * ρ - 1) ^ 3 := by
    simp only [J4uv] at h4
    rw [hU] at h4
    linear_combination (-1 / 128 : K) * h4 + ρ * hv3 + ((-13 : K) * ρ ^ 2 + (13 : K)) * hu
  have ht : ρ * (4 / ρ - 1) = 4 - ρ := by field_simp
  have h1 : Eqv (E a b) (E (4 / ρ - 1) (4 / ρ - 1)) := by
    apply E_orbit
    · apply mul_left_cancel₀ (pow_ne_zero 2 hρ0)
      rw [hu]; linear_combination (-(ρ * (4 / ρ - 1)) - (4 - ρ)) * ht
    · apply mul_left_cancel₀ (pow_ne_zero 3 hρ0)
      rw [hv3]
      linear_combination (-2 * ((ρ * (4 / ρ - 1)) ^ 2 + (ρ * (4 / ρ - 1)) * (4 - ρ) +
        (4 - ρ) ^ 2)) * ht
  have h3 : Eqv (E (4 * ρ - 1) (4 * ρ - 1)) (E a' b') :=
    E_orbit _ _ _ _ (by rw [hu']; ring) (by rw [hv']; ring)
  exact (h1.trans (E_D4 ρ hρ0)).trans h3

end Family

end T28Special
