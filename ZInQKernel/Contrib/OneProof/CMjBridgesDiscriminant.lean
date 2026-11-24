import ZInQKernel.Contrib.OneProof.CMjBridgesPrint

namespace HDec.CMBranch.CMjBridges

open scoped UpperHalfPlane

/-- The ring of multipliers of a rotated and scaled lattice with normalized basis
`(1, τ)` is `ℤ[aτ] = ℤ + ℤ(aτ)`, for a primitive equation
`aτ² + bτ + c = 0`. This is the lattice computation in the p. 607/p. 612
discriminant comparison. -/
theorem mem_latticeMultipliers_iff {Λ : Submodule ℤ (Fin 1 → ℂ)}
    {s : ℂ} (hs : s ≠ 0) (τ : ℍ)
    (hΛ : ∀ z, z ∈ Λ ↔ ∃ m n : ℤ, z 0 = s * (m + n * (τ : ℂ)))
    {a b c : ℤ} (ha : a ≠ 0) (hprim : Int.gcd (Int.gcd a b) c = 1)
    (heq : (a : ℂ) * (τ : ℂ) ^ 2 + b * (τ : ℂ) + c = 0)
    (u : ℂ) : u ∈ latticeMultipliers Λ ↔ ∃ m n : ℤ, u = m + n * ((a : ℂ) * (τ : ℂ)) := by
  let t : ℂ := τ
  have ht : t.im ≠ 0 := (UpperHalfPlane.im_pos τ).ne'
  have hmem : u ∈ latticeMultipliers Λ ↔
      (∃ m n : ℤ, u = m + n * t) ∧ (∃ p q : ℤ, u * t = p + q * t) := by
    constructor
    · intro hu
      change ∀ z ∈ Λ, u • z ∈ Λ at hu
      have h1 : (fun _ : Fin 1 => s) ∈ Λ := (hΛ _).mpr ⟨1, 0, by simp⟩
      have h2 : (fun _ : Fin 1 => s * t) ∈ Λ := (hΛ _).mpr ⟨0, 1, by simp [t]⟩
      obtain ⟨m, n, hmn⟩ := (hΛ _).mp (hu _ h1)
      obtain ⟨p, q, hpq⟩ := (hΛ _).mp (hu _ h2)
      simp only [Pi.smul_apply, smul_eq_mul] at hmn hpq
      refine ⟨⟨m, n, mul_left_cancel₀ hs ?_⟩, ⟨p, q, mul_left_cancel₀ hs ?_⟩⟩
      · change s * u = s * ((m : ℂ) + n * (τ : ℂ))
        rw [← hmn]; ring
      · change s * (u * t) = s * ((p : ℂ) + q * (τ : ℂ))
        rw [← hpq]; ring
    · rintro ⟨⟨m, n, hmn⟩, ⟨p, q, hpq⟩⟩
      change ∀ z ∈ Λ, u • z ∈ Λ
      intro z hz
      obtain ⟨r, w, hrw⟩ := (hΛ _).mp hz
      refine (hΛ _).mpr ⟨r * m + w * p, r * n + w * q, ?_⟩
      simp only [Pi.smul_apply, smul_eq_mul, hrw]
      change u * (s * ((r : ℂ) + w * t)) =
        s * (((r * m + w * p : ℤ) : ℂ) + ((r * n + w * q : ℤ) : ℂ) * t)
      push_cast
      linear_combination (s * r) * hmn + (s * w) * hpq
  rw [hmem]
  constructor
  · rintro ⟨⟨m, n, hmn⟩, hpq⟩
    rw [hmn] at hpq
    obtain ⟨v, rfl⟩ := (mult_iff_dvd ht ha hprim heq m n).mp hpq
    refine ⟨m, v, ?_⟩
    rw [hmn]
    push_cast
    ring
  · rintro ⟨m, v, hmv⟩
    have h : u = (m : ℂ) + ((a * v : ℤ) : ℂ) * t := by
      rw [hmv]
      dsimp [t]
      push_cast
      ring
    refine ⟨⟨m, a * v, h⟩, ?_⟩
    rw [h]
    exact (mult_iff_dvd ht ha hprim heq m (a * v)).mpr ⟨v, rfl⟩

/-- A nonreal period has only one primitive discriminant. Positivity fixes the
sign of the primitive equation. -/
theorem periodDiscriminant_unique {τ : ℍ} {D D' : ℤ}
    (h : PeriodDiscriminant τ D) (h' : PeriodDiscriminant τ D') : D = D' := by
  obtain ⟨a, b, c, ha, hp, hq, rfl⟩ := h
  obtain ⟨a', b', c', ha', hp', hq', rfl⟩ := h'
  have hlin : ((a' * b - a * b' : ℤ) : ℂ) * (τ : ℂ) + ((a' * c - a * c' : ℤ) : ℂ) = 0 := by
    push_cast
    linear_combination (a' : ℂ) * hq - (a : ℂ) * hq'
  have hi := congrArg Complex.im hlin
  simp only [Complex.add_im, Complex.mul_im, Complex.intCast_im, Complex.intCast_re,
    Complex.zero_im, zero_mul, add_zero] at hi
  have hB : a' * b = a * b' := by
    have hz := (mul_eq_zero.mp hi).resolve_right (UpperHalfPlane.im_pos τ).ne'
    exact sub_eq_zero.mp (by exact_mod_cast hz)
  have hC : a' * c = a * c' := by
    rw [hB, sub_self, Int.cast_zero, zero_mul, zero_add] at hlin
    exact sub_eq_zero.mp (by exact_mod_cast hlin)
  have hdiv : a ∣ a' := dvd_of_dvd_mul_prim hp ⟨b', hB⟩ ⟨c', hC⟩
  have hdiv' : a' ∣ a := dvd_of_dvd_mul_prim hp' ⟨b, hB.symm⟩ ⟨c, hC.symm⟩
  have he : a = a' := le_antisymm (Int.le_of_dvd ha' hdiv) (Int.le_of_dvd ha hdiv')
  subst a'
  rw [mul_left_cancel₀ ha.ne' hB, mul_left_cancel₀ ha.ne' hC]

/-- Given a period lattice with multiplier ring `R`, every primitive form
discriminant for the period is `orderDisc R`. The existing Cox lattice proof
computes the trace discriminant using the basis `(1, aτ)` of the multiplier ring. -/
theorem periodDiscriminant_iff_orderDisc {k : Type} [Field k] [NumberField k] (R : Subring k)
    (hR : IsImagQuadOrder k R) {Λ : Submodule ℤ (Fin 1 → ℂ)}
    {s : ℂ} (hs : s ≠ 0) (τ : ℍ)
    (hΛ : ∀ z, z ∈ Λ ↔ ∃ m n : ℤ, z 0 = s * (m + n * (τ : ℂ)))
    (hRing : Nonempty (R ≃+* latticeMultipliers Λ)) (Δ : ℤ) :
    PeriodDiscriminant τ Δ ↔ Δ = orderDisc R := by
  have hD : PeriodDiscriminant τ (orderDisc R) :=
    coxProperLattice_proof k R hR Λ s τ hs (UpperHalfPlane.im_pos τ) hΛ hRing
  exact ⟨fun h => periodDiscriminant_unique h hD, fun h => h.symm ▸ hD⟩

end HDec.CMBranch.CMjBridges
