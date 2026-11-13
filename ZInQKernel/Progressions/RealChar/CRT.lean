import ZInQKernel.Progressions.RealChar.Local

/-!
# Real characters modulo a product of coprime moduli

A Dirichlet character modulo `m * n`, with `m` and `n` coprime, is the product of its components
modulo `m` and modulo `n` (through `ZMod.chineseRemainder`); the components of a real character
are real, and the integers `d` of the classification multiply.
-/

namespace ZInQ.Progressions

variable {m n : ℕ}

/-- The component modulo `m` of a character modulo `m * n`: `a ↦ χ (CRT (a, 1))`. -/
def realCharCrtLeft (h : m.Coprime n) (χ : DirichletCharacter ℂ (m * n)) :
    DirichletCharacter ℂ m where
  toFun a := χ ((ZMod.chineseRemainder h).symm (a, 1))
  map_one' := by
    show χ ((ZMod.chineseRemainder h).symm 1) = 1
    rw [map_one, map_one]
  map_mul' a b := by
    show χ ((ZMod.chineseRemainder h).symm (a * b, 1)) =
      χ ((ZMod.chineseRemainder h).symm (a, 1)) * χ ((ZMod.chineseRemainder h).symm (b, 1))
    rw [← map_mul, ← map_mul, Prod.mk_mul_mk, mul_one]
  map_nonunit' a ha := by
    apply χ.map_nonunit
    intro hu
    apply ha
    have := hu.map (ZMod.chineseRemainder h)
    rw [RingEquiv.apply_symm_apply] at this
    exact (Prod.isUnit_iff.mp this).1

/-- The component modulo `n` of a character modulo `m * n`: `b ↦ χ (CRT (1, b))`. -/
def realCharCrtRight (h : m.Coprime n) (χ : DirichletCharacter ℂ (m * n)) :
    DirichletCharacter ℂ n where
  toFun b := χ ((ZMod.chineseRemainder h).symm (1, b))
  map_one' := by
    show χ ((ZMod.chineseRemainder h).symm 1) = 1
    rw [map_one, map_one]
  map_mul' a b := by
    show χ ((ZMod.chineseRemainder h).symm (1, a * b)) =
      χ ((ZMod.chineseRemainder h).symm (1, a)) * χ ((ZMod.chineseRemainder h).symm (1, b))
    rw [← map_mul, ← map_mul, Prod.mk_mul_mk, mul_one]
  map_nonunit' a ha := by
    apply χ.map_nonunit
    intro hu
    apply ha
    have := hu.map (ZMod.chineseRemainder h)
    rw [RingEquiv.apply_symm_apply] at this
    exact (Prod.isUnit_iff.mp this).2

theorem realCharCrtLeft_apply (h : m.Coprime n) (χ : DirichletCharacter ℂ (m * n)) (a : ZMod m) :
    realCharCrtLeft h χ a = χ ((ZMod.chineseRemainder h).symm (a, 1)) := rfl

theorem realCharCrtRight_apply (h : m.Coprime n) (χ : DirichletCharacter ℂ (m * n))
    (b : ZMod n) : realCharCrtRight h χ b = χ ((ZMod.chineseRemainder h).symm (1, b)) := rfl

/-- `χ` is the product of its two components. -/
theorem realCharCrt_apply (h : m.Coprime n) (χ : DirichletCharacter ℂ (m * n))
    (x : ZMod (m * n)) :
    χ x = realCharCrtLeft h χ (ZMod.chineseRemainder h x).1 *
      realCharCrtRight h χ (ZMod.chineseRemainder h x).2 := by
  rw [realCharCrtLeft_apply, realCharCrtRight_apply, ← map_mul, ← map_mul, Prod.mk_mul_mk,
    mul_one, one_mul, RingEquiv.symm_apply_apply]

theorem realCharCrtLeft_sq (h : m.Coprime n) {χ : DirichletCharacter ℂ (m * n)}
    (hχ : χ ^ 2 = 1) : realCharCrtLeft h χ ^ 2 = 1 := by
  refine MulChar.ext fun a => ?_
  rw [MulChar.pow_apply' _ two_ne_zero, MulChar.one_apply_coe, realCharCrtLeft_apply]
  exact realChar_apply_sq_eq_one hχ
    ((Prod.isUnit_iff.mpr ⟨a.isUnit, isUnit_one⟩).map (ZMod.chineseRemainder h).symm)

theorem realCharCrtRight_sq (h : m.Coprime n) {χ : DirichletCharacter ℂ (m * n)}
    (hχ : χ ^ 2 = 1) : realCharCrtRight h χ ^ 2 = 1 := by
  refine MulChar.ext fun a => ?_
  rw [MulChar.pow_apply' _ two_ne_zero, MulChar.one_apply_coe, realCharCrtRight_apply]
  exact realChar_apply_sq_eq_one hχ
    ((Prod.isUnit_iff.mpr ⟨isUnit_one, a.isUnit⟩).map (ZMod.chineseRemainder h).symm)

/-- The classification is multiplicative in coprime moduli. -/
theorem realChar_coprime_mul (h : m.Coprime n)
    (h₁ : ∀ χ₁ : DirichletCharacter ℂ m, χ₁ ^ 2 = 1 → ∃ d : ℤ, RealCharData m χ₁ d)
    (h₂ : ∀ χ₂ : DirichletCharacter ℂ n, χ₂ ^ 2 = 1 → ∃ d : ℤ, RealCharData n χ₂ d)
    (χ : DirichletCharacter ℂ (m * n)) (hχ : χ ^ 2 = 1) :
    ∃ d : ℤ, RealCharData (m * n) χ d := by
  obtain ⟨d₁, sq₁, dvd₁, two₁, leg₁⟩ := h₁ _ (realCharCrtLeft_sq h hχ)
  obtain ⟨d₂, sq₂, dvd₂, two₂, leg₂⟩ := h₂ _ (realCharCrtRight_sq h hχ)
  refine ⟨d₁ * d₂, ?_, ?_, ?_, ?_⟩
  · rw [← Int.squarefree_natAbs, Int.natAbs_mul, Nat.squarefree_mul_iff]
    exact ⟨Nat.Coprime.of_dvd dvd₁ dvd₂ h, Int.squarefree_natAbs.mpr sq₁,
      Int.squarefree_natAbs.mpr sq₂⟩
  · rw [Int.natAbs_mul]; exact Nat.mul_dvd_mul dvd₁ dvd₂
  · intro h2
    rcases Int.prime_two.dvd_or_dvd h2 with h' | h'
    · exact (two₁ h').mul_right n
    · exact (two₂ h').mul_left m
  · intro ℓ _ hdvd
    have hℓm : ¬ ℓ ∣ 2 * m := fun h' =>
      hdvd (h'.trans (Nat.mul_dvd_mul_left 2 (dvd_mul_right m n)))
    have hℓn : ¬ ℓ ∣ 2 * n := fun h' =>
      hdvd (h'.trans (Nat.mul_dvd_mul_left 2 (dvd_mul_left n m)))
    rw [realCharCrt_apply h χ, map_natCast, Prod.fst_natCast, Prod.snd_natCast, leg₁ ℓ hℓm,
      leg₂ ℓ hℓn, legendreSym.mul]
    push_cast
    ring

end ZInQ.Progressions
