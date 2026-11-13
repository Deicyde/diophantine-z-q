import Mathlib.Algebra.Group.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic.Abel

/-!
# An explicit power cochain for a normalized sign cocycle

This is an algebraic helper, not the unramified Galois assertion.  The coefficient
commutative group is arbitrary.  The product formula and every cancellation are
proved here; no cohomological-dimension assertion is used.
-/

namespace ZInQ.Contrib.UnramifiedCocycle

variable {G U : Type*} [Group G] [CommGroup U]

/-- The trivial-action two-cocycle equation, in the baseline's convention. -/
def CocycleLaw (η : G → G → U) : Prop :=
  ∀ x y z, η (x * y) z * η x y = η y z * η x (y * z)

/-- The finite product of the inverse cocycle values along powers of a generator. -/
def powerCochain (η : G → G → U) (g : G) (k : ℕ) : U :=
  ∏ i ∈ Finset.range k, (η (g ^ i) g)⁻¹

@[simp] theorem powerCochain_zero (η : G → G → U) (g : G) :
    powerCochain η g 0 = 1 := by
  simp [powerCochain]

@[simp] theorem powerCochain_succ (η : G → G → U) (g : G) (k : ℕ) :
    powerCochain η g (k + 1) = powerCochain η g k * (η (g ^ k) g)⁻¹ := by
  simp [powerCochain, Finset.prod_range_succ, mul_comm]

/-- The product is sign-valued if every cocycle value is sign-valued. -/
theorem powerCochain_sq (η : G → G → U) (g : G)
    (hs : ∀ x y, η x y ^ 2 = 1) (k : ℕ) : powerCochain η g k ^ 2 = 1 := by
  induction k with
  | zero => simp
  | succ k ih => simp [powerCochain_succ, mul_pow, inv_pow, hs, ih]

/-- Induction on the second exponent is the connecting cochain calculation. -/
theorem powerCochain_mul (η : G → G → U) (g : G)
    (hc : CocycleLaw η) (hunit : ∀ x, η x 1 = 1) (k l : ℕ) :
    η (g ^ k) (g ^ l) * powerCochain η g (k + l) =
      powerCochain η g k * powerCochain η g l := by
  induction l with
  | zero => simp [hunit]
  | succ l ih =>
    have h := hc (g ^ k) (g ^ l) g
    rw [← pow_add, ← pow_succ] at h
    have he : η (g ^ k) (g ^ (l + 1)) =
        η (g ^ (k + l)) g * η (g ^ k) (g ^ l) * (η (g ^ l) g)⁻¹ := by
      apply (eq_mul_inv_iff_mul_eq).2
      calc
        η (g ^ k) (g ^ (l + 1)) * η (g ^ l) g =
            η (g ^ l) g * η (g ^ k) (g ^ (l + 1)) := mul_comm _ _
        _ = η (g ^ (k + l)) g * η (g ^ k) (g ^ l) := h.symm
    simp only [Nat.add_succ, powerCochain_succ]
    calc
      η (g ^ k) (g ^ (l + 1)) *
          (powerCochain η g (k + l) * (η (g ^ (k + l)) g)⁻¹) =
          (η (g ^ k) (g ^ l) * powerCochain η g (k + l)) * (η (g ^ l) g)⁻¹ := by
            rw [he]
            apply Additive.ofMul.injective
            simp only [ofMul_mul, ofMul_inv]
            abel
      _ = (powerCochain η g k * powerCochain η g l) * (η (g ^ l) g)⁻¹ := by rw [ih]
      _ = powerCochain η g k * (powerCochain η g l * (η (g ^ l) g)⁻¹) :=
        mul_assoc _ _ _

/-- The same calculation solved for the product cochain. -/
theorem powerCochain_add (η : G → G → U) (g : G)
    (hc : CocycleLaw η) (hunit : ∀ x, η x 1 = 1) (k l : ℕ) :
    powerCochain η g (k + l) =
      powerCochain η g k * powerCochain η g l * (η (g ^ k) (g ^ l))⁻¹ := by
  apply (eq_mul_inv_iff_mul_eq).2
  rw [mul_comm]
  exact powerCochain_mul η g hc hunit k l

/-- If the generator has exponent dividing `n`, the cochain has period `2*n`.
There is no parity assumption on `n`. -/
theorem powerCochain_double_period (η : G → G → U) (g : G)
    (hc : CocycleLaw η) (hunit : ∀ x, η x 1 = 1)
    (hs : ∀ x y, η x y ^ 2 = 1) (n : ℕ) (hgn : g ^ n = 1) (k : ℕ) :
    powerCochain η g (k + 2 * n) = powerCochain η g k := by
  have hnn : 2 * n = n + n := by rw [Nat.mul_comm, Nat.mul_succ, Nat.mul_one]
  have hg2 : g ^ (2 * n) = 1 := by rw [hnn, pow_add, hgn, mul_one]
  have hb2 : powerCochain η g (2 * n) = 1 := by
    rw [hnn, powerCochain_add η g hc hunit, hgn, hunit, inv_one, mul_one]
    simpa only [pow_two] using powerCochain_sq η g hs n
  rw [powerCochain_add η g hc hunit, hg2, hunit, hb2, inv_one, mul_one, mul_one]

/-- A cocycle's value at a left identity is the same constant at every point. -/
theorem cocycle_one_left (η : G → G → U) (hc : CocycleLaw η) (x : G) :
    η 1 x = η 1 1 := by
  have h := hc 1 1 x
  simp only [one_mul] at h
  exact (mul_left_cancel h).symm

/-- A cocycle's value at a right identity is that same constant. -/
theorem cocycle_one_right (η : G → G → U) (hc : CocycleLaw η) (x : G) :
    η x 1 = η 1 1 := by
  have h := hc x 1 1
  simp only [mul_one] at h
  exact mul_right_cancel h

/-- Normalization is proved, rather than imposed as an extra target hypothesis. -/
def normalize (η : G → G → U) (x y : G) : U := η x y * (η 1 1)⁻¹

theorem normalize_cocycle (η : G → G → U) (hc : CocycleLaw η) :
    CocycleLaw (normalize η) := by
  intro x y z
  change (η (x * y) z * (η 1 1)⁻¹) * (η x y * (η 1 1)⁻¹) =
    (η y z * (η 1 1)⁻¹) * (η x (y * z) * (η 1 1)⁻¹)
  calc
    _ = (η (x * y) z * η x y) * ((η 1 1)⁻¹ * (η 1 1)⁻¹) := by ac_rfl
    _ = (η y z * η x (y * z)) * ((η 1 1)⁻¹ * (η 1 1)⁻¹) := by rw [hc]
    _ = _ := by ac_rfl

@[simp] theorem normalize_one_left (η : G → G → U) (hc : CocycleLaw η) (x : G) :
    normalize η 1 x = 1 := by
  rw [normalize, cocycle_one_left η hc, mul_inv_cancel]

@[simp] theorem normalize_one_right (η : G → G → U) (hc : CocycleLaw η) (x : G) :
    normalize η x 1 = 1 := by
  rw [normalize, cocycle_one_right η hc, mul_inv_cancel]

theorem normalize_sq (η : G → G → U) (hs : ∀ x y, η x y ^ 2 = 1) (x y : G) :
    normalize η x y ^ 2 = 1 := by
  simp only [normalize, mul_pow, inv_pow, hs, inv_one, mul_one]

@[simp] theorem normalize_mul_constant (η : G → G → U) (x y : G) :
    normalize η x y * η 1 1 = η x y := by
  simp [normalize, mul_assoc]

/-- Any natural-number function with a period is invariant under reduction modulo it. -/
theorem nat_mod_of_period {X : Type*} (f : ℕ → X) (m : ℕ)
    (hf : ∀ k, f (k + m) = f k) (k : ℕ) : f (k % m) = f k := by
  have hmul : ∀ q j : ℕ, f (j + q * m) = f j := by
    intro q
    induction q with
    | zero => intro j; simp
    | succ q ih =>
      intro j
      rw [Nat.succ_mul, ← Nat.add_assoc, hf, ih]
  have h := hmul (k / m) (k % m)
  rw [Nat.mul_comm (k / m) m, Nat.mod_add_div] at h
  exact h.symm

end ZInQ.Contrib.UnramifiedCocycle
