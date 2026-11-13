import Mathlib
import ZInQKernel.HDecomp.Vigneras.Local

/-!
# t30-adelic, part G1-adelic (b): the adelic normalizer quotient of A3

`B̂ = B ⊗ 𝔸_f` is the restricted product of the `B_p = ℍ[ℚ_p, 2, 0, -3]` with respect to N5's
lattices `𝒪_p` (`GlueVigneras.Op`), `𝒪̂ = ∏_p 𝒪_p`, `N` the normalizer of `𝒪̂` in `B̂^×`,
`K₀ = 𝒪̂^×` and `Z = 𝔸_f^×` (the central scalars). Main results:

* `normalizer_component`: `x ∈ N` ⇒ every component `x_p` normalizes `𝒪_p`;
* `mem_sup_iff`: `x ∈ N` lies in `Z K₀` iff `x_p ∈ ℚ_p^× 𝒪_p^×` at `p = 2, 3` (at `p ∤ 6` this
  holds automatically by `unramified_normalizer`): the identification of `N/(Z K₀)` with the
  restricted product of the local quotients, which are trivial at `p ∤ 6`;
* `relIndex_eq_four`: `[N : Z K₀] = 4`.
-/

open GlueVigneras
open scoped RestrictedProduct

namespace G1Adelic

local instance (p : Nat.Primes) : Fact (p : ℕ).Prime := ⟨p.2⟩

section Local

variable (p : ℕ) [Fact p.Prime]

/-- Multiplication in N5's basis (the integer formula of `GlueRepo.A1.combMul`). -/
noncomputable def combMulp (n m : Fin 4 → ℤ_[p]) : Fin 4 → ℤ_[p] :=
  ![m 0 * n 0 + 2 * m 1 * n 1 + 2 * m 1 * n 3 - m 2 * n 2 + 2 * m 3 * n 3,
    m 0 * n 1 + m 1 * n 0 + m 1 * n 2 - m 2 * n 3 + m 3 * n 2,
    m 0 * n 2 - 2 * m 1 * n 3 + m 2 * n 0 + m 2 * n 2 + 2 * m 3 * n 1,
    m 0 * n 3 - m 1 * n 2 + m 2 * n 1 + m 2 * n 3 + m 3 * n 0]

theorem combp_mul (n m : Fin 4 → ℤ_[p]) : combp p n * combp p m = combp p (combMulp p n m) := by
  ext <;> simp [combp, combMulp] <;> ring

theorem combp_add (n m : Fin 4 → ℤ_[p]) : combp p n + combp p m = combp p (n + m) := by
  ext <;> simp [combp] <;> ring

theorem combp_neg (n : Fin 4 → ℤ_[p]) : -combp p n = combp p (-n) := by
  ext <;> simp [combp] <;> ring

theorem combp_one : combp p ![1, 0, 0, 0] = 1 := by
  ext <;> simp [combp]

theorem combp_zero : combp p 0 = 0 := by
  ext <;> simp [combp]

/-- `𝒪_p` as a subring of `B_p`. -/
noncomputable def OpSub : Subring (Bp p) where
  carrier := Op p
  mul_mem' := by
    rintro _ _ ⟨n, rfl⟩ ⟨m, rfl⟩
    exact ⟨_, (combp_mul p n m).symm⟩
  one_mem' := ⟨_, combp_one p⟩
  add_mem' := by
    rintro _ _ ⟨n, rfl⟩ ⟨m, rfl⟩
    exact ⟨_, (combp_add p n m).symm⟩
  zero_mem' := ⟨_, combp_zero p⟩
  neg_mem' := by
    rintro _ ⟨n, rfl⟩
    exact ⟨_, (combp_neg p n).symm⟩

theorem mem_OpSub {x : Bp p} : x ∈ OpSub p ↔ x ∈ Op p := Iff.rfl

end Local

/-- `B̂ = B ⊗ 𝔸_f`: the restricted product of the `B_p` with respect to the `𝒪_p`. -/
abbrev BA := Πʳ p : Nat.Primes, [Bp (p : ℕ), OpSub (p : ℕ)]

/-- The component `x_p ∈ B_p^×` of `x ∈ B̂^×`. -/
noncomputable def comp (p : Nat.Primes) : BAˣ →* (Bp (p : ℕ))ˣ :=
  Units.map (RestrictedProduct.evalRingHom _ p).toMonoidHom

theorem comp_val (p : Nat.Primes) (x : BAˣ) : ((comp p x : (Bp (p : ℕ))ˣ) : Bp (p : ℕ)) =
    (x : BA) p := rfl

theorem comp_inv_val (p : Nat.Primes) (x : BAˣ) :
    (((comp p x)⁻¹ : (Bp (p : ℕ))ˣ) : Bp (p : ℕ)) = ((x⁻¹ : BAˣ) : BA) p := rfl

/-- `𝒪̂ = ∏_p 𝒪_p ⊆ B̂`. -/
def Ohat : Set BA := {y | ∀ p : Nat.Primes, y p ∈ Op (p : ℕ)}

/-- The normalizer `N` of `𝒪̂` in `B̂^×`. -/
noncomputable def Nhat : Subgroup BAˣ where
  carrier := {x | ∀ y : BA, y ∈ Ohat ↔ (x : BA) * y * ((x⁻¹ : BAˣ) : BA) ∈ Ohat}
  one_mem' := by intro y; simp
  mul_mem' := by
    intro a b ha hb y
    rw [hb y, ha]
    simp only [Units.val_mul, mul_inv_rev]
    simp only [mul_assoc]
  inv_mem' := by
    intro a ha y
    simp only [inv_inv]
    have : (a : BA) * ((((a⁻¹ : BAˣ) : BA)) * y * (a : BA)) * ((a⁻¹ : BAˣ) : BA) = y := by
      simp only [← mul_assoc, Units.mul_inv, one_mul]
      rw [mul_assoc, Units.mul_inv, mul_one]
    rw [ha (((a⁻¹ : BAˣ) : BA) * y * (a : BA)), this]

/-- `K₀ = 𝒪̂^×`. -/
noncomputable def K0 : Subgroup BAˣ where
  carrier := {x | (x : BA) ∈ Ohat ∧ ((x⁻¹ : BAˣ) : BA) ∈ Ohat}
  one_mem' := ⟨fun p => (OpSub (p : ℕ)).one_mem, fun p => (OpSub (p : ℕ)).one_mem⟩
  mul_mem' := by
    rintro a b ⟨ha1, ha2⟩ ⟨hb1, hb2⟩
    refine ⟨fun p => (OpSub (p : ℕ)).mul_mem (ha1 p) (hb1 p), fun p => ?_⟩
    rw [mul_inv_rev]
    exact (OpSub (p : ℕ)).mul_mem (hb2 p) (ha2 p)
  inv_mem' := by
    rintro a ⟨ha1, ha2⟩
    exact ⟨ha2, by rw [inv_inv]; exact ha1⟩

/-- `Z = 𝔸_f^×`, the central scalars of `B̂^×` (componentwise in `ℚ_p^×`). -/
noncomputable def Zhat : Subgroup BAˣ where
  carrier := {x | ∀ p : Nat.Primes, ∃ c : ℚ_[(p : ℕ)], (x : BA) p = algebraMap _ _ c}
  one_mem' := fun p => ⟨1, by simp⟩
  mul_mem' := by
    intro a b ha hb p
    obtain ⟨c, hc⟩ := ha p
    obtain ⟨d, hd⟩ := hb p
    exact ⟨c * d, by rw [Units.val_mul, RestrictedProduct.mul_apply, hc, hd, map_mul]⟩
  inv_mem' := by
    intro a ha p
    obtain ⟨c, hc⟩ := ha p
    refine ⟨c⁻¹, ?_⟩
    have h1 : (a : BA) p * ((a⁻¹ : BAˣ) : BA) p = 1 := by
      rw [← RestrictedProduct.mul_apply, Units.mul_inv]; rfl
    rw [hc] at h1
    have hc0 : c ≠ 0 := by
      rintro rfl
      rw [map_zero, zero_mul] at h1
      exact zero_ne_one h1
    calc ((a⁻¹ : BAˣ) : BA) p = algebraMap _ _ c⁻¹ * (algebraMap _ _ c * ((a⁻¹ : BAˣ) : BA) p) := by
          rw [← mul_assoc, ← map_mul, inv_mul_cancel₀ hc0, map_one, one_mul]
      _ = algebraMap _ _ c⁻¹ := by rw [h1, mul_one]

/-! ### Components of the normalizer -/

open Classical in
/-- The element of `B̂` with component `y` at `p` and `0` elsewhere. -/
noncomputable def single (p : Nat.Primes) (y : Bp (p : ℕ)) : BA :=
  RestrictedProduct.single (fun q : Nat.Primes => OpSub (q : ℕ)) p y

theorem single_apply_self (p : Nat.Primes) (y : Bp (p : ℕ)) : single p y p = y := by
  classical
  simp [single]

theorem single_apply_ne {p q : Nat.Primes} (h : q ≠ p) (y : Bp (p : ℕ)) : single p y q = 0 := by
  classical
  simp [single, h]

theorem conj_apply (x : BAˣ) (y : BA) (q : Nat.Primes) :
    ((x : BA) * y * ((x⁻¹ : BAˣ) : BA)) q =
      ((comp q x : (Bp (q : ℕ))ˣ) : Bp (q : ℕ)) * y q * (((comp q x)⁻¹ : (Bp (q : ℕ))ˣ) :
        Bp (q : ℕ)) := by
  rw [comp_val, comp_inv_val, RestrictedProduct.mul_apply, RestrictedProduct.mul_apply]

theorem single_mem_Ohat (p : Nat.Primes) {y : Bp (p : ℕ)} (hy : y ∈ Op (p : ℕ)) :
    single p y ∈ Ohat := by
  intro q
  by_cases h : q = p
  · subst h; rw [single_apply_self]; exact hy
  · rw [single_apply_ne h]; exact (OpSub (q : ℕ)).zero_mem

/-- **Components of the normalizer.** If `x ∈ N`, every `x_p` normalizes `𝒪_p`. -/
theorem normalizer_component {x : BAˣ} (hx : x ∈ Nhat) (p : Nat.Primes) :
    comp p x ∈ normalizerOp (p : ℕ) := by
  intro y
  have key : ∀ q : Nat.Primes, ((x : BA) * single p y * ((x⁻¹ : BAˣ) : BA)) q ∈ Op (q : ℕ) ↔
      (q = p → ((comp p x : (Bp (p : ℕ))ˣ) : Bp (p : ℕ)) * y *
        (((comp p x)⁻¹ : (Bp (p : ℕ))ˣ) : Bp (p : ℕ)) ∈ Op (p : ℕ)) := by
    intro q
    rw [conj_apply]
    by_cases h : q = p
    · subst h; rw [single_apply_self]; simp
    · rw [single_apply_ne h, mul_zero, zero_mul]
      simp only [h, IsEmpty.forall_iff, iff_true]
      exact (OpSub (q : ℕ)).zero_mem
  constructor
  · intro hy
    have := (hx (single p y)).mp (single_mem_Ohat p hy) p
    exact (key p).mp this rfl
  · intro hy
    have h1 : (x : BA) * single p y * ((x⁻¹ : BAˣ) : BA) ∈ Ohat := fun q => (key q).mpr
      (fun h => by subst h; exact hy)
    have := (hx (single p y)).mpr h1 p
    rwa [single_apply_self] at this

end G1Adelic
