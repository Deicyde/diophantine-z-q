import Mathlib.NumberTheory.Padics.RingHoms
import Mathlib.Algebra.Module.Equiv.Basic

set_option autoImplicit false

namespace RC53.EllAdic

universe u v w

variable {p : ℕ} [Fact p.Prime]

/-- The actual residue map gives a natural representative modulo `p^n`. -/
theorem padicInt_exists_residue_difference (a : ℤ_[p]) (n : ℕ) :
    ∃ b : ℤ_[p],
      a - ((PadicInt.toZModPow n a).val : ℤ_[p]) = (p : ℤ_[p]) ^ n * b := by
  let : NeZero (p ^ n) := ⟨pow_ne_zero n (Fact.out : p.Prime).ne_zero⟩
  have hk : a - ((PadicInt.toZModPow n a).val : ℤ_[p]) ∈
      RingHom.ker (PadicInt.toZModPow n : ℤ_[p] →+* ZMod (p ^ n)) := by
    rw [RingHom.mem_ker, map_sub, map_natCast, ZMod.natCast_zmod_val, sub_self]
  rw [PadicInt.ker_toZModPow] at hk
  exact Ideal.mem_span_singleton.mp hk

variable {M : Type u} {L : Type v} {T : ℕ → Type w}
  [AddCommGroup M] [AddCommGroup L] [∀ n, AddCommGroup (T n)]
  [Module ℤ_[p] M] [Module ℤ_[p] L]

/-- Additive maps preserve the actual p-adic scalar action if the target's
additive residue projections separate points and have the specified exponent.
The projections need not already be linear. -/
theorem additive_map_Zp_smul_of_residue_projections
    (f : M →+ L) (π : ∀ n, L →+ T n)
    (hsep : ∀ {x y : L}, (∀ n : ℕ, π n x = π n y) → x = y)
    (hkill : ∀ n : ℕ, ∀ y : T n, p ^ n • y = 0)
    (a : ℤ_[p]) (x : M) : f (a • x) = a • f x := by
  apply hsep
  intro n
  let r := (PadicInt.toZModPow n a).val
  obtain ⟨b, hb⟩ := padicInt_exists_residue_difference a n
  have hb' : a - (r : ℤ_[p]) = (p : ℤ_[p]) ^ n * b := hb
  have ha : a = (r : ℤ_[p]) + (p : ℤ_[p]) ^ n * b := by
    calc
      a = (a - (r : ℤ_[p])) + (r : ℤ_[p]) := (sub_add_cancel a _).symm
      _ = _ := by rw [hb', add_comm]
  simp only [ha, add_smul, mul_smul, ← Nat.cast_pow, Nat.cast_smul_eq_nsmul,
    map_add, map_nsmul, hkill, add_zero]

/-- This is the same equivalence on elements, with linearity proved rather
than chosen by replacing either module action. -/
def linearEquiv_of_addEquiv_residue_projections
    (e : M ≃+ L) (π : ∀ n, L →+ T n)
    (hsep : ∀ {x y : L}, (∀ n : ℕ, π n x = π n y) → x = y)
    (hkill : ∀ n : ℕ, ∀ y : T n, p ^ n • y = 0) : M ≃ₗ[ℤ_[p]] L :=
  { e with
    map_smul' := fun a x => additive_map_Zp_smul_of_residue_projections e.toAddMonoidHom π hsep hkill a x }

@[simp] theorem linearEquiv_of_addEquiv_residue_projections_apply
    (e : M ≃+ L) (π : ∀ n, L →+ T n)
    (hsep : ∀ {x y : L}, (∀ n : ℕ, π n x = π n y) → x = y)
    (hkill : ∀ n : ℕ, ∀ y : T n, p ^ n • y = 0) (x : M) :
    linearEquiv_of_addEquiv_residue_projections e π hsep hkill x = e x := rfl

end RC53.EllAdic
