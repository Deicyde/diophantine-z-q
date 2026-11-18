import ValuationLocalizationV001
import Mathlib.RingTheory.RamificationInertia.Ramification
import Mathlib.RingTheory.Localization.AtPrime.Basic

/-!
# Ramification index one at the center gives an unramified valuation ring

Let `B` be a Dedekind domain with fraction field `M`, `W` a valuation subring of `M` containing `B`
with center `Q`, and `A → B` an algebra over a ring `A` with `Q ∩ A = (ϖ)`. If `Q` has
ramification index `1` over `A`, then every element of `M` of `W`-value `< 1` has value at most that
of `ϖ`: the image of `ϖ` generates the maximal ideal of `W`.

Proof: ramification index one means `(Q ∩ A) B_Q` is the maximal ideal of `B_Q`. Write `x = a / s`
with `s ∉ Q`; then `a ∈ Q`, so `a = ϖ · b / t` in `B_Q` with `t ∉ Q`, hence `a t = ϖ b` in `B`
and `v(x) = v(a) = v(ϖ) v(b) ≤ v(ϖ)`.
-/

noncomputable section
set_option autoImplicit false

namespace InertiaPointDescent

open IsLocalRing

variable {A B M : Type*} [CommRing A] [CommRing B] [IsDedekindDomain B] [Field M] [Algebra B M]
  [IsFractionRing B M] [Algebra A B]

theorem maximalIdeal_eq_map_of_ramificationIdx_eq_one (Q : Ideal B) [Q.IsPrime]
    (h : Q.ramificationIdx A = 1) :
    (Q.under A).map (algebraMap A (Localization.AtPrime Q)) =
      maximalIdeal (Localization.AtPrime Q) := by
  rw [Ideal.ramificationIdx_def, ENat.toNat_eq_iff_eq_natCast, Nat.cast_one,
    Module.length_eq_one_iff, isSimpleModule_iff_isCoatom, ← Ideal.isMaximal_def,
    IsLocalRing.isMaximal_iff] at h
  exact h

/-- **Unramified valuation ring from ramification index one.** -/
theorem val_le_of_ramificationIdx_eq_one (W : ValuationSubring M)
    (hB : ∀ b : B, algebraMap B M b ∈ W) (ϖ : A)
    (hϖ : (center W hB).under A = Ideal.span {ϖ})
    (he : (center W hB).ramificationIdx A = 1) (x : M) (hx : W.valuation x < 1) :
    W.valuation x ≤ W.valuation (algebraMap B M (algebraMap A B ϖ)) := by
  classical
  set Q := center W hB with hQ
  let Sq := Localization.AtPrime Q
  have hmax := maximalIdeal_eq_map_of_ramificationIdx_eq_one (A := A) Q he
  rw [hϖ, Ideal.map_span, Set.image_singleton] at hmax
  have hxW : x ∈ W := (W.valuation_le_one_iff x).1 hx.le
  obtain ⟨a, s, hs, e⟩ := exists_eq_div_of_mem W hB hxW
  have hs1 : W.valuation (algebraMap B M s) = 1 := val_eq_one_of_not_mem_center W hB hs
  have hva : W.valuation (algebraMap B M a) = W.valuation x := by
    rw [e, Valuation.map_mul, Valuation.map_inv, hs1, inv_one, mul_one]
  have haQ : a ∈ Q := by
    rw [hQ, mem_center_iff, hva]
    exact hx
  have haSq : algebraMap B Sq a ∈ maximalIdeal Sq :=
    (IsLocalization.AtPrime.to_map_mem_maximal_iff Sq Q a).2 haQ
  rw [← hmax, Ideal.mem_span_singleton'] at haSq
  obtain ⟨y, hy⟩ := haSq
  obtain ⟨⟨b, t⟩, rfl⟩ := IsLocalization.mk'_surjective Q.primeCompl y
  -- clear the denominator
  have heq : algebraMap B Sq (a * t) = algebraMap B Sq (b * algebraMap A B ϖ) := by
    rw [map_mul, map_mul, ← hy, mul_assoc, mul_comm (algebraMap A Sq ϖ), ← mul_assoc,
      IsLocalization.mk'_spec, IsScalarTower.algebraMap_apply A B Sq]
  have hinj : Function.Injective (algebraMap B Sq) :=
    IsLocalization.injective Sq (Ideal.primeCompl_le_nonZeroDivisors Q)
  have hab := congrArg (algebraMap B M) (hinj heq)
  rw [map_mul, map_mul] at hab
  have hv := congrArg W.valuation hab
  rw [Valuation.map_mul, Valuation.map_mul,
    val_eq_one_of_not_mem_center W hB t.2, mul_one, hva] at hv
  rw [hv]
  calc W.valuation (algebraMap B M b) * W.valuation (algebraMap B M (algebraMap A B ϖ))
      ≤ 1 * W.valuation (algebraMap B M (algebraMap A B ϖ)) :=
        mul_le_mul_of_nonneg_right ((W.valuation_le_one_iff _).2 (hB b)) zero_le
    _ = W.valuation (algebraMap B M (algebraMap A B ϖ)) := one_mul _

end InertiaPointDescent
