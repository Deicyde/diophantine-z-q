import UnramifiedValuationV002
import Mathlib.RingTheory.RamificationInertia.Ramification

/-!
# From an unramified valuation ring to `Algebra.IsUnramifiedAt`

Let `B` be a Dedekind domain with fraction field `M`, `W` a valuation subring of `M` containing `B`
with center `Q`, and `A → B` with `Q ∩ A = (ϖ)`, `ϖ ≠ 0` in `M`. If `ϖ` generates the maximal ideal
of `W` (every `x` with `v(x) < 1` has `x / ϖ ∈ W`), then `Q` has ramification index one over `A`;
with essentially finite type and separable residue fields, `B` is unramified over `A` at `Q`.

Proof: the maximal ideal of `B_Q` is `ϖ B_Q`. For `b / t` in it, `b ∈ Q`, so `b / ϖ = a / s` with
`s ∉ Q`, i.e. `b s = ϖ a` in `B`, and `b / t = ϖ · a / (s t)`.
-/

noncomputable section
set_option autoImplicit false

namespace InertiaPointDescent

open IsLocalRing

variable {A B M : Type*} [CommRing A] [CommRing B] [IsDedekindDomain B] [Field M] [Algebra B M]
  [IsFractionRing B M] [Algebra A B]

theorem ramificationIdx_eq_one_of_div_mem (W : ValuationSubring M)
    (hB : ∀ b : B, algebraMap B M b ∈ W) (ϖ : A)
    (hϖ : (center W hB).under A = Ideal.span {ϖ})
    (hϖ0 : algebraMap B M (algebraMap A B ϖ) ≠ 0)
    (hdiv : ∀ x : M, W.valuation x < 1 → x * (algebraMap B M (algebraMap A B ϖ))⁻¹ ∈ W) :
    (center W hB).ramificationIdx A = 1 := by
  classical
  set Q := center W hB with hQ
  let Sq := Localization.AtPrime Q
  rw [Ideal.ramificationIdx_def, ENat.toNat_eq_iff_eq_natCast, Nat.cast_one,
    Module.length_eq_one_iff, isSimpleModule_iff_isCoatom, ← Ideal.isMaximal_def,
    IsLocalRing.isMaximal_iff, hϖ, Ideal.map_span, Set.image_singleton]
  have hϖQ : algebraMap A B ϖ ∈ Q := by
    have : ϖ ∈ Q.under A := by
      rw [hϖ]
      exact Ideal.subset_span rfl
    exact this
  apply le_antisymm
  · rw [Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe,
      IsScalarTower.algebraMap_apply A B Sq]
    exact (IsLocalization.AtPrime.to_map_mem_maximal_iff Sq Q _).2 hϖQ
  · intro z hz
    obtain ⟨⟨b, t⟩, rfl⟩ := IsLocalization.mk'_surjective Q.primeCompl z
    have hbQ : b ∈ Q := (IsLocalization.AtPrime.mk'_mem_maximal_iff Sq Q b t).1 hz
    have hvb : W.valuation (algebraMap B M b) < 1 := by
      rw [hQ, mem_center_iff] at hbQ
      exact hbQ
    obtain ⟨a, s, hs, e⟩ := exists_eq_div_of_mem W hB (hdiv _ hvb)
    have hs0 : algebraMap B M s ≠ 0 := by
      intro h0
      have := val_eq_one_of_not_mem_center W hB hs
      rw [h0, Valuation.map_zero] at this
      exact zero_ne_one this
    have heqM : algebraMap B M (b * s) = algebraMap B M (algebraMap A B ϖ * a) := by
      rw [map_mul, map_mul]
      field_simp at e
      rw [e]
    have heqB : b * s = algebraMap A B ϖ * a := IsFractionRing.injective B M heqM
    have hst : s * (t : B) ∈ Q.primeCompl := Q.primeCompl.mul_mem hs t.2
    rw [Ideal.mem_span_singleton']
    refine ⟨IsLocalization.mk' Sq a ⟨s * t, hst⟩, ?_⟩
    rw [IsScalarTower.algebraMap_apply A B Sq, mul_comm, IsLocalization.mul_mk'_eq_mk'_of_mul,
      IsLocalization.mk'_eq_iff_eq]
    congr 1
    change (t : B) * (algebraMap A B ϖ * a) = s * t * b
    rw [← heqB]
    ring

/-- **`Algebra.IsUnramifiedAt` from an unramified valuation ring.** -/
theorem isUnramifiedAt_of_div_mem (W : ValuationSubring M)
    (hB : ∀ b : B, algebraMap B M b ∈ W) (ϖ : A)
    (hϖ : (center W hB).under A = Ideal.span {ϖ})
    (hϖ0 : algebraMap B M (algebraMap A B ϖ) ≠ 0)
    (hdiv : ∀ x : M, W.valuation x < 1 → x * (algebraMap B M (algebraMap A B ϖ))⁻¹ ∈ W)
    [Algebra.EssFiniteType A B]
    [Algebra.HasSeparableResidueFieldsAt A B ((center W hB).under A)] :
    Algebra.IsUnramifiedAt A (center W hB) :=
  (Ideal.ramificationIdx_eq_one_iff).1 (ramificationIdx_eq_one_of_div_mem W hB ϖ hϖ hϖ0 hdiv)

end InertiaPointDescent
