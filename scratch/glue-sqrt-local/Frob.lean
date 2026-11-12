import Mathlib

open Polynomial IsLocalRing

namespace GlueSqrtLocal

variable (p : ℕ) [hp : Fact p.Prime] (L : Type) [Field L] [Algebra ℚ_[p] L]
  [Algebra ℤ_[p] L] [IsScalarTower ℤ_[p] ℚ_[p] L] [FiniteDimensional ℚ_[p] L] [IsGalois ℚ_[p] L]

/-- `ℤ_p/(p)` has `p` elements. -/
theorem card_quotient_maximalIdeal : Nat.card (ℤ_[p] ⧸ maximalIdeal ℤ_[p]) = p := by
  rw [← PadicInt.ker_toZMod]
  rw [Nat.card_congr (RingHom.quotientKerEquivOfSurjective
    (ZMod.ringHom_surjective (PadicInt.toZMod (p := p)))).toEquiv]
  simp

/-- **Frobenius in a finite Galois extension of `ℚ_p`.** There is `σ ∈ Gal(L/ℚ_p)` with
`σ ζ = ζ^p` for every root of unity `ζ ∈ L` of order prime to `p`. -/
theorem exists_frobenius :
    ∃ σ : Gal(L/ℚ_[p]), ∀ (m : ℕ), ¬ p ∣ m → ∀ ζ : L, ζ ^ m = 1 → σ ζ = ζ ^ p := by
  let S := integralClosure ℤ_[p] L
  have : IsFractionRing S L := integralClosure.isFractionRing_of_finite_extension ℚ_[p] L
  have : IsGaloisGroup Gal(L/ℚ_[p]) ℤ_[p] S :=
    IsGaloisGroup.of_isFractionRing Gal(L/ℚ_[p]) ℤ_[p] S ℚ_[p] L
  have : Module.Finite ℤ_[p] S := IsIntegralClosure.finite ℤ_[p] ℚ_[p] L S
  have hinjL : Function.Injective (algebraMap ℤ_[p] L) := by
    rw [IsScalarTower.algebraMap_eq ℤ_[p] ℚ_[p] L]
    exact (algebraMap ℚ_[p] L).injective.comp (IsFractionRing.injective ℤ_[p] ℚ_[p])
  have : FaithfulSMul ℤ_[p] S := by
    rw [faithfulSMul_iff_algebraMap_injective]
    intro a b h
    apply hinjL
    rw [IsScalarTower.algebraMap_apply ℤ_[p] S L, h, ← IsScalarTower.algebraMap_apply]
  obtain ⟨Q, hQmax, hQ⟩ := Ideal.exists_maximal_ideal_liesOver_of_isIntegral (S := S)
    (maximalIdeal ℤ_[p])
  have hunder : Q.under ℤ_[p] = maximalIdeal ℤ_[p] := (Ideal.liesOver_iff _ _).mp hQ |>.symm
  have : Finite (ℤ_[p] ⧸ Q.under ℤ_[p]) := by
    rw [hunder]
    exact Nat.finite_of_card_ne_zero (by rw [card_quotient_maximalIdeal p]; exact hp.out.ne_zero)
  have : Module.Finite (ℤ_[p] ⧸ Q.under ℤ_[p]) (S ⧸ Q) :=
    Module.Finite.of_restrictScalars_finite ℤ_[p] _ _
  have : Finite (S ⧸ Q) := Module.finite_of_finite (ℤ_[p] ⧸ Q.under ℤ_[p])
  obtain ⟨σ, hσ⟩ := IsArithFrobAt.exists_of_isInvariant ℤ_[p] Gal(L/ℚ_[p]) Q
  refine ⟨σ, fun m hm ζ hζ => ?_⟩
  have hm0 : m ≠ 0 := by rintro rfl; exact hm (dvd_zero p)
  have hζS : IsIntegral ℤ_[p] ζ := ⟨X ^ m - C 1, monic_X_pow_sub_C 1 hm0, by simp [hζ]⟩
  let z : S := ⟨ζ, hζS⟩
  have hz : z ^ m = 1 := Subtype.ext (by simp [z, hζ])
  have hmQ : (m : S) ∉ Q := by
    intro h
    have h1 : (m : ℤ_[p]) ∈ Q.under ℤ_[p] := by
      rw [Ideal.under, Ideal.mem_comap, map_natCast]; exact h
    rw [hunder, ← PadicInt.ker_toZMod, RingHom.mem_ker, map_natCast,
      ZMod.natCast_eq_zero_iff] at h1
    exact hm h1
  have key := hσ.apply_of_pow_eq_one hz hmQ
  rw [hunder, card_quotient_maximalIdeal p] at key
  have := congrArg (fun s : S => (s : L)) key
  simp only [SubmonoidClass.coe_pow, z] at this
  exact this

end GlueSqrtLocal

#print axioms GlueSqrtLocal.exists_frobenius
