/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: P2M.Sol.S_NumberField_exists_valuationSubring_eq_localization (git blob 80024913b73592db228918b3826e9d411565084a, sha256 43199638edbc64f98d5514a98f7acf259569c0d979126db624132754a5d5b70c).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_FieldTheory_RatAlgClosureGalois
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.RingTheory.DedekindDomain.AdicValuation
import Mathlib.RingTheory.DedekindDomain.IntegralClosure
import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
import Mathlib.RingTheory.Ideal.GoingUp
import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.Algebra.Algebra.Rat

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

namespace P2MW.S_NumberField_exists_valuationSubring_eq_localization

open scoped NumberField



namespace C6P1T3a

variable (Qt : Ideal (𝓞 (AlgebraicClosure ℚ))) [Qt.IsMaximal]

def carrier : Set (AlgebraicClosure ℚ) := {x | ∃ s : 𝓞 (AlgebraicClosure ℚ), s ∉ Qt ∧ ∃ a : 𝓞 (AlgebraicClosure ℚ), (s : (AlgebraicClosure ℚ)) * x = a}

omit [Qt.IsMaximal] in
theorem mem_carrier {x : (AlgebraicClosure ℚ)} : x ∈ carrier Qt ↔ ∃ s : 𝓞 (AlgebraicClosure ℚ), s ∉ Qt ∧ ∃ a : 𝓞 (AlgebraicClosure ℚ), (s : (AlgebraicClosure ℚ)) * x = a := Iff.rfl

theorem one_notMem : (1 : 𝓞 (AlgebraicClosure ℚ)) ∉ Qt := fun h => Ideal.IsPrime.ne_top' ((Ideal.eq_top_iff_one Qt).mpr h)

noncomputable def subring : Subring (AlgebraicClosure ℚ) where
  carrier := carrier Qt
  mul_mem' := by
    rintro x y ⟨s, hs, a, ha⟩ ⟨t, ht, b, hb⟩
    refine ⟨s * t, fun h => ((Ideal.IsPrime.mem_or_mem inferInstance h).elim hs ht), a * b, ?_⟩
    simp only [NumberField.RingOfIntegers.coe_eq_algebraMap, map_mul] at ha hb ⊢
    rw [← ha, ← hb]; ring
  one_mem' := ⟨1, one_notMem Qt, 1, by simp only [map_one, mul_one]⟩
  add_mem' := by
    rintro x y ⟨s, hs, a, ha⟩ ⟨t, ht, b, hb⟩
    refine ⟨s * t, fun h => ((Ideal.IsPrime.mem_or_mem inferInstance h).elim hs ht), t * a + s * b, ?_⟩
    simp only [NumberField.RingOfIntegers.coe_eq_algebraMap, map_mul, map_add] at ha hb ⊢
    rw [← ha, ← hb]; ring
  zero_mem' := ⟨1, one_notMem Qt, 0, by simp only [map_one, map_zero, mul_zero]⟩
  neg_mem' := by
    rintro x ⟨s, hs, a, ha⟩
    refine ⟨s, hs, -a, ?_⟩
    simp only [NumberField.RingOfIntegers.coe_eq_algebraMap, map_neg] at ha ⊢
    rw [← ha]; ring

theorem comap_ne_bot (K : IntermediateField ℚ (AlgebraicClosure ℚ)) [NumberField K] :
    Qt.comap (algebraMap (𝓞 K) (𝓞 (AlgebraicClosure ℚ))) ≠ ⊥ := by

  haveI : (Qt.under ℤ).IsMaximal := Ideal.IsMaximal.under ℤ Qt
  have hne : Qt.under ℤ ≠ ⊥ := Ring.ne_bot_of_isMaximal_of_not_isField inferInstance Int.not_isField
  obtain ⟨n, hn, hn0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  rw [Ideal.under_def, Ideal.mem_comap] at hn
  intro h
  have hmem : ((n : ℤ) : 𝓞 K) ∈ Qt.comap (algebraMap (𝓞 K) (𝓞 (AlgebraicClosure ℚ))) := by
    rw [Ideal.mem_comap, map_intCast]
    simpa using hn
  rw [h, Ideal.mem_bot] at hmem
  exact hn0 (by exact_mod_cast hmem)

theorem mem_or_inv_mem (x : (AlgebraicClosure ℚ)) : x ∈ carrier Qt ∨ x⁻¹ ∈ carrier Qt := by

  have hx : IsIntegral ℚ x := Algebra.IsIntegral.isIntegral x
  let K : IntermediateField ℚ (AlgebraicClosure ℚ) := IntermediateField.adjoin ℚ {x}
  haveI : FiniteDimensional ℚ K := IntermediateField.adjoin.finiteDimensional hx
  haveI : NumberField K := NumberField.mk
  have hxK : x ∈ K := IntermediateField.mem_adjoin_simple_self ℚ x

  let v : IsDedekindDomain.HeightOneSpectrum (𝓞 K) :=
    ⟨Qt.comap (algebraMap (𝓞 K) (𝓞 (AlgebraicClosure ℚ))), Ideal.IsPrime.comap _, comap_ne_bot Qt K⟩

  obtain ⟨n, d, hnd⟩ := IsDedekindDomain.HeightOneSpectrum.exists_primeCompl_mul_eq_or_mul_eq (K := K) v ⟨x, hxK⟩
  have hd : algebraMap (𝓞 K) (𝓞 (AlgebraicClosure ℚ)) d ∉ Qt := fun h => d.2 (Ideal.mem_comap.mpr h)
  have coe_alg : ∀ a : 𝓞 K, ((algebraMap (𝓞 K) (𝓞 (AlgebraicClosure ℚ)) a : 𝓞 (AlgebraicClosure ℚ)) : (AlgebraicClosure ℚ)) = ((algebraMap (𝓞 K) K a : K) : (AlgebraicClosure ℚ)) :=
    fun _ => rfl
  rcases hnd with h | h
  ·
    left
    refine ⟨algebraMap (𝓞 K) (𝓞 (AlgebraicClosure ℚ)) d, hd, algebraMap (𝓞 K) (𝓞 (AlgebraicClosure ℚ)) n, ?_⟩
    have := congrArg (fun y : K => (y : (AlgebraicClosure ℚ))) h
    simp only [MulMemClass.coe_mul] at this
    rw [coe_alg, coe_alg, ← this, mul_comm]
  ·
    right
    have hK := congrArg (fun y : K => (y : (AlgebraicClosure ℚ))) h
    simp only [MulMemClass.coe_mul] at hK
    have hx0 : x ≠ 0 := by
      rintro rfl
      apply d.2
      have hd0 : (algebraMap (𝓞 K) K (d : 𝓞 K) : K) = 0 := by
        apply Subtype.ext
        change ((algebraMap (𝓞 K) K (d : 𝓞 K) : K) : (AlgebraicClosure ℚ)) = 0
        rw [← hK]; simp
      have : (d : 𝓞 K) = 0 := (IsFractionRing.injective (𝓞 K) K) (by rw [hd0, map_zero])
      rw [this]; exact Ideal.zero_mem _
    refine ⟨algebraMap (𝓞 K) (𝓞 (AlgebraicClosure ℚ)) d, hd, algebraMap (𝓞 K) (𝓞 (AlgebraicClosure ℚ)) n, ?_⟩
    rw [coe_alg, coe_alg, ← hK, mul_comm x, mul_assoc, mul_inv_cancel₀ hx0, mul_one]

noncomputable def valuationSubring : ValuationSubring (AlgebraicClosure ℚ) :=
  { subring Qt with
    mem_or_inv_mem' := mem_or_inv_mem Qt }

end C6P1T3a

theorem solution
    (Qt : Ideal (𝓞 (AlgebraicClosure ℚ))) [Qt.IsMaximal] :
    ∃ A : ValuationSubring (AlgebraicClosure ℚ), ∀ x : AlgebraicClosure ℚ,
      x ∈ A ↔ ∃ s : 𝓞 (AlgebraicClosure ℚ), s ∉ Qt ∧ ∃ a : 𝓞 (AlgebraicClosure ℚ), (s : AlgebraicClosure ℚ) * x = a :=
  ⟨C6P1T3a.valuationSubring Qt, fun _ => Iff.rfl⟩
