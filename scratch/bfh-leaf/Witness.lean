import Mathlib.NumberTheory.NumberField.Cyclotomic.Basic
import Mathlib.RingTheory.ZMod
import ZInQKernel.Contrib.OneProof.BFHPrinted.Split

/-! Nonvacuity of the splitting clause: `7` splits in `ℚ(√−3) = ℚ(ζ₃)`. -/

open NumberField Polynomial

namespace ZInQ.BFHPrinted

/-- `ℚ(ζ₃)` is a quadratic field containing `√−3 = 2ζ₃ + 1`, and `7` splits in it: the primes
`(7, ζ₃ − 2)` and `(7, ζ₃ − 4)` are the kernels of `ζ₃ ↦ 2` and `ζ₃ ↦ 4` into `𝔽₇`. -/
theorem cyclotomicThree_witness_of (K : Type) [Field K] [NumberField K]
    [IsCyclotomicExtension {3} ℚ K] :
    Module.finrank ℚ K = 2 ∧ (∃ δ : K, δ ^ 2 = ((-3 : ℤ) : K)) ∧ SplitsIn K 7 := by
  have hζ := IsCyclotomicExtension.zeta_spec 3 ℚ K
  set ζ := IsCyclotomicExtension.zeta 3 ℚ K
  have hroot : ζ ^ 2 + ζ + 1 = 0 := by
    have := hζ.isRoot_cyclotomic (by norm_num)
    simpa [cyclotomic_three, IsRoot] using this
  refine ⟨?_, ⟨2 * ζ + 1, by push_cast; linear_combination 4 * hroot⟩, ?_⟩
  · rw [IsCyclotomicExtension.finrank K
      (cyclotomic.irreducible_rat (n := 3) (by norm_num))]
    exact Nat.totient_prime Nat.prime_three
  · have h2 : (2 : ZMod 7) ^ 2 + 2 + 1 = 0 := by decide
    have h4 : (4 : ZMod 7) ^ 2 + 4 + 1 = 0 := by decide
    have hne : (4 : ZMod 7) - 2 ≠ 0 := by decide
    have : Fact (Nat.Prime 7) := ⟨by decide⟩
    let pb := hζ.integralPowerBasis
    have hmin : minpoly ℤ pb.gen = X ^ 2 + X + 1 := by
      rw [IsPrimitiveRoot.integralPowerBasis_gen, ← minpoly.algebraMap_eq
        (RingOfIntegers.coe_injective (K := K)) hζ.toInteger]
      rw [← cyclotomic_three ℤ]
      exact (cyclotomic_eq_minpoly hζ (by norm_num)).symm
    let φ : (a : ZMod 7) → a ^ 2 + a + 1 = 0 → (𝓞 K →ₐ[ℤ] ZMod 7) :=
      fun a ha => pb.lift a (by rw [hmin]; simpa using ha)
    have hφgen : ∀ a ha, φ a ha pb.gen = a := fun a ha => pb.lift_gen _ _
    have hmem : ∀ a ha, RingHom.ker (φ a ha).toRingHom ∈
        (Ideal.span {((7 : ℕ) : ℤ)}).primesOver (𝓞 K) := by
      intro a ha
      refine ⟨RingHom.ker_isPrime _, ⟨?_⟩⟩
      rw [Ideal.under, RingHom.comap_ker]
      have : (φ a ha).toRingHom.comp (algebraMap ℤ (𝓞 K)) =
          Int.castRingHom (ZMod 7) := RingHom.ext_int _ _
      rw [this, ZMod.ker_intCastRingHom]
    refine ⟨_, hmem 2 h2, _, hmem 4 h4, fun h => ?_⟩
    have hx : pb.gen - 2 ∈ RingHom.ker (φ 2 h2).toRingHom := by
      rw [RingHom.mem_ker]; simp [hφgen, map_ofNat]
    rw [h, RingHom.mem_ker] at hx
    simp [hφgen, map_ofNat] at hx
    exact hne hx

theorem cyclotomicThree_witness :
    ∃ (K : Type) (_ : Field K) (_ : NumberField K), Module.finrank ℚ K = 2 ∧
      (∃ δ : K, δ ^ 2 = ((-3 : ℤ) : K)) ∧ SplitsIn K 7 := by
  have : NeZero ((3 : ℕ) : ℚ) := ⟨by norm_num⟩
  exact ⟨CyclotomicField 3 ℚ, inferInstance, inferInstance,
    @cyclotomicThree_witness_of (CyclotomicField 3 ℚ) _ _
      (CyclotomicField.isCyclotomicExtension 3 ℚ)⟩

end ZInQ.BFHPrinted
