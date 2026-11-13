import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
import Mathlib.FieldTheory.SeparableClosure
import Mathlib.RingTheory.IntegralClosure.IsIntegral.Basic

/-!
# Field and scalar-tower checks for T2

The baseline does not explicitly supply `IsScalarTower R L M`, finiteness of
`M/K`, or separability of `M/K`. The lemmas here derive them from the actual
root and generation hypotheses. No tame-compositum assertion is used.
-/

namespace ZInQ.Contrib.Abhyankar

open Polynomial

/-- The three scalar towers in the baseline supply the fourth one. -/
theorem scalarTower_right
    {R K L M : Type*} [CommSemiring R] [CommSemiring K] [CommSemiring L] [Semiring M]
    [Algebra R K] [Algebra K L] [Algebra R L] [IsScalarTower R K L]
    [Algebra L M] [Algebra K M] [Algebra R M]
    [IsScalarTower K L M] [IsScalarTower R K M] : IsScalarTower R L M := by
  apply IsScalarTower.of_algebraMap_eq
  intro r
  calc
    algebraMap R M r = algebraMap K M (algebraMap R K r) :=
      IsScalarTower.algebraMap_apply R K M r
    _ = algebraMap L M (algebraMap K L (algebraMap R K r)) :=
      IsScalarTower.algebraMap_apply K L M _
    _ = algebraMap L M (algebraMap R L r) := by
      rw [← IsScalarTower.algebraMap_apply R K L]

/-- A positive-power root of an element of the base ring is integral over it. -/
theorem isIntegral_root
    {R M : Type*} [CommRing R] [Ring M] [Algebra R M]
    {π : R} {n : ℕ} (hn : 0 < n) {t : M}
    (ht : t ^ n = algebraMap R M π) : IsIntegral R t := by
  apply IsIntegral.of_pow hn
  rw [ht]
  exact isIntegral_algebraMap

/-- The generation hypothesis supplies finiteness over the intermediate field. -/
theorem finiteDimensional_of_root_adjoin
    {R L M : Type*} [CommRing R] [Field L] [Field M]
    [Algebra R L] [Algebra L M] [Algebra R M] [IsScalarTower R L M]
    {π : R} {n : ℕ} (hn : 0 < n) {t : M}
    (ht : t ^ n = algebraMap R M π)
    (hadjoin : IntermediateField.adjoin L {t} = ⊤) : FiniteDimensional L M := by
  have htL : IsIntegral L t := by
    apply IsIntegral.of_pow hn
    rw [ht, IsScalarTower.algebraMap_apply R L M]
    exact isIntegral_algebraMap
  have hfin := IntermediateField.adjoin.finiteDimensional htL
  rw [hadjoin] at hfin
  exact IntermediateField.topEquiv.toLinearEquiv.finiteDimensional

/-- Invertibility of the exponent in the actual base ring supplies separability.
The nonzero constant term is checked in `L`, not replaced by a characteristic assumption. -/
theorem isSeparable_of_root_adjoin
    {R L M : Type*} [CommRing R] [Field L] [Field M]
    [Algebra R L] [Algebra L M] [Algebra R M] [IsScalarTower R L M]
    {π : R} (hπ : algebraMap R L π ≠ 0) {n : ℕ} (hn : IsUnit (n : R)) {t : M}
    (ht : t ^ n = algebraMap R M π)
    (hadjoin : IntermediateField.adjoin L {t} = ⊤) : Algebra.IsSeparable L M := by
  have hnL : (n : L) ≠ 0 := by
    simpa only [map_natCast] using (hn.map (algebraMap R L)).ne_zero
  have hroot : aeval t (X ^ n - C (algebraMap R L π)) = 0 := by
    simp only [map_sub, map_pow, aeval_X, aeval_C,
      ← IsScalarTower.algebraMap_apply R L M, ht, sub_self]
  have htsep : IsSeparable L t :=
    (separable_X_pow_sub_C _ hnL hπ).of_dvd (minpoly.dvd L t hroot)
  rw [← IntermediateField.isSeparable_top L M, ← hadjoin]
  exact (IntermediateField.isSeparable_adjoin_iff_isSeparable L M).mpr
    (by simpa only [Set.mem_singleton_iff, forall_eq] using htsep)

/-- If the generator already belongs to the image of the base field, generation of
all of `M` forces the given algebra map to be surjective. This treats the `n = 1` case. -/
theorem algebraMap_surjective_of_adjoin_eq_top
    {L M : Type*} [Field L] [Field M] [Algebra L M]
    {t : M} (ht : t ∈ Set.range (algebraMap L M))
    (hadjoin : IntermediateField.adjoin L {t} = ⊤) :
    Function.Surjective (algebraMap L M) := by
  have hbot : IntermediateField.adjoin L {t} = ⊥ :=
    IntermediateField.adjoin_eq_bot_iff.mpr (by
      simpa only [Set.singleton_subset_iff, SetLike.mem_coe, IntermediateField.mem_bot] using ht)
  intro x
  apply IntermediateField.mem_bot.mp
  rw [← hbot, hadjoin]
  exact IntermediateField.mem_top

/-- The fraction-field tower makes the specified base-ring embedding injective. -/
theorem algebraMap_injective_of_fractionTower
    {R K M : Type*} [CommRing R] [Field K] [Field M]
    [Algebra R K] [IsFractionRing R K] [Algebra K M] [Algebra R M]
    [IsScalarTower R K M] : Function.Injective (algebraMap R M) := by
  rw [IsScalarTower.algebraMap_eq R K M]
  exact (algebraMap K M).injective.comp (IsFractionRing.injective R K)

/-- A surjective intermediate scalar map does not enlarge the field generated
by a set. This is the arbitrary-presentation version of the trivial `L/K` case. -/
theorem adjoin_eq_top_of_surjective_scalarMap
    {K L M : Type*} [Field K] [Field L] [Field M]
    [Algebra K L] [Algebra L M] [Algebra K M] [IsScalarTower K L M]
    (hKL : Function.Surjective (algebraMap K L)) {s : Set M}
    (hgen : IntermediateField.adjoin L s = ⊤) : IntermediateField.adjoin K s = ⊤ := by
  apply top_unique
  intro x hx
  have hxL : x ∈ IntermediateField.adjoin L s := hgen ▸ IntermediateField.mem_top
  refine IntermediateField.adjoin_induction L
    (fun y hy ↦ IntermediateField.subset_adjoin K s hy)
    (fun l ↦ ?_) (fun a b _ _ ha hb ↦ add_mem ha hb)
    (fun a _ ha ↦ inv_mem ha) (fun a b _ _ ha hb ↦ mul_mem ha hb) hxL
  obtain ⟨k, rfl⟩ := hKL l
  rw [← IsScalarTower.algebraMap_apply K L M]
  exact IntermediateField.algebraMap_mem _ k

end ZInQ.Contrib.Abhyankar
