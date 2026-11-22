import Mathlib.Algebra.Module.LocalizedModule.Away
import Mathlib.RingTheory.Localization.Away.Basic
import Mathlib.RingTheory.Ideal.Maps

/-!
The genuine denominator-clearing step for reverse ideal extraction.
A section image into the unit module localizes to the section image on a basic
open. The localization and compatibility maps are concrete linear maps, not a
GAGA or graph-algebraicity premise.
-/

set_option autoImplicit false

noncomputable section

namespace ZInQ.Contrib.CloudB3W17bGraphScoutReverseIdeal

/-- The image of a linear map into the ring is an actual ideal. -/
def linearRangeIdeal {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    (q : M →ₗ[R] R) : Ideal R := LinearMap.range q

/-- A compatible image into the unit module commutes with localization at a basic open.
This is the nontrivial map_ideal_basicOpen edge needed by Scheme.IdealSheafData. -/
theorem linearRangeIdeal_localization
    {R S M N : Type*} [CommRing R] [CommRing S] [Algebra R S]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N] [Module S N]
    [IsScalarTower R S N] (a : R) [IsLocalization.Away a S]
    (l : M →ₗ[R] N) [IsLocalizedModule.Away a l]
    (q : M →ₗ[R] R) (q' : N →ₗ[S] S)
    (h : ∀ m, q' (l m) = algebraMap R S (q m)) :
    (linearRangeIdeal q).map (algebraMap R S) = linearRangeIdeal q' := by
  apply le_antisymm
  · refine Ideal.map_le_iff_le_comap.mpr ?_
    rintro r ⟨m, rfl⟩
    exact ⟨l m, h m⟩
  · rintro y ⟨n, rfl⟩
    obtain ⟨k, m, hm⟩ := IsLocalizedModule.Away.surj l a n
    have hden : algebraMap R S (a ^ k) * q' n = algebraMap R S (q m) := by
      have hd := congrArg q' hm
      rw [← IsScalarTower.algebraMap_smul S (a ^ k) n, q'.map_smul, smul_eq_mul, h m] at hd
      exact hd
    have hu : IsUnit (algebraMap R S (a ^ k)) := by
      rw [map_pow]
      exact (IsLocalization.Away.algebraMap_isUnit (S := S) a).pow k
    obtain ⟨u, hu⟩ := hu
    have hmem : (u : S) * q' n ∈ (linearRangeIdeal q).map (algebraMap R S) := by
      rw [hu, hden]
      exact Ideal.mem_map_of_mem (algebraMap R S) ⟨m, rfl⟩
    have hi := ((linearRangeIdeal q).map (algebraMap R S)).mul_mem_left (↑u⁻¹ : S) hmem
    simpa only [← mul_assoc, u.inv_mul, one_mul] using hi

end ZInQ.Contrib.CloudB3W17bGraphScoutReverseIdeal
