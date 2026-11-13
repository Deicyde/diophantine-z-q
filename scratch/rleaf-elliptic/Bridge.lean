import Mathlib
import ZInQKernel.Contrib.TauCeti.AlgebraicGeometry.EllipticCurve.Affine.Point.Inertia
import ZInQKernel.Contrib.TauCeti.RingTheory.DedekindDomain.AdicValuation.Transport
import ZInQKernel.Contrib.TauCeti.RingTheory.DedekindDomain.AdicValuation.Basic

namespace ZInQ.RLeaf.T37

open IsDedekindDomain Pointwise

section Bridge

variable {R K L : Type*} [CommRing R] [Field K] [Field L] [Algebra R K] [IsFractionRing R K]
  [Algebra K L] [Algebra R L] [IsScalarTower R K L] [Algebra.IsAlgebraic K L]
  (B : Type*) [CommRing B] [IsDomain B] [IsDedekindDomain B] [Algebra B L] [IsFractionRing B L]
  [Algebra R B] [IsScalarTower R B L] [IsIntegralClosure B R L]

/-- The automorphism of `L = Frac B` induced by `galRestrict σ` is `σ`. -/
theorem ringEquivOfRingEquiv_galRestrict (σ : Gal(L/K)) (x : L) :
    IsFractionRing.ringEquivOfRingEquiv (A := B) (K := L) (B := B) (L := L)
      ((galRestrict R K L B σ : B ≃ₐ[R] B) : B ≃+* B) x = σ x := by
  obtain ⟨a, b, -, rfl⟩ := IsFractionRing.div_surjective (A := B) x
  rw [map_div₀, map_div₀, IsFractionRing.ringEquivOfRingEquiv_algebraMap,
    IsFractionRing.ringEquivOfRingEquiv_algebraMap]
  simp only [AlgEquiv.coe_toRingEquiv]
  rw [algebraMap_galRestrict_apply, algebraMap_galRestrict_apply]

variable {B}

/-- An automorphism acting trivially modulo `v` preserves the `v`-adic valuation. -/
theorem valuation_apply_of_forall_sub_mem (σ : Gal(L/K)) (v : HeightOneSpectrum B)
    (hσ : ∀ a : B, galRestrict R K L B σ a - a ∈ v.asIdeal) (x : L) :
    v.valuation L (σ x) = v.valuation L x := by
  set e : B ≃+* B := ((galRestrict R K L B σ : B ≃ₐ[R] B) : B ≃+* B)
  have he : ∀ a, e a = galRestrict R K L B σ a := fun _ => rfl
  have hvw : v.asIdeal = Ideal.map e v.asIdeal := by
    apply le_antisymm
    · intro a ha
      have hb : e.symm a ∈ v.asIdeal := by
        have h1 := hσ (e.symm a)
        rw [← he, e.apply_symm_apply] at h1
        have := v.asIdeal.sub_mem ha h1
        simpa using this
      rw [Ideal.mem_map_of_equiv]
      exact ⟨e.symm a, hb, e.apply_symm_apply a⟩
    · rw [Ideal.map_le_iff_le_comap]
      intro a ha
      rw [Ideal.mem_comap, he]
      have := v.asIdeal.add_mem ha (hσ a)
      simpa using this
  have := HeightOneSpectrum.valuation_ringEquivOfRingEquiv (K := L) (K' := L) e hvw x
  rwa [ringEquivOfRingEquiv_galRestrict] at this

/-- **Bridge**: an element of the ideal-theoretic inertia group of `v` (it acts trivially on
`B / v`) lies in the decomposition group and in the inertia group of the valuation subring of `v`
(Tau Ceti's / Mathlib's `ValuationSubring.inertiaSubgroup`). -/
theorem mem_inertiaSubgroup_of_forall_sub_mem (σ : Gal(L/K)) (v : HeightOneSpectrum B)
    (hσ : ∀ a : B, galRestrict R K L B σ a - a ∈ v.asIdeal) :
    ∃ h : σ ∈ (v.valuation L).valuationSubring.decompositionSubgroup K,
      (⟨σ, h⟩ : (v.valuation L).valuationSubring.decompositionSubgroup K) ∈
        (v.valuation L).valuationSubring.inertiaSubgroup K := by
  have hval := valuation_apply_of_forall_sub_mem σ v hσ
  have hval' : ∀ x : L, v.valuation L (σ⁻¹ x) = v.valuation L x := fun x => by
    conv_rhs => rw [← AlgEquiv.apply_symm_apply σ x]
    rw [hval]; rfl
  have hdec : σ ∈ (v.valuation L).valuationSubring.decompositionSubgroup K := by
    change σ • (v.valuation L).valuationSubring = (v.valuation L).valuationSubring
    ext x
    rw [ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem, AlgEquiv.smul_def,
      Valuation.mem_valuationSubring_iff, Valuation.mem_valuationSubring_iff, hval']
  refine ⟨hdec, ?_⟩
  rw [ValuationSubring.mem_inertiaSubgroup_iff]
  intro y
  rw [← sub_eq_zero, ← map_sub, IsLocalRing.residue_eq_zero_iff, Valuation.mem_maximalIdeal_iff]
  have hy : v.valuation L (y : L) ≤ 1 := y.2
  obtain ⟨n, d, hnd⟩ := HeightOneSpectrum.exists_primeCompl_mul_eq_of_integer v (y : L) hy
  set Y : L := (y : L)
  have hsmul : (((⟨σ, hdec⟩ : (v.valuation L).valuationSubring.decompositionSubgroup K) • y :
      (v.valuation L).valuationSubring) : L) = σ Y :=
    ValuationSubring.coe_decompositionSubgroup_smul _ _ y
  rw [AddSubgroupClass.coe_sub, hsmul]
  -- notation
  set D : L := algebraMap B L (d : B)
  set Nn : L := algebraMap B L n
  have hσD : σ D = algebraMap B L (galRestrict R K L B σ (d : B)) :=
    (algebraMap_galRestrict_apply R σ (d : B)).symm
  have hσN : σ Nn = algebraMap B L (galRestrict R K L B σ n) :=
    (algebraMap_galRestrict_apply R σ n).symm
  have hσY : σ Y * σ D = σ Nn := by rw [← map_mul, hnd]
  have hD1 : v.valuation L D = 1 := by
    rw [HeightOneSpectrum.valuation_of_algebraMap]
    exact (v.intValuation_eq_one_iff_mem_primeCompl (d : B)).mpr d.2
  have hσD1 : v.valuation L (σ D) = 1 := by rw [hval, hD1]
  have hkey : (σ Y - Y) * (D * σ D) = (σ Nn - Nn) * D - Nn * (σ D - D) := by
    linear_combination D * hσY - σ D * hnd
  have hlt1 : v.valuation L (σ Nn - Nn) < 1 := by
    rw [hσN, ← map_sub, HeightOneSpectrum.valuation_lt_one_iff_mem]
    exact hσ n
  have hlt2 : v.valuation L (σ D - D) < 1 := by
    rw [hσD, ← map_sub, HeightOneSpectrum.valuation_lt_one_iff_mem]
    exact hσ d
  have hN1 : v.valuation L Nn ≤ 1 := HeightOneSpectrum.valuation_le_one v n
  have hrhs : v.valuation L ((σ Nn - Nn) * D - Nn * (σ D - D)) < 1 := by
    refine lt_of_le_of_lt (Valuation.map_sub _ _ _) (max_lt ?_ ?_)
    · rw [map_mul, hD1, mul_one]; exact hlt1
    · rw [map_mul]
      calc v.valuation L Nn * v.valuation L (σ D - D) ≤ 1 * v.valuation L (σ D - D) := by
            gcongr
        _ < 1 := by rw [one_mul]; exact hlt2
  rw [← hkey, map_mul, map_mul, hD1, hσD1, mul_one, mul_one] at hrhs
  exact hrhs

end Bridge

end ZInQ.RLeaf.T37
