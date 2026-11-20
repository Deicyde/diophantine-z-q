import ZInQKernel.HDecomp.Objects
import ZInQKernel.Contrib.TauCeti.RingTheory.RootsOfUnity.LocalRing

namespace SZRaynaud

/-- Inertia fixes every root of unity whose order is invertible in the valuation ring. -/
theorem inertia_fixes_root_of_unity {K Ω : Type} [Field K] [Field Ω] [Algebra K Ω]
    (w : ValuationSubring Ω) (σ : Ω ≃ₐ[K] Ω) (hσ : PkgI2.IsInertia w σ)
    {n : ℕ} (hn : IsUnit (n : w)) (x : Ω) (hx : x ^ n = 1) : σ x = x := by
  have hne : n ≠ 0 := by
    rintro rfl
    simp at hn
  have hmem {a : Ω} (ha : a ^ n = 1) : a ∈ w := by
    rw [← w.valuation_le_one_iff, ← pow_le_one_iff_of_nonneg zero_le hne, ← map_pow, ha, map_one]
  let xw : w := ⟨x, hmem hx⟩
  have hpow : (σ x) ^ n = 1 := by rw [← map_pow, hx, map_one]
  let yw : w := ⟨σ x, hmem hpow⟩
  obtain ⟨hD, hI⟩ := hσ
  have hres := RingEquiv.congr_fun hI (IsLocalRing.residue w xw)
  change (⟨σ, hD⟩ : w.decompositionSubgroup K) • IsLocalRing.residue w xw =
    IsLocalRing.residue w xw at hres
  rw [← IsLocalRing.ResidueField.residue_smul] at hres
  change IsLocalRing.residue w yw = IsLocalRing.residue w xw at hres
  have he := TauCeti.eq_of_residue_eq_of_pow_eq_one hn (show yw ^ n = 1 from Subtype.ext hpow)
    (show xw ^ n = 1 from Subtype.ext hx) hres
  exact congrArg Subtype.val he

end SZRaynaud
