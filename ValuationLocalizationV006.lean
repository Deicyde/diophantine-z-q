import ExtendedRingMapsV003
import Mathlib.RingTheory.DedekindDomain.Dvr
import Mathlib.RingTheory.KrullDimension.PID

/-! # A valuation ring dominating a Dedekind normalization is its localization at the center -/

noncomputable section
set_option autoImplicit false

namespace FiniteExtensionValuation

variable {F : Type*} [Field F]

/-- A DVR realized as a subring of its fraction field is a valuation subring. -/
def dvrValuationSubring (S : Subring F) [IsDiscreteValuationRing S] [IsFractionRing S F] :
    ValuationSubring F :=
  ValuationSubring.ofSubring S (fun x => by
    rcases ValuationRing.isInteger_or_isInteger S x with ⟨a, ha⟩ | ⟨a, ha⟩
    · exact Or.inl (ha ▸ a.2)
    · exact Or.inr (ha ▸ a.2))

instance dvrValuationSubring_isDVR (S : Subring F) [IsDiscreteValuationRing S]
    [IsFractionRing S F] : IsDiscreteValuationRing (dvrValuationSubring S) :=
  inferInstanceAs (IsDiscreteValuationRing S)

/-- The literal fraction description at the center of a valuation ring. -/
theorem dedekind_center_fraction_description (C : Subring F) [IsDedekindDomain C]
    [IsFractionRing C F] (w : ValuationSubring F) (hC : C ≤ w.toSubring)
    (hw : w ≠ ⊤)
    (hq0 : (IsLocalRing.maximalIdeal w).comap (Subring.inclusion hC) ≠ ⊥) :
    ∀ x : F, x ∈ w ↔ ∃ a s : C,
      s ∉ (IsLocalRing.maximalIdeal w).comap (Subring.inclusion hC) ∧
      x = (a : F) * (s : F)⁻¹ := by
  let q : Ideal C := (IsLocalRing.maximalIdeal w).comap (Subring.inclusion hC)
  let S := Localization.subalgebra.ofField F q.primeCompl q.primeCompl_le_nonZeroDivisors
  haveI : IsDiscreteValuationRing S :=
    IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain C hq0 S
  haveI : IsDiscreteValuationRing S.toSubring := inferInstanceAs (IsDiscreteValuationRing S)
  haveI : IsFractionRing S.toSubring F := inferInstanceAs (IsFractionRing S F)
  let V := dvrValuationSubring S.toSubring
  have hV : V ≤ w := by
    intro x hx
    change x ∈ S at hx
    rcases hx with ⟨a, s, hs, rfl⟩
    apply w.mul_mem
    · exact hC a.2
    · have hv : w.valuation (s : F) = 1 := by
        apply (w.valuation_eq_one_iff (Subring.inclusion hC s)).1
        change s ∉ q at hs
        simpa only [q, Ideal.mem_comap, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff,
          not_not] using hs
      apply (w.valuation_le_one_iff _).1
      change w.valuation (s : F)⁻¹ ≤ 1
      rw [map_inv₀, hv, inv_one]
  have heq : V = w := V.eq_of_le_of_ne_top hV hw
  intro x
  apply (show x ∈ w ↔ x ∈ V from by rw [heq]).trans
  change (∃ a s : C, ∃ (_ : s ∉ q), x = (a : F) * (s : F)⁻¹) ↔ _
  simp only [exists_prop]
  rfl

end FiniteExtensionValuation
