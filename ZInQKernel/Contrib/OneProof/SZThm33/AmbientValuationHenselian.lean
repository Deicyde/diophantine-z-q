import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Valuation.LocalSubring
import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
import Mathlib.FieldTheory.IsAlgClosed.Basic

/-!
# Henselian valuation rings in algebraically closed fields
-/

open Polynomial IsLocalRing

namespace SZRaynaud

universe u

/-- Every monic polynomial over a valuation subring of an algebraically
closed field splits in that valuation subring. -/
theorem splits_of_monic_of_valuationSubring {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (w : ValuationSubring Ω) {f : w[X]} (hf : f.Monic) : f.Splits := by
  apply (IsAlgClosed.splits (f.map (algebraMap w Ω))).of_splits_algebraMap
  intro x hx
  exact (IsIntegrallyClosed.isIntegral_iff (R := w) (K := Ω)).mp
    ⟨f, hf, Polynomial.aeval_eq_zero_of_mem_rootSet hx⟩

/-- A valuation subring in an algebraically closed field is henselian. -/
theorem henselianLocalRing_of_valuationSubring {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (w : ValuationSubring Ω) : HenselianLocalRing w where
  toIsLocalRing := inferInstance
  is_henselian f hf a ha _ := by
    have hz := (IsLocalRing.residue_eq_zero_iff _).2 ha
    rw [(splits_of_monic_of_valuationSubring w hf).eval_eq_prod_roots_of_monic hf,
      map_multiset_prod, Multiset.map_map, Multiset.prod_eq_zero_iff] at hz
    obtain ⟨x, hx, hxz⟩ := Multiset.mem_map.mp hz
    have hax : residue w (a - x) = 0 := hxz
    have hxa : residue w (x - a) = 0 := by rw [← neg_sub, map_neg, hax, neg_zero]
    exact ⟨x, (mem_roots hf.ne_zero).mp hx, (IsLocalRing.residue_eq_zero_iff _).mp hxa⟩

#print axioms splits_of_monic_of_valuationSubring
#print axioms henselianLocalRing_of_valuationSubring

end SZRaynaud
