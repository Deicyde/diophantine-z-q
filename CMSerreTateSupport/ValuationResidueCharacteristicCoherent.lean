import Mathlib.RingTheory.Valuation.ValuationSubring
import Mathlib.RingTheory.LocalRing.ResidueField.Basic
import Mathlib.Algebra.CharP.Algebra

/-!
# Coherent residue characteristics under valuation restriction

The residue field maps are obtained from the actual inverse-image
valuation rings. Units are reflected by the natural maps, so the residue
characteristic is the same on every finite restriction.
-/

noncomputable section
set_option autoImplicit false

namespace ValuationResidueCharacteristic

variable {K Ω : Type*} [Field K] [Field Ω]

def comapMap (w : ValuationSubring Ω) (f : K →+* Ω) : w.comap f →+* w :=
  (f.comp (w.comap f).subtype).codRestrict w.toSubring (fun x => x.2)

theorem comap_valuation_equiv (w : ValuationSubring Ω) (f : K →+* Ω) :
    (w.valuation.comap f).IsEquiv (w.comap f).valuation := by
  apply Valuation.isEquiv_of_val_le_one
  intro x
  simp only [Valuation.comap_apply, ValuationSubring.valuation_le_one_iff, ValuationSubring.mem_comap]

instance comapMap_isLocalHom (w : ValuationSubring Ω) (f : K →+* Ω) : IsLocalHom (comapMap w f) where
  map_nonunit a ha := by
    apply ((w.comap f).valuation_eq_one_iff a).mpr
    apply (comap_valuation_equiv w f).eq_one_iff_eq_one.mp
    exact (w.valuation_eq_one_iff (comapMap w f a)).mp ha

def residueMap (w : ValuationSubring Ω) (f : K →+* Ω) :
    IsLocalRing.ResidueField (w.comap f) →+* IsLocalRing.ResidueField w :=
  IsLocalRing.ResidueField.map (comapMap w f)

/-- The actual residue characteristic on a restricted valuation ring is
identical to the original residue characteristic. -/
theorem residue_charP_iff (w : ValuationSubring Ω) (f : K →+* Ω) (p : ℕ) :
    CharP (IsLocalRing.ResidueField (w.comap f)) p ↔ CharP (IsLocalRing.ResidueField w) p :=
  (residueMap w f).charP_iff (residueMap w f).injective p

/-- An invertible prime is distinct from the actual positive residue
characteristic; no p-versus-ell comparison is supplied. -/
theorem prime_ne_of_isUnit (O : ValuationSubring K) (p ell : ℕ)
    [CharP (IsLocalRing.ResidueField O) p] (hu : IsUnit (ell : O)) : p ≠ ell := by
  intro h
  have hne := (IsLocalRing.residue_ne_zero_iff_isUnit (ell : O)).mpr hu
  rw [map_natCast, ← h, CharP.cast_eq_zero] at hne
  exact hne rfl

#print axioms residue_charP_iff
#print axioms prime_ne_of_isUnit
#check IsAlgebraic.exists_nonzero_coeff_and_aeval_eq_zero
#check Polynomial.aeval_algHom_apply
#check RingHom.toIntAlgHom
#check CharP.intCast_eq_zero_iff

end ValuationResidueCharacteristic
