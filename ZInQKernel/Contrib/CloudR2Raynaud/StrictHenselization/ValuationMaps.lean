/-
Canonical maps between valuation subrings and their residue fields.
The coefficient map and inverse-residue point retain their literal values.
The fraction-preimage statement is proved by valuation-ring divisibility
and reflection of units, without an additional injectivity hypothesis.
-/
import Mathlib

set_option autoImplicit false
noncomputable section
universe u

namespace ZInQ.Contrib.CloudR2Raynaud.StrictHenselization

open IsLocalRing

section Comap

variable {K L : Type u} [Field K] [Field L] [Algebra K L]
variable {O : ValuationSubring K} {P : ValuationSubring L}

/-- The original coefficient embedding, restricted to the exact comap. -/
def comapHom (hP : P.comap (algebraMap K L) = O) : O →+* P where
  toFun r := ⟨algebraMap K L (r : K), by
    change (r : K) ∈ P.comap (algebraMap K L)
    rw [hP]
    exact r.2⟩
  map_one' := Subtype.ext (map_one (algebraMap K L))
  map_mul' r s := Subtype.ext (map_mul (algebraMap K L) (r : K) (s : K))
  map_zero' := Subtype.ext (map_zero (algebraMap K L))
  map_add' r s := Subtype.ext (map_add (algebraMap K L) (r : K) (s : K))

@[simp]
theorem comapHom_coe (hP : P.comap (algebraMap K L) = O) (r : O) :
    (comapHom hP r : L) = algebraMap K L (r : K) := rfl

/-- The exact-comap map reflects units. Its local-hom witness is derived
    by pulling the inverse in P back to the original valuation subring. -/
instance isLocalHom_comapHom (hP : P.comap (algebraMap K L) = O) :
    IsLocalHom (comapHom hP) where
  map_nonunit r hr := by
    obtain ⟨b, hb⟩ := hr.exists_right_inv
    have hmul : algebraMap K L (r : K) * (b : L) = 1 :=
      congrArg (fun a : P => (a : L)) hb
    have hL : algebraMap K L (r : K) ≠ 0 := by
      intro h
      rw [h, zero_mul] at hmul
      exact zero_ne_one hmul
    have hK : (r : K) ≠ 0 := by
      intro h
      apply hL
      rw [h, map_zero]
    have hbval : (b : L) = algebraMap K L ((r : K)⁻¹) := by
      rw [map_inv₀]
      apply mul_left_cancel₀ hL
      rw [hmul, mul_inv_cancel₀ hL]
    have hpre : (r : K)⁻¹ ∈ P.comap (algebraMap K L) := by
      change algebraMap K L ((r : K)⁻¹) ∈ P
      rw [← hbval]
      exact b.2
    have hinv : (r : K)⁻¹ ∈ O :=
      Eq.mp (congrArg (fun Q : ValuationSubring K => (r : K)⁻¹ ∈ Q) hP) hpre
    refine IsUnit.of_mul_eq_one (⟨(r : K)⁻¹, hinv⟩ : O) ?_
    apply Subtype.ext
    exact mul_inv_cancel₀ hK

/-- The induced map on the original residue fields. The local-hom
    witness is supplied internally by the exact-comap map above. -/
def residueMap (hP : P.comap (algebraMap K L) = O) :
    ResidueField O →+* ResidueField P :=
  ResidueField.map (comapHom hP)

@[simp]
theorem residueMap_residue (hP : P.comap (algebraMap K L) = O) (r : O) :
    residueMap hP (residue O r) = residue P (comapHom hP r) :=
  ResidueField.map_residue (comapHom hP) r

end Comap

namespace Ordinary

section ResiduePoint

variable {R S : Type u} [CommRing R] [IsLocalRing R] [CommRing S] [IsLocalRing S]

/-- The ordinary residue point is the literal inverse-residue composition. -/
def residuePoint (e : ResidueField R ≃+* ResidueField S) : S →+* ResidueField R :=
  e.symm.toRingHom.comp (residue S)

/-- Compatibility with the original base residue quotient. -/
theorem residuePoint_comp [Algebra R S]
    (e : ResidueField R ≃+* ResidueField S)
    (he : ∀ r : R, e (residue R r) = residue S (algebraMap R S r)) :
    (residuePoint e).comp (algebraMap R S) = residue R := by
  apply RingHom.ext
  intro r
  change e.symm (residue S (algebraMap R S r)) = residue R r
  rw [← he r, e.symm_apply_apply]

end ResiduePoint

end Ordinary

/-- A local map from the given DVR into w cannot make a genuinely
    nonintegral fraction integral. The proof uses that either a fraction
    or its inverse is in the DVR, and that the local map reflects units. -/
theorem fraction_preimage_of_local
    {Rh Ω : Type u} [CommRing Rh] [IsDomain Rh] [IsDiscreteValuationRing Rh] [Field Ω]
    (w : ValuationSubring Ω) (f : Rh →+* w) [IsLocalHom f]
    (φ₀ : FractionRing Rh →+* Ω)
    (hφ₀ : ∀ r : Rh, φ₀ (algebraMap Rh (FractionRing Rh) r) = (f r : Ω))
    (z : FractionRing Rh) (hwz : φ₀ z ∈ w) :
    ∃ r : Rh, algebraMap Rh (FractionRing Rh) r = z := by
  by_cases hz : z = 0
  · exact ⟨0, by rw [hz, map_zero]⟩
  obtain (⟨r, hr⟩ | ⟨r, hr⟩) := ValuationRing.isInteger_or_isInteger Rh z
  · exact ⟨r, hr⟩
  · have hzφ : φ₀ z ≠ 0 := by
      intro h
      apply hz
      apply φ₀.injective
      simpa only [map_zero] using h
    have hmul : (f r : Ω) * φ₀ z = 1 := by
      rw [← hφ₀ r, hr, map_inv₀, inv_mul_cancel₀ hzφ]
    have hfr : IsUnit (f r) :=
      IsUnit.of_mul_eq_one (⟨φ₀ z, hwz⟩ : w) (Subtype.ext hmul)
    have hunit : IsUnit r := isUnit_of_map_unit f r hfr
    obtain ⟨s, hs⟩ := hunit.exists_right_inv
    refine ⟨s, ?_⟩
    have hr0 : algebraMap Rh (FractionRing Rh) r ≠ 0 := by
      rw [hr]
      exact inv_ne_zero hz
    apply mul_left_cancel₀ hr0
    calc
      algebraMap Rh (FractionRing Rh) r * algebraMap Rh (FractionRing Rh) s = 1 := by
        rw [← map_mul, hs, map_one]
      _ = algebraMap Rh (FractionRing Rh) r * z := by
        rw [hr, inv_mul_cancel₀ hz]

end ZInQ.Contrib.CloudR2Raynaud.StrictHenselization
