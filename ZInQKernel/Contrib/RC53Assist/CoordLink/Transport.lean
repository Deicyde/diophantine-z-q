import ZInQKernel.Contrib.CloudB3RC53.CoordLink.RelCore

/-!
# Coordinate transport through nonunit denominators

Manuscript ex:arith-coordinate, TeX 3877–3892, and
ex:arith-common-coordinate, TeX 4155 and 4219–4231.

Two scalar realizations of one integral matrix model are compared by clearing
one nonzero denominator in their common coefficient ring.  That denominator
need not be a unit of the power-series ring.  The source scalar ring can itself
be a fraction field, so the result does not impose regularity on the relaxed
coordinate or on the correction.  No additional printed proposition is used.
-/

set_option autoImplicit false

noncomputable section

namespace ZInQ.Contrib.RC53Assist.CoordLink

open Matrix
open ZInQ.Manuscript.RC
open ZInQ.Contrib.CloudB3RC53.CoordLink
open ZInQ.Manuscript.RC.Determinant (Lam OO)

section Transport

variable {R A F : Type*} [CommRing R] [CommRing A] [Field F]

/-- A class-functional coordinate transports through a common nonzero
numerator-denominator representation.  Neither realization requires the
denominator to be a unit of the common coefficient ring. -/
theorem isClassFunctionalCoord_transport_cleared {n : ℕ}
    (f : R →+* A) (hf : Function.Injective f) (g : R →+* F) (hg : Function.Injective g)
    (D : Matrix (Fin n) (Fin n) R) (z w : Fin n → R)
    (u : A) (num den : R) (hden : den ≠ 0)
    (hu : Central.IsClassFunctionalCoord (D.map f) (f ∘ z) (f ∘ w) u)
    (hclear : f den * u = f num) :
    Central.IsClassFunctionalCoord (D.map g) (g ∘ z) (g ∘ w) (g num / g den) := by
  have hR : ∀ i j, den * z i * w j = num * D.adjugate i j := by
    intro i j
    apply hf
    have h := congrFun (congrFun hu i) j
    simp only [vecMulVec_apply, Function.comp_apply, Matrix.smul_apply, smul_eq_mul,
      adjugate_map_apply] at h
    simp only [map_mul]
    calc
      f den * f (z i) * f (w j) = f den * (f (z i) * f (w j)) := by ring
      _ = f den * (u * f (D.adjugate i j)) := by rw [h]
      _ = f num * f (D.adjugate i j) := by rw [← mul_assoc, hclear]
  have hgd : g den ≠ 0 := (map_ne_zero_iff g hg).mpr hden
  refine Matrix.ext fun i j => ?_
  have h := congrArg g (hR i j)
  simp only [map_mul] at h
  change g (z i) * g (w j) = (g num / g den) * (D.map g).adjugate i j
  rw [adjugate_map_apply, div_mul_eq_mul_div]
  apply (eq_div_iff hgd).mpr
  calc
    g (z i) * g (w j) * g den = g den * g (z i) * g (w j) := by ring
    _ = g num * g (D.adjugate i j) := h

/-- Every nonzero maximal minor gives a common cleared representative of the
coordinate.  This proves rationality from the integral model, rather than
assuming that the relaxed coordinate belongs to the two-localized power series. -/
theorem exists_common_coordinate_fraction {n : ℕ}
    (f : R →+* A) (hf : Function.Injective f) (g : R →+* F) (hg : Function.Injective g)
    (D : Matrix (Fin n) (Fin n) R) (z w : Fin n → R) (u : A)
    (hadj : D.adjugate ≠ 0)
    (hu : Central.IsClassFunctionalCoord (D.map f) (f ∘ z) (f ∘ w) u) :
    ∃ num den : R, den ≠ 0 ∧ f den * u = f num ∧
      Central.IsClassFunctionalCoord (D.map g) (g ∘ z) (g ∘ w) (g num / g den) := by
  obtain ⟨i, j, hij⟩ := Central.exists_entry_ne_zero hadj
  have hclear : f (D.adjugate i j) * u = f (z i * w j) := by
    have h := congrFun (congrFun hu i) j
    simp only [vecMulVec_apply, Function.comp_apply, Matrix.smul_apply, smul_eq_mul,
      adjugate_map_apply] at h
    rw [map_mul, mul_comm]
    exact h.symm
  exact ⟨z i * w j, D.adjugate i j, hij, hclear,
    isClassFunctionalCoord_transport_cleared f hf g hg D z w u _ _ hij hu hclear⟩

/-- The resulting fraction is independent of the cleared representative:
nonzero adjugate and injectivity make the target coordinate unique. -/
theorem common_coordinate_fraction_unique {n : ℕ}
    (f : R →+* A) (hf : Function.Injective f) (g : R →+* F) (hg : Function.Injective g)
    (D : Matrix (Fin n) (Fin n) R) (z w : Fin n → R) (u : A)
    (hadj : D.adjugate ≠ 0)
    (hu : Central.IsClassFunctionalCoord (D.map f) (f ∘ z) (f ∘ w) u)
    (num den num' den' : R) (hden : den ≠ 0) (hden' : den' ≠ 0)
    (hclear : f den * u = f num) (hclear' : f den' * u = f num') :
    g num / g den = g num' / g den' := by
  have hadjF : (D.map g).adjugate ≠ 0 := by
    obtain ⟨i, j, hij⟩ := Central.exists_entry_ne_zero hadj
    intro h
    have hentry := congrFun (congrFun h i) j
    rw [adjugate_map_apply, Matrix.zero_apply] at hentry
    exact hij ((map_eq_zero_iff g hg).mp hentry)
  exact Central.isClassFunctionalCoord_unique hadjF
    (isClassFunctionalCoord_transport_cleared f hf g hg D z w u num den hden hu hclear)
    (isClassFunctionalCoord_transport_cleared f hf g hg D z w u num' den' hden' hu hclear')

end Transport

/-- The common power-series coefficient ring embeds in the clearing fraction field. -/
theorem psiO_injective : Function.Injective ψO :=
  (IsFractionRing.injective OO (FractionRing OO)).comp
    (by simpa [Determinant.algebraMap_eq_lamToO] using Determinant.lamToO_injective)

/-- The concrete two-world bridge with an arbitrary nonzero power-series
denominator, replacing the integral-unit restriction. -/
theorem isClassFunctionalCoord_transport_nonunit {n : ℕ}
    (D : Matrix (Fin n) (Fin n) Lam) (z w : Fin n → Lam)
    (u : PowerSeries ℚ_[2]) (num den : Lam) (hden : den ≠ 0)
    (hu : Central.IsClassFunctionalCoord (D.map ιQ) (ιQ ∘ z) (ιQ ∘ w) u)
    (hclear : ιQ den * u = ιQ num) :
    Central.IsClassFunctionalCoord (D.map ψO) (ψO ∘ z) (ψO ∘ w) (ψO num / ψO den) :=
  isClassFunctionalCoord_transport_cleared ιQ ιQ_injective ψO psiO_injective
    D z w u num den hden hu hclear

set_option pp.universes false

end ZInQ.Contrib.RC53Assist.CoordLink
