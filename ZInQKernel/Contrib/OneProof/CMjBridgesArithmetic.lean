import ZInQKernel.Contrib.OneProof.CMjBridgesPrint
import Mathlib.Algebra.Algebra.Rat

namespace HDec.CMBranch.CMjBridges

open scoped UpperHalfPlane
open Module NumberField TauCeti.GlobalNumberFields

/-- A nonsingular Weierstrass equation over `L` has its algebraic j-value in `L`;
mapping the coefficients by `σ` maps the j-value by `σ`. This does not assert the
existence of such an equation for an arbitrary scheme in the row. -/
theorem weierstrass_j_map {L : Type} [Field L] (W : WeierstrassCurve L) [W.IsElliptic]
    (σ : L →+* ℂ) : σ W.j = (W.map σ).j :=
  (W.map_j σ).symm

/-- Over an embedding of a number field, an element of the image generates a
subextension of degree at most that of the number field. -/
theorem degree_le_of_mem_range {L : Type} [Field L] [NumberField L] (σ : L →+* ℂ)
    {x : ℂ} (hx : x ∈ Set.range σ) :
    finrank ℚ (IntermediateField.adjoin ℚ {x}) ≤ finrank ℚ L := by
  let f : L →ₐ[ℚ] ℂ := { σ with commutes' := σ.map_rat_algebraMap }
  have h : IntermediateField.adjoin ℚ {x} ≤ f.fieldRange :=
    IntermediateField.adjoin_simple_le_iff.mpr (show x ∈ f.fieldRange from hx)
  let g := f.equivFieldRange.symm.toLinearMap.comp (IntermediateField.inclusion h).toLinearMap
  have hg : Function.Injective g :=
    f.equivFieldRange.symm.injective.comp (IntermediateField.inclusion h).injective
  exact LinearMap.finrank_le_finrank_of_injective hg

/-- The order representing `R` for the printed class number has discriminant `orderDisc R`. -/
theorem toOrder_discr_eq_orderDisc {k : Type} [Field k] [NumberField k] (R : Subring k)
    (hR : IsImagQuadOrder k R) : (FowlerBridges.toOrder R hR).discr = orderDisc R := by
  obtain ⟨b⟩ := FowlerBridges.exists_intBasis_of_isImagQuadOrder R hR
  exact ((FowlerBridges.toOrder R hR).discr_eq_discr b).symm.trans
    (FowlerBridges.orderDisc_eq_discr R hR b).symm

/-- Steps 4 and 5: if a singular modulus of discriminant `orderDisc R` lies in the
embedded number field, Fowler's printed degree equality bounds the Picard cardinal. -/
theorem card_pic_le_of_singular_modulus (hPrint : CMjDegreePrint)
    {L : Type} [Field L] [NumberField L] (σ : L →+* ℂ)
    {k : Type} [Field k] [NumberField k] (R : Subring k) (hR : IsImagQuadOrder k R)
    {x : ℂ} (hx : x ∈ Set.range σ) (hDisc : IsSingularModulusOfDisc x (orderDisc R)) :
    Nat.card (CommRing.Pic R) ≤ finrank ℚ L := by
  let : IsTotallyComplex k := hR.1
  have hDegree := hPrint x (orderDisc R) hDisc k hR.2.1
    (FowlerBridges.toOrder R hR) (toOrder_discr_eq_orderDisc R hR)
  rw [FowlerBridges.card_pic_eq_properClassNumber R hR, ← hDegree]
  exact degree_le_of_mem_range σ hx

end HDec.CMBranch.CMjBridges
