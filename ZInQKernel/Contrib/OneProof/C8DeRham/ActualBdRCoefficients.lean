import ZInQKernel.Contrib.OneProof.DeRhamRange
import ZInQKernel.OneProof.H.TailT

/-! # The coefficient embedding used by the C8 Hom calculation

Use the actual coefficient subfield of the chosen algebraic closure, not an
abstract field equipped with an unrelated embedding. Its embedding in `B_dR`
is the Hensel lift of that very embedding in `ℂ_p`.
-/

noncomputable section

namespace HDec.G0Galois.C8Conrad.Manuscript

open _root_.ZInQ.Contrib.G9 _root_.ZInQ.Contrib.G9.PkgI4
open _root_.ZInQ.Contrib.HodgeSplit

section Coefficients

variable (p : ℕ) [Fact p.Prime]
variable (E : IntermediateField ℚ_[p] (PadicAlgCl p)) [FiniteDimensional ℚ_[p] E]

attribute [local instance] algPlus

/-- The original inclusion of the coefficient subfield in `ℂ_p`. -/
abbrev coeffToCp : E →ₐ[ℚ_[p]] ℂ_[p] := IsScalarTower.toAlgHom ℚ_[p] E ℂ_[p]

private theorem exists_coeffToBdRPlus :
    ∃ j : E →ₐ[ℚ_[p]] BDeRhamPlus 𝓞_ℂ_[p] p,
      ∀ x, thetaAlg p (j x) = coeffToCp p E x :=
  exists_hensel_lift (thetaAlg p) (BdrKer.Cp.thetaPlusCp_surjective p)
    (isUnit_of_thetaAlg_ne_zero p) (coeffToCp p E)

/-- The actual coefficient field, inside `B_dR^+`. -/
def coeffToBdRPlus : E →ₐ[ℚ_[p]] BDeRhamPlus 𝓞_ℂ_[p] p :=
  (exists_coeffToBdRPlus p E).choose

theorem theta_coeffToBdRPlus (x : E) :
    thetaAlg p (coeffToBdRPlus p E x) = coeffToCp p E x :=
  (exists_coeffToBdRPlus p E).choose_spec x

/-- The same coefficient field inside `B_dR`. -/
def coeffToBdR : E →ₐ[ℚ_[p]] BdR p :=
  { (algebraMap (BDeRhamPlus 𝓞_ℂ_[p] p) (BdR p)).comp (coeffToBdRPlus p E).toRingHom with
    commutes' := fun c => by
      change algebraMap _ (BdR p) (coeffToBdRPlus p E (algebraMap ℚ_[p] E c)) = qpToBdR p c
      rw [AlgHom.commutes]
      rfl }

/-- The canonical embedding is equivariant for any automorphism preserving
the chosen coefficient subfield. -/
theorem bdrAct_coeffToBdR_of (σ : GQp p) (u : E →ₐ[ℚ_[p]] E)
    (hu : ∀ x : E, σ (x : PadicAlgCl p) = (u x : PadicAlgCl p)) (x : E) :
    bdrAct p σ (coeffToBdR p E x) = coeffToBdR p E (u x) := by
  have hι (z : E) : cpAct p σ (coeffToCp p E z) = coeffToCp p E (u z) := by
    change cpAct p σ ((z : PadicAlgCl p) : ℂ_[p]) = ((u z : PadicAlgCl p) : ℂ_[p])
    rw [cpAct_coe, hu z]
  have heq : DR.bdrPlusMap p (oAct p σ) (coeffToBdRPlus p E x) = coeffToBdRPlus p E (u x) :=
    hensel_lift_natural (thetaAlg p) (coeffToCp p E) (coeffToBdRPlus p E)
      (theta_coeffToBdRPlus p E) (sPlus p σ) u
      (fun z => by
        change BdrKer.Cp.thetaPlusCp p (DR.bdrPlusMap p (oAct p σ) (coeffToBdRPlus p E z)) =
          coeffToCp p E (u z)
        rw [thetaPlusCp_bdrPlusMap, ← thetaAlg_apply, theta_coeffToBdRPlus, hι]) x
  change bdrAct p σ (algebraMap (BDeRhamPlus 𝓞_ℂ_[p] p) (BdR p) (coeffToBdRPlus p E x)) = _
  rw [BdRInv.bdrAct_algebraMap, heq]
  rfl

/-- The coefficient fixing subgroup really fixes these elements of `B_dR`. -/
theorem bdrAct_coeffToBdR (σ : GQp p) (hσ : σ ∈ E.fixingSubgroup) (x : E) :
    bdrAct p σ (coeffToBdR p E x) = coeffToBdR p E x :=
  bdrAct_coeffToBdR_of p E σ (AlgHom.id _ _) (fun z => hσ z) x

/-- The action on coefficients is the actual restriction of the original
Galois action, not a choice of another copy of the coefficient field. -/
theorem bdrAct_coeffToBdR_restrict [IsGalois ℚ_[p] E] (σ : GQp p) (x : E) :
    bdrAct p σ (coeffToBdR p E x) = coeffToBdR p E ((AlgEquiv.restrictNormalHom E) σ x) :=
  bdrAct_coeffToBdR_of p E σ ((AlgEquiv.restrictNormalHom E) σ).toAlgHom
    (fun z => (AlgEquiv.restrictNormal_commutes σ E z).symm) x

end Coefficients

/-- Fixed-field equality for the same finite Galois coefficient subfield,
with the canonical embedding used in the matrix equations. -/
theorem exists_coeffToBdR_of_fixed (p : ℕ) [Fact p.Prime]
    (E : IntermediateField ℚ_[p] (PadicAlgCl p)) [FiniteDimensional ℚ_[p] E] [IsGalois ℚ_[p] E]
    (x : BdR p) (hx : ∀ σ ∈ E.fixingSubgroup, bdrAct p σ x = x) :
    ∃ y : E, coeffToBdR p E y = x := by
  have hE : fieldF p E = E := AlgHom.fieldRange_of_normal (phiF p E)
  let L := (coeffToBdR p E).toLinearMap
  have hL : Function.Injective L := (coeffToBdR p E).injective
  have heq : Set.range (gfToGqp p E) = (E.fixingSubgroup : Set (GQp p)) := by
    rw [range_gfToGqp_eq, hE]
  have hLfix : LinearMap.range L ≤ DeRhamPrint.bdrFix p E := by
    rintro _ ⟨y, rfl⟩ g
    have hg : gfToGqp p E g ∈ E.fixingSubgroup := by
      have hm : gfToGqp p E g ∈ Set.range (gfToGqp p E) := ⟨g, rfl⟩
      rw [heq] at hm
      exact hm
    exact bdrAct_coeffToBdR p E _ hg y
  have hd : Module.finrank ℚ_[p] (DeRhamPrint.bdrFix p E) = Module.finrank ℚ_[p] E :=
    BdRInv.bdRInvariantsPrinted_proof p E
  letI : FiniteDimensional ℚ_[p] (DeRhamPrint.bdrFix p E) :=
    Module.finite_of_finrank_pos (hd ▸ Module.finrank_pos)
  have hR : LinearMap.range L = DeRhamPrint.bdrFix p E :=
    Submodule.eq_of_le_of_finrank_eq hLfix ((LinearMap.finrank_range_of_inj hL).trans hd.symm)
  have hmem : x ∈ DeRhamPrint.bdrFix p E := by
    intro g
    have hg : gfToGqp p E g ∈ Set.range (gfToGqp p E) := ⟨g, rfl⟩
    rw [heq] at hg
    exact hx _ hg
  have hmem' : x ∈ LinearMap.range L := by rw [hR]; exact hmem
  exact hmem'

end HDec.G0Galois.C8Conrad.Manuscript
