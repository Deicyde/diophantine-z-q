import ZInQKernel.Contrib.RC53Assist.HodgeLatticeIdeal.Coordinates
import ZInQKernel.Contrib.RC53Assist.HodgeLatticeIdeal.ModelLattice

/-!
# The fractional ideal of a first Hodge lattice in nonzero coordinates

For a one-dimensional group model and a nonzero vector `η`, the coefficients of the unchanged
Hodge lattice form a nonzero fractional ideal. Its norm gives the original section index,
with the orientation `#(I / 𝓞_L a)`, whenever `a` is a nonzero element of `I`.
This does not assert that `I` is principal or that `η` is a global integral generator.

Locators: `ModelLattice.hodgeLattice_one`, `IdealLines.secIndex_mul_absNorm`, Mathlib,
`FractionalIdeal.isFractional_of_fg`, `FractionalIdeal.absNorm_eq_zero_iff`.
-/

set_option maxHeartbeats 800000
set_option autoImplicit false

noncomputable section

namespace ZInQ.Contrib.RC53Assist.HodgeLatticeIdeal

open NumberField
open ZInQ.DefFaltings
open ZInQ.Contrib.RC53Assist.HodgeLineBinding

variable {K : Type} [Field K] {E : PkgI3.AbVar K} {L : Type} [Field L] [NumberField L]
  [Algebra K L]

/-- THEOREM. The determinant lattice is reconstructed from its exact coefficients.
Locator: `Coordinates.coefficientSubmodule_map`, `finrank_hodgeSpace_one_of_dim_one`. -/
theorem detLattice_eq_coefficient_map (G : GroupModel E L) (hdim : E.dim = 1)
    (η : G.hodgeSpace 1) (hη : η ≠ 0) :
    G.detLattice 1 = (coefficientSubmodule (G.detLattice 1) η).map (coordinateMap η) :=
  coefficientSubmodule_map (finrank_hodgeSpace_one_of_dim_one G hdim) η hη _

/-- THEOREM. Each original determinant-lattice element has a unique admissible coefficient.
Locator: `Coordinates.existsUnique_coefficient`, `finrank_hodgeSpace_one_of_dim_one`. -/
theorem existsUnique_detLattice_coefficient (G : GroupModel E L) (hdim : E.dim = 1)
    (η : G.hodgeSpace 1) (hη : η ≠ 0) (v : G.hodgeSpace 1) (hv : v ∈ G.detLattice 1) :
    ∃! a : L, a ∈ coefficientSubmodule (G.detLattice 1) η ∧ a • η = v :=
  existsUnique_coefficient (finrank_hodgeSpace_one_of_dim_one G hdim) η hη _ v hv

/-- THEOREM. The coefficients of the original determinant lattice are finitely generated.
Locator: `Coordinates.coefficientSubmodule_fg`, `ModelLattice.detLattice_fg`. -/
theorem coefficientSubmodule_detLattice_fg (G : GroupModel E L) (hdim : E.dim = 1)
    (η : G.hodgeSpace 1) (hη : η ≠ 0) :
    (coefficientSubmodule (G.detLattice 1) η).FG :=
  coefficientSubmodule_fg (finrank_hodgeSpace_one_of_dim_one G hdim) η hη _ (detLattice_fg G 1)

/-- THEOREM. The coefficients of the original determinant lattice are nonzero.
Locator: `Coordinates.coefficientSubmodule_ne_bot`, `ModelLattice.detLattice_one_ne_bot`. -/
theorem coefficientSubmodule_detLattice_ne_bot (G : GroupModel E L) (hdim : E.dim = 1)
    (η : G.hodgeSpace 1) (hη : η ≠ 0) : coefficientSubmodule (G.detLattice 1) η ≠ ⊥ :=
  coefficientSubmodule_ne_bot (finrank_hodgeSpace_one_of_dim_one G hdim) η hη _
    (detLattice_one_ne_bot G hdim)

/-- THEOREM. The coefficient submodule spans the field over itself.
Locator: `Coordinates.submodule_spans_of_ne_bot`, `coefficientSubmodule_detLattice_ne_bot`. -/
theorem coefficientSubmodule_detLattice_spans (G : GroupModel E L) (hdim : E.dim = 1)
    (η : G.hodgeSpace 1) (hη : η ≠ 0) :
    Submodule.span L (coefficientSubmodule (G.detLattice 1) η : Set L) = ⊤ :=
  submodule_spans_of_ne_bot _ (coefficientSubmodule_detLattice_ne_bot G hdim η hη)

/-- THEOREM. A common nonzero denominator makes all coefficients integral.
Locator: Mathlib, `FractionalIdeal.isFractional_of_fg`; `coefficientSubmodule_detLattice_fg`. -/
theorem coefficientSubmodule_detLattice_isFractional (G : GroupModel E L)
    (hdim : E.dim = 1) (η : G.hodgeSpace 1) (hη : η ≠ 0) :
    IsFractional (nonZeroDivisors (𝓞 L)) (coefficientSubmodule (G.detLattice 1) η) :=
  FractionalIdeal.isFractional_of_fg (coefficientSubmodule_detLattice_fg G hdim η hη)

/-- DEFINITION. The genuine fractional ideal with the stipulated coefficient submodule.
Locator: Mathlib, `FractionalIdeal`; `coefficientSubmodule_detLattice_isFractional`. -/
def coefficientFractionalIdeal (G : GroupModel E L) (hdim : E.dim = 1)
    (η : G.hodgeSpace 1) (hη : η ≠ 0) : FractionalIdeal (nonZeroDivisors (𝓞 L)) L :=
  ⟨coefficientSubmodule (G.detLattice 1) η,
    coefficientSubmodule_detLattice_isFractional G hdim η hη⟩

/-- THEOREM. Bundling does not change the coefficient submodule.
Locator: `coefficientFractionalIdeal`. -/
@[simp] theorem coefficientFractionalIdeal_coe (G : GroupModel E L) (hdim : E.dim = 1)
    (η : G.hodgeSpace 1) (hη : η ≠ 0) :
    (coefficientFractionalIdeal G hdim η hη : Submodule (𝓞 L) L) =
      coefficientSubmodule (G.detLattice 1) η := rfl

/-- THEOREM. The bundled fractional ideal is nonzero.
Locator: Mathlib, `FractionalIdeal.coeToSubmodule_ne_bot`;
`coefficientSubmodule_detLattice_ne_bot`. -/
theorem coefficientFractionalIdeal_ne_zero (G : GroupModel E L) (hdim : E.dim = 1)
    (η : G.hodgeSpace 1) (hη : η ≠ 0) : coefficientFractionalIdeal G hdim η hη ≠ 0 :=
  FractionalIdeal.coeToSubmodule_ne_bot.mp (coefficientSubmodule_detLattice_ne_bot G hdim η hη)

/-- DEFINITION. The exact dictionary from the model's original `omega` to its coefficients.
Locator: `ModelLattice.omegaDetEquiv`, `Coordinates.coefficientEquiv`. -/
def omegaCoefficientEquiv (G : GroupModel E L) (hdim : E.dim = 1)
    (η : G.hodgeSpace 1) (hη : η ≠ 0) :
    G.omega ≃ₗ[𝓞 L] coefficientSubmodule (G.detLattice 1) η :=
  (omegaDetEquiv G).trans
    (coefficientEquiv (finrank_hodgeSpace_one_of_dim_one G hdim) η hη (G.detLattice 1)).symm

/-- THEOREM. The dictionary gives the coefficient of the natural first wedge, without rescaling.
Locator: `omegaCoefficientEquiv`, `Coordinates.coefficientEquiv_apply`. -/
theorem omegaCoefficientEquiv_spec (G : GroupModel E L) (hdim : E.dim = 1)
    (η : G.hodgeSpace 1) (hη : η ≠ 0) (x : G.omega) :
    (omegaCoefficientEquiv G hdim η hη x : L) • η = oneHodgeMap G x := by
  have h := coefficientEquiv_apply (finrank_hodgeSpace_one_of_dim_one G hdim) η hη
    (G.detLattice 1) (omegaCoefficientEquiv G hdim η hη x)
  change (coefficientEquiv (finrank_hodgeSpace_one_of_dim_one G hdim) η hη (G.detLattice 1)
    ((coefficientEquiv (finrank_hodgeSpace_one_of_dim_one G hdim) η hη (G.detLattice 1)).symm
      (omegaDetEquiv G x)) : G.hodgeSpace 1) = _ at h
  rw [LinearEquiv.apply_symm_apply] at h
  exact h.symm

/-- THEOREM. The original section index equals the coefficient section index for every scalar.
Locator: `Coordinates.secIndex_coordinate`, `finrank_hodgeSpace_one_of_dim_one`. -/
theorem secIndex_detLattice_coordinate (G : GroupModel E L) (hdim : E.dim = 1)
    (η : G.hodgeSpace 1) (hη : η ≠ 0) (a : L) :
    secIndex (G.detLattice 1) (a • η) = secIndex (coefficientSubmodule (G.detLattice 1) η) a :=
  secIndex_coordinate (finrank_hodgeSpace_one_of_dim_one G hdim) η hη _ a

/-- THEOREM. The relative index is oriented from the scalar section into the coefficient lattice.
Locator: `HodgeData.secIndex`, `secIndex_detLattice_coordinate`. -/
theorem secIndex_detLattice_relIndex (G : GroupModel E L) (hdim : E.dim = 1)
    (η : G.hodgeSpace 1) (hη : η ≠ 0) (a : L) :
    secIndex (G.detLattice 1) (a • η) = (Submodule.span (𝓞 L) {a}).toAddSubgroup.relIndex
      (coefficientSubmodule (G.detLattice 1) η).toAddSubgroup :=
  secIndex_detLattice_coordinate G hdim η hη a

/-- THEOREM. For a nonzero integral section, index times fractional-ideal norm is scalar norm.
Locator: `IdealLines.secIndex_mul_absNorm`, `secIndex_detLattice_coordinate`. -/
theorem secIndex_detLattice_mul_absNorm (G : GroupModel E L) (hdim : E.dim = 1)
    (η : G.hodgeSpace 1) (hη : η ≠ 0) {a : L}
    (ha : a ∈ coefficientSubmodule (G.detLattice 1) η) (ha0 : a ≠ 0) :
    (secIndex (G.detLattice 1) (a • η) : ℚ) *
      FractionalIdeal.absNorm (coefficientFractionalIdeal G hdim η hη) = |Algebra.norm ℚ a| := by
  rw [secIndex_detLattice_coordinate G hdim η hη]
  exact secIndex_mul_absNorm (coefficientFractionalIdeal G hdim η hη) ha ha0

/-- THEOREM. The coefficient fractional ideal has nonzero absolute norm.
Locator: Mathlib, `FractionalIdeal.absNorm_eq_zero_iff`; `coefficientFractionalIdeal_ne_zero`. -/
theorem coefficientFractionalIdeal_absNorm_ne_zero (G : GroupModel E L) (hdim : E.dim = 1)
    (η : G.hodgeSpace 1) (hη : η ≠ 0) :
    FractionalIdeal.absNorm (coefficientFractionalIdeal G hdim η hη) ≠ 0 :=
  FractionalIdeal.absNorm_eq_zero_iff.not.mpr (coefficientFractionalIdeal_ne_zero G hdim η hη)

/-- THEOREM. The original index is scalar norm divided by coefficient-ideal norm.
Locator: `secIndex_detLattice_mul_absNorm`, `coefficientFractionalIdeal_absNorm_ne_zero`. -/
theorem secIndex_detLattice_eq_norm_div (G : GroupModel E L) (hdim : E.dim = 1)
    (η : G.hodgeSpace 1) (hη : η ≠ 0) {a : L}
    (ha : a ∈ coefficientSubmodule (G.detLattice 1) η) (ha0 : a ≠ 0) :
    (secIndex (G.detLattice 1) (a • η) : ℚ) =
      |Algebra.norm ℚ a| / FractionalIdeal.absNorm (coefficientFractionalIdeal G hdim η hη) :=
  (eq_div_iff (coefficientFractionalIdeal_absNorm_ne_zero G hdim η hη)).mpr
    (secIndex_detLattice_mul_absNorm G hdim η hη ha ha0)

/-- THEOREM. Every nonzero coefficient belonging to the ideal defines a finite-index section.
Locator: `secIndex_detLattice_mul_absNorm`, Mathlib, `Algebra.norm_ne_zero_iff`. -/
theorem secIndex_detLattice_ne_zero (G : GroupModel E L) (hdim : E.dim = 1)
    (η : G.hodgeSpace 1) (hη : η ≠ 0) {a : L}
    (ha : a ∈ coefficientSubmodule (G.detLattice 1) η) (ha0 : a ≠ 0) :
    secIndex (G.detLattice 1) (a • η) ≠ 0 := by
  intro hzero
  have h := secIndex_detLattice_mul_absNorm G hdim η hη ha ha0
  rw [hzero, Nat.cast_zero, zero_mul] at h
  exact (Algebra.norm_ne_zero_iff.mpr ha0) (abs_eq_zero.mp h.symm)

/-- THEOREM. Integral rescaling multiplies the index, in the original orientation.
Locator: `HodgeData.secIndex_smul`, Mathlib, `smul_assoc`. -/
theorem secIndex_detLattice_integral_smul (G : GroupModel E L)
    (η : G.hodgeSpace 1) (hη : η ≠ 0) {a : L}
    (ha : a ∈ coefficientSubmodule (G.detLattice 1) η) (ha0 : a ≠ 0) (r : 𝓞 L) :
    secIndex (G.detLattice 1) ((r • a) • η) =
      (Algebra.norm ℤ r).natAbs * secIndex (G.detLattice 1) (a • η) := by
  rw [smul_assoc]
  exact secIndex_smul (G.detLattice 1) ha (smul_ne_zero ha0 hη) r

end ZInQ.Contrib.RC53Assist.HodgeLatticeIdeal
