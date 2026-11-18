import ZInQKernel.Contrib.OneProof.ManuscriptPole.GaloisCoefficients
import ZInQKernel.Contrib.OneProof.ManuscriptPole.GeometricTwoDivision
import ZInQKernel.Contrib.TauCeti.RepresentationTheory.Homological.ContCohomology.LowDegree
import ZInQKernel.Contrib.TauCeti.RepresentationTheory.Homological.ContCohomology.SmoothDiscrete.Basic
import ZInQKernel.Contrib.TauCeti.RepresentationTheory.Homological.ContCohomology.CohomologyComparison
import Mathlib.Tactic.Abel

/-!
# Rational Kummer cocycles on the manuscript elliptic curve

Rational points embed by their actual field map into the existing geometric
point group over the one algebraic closure of the rationals. The embedded
points are fixed by the rational Galois action.

A geometric half defines the crossed homomorphism sending an automorphism
to its displacement of that half. Its values lie in the actual doubling
kernel, and continuity follows from the point action and its discrete
coefficient topology. Two halves differ by a genuine two-torsion point,
so their cocycles differ by the corresponding coboundary.

The class is read in continuous degree-one cohomology of the existing
finite coefficient representation. Only rational Kummer cocycles and
independence of the geometric half are treated. No rational division,
local or global Selmer group, rank or restricted converse is asserted.
-/

set_option autoImplicit false

open scoped Classical

noncomputable section

namespace ZInQ.Contrib.OneProof.ManuscriptPole.KummerCocycle

open ZInQ.Contrib.OneProof.ManuscriptPole.GaloisCoefficients

private theorem rationalAlgHom_comp (sigma : GaloisGroup) :
    sigma.toAlgHom.comp (Algebra.ofId ℚ Qbar) = Algebra.ofId ℚ Qbar := by
  apply AlgHom.ext
  intro q
  change sigma.toAlgHom (algebraMap ℚ Qbar q) = algebraMap ℚ Qbar q
  exact sigma.toAlgHom.commutes q

/-- The rational point map is the actual map on points induced by the rational algebra map. -/
def rationalPointEmbedding (ell : ℚ) :
    (ZInQ.Manuscript.curve ell).toAffine.Point →+ GeometricPoints ell :=
  WeierstrassCurve.Affine.Point.map
    (R := ℚ) (S := ℚ) (F := ℚ) (K := Qbar)
    (W' := (ZInQ.Manuscript.curve ell).toAffine) (Algebra.ofId ℚ Qbar)

/-- The actual rational point map is injective. -/
theorem rationalPointEmbedding_injective (ell : ℚ) :
    Function.Injective (rationalPointEmbedding ell) :=
  WeierstrassCurve.Affine.Point.map_injective
    (R := ℚ) (S := ℚ) (F := ℚ) (K := Qbar)
    (W' := (ZInQ.Manuscript.curve ell).toAffine) (Algebra.ofId ℚ Qbar)

/-- Galois fixedness is proved from composition of the actual rational point maps. -/
theorem rationalPointEmbedding_galoisFixed (ell : ℚ) (sigma : GaloisGroup)
    (P : (ZInQ.Manuscript.curve ell).toAffine.Point) :
    geometricPointMap ell sigma (rationalPointEmbedding ell P) =
      rationalPointEmbedding ell P := by
  exact galois_fixes_rational_baseChange ell sigma P

/-- The same fixedness statement uses the existing canonical geometric action. -/
theorem rationalPointEmbedding_smul (ell : ℚ) (sigma : GaloisGroup)
    (P : (ZInQ.Manuscript.curve ell).toAffine.Point) :
    sigma • (rationalPointEmbedding ell P) = rationalPointEmbedding ell P := by
  rw [geometric_galois_smul, rationalPointEmbedding_galoisFixed]

/-- A geometric half is selected from the geometric doubling theorem, not supplied by the caller. -/
def geometricHalf (ell : ℚ) (hell : ell ≠ 0)
    (P : (ZInQ.Manuscript.curve ell).toAffine.Point) : GeometricPoints ell :=
  Classical.choose
    (GeometricTwoDivision.geometricTwoSurjective ell hell (rationalPointEmbedding ell P))

/-- The selected half doubles to the embedded rational input. -/
theorem geometricHalf_spec (ell : ℚ) (hell : ell ≠ 0)
    (P : (ZInQ.Manuscript.curve ell).toAffine.Point) :
    (2 : ℕ) • geometricHalf ell hell P = rationalPointEmbedding ell P :=
  Classical.choose_spec
    (GeometricTwoDivision.geometricTwoSurjective ell hell (rationalPointEmbedding ell P))

private theorem difference_mem_twoTorsion (ell : ℚ)
    (P : (ZInQ.Manuscript.curve ell).toAffine.Point) (Q : GeometricPoints ell)
    (hQ : (2 : ℕ) • Q = rationalPointEmbedding ell P) (sigma : GaloisGroup) :
    geometricPointMap ell sigma Q - Q ∈ twoPowerTorsion ell 1 := by
  rw [mem_twoPowerTorsion, pow_one, nsmul_sub, ← map_nsmul, hQ,
    rationalPointEmbedding_galoisFixed, sub_self]

/-- The actual two-torsion-valued continuous cocycle attached to a geometric half. -/
def kummerCocycleForHalf (ell : ℚ) (hell : ell ≠ 0)
    (P : (ZInQ.Manuscript.curve ell).toAffine.Point) (Q : GeometricPoints ell)
    (hQ : (2 : ℕ) • Q = rationalPointEmbedding ell P) :
    TauCeti.ContCohomology.Z1 GaloisGroup (twoPowerTorsion ell 1) := by
  let c : GaloisGroup → twoPowerTorsion ell 1 := fun sigma =>
    ⟨geometricPointMap ell sigma Q - Q, difference_mem_twoTorsion ell P Q hQ sigma⟩
  refine ⟨c, ?_⟩
  exact TauCeti.ContCohomology.mem_Z1_of_injective_comp_eq_d0
    (φ := twoPowerToGeometric ell 1) (b := Q) (a := c)
    (twoPowerToGeometric_injective ell 1)
    (fun sigma T => twoPowerToGeometric_galois ell 1 sigma T)
    (fun _ => rfl)

/-- The cocycle's values are the literal displacements of the same geometric half. -/
@[simp] theorem kummerCocycleForHalf_apply (ell : ℚ) (hell : ell ≠ 0)
    (P : (ZInQ.Manuscript.curve ell).toAffine.Point) (Q : GeometricPoints ell)
    (hQ : (2 : ℕ) • Q = rationalPointEmbedding ell P) (sigma : GaloisGroup) :
    (((kummerCocycleForHalf ell hell P Q hQ : GaloisGroup → twoPowerTorsion ell 1)
      sigma : twoPowerTorsion ell 1) : GeometricPoints ell) =
      geometricPointMap ell sigma Q - Q := rfl

/-- Continuity into the discrete kernel is derived, not an input hypothesis. -/
theorem kummerCocycleForHalf_continuous (ell : ℚ) (hell : ell ≠ 0)
    (P : (ZInQ.Manuscript.curve ell).toAffine.Point) (Q : GeometricPoints ell)
    (hQ : (2 : ℕ) • Q = rationalPointEmbedding ell P) :
    Continuous (kummerCocycleForHalf ell hell P Q hQ :
      GaloisGroup → twoPowerTorsion ell 1) :=
  (TauCeti.ContCohomology.mem_Z1_iff.mp (kummerCocycleForHalf ell hell P Q hQ).property).1

/-- The cocycle identity uses the actual action on the doubling kernel. -/
theorem kummerCocycleForHalf_mul (ell : ℚ) (hell : ell ≠ 0)
    (P : (ZInQ.Manuscript.curve ell).toAffine.Point) (Q : GeometricPoints ell)
    (hQ : (2 : ℕ) • Q = rationalPointEmbedding ell P) (sigma tau : GaloisGroup) :
    (kummerCocycleForHalf ell hell P Q hQ : GaloisGroup → twoPowerTorsion ell 1)
        (sigma * tau) =
      sigma • (kummerCocycleForHalf ell hell P Q hQ :
        GaloisGroup → twoPowerTorsion ell 1) tau +
      (kummerCocycleForHalf ell hell P Q hQ : GaloisGroup → twoPowerTorsion ell 1) sigma :=
  (TauCeti.ContCohomology.mem_Z1_iff.mp
    (kummerCocycleForHalf ell hell P Q hQ).property).2 sigma tau

/-- The rational Kummer cocycle has no externally supplied lift or output premise. -/
def kummerCocycle (ell : ℚ) (hell : ell ≠ 0)
    (P : (ZInQ.Manuscript.curve ell).toAffine.Point) :
    TauCeti.ContCohomology.Z1 GaloisGroup (twoPowerTorsion ell 1) :=
  kummerCocycleForHalf ell hell P (geometricHalf ell hell P) (geometricHalf_spec ell hell P)

/-- The selected cocycle is the displacement of its internally selected geometric half. -/
@[simp] theorem kummerCocycle_apply (ell : ℚ) (hell : ell ≠ 0)
    (P : (ZInQ.Manuscript.curve ell).toAffine.Point) (sigma : GaloisGroup) :
    (((kummerCocycle ell hell P : GaloisGroup → twoPowerTorsion ell 1)
      sigma : twoPowerTorsion ell 1) : GeometricPoints ell) =
      geometricPointMap ell sigma (geometricHalf ell hell P) - geometricHalf ell hell P := rfl

/-- The rational Kummer cocycle is continuous with the existing discrete coefficient topology. -/
theorem kummerCocycle_continuous (ell : ℚ) (hell : ell ≠ 0)
    (P : (ZInQ.Manuscript.curve ell).toAffine.Point) :
    Continuous (kummerCocycle ell hell P : GaloisGroup → twoPowerTorsion ell 1) :=
  kummerCocycleForHalf_continuous ell hell P (geometricHalf ell hell P)
    (geometricHalf_spec ell hell P)

/-- The rational Kummer cocycle satisfies the genuine crossed-homomorphism identity. -/
theorem kummerCocycle_mul (ell : ℚ) (hell : ell ≠ 0)
    (P : (ZInQ.Manuscript.curve ell).toAffine.Point) (sigma tau : GaloisGroup) :
    (kummerCocycle ell hell P : GaloisGroup → twoPowerTorsion ell 1) (sigma * tau) =
      sigma • (kummerCocycle ell hell P : GaloisGroup → twoPowerTorsion ell 1) tau +
      (kummerCocycle ell hell P : GaloisGroup → twoPowerTorsion ell 1) sigma :=
  kummerCocycleForHalf_mul ell hell P (geometricHalf ell hell P)
    (geometricHalf_spec ell hell P) sigma tau

/-- Every value is killed by actual doubling in the geometric point group. -/
theorem kummerCocycle_two_nsmul (ell : ℚ) (hell : ell ≠ 0)
    (P : (ZInQ.Manuscript.curve ell).toAffine.Point) (sigma : GaloisGroup) :
    (2 : ℕ) • (((kummerCocycle ell hell P : GaloisGroup → twoPowerTorsion ell 1)
      sigma : twoPowerTorsion ell 1) : GeometricPoints ell) = 0 := by
  have h := ((kummerCocycle ell hell P : GaloisGroup → twoPowerTorsion ell 1) sigma).property
  simpa only [mem_twoPowerTorsion, pow_one] using h

private theorem halfDifference_mem (ell : ℚ)
    (P : (ZInQ.Manuscript.curve ell).toAffine.Point) (Q Q' : GeometricPoints ell)
    (hQ : (2 : ℕ) • Q = rationalPointEmbedding ell P)
    (hQ' : (2 : ℕ) • Q' = rationalPointEmbedding ell P) :
    Q - Q' ∈ twoPowerTorsion ell 1 := by
  rw [mem_twoPowerTorsion, pow_one, nsmul_sub, hQ, hQ', sub_self]

/-- Two genuine halves yield cocycles differing by the coboundary of their two-torsion difference. -/
theorem kummerCocycleForHalf_sub_d0 (ell : ℚ) (hell : ell ≠ 0)
    (P : (ZInQ.Manuscript.curve ell).toAffine.Point) (Q Q' : GeometricPoints ell)
    (hQ : (2 : ℕ) • Q = rationalPointEmbedding ell P)
    (hQ' : (2 : ℕ) • Q' = rationalPointEmbedding ell P) :
    ∃ T : twoPowerTorsion ell 1,
      (T : GeometricPoints ell) = Q - Q' ∧
      (kummerCocycleForHalf ell hell P Q hQ : GaloisGroup → twoPowerTorsion ell 1) -
        (kummerCocycleForHalf ell hell P Q' hQ' : GaloisGroup → twoPowerTorsion ell 1) =
      TauCeti.ContCohomology.d0 GaloisGroup (twoPowerTorsion ell 1) T := by
  refine ⟨⟨Q - Q', halfDifference_mem ell P Q Q' hQ hQ'⟩, rfl, ?_⟩
  funext sigma
  apply Subtype.ext
  change (geometricPointMap ell sigma Q - Q) - (geometricPointMap ell sigma Q' - Q') =
    geometricPointMap ell sigma (Q - Q') - (Q - Q')
  rw [map_sub]
  abel

section CanonicalClasses

attribute [local instance] TopRep.distribMulAction

local instance twoTorsionTopRepDiscrete (ell : ℚ) (hell : ell ≠ 0) :
    DiscreteTopology (twoPowerTopRep ell hell 1).V :=
  inferInstanceAs (DiscreteTopology (twoPowerTorsion ell 1))

private theorem twoTorsionTopRep_smooth (ell : ℚ) (hell : ell ≠ 0) :
    TauCeti.IsSmoothDiscrete ℤ (twoPowerTopRep ell hell 1) :=
  ⟨inferInstance, twoPowerTopRep_operator_stabilizer_isOpen ell hell 1⟩

local instance twoTorsionTopRepContinuous (ell : ℚ) (hell : ell ≠ 0) :
    ContinuousSMul GaloisGroup (twoPowerTopRep ell hell 1).V :=
  TauCeti.IsSmoothDiscrete.continuousSMul (twoTorsionTopRep_smooth ell hell)

/-- The same displacements form a cocycle for the existing finite representation's derived action. -/
def packagedKummerCocycleForHalf (ell : ℚ) (hell : ell ≠ 0)
    (P : (ZInQ.Manuscript.curve ell).toAffine.Point) (Q : GeometricPoints ell)
    (hQ : (2 : ℕ) • Q = rationalPointEmbedding ell P) :
    TauCeti.ContCohomology.Z1 GaloisGroup (twoPowerTopRep ell hell 1).V := by
  let c : GaloisGroup → (twoPowerTopRep ell hell 1).V := fun sigma =>
    (⟨geometricPointMap ell sigma Q - Q,
      difference_mem_twoTorsion ell P Q hQ sigma⟩ : twoPowerTorsion ell 1)
  let phi : (twoPowerTopRep ell hell 1).V →+ GeometricPoints ell :=
    twoPowerToGeometric ell 1
  refine ⟨c, ?_⟩
  refine TauCeti.ContCohomology.mem_Z1_of_injective_comp_eq_d0
    (G := GaloisGroup) (A := (twoPowerTopRep ell hell 1).V) (B := GeometricPoints ell)
    (φ := phi) (a := c) (b := Q) (twoPowerToGeometric_injective ell 1) ?_ ?_
  · intro sigma T
    exact twoPowerTopRep_operator_coe ell hell 1 sigma T
  · intro sigma
    rfl

/-- The packaged cocycle has the same actual two-torsion displacements under the coefficient inclusion. -/
@[simp] theorem packagedKummerCocycleForHalf_apply (ell : ℚ) (hell : ell ≠ 0)
    (P : (ZInQ.Manuscript.curve ell).toAffine.Point) (Q : GeometricPoints ell)
    (hQ : (2 : ℕ) • Q = rationalPointEmbedding ell P) (sigma : GaloisGroup) :
    twoPowerToGeometric ell 1
      ((packagedKummerCocycleForHalf ell hell P Q hQ :
        GaloisGroup → (twoPowerTopRep ell hell 1).V) sigma) =
      geometricPointMap ell sigma Q - Q := rfl

/-- The class lies in continuous cohomology of the actual finite coefficient representation. -/
def kummerClassForHalf (ell : ℚ) (hell : ell ≠ 0)
    (P : (ZInQ.Manuscript.curve ell).toAffine.Point) (Q : GeometricPoints ell)
    (hQ : (2 : ℕ) • Q = rationalPointEmbedding ell P) :
    continuousCohomology 1 (twoPowerTopRep ell hell 1) :=
  (twoPowerTopRep ell hell 1).explicitH1AddEquivContinuousCohomologyOfDiscrete
    (packagedKummerCocycleForHalf ell hell P Q hQ :
      TauCeti.ContCohomology.H1 GaloisGroup (twoPowerTopRep ell hell 1).V)

/-- The canonical continuous-cohomology class is independent of the chosen geometric half. -/
theorem kummerClassForHalf_independent (ell : ℚ) (hell : ell ≠ 0)
    (P : (ZInQ.Manuscript.curve ell).toAffine.Point) (Q Q' : GeometricPoints ell)
    (hQ : (2 : ℕ) • Q = rationalPointEmbedding ell P)
    (hQ' : (2 : ℕ) • Q' = rationalPointEmbedding ell P) :
    kummerClassForHalf ell hell P Q hQ = kummerClassForHalf ell hell P Q' hQ' := by
  let X := twoPowerTopRep ell hell 1
  let c : TauCeti.ContCohomology.Z1 GaloisGroup X.V :=
    packagedKummerCocycleForHalf ell hell P Q hQ
  let c' : TauCeti.ContCohomology.Z1 GaloisGroup X.V :=
    packagedKummerCocycleForHalf ell hell P Q' hQ'
  let T : X.V := (⟨Q - Q', halfDifference_mem ell P Q Q' hQ hQ'⟩ : twoPowerTorsion ell 1)
  let phi : X.V →+ GeometricPoints ell := twoPowerToGeometric ell 1
  have hinj : Function.Injective phi := twoPowerToGeometric_injective ell 1
  have heq (sigma : GaloisGroup) (U : X.V) : phi (sigma • U) = sigma • phi U := by
    exact twoPowerTopRep_operator_coe ell hell 1 sigma U
  have hdiff : (c : GaloisGroup → X.V) - (c' : GaloisGroup → X.V) =
      TauCeti.ContCohomology.d0 GaloisGroup X.V T := by
    funext sigma
    apply hinj
    change phi ((c : GaloisGroup → X.V) sigma - (c' : GaloisGroup → X.V) sigma) =
      phi (sigma • T - T)
    rw [map_sub, map_sub, heq]
    change (geometricPointMap ell sigma Q - Q) - (geometricPointMap ell sigma Q' - Q') =
      geometricPointMap ell sigma (Q - Q') - (Q - Q')
    rw [map_sub]
    abel
  have hclass : (c : TauCeti.ContCohomology.H1 GaloisGroup X.V) =
      (c' : TauCeti.ContCohomology.H1 GaloisGroup X.V) := by
    apply TauCeti.ContCohomology.H1pi_eq_iff.mpr
    rw [hdiff]
    exact TauCeti.ContCohomology.d0_mem_B1 T
  change X.explicitH1AddEquivContinuousCohomologyOfDiscrete
      (c : TauCeti.ContCohomology.H1 GaloisGroup X.V) =
    X.explicitH1AddEquivContinuousCohomologyOfDiscrete
      (c' : TauCeti.ContCohomology.H1 GaloisGroup X.V)
  exact congrArg X.explicitH1AddEquivContinuousCohomologyOfDiscrete hclass

/-- The rational Kummer class uses an internally selected geometric half. -/
def kummerClass (ell : ℚ) (hell : ell ≠ 0)
    (P : (ZInQ.Manuscript.curve ell).toAffine.Point) :
    continuousCohomology 1 (twoPowerTopRep ell hell 1) :=
  kummerClassForHalf ell hell P (geometricHalf ell hell P) (geometricHalf_spec ell hell P)

/-- Any genuine half of the embedded rational point represents the same canonical class. -/
theorem kummerClass_eq_of_half (ell : ℚ) (hell : ell ≠ 0)
    (P : (ZInQ.Manuscript.curve ell).toAffine.Point) (Q : GeometricPoints ell)
    (hQ : (2 : ℕ) • Q = rationalPointEmbedding ell P) :
    kummerClass ell hell P = kummerClassForHalf ell hell P Q hQ :=
  kummerClassForHalf_independent ell hell P (geometricHalf ell hell P) Q
    (geometricHalf_spec ell hell P) hQ

end CanonicalClasses

end ZInQ.Contrib.OneProof.ManuscriptPole.KummerCocycle
