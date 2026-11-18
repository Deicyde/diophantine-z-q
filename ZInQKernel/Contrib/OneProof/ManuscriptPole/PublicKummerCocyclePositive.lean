import ZInQKernel.Contrib.OneProof.ManuscriptPole.KummerCocycle

/-!
# Public rational Kummer consumers

These consumers retain the rational input, the actual geometric point group,
its doubling kernel and the canonical continuous cohomology representation.
Geometric halves are supplied internally by the public constructors. The
representative statements retain precisely their genuine half equations.
-/

set_option autoImplicit false
open scoped Classical
open ZInQ.Contrib.OneProof.ManuscriptPole.GaloisCoefficients
open ZInQ.Contrib.OneProof.ManuscriptPole.KummerCocycle

noncomputable section

set_option pp.all true
set_option pp.proofs true
set_option pp.universes true
set_option pp.fullNames true

/- Closed public signature: rationalPointEmbedding. -/
#check @ZInQ.Contrib.OneProof.ManuscriptPole.KummerCocycle.rationalPointEmbedding
example : ∀ (ell : ℚ),
    (ZInQ.Manuscript.curve ell).toAffine.Point →+ GeometricPoints ell :=
  @ZInQ.Contrib.OneProof.ManuscriptPole.KummerCocycle.rationalPointEmbedding
#print axioms ZInQ.Contrib.OneProof.ManuscriptPole.KummerCocycle.rationalPointEmbedding

/- Closed public signature: rationalPointEmbedding_injective. -/
#check @ZInQ.Contrib.OneProof.ManuscriptPole.KummerCocycle.rationalPointEmbedding_injective
example : ∀ (ell : ℚ), Function.Injective (rationalPointEmbedding ell) :=
  @ZInQ.Contrib.OneProof.ManuscriptPole.KummerCocycle.rationalPointEmbedding_injective
#print axioms ZInQ.Contrib.OneProof.ManuscriptPole.KummerCocycle.rationalPointEmbedding_injective

/- Closed public signature: rationalPointEmbedding_galoisFixed. -/
#check @ZInQ.Contrib.OneProof.ManuscriptPole.KummerCocycle.rationalPointEmbedding_galoisFixed
example : ∀ (ell : ℚ) (sigma : GaloisGroup)
    (P : (ZInQ.Manuscript.curve ell).toAffine.Point),
    geometricPointMap ell sigma (rationalPointEmbedding ell P) = rationalPointEmbedding ell P :=
  @ZInQ.Contrib.OneProof.ManuscriptPole.KummerCocycle.rationalPointEmbedding_galoisFixed
#print axioms ZInQ.Contrib.OneProof.ManuscriptPole.KummerCocycle.rationalPointEmbedding_galoisFixed

/- Closed public signature: rationalPointEmbedding_smul. -/
#check @ZInQ.Contrib.OneProof.ManuscriptPole.KummerCocycle.rationalPointEmbedding_smul
example : ∀ (ell : ℚ) (sigma : GaloisGroup)
    (P : (ZInQ.Manuscript.curve ell).toAffine.Point),
    sigma • (rationalPointEmbedding ell P) = rationalPointEmbedding ell P :=
  @ZInQ.Contrib.OneProof.ManuscriptPole.KummerCocycle.rationalPointEmbedding_smul
#print axioms ZInQ.Contrib.OneProof.ManuscriptPole.KummerCocycle.rationalPointEmbedding_smul

/- Closed public signature: geometricHalf. -/
#check @ZInQ.Contrib.OneProof.ManuscriptPole.KummerCocycle.geometricHalf
example : ∀ (ell : ℚ) (hell : ell ≠ 0)
    (P : (ZInQ.Manuscript.curve ell).toAffine.Point), GeometricPoints ell :=
  @ZInQ.Contrib.OneProof.ManuscriptPole.KummerCocycle.geometricHalf
#print axioms ZInQ.Contrib.OneProof.ManuscriptPole.KummerCocycle.geometricHalf

/- Closed public signature: geometricHalf_spec. -/
#check @ZInQ.Contrib.OneProof.ManuscriptPole.KummerCocycle.geometricHalf_spec
example : ∀ (ell : ℚ) (hell : ell ≠ 0)
    (P : (ZInQ.Manuscript.curve ell).toAffine.Point),
    (2 : ℕ) • geometricHalf ell hell P = rationalPointEmbedding ell P :=
  @ZInQ.Contrib.OneProof.ManuscriptPole.KummerCocycle.geometricHalf_spec
#print axioms ZInQ.Contrib.OneProof.ManuscriptPole.KummerCocycle.geometricHalf_spec

/- Closed public signature: kummerCocycleForHalf. -/
#check @ZInQ.Contrib.OneProof.ManuscriptPole.KummerCocycle.kummerCocycleForHalf
example : ∀ (ell : ℚ) (hell : ell ≠ 0)
    (P : (ZInQ.Manuscript.curve ell).toAffine.Point) (Q : GeometricPoints ell)
    (hQ : (2 : ℕ) • Q = rationalPointEmbedding ell P),
    TauCeti.ContCohomology.Z1 GaloisGroup (twoPowerTorsion ell 1) :=
  @ZInQ.Contrib.OneProof.ManuscriptPole.KummerCocycle.kummerCocycleForHalf
#print axioms ZInQ.Contrib.OneProof.ManuscriptPole.KummerCocycle.kummerCocycleForHalf

/- Closed public signature: kummerCocycleForHalf_apply. -/
#check @ZInQ.Contrib.OneProof.ManuscriptPole.KummerCocycle.kummerCocycleForHalf_apply
example : ∀ (ell : ℚ) (hell : ell ≠ 0)
    (P : (ZInQ.Manuscript.curve ell).toAffine.Point) (Q : GeometricPoints ell)
    (hQ : (2 : ℕ) • Q = rationalPointEmbedding ell P) (sigma : GaloisGroup),
    (((kummerCocycleForHalf ell hell P Q hQ : GaloisGroup → twoPowerTorsion ell 1)
      sigma : twoPowerTorsion ell 1) : GeometricPoints ell) =
      geometricPointMap ell sigma Q - Q :=
  @ZInQ.Contrib.OneProof.ManuscriptPole.KummerCocycle.kummerCocycleForHalf_apply
#print axioms ZInQ.Contrib.OneProof.ManuscriptPole.KummerCocycle.kummerCocycleForHalf_apply

/- Closed public signature: kummerCocycleForHalf_continuous. -/
#check @ZInQ.Contrib.OneProof.ManuscriptPole.KummerCocycle.kummerCocycleForHalf_continuous
example : ∀ (ell : ℚ) (hell : ell ≠ 0)
    (P : (ZInQ.Manuscript.curve ell).toAffine.Point) (Q : GeometricPoints ell)
    (hQ : (2 : ℕ) • Q = rationalPointEmbedding ell P),
    Continuous (kummerCocycleForHalf ell hell P Q hQ :
      GaloisGroup → twoPowerTorsion ell 1) :=
  @ZInQ.Contrib.OneProof.ManuscriptPole.KummerCocycle.kummerCocycleForHalf_continuous
#print axioms ZInQ.Contrib.OneProof.ManuscriptPole.KummerCocycle.kummerCocycleForHalf_continuous

/- Closed public signature: kummerCocycleForHalf_mul. -/
#check @ZInQ.Contrib.OneProof.ManuscriptPole.KummerCocycle.kummerCocycleForHalf_mul
example : ∀ (ell : ℚ) (hell : ell ≠ 0)
    (P : (ZInQ.Manuscript.curve ell).toAffine.Point) (Q : GeometricPoints ell)
    (hQ : (2 : ℕ) • Q = rationalPointEmbedding ell P) (sigma tau : GaloisGroup),
    (kummerCocycleForHalf ell hell P Q hQ : GaloisGroup → twoPowerTorsion ell 1)
        (sigma * tau) =
      sigma • (kummerCocycleForHalf ell hell P Q hQ :
        GaloisGroup → twoPowerTorsion ell 1) tau +
      (kummerCocycleForHalf ell hell P Q hQ : GaloisGroup → twoPowerTorsion ell 1) sigma :=
  @ZInQ.Contrib.OneProof.ManuscriptPole.KummerCocycle.kummerCocycleForHalf_mul
#print axioms ZInQ.Contrib.OneProof.ManuscriptPole.KummerCocycle.kummerCocycleForHalf_mul

/- Closed public signature: kummerCocycle. -/
#check @ZInQ.Contrib.OneProof.ManuscriptPole.KummerCocycle.kummerCocycle
example : ∀ (ell : ℚ) (hell : ell ≠ 0)
    (P : (ZInQ.Manuscript.curve ell).toAffine.Point),
    TauCeti.ContCohomology.Z1 GaloisGroup (twoPowerTorsion ell 1) :=
  @ZInQ.Contrib.OneProof.ManuscriptPole.KummerCocycle.kummerCocycle
#print axioms ZInQ.Contrib.OneProof.ManuscriptPole.KummerCocycle.kummerCocycle

/- Closed public signature: kummerCocycle_apply. -/
#check @ZInQ.Contrib.OneProof.ManuscriptPole.KummerCocycle.kummerCocycle_apply
example : ∀ (ell : ℚ) (hell : ell ≠ 0)
    (P : (ZInQ.Manuscript.curve ell).toAffine.Point) (sigma : GaloisGroup),
    (((kummerCocycle ell hell P : GaloisGroup → twoPowerTorsion ell 1)
      sigma : twoPowerTorsion ell 1) : GeometricPoints ell) =
      geometricPointMap ell sigma (geometricHalf ell hell P) - geometricHalf ell hell P :=
  @ZInQ.Contrib.OneProof.ManuscriptPole.KummerCocycle.kummerCocycle_apply
#print axioms ZInQ.Contrib.OneProof.ManuscriptPole.KummerCocycle.kummerCocycle_apply

/- Closed public signature: kummerCocycle_continuous. -/
#check @ZInQ.Contrib.OneProof.ManuscriptPole.KummerCocycle.kummerCocycle_continuous
example : ∀ (ell : ℚ) (hell : ell ≠ 0)
    (P : (ZInQ.Manuscript.curve ell).toAffine.Point),
    Continuous (kummerCocycle ell hell P : GaloisGroup → twoPowerTorsion ell 1) :=
  @ZInQ.Contrib.OneProof.ManuscriptPole.KummerCocycle.kummerCocycle_continuous
#print axioms ZInQ.Contrib.OneProof.ManuscriptPole.KummerCocycle.kummerCocycle_continuous

/- Closed public signature: kummerCocycle_mul. -/
#check @ZInQ.Contrib.OneProof.ManuscriptPole.KummerCocycle.kummerCocycle_mul
example : ∀ (ell : ℚ) (hell : ell ≠ 0)
    (P : (ZInQ.Manuscript.curve ell).toAffine.Point) (sigma tau : GaloisGroup),
    (kummerCocycle ell hell P : GaloisGroup → twoPowerTorsion ell 1) (sigma * tau) =
      sigma • (kummerCocycle ell hell P : GaloisGroup → twoPowerTorsion ell 1) tau +
      (kummerCocycle ell hell P : GaloisGroup → twoPowerTorsion ell 1) sigma :=
  @ZInQ.Contrib.OneProof.ManuscriptPole.KummerCocycle.kummerCocycle_mul
#print axioms ZInQ.Contrib.OneProof.ManuscriptPole.KummerCocycle.kummerCocycle_mul

/- Closed public signature: kummerCocycle_two_nsmul. -/
#check @ZInQ.Contrib.OneProof.ManuscriptPole.KummerCocycle.kummerCocycle_two_nsmul
example : ∀ (ell : ℚ) (hell : ell ≠ 0)
    (P : (ZInQ.Manuscript.curve ell).toAffine.Point) (sigma : GaloisGroup),
    (2 : ℕ) • (((kummerCocycle ell hell P : GaloisGroup → twoPowerTorsion ell 1)
      sigma : twoPowerTorsion ell 1) : GeometricPoints ell) = 0 :=
  @ZInQ.Contrib.OneProof.ManuscriptPole.KummerCocycle.kummerCocycle_two_nsmul
#print axioms ZInQ.Contrib.OneProof.ManuscriptPole.KummerCocycle.kummerCocycle_two_nsmul

/- Closed public signature: kummerCocycleForHalf_sub_d0. -/
#check @ZInQ.Contrib.OneProof.ManuscriptPole.KummerCocycle.kummerCocycleForHalf_sub_d0
example : ∀ (ell : ℚ) (hell : ell ≠ 0)
    (P : (ZInQ.Manuscript.curve ell).toAffine.Point) (Q Q' : GeometricPoints ell)
    (hQ : (2 : ℕ) • Q = rationalPointEmbedding ell P)
    (hQ' : (2 : ℕ) • Q' = rationalPointEmbedding ell P),
    ∃ T : twoPowerTorsion ell 1,
      (T : GeometricPoints ell) = Q - Q' ∧
      (kummerCocycleForHalf ell hell P Q hQ : GaloisGroup → twoPowerTorsion ell 1) -
        (kummerCocycleForHalf ell hell P Q' hQ' : GaloisGroup → twoPowerTorsion ell 1) =
      TauCeti.ContCohomology.d0 GaloisGroup (twoPowerTorsion ell 1) T :=
  @ZInQ.Contrib.OneProof.ManuscriptPole.KummerCocycle.kummerCocycleForHalf_sub_d0
#print axioms ZInQ.Contrib.OneProof.ManuscriptPole.KummerCocycle.kummerCocycleForHalf_sub_d0

/- Literal closure, carrier and rational fixedness. -/
example : Qbar = AlgebraicClosure ℚ := rfl
example (ell : ℚ) : GeometricPoints ell =
    ((ZInQ.Manuscript.curve ell).baseChange Qbar).toAffine.Point := rfl
example (ell : ℚ) (sigma : GaloisGroup)
    (P : (ZInQ.Manuscript.curve ell).toAffine.Point) :
    sigma • rationalPointEmbedding ell P = rationalPointEmbedding ell P :=
  rationalPointEmbedding_smul ell sigma P

/- Internal half and literal displacement, with no external lift premise. -/
example (ell : ℚ) (hell : ell ≠ 0)
    (P : (ZInQ.Manuscript.curve ell).toAffine.Point) :
    ∃ Q : GeometricPoints ell, (2 : ℕ) • Q = rationalPointEmbedding ell P :=
  ⟨geometricHalf ell hell P, geometricHalf_spec ell hell P⟩
example (ell : ℚ) (hell : ell ≠ 0)
    (P : (ZInQ.Manuscript.curve ell).toAffine.Point) (sigma : GaloisGroup) :
    (((kummerCocycle ell hell P : GaloisGroup → twoPowerTorsion ell 1)
      sigma : twoPowerTorsion ell 1) : GeometricPoints ell) =
      geometricPointMap ell sigma (geometricHalf ell hell P) - geometricHalf ell hell P :=
  kummerCocycle_apply ell hell P sigma
example (ell : ℚ) (hell : ell ≠ 0)
    (P : (ZInQ.Manuscript.curve ell).toAffine.Point) (sigma : GaloisGroup) :
    (2 : ℕ) • (((kummerCocycle ell hell P : GaloisGroup → twoPowerTorsion ell 1)
      sigma : twoPowerTorsion ell 1) : GeometricPoints ell) = 0 :=
  kummerCocycle_two_nsmul ell hell P sigma

/- The existing raw coefficient inclusion is equivariant and killed by two. -/
example (ell : ℚ) (sigma : GaloisGroup) (T : twoPowerTorsion ell 1) :
    twoPowerToGeometric ell 1 (sigma • T) = sigma • twoPowerToGeometric ell 1 T :=
  twoPowerToGeometric_galois ell 1 sigma T
example (ell : ℚ) (T : twoPowerTorsion ell 1) :
    (2 : ℕ) • (T : GeometricPoints ell) = 0 := by
  simpa only [pow_one] using (mem_twoPowerTorsion ell 1 (T : GeometricPoints ell)).mp T.property

section CanonicalConsumers

attribute [local instance] TopRep.distribMulAction

/- These properties are derived from the public coefficient representation. -/
local instance (ell : ℚ) (hell : ell ≠ 0) :
    DiscreteTopology (twoPowerTopRep ell hell 1).V :=
  inferInstanceAs (DiscreteTopology (twoPowerTorsion ell 1))

local instance (ell : ℚ) (hell : ell ≠ 0) :
    ContinuousSMul GaloisGroup (twoPowerTopRep ell hell 1).V :=
  TauCeti.IsSmoothDiscrete.continuousSMul
    (show TauCeti.IsSmoothDiscrete ℤ (twoPowerTopRep ell hell 1) from
      ⟨inferInstance, twoPowerTopRep_operator_stabilizer_isOpen ell hell 1⟩)

/- Closed public signature: packagedKummerCocycleForHalf. -/
#check @ZInQ.Contrib.OneProof.ManuscriptPole.KummerCocycle.packagedKummerCocycleForHalf
example : ∀ (ell : ℚ) (hell : ell ≠ 0)
    (P : (ZInQ.Manuscript.curve ell).toAffine.Point) (Q : GeometricPoints ell)
    (hQ : (2 : ℕ) • Q = rationalPointEmbedding ell P),
    TauCeti.ContCohomology.Z1 GaloisGroup (twoPowerTopRep ell hell 1).V :=
  @ZInQ.Contrib.OneProof.ManuscriptPole.KummerCocycle.packagedKummerCocycleForHalf
#print axioms ZInQ.Contrib.OneProof.ManuscriptPole.KummerCocycle.packagedKummerCocycleForHalf

/- Closed public signature: packagedKummerCocycleForHalf_apply. -/
#check @ZInQ.Contrib.OneProof.ManuscriptPole.KummerCocycle.packagedKummerCocycleForHalf_apply
example : ∀ (ell : ℚ) (hell : ell ≠ 0)
    (P : (ZInQ.Manuscript.curve ell).toAffine.Point) (Q : GeometricPoints ell)
    (hQ : (2 : ℕ) • Q = rationalPointEmbedding ell P) (sigma : GaloisGroup),
    twoPowerToGeometric ell 1
      ((packagedKummerCocycleForHalf ell hell P Q hQ :
        GaloisGroup → (twoPowerTopRep ell hell 1).V) sigma) =
      geometricPointMap ell sigma Q - Q :=
  @ZInQ.Contrib.OneProof.ManuscriptPole.KummerCocycle.packagedKummerCocycleForHalf_apply
#print axioms ZInQ.Contrib.OneProof.ManuscriptPole.KummerCocycle.packagedKummerCocycleForHalf_apply

/- Closed public signature: kummerClassForHalf. -/
#check @ZInQ.Contrib.OneProof.ManuscriptPole.KummerCocycle.kummerClassForHalf
example : ∀ (ell : ℚ) (hell : ell ≠ 0)
    (P : (ZInQ.Manuscript.curve ell).toAffine.Point) (Q : GeometricPoints ell)
    (hQ : (2 : ℕ) • Q = rationalPointEmbedding ell P),
    continuousCohomology 1 (twoPowerTopRep ell hell 1) :=
  @ZInQ.Contrib.OneProof.ManuscriptPole.KummerCocycle.kummerClassForHalf
#print axioms ZInQ.Contrib.OneProof.ManuscriptPole.KummerCocycle.kummerClassForHalf

/- Closed public signature: kummerClassForHalf_independent. -/
#check @ZInQ.Contrib.OneProof.ManuscriptPole.KummerCocycle.kummerClassForHalf_independent
example : ∀ (ell : ℚ) (hell : ell ≠ 0)
    (P : (ZInQ.Manuscript.curve ell).toAffine.Point) (Q Q' : GeometricPoints ell)
    (hQ : (2 : ℕ) • Q = rationalPointEmbedding ell P)
    (hQ' : (2 : ℕ) • Q' = rationalPointEmbedding ell P),
    kummerClassForHalf ell hell P Q hQ = kummerClassForHalf ell hell P Q' hQ' :=
  @ZInQ.Contrib.OneProof.ManuscriptPole.KummerCocycle.kummerClassForHalf_independent
#print axioms ZInQ.Contrib.OneProof.ManuscriptPole.KummerCocycle.kummerClassForHalf_independent

/- Closed public signature: kummerClass. -/
#check @ZInQ.Contrib.OneProof.ManuscriptPole.KummerCocycle.kummerClass
example : ∀ (ell : ℚ) (hell : ell ≠ 0)
    (P : (ZInQ.Manuscript.curve ell).toAffine.Point),
    continuousCohomology 1 (twoPowerTopRep ell hell 1) :=
  @ZInQ.Contrib.OneProof.ManuscriptPole.KummerCocycle.kummerClass
#print axioms ZInQ.Contrib.OneProof.ManuscriptPole.KummerCocycle.kummerClass

/- Closed public signature: kummerClass_eq_of_half. -/
#check @ZInQ.Contrib.OneProof.ManuscriptPole.KummerCocycle.kummerClass_eq_of_half
example : ∀ (ell : ℚ) (hell : ell ≠ 0)
    (P : (ZInQ.Manuscript.curve ell).toAffine.Point) (Q : GeometricPoints ell)
    (hQ : (2 : ℕ) • Q = rationalPointEmbedding ell P),
    kummerClass ell hell P = kummerClassForHalf ell hell P Q hQ :=
  @ZInQ.Contrib.OneProof.ManuscriptPole.KummerCocycle.kummerClass_eq_of_half
#print axioms ZInQ.Contrib.OneProof.ManuscriptPole.KummerCocycle.kummerClass_eq_of_half

/- Public property exposure and the actual derived coefficient action. -/
example (ell : ℚ) (hell : ell ≠ 0) : DiscreteTopology (twoPowerTopRep ell hell 1).V :=
  inferInstance
example (ell : ℚ) (hell : ell ≠ 0) :
    ContinuousSMul GaloisGroup (twoPowerTopRep ell hell 1).V := inferInstance
example (ell : ℚ) (hell : ell ≠ 0) (sigma : GaloisGroup)
    (T : (twoPowerTopRep ell hell 1).V) :
    sigma • T = (twoPowerTopRep ell hell 1).ρ sigma T :=
  TopRep.distribMulAction_smul (twoPowerTopRep ell hell 1) sigma T

/- Inclusion uses the same packaged operator, not an assumed action equality. -/
example (ell : ℚ) (hell : ell ≠ 0) (sigma : GaloisGroup)
    (T : (twoPowerTopRep ell hell 1).V) :
    (twoPowerToGeometric ell 1 : (twoPowerTopRep ell hell 1).V →+ GeometricPoints ell)
      (sigma • T) =
      geometricPointMap ell sigma
        ((twoPowerToGeometric ell 1 : (twoPowerTopRep ell hell 1).V →+ GeometricPoints ell) T) := by
  exact twoPowerTopRep_operator_coe ell hell 1 sigma T

/- Packaged and raw cocycles expose the same literal displacement. -/
example (ell : ℚ) (hell : ell ≠ 0)
    (P : (ZInQ.Manuscript.curve ell).toAffine.Point) (Q : GeometricPoints ell)
    (hQ : (2 : ℕ) • Q = rationalPointEmbedding ell P) (sigma : GaloisGroup) :
    twoPowerToGeometric ell 1
      ((packagedKummerCocycleForHalf ell hell P Q hQ :
        GaloisGroup → (twoPowerTopRep ell hell 1).V) sigma) =
      (((kummerCocycleForHalf ell hell P Q hQ : GaloisGroup → twoPowerTorsion ell 1)
        sigma : twoPowerTorsion ell 1) : GeometricPoints ell) :=
  (packagedKummerCocycleForHalf_apply ell hell P Q hQ sigma).trans
    (kummerCocycleForHalf_apply ell hell P Q hQ sigma).symm

/- The packaged value is a member of the actual doubling kernel. -/
example (ell : ℚ) (hell : ell ≠ 0)
    (P : (ZInQ.Manuscript.curve ell).toAffine.Point) (Q : GeometricPoints ell)
    (hQ : (2 : ℕ) • Q = rationalPointEmbedding ell P) (sigma : GaloisGroup) :
    (2 : ℕ) • twoPowerToGeometric ell 1
      ((packagedKummerCocycleForHalf ell hell P Q hQ :
        GaloisGroup → (twoPowerTopRep ell hell 1).V) sigma) = 0 := by
  let T : twoPowerTorsion ell 1 :=
    (packagedKummerCocycleForHalf ell hell P Q hQ :
      GaloisGroup → (twoPowerTopRep ell hell 1).V) sigma
  have ht : (2 : ℕ) • (T : GeometricPoints ell) = 0 := by
    simpa only [mem_twoPowerTorsion, pow_one] using T.property
  exact ht

/- The comparison consumes the exact packaged cocycle and canonical target. -/
example (ell : ℚ) (hell : ell ≠ 0)
    (P : (ZInQ.Manuscript.curve ell).toAffine.Point) :
    continuousCohomology 1 (twoPowerTopRep ell hell 1) :=
  (twoPowerTopRep ell hell 1).explicitH1AddEquivContinuousCohomologyOfDiscrete
    (packagedKummerCocycleForHalf ell hell P (geometricHalf ell hell P)
      (geometricHalf_spec ell hell P) :
      TauCeti.ContCohomology.H1 GaloisGroup (twoPowerTopRep ell hell 1).V)

/- The final constructor agrees with its internally supplied representative. -/
example (ell : ℚ) (hell : ell ≠ 0)
    (P : (ZInQ.Manuscript.curve ell).toAffine.Point) :
    kummerClass ell hell P = kummerClassForHalf ell hell P
      (geometricHalf ell hell P) (geometricHalf_spec ell hell P) :=
  kummerClass_eq_of_half ell hell P (geometricHalf ell hell P) (geometricHalf_spec ell hell P)

end CanonicalConsumers
