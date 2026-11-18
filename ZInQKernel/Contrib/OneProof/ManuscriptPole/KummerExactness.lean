import ZInQKernel.Contrib.OneProof.ManuscriptPole.GaloisCoefficients
import ZInQKernel.Contrib.OneProof.ManuscriptPole.KummerCocycle
import ZInQKernel.Contrib.OneProof.ManuscriptPole.RationalPointDescent
import ZInQKernel.Contrib.TauCeti.RepresentationTheory.Homological.ContCohomology.LowDegree
import ZInQKernel.Contrib.TauCeti.RepresentationTheory.Homological.ContCohomology.SmoothDiscrete.Basic
import ZInQKernel.Contrib.TauCeti.RepresentationTheory.Homological.ContCohomology.CohomologyComparison
import Mathlib.Algebra.Group.Hom.Basic
import Mathlib.Algebra.Group.Subgroup.Ker
import Mathlib.Tactic.Abel

/-!
# Additivity and kernel of the rational Kummer class

Addition of geometric halves gives addition of their actual displacement
cocycles. Passing through the additive quotient and its canonical
continuous-cohomology comparison gives the rational Kummer homomorphism.

A vanishing class supplies an actual two-torsion boundary witness. Removing
that witness from a geometric half gives a Galois-fixed geometric point;
rational point descent then proves that the original point is a rational
double. Conversely, an embedded rational half has zero displacement.

The coefficient representation, point maps and canonical class target are
the existing ones. No local or global Selmer condition, rank statement or
restricted converse is asserted.
-/

set_option autoImplicit false

open scoped Classical

noncomputable section

namespace ZInQ.Contrib.OneProof.ManuscriptPole.KummerExactness

open ZInQ.Contrib.OneProof.ManuscriptPole.GaloisCoefficients
open ZInQ.Contrib.OneProof.ManuscriptPole.KummerCocycle

attribute [local instance] TopRep.distribMulAction

local instance coefficientDiscrete (ell : ℚ) (hell : ell ≠ 0) :
    DiscreteTopology (twoPowerTopRep ell hell 1).V :=
  inferInstanceAs (DiscreteTopology (twoPowerTorsion ell 1))

private theorem coefficientSmooth (ell : ℚ) (hell : ell ≠ 0) :
    TauCeti.IsSmoothDiscrete ℤ (twoPowerTopRep ell hell 1) :=
  ⟨inferInstance, twoPowerTopRep_operator_stabilizer_isOpen ell hell 1⟩

local instance coefficientContinuous (ell : ℚ) (hell : ell ≠ 0) :
    ContinuousSMul GaloisGroup (twoPowerTopRep ell hell 1).V :=
  TauCeti.IsSmoothDiscrete.continuousSMul (coefficientSmooth ell hell)

private theorem coefficient_inclusion_galois (ell : ℚ) (hell : ell ≠ 0)
    (sigma : GaloisGroup) (T : (twoPowerTopRep ell hell 1).V) :
    twoPowerToGeometric ell 1 (sigma • T) =
      geometricPointMap ell sigma (twoPowerToGeometric ell 1 T) := by
  exact twoPowerTopRep_operator_coe ell hell 1 sigma T

/-- The sum of actual geometric halves doubles to the embedded sum of the rational points. -/
theorem geometricHalf_add_spec (ell : ℚ)
    (P P' : (ZInQ.Manuscript.curve ell).toAffine.Point) (Q Q' : GeometricPoints ell)
    (hQ : (2 : ℕ) • Q = rationalPointEmbedding ell P)
    (hQ' : (2 : ℕ) • Q' = rationalPointEmbedding ell P') :
    (2 : ℕ) • (Q + Q') = rationalPointEmbedding ell (P + P') := by
  calc
    (2 : ℕ) • (Q + Q') = (2 : ℕ) • Q + (2 : ℕ) • Q' := nsmul_add Q Q' 2
    _ = rationalPointEmbedding ell P + rationalPointEmbedding ell P' :=
      congrArg₂ (fun A B : GeometricPoints ell => A + B) hQ hQ'
    _ = rationalPointEmbedding ell (P + P') :=
      (map_add (rationalPointEmbedding ell) P P').symm

/-- Packaged cocycles add for the same coefficient representation and the sum of the actual halves. -/
theorem packagedKummerCocycleForHalf_add (ell : ℚ) (hell : ell ≠ 0)
    (P P' : (ZInQ.Manuscript.curve ell).toAffine.Point) (Q Q' : GeometricPoints ell)
    (hQ : (2 : ℕ) • Q = rationalPointEmbedding ell P)
    (hQ' : (2 : ℕ) • Q' = rationalPointEmbedding ell P') :
    packagedKummerCocycleForHalf ell hell (P + P') (Q + Q')
        (geometricHalf_add_spec ell P P' Q Q' hQ hQ') =
      packagedKummerCocycleForHalf ell hell P Q hQ +
        packagedKummerCocycleForHalf ell hell P' Q' hQ' := by
  let X := twoPowerTopRep ell hell 1
  let c : TauCeti.ContCohomology.Z1 GaloisGroup X.V :=
    packagedKummerCocycleForHalf ell hell P Q hQ
  let c' : TauCeti.ContCohomology.Z1 GaloisGroup X.V :=
    packagedKummerCocycleForHalf ell hell P' Q' hQ'
  let cs : TauCeti.ContCohomology.Z1 GaloisGroup X.V :=
    packagedKummerCocycleForHalf ell hell (P + P') (Q + Q')
      (geometricHalf_add_spec ell P P' Q Q' hQ hQ')
  change cs = c + c'
  apply Subtype.ext
  funext sigma
  apply twoPowerToGeometric_injective ell 1
  change twoPowerToGeometric ell 1 ((cs : GaloisGroup → X.V) sigma) =
    twoPowerToGeometric ell 1
      ((c : GaloisGroup → X.V) sigma + (c' : GaloisGroup → X.V) sigma)
  calc
    twoPowerToGeometric ell 1 ((cs : GaloisGroup → X.V) sigma) =
        geometricPointMap ell sigma (Q + Q') - (Q + Q') :=
      packagedKummerCocycleForHalf_apply ell hell (P + P') (Q + Q')
        (geometricHalf_add_spec ell P P' Q Q' hQ hQ') sigma
    _ = (geometricPointMap ell sigma Q - Q) +
        (geometricPointMap ell sigma Q' - Q') := by
      rw [map_add]
      abel
    _ = twoPowerToGeometric ell 1 ((c : GaloisGroup → X.V) sigma) +
        twoPowerToGeometric ell 1 ((c' : GaloisGroup → X.V) sigma) :=
      congrArg₂ (fun A B : GeometricPoints ell => A + B)
        (packagedKummerCocycleForHalf_apply ell hell P Q hQ sigma).symm
        (packagedKummerCocycleForHalf_apply ell hell P' Q' hQ' sigma).symm
    _ = twoPowerToGeometric ell 1
        ((c : GaloisGroup → X.V) sigma + (c' : GaloisGroup → X.V) sigma) :=
      (map_add (twoPowerToGeometric ell 1) _ _).symm

/-- The actual additive quotient and its canonical comparison carry representative addition to class addition. -/
theorem kummerClassForHalf_add (ell : ℚ) (hell : ell ≠ 0)
    (P P' : (ZInQ.Manuscript.curve ell).toAffine.Point) (Q Q' : GeometricPoints ell)
    (hQ : (2 : ℕ) • Q = rationalPointEmbedding ell P)
    (hQ' : (2 : ℕ) • Q' = rationalPointEmbedding ell P') :
    kummerClassForHalf ell hell (P + P') (Q + Q')
        (geometricHalf_add_spec ell P P' Q Q' hQ hQ') =
      kummerClassForHalf ell hell P Q hQ + kummerClassForHalf ell hell P' Q' hQ' := by
  let X := twoPowerTopRep ell hell 1
  let c : TauCeti.ContCohomology.Z1 GaloisGroup X.V :=
    packagedKummerCocycleForHalf ell hell P Q hQ
  let c' : TauCeti.ContCohomology.Z1 GaloisGroup X.V :=
    packagedKummerCocycleForHalf ell hell P' Q' hQ'
  let cs : TauCeti.ContCohomology.Z1 GaloisGroup X.V :=
    packagedKummerCocycleForHalf ell hell (P + P') (Q + Q')
      (geometricHalf_add_spec ell P P' Q Q' hQ hQ')
  let pi : TauCeti.ContCohomology.Z1 GaloisGroup X.V →+
      TauCeti.ContCohomology.H1 GaloisGroup X.V :=
    TauCeti.ContCohomology.H1pi GaloisGroup X.V
  let e : TauCeti.ContCohomology.H1 GaloisGroup X.V ≃+ continuousCohomology 1 X :=
    X.explicitH1AddEquivContinuousCohomologyOfDiscrete
  have hc : cs = c + c' := packagedKummerCocycleForHalf_add ell hell P P' Q Q' hQ hQ'
  change e (pi cs) = e (pi c) + e (pi c')
  calc
    e (pi cs) = e (pi (c + c')) := congrArg (fun d => e (pi d)) hc
    _ = e (pi c + pi c') := congrArg e (map_add pi c c')
    _ = e (pi c) + e (pi c') := map_add e _ _

/-- The rational Kummer class is additive without any externally supplied geometric half. -/
theorem kummerClass_add (ell : ℚ) (hell : ell ≠ 0)
    (P P' : (ZInQ.Manuscript.curve ell).toAffine.Point) :
    kummerClass ell hell (P + P') = kummerClass ell hell P + kummerClass ell hell P' := by
  let Q := geometricHalf ell hell P
  let Q' := geometricHalf ell hell P'
  let hQ : (2 : ℕ) • Q = rationalPointEmbedding ell P := geometricHalf_spec ell hell P
  let hQ' : (2 : ℕ) • Q' = rationalPointEmbedding ell P' := geometricHalf_spec ell hell P'
  let hs : (2 : ℕ) • (Q + Q') = rationalPointEmbedding ell (P + P') :=
    geometricHalf_add_spec ell P P' Q Q' hQ hQ'
  calc
    kummerClass ell hell (P + P') =
        kummerClassForHalf ell hell (P + P') (Q + Q') hs :=
      kummerClass_eq_of_half ell hell (P + P') (Q + Q') hs
    _ = kummerClassForHalf ell hell P Q hQ + kummerClassForHalf ell hell P' Q' hQ' :=
      kummerClassForHalf_add ell hell P P' Q Q' hQ hQ'
    _ = kummerClass ell hell P + kummerClass ell hell P' :=
      congrArg₂ (fun A B : continuousCohomology 1 (twoPowerTopRep ell hell 1) => A + B)
        (kummerClass_eq_of_half ell hell P Q hQ).symm
        (kummerClass_eq_of_half ell hell P' Q' hQ').symm

/-- The zero rational point has zero Kummer class, by actual additivity and cancellation. -/
theorem kummerClass_zero (ell : ℚ) (hell : ell ≠ 0) :
    kummerClass ell hell (0 : (ZInQ.Manuscript.curve ell).toAffine.Point) = 0 := by
  have h : kummerClass ell hell (0 : (ZInQ.Manuscript.curve ell).toAffine.Point) +
        kummerClass ell hell (0 : (ZInQ.Manuscript.curve ell).toAffine.Point) =
      kummerClass ell hell (0 : (ZInQ.Manuscript.curve ell).toAffine.Point) +
        (0 : continuousCohomology 1 (twoPowerTopRep ell hell 1)) := by
    simpa only [zero_add, add_zero] using (kummerClass_add ell hell 0 0).symm
  exact add_left_cancel h

/-- The actual rational Kummer homomorphism lands in the existing canonical continuous degree-one cohomology. -/
def rationalKummerHom (ell : ℚ) (hell : ell ≠ 0) :
    (ZInQ.Manuscript.curve ell).toAffine.Point →+
      continuousCohomology 1 (twoPowerTopRep ell hell 1) where
  toFun := kummerClass ell hell
  map_zero' := kummerClass_zero ell hell
  map_add' := kummerClass_add ell hell

theorem rationalKummerHom_apply (ell : ℚ) (hell : ell ≠ 0)
    (P : (ZInQ.Manuscript.curve ell).toAffine.Point) :
    rationalKummerHom ell hell P = kummerClass ell hell P := rfl

/-- Negation is preserved by the same actual additive homomorphism. -/
theorem kummerClass_neg (ell : ℚ) (hell : ell ≠ 0)
    (P : (ZInQ.Manuscript.curve ell).toAffine.Point) :
    kummerClass ell hell (-P) = -kummerClass ell hell P :=
  map_neg (rationalKummerHom ell hell) P

/-- An actual rational double has zero class because its embedded rational half has zero displacement. -/
theorem kummerClass_two_nsmul (ell : ℚ) (hell : ell ≠ 0)
    (R : (ZInQ.Manuscript.curve ell).toAffine.Point) :
    kummerClass ell hell ((2 : ℕ) • R) = 0 := by
  let X := twoPowerTopRep ell hell 1
  let P := (2 : ℕ) • R
  let Q := rationalPointEmbedding ell R
  have hQ : (2 : ℕ) • Q = rationalPointEmbedding ell P :=
    (map_nsmul (rationalPointEmbedding ell) 2 R).symm
  let c : TauCeti.ContCohomology.Z1 GaloisGroup X.V :=
    packagedKummerCocycleForHalf ell hell P Q hQ
  have hc : c = 0 := by
    apply Subtype.ext
    funext sigma
    apply twoPowerToGeometric_injective ell 1
    change twoPowerToGeometric ell 1 ((c : GaloisGroup → X.V) sigma) =
      twoPowerToGeometric ell 1 (0 : X.V)
    calc
      twoPowerToGeometric ell 1 ((c : GaloisGroup → X.V) sigma) =
          geometricPointMap ell sigma Q - Q :=
        packagedKummerCocycleForHalf_apply ell hell P Q hQ sigma
      _ = 0 := by
        change geometricPointMap ell sigma (rationalPointEmbedding ell R) -
          rationalPointEmbedding ell R = 0
        rw [rationalPointEmbedding_galoisFixed, sub_self]
      _ = twoPowerToGeometric ell 1 (0 : X.V) := (map_zero (twoPowerToGeometric ell 1)).symm
  let pi : TauCeti.ContCohomology.Z1 GaloisGroup X.V →+
      TauCeti.ContCohomology.H1 GaloisGroup X.V :=
    TauCeti.ContCohomology.H1pi GaloisGroup X.V
  let e : TauCeti.ContCohomology.H1 GaloisGroup X.V ≃+ continuousCohomology 1 X :=
    X.explicitH1AddEquivContinuousCohomologyOfDiscrete
  calc
    kummerClass ell hell ((2 : ℕ) • R) = kummerClassForHalf ell hell P Q hQ :=
      kummerClass_eq_of_half ell hell P Q hQ
    _ = e (pi c) := rfl
    _ = e (pi (0 : TauCeti.ContCohomology.Z1 GaloisGroup X.V)) :=
      congrArg (fun d => e (pi d)) hc
    _ = e (0 : TauCeti.ContCohomology.H1 GaloisGroup X.V) := congrArg e (map_zero pi)
    _ = 0 := map_zero e

/-- Vanishing of the actual rational Kummer class is equivalent to being an actual rational double. -/
theorem kummerClass_eq_zero_iff_two_nsmul (ell : ℚ) (hell : ell ≠ 0)
    (P : (ZInQ.Manuscript.curve ell).toAffine.Point) :
    kummerClass ell hell P = 0 ↔
      ∃ R : (ZInQ.Manuscript.curve ell).toAffine.Point, (2 : ℕ) • R = P := by
  let X := twoPowerTopRep ell hell 1
  let Q := geometricHalf ell hell P
  let hQ : (2 : ℕ) • Q = rationalPointEmbedding ell P := geometricHalf_spec ell hell P
  let c : TauCeti.ContCohomology.Z1 GaloisGroup X.V :=
    packagedKummerCocycleForHalf ell hell P Q hQ
  let e : TauCeti.ContCohomology.H1 GaloisGroup X.V ≃+ continuousCohomology 1 X :=
    X.explicitH1AddEquivContinuousCohomologyOfDiscrete
  let phi : X.V →+ GeometricPoints ell := twoPowerToGeometric ell 1
  constructor
  · intro hzero
    have he : e (c : TauCeti.ContCohomology.H1 GaloisGroup X.V) = 0 :=
      (kummerClass_eq_of_half ell hell P Q hQ).symm.trans hzero
    have hcclass : (c : TauCeti.ContCohomology.H1 GaloisGroup X.V) = 0 :=
      e.injective (he.trans (map_zero e).symm)
    have hB : (c : GaloisGroup → X.V) ∈ TauCeti.ContCohomology.B1 GaloisGroup X.V :=
      TauCeti.ContCohomology.H1pi_eq_zero_iff.mp hcclass
    obtain ⟨T, hT⟩ := TauCeti.ContCohomology.mem_B1_iff.mp hB
    let Tg : GeometricPoints ell := phi T
    have hTzero : (2 : ℕ) • Tg = 0 := by
      have ht := (show twoPowerTorsion ell 1 from T).property
      have hz : (2 : ℕ) • ((show twoPowerTorsion ell 1 from T) : GeometricPoints ell) = 0 := by
        simpa only [mem_twoPowerTorsion, pow_one] using ht
      exact hz
    have hdisplacement (sigma : GaloisGroup) :
        geometricPointMap ell sigma Tg - Tg = geometricPointMap ell sigma Q - Q := by
      calc
        geometricPointMap ell sigma Tg - Tg = phi (sigma • T) - phi T :=
          congrArg₂ (fun A B : GeometricPoints ell => A - B)
            (coefficient_inclusion_galois ell hell sigma T).symm rfl
        _ = phi (sigma • T - T) := (map_sub phi _ _).symm
        _ = phi ((c : GaloisGroup → X.V) sigma) := congrArg phi (hT sigma)
        _ = geometricPointMap ell sigma Q - Q :=
          packagedKummerCocycleForHalf_apply ell hell P Q hQ sigma
    have hfixed : ∀ sigma : GaloisGroup,
        geometricPointMap ell sigma (Q - Tg) = Q - Tg := by
      intro sigma
      calc
        geometricPointMap ell sigma (Q - Tg) =
            geometricPointMap ell sigma Q - geometricPointMap ell sigma Tg :=
          map_sub (geometricPointMap ell sigma) Q Tg
        _ = (geometricPointMap ell sigma Q - Q) -
            (geometricPointMap ell sigma Tg - Tg) + (Q - Tg) := by abel
        _ = Q - Tg := by
          rw [← hdisplacement sigma, sub_self, zero_add]
    obtain ⟨R, hR⟩ :=
      RationalPointDescent.exists_rationalPoint_of_galoisFixed ell (Q - Tg) hfixed
    have hembR : rationalPointEmbedding ell R = Q - Tg := hR
    refine ⟨R, rationalPointEmbedding_injective ell ?_⟩
    calc
      rationalPointEmbedding ell ((2 : ℕ) • R) =
          (2 : ℕ) • rationalPointEmbedding ell R := map_nsmul (rationalPointEmbedding ell) 2 R
      _ = (2 : ℕ) • (Q - Tg) := congrArg (fun U : GeometricPoints ell => (2 : ℕ) • U) hembR
      _ = rationalPointEmbedding ell P := by
        rw [nsmul_sub, hQ, hTzero, sub_zero]
  · rintro ⟨R, hR⟩
    calc
      kummerClass ell hell P = kummerClass ell hell ((2 : ℕ) • R) :=
        congrArg (kummerClass ell hell) hR.symm
      _ = 0 := kummerClass_two_nsmul ell hell R

/-- The kernel is exactly the range of actual rational doubling in the original point group. -/
theorem rationalKummerHom_ker (ell : ℚ) (hell : ell ≠ 0) :
    (rationalKummerHom ell hell).ker =
      (nsmulAddMonoidHom (α := (ZInQ.Manuscript.curve ell).toAffine.Point) 2).range := by
  ext P
  rw [AddMonoidHom.mem_ker, AddMonoidHom.mem_range]
  change kummerClass ell hell P = 0 ↔
    ∃ R : (ZInQ.Manuscript.curve ell).toAffine.Point, (2 : ℕ) • R = P
  exact kummerClass_eq_zero_iff_two_nsmul ell hell P

end ZInQ.Contrib.OneProof.ManuscriptPole.KummerExactness
