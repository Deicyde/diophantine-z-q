import ZInQKernel.Contrib.OneProof.ManuscriptPole.RationalPointDescent

/-!
# Public rational fixed-point descent consumers

The consumers retain the existing rational closure and geometric point group,
the full automorphism-fixedness input, and the actual rational field map.
Infinity and affine nonsingular points use the same map and unique-preimage
orientation. No nonzero-parameter or rational preimage premise is supplied.
-/

set_option autoImplicit false
open scoped Classical
open ZInQ.Contrib.OneProof.ManuscriptPole.GaloisCoefficients
open ZInQ.Contrib.OneProof.ManuscriptPole.RationalPointDescent

noncomputable section

set_option pp.all true
set_option pp.proofs true
set_option pp.universes true
set_option pp.fullNames true

/- Closed public signature: qbar_fixed_iff_rational. -/
#check @ZInQ.Contrib.OneProof.ManuscriptPole.RationalPointDescent.qbar_fixed_iff_rational
example : ∀ (x : Qbar),
    (∀ sigma : GaloisGroup, sigma.toAlgHom x = x) ↔
      ∃ q : ℚ, algebraMap ℚ Qbar q = x :=
  @ZInQ.Contrib.OneProof.ManuscriptPole.RationalPointDescent.qbar_fixed_iff_rational
#print axioms ZInQ.Contrib.OneProof.ManuscriptPole.RationalPointDescent.qbar_fixed_iff_rational

/- Closed public signature: exists_rationalPoint_of_galoisFixed. -/
#check @ZInQ.Contrib.OneProof.ManuscriptPole.RationalPointDescent.exists_rationalPoint_of_galoisFixed
example : ∀ (ell : ℚ) (P : GeometricPoints ell)
    (hfixed : ∀ sigma : GaloisGroup, geometricPointMap ell sigma P = P),
    ∃ R : (ZInQ.Manuscript.curve ell).toAffine.Point,
      WeierstrassCurve.Affine.Point.map
        (R := ℚ) (S := ℚ) (F := ℚ) (K := Qbar)
        (W' := (ZInQ.Manuscript.curve ell).toAffine) (Algebra.ofId ℚ Qbar) R = P :=
  @ZInQ.Contrib.OneProof.ManuscriptPole.RationalPointDescent.exists_rationalPoint_of_galoisFixed
#print axioms ZInQ.Contrib.OneProof.ManuscriptPole.RationalPointDescent.exists_rationalPoint_of_galoisFixed

/- Closed public signature: existsUnique_rationalPoint_of_galoisFixed. -/
#check @ZInQ.Contrib.OneProof.ManuscriptPole.RationalPointDescent.existsUnique_rationalPoint_of_galoisFixed
example : ∀ (ell : ℚ) (P : GeometricPoints ell)
    (hfixed : ∀ sigma : GaloisGroup, geometricPointMap ell sigma P = P),
    ∃! R : (ZInQ.Manuscript.curve ell).toAffine.Point,
      WeierstrassCurve.Affine.Point.map
        (R := ℚ) (S := ℚ) (F := ℚ) (K := Qbar)
        (W' := (ZInQ.Manuscript.curve ell).toAffine) (Algebra.ofId ℚ Qbar) R = P :=
  @ZInQ.Contrib.OneProof.ManuscriptPole.RationalPointDescent.existsUnique_rationalPoint_of_galoisFixed
#print axioms ZInQ.Contrib.OneProof.ManuscriptPole.RationalPointDescent.existsUnique_rationalPoint_of_galoisFixed

/- Closed public signature: existsUnique_rationalPoint_of_fixed. -/
#check @ZInQ.Contrib.OneProof.ManuscriptPole.RationalPointDescent.existsUnique_rationalPoint_of_fixed
example : ∀ (ell : ℚ) (P : GeometricPoints ell)
    (hfixed : ∀ sigma : GaloisGroup, sigma • P = P),
    ∃! R : (ZInQ.Manuscript.curve ell).toAffine.Point,
      WeierstrassCurve.Affine.Point.map
        (R := ℚ) (S := ℚ) (F := ℚ) (K := Qbar)
        (W' := (ZInQ.Manuscript.curve ell).toAffine) (Algebra.ofId ℚ Qbar) R = P :=
  @ZInQ.Contrib.OneProof.ManuscriptPole.RationalPointDescent.existsUnique_rationalPoint_of_fixed
#print axioms ZInQ.Contrib.OneProof.ManuscriptPole.RationalPointDescent.existsUnique_rationalPoint_of_fixed

/- The point map uses exactly the existing rational algebra map. -/
example (q : ℚ) : (Algebra.ofId ℚ Qbar) q = algebraMap ℚ Qbar q := rfl

/- The two public presentations are the same actual point map. -/
example (ell : ℚ) (R : (ZInQ.Manuscript.curve ell).toAffine.Point) :
    WeierstrassCurve.Affine.Point.map
      (R := ℚ) (S := ℚ) (F := ℚ) (K := Qbar)
      (W' := (ZInQ.Manuscript.curve ell).toAffine) (Algebra.ofId ℚ Qbar) R =
    WeierstrassCurve.Affine.Point.baseChange
      (W' := (ZInQ.Manuscript.curve ell).toAffine) ℚ Qbar R := rfl

/- Infinity maps to infinity through this same rational point map. -/
example (ell : ℚ) :
    WeierstrassCurve.Affine.Point.map
      (R := ℚ) (S := ℚ) (F := ℚ) (K := Qbar)
      (W' := (ZInQ.Manuscript.curve ell).toAffine) (Algebra.ofId ℚ Qbar)
      (0 : (ZInQ.Manuscript.curve ell).toAffine.Point) = (0 : GeometricPoints ell) :=
  map_zero (WeierstrassCurve.Affine.Point.map
    (R := ℚ) (S := ℚ) (F := ℚ) (K := Qbar)
    (W' := (ZInQ.Manuscript.curve ell).toAffine) (Algebra.ofId ℚ Qbar))

/- Zero fixedness is derived, not assumed for arbitrary points. -/
example (ell : ℚ) (sigma : GaloisGroup) :
    geometricPointMap ell sigma (0 : GeometricPoints ell) = 0 :=
  geometricPointMap_zero ell sigma

/- The zero consumer supplies the genuine all-automorphism fixedness proof. -/
example (ell : ℚ) :
    ∃! R : (ZInQ.Manuscript.curve ell).toAffine.Point,
      WeierstrassCurve.Affine.Point.map
        (R := ℚ) (S := ℚ) (F := ℚ) (K := Qbar)
        (W' := (ZInQ.Manuscript.curve ell).toAffine) (Algebra.ofId ℚ Qbar) R =
      (0 : GeometricPoints ell) :=
  existsUnique_rationalPoint_of_galoisFixed ell (0 : GeometricPoints ell)
    (fun sigma => geometricPointMap_zero ell sigma)

/- An affine consumer retains intrinsic nonsingularity and full fixedness. -/
example (ell : ℚ) (x y : Qbar)
    (hxy : ((ZInQ.Manuscript.curve ell).baseChange Qbar).toAffine.Nonsingular x y)
    (hfixed : ∀ sigma : GaloisGroup,
      geometricPointMap ell sigma
        (WeierstrassCurve.Affine.Point.some x y hxy : GeometricPoints ell) =
        (WeierstrassCurve.Affine.Point.some x y hxy : GeometricPoints ell)) :
    ∃! R : (ZInQ.Manuscript.curve ell).toAffine.Point,
      WeierstrassCurve.Affine.Point.map
        (R := ℚ) (S := ℚ) (F := ℚ) (K := Qbar)
        (W' := (ZInQ.Manuscript.curve ell).toAffine) (Algebra.ofId ℚ Qbar) R =
      (WeierstrassCurve.Affine.Point.some x y hxy : GeometricPoints ell) :=
  existsUnique_rationalPoint_of_galoisFixed ell
    (WeierstrassCurve.Affine.Point.some x y hxy : GeometricPoints ell) hfixed
