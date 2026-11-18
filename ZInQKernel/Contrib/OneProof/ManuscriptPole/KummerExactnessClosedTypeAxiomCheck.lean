import ZInQKernel.Contrib.OneProof.ManuscriptPole.KummerExactness

set_option autoImplicit false
open scoped Classical
open ZInQ.Contrib.OneProof.ManuscriptPole.GaloisCoefficients
open ZInQ.Contrib.OneProof.ManuscriptPole.KummerCocycle

noncomputable section

/- Source-only future consumer input. No execution result is asserted here. -/

set_option pp.all true
set_option pp.proofs true
set_option pp.universes true
set_option pp.fullNames true

/- Closed source telescope: geometricHalf_add_spec. -/
#check @ZInQ.Contrib.OneProof.ManuscriptPole.KummerExactness.geometricHalf_add_spec
example : ∀ (ell : ℚ)
    (P P' : (ZInQ.Manuscript.curve ell).toAffine.Point) (Q Q' : GeometricPoints ell)
    (hQ : (2 : ℕ) • Q = rationalPointEmbedding ell P)
    (hQ' : (2 : ℕ) • Q' = rationalPointEmbedding ell P'),
  (2 : ℕ) • (Q + Q') = rationalPointEmbedding ell (P + P') :=
  @ZInQ.Contrib.OneProof.ManuscriptPole.KummerExactness.geometricHalf_add_spec
#print axioms ZInQ.Contrib.OneProof.ManuscriptPole.KummerExactness.geometricHalf_add_spec

/- Closed source telescope: packagedKummerCocycleForHalf_add. -/
#check @ZInQ.Contrib.OneProof.ManuscriptPole.KummerExactness.packagedKummerCocycleForHalf_add
example : ∀ (ell : ℚ) (hell : ell ≠ 0)
    (P P' : (ZInQ.Manuscript.curve ell).toAffine.Point) (Q Q' : GeometricPoints ell)
    (hQ : (2 : ℕ) • Q = rationalPointEmbedding ell P)
    (hQ' : (2 : ℕ) • Q' = rationalPointEmbedding ell P'),
  packagedKummerCocycleForHalf ell hell (P + P') (Q + Q')
      (ZInQ.Contrib.OneProof.ManuscriptPole.KummerExactness.geometricHalf_add_spec
        ell P P' Q Q' hQ hQ') =
    packagedKummerCocycleForHalf ell hell P Q hQ +
      packagedKummerCocycleForHalf ell hell P' Q' hQ' :=
  @ZInQ.Contrib.OneProof.ManuscriptPole.KummerExactness.packagedKummerCocycleForHalf_add
#print axioms ZInQ.Contrib.OneProof.ManuscriptPole.KummerExactness.packagedKummerCocycleForHalf_add

/- Closed source telescope: kummerClassForHalf_add. -/
#check @ZInQ.Contrib.OneProof.ManuscriptPole.KummerExactness.kummerClassForHalf_add
example : ∀ (ell : ℚ) (hell : ell ≠ 0)
    (P P' : (ZInQ.Manuscript.curve ell).toAffine.Point) (Q Q' : GeometricPoints ell)
    (hQ : (2 : ℕ) • Q = rationalPointEmbedding ell P)
    (hQ' : (2 : ℕ) • Q' = rationalPointEmbedding ell P'),
  kummerClassForHalf ell hell (P + P') (Q + Q')
      (ZInQ.Contrib.OneProof.ManuscriptPole.KummerExactness.geometricHalf_add_spec
        ell P P' Q Q' hQ hQ') =
    kummerClassForHalf ell hell P Q hQ + kummerClassForHalf ell hell P' Q' hQ' :=
  @ZInQ.Contrib.OneProof.ManuscriptPole.KummerExactness.kummerClassForHalf_add
#print axioms ZInQ.Contrib.OneProof.ManuscriptPole.KummerExactness.kummerClassForHalf_add

/- Closed source telescope: kummerClass_add. -/
#check @ZInQ.Contrib.OneProof.ManuscriptPole.KummerExactness.kummerClass_add
example : ∀ (ell : ℚ) (hell : ell ≠ 0)
    (P P' : (ZInQ.Manuscript.curve ell).toAffine.Point),
  kummerClass ell hell (P + P') = kummerClass ell hell P + kummerClass ell hell P' :=
  @ZInQ.Contrib.OneProof.ManuscriptPole.KummerExactness.kummerClass_add
#print axioms ZInQ.Contrib.OneProof.ManuscriptPole.KummerExactness.kummerClass_add

/- Closed source telescope: kummerClass_zero. -/
#check @ZInQ.Contrib.OneProof.ManuscriptPole.KummerExactness.kummerClass_zero
example : ∀ (ell : ℚ) (hell : ell ≠ 0),
  kummerClass ell hell (0 : (ZInQ.Manuscript.curve ell).toAffine.Point) = 0 :=
  @ZInQ.Contrib.OneProof.ManuscriptPole.KummerExactness.kummerClass_zero
#print axioms ZInQ.Contrib.OneProof.ManuscriptPole.KummerExactness.kummerClass_zero

/- Closed source telescope: rationalKummerHom. -/
#check @ZInQ.Contrib.OneProof.ManuscriptPole.KummerExactness.rationalKummerHom
example : ∀ (ell : ℚ) (hell : ell ≠ 0),
  (ZInQ.Manuscript.curve ell).toAffine.Point →+
    continuousCohomology 1 (twoPowerTopRep ell hell 1) :=
  @ZInQ.Contrib.OneProof.ManuscriptPole.KummerExactness.rationalKummerHom
#print axioms ZInQ.Contrib.OneProof.ManuscriptPole.KummerExactness.rationalKummerHom

/- Closed source telescope: rationalKummerHom_apply. -/
#check @ZInQ.Contrib.OneProof.ManuscriptPole.KummerExactness.rationalKummerHom_apply
example : ∀ (ell : ℚ) (hell : ell ≠ 0)
    (P : (ZInQ.Manuscript.curve ell).toAffine.Point),
  ZInQ.Contrib.OneProof.ManuscriptPole.KummerExactness.rationalKummerHom ell hell P =
    kummerClass ell hell P :=
  @ZInQ.Contrib.OneProof.ManuscriptPole.KummerExactness.rationalKummerHom_apply
#print axioms ZInQ.Contrib.OneProof.ManuscriptPole.KummerExactness.rationalKummerHom_apply

/- Closed source telescope: kummerClass_neg. -/
#check @ZInQ.Contrib.OneProof.ManuscriptPole.KummerExactness.kummerClass_neg
example : ∀ (ell : ℚ) (hell : ell ≠ 0)
    (P : (ZInQ.Manuscript.curve ell).toAffine.Point),
  kummerClass ell hell (-P) = -kummerClass ell hell P :=
  @ZInQ.Contrib.OneProof.ManuscriptPole.KummerExactness.kummerClass_neg
#print axioms ZInQ.Contrib.OneProof.ManuscriptPole.KummerExactness.kummerClass_neg

/- Closed source telescope: kummerClass_two_nsmul. -/
#check @ZInQ.Contrib.OneProof.ManuscriptPole.KummerExactness.kummerClass_two_nsmul
example : ∀ (ell : ℚ) (hell : ell ≠ 0)
    (R : (ZInQ.Manuscript.curve ell).toAffine.Point),
  kummerClass ell hell ((2 : ℕ) • R) = 0 :=
  @ZInQ.Contrib.OneProof.ManuscriptPole.KummerExactness.kummerClass_two_nsmul
#print axioms ZInQ.Contrib.OneProof.ManuscriptPole.KummerExactness.kummerClass_two_nsmul

/- Closed source telescope: kummerClass_eq_zero_iff_two_nsmul. -/
#check @ZInQ.Contrib.OneProof.ManuscriptPole.KummerExactness.kummerClass_eq_zero_iff_two_nsmul
example : ∀ (ell : ℚ) (hell : ell ≠ 0)
    (P : (ZInQ.Manuscript.curve ell).toAffine.Point),
  kummerClass ell hell P = 0 ↔
    ∃ R : (ZInQ.Manuscript.curve ell).toAffine.Point, (2 : ℕ) • R = P :=
  @ZInQ.Contrib.OneProof.ManuscriptPole.KummerExactness.kummerClass_eq_zero_iff_two_nsmul
#print axioms ZInQ.Contrib.OneProof.ManuscriptPole.KummerExactness.kummerClass_eq_zero_iff_two_nsmul

/- Closed source telescope: rationalKummerHom_ker. -/
#check @ZInQ.Contrib.OneProof.ManuscriptPole.KummerExactness.rationalKummerHom_ker
example : ∀ (ell : ℚ) (hell : ell ≠ 0),
  (ZInQ.Contrib.OneProof.ManuscriptPole.KummerExactness.rationalKummerHom ell hell).ker =
    (nsmulAddMonoidHom (α := (ZInQ.Manuscript.curve ell).toAffine.Point) 2).range :=
  @ZInQ.Contrib.OneProof.ManuscriptPole.KummerExactness.rationalKummerHom_ker
#print axioms ZInQ.Contrib.OneProof.ManuscriptPole.KummerExactness.rationalKummerHom_ker

/- Literal source body of the one public definition. -/
#print ZInQ.Contrib.OneProof.ManuscriptPole.KummerExactness.rationalKummerHom
