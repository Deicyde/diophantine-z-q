import ZInQKernel.Contrib.OneProof.ManuscriptPole.KummerExactness

set_option autoImplicit false
open scoped Classical
open ZInQ.Contrib.OneProof.ManuscriptPole.GaloisCoefficients
open ZInQ.Contrib.OneProof.ManuscriptPole.KummerCocycle

noncomputable section

/- Source-only future consumer input. No execution result is asserted here. -/

/- The rational Kummer homomorphism is additive. -/
example (ell : ℚ) (hell : ell ≠ 0) (P P' : (ZInQ.Manuscript.curve ell).toAffine.Point) :
    ZInQ.Contrib.OneProof.ManuscriptPole.KummerExactness.rationalKummerHom ell hell (P + P') =
      ZInQ.Contrib.OneProof.ManuscriptPole.KummerExactness.rationalKummerHom ell hell P +
        ZInQ.Contrib.OneProof.ManuscriptPole.KummerExactness.rationalKummerHom ell hell P' :=
  map_add (ZInQ.Contrib.OneProof.ManuscriptPole.KummerExactness.rationalKummerHom ell hell) P P'

/- The rational Kummer homomorphism preserves negation. -/
example (ell : ℚ) (hell : ell ≠ 0) (P : (ZInQ.Manuscript.curve ell).toAffine.Point) :
    ZInQ.Contrib.OneProof.ManuscriptPole.KummerExactness.rationalKummerHom ell hell (-P) =
      -ZInQ.Contrib.OneProof.ManuscriptPole.KummerExactness.rationalKummerHom ell hell P :=
  map_neg (ZInQ.Contrib.OneProof.ManuscriptPole.KummerExactness.rationalKummerHom ell hell) P

/- The rational Kummer homomorphism preserves subtraction. -/
example (ell : ℚ) (hell : ell ≠ 0) (P P' : (ZInQ.Manuscript.curve ell).toAffine.Point) :
    ZInQ.Contrib.OneProof.ManuscriptPole.KummerExactness.rationalKummerHom ell hell (P - P') =
      ZInQ.Contrib.OneProof.ManuscriptPole.KummerExactness.rationalKummerHom ell hell P -
        ZInQ.Contrib.OneProof.ManuscriptPole.KummerExactness.rationalKummerHom ell hell P' :=
  map_sub (ZInQ.Contrib.OneProof.ManuscriptPole.KummerExactness.rationalKummerHom ell hell) P P'

/- Every rational double lies in the kernel of the homomorphism. -/
example (ell : ℚ) (hell : ell ≠ 0) (R : (ZInQ.Manuscript.curve ell).toAffine.Point) :
    (2 : ℕ) • R ∈
      (ZInQ.Contrib.OneProof.ManuscriptPole.KummerExactness.rationalKummerHom ell hell).ker :=
  AddMonoidHom.mem_ker.mpr
    ((ZInQ.Contrib.OneProof.ManuscriptPole.KummerExactness.rationalKummerHom_apply
        ell hell ((2 : ℕ) • R)).trans
      (ZInQ.Contrib.OneProof.ManuscriptPole.KummerExactness.kummerClass_two_nsmul ell hell R))

/- Kernel membership is membership in the range of rational doubling. -/
example (ell : ℚ) (hell : ell ≠ 0) (P : (ZInQ.Manuscript.curve ell).toAffine.Point) :
    P ∈ (ZInQ.Contrib.OneProof.ManuscriptPole.KummerExactness.rationalKummerHom ell hell).ker ↔
      P ∈ (nsmulAddMonoidHom (α := (ZInQ.Manuscript.curve ell).toAffine.Point) 2).range := by
  rw [ZInQ.Contrib.OneProof.ManuscriptPole.KummerExactness.rationalKummerHom_ker ell hell]

/- A vanishing homomorphism value yields an actual rational half. -/
example (ell : ℚ) (hell : ell ≠ 0) (P : (ZInQ.Manuscript.curve ell).toAffine.Point)
    (h : ZInQ.Contrib.OneProof.ManuscriptPole.KummerExactness.rationalKummerHom ell hell P = 0) :
    ∃ R : (ZInQ.Manuscript.curve ell).toAffine.Point, (2 : ℕ) • R = P :=
  (ZInQ.Contrib.OneProof.ManuscriptPole.KummerExactness.kummerClass_eq_zero_iff_two_nsmul
      ell hell P).mp
    ((ZInQ.Contrib.OneProof.ManuscriptPole.KummerExactness.rationalKummerHom_apply
        ell hell P).symm.trans h)
