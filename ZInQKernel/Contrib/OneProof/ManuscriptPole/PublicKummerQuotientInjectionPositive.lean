import ZInQKernel.Contrib.OneProof.ManuscriptPole.KummerQuotientInjection

/-!
# Public rational two-descent quotient consumers

The quotient is the actual rational point group modulo its doubling range.
The descended additive homomorphism retains the canonical continuous
cohomology target, its literal projection values and its injectivity.
No surjectivity, local condition or finiteness conclusion is asserted.
-/

set_option autoImplicit false
open scoped Classical
open ZInQ.Contrib.OneProof.ManuscriptPole.GaloisCoefficients
open ZInQ.Contrib.OneProof.ManuscriptPole.KummerCocycle
open ZInQ.Contrib.OneProof.ManuscriptPole.KummerExactness
open ZInQ.Contrib.OneProof.ManuscriptPole.KummerQuotientInjection

noncomputable section

set_option pp.all true
set_option pp.proofs true
set_option pp.universes true
set_option pp.fullNames true

/- Closed public signature: rationalDoublingSubgroup. -/
#check @ZInQ.Contrib.OneProof.ManuscriptPole.KummerQuotientInjection.rationalDoublingSubgroup
example : ∀ (ell : ℚ), AddSubgroup ((ZInQ.Manuscript.curve ell).toAffine.Point) :=
  @ZInQ.Contrib.OneProof.ManuscriptPole.KummerQuotientInjection.rationalDoublingSubgroup
#print axioms ZInQ.Contrib.OneProof.ManuscriptPole.KummerQuotientInjection.rationalDoublingSubgroup

/- Closed public signature: mem_rationalDoublingSubgroup. -/
#check @ZInQ.Contrib.OneProof.ManuscriptPole.KummerQuotientInjection.mem_rationalDoublingSubgroup
example : ∀ (ell : ℚ) (P : (ZInQ.Manuscript.curve ell).toAffine.Point),
    P ∈ rationalDoublingSubgroup ell ↔
      ∃ R : (ZInQ.Manuscript.curve ell).toAffine.Point, (2 : ℕ) • R = P :=
  @ZInQ.Contrib.OneProof.ManuscriptPole.KummerQuotientInjection.mem_rationalDoublingSubgroup
#print axioms ZInQ.Contrib.OneProof.ManuscriptPole.KummerQuotientInjection.mem_rationalDoublingSubgroup

/- Closed public signature: RationalTwoDescentQuotient. -/
#check @ZInQ.Contrib.OneProof.ManuscriptPole.KummerQuotientInjection.RationalTwoDescentQuotient
example : ∀ (ell : ℚ), Type :=
  @ZInQ.Contrib.OneProof.ManuscriptPole.KummerQuotientInjection.RationalTwoDescentQuotient
#print axioms ZInQ.Contrib.OneProof.ManuscriptPole.KummerQuotientInjection.RationalTwoDescentQuotient

/- Closed public signature: rationalDoublingSubgroup_eq_ker. -/
#check @ZInQ.Contrib.OneProof.ManuscriptPole.KummerQuotientInjection.rationalDoublingSubgroup_eq_ker
example : ∀ (ell : ℚ) (hell : ell ≠ 0),
    rationalDoublingSubgroup ell = (rationalKummerHom ell hell).ker :=
  @ZInQ.Contrib.OneProof.ManuscriptPole.KummerQuotientInjection.rationalDoublingSubgroup_eq_ker
#print axioms ZInQ.Contrib.OneProof.ManuscriptPole.KummerQuotientInjection.rationalDoublingSubgroup_eq_ker

/- Closed public signature: kummerClass_eq_zero_iff_mem_rationalDoublingSubgroup. -/
#check @ZInQ.Contrib.OneProof.ManuscriptPole.KummerQuotientInjection.kummerClass_eq_zero_iff_mem_rationalDoublingSubgroup
example : ∀ (ell : ℚ) (hell : ell ≠ 0)
    (P : (ZInQ.Manuscript.curve ell).toAffine.Point),
    kummerClass ell hell P = 0 ↔ P ∈ rationalDoublingSubgroup ell :=
  @ZInQ.Contrib.OneProof.ManuscriptPole.KummerQuotientInjection.kummerClass_eq_zero_iff_mem_rationalDoublingSubgroup
#print axioms ZInQ.Contrib.OneProof.ManuscriptPole.KummerQuotientInjection.kummerClass_eq_zero_iff_mem_rationalDoublingSubgroup

/- Closed public signature: mk_eq_zero_iff_mem_rationalDoublingSubgroup. -/
#check @ZInQ.Contrib.OneProof.ManuscriptPole.KummerQuotientInjection.mk_eq_zero_iff_mem_rationalDoublingSubgroup
example : ∀ (ell : ℚ) (P : (ZInQ.Manuscript.curve ell).toAffine.Point),
    (P : RationalTwoDescentQuotient ell) = 0 ↔ P ∈ rationalDoublingSubgroup ell :=
  @ZInQ.Contrib.OneProof.ManuscriptPole.KummerQuotientInjection.mk_eq_zero_iff_mem_rationalDoublingSubgroup
#print axioms ZInQ.Contrib.OneProof.ManuscriptPole.KummerQuotientInjection.mk_eq_zero_iff_mem_rationalDoublingSubgroup

/- Closed public signature: rationalKummerQuotientHom. -/
#check @ZInQ.Contrib.OneProof.ManuscriptPole.KummerQuotientInjection.rationalKummerQuotientHom
example : ∀ (ell : ℚ) (hell : ell ≠ 0),
    RationalTwoDescentQuotient ell →+
      continuousCohomology 1 (twoPowerTopRep ell hell 1) :=
  @ZInQ.Contrib.OneProof.ManuscriptPole.KummerQuotientInjection.rationalKummerQuotientHom
#print axioms ZInQ.Contrib.OneProof.ManuscriptPole.KummerQuotientInjection.rationalKummerQuotientHom

/- Closed public signature: rationalKummerQuotientHom_mk. -/
#check @ZInQ.Contrib.OneProof.ManuscriptPole.KummerQuotientInjection.rationalKummerQuotientHom_mk
example : ∀ (ell : ℚ) (hell : ell ≠ 0)
    (P : (ZInQ.Manuscript.curve ell).toAffine.Point),
    rationalKummerQuotientHom ell hell (P : RationalTwoDescentQuotient ell) =
      kummerClass ell hell P :=
  @ZInQ.Contrib.OneProof.ManuscriptPole.KummerQuotientInjection.rationalKummerQuotientHom_mk
#print axioms ZInQ.Contrib.OneProof.ManuscriptPole.KummerQuotientInjection.rationalKummerQuotientHom_mk

/- Closed public signature: rationalKummerQuotientHom_mk'. -/
#check @ZInQ.Contrib.OneProof.ManuscriptPole.KummerQuotientInjection.rationalKummerQuotientHom_mk'
example : ∀ (ell : ℚ) (hell : ell ≠ 0)
    (P : (ZInQ.Manuscript.curve ell).toAffine.Point),
    rationalKummerQuotientHom ell hell
        (QuotientAddGroup.mk' (rationalDoublingSubgroup ell) P) =
      kummerClass ell hell P :=
  @ZInQ.Contrib.OneProof.ManuscriptPole.KummerQuotientInjection.rationalKummerQuotientHom_mk'
#print axioms ZInQ.Contrib.OneProof.ManuscriptPole.KummerQuotientInjection.rationalKummerQuotientHom_mk'

/- Closed public signature: rationalKummerQuotientHom_comp_mk'. -/
#check @ZInQ.Contrib.OneProof.ManuscriptPole.KummerQuotientInjection.rationalKummerQuotientHom_comp_mk'
example : ∀ (ell : ℚ) (hell : ell ≠ 0),
    (rationalKummerQuotientHom ell hell).comp
        (QuotientAddGroup.mk' (rationalDoublingSubgroup ell)) =
      rationalKummerHom ell hell :=
  @ZInQ.Contrib.OneProof.ManuscriptPole.KummerQuotientInjection.rationalKummerQuotientHom_comp_mk'
#print axioms ZInQ.Contrib.OneProof.ManuscriptPole.KummerQuotientInjection.rationalKummerQuotientHom_comp_mk'

/- Closed public signature: rationalKummerQuotientHom_mk_eq_zero_iff. -/
#check @ZInQ.Contrib.OneProof.ManuscriptPole.KummerQuotientInjection.rationalKummerQuotientHom_mk_eq_zero_iff
example : ∀ (ell : ℚ) (hell : ell ≠ 0)
    (P : (ZInQ.Manuscript.curve ell).toAffine.Point),
    rationalKummerQuotientHom ell hell (P : RationalTwoDescentQuotient ell) = 0 ↔
      (P : RationalTwoDescentQuotient ell) = 0 :=
  @ZInQ.Contrib.OneProof.ManuscriptPole.KummerQuotientInjection.rationalKummerQuotientHom_mk_eq_zero_iff
#print axioms ZInQ.Contrib.OneProof.ManuscriptPole.KummerQuotientInjection.rationalKummerQuotientHom_mk_eq_zero_iff

/- Closed public signature: rationalKummerQuotientHom_injective. -/
#check @ZInQ.Contrib.OneProof.ManuscriptPole.KummerQuotientInjection.rationalKummerQuotientHom_injective
example : ∀ (ell : ℚ) (hell : ell ≠ 0),
    Function.Injective (rationalKummerQuotientHom ell hell) :=
  @ZInQ.Contrib.OneProof.ManuscriptPole.KummerQuotientInjection.rationalKummerQuotientHom_injective
#print axioms ZInQ.Contrib.OneProof.ManuscriptPole.KummerQuotientInjection.rationalKummerQuotientHom_injective

/- Closed public signature: rationalKummerQuotientHom_ker. -/
#check @ZInQ.Contrib.OneProof.ManuscriptPole.KummerQuotientInjection.rationalKummerQuotientHom_ker
example : ∀ (ell : ℚ) (hell : ell ≠ 0),
    (rationalKummerQuotientHom ell hell).ker = ⊥ :=
  @ZInQ.Contrib.OneProof.ManuscriptPole.KummerQuotientInjection.rationalKummerQuotientHom_ker
#print axioms ZInQ.Contrib.OneProof.ManuscriptPole.KummerQuotientInjection.rationalKummerQuotientHom_ker

/- The subgroup is the actual rational doubling range. -/
example (ell : ℚ) : rationalDoublingSubgroup ell =
    (nsmulAddMonoidHom (α := (ZInQ.Manuscript.curve ell).toAffine.Point) 2).range := rfl

/- The quotient is the public additive quotient of that same point group. -/
example (ell : ℚ) : RationalTwoDescentQuotient ell =
    ((ZInQ.Manuscript.curve ell).toAffine.Point ⧸ rationalDoublingSubgroup ell) := rfl

/- The canonical projection retains the public Kummer value. -/
example (ell : ℚ) (hell : ell ≠ 0)
    (P : (ZInQ.Manuscript.curve ell).toAffine.Point) :
    rationalKummerQuotientHom ell hell
      (QuotientAddGroup.mk' (rationalDoublingSubgroup ell) P) = kummerClass ell hell P :=
  rationalKummerQuotientHom_mk' ell hell P

/- Additivity is consumed from the descended homomorphism. -/
example (ell : ℚ) (hell : ell ≠ 0) (A B : RationalTwoDescentQuotient ell) :
    rationalKummerQuotientHom ell hell (A + B) =
      rationalKummerQuotientHom ell hell A + rationalKummerQuotientHom ell hell B :=
  map_add (rationalKummerQuotientHom ell hell) A B

/- Zero is preserved by the same descended homomorphism. -/
example (ell : ℚ) (hell : ell ≠ 0) :
    rationalKummerQuotientHom ell hell (0 : RationalTwoDescentQuotient ell) = 0 :=
  map_zero (rationalKummerQuotientHom ell hell)

/- Equality of image values is reflected by the public injection. -/
example (ell : ℚ) (hell : ell ≠ 0) (A B : RationalTwoDescentQuotient ell)
    (h : rationalKummerQuotientHom ell hell A = rationalKummerQuotientHom ell hell B) :
    A = B :=
  rationalKummerQuotientHom_injective ell hell h
