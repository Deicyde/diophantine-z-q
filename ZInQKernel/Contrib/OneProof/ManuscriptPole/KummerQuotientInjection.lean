import ZInQKernel.Contrib.OneProof.ManuscriptPole.GaloisCoefficients
import ZInQKernel.Contrib.OneProof.ManuscriptPole.KummerCocycle
import ZInQKernel.Contrib.OneProof.ManuscriptPole.KummerExactness
import Mathlib.RepresentationTheory.Homological.ContCohomology.Basic
import Mathlib.GroupTheory.QuotientGroup.Defs
import Mathlib.Algebra.Group.Subgroup.Ker
import Mathlib.Algebra.Group.Hom.Basic

/-!
# The rational two-descent quotient injects into continuous cohomology

The rational Kummer homomorphism kills exactly the actual doubles of rational
points. Dividing its source by that actual doubling subgroup therefore
descends it, and the descended additive homomorphism is injective.

The quotient taken here is the additive quotient of the raw rational point
group of the manuscript curve by the range of actual doubling on that same
group. The target is unchanged: the canonical continuous degree-one
cohomology of the existing finite coefficient representation. The descended
map composed with the canonical projection is the original Kummer
homomorphism, and its value on the class of an actual rational point is the
original Kummer class of that point.

Only the algebraic injection is proved. No local condition, Selmer group,
restriction or localisation map, surjectivity, isomorphism, finiteness,
finite rank, finite cardinality, topological description of the image, or
identification with a connecting homomorphism is asserted.
-/

set_option autoImplicit false

open scoped Classical

noncomputable section

namespace ZInQ.Contrib.OneProof.ManuscriptPole.KummerQuotientInjection

open ZInQ.Contrib.OneProof.ManuscriptPole.GaloisCoefficients
open ZInQ.Contrib.OneProof.ManuscriptPole.KummerCocycle
open ZInQ.Contrib.OneProof.ManuscriptPole.KummerExactness

/-- The actual doubling subgroup of the raw rational point group, written as the
range of the public multiplication-by-two additive homomorphism on that same
group. This is the identical term occurring in the existing kernel theorem. -/
def rationalDoublingSubgroup (ell : ℚ) :
    AddSubgroup ((ZInQ.Manuscript.curve ell).toAffine.Point) :=
  (nsmulAddMonoidHom (α := (ZInQ.Manuscript.curve ell).toAffine.Point) 2).range

/-- Membership in the doubling subgroup is literally being an actual rational double. -/
theorem mem_rationalDoublingSubgroup (ell : ℚ)
    (P : (ZInQ.Manuscript.curve ell).toAffine.Point) :
    P ∈ rationalDoublingSubgroup ell ↔
      ∃ R : (ZInQ.Manuscript.curve ell).toAffine.Point, (2 : ℕ) • R = P := by
  have hmem : P ∈ rationalDoublingSubgroup ell ↔
      ∃ R : (ZInQ.Manuscript.curve ell).toAffine.Point,
        nsmulAddMonoidHom (α := (ZInQ.Manuscript.curve ell).toAffine.Point) 2 R = P :=
    AddMonoidHom.mem_range
  exact hmem

/-- The actual additive quotient of the raw rational point group by actual doubling. -/
abbrev RationalTwoDescentQuotient (ell : ℚ) : Type :=
  (ZInQ.Manuscript.curve ell).toAffine.Point ⧸ rationalDoublingSubgroup ell

/-- The doubling subgroup is exactly the kernel of the existing rational Kummer
homomorphism. This is the existing exactness result, read in the other direction. -/
theorem rationalDoublingSubgroup_eq_ker (ell : ℚ) (hell : ell ≠ 0) :
    rationalDoublingSubgroup ell = (rationalKummerHom ell hell).ker :=
  (rationalKummerHom_ker ell hell).symm

/-- Vanishing of the existing Kummer class is membership in the doubling subgroup. -/
theorem kummerClass_eq_zero_iff_mem_rationalDoublingSubgroup (ell : ℚ) (hell : ell ≠ 0)
    (P : (ZInQ.Manuscript.curve ell).toAffine.Point) :
    kummerClass ell hell P = 0 ↔ P ∈ rationalDoublingSubgroup ell := by
  rw [mem_rationalDoublingSubgroup ell P]
  exact kummerClass_eq_zero_iff_two_nsmul ell hell P

/-- A rational point has zero class in the actual quotient exactly when it is an
actual rational double. -/
theorem mk_eq_zero_iff_mem_rationalDoublingSubgroup (ell : ℚ)
    (P : (ZInQ.Manuscript.curve ell).toAffine.Point) :
    (P : RationalTwoDescentQuotient ell) = 0 ↔ P ∈ rationalDoublingSubgroup ell :=
  QuotientAddGroup.eq_zero_iff P

/-- The descended rational Kummer homomorphism on the actual two-descent quotient.
Well-definedness is the existing kernel theorem; the target is the same canonical
continuous degree-one cohomology of the same coefficient representation. -/
def rationalKummerQuotientHom (ell : ℚ) (hell : ell ≠ 0) :
    RationalTwoDescentQuotient ell →+
      continuousCohomology 1 (twoPowerTopRep ell hell 1) :=
  QuotientAddGroup.lift (rationalDoublingSubgroup ell) (rationalKummerHom ell hell)
    (rationalDoublingSubgroup_eq_ker ell hell).le

/-- The literal value on the class of an actual rational point is the existing class. -/
theorem rationalKummerQuotientHom_mk (ell : ℚ) (hell : ell ≠ 0)
    (P : (ZInQ.Manuscript.curve ell).toAffine.Point) :
    rationalKummerQuotientHom ell hell (P : RationalTwoDescentQuotient ell) =
      kummerClass ell hell P :=
  (QuotientAddGroup.lift_mk (N := rationalDoublingSubgroup ell)
      (φ := rationalKummerHom ell hell)
      (rationalDoublingSubgroup_eq_ker ell hell).le P).trans
    (rationalKummerHom_apply ell hell P)

/-- The same value through the canonical projection homomorphism. -/
theorem rationalKummerQuotientHom_mk' (ell : ℚ) (hell : ell ≠ 0)
    (P : (ZInQ.Manuscript.curve ell).toAffine.Point) :
    rationalKummerQuotientHom ell hell
        (QuotientAddGroup.mk' (rationalDoublingSubgroup ell) P) =
      kummerClass ell hell P := by
  rw [QuotientAddGroup.mk'_apply]
  exact rationalKummerQuotientHom_mk ell hell P

/-- The descended homomorphism factors the existing one: nothing is replaced. -/
theorem rationalKummerQuotientHom_comp_mk' (ell : ℚ) (hell : ell ≠ 0) :
    (rationalKummerQuotientHom ell hell).comp
        (QuotientAddGroup.mk' (rationalDoublingSubgroup ell)) =
      rationalKummerHom ell hell :=
  QuotientAddGroup.lift_comp_mk' (rationalDoublingSubgroup ell)
    (rationalKummerHom ell hell) (rationalDoublingSubgroup_eq_ker ell hell).le

/-- A class of the actual quotient dies in the canonical continuous cohomology
exactly when it is already zero in that quotient. -/
theorem rationalKummerQuotientHom_mk_eq_zero_iff (ell : ℚ) (hell : ell ≠ 0)
    (P : (ZInQ.Manuscript.curve ell).toAffine.Point) :
    rationalKummerQuotientHom ell hell (P : RationalTwoDescentQuotient ell) = 0 ↔
      (P : RationalTwoDescentQuotient ell) = 0 := by
  rw [rationalKummerQuotientHom_mk ell hell P,
    mk_eq_zero_iff_mem_rationalDoublingSubgroup ell P]
  exact kummerClass_eq_zero_iff_mem_rationalDoublingSubgroup ell hell P

/-- The actual two-descent quotient injects into the existing canonical continuous
degree-one cohomology of the existing coefficient representation. -/
theorem rationalKummerQuotientHom_injective (ell : ℚ) (hell : ell ≠ 0) :
    Function.Injective (rationalKummerQuotientHom ell hell) :=
  (QuotientAddGroup.injective_lift_iff (rationalDoublingSubgroup ell)
      (rationalKummerHom ell hell)
      (rationalDoublingSubgroup_eq_ker ell hell).le).mpr
    (rationalDoublingSubgroup_eq_ker ell hell)

/-- Equivalently, the descended homomorphism has trivial kernel. -/
theorem rationalKummerQuotientHom_ker (ell : ℚ) (hell : ell ≠ 0) :
    (rationalKummerQuotientHom ell hell).ker = ⊥ :=
  AddMonoidHom.ker_eq_bot (rationalKummerQuotientHom ell hell)
    (rationalKummerQuotientHom_injective ell hell)

end ZInQ.Contrib.OneProof.ManuscriptPole.KummerQuotientInjection
