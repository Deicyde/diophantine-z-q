import ZInQKernel.Contrib.OneProof.ComplexPointDerivation
import ZInQKernel.Contrib.CloudB3W17bOkaComparison.PointClosedDictionary

/-! Values at the native complex points detect regular functions on affine
opens of a reduced complex scheme. -/

noncomputable section

open AlgebraicGeometry CategoryTheory

namespace AlgebraicGeometry.ComplexPoint

open ZInQ.Contrib.CloudB3W17bOkaComparison

/-- If a regular function on an affine open of a reduced complex scheme of
finite type vanishes at every complex point of the open, it is zero. -/
theorem regularSection_eq_zero_of_evaluate_eq_zero
    {X : Over (Spec (CommRingCat.of ℂ))} [LocallyOfFiniteType X.hom] [IsReduced X.left]
    {U : X.left.Opens} (hU : IsAffineOpen U) (a : Γ(X.left, U))
    (ha : ∀ p : ComplexPoint X, p.underlying ∈ U → Point.evaluate U a p = 0) :
    a = 0 := by
  have hJac : JacobsonSpace X.left := LocallyOfFiniteType.jacobsonSpace X.hom
  have hB : X.left.basicOpen a = ⊥ := by
    apply le_bot_iff.mp
    intro x hx
    obtain ⟨y, hy, hcl⟩ := nonempty_inter_closedPoints
      (show ((X.left.basicOpen a : X.left.Opens) : Set X.left).Nonempty from ⟨x, hx⟩)
      (X.left.basicOpen a).isOpen.isLocallyClosed
    let p := (nativePointClosedEquiv X).symm ⟨y, hcl⟩
    have hp : p.underlying = y := congrArg Subtype.val
      ((nativePointClosedEquiv X).apply_symm_apply ⟨y, hcl⟩)
    have hpb : p.underlying ∈ X.left.basicOpen a := hp.symm ▸ hy
    have hpU : p.underlying ∈ U := X.left.basicOpen_le a hpb
    have hun := (Point.mem_overOpen_basicOpen_iff_isUnit_evaluate a p hpU).mp hpb
    exact False.elim (hun.ne_zero (ha p hpU))
  exact ((Scheme.isNilpotent_iff_basicOpen_eq_bot_of_isCompact hU.isCompact a).mpr hB).eq_zero

end AlgebraicGeometry.ComplexPoint

#print axioms AlgebraicGeometry.ComplexPoint.regularSection_eq_zero_of_evaluate_eq_zero
