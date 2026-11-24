import ZInQKernel.Contrib.CloudR2Poincare.L4.ProductGeometry
import ZInQKernel.Contrib.CloudR2Poincare.L4.FibreStalk
import ZInQKernel.Contrib.CloudR2Poincare.L3.Vendor.StacksFrontier.AlgebraicGeometry.Variety.Defs.Dimension.NonemptyOpen
import ZInQKernel.Contrib.CloudR2Poincare.L3.Vendor.StacksFrontier.AlgebraicGeometry.Variety.Defs.Dimension.ClosedPoint
import ZInQKernel.Contrib.CloudR2Poincare.Skeleton

/-!
# The product-dimension lower bound for the actual abelian varieties

H-72 round 2, lane L4. This proves precisely the dimension bound the fixed
complement isogeny needs, using the rational identity points of the actual
`Over (Spec k)` objects. At `lift η[B] η[Z]`, the actual first projection is
flat and its scheme-theoretic fibre is canonically `Z`; its local-ring
dimension is therefore `dim B + dim Z`. A local ring's dimension is at most
the global dimension of the actual product scheme.

This avoids the generic 0B2M field-extension/Composite import tree. It does
not replace the varieties or the sum by an abstract group or torus.
-/

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj

noncomputable section

namespace ZInQ.Contrib.CloudR2Poincare.L4

set_option linter.style.haveILetI false

/-- The dimension of an abelian variety is the dimension of its local ring at its rational identity point. -/
theorem abVar_dim_eq_stalk_unit {k : Type} [Field k] (A : _root_.PkgI3.AbVar k)
    (x : Spec (.of k)) : A.dim = ringKrullDim (A.X.left.presheaf.stalk ((η[A.X]).left x)) := by
  haveI : IsIntegral A.X.left := GeometricallyIntegral.isIntegral_of_subsingleton A.X.hom
  change topologicalKrullDim A.X.left = _
  exact
    (ZInQ.Contrib.CloudR2Poincare.L3.StacksPort.AlgebraicGeometry.topologicalKrullDim_eq_topologicalKrullDimAt_of_irreducible
      k A.X.left A.X.hom ((η[A.X]).left x)).trans
    (ZInQ.Contrib.CloudR2Poincare.L3.StacksPort.AlgebraicGeometry.topologicalKrullDimAt_eq_krullDimOfRing_stalk
      k A.X.left A.X.hom ((η[A.X]).left x) (isClosed_unitPoint A.X x))

/-- The actual product of the two abelian varieties has dimension at least the sum of their dimensions. -/
theorem product_dimension_lower_bound {k : Type} [Field k] (B Z : _root_.PkgI3.AbVar k) :
    B.dim + Z.dim ≤ topologicalKrullDim (B.X ⊗ Z.X).left := by
  let x : Spec (.of k) := IsLocalRing.closedPoint k
  let p := productUnitPoint B.X Z.X x
  let f := (fst B.X Z.X).left
  have hp : f p = (η[B.X]).left x := productUnitPoint_fst B.X Z.X x
  haveI : IsProper (B.X ⊗ Z.X).hom := by dsimp; infer_instance
  haveI : IsLocallyNoetherian (B.X ⊗ Z.X).left :=
    LocallyOfFiniteType.isLocallyNoetherian (B.X ⊗ Z.X).hom
  haveI : IsLocallyNoetherian B.X.left := LocallyOfFiniteType.isLocallyNoetherian B.X.hom
  haveI : Flat f := inferInstanceAs (Flat (pullback.fst B.X.hom Z.X.hom))
  let e := productUnitFibreIso B.X Z.X x
  let a : f.fiber ((η[B.X]).left x) := (f.fiberHomeo ((η[B.X]).left x)).symm ⟨p, hp⟩
  have hpoint : e.hom a = (η[Z.X]).left x := by
    rw [productUnitFibreIso_hom, Scheme.Hom.comp_apply]
    change (snd B.X Z.X).left
      (f.fiberι ((η[B.X]).left x) ((f.fiberHomeo ((η[B.X]).left x)).symm ⟨p, hp⟩)) = _
    rw [Scheme.Hom.fiberι_fiberHomeo_symm]
    exact productUnitPoint_snd B.X Z.X x
  have hFib : ringKrullDim ((f.fiber (f p)).presheaf.stalk (f.asFiber p)) =
      ringKrullDim (Z.X.left.presheaf.stalk ((η[Z.X]).left x)) := by
    have hd := ringKrullDim_eq_of_ringEquiv
      (asIso (e.hom.stalkMap a)).commRingCatIsoToRingEquiv
    rw [hpoint] at hd
    exact (ringKrullDim_stalk_fiberHomeo_symm f p ((η[B.X]).left x) hp).symm.trans hd.symm
  have hdim := flat_stalk_dimension f p
  rw [hFib, hp] at hdim
  calc
    B.dim + Z.dim = ringKrullDim ((B.X ⊗ Z.X).left.presheaf.stalk p) := by
      rw [abVar_dim_eq_stalk_unit B x, abVar_dim_eq_stalk_unit Z x]
      exact hdim.symm
    _ ≤ topologicalKrullDim (B.X ⊗ Z.X).left :=
      ringKrullDim_stalk_le_topologicalKrullDim _ p

end ZInQ.Contrib.CloudR2Poincare.L4
