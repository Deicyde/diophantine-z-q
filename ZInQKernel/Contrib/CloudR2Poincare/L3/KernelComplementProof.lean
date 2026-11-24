import ZInQKernel.Contrib.CloudR2Poincare.L3.KernelIdentity
import ZInQKernel.Contrib.CloudR2Poincare.L3.KernelFibreGeometry
import ZInQKernel.Contrib.CloudR2Poincare.L3.EmbeddingDimension
import ZInQKernel.Contrib.CloudR2Poincare.L4.ProductDimension
import ZInQKernel.Contrib.CloudR2Poincare.Skeleton
import ZInQKernel.Contrib.CloudR2Poincare.L3.InstanceScope

#cloudR2LocalInstances

/-!
# The exact KernelComplement obligation

The dimension count uses proved embedding-dimension subadditivity, regularity of
smooth stalks, the scheme-theoretic unit-fibre/kernel isomorphism, and L4's proved
quotient-stalk bridge. It needs no desired fibre-dimension/equidimension fact.
-/

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj

namespace ZInQ.Contrib.CloudR2Poincare.L3
#cloudR2LocalInstances

set_option linter.style.haveILetI false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

section Dimension
#cloudR2LocalInstances
variable {k : Type} [Field k] [CharZero k] {A B : _root_.PkgI3.AbVar k}
    (h : A.X ⟶ B.X) [IsMonHom h]

/-- The unit local ring of the kernel is the local ring of its open identity component. -/
theorem kernel_unit_stalk_le_component_dim (x : Spec (.of k)) :
    ringKrullDim ((kerOver h).left.presheaf.stalk (ePt h)) ≤
      topologicalKrullDim (covOver h).left := by
  let p : (covOver h).left := (oneCov h).left x
  have hp : (jK h).left p = ePt h := by
    have H := congrArg Over.Hom.left (oneCov_jK h)
    simp only [Over.comp_left] at H
    have HH := congrArg (fun f => f x) H
    simpa only [Scheme.Hom.comp_apply, ePt_eq_unit h x] using HH
  haveI : IsOpenImmersion (jK h).left := by
    change IsOpenImmersion (U0 h).ι
    infer_instance
  have he := ringKrullDim_eq_of_ringEquiv
    (asIso ((jK h).left.stalkMap p)).commRingCatIsoToRingEquiv
  rw [hp] at he
  exact he.trans_le
    (ZInQ.Contrib.CloudR2Poincare.L4.ringKrullDim_stalk_le_topologicalKrullDim _ p)

/-- The exact dimension inequality for the actual connected kernel component. -/
theorem dimension_kernel_component : A.dim ≤ (covAbVar h).dim + B.dim := by
  let x : Spec (.of k) := IsLocalRing.closedPoint k
  let u : A.X.left := (η[A.X]).left x
  let f := h.left
  let q : f.fiber (f u) := f.asFiber u
  let e := kernelUnitFibreIso h x
  have hept : e.hom q = ePt h := kernelUnitFibreIso_point h x
  haveI : Smooth (kerOver h).hom := smooth_ker h
  haveI : IsRegularLocalRing ((kerOver h).left.presheaf.stalk (e.hom q)) :=
    TauCeti.AlgebraicGeometry.isRegularLocalRing_stalk_of_smooth (kerOver h).hom (e.hom q)
  let R := B.X.left.presheaf.stalk (f u)
  let S := A.X.left.presheaf.stalk u
  let F := (f.fiber (f u)).presheaf.stalk q
  letI : Algebra R S := (f.stalkMap u).hom.toAlgebra
  haveI : IsLocalHom (algebraMap R S) :=
    inferInstanceAs (IsLocalHom (f.stalkMap u).hom)
  haveI : IsRegularLocalRing R :=
    TauCeti.AlgebraicGeometry.isRegularLocalRing_stalk_of_smooth B.X.hom (f u)
  haveI : IsRegularLocalRing S :=
    TauCeti.AlgebraicGeometry.isRegularLocalRing_stalk_of_smooth A.X.hom u
  let eKF := (asIso (e.hom.stalkMap q)).commRingCatIsoToRingEquiv
  haveI : IsRegularLocalRing F := IsRegularLocalRing.of_ringEquiv eKF
  let eQF := ZInQ.Contrib.CloudR2Poincare.L4.quotientStalkEquivFiberStalk f u
  haveI : IsRegularLocalRing (StacksPort.ClosedFibre R S) :=
    IsRegularLocalRing.of_ringEquiv eQF.symm
  have hlocal : ringKrullDim S ≤ ringKrullDim R + ringKrullDim F := by
    have H := regular_local_dimension_le_closedFibre R S
    have hQ : ringKrullDim (StacksPort.ClosedFibre R S) = ringKrullDim F :=
      ringKrullDim_eq_of_ringEquiv eQF
    simpa only [hQ] using H
  have hF : ringKrullDim F ≤ (covAbVar h).dim := by
    have H := ringKrullDim_eq_of_ringEquiv eKF
    rw [hept] at H
    change ringKrullDim F ≤ topologicalKrullDim (covOver h).left
    exact H.symm.trans_le (kernel_unit_stalk_le_component_dim h x)
  have hR : ringKrullDim R ≤ B.dim :=
    ZInQ.Contrib.CloudR2Poincare.L4.ringKrullDim_stalk_le_topologicalKrullDim B.X.left (f u)
  calc
    A.dim = ringKrullDim S := ZInQ.Contrib.CloudR2Poincare.L4.abVar_dim_eq_stalk_unit A x
    _ ≤ ringKrullDim R + ringKrullDim F := hlocal
    _ ≤ B.dim + (covAbVar h).dim := add_le_add hR hF
    _ = (covAbVar h).dim + B.dim := add_comm _ _

end Dimension

/-- The fixed H72 L3 obligation, with no additional hypotheses. -/
theorem KernelComplement_proof : ZInQ.Contrib.CloudR2Poincare.KernelComplement := by
  intro k _ _ J D φ
  refine ⟨covAbVar φ.hom, covHom φ.hom, ?_, ?_, ?_⟩
  · exact covHom_killed φ.hom
  · exact covHom_closed φ.hom
  · exact dimension_kernel_component φ.hom

end ZInQ.Contrib.CloudR2Poincare.L3
