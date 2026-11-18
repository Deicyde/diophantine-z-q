import ZInQKernel.Contrib.CloudR2Poincare.L3.KernelGeometry
import ZInQKernel.Contrib.CloudR2Poincare.L3.Cartier
import ZInQKernel.Contrib.CloudR2Poincare.L3.Vendor.StacksFrontier.AlgebraicGeometry.Variety.Geometrically.ConnectedPoint
import ZInQKernel.Contrib.TauCeti.AlgebraicGeometry.Morphisms.Smooth.GeometricallyIntegral
import ZInQKernel.Contrib.CloudR2Poincare.L3.InstanceScope

#cloudR2LocalInstances

/-!
# The actual connected kernel component as an abelian variety

Credited reuse: group/component construction from `scratch/av-glue/Kernel.lean`
at df98652a; modified 2026-11-14 by L3 to supply actual proved Cartier and 04KV
inputs rather than any scratch leaf. The reduced structure needs no replacement:
Cartier makes the kernel smooth, and the connected open component is integral.
-/

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
namespace ZInQ.Contrib.CloudR2Poincare.L3
#cloudR2LocalInstances
set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false

section Identity
#cloudR2LocalInstances
variable {k : Type} [Field k] {A B : _root_.PkgI3.AbVar k} (h : A.X ⟶ B.X) [IsMonHom h]

/-- A connected component of the kernel contains the rational unit and is geometrically connected. -/
theorem geomConn_cov : GeometricallyConnected (covOver h).hom := by
  exact StacksPort.AlgebraicGeometry.geometricallyConnected_of_connectedSpace_of_section
    (covOver h).hom (oneCov h).left (Over.w (oneCov h))

lemma one_eq_eta : (1 : 𝟙_ (Over (Spec (CommRingCat.of k))) ⟶ kerOver h) = η[kerOver h] := by
  rw [Hom.one_def, show toUnit (𝟙_ (Over (Spec (CommRingCat.of k)))) = 𝟙 _
    from toUnit_unique _ _, Category.id_comp]

theorem exists_mulCov : ∃ m : covOver h ⊗ covOver h ⟶ covOver h,
    m ≫ jK h = fst _ _ ≫ jK h * snd _ _ ≫ jK h := by
  haveI := geomConn_cov h
  haveI : ConnectedSpace (covOver h ⊗ covOver h).left :=
    (inferInstance : ConnectedSpace (pullback (C := Scheme.{0}) (covOver h).hom (covOver h).hom))
  refine ⟨liftCov h _ (range_sub h _ ((lift (oneCov h) (oneCov h)).left
    (Nonempty.some (inferInstance : Nonempty (Spec (CommRingCat.of k))))) ?_), liftCov_jK _ _ _⟩
  rw [← Scheme.Hom.comp_apply, ← Over.comp_left, MonObj.comp_mul, ← Category.assoc,
    ← Category.assoc, lift_fst, lift_snd, oneCov_jK, ← one_eq_eta, _root_.mul_one, one_eq_eta, ePt]

theorem exists_invCov : ∃ v : covOver h ⟶ covOver h, v ≫ jK h = (jK h)⁻¹ := by
  refine ⟨liftCov h _ (range_sub h _ ((oneCov h).left
    (Nonempty.some (inferInstance : Nonempty (Spec (CommRingCat.of k))))) ?_), liftCov_jK _ _ _⟩
  rw [← Scheme.Hom.comp_apply, ← Over.comp_left, GrpObj.comp_inv, oneCov_jK, ← one_eq_eta,
    inv_one, one_eq_eta, ePt]

/-- The group structure of `(ker h)⁰`. -/
noncomputable abbrev covGrp : GrpObj (covOver h) :=
  grpObjOfMono (jK h) (exists_mulCov h).choose (exists_mulCov h).choose_spec
    (oneCov h) (oneCov_jK h) (exists_invCov h).choose (exists_invCov h).choose_spec


/-- The component inclusion is a group homomorphism for the proved component group structure. -/
theorem isMonHom_jK : letI := covGrp h; IsMonHom (jK h) :=
  isMonHom_grpObjOfMono (jK h) (exists_mulCov h).choose (exists_mulCov h).choose_spec
    (oneCov h) (oneCov_jK h) (exists_invCov h).choose (exists_invCov h).choose_spec

/-- Cartier applies to the actual kernel group constructed in KernelGeometry. -/
theorem smooth_ker [CharZero k] : Smooth (kerOver h).hom :=
  cartierSmooth_proof k (kerOver h) inferInstance

/-- The connected kernel component, with all AbVar fields actually supplied. -/
noncomputable abbrev covAbVar [CharZero k] : _root_.PkgI3.AbVar k :=
  letI := covGrp h
  haveI : IsProper (covOver h).hom := identityComponent_proper h
  haveI : Smooth (kerOver h).hom := smooth_ker h
  haveI : Smooth (covOver h).hom := by
    change Smooth ((U0 h).ι ≫ (kerOver h).hom)
    infer_instance
  haveI : GeometricallyConnected (covOver h).hom := geomConn_cov h
  haveI : GeometricallyIntegral (covOver h).hom :=
    TauCeti.AlgebraicGeometry.Smooth.geometricallyIntegral _
  { X := covOver h }

/-- The closed component inclusion as a homomorphism of abelian varieties. -/
noncomputable def covHom [CharZero k] : _root_.PkgI3.AbVar.Hom (covAbVar h) A :=
  letI := covGrp h
  haveI : IsMonHom (jK h) := isMonHom_jK h
  _root_.PkgI3.AbVar.Hom.mk' (jK h ≫ kerι h)

@[simp] theorem covHom_hom [CharZero k] : (covHom h).hom = jK h ≫ kerι h := rfl

theorem covHom_killed [CharZero k] : (covHom h).hom ≫ h = 1 := by
  rw [covHom_hom, Category.assoc, kerι_comp, MonObj.comp_one]

theorem covHom_closed [CharZero k] : IsClosedImmersion (covHom h).hom.left := by
  rw [covHom_hom]
  exact identityInclusion_closed h

end Identity
end ZInQ.Contrib.CloudR2Poincare.L3
