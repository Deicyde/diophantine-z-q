/-
NEW EDITION: Lane2 world004 inversion reference repair, 2026-11-17.
Base NativeInversionReduction.lean:
9d4e93a68e96b79e590b781331e5198dd146237789c38d1287c88020a5c2d946.
The base and its failed world004 proof history remain unchanged.
NativeCubeUnitReduction declares the same namespace used below. The
qualified identifier was split after its namespace-dot across two lines;
join it into one identifier, with argument wrapping only after that token.
Public statements, namespace, all native maps and universe u are unchanged.
UNCOMPILED new Source. Parent probes it; no lane compile or Native run.
-/
/-
H5 original-input Step2 / GM7: native binary-product-to-inversion reduction.
Copyright (c) 2026 H5 lane2 contributors. Apache-2.0.

NEW Source-only / UNCOMPILED. This proves the final genuine restriction/map
calculation for I5b once C3's GM1 seesaw has supplied the ACTUAL binary-product
isomorphism. No seesaw/cube/square Fact or factory is installed, no pending
producer is claimed proved, and this is not the full I5b endpoint.

Named pending earlier producer: C3 Step1.Interfaces.SeesawPulledBack,
actual Source Interfaces.lean dd093d6f (native slice-trivial -> pulled-base-line
contract, not a proved theorem). For invariant Q it must be applied to
mu^*Q tensor p1^*(Q-dual), then native cancellation supplies the isomorphism
consumed below. This file does NOT duplicate the GM1 proof or its assembly.

All operations are W07 native Scheme.Modules pullback/tensor/unit; group
inversion and multiplication are the SAME original Grp object. Symbolic u,
any field characteristic, any abelian dimension (the helper is stronger:
no properness, smoothness or abelian-variety predicate is needed).
Existing licences/attributions of native primitives stay unchanged.
-/
import NativeCubeUnitReduction
import ZInQKernel.Contrib.CloudW07JacobiansCurves.Jacobian.AlgebraicGeometry.Modules.PullbackMonoidal

set_option autoImplicit false
noncomputable section
universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
  CategoryTheory.CartesianMonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.MonObj AlgebraicGeometry.Scheme.Modules

namespace H5OriginalDVR.Lane2.NativeInversionReduction

/-- Restrict the ACTUAL product-law isomorphism along (id,inversion). The
multiplication composite is the original constant identity section; pulling
a native line through that field-valued point is the native unit. This is
ordinary isomorphism data, not an added seesaw or inversion premise in NOS. -/
theorem inversion_tensor_iso_unit_of_actual_binary_product_iso
    {K : Type u} [Field K]
    (A : Grp (Over (Spec (CommRingCat.of K))))
    (Q : A.X.left.Modules) [Q.IsInvertible]
    (e : (Scheme.Modules.pullback μ[A.X].left).obj Q ≅
      (Scheme.Modules.pullback (fst A.X A.X).left).obj Q ⊗
        (Scheme.Modules.pullback (snd A.X A.X).left).obj Q) :
    Nonempty ((Scheme.Modules.pullback (ι[A.X]).left).obj Q ⊗ Q ≅
      Scheme.Modules.unit A.X.left) := by
  let d := (lift (𝟙 A.X) ι[A.X]).left
  let p1 := (fst A.X A.X).left
  let p2 := (snd A.X A.X).left
  let m := μ[A.X].left
  let i := ι[A.X].left
  have h1 : d ≫ p1 = 𝟙 A.X.left := by
    dsimp only [d, p1]
    rw [← Over.comp_left, lift_fst, Over.id_left]
  have h2 : d ≫ p2 = i := by
    dsimp only [d, p2, i]
    rw [← Over.comp_left, lift_snd]
  have hm : d ≫ m = A.X.hom ≫ η[A.X].left := by
    have h := congrArg (fun f : A.X ⟶ A.X => f.left) (GrpObj.right_inv A.X)
    simpa only [d, m, Over.comp_left, Over.toUnit_left] using h
  let e1 : (Scheme.Modules.pullback d).obj
      ((Scheme.Modules.pullback p1).obj Q) ≅ Q :=
    (Scheme.Modules.pullbackComp d p1).app Q ≪≫
      (Scheme.Modules.pullbackCongr h1).app Q ≪≫ (Scheme.Modules.pullbackId A.X.left).app Q
  let e2 : (Scheme.Modules.pullback d).obj
      ((Scheme.Modules.pullback p2).obj Q) ≅ (Scheme.Modules.pullback i).obj Q :=
    (Scheme.Modules.pullbackComp d p2).app Q ≪≫ (Scheme.Modules.pullbackCongr h2).app Q
  let eright : (Scheme.Modules.pullback d).obj
      ((Scheme.Modules.pullback m).obj Q) ≅
      (Scheme.Modules.pullback i).obj Q ⊗ Q :=
    (Scheme.Modules.pullback d).mapIso e ≪≫
      Scheme.Modules.pullbackTensorObjIso d
        ((Scheme.Modules.pullback p1).obj Q) ((Scheme.Modules.pullback p2).obj Q) ≪≫
      (e1 ⊗ᵢ e2) ≪≫ β_ Q ((Scheme.Modules.pullback i).obj Q)
  obtain ⟨ec⟩ := H5OriginalDVR.Lane2.NativeCubeUnitReduction.nonempty_pullback_iso_unit_through_field_point
    A.X.hom η[A.X].left Q
  let eleft : (Scheme.Modules.pullback d).obj
      ((Scheme.Modules.pullback m).obj Q) ≅ Scheme.Modules.unit A.X.left :=
    (Scheme.Modules.pullbackComp d m).app Q ≪≫
      (Scheme.Modules.pullbackCongr hm).app Q ≪≫ ec
  exact ⟨eright.symm ≪≫ eleft⟩

end H5OriginalDVR.Lane2.NativeInversionReduction
