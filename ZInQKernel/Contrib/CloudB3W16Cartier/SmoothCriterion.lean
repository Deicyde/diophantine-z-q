/-
Adapted from AxiomMath/Stacks c496df0d9beea9deaeabcea8492605f9a0a2313b,
StacksFrontier/AlgebraicGeometry/Variety/SmoothOverField/LocallyFreeDifferentials.lean,
lines 51–140. Source SHA256: ef384b01ccb62660e40ec6ddde792e5f6485784fb59661f05dfd794a6867df29.
Apache-2.0; see LICENSE and NOTICE.md. Changes: isolate declarations,
remove citation attributes, use the pruned 00TX/00TV local criterion.
-/
import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.AlgebraicGeometry.Noetherian
import ZInQKernel.Contrib.CloudB3W16Cartier.CharZeroRegularity
import ZInQKernel.Contrib.CloudB3W16Cartier.Vendor.StacksFrontier.AlgebraicGeometry.RelativeDifferentialStalkMap.Scheme
import ZInQKernel.Contrib.CloudB3W16Cartier.Vendor.StacksFrontier.AlgebraicGeometry.StalkFreeBridge.StalkFree
import ZInQKernel.Contrib.CloudB3W16Cartier.Vendor.StacksFrontier.RingTheory.Kaehler.BaseChange

namespace ZInQ.Contrib.CloudB3W16Cartier.Vendor
open _root_.AlgebraicGeometry _root_.CategoryTheory
open CategoryTheory TopologicalSpace
open Stacks.RelativeDifferentialStalkMap

universe u

namespace AlgebraicGeometry

/-- The stalk at a point of the sheaf of relative differentials of a morphism with locally free
relative differentials is a free module over the local ring of the source at that point, in the
spelling `Ω[𝒪_{X,x}⁄𝒪_{S,f x}]` of the Kähler differentials of the stalk map. -/
private theorem free_kaehlerDifferential_stalkMap_of_isLocallyFree
    {X S : Scheme.{u}} (f : X ⟶ S)
    (hΩ : _root_.SheafOfModules.IsLocallyFree.{u, u, u} (Scheme.Hom.relativeDifferentials f)) (x : X) :
    let _ := algebraStalkMap f x
    Module.Free (ToType (X.sheaf.presheaf.stalk x))
      (KaehlerDifferential (ToType (S.presheaf.stalk (f x)))
        (ToType (X.sheaf.presheaf.stalk x))) := by
  classical
  let := algebraStalkMap f x
  have := hΩ
  exact (Stacks.StalkFreeBridge.free_stalk_of_isLocallyFree.{u}
    (Scheme.Hom.relativeDifferentials f) x).of_equiv (relativeDifferentialsStalkKaehlerEquiv f x)

/-- The stalk map of a morphism from a scheme locally of finite type over a characteristic-zero
field with locally free relative differentials is formally smooth at every point.

On an affine chart `V` of the source the local ring at the point is the localization of `Γ(X, V)`
at the corresponding prime, `Γ(X, V)` is a finite type algebra over the field, and the Kähler
differentials of that localization over the field are free; Stacks Tag 00TX then gives smoothness
at the prime, which is formal smoothness of the stalk map. -/
private theorem formallySmooth_stalkMap_of_isLocallyFree_relativeDifferentials
    {k : Type u} [Field k] [CharZero k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))
    [LocallyOfFiniteType f]
    (hΩ : _root_.SheafOfModules.IsLocallyFree.{u, u, u} (Scheme.Hom.relativeDifferentials f)) (x : X) :
    (f.stalkMap x).hom.FormallySmooth := by
  classical
  let U : (Spec (.of k)).Opens := ⊤
  have hU : IsAffineOpen U := isAffineOpen_top _
  have hxU : f x ∈ U := trivial
  obtain ⟨_, ⟨V, hV, rfl⟩, hxV, -⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
  have hVU : V ≤ f ⁻¹ᵁ U := fun _ _ => trivial
  let R := ToType Γ(Spec (.of k), U)
  let A := ToType Γ(X, V)
  let T := ToType ((Spec (.of k)).presheaf.stalk (f x))
  let Sx := ToType (X.sheaf.presheaf.stalk x)
  let eR := (Scheme.ΓSpecIso (CommRingCat.of k)).commRingCatIsoToRingEquiv
  let : Field R := (eR.toMulEquiv.isField (Field.toIsField k)).toField
  let : CharZero R := charZero_of_injective_ringHom eR.symm.injective
  let p := hU.primeIdealOf ⟨f x, hxU⟩
  let q := hV.primeIdealOf ⟨x, hxV⟩
  let : Algebra R T := ((Spec (.of k)).presheaf.germ U (f x) hxU).hom.toAlgebra
  have : IsLocalization.AtPrime T p.asIdeal := hU.isLocalization_stalk ⟨f x, hxU⟩
  let : Algebra T Sx := algebraStalkMap f x
  let : Algebra R Sx := ((algebraMap T Sx).comp (algebraMap R T)).toAlgebra
  have : IsScalarTower R T Sx := IsScalarTower.of_algebraMap_eq' rfl
  let : Algebra R A := (f.appLE U V hVU).hom.toAlgebra
  have : Algebra.FiniteType R A :=
    RingHom.finiteType_algebraMap.mp (f.finiteType_appLE hU hV hVU)
  let : Algebra A Sx := (X.presheaf.germ V x hxV).hom.toAlgebra
  have : IsLocalization.AtPrime Sx q.asIdeal := hV.isLocalization_stalk ⟨x, hxV⟩
  have hcompat : f.appLE U V hVU ≫ X.presheaf.germ V x hxV =
      (Spec (.of k)).presheaf.germ U (f x) hxU ≫ f.stalkMap x := by
    rw [Scheme.Hom.appLE, Category.assoc, X.presheaf.germ_res (homOfLE hVU) x hxV]
    exact (Scheme.Hom.germ_stalkMap f U x hxU).symm
  have : IsScalarTower R A Sx := IsScalarTower.of_algebraMap_eq fun r =>
    (DFunLike.congr_fun (congrArg CommRingCat.Hom.hom hcompat) r).symm
  have hfreeT : Module.Free Sx Ω[Sx⁄T] :=
    free_kaehlerDifferential_stalkMap_of_isLocallyFree f hΩ x
  have hfreeR : Module.Free Sx Ω[Sx⁄R] :=
    hfreeT.of_equiv (LinearEquiv.ofBijective (KaehlerDifferential.map R T Sx Sx)
      (omega_localization_base R Sx p.asIdeal.primeCompl T)).symm
  exact (formallySmooth_stalkMap_iff U hU V hV hVU hxV).mpr
    (haveI := hfreeR;
      _root_.ZInQ.Contrib.CloudB3W16Cartier.isSmoothAt_of_free_kaehlerDifferential
        (k := R) (S := A) q.asIdeal Sx)

/-- **Stacks Project, Tag 04QN.** A scheme locally of finite type over a field of
characteristic zero is smooth if its sheaf of relative differentials is locally free. -/
theorem smooth_of_isLocallyFree_relativeDifferentials_of_charZero
    {k : Type u} [Field k] [CharZero k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))
    [LocallyOfFiniteType f]
    (hΩ : _root_.SheafOfModules.IsLocallyFree.{u, u, u} (Scheme.Hom.relativeDifferentials f)) :
    Smooth f :=
  f.smoothLocus_eq_top_iff.mp (top_le_iff.mp fun x _ =>
    Scheme.Hom.mem_smoothLocus.mpr
      (formallySmooth_stalkMap_of_isLocallyFree_relativeDifferentials f hΩ x))

end AlgebraicGeometry
end ZInQ.Contrib.CloudB3W16Cartier.Vendor
