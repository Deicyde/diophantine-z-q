import ZInQKernel.Contrib.CloudR2Poincare.L3.Vendor.StacksFrontier.RingTheory.Smooth.RegularLocalRing.CharZeroRegularity
import ZInQKernel.Contrib.CloudR2Poincare.L3.Vendor.StacksFrontier.AlgebraicGeometry.RelativeDifferentialStalkMap.Scheme
import ZInQKernel.Contrib.CloudR2Poincare.L3.Vendor.StacksFrontier.AlgebraicGeometry.StalkFreeBridge.StalkFree
import ZInQKernel.Contrib.CloudR2Poincare.L3.Vendor.StacksFrontier.RingTheory.Kaehler.BaseChange
import TauCeti.RingTheory.RegularLocalRing.Basic
import ZInQKernel.Contrib.CloudR2Poincare.L3.InstanceScope

#cloudR2LocalInstances

/-!
# Locally free relative differentials in characteristic zero give reducedness

Source credit: the stalk/localization setup is adapted from AxiomMath/Stacks,
commit c496df0d9beea9deaeabcea8492605f9a0a2313b,
`Variety/SmoothOverField/LocallyFreeDifferentials.lean:61–122` (Apache-2.0).
Prominent change notice, 2026-11-14: instead of importing the full smooth/regular
TFAE, this file uses only the proved 00TX direction free differentials ⇒ regular
local ring, then the published Tau Ceti regular-local-ring ⇒ domain instance.
This suffices for Cartier via Mathlib's geometrically reduced group ⇒ smooth.
-/

open CategoryTheory AlgebraicGeometry TopologicalSpace

namespace ZInQ.Contrib.CloudR2Poincare.L3
#cloudR2LocalInstances

open StacksPort StacksPort.Stacks.RelativeDifferentialStalkMap
open StacksPort.AlgebraicGeometry.Scheme.Hom

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option linter.style.haveILetI false

universe u

/-- The stalk of locally free relative differentials is free over the local ring. -/
theorem free_kaehlerDifferential_stalkMap_of_isLocallyFree {X S : Scheme.{u}} (f : X ⟶ S)
    (hΩ : _root_.SheafOfModules.IsLocallyFree.{u, u, u} (_root_.ZInQ.Contrib.CloudR2Poincare.L3.StacksPort.AlgebraicGeometry.Scheme.Hom.relativeDifferentials f)) (x : X) :
    let _ := algebraStalkMap f x
    Module.Free (ToType (X.sheaf.presheaf.stalk x))
      (KaehlerDifferential (ToType (S.presheaf.stalk (f x)))
        (ToType (X.sheaf.presheaf.stalk x))) := by
  classical
  let := algebraStalkMap f x
  have := hΩ
  exact (StacksPort.Stacks.StalkFreeBridge.free_stalk_of_isLocallyFree.{u}
    (_root_.ZInQ.Contrib.CloudR2Poincare.L3.StacksPort.AlgebraicGeometry.Scheme.Hom.relativeDifferentials f) x).of_equiv (relativeDifferentialsStalkKaehlerEquiv f x)

/-- The needed 04QN/00TX consequence, without importing the full smoothness criterion. -/
theorem regular_stalk_of_isLocallyFree_relativeDifferentials_charZero
    {k : Type u} [Field k] [CharZero k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))
    [LocallyOfFiniteType f]
    (hΩ : _root_.SheafOfModules.IsLocallyFree.{u, u, u} (_root_.ZInQ.Contrib.CloudR2Poincare.L3.StacksPort.AlgebraicGeometry.Scheme.Hom.relativeDifferentials f)) (x : X) :
    IsRegularLocalRing (X.presheaf.stalk x) := by
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
  letI : Field R := (eR.toMulEquiv.isField (Field.toIsField k)).toField
  letI : CharZero R := charZero_of_injective_ringHom eR.symm.injective
  let p := hU.primeIdealOf ⟨f x, hxU⟩
  let q := hV.primeIdealOf ⟨x, hxV⟩
  letI : Algebra R T := ((Spec (.of k)).presheaf.germ U (f x) hxU).hom.toAlgebra
  haveI : IsLocalization.AtPrime T p.asIdeal := hU.isLocalization_stalk ⟨f x, hxU⟩
  letI : Algebra T Sx := algebraStalkMap f x
  letI : Algebra R Sx := ((algebraMap T Sx).comp (algebraMap R T)).toAlgebra
  haveI : IsScalarTower R T Sx := IsScalarTower.of_algebraMap_eq' rfl
  letI : Algebra R A := (f.appLE U V hVU).hom.toAlgebra
  haveI : Algebra.FiniteType R A :=
    RingHom.finiteType_algebraMap.mp (f.finiteType_appLE hU hV hVU)
  letI : Algebra A Sx := (X.presheaf.germ V x hxV).hom.toAlgebra
  haveI : IsLocalization.AtPrime Sx q.asIdeal := hV.isLocalization_stalk ⟨x, hxV⟩
  have hcompat : f.appLE U V hVU ≫ X.presheaf.germ V x hxV =
      (Spec (.of k)).presheaf.germ U (f x) hxU ≫ f.stalkMap x := by
    rw [Scheme.Hom.appLE, Category.assoc, X.presheaf.germ_res (homOfLE hVU) x hxV]
    exact (Scheme.Hom.germ_stalkMap f U x hxU).symm
  haveI : IsScalarTower R A Sx := IsScalarTower.of_algebraMap_eq fun r =>
    (DFunLike.congr_fun (congrArg CommRingCat.Hom.hom hcompat) r).symm
  have hfreeT : Module.Free Sx Ω[Sx⁄T] :=
    free_kaehlerDifferential_stalkMap_of_isLocallyFree f hΩ x
  haveI hfreeR : Module.Free Sx Ω[Sx⁄R] :=
    hfreeT.of_equiv (LinearEquiv.ofBijective (KaehlerDifferential.map R T Sx Sx)
      (omega_localization_base R Sx p.asIdeal.primeCompl T)).symm
  haveI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  haveI : IsLocalRing Sx := inferInstanceAs (IsLocalRing (X.presheaf.stalk x))
  haveI : IsNoetherianRing Sx := inferInstanceAs (IsNoetherianRing (X.presheaf.stalk x))
  haveI : Algebra.EssFiniteType A Sx :=
    Algebra.EssFiniteType.of_isLocalization Sx q.asIdeal.primeCompl
  haveI : Algebra.EssFiniteType R Sx := Algebra.EssFiniteType.comp R A Sx
  haveI : Module.Finite Sx Ω[Sx⁄R] := inferInstance
  haveI : Algebra.EssFiniteType R (IsLocalRing.ResidueField Sx) :=
    Algebra.EssFiniteType.comp R Sx (IsLocalRing.ResidueField Sx)
  change IsRegularLocalRing Sx
  exact StacksPort.isRegularLocalRing_of_free_kaehlerDifferential R
    (IsLocalRing.ResidueField Sx) (Module.finrank Sx Ω[Sx⁄R]) Sx
    Ideal.Quotient.mk_surjective rfl

/-- A finite-type scheme over a characteristic-zero field with locally free relative
    differentials is reduced. All stalk regularity is proved above, not assumed. -/
theorem isReduced_of_isLocallyFree_relativeDifferentials_charZero
    {k : Type u} [Field k] [CharZero k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))
    [LocallyOfFiniteType f]
    (hΩ : _root_.SheafOfModules.IsLocallyFree.{u, u, u} (_root_.ZInQ.Contrib.CloudR2Poincare.L3.StacksPort.AlgebraicGeometry.Scheme.Hom.relativeDifferentials f)) :
    IsReduced X := by
  haveI : ∀ x : X, IsRegularLocalRing (X.presheaf.stalk x) := fun x =>
    regular_stalk_of_isLocallyFree_relativeDifferentials_charZero f hΩ x
  haveI : ∀ x : X, IsDomain (X.presheaf.stalk x) := fun x =>
    TauCeti.IsRegularLocalRing.isDomain
  exact isReduced_of_isReduced_stalk X

end ZInQ.Contrib.CloudR2Poincare.L3
