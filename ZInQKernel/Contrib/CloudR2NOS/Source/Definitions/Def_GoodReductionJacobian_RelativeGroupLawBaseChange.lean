/-
NOS-CORE PROBE STAGING COPY (lane4, 2026-11-17). NOT an H5 edition:
probe world only; it enters H5 only by the lead binding plus C6 review. No recorded port
SHA exists for this module (lead 2026-11-17T06:06Z). Generated deterministically from the pinned
upstream file by the documented lane4 port transform, as reproduced by the located C5 conformance
pair (Thm/S_AlgebraicGeometry_Scheme_Modules_ProjPresentation_exists_of_iso), numeric options
omitted. SOURCE ONLY, UNCOMPILED. Native HELD.

Vendored, unmodified in substance, from the Fermat's Last Theorem Lean development.

  Source project : https://github.com/anthropics/fermats-last-theorem
  Source revision: 6e837e75355538c7f80bab5b956861e86c4eacc2
  Source file    : Definitions/Def_GoodReductionJacobian_RelativeGroupLawBaseChange.lean
  Source sha256  : d7f0788a3d67bd367199faf79ea7bc3f1bd7437c959b322af7c1379834894e0f
  Retrieved      : pinned upstream source revision (6e837e75), byte-for-byte
  Copyright      : 2026 Anthropic, PBC (see ATTRIBUTION.md of the source for third-party credits)
  Licence        : Apache License, Version 2.0 (see Contrib/CloudW03NeronSurj/LICENSE and NOTICE)

NOTICE OF MODIFICATION (Apache-2.0 §4(b)). This file has been changed from the original
(H5 lane4 port to Lean 4.35.0 / Mathlib 56a005855ea17e0b0958f73ec801ae140b0a1679).
Mechanical changes; no statement, hypothesis, definition or proof term was weakened or omitted:
  * 2 `r2nos_namespace_dual` shim line(s) after source `namespace` commands (Mathlib names of the same source namespace stay visible, as in the unprefixed original).
  * 1 `r2nos_open_dual`/`r2nos_open_scoped_dual` shim line(s) after source `open` commands (completes each opened namespace by its other half where the port splits one source root namespace between Mathlib root and the prefix).
  * 1 import of the lane4 Mathlib-db584 compatibility module `ZInQKernel.Contrib.CloudR2NOS.Source.Compat.PresheafOfModulesMonoidal` added (as in every located lane4 port copy).
  * 4 internal `import`(s) retargeted to `ZInQKernel.Contrib.CloudR2NOS.Source.*` / `ZInQKernel.Contrib.CloudW03NeronSurj.Vendor.*` (published W03 duals bound, see ledger) / port utilities.
  * file-level `set_option`s inserted after the port namespace: autoImplicit false; backward.isDefEq.respectTransparency.types false; backward.isDefEq.respectTransparency.instanceSearchTypes false (non-numeric, as in the located C5 conformance copies). NO maxHeartbeats/synthInstance option (numeric options omitted).
  * `import ZInQKernel.Contrib.CloudR2NOS.Source.PortUtilExt` added (port commands) and `open ZInQ.Contrib.CloudW03NeronSurj.FLT` inserted so the source's generalized field notation resolves the isolated declarations exactly as in the unprefixed original.
  * whole file wrapped in `namespace ZInQ.Contrib.CloudW03NeronSurj.FLT … end ZInQ.Contrib.CloudW03NeronSurj.FLT`.
-/

import Mathlib.AlgebraicGeometry.Pullbacks
import ZInQKernel.Contrib.CloudR2NOS.Source.Definitions.Def_GoodReductionJacobian_RelativeGroupLawKernel
import ZInQKernel.Contrib.CloudR2NOS.Source.Definitions.Def_AlgebraicGeometry_NeronModelEndomorphismExtension
import ZInQKernel.Contrib.CloudR2NOS.Source.Definitions.Def_AlgebraicGeometry_NeronSpecialFibreRestriction
import ZInQKernel.Contrib.CloudR2NOS.Source.Definitions.Def_GoodReductionJacobian_RelativeGroupLawFibre
import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.PresheafOfModulesMonoidal
import ZInQKernel.Contrib.CloudR2NOS.Source.PortUtilExt

namespace ZInQ.Contrib.CloudW03NeronSurj.FLT

open ZInQ.Contrib.CloudW03NeronSurj.FLT

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false

set_option autoImplicit false

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra NeronSpecialFibreInfra
r2nos_open_dual "CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra NeronSpecialFibreInfra"

namespace GoodReductionJacobian
r2nos_namespace_dual
namespace RelativeGroupLaw
r2nos_namespace_dual

section BaseChange

variable {R : Type u} [CommRing R] {R' : Type u} [CommRing R']
variable (ι : Spec (CommRingCat.of R') ⟶ Spec (CommRingCat.of R))
variable {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of R)}

abbrev baseChangeScheme (f : A ⟶ Spec (CommRingCat.of R)) : Scheme.{u} :=
  pullback f ι

abbrev baseChangeStr (f : A ⟶ Spec (CommRingCat.of R)) :
    baseChangeScheme ι f ⟶ Spec (CommRingCat.of R') :=
  pullback.snd f ι

def baseChangePointToBase {T : Scheme.{u}} {t' : T ⟶ Spec (CommRingCat.of R')}
    (x : SchemeHomOver t' (baseChangeStr ι f)) : SchemeHomOver (t' ≫ ι) f :=
  ⟨x.1 ≫ pullback.fst f ι, by rw [Category.assoc, pullback.condition, ← Category.assoc, x.2]⟩

def baseChangePointOfBase {T : Scheme.{u}} {t' : T ⟶ Spec (CommRingCat.of R')}
    (y : SchemeHomOver (t' ≫ ι) f) : SchemeHomOver t' (baseChangeStr ι f) :=
  ⟨pullback.lift y.1 t' y.2, pullback.lift_snd _ _ _⟩

@[simp]
theorem baseChangePointToBase_coe {T : Scheme.{u}} {t' : T ⟶ Spec (CommRingCat.of R')}
    (x : SchemeHomOver t' (baseChangeStr ι f)) :
    (baseChangePointToBase ι x).1 = x.1 ≫ pullback.fst f ι :=
  rfl

@[simp]
theorem baseChangePointOfBase_coe {T : Scheme.{u}} {t' : T ⟶ Spec (CommRingCat.of R')}
    (y : SchemeHomOver (t' ≫ ι) f) :
    (baseChangePointOfBase ι y).1 = pullback.lift y.1 t' y.2 :=
  rfl

@[simp]
theorem baseChangePointToBase_ofBase {T : Scheme.{u}} {t' : T ⟶ Spec (CommRingCat.of R')}
    (y : SchemeHomOver (t' ≫ ι) f) :
    baseChangePointToBase ι (baseChangePointOfBase ι y) = y :=
  Subtype.ext (pullback.lift_fst _ _ _)

@[simp]
theorem baseChangePointOfBase_toBase {T : Scheme.{u}} {t' : T ⟶ Spec (CommRingCat.of R')}
    (x : SchemeHomOver t' (baseChangeStr ι f)) :
    baseChangePointOfBase ι (baseChangePointToBase ι x) = x := by
  apply Subtype.ext
  apply pullback.hom_ext
  · rw [baseChangePointOfBase_coe, pullback.lift_fst, baseChangePointToBase_coe]
  · rw [baseChangePointOfBase_coe, pullback.lift_snd]
    exact x.2.symm

def baseChangePointEquiv {T : Scheme.{u}} (t' : T ⟶ Spec (CommRingCat.of R')) :
    SchemeHomOver t' (baseChangeStr ι f) ≃ SchemeHomOver (t' ≫ ι) f where
  toFun := baseChangePointToBase ι
  invFun := baseChangePointOfBase ι
  left_inv := baseChangePointOfBase_toBase ι
  right_inv := baseChangePointToBase_ofBase ι

theorem baseChangePointToBase_schemeHomOverComp {T T' : Scheme.{u}}
    (t : T ⟶ Spec (CommRingCat.of R')) (t' : T' ⟶ Spec (CommRingCat.of R')) (ψ : T' ⟶ T)
    (hψ : ψ ≫ t = t') (x : SchemeHomOver t (baseChangeStr ι f)) :
    baseChangePointToBase ι (schemeHomOverComp ψ hψ x) =
      schemeHomOverComp ψ (by rw [← Category.assoc, hψ]) (baseChangePointToBase ι x) :=
  Subtype.ext (Category.assoc _ _ _)

theorem baseChangePointToBase_comp_fibreRestrictAlong {B : Scheme.{u}}
    {g : B ⟶ Spec (CommRingCat.of R)} (φ : SchemeHomOver g f)
    {T : Scheme.{u}} {t' : T ⟶ Spec (CommRingCat.of R')} (x : SchemeHomOver t' (baseChangeStr ι g)) :
    baseChangePointToBase ι (NeronModelInfra.schemeHomOverComp x (fibreRestrictAlong ι f g φ)) =
      NeronModelInfra.schemeHomOverComp (baseChangePointToBase ι x) φ := by
  apply Subtype.ext
  simp only [baseChangePointToBase_coe, NeronModelInfra.schemeHomOverComp_coe, Category.assoc,
    fibreRestrictAlong_coe_comp_fst]

def baseChange (G : RelativeGroupLaw R f) : RelativeGroupLaw R' (baseChangeStr ι f) where
  mul t' x y := baseChangePointOfBase ι (G.mul _ (baseChangePointToBase ι x) (baseChangePointToBase ι y))
  one t' := baseChangePointOfBase ι (G.one _)
  inv t' x := baseChangePointOfBase ι (G.inv _ (baseChangePointToBase ι x))
  mul_assoc t' x y z := by
    simp only [baseChangePointToBase_ofBase, G.mul_assoc]
  one_mul t' x := by
    simp only [baseChangePointToBase_ofBase, G.one_mul, baseChangePointOfBase_toBase]
  mul_one t' x := by
    simp only [baseChangePointToBase_ofBase, G.mul_one, baseChangePointOfBase_toBase]
  inv_mul_cancel t' x := by
    simp only [baseChangePointToBase_ofBase, G.inv_mul_cancel]
  mul_natural t t' ψ hψ x y := by
    apply Subtype.ext
    apply pullback.hom_ext
    · rw [schemeHomOverComp_coe, baseChangePointOfBase_coe, baseChangePointOfBase_coe, Category.assoc,
        pullback.lift_fst, pullback.lift_fst]
      have h := congrArg Subtype.val
        (G.mul_natural (t ≫ ι) (t' ≫ ι) ψ (by rw [← Category.assoc, hψ]) (baseChangePointToBase ι x)
          (baseChangePointToBase ι y))
      rw [schemeHomOverComp_coe] at h
      rw [h, ← baseChangePointToBase_schemeHomOverComp, ← baseChangePointToBase_schemeHomOverComp]
    · rw [schemeHomOverComp_coe, baseChangePointOfBase_coe, baseChangePointOfBase_coe, Category.assoc,
        pullback.lift_snd, pullback.lift_snd]
      exact hψ

@[simp]
theorem baseChange_mul (G : RelativeGroupLaw R f) {T : Scheme.{u}}
    (t' : T ⟶ Spec (CommRingCat.of R')) (x y : SchemeHomOver t' (baseChangeStr ι f)) :
    (G.baseChange ι).mul t' x y =
      baseChangePointOfBase ι (G.mul _ (baseChangePointToBase ι x) (baseChangePointToBase ι y)) :=
  rfl

@[simp]
theorem baseChange_one (G : RelativeGroupLaw R f) {T : Scheme.{u}} (t' : T ⟶ Spec (CommRingCat.of R')) :
    (G.baseChange ι).one t' = baseChangePointOfBase ι (G.one _) :=
  rfl

@[simp]
theorem baseChange_inv (G : RelativeGroupLaw R f) {T : Scheme.{u}}
    (t' : T ⟶ Spec (CommRingCat.of R')) (x : SchemeHomOver t' (baseChangeStr ι f)) :
    (G.baseChange ι).inv t' x = baseChangePointOfBase ι (G.inv _ (baseChangePointToBase ι x)) :=
  rfl

theorem baseChangePointToBase_mul (G : RelativeGroupLaw R f) {T : Scheme.{u}}
    (t' : T ⟶ Spec (CommRingCat.of R')) (x y : SchemeHomOver t' (baseChangeStr ι f)) :
    baseChangePointToBase ι ((G.baseChange ι).mul t' x y) =
      G.mul _ (baseChangePointToBase ι x) (baseChangePointToBase ι y) := by
  rw [baseChange_mul, baseChangePointToBase_ofBase]

theorem baseChangePointToBase_one (G : RelativeGroupLaw R f) {T : Scheme.{u}}
    (t' : T ⟶ Spec (CommRingCat.of R')) :
    baseChangePointToBase ι ((G.baseChange ι).one t') = G.one _ := by
  rw [baseChange_one, baseChangePointToBase_ofBase]

theorem baseChangePointToBase_inv (G : RelativeGroupLaw R f) {T : Scheme.{u}}
    (t' : T ⟶ Spec (CommRingCat.of R')) (x : SchemeHomOver t' (baseChangeStr ι f)) :
    baseChangePointToBase ι ((G.baseChange ι).inv t' x) = G.inv _ (baseChangePointToBase ι x) := by
  rw [baseChange_inv, baseChangePointToBase_ofBase]

theorem IsCommutative.baseChange {G : RelativeGroupLaw R f} (hG : G.IsCommutative) :
    (G.baseChange ι).IsCommutative := fun t' x y => by
  rw [baseChange_mul, baseChange_mul, hG.mul_comm]

theorem fibre_eq_baseChange (G : RelativeGroupLaw R f) (s : (Spec (CommRingCat.of R) : Scheme.{u})) :
    G.fibre s = G.baseChange (basePointInclusion s) :=
  rfl

end BaseChange

section GenericFibre

variable {R : Type u} [CommRing R] (K : Type u) [Field K] [Algebra R K]
variable {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of R)}

abbrev genericFibreScheme (f : A ⟶ Spec (CommRingCat.of R)) : Scheme.{u} :=
  baseChangeScheme (specGenericFibreInclusion R K) f

abbrev genericFibreStr (f : A ⟶ Spec (CommRingCat.of R)) : genericFibreScheme K f ⟶ Spec (CommRingCat.of K) :=
  baseChangeStr (specGenericFibreInclusion R K) f

abbrev genericFibre (G : RelativeGroupLaw R f) : RelativeGroupLaw K (genericFibreStr K f) :=
  G.baseChange (specGenericFibreInclusion R K)

theorem baseChangePointToBase_comp_genericFibreRestrict {B : Scheme.{u}}
    {g : B ⟶ Spec (CommRingCat.of R)} (φ : SchemeHomOver g f)
    {T : Scheme.{u}} {t' : T ⟶ Spec (CommRingCat.of K)} (x : SchemeHomOver t' (genericFibreStr K g)) :
    baseChangePointToBase (specGenericFibreInclusion R K)
        (NeronModelInfra.schemeHomOverComp x (genericFibreRestrict R K f g φ)) =
      NeronModelInfra.schemeHomOverComp (baseChangePointToBase (specGenericFibreInclusion R K) x) φ :=
  baseChangePointToBase_comp_fibreRestrictAlong (specGenericFibreInclusion R K) φ x

end GenericFibre

end RelativeGroupLaw
end GoodReductionJacobian

end

end ZInQ.Contrib.CloudW03NeronSurj.FLT
