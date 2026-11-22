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
  Source file    : Definitions/Def_AlgebraicGeometry_NeronSpecialFibreRestriction.lean
  Source sha256  : dc947b48c74a11e2fee7ff133e867fd7eeb99f6b9f1ad09b96d30d9b780a1595
  Retrieved      : pinned upstream source revision (6e837e75), byte-for-byte
  Copyright      : 2026 Anthropic, PBC (see ATTRIBUTION.md of the source for third-party credits)
  Licence        : Apache License, Version 2.0 (see Contrib/CloudW03NeronSurj/LICENSE and NOTICE)

NOTICE OF MODIFICATION (Apache-2.0 §4(b)). This file has been changed from the original
(H5 lane4 port to Lean 4.35.0 / Mathlib 56a005855ea17e0b0958f73ec801ae140b0a1679).
Mechanical changes; no statement, hypothesis, definition or proof term was weakened or omitted:
  * 1 `r2nos_namespace_dual` shim line(s) after source `namespace` commands (Mathlib names of the same source namespace stay visible, as in the unprefixed original).
  * 1 `r2nos_open_dual`/`r2nos_open_scoped_dual` shim line(s) after source `open` commands (completes each opened namespace by its other half where the port splits one source root namespace between Mathlib root and the prefix).
  * 1 import of the lane4 Mathlib-db584 compatibility module `ZInQKernel.Contrib.CloudR2NOS.Source.Compat.PresheafOfModulesMonoidal` added (as in every located lane4 port copy).
  * 1 internal `import`(s) retargeted to `ZInQKernel.Contrib.CloudR2NOS.Source.*` / `ZInQKernel.Contrib.CloudW03NeronSurj.Vendor.*` (published W03 duals bound, see ledger) / port utilities.
  * file-level `set_option`s inserted after the port namespace: autoImplicit false; backward.isDefEq.respectTransparency.types false; backward.isDefEq.respectTransparency.instanceSearchTypes false (non-numeric, as in the located C5 conformance copies). NO maxHeartbeats/synthInstance option (numeric options omitted).
  * `import ZInQKernel.Contrib.CloudR2NOS.Source.PortUtilExt` added (port commands) and `open ZInQ.Contrib.CloudW03NeronSurj.FLT` inserted so the source's generalized field notation resolves the isolated declarations exactly as in the unprefixed original.
  * whole file wrapped in `namespace ZInQ.Contrib.CloudW03NeronSurj.FLT … end ZInQ.Contrib.CloudW03NeronSurj.FLT`.
  * DRIFT/PORT-PITFALL RULES v1 (compatibility rules), applied: T2×11, T4×1; rule citations in the batch ledger.
-/

import Mathlib
import ZInQKernel.Contrib.CloudW03NeronSurj.Vendor.Definitions.Def_AlgebraicGeometry_NeronModelPropertyBundleCarrier
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

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra
r2nos_open_dual "CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra"

namespace NeronSpecialFibreInfra
r2nos_namespace_dual

section RelativeHomBookkeeping

variable {B X Y Z : Scheme.{u}}

def homOverId (f : X ⟶ B) : SchemeHomOver f f :=
  ⟨𝟙 X, Category.id_comp f⟩

@[simp]
theorem homOverId_coe (f : X ⟶ B) : (homOverId f).1 = 𝟙 X :=
  rfl

def homOverComp {e : Z ⟶ B} {g : Y ⟶ B} {f : X ⟶ B}
    (ψ : SchemeHomOver e g) (φ : SchemeHomOver g f) : SchemeHomOver e f :=
  ⟨ψ.1 ≫ φ.1, by rw [Category.assoc, φ.2, ψ.2]⟩

@[simp]
theorem homOverComp_coe {e : Z ⟶ B} {g : Y ⟶ B} {f : X ⟶ B}
    (ψ : SchemeHomOver e g) (φ : SchemeHomOver g f) :
    (homOverComp ψ φ).1 = ψ.1 ≫ φ.1 :=
  rfl

end RelativeHomBookkeeping

section FibreRestrictAlong

variable {B C X Y Z : Scheme.{u}}

def fibreRestrictAlong (c : C ⟶ B) (f : X ⟶ B) (g : Y ⟶ B) (φ : SchemeHomOver g f) :
    SchemeHomOver (pullback.snd g c) (pullback.snd f c) :=
  ⟨pullback.lift (pullback.fst g c ≫ φ.1) (pullback.snd g c)
      (by rw [Category.assoc, φ.2, pullback.condition]),
    pullback.lift_snd _ _ _⟩

@[reassoc (attr := simp)]
theorem fibreRestrictAlong_coe_comp_fst (c : C ⟶ B) (f : X ⟶ B) (g : Y ⟶ B)
    (φ : SchemeHomOver g f) :
    (fibreRestrictAlong c f g φ).1 ≫ pullback.fst f c = pullback.fst g c ≫ φ.1 :=
  pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
theorem fibreRestrictAlong_coe_comp_snd (c : C ⟶ B) (f : X ⟶ B) (g : Y ⟶ B)
    (φ : SchemeHomOver g f) :
    (fibreRestrictAlong c f g φ).1 ≫ pullback.snd f c = pullback.snd g c :=
  pullback.lift_snd _ _ _

theorem fibreRestrictAlong_coe_eq_pullbackMap (c : C ⟶ B) (f : X ⟶ B) (g : Y ⟶ B)
    (φ : SchemeHomOver g f)
    (eq₁ : g ≫ 𝟙 B = φ.1 ≫ f) (eq₂ : c ≫ 𝟙 B = 𝟙 C ≫ c) :
    (fibreRestrictAlong c f g φ).1 =
      pullback.map g c f c φ.1 (𝟙 C) (𝟙 B) eq₁ eq₂ := by
  apply pullback.hom_ext
  · simp [fibreRestrictAlong, pullback.map, pullback.lift_fst]
  · simp [fibreRestrictAlong, pullback.map, pullback.lift_snd]

theorem fibreRestrictAlong_homOverId (c : C ⟶ B) (f : X ⟶ B) :
    fibreRestrictAlong c f f (homOverId f) = homOverId (pullback.snd f c) := by
  apply Subtype.ext
  apply pullback.hom_ext <;> simp

theorem fibreRestrictAlong_homOverComp (c : C ⟶ B) (f : X ⟶ B) (g : Y ⟶ B) (e : Z ⟶ B)
    (ψ : SchemeHomOver e g) (φ : SchemeHomOver g f) :
    fibreRestrictAlong c f e (homOverComp ψ φ) =
      homOverComp (fibreRestrictAlong c g e ψ) (fibreRestrictAlong c f g φ) := by
  apply Subtype.ext
  apply pullback.hom_ext <;> simp

end FibreRestrictAlong

section GenericFibreComparison

variable (R K : Type u) [CommRing R] [Field K] [Algebra R K]
variable {X Y Z : Scheme.{u}}

theorem fibreRestrictAlong_specGenericFibreInclusion
    (f : X ⟶ Spec (CommRingCat.of R)) (g : Y ⟶ Spec (CommRingCat.of R))
    (φ : SchemeHomOver g f) :
    fibreRestrictAlong (specGenericFibreInclusion R K) f g φ =
      genericFibreRestrict R K f g φ :=
  rfl

theorem genericFibreRestrict_homOverId (f : X ⟶ Spec (CommRingCat.of R)) :
    genericFibreRestrict R K f f (homOverId f) =
      homOverId (pullback.snd f (specGenericFibreInclusion R K)) :=
  fibreRestrictAlong_homOverId (specGenericFibreInclusion R K) f

theorem genericFibreRestrict_homOverComp (f : X ⟶ Spec (CommRingCat.of R))
    (g : Y ⟶ Spec (CommRingCat.of R)) (e : Z ⟶ Spec (CommRingCat.of R))
    (ψ : SchemeHomOver e g) (φ : SchemeHomOver g f) :
    genericFibreRestrict R K f e (homOverComp ψ φ) =
      homOverComp (genericFibreRestrict R K g e ψ) (genericFibreRestrict R K f g φ) :=
  fibreRestrictAlong_homOverComp (specGenericFibreInclusion R K) f g e ψ φ

end GenericFibreComparison

section SpecialFibre

variable (R : Type u) [CommRing R] (m : Ideal R)
variable {X Y Z : Scheme.{u}}

def specClosedFibreInclusion : Spec (CommRingCat.of (R ⧸ m)) ⟶ Spec (CommRingCat.of R) :=
  Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk m))

@[simp]
theorem specClosedFibreInclusion_eq :
    specClosedFibreInclusion R m = Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk m)) :=
  rfl

theorem specClosedFibreInclusion_eq_spec_algebraMap :
    specClosedFibreInclusion R m =
      Spec.map (CommRingCat.ofHom (algebraMap R (R ⧸ m))) := by
  simp only [specClosedFibreInclusion_eq, Ideal.Quotient.algebraMap_eq]

theorem isClosedImmersion_specClosedFibreInclusion :
    IsClosedImmersion (specClosedFibreInclusion R m) :=
  IsClosedImmersion.spec_of_surjective
    (CommRingCat.ofHom (Ideal.Quotient.mk m)) Ideal.Quotient.mk_surjective

theorem isField_residueField [m.IsMaximal] : IsField (R ⧸ m) :=
  (Ideal.Quotient.maximal_ideal_iff_isField_quotient m).mp inferInstance

def specialFibreRestrict (f : X ⟶ Spec (CommRingCat.of R)) (g : Y ⟶ Spec (CommRingCat.of R))
    (φ : SchemeHomOver g f) :
    SchemeHomOver (pullback.snd g (specClosedFibreInclusion R m))
      (pullback.snd f (specClosedFibreInclusion R m)) :=
  fibreRestrictAlong (specClosedFibreInclusion R m) f g φ

theorem specialFibreRestrict_eq_fibreRestrictAlong
    (f : X ⟶ Spec (CommRingCat.of R)) (g : Y ⟶ Spec (CommRingCat.of R))
    (φ : SchemeHomOver g f) :
    specialFibreRestrict R m f g φ =
      fibreRestrictAlong (specClosedFibreInclusion R m) f g φ :=
  rfl

@[reassoc (attr := simp)]
theorem specialFibreRestrict_coe_comp_fst (f : X ⟶ Spec (CommRingCat.of R))
    (g : Y ⟶ Spec (CommRingCat.of R)) (φ : SchemeHomOver g f) :
    (specialFibreRestrict R m f g φ).1 ≫ pullback.fst f (specClosedFibreInclusion R m) =
      pullback.fst g (specClosedFibreInclusion R m) ≫ φ.1 :=
  fibreRestrictAlong_coe_comp_fst (specClosedFibreInclusion R m) f g φ

@[reassoc (attr := simp)]
theorem specialFibreRestrict_coe_comp_snd (f : X ⟶ Spec (CommRingCat.of R))
    (g : Y ⟶ Spec (CommRingCat.of R)) (φ : SchemeHomOver g f) :
    (specialFibreRestrict R m f g φ).1 ≫ pullback.snd f (specClosedFibreInclusion R m) =
      pullback.snd g (specClosedFibreInclusion R m) :=
  fibreRestrictAlong_coe_comp_snd (specClosedFibreInclusion R m) f g φ

theorem specialFibreRestrict_homOverId (f : X ⟶ Spec (CommRingCat.of R)) :
    specialFibreRestrict R m f f (homOverId f) =
      homOverId (pullback.snd f (specClosedFibreInclusion R m)) :=
  fibreRestrictAlong_homOverId (specClosedFibreInclusion R m) f

theorem specialFibreRestrict_homOverComp (f : X ⟶ Spec (CommRingCat.of R))
    (g : Y ⟶ Spec (CommRingCat.of R)) (e : Z ⟶ Spec (CommRingCat.of R))
    (ψ : SchemeHomOver e g) (φ : SchemeHomOver g f) :
    specialFibreRestrict R m f e (homOverComp ψ φ) =
      homOverComp (specialFibreRestrict R m g e ψ) (specialFibreRestrict R m f g φ) :=
  fibreRestrictAlong_homOverComp (specClosedFibreInclusion R m) f g e ψ φ

end SpecialFibre

section NeronEndExtension

variable {R K : Type u} [CommRing R] [Field K] [Algebra R K]
variable [IsDomain R] [IsDedekindDomain R] [IsFractionRing R K]
variable {X : Scheme.{u}} {f : X ⟶ Spec (CommRingCat.of R)}

def neronEndRestrictEquiv (h : NeronModelPropertyBundle R K f) :
    SchemeHomOver f f ≃
      SchemeHomOver (pullback.snd f (specGenericFibreInclusion R K))
        (pullback.snd f (specGenericFibreInclusion R K)) :=
  Equiv.ofBijective (genericFibreRestrict R K f f) (h.neronMapping X f h.smooth)

@[simp]
theorem neronEndRestrictEquiv_apply (h : NeronModelPropertyBundle R K f)
    (Φ : SchemeHomOver f f) :
    neronEndRestrictEquiv h Φ = genericFibreRestrict R K f f Φ :=
  rfl

def neronEndExtension (h : NeronModelPropertyBundle R K f)
    (v : SchemeHomOver (pullback.snd f (specGenericFibreInclusion R K))
      (pullback.snd f (specGenericFibreInclusion R K))) :
    SchemeHomOver f f :=
  (neronEndRestrictEquiv h).symm v

@[simp]
theorem genericFibreRestrict_neronEndExtension (h : NeronModelPropertyBundle R K f)
    (v : SchemeHomOver (pullback.snd f (specGenericFibreInclusion R K))
      (pullback.snd f (specGenericFibreInclusion R K))) :
    genericFibreRestrict R K f f (neronEndExtension h v) = v :=
  Equiv.ofBijective_apply_symm_apply (genericFibreRestrict R K f f)
    (h.neronMapping X f h.smooth) v

theorem neronEndExtension_eq_of_restrict (h : NeronModelPropertyBundle R K f)
    {Φ : SchemeHomOver f f}
    {v : SchemeHomOver (pullback.snd f (specGenericFibreInclusion R K))
      (pullback.snd f (specGenericFibreInclusion R K))}
    (hΦ : genericFibreRestrict R K f f Φ = v) :
    neronEndExtension h v = Φ := by
  refine (h.neronMapping X f h.smooth).injective ?_
  rw [genericFibreRestrict_neronEndExtension, hΦ]

@[simp]
theorem neronEndExtension_genericFibreRestrict (h : NeronModelPropertyBundle R K f)
    (Φ : SchemeHomOver f f) :
    neronEndExtension h (genericFibreRestrict R K f f Φ) = Φ :=
  neronEndExtension_eq_of_restrict h rfl

theorem neronEndExtension_homOverId (h : NeronModelPropertyBundle R K f) :
    neronEndExtension h (homOverId (pullback.snd f (specGenericFibreInclusion R K))) =
      homOverId f :=
  neronEndExtension_eq_of_restrict h (genericFibreRestrict_homOverId R K f)

theorem neronEndExtension_homOverComp (h : NeronModelPropertyBundle R K f)
    (v w : SchemeHomOver (pullback.snd f (specGenericFibreInclusion R K))
      (pullback.snd f (specGenericFibreInclusion R K))) :
    neronEndExtension h (homOverComp v w) =
      homOverComp (neronEndExtension h v) (neronEndExtension h w) := by
  apply neronEndExtension_eq_of_restrict h
  simp only [genericFibreRestrict_homOverComp, genericFibreRestrict_neronEndExtension]

end NeronEndExtension

section NeronSpecialFibreTransfer

variable {R K : Type u} [CommRing R] [Field K] [Algebra R K]
variable [IsDomain R] [IsDedekindDomain R] [IsFractionRing R K]
variable {X : Scheme.{u}} {f : X ⟶ Spec (CommRingCat.of R)}

def neronSpecialFibreTransfer (h : NeronModelPropertyBundle R K f)
    (m : Ideal R) [m.IsMaximal]
    (v : SchemeHomOver (pullback.snd f (specGenericFibreInclusion R K))
      (pullback.snd f (specGenericFibreInclusion R K))) :
    SchemeHomOver (pullback.snd f (specClosedFibreInclusion R m))
      (pullback.snd f (specClosedFibreInclusion R m)) :=
  specialFibreRestrict R m f f (neronEndExtension h v)

theorem neronSpecialFibreTransfer_eq_of_restrict (h : NeronModelPropertyBundle R K f)
    (m : Ideal R) [m.IsMaximal] {Φ : SchemeHomOver f f}
    {v : SchemeHomOver (pullback.snd f (specGenericFibreInclusion R K))
      (pullback.snd f (specGenericFibreInclusion R K))}
    (hΦ : genericFibreRestrict R K f f Φ = v) :
    neronSpecialFibreTransfer h m v = specialFibreRestrict R m f f Φ :=
  congrArg (specialFibreRestrict R m f f) (neronEndExtension_eq_of_restrict h hΦ)

theorem specialFibreRestrict_congr_genericFibre (h : NeronModelPropertyBundle R K f)
    (m : Ideal R) [m.IsMaximal] {Φ Ψ : SchemeHomOver f f}
    (hΦΨ : genericFibreRestrict R K f f Φ = genericFibreRestrict R K f f Ψ) :
    specialFibreRestrict R m f f Φ = specialFibreRestrict R m f f Ψ :=
  congrArg (specialFibreRestrict R m f f) ((h.neronMapping X f h.smooth).injective hΦΨ)

theorem exists_neronExtension_specialFibreRestrict (h : NeronModelPropertyBundle R K f)
    (m : Ideal R) [m.IsMaximal]
    (v : SchemeHomOver (pullback.snd f (specGenericFibreInclusion R K))
      (pullback.snd f (specGenericFibreInclusion R K))) :
    ∃ Φ : SchemeHomOver f f, genericFibreRestrict R K f f Φ = v ∧
      specialFibreRestrict R m f f Φ = neronSpecialFibreTransfer h m v :=
  ⟨neronEndExtension h v, genericFibreRestrict_neronEndExtension h v, rfl⟩

theorem neronSpecialFibreTransfer_homOverId (h : NeronModelPropertyBundle R K f)
    (m : Ideal R) [m.IsMaximal] :
    neronSpecialFibreTransfer h m
        (homOverId (pullback.snd f (specGenericFibreInclusion R K))) =
      homOverId (pullback.snd f (specClosedFibreInclusion R m)) :=
  (congrArg (specialFibreRestrict R m f f) (neronEndExtension_homOverId h)).trans
    (specialFibreRestrict_homOverId R m f)

theorem neronSpecialFibreTransfer_homOverComp (h : NeronModelPropertyBundle R K f)
    (m : Ideal R) [m.IsMaximal]
    (v w : SchemeHomOver (pullback.snd f (specGenericFibreInclusion R K))
      (pullback.snd f (specGenericFibreInclusion R K))) :
    neronSpecialFibreTransfer h m (homOverComp v w) =
      homOverComp (neronSpecialFibreTransfer h m v) (neronSpecialFibreTransfer h m w) :=
  (congrArg (specialFibreRestrict R m f f) (neronEndExtension_homOverComp h v w)).trans
    (specialFibreRestrict_homOverComp R m f f f
      (neronEndExtension h v) (neronEndExtension h w))

end NeronSpecialFibreTransfer


end NeronSpecialFibreInfra












end

end ZInQ.Contrib.CloudW03NeronSurj.FLT
