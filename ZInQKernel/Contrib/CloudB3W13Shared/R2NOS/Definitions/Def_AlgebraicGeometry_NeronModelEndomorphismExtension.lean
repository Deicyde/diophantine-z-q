/- Additional modification notice, 2026-11-16: Cloud Batch 3 Worker 13
retargeted only repository module paths into the task-owned CloudB3W13
directories. Canonical mathematical declaration names and statements
are retained. Recovery and later compatibility changes are documented
in the accompanying source manifest and NOTICE. -/
/-
Vendored, unmodified in substance, from the Fermat's Last Theorem Lean development.

  Source project : https://github.com/anthropics/fermats-last-theorem
  Source revision: 6e837e75355538c7f80bab5b956861e86c4eacc2
  Source file    : Definitions/Def_AlgebraicGeometry_NeronModelEndomorphismExtension.lean
  Retrieved      : 2026-11-14 (git smart-protocol blob, byte-for-byte; sha256 in lane4 port manifest)
  Copyright      : 2026 Anthropic, PBC (see ATTRIBUTION.md of the source for third-party credits)
  Licence        : Apache License, Version 2.0 (see Contrib/CloudW03NeronSurj/LICENSE and NOTICE)

NOTICE OF MODIFICATION (Apache-2.0 §4(b)). This file has been changed from the original
(H5 lane4 port to Lean 4.35.0 / Mathlib 56a005855ea17e0b0958f73ec801ae140b0a1679, 2026-11-14).
Mechanical changes; no statement, hypothesis, definition or proof term was weakened or
omitted unless listed under manual repairs:
  * 1 `r2nos_namespace_dual` shim line(s) after source `namespace` commands (Mathlib names of the same source namespace stay visible, as in the unprefixed original).
  * 1 `r2nos_open_dual` shim line(s) after source `open` commands (completes each opened namespace by its other half where the port splits one source root namespace between Mathlib root and the prefix).
  * 1 import(s) of `ZInQKernel.Contrib.CloudB3W13Shared.R2NOS.Restore.Def_AlgebraicGeometry_NeronModelPropertyBundleCarrier_Gates` added: it restores the source carrier self-test lemmas that the published H76 vendored copy omitted and that this file uses.
  * 1 internal `import`(s) retargeted to `ZInQKernel.Contrib.CloudB3W13Shared.R2NOS.*` / `ZInQKernel.Contrib.CloudW03NeronSurj.Vendor.*` / port utilities.
  * 52 line(s) of `#print axioms` / `#guard_msgs` audit removed (diagnostics only; no proof term).
  * 1 scope(s) the source leaves open at EOF closed explicitly so the port namespace can be closed (Lean closes these implicitly at EOF in the original; no-op).
  * file-level `set_option`s inserted after the port namespace, reproducing the source build environment: autoImplicit false (source lakefile.lean leanOptions); maxHeartbeats 4000000 (source lakefile.lean leanOptions); synthInstance.maxHeartbeats 400000 (source lakefile.lean leanOptions); backward.isDefEq.respectTransparency.types false (source lakefile.lean leanOptions); backward.isDefEq.respectTransparency.instanceSearchTypes false (Lean 4.35 option absent from source Lean 4.33.1; `false` restores 4.33.1 behaviour).
  * `import ZInQKernel.Contrib.CloudB3W13Shared.R2NOS.PortUtilExt` added (port commands) and `open ZInQ.Contrib.CloudW03NeronSurj.FLT` inserted so the source's generalized field notation resolves the isolated declarations exactly as in the unprefixed original.
  * whole file wrapped in `namespace ZInQ.Contrib.CloudW03NeronSurj.FLT … end ZInQ.Contrib.CloudW03NeronSurj.FLT`.
-/

import Mathlib
import ZInQKernel.Contrib.CloudW03NeronSurj.Vendor.Definitions.Def_AlgebraicGeometry_NeronModelPropertyBundleCarrier
import ZInQKernel.Contrib.CloudB3W13Shared.R2NOS.Restore.Def_AlgebraicGeometry_NeronModelPropertyBundleCarrier_Gates
import ZInQKernel.Contrib.CloudB3W13Shared.R2NOS.PortUtilExt

namespace ZInQ.Contrib.CloudW03NeronSurj.FLT

open ZInQ.Contrib.CloudW03NeronSurj.FLT

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false

set_option autoImplicit false

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
r2nos_open_dual "CategoryTheory CategoryTheory.Limits AlgebraicGeometry"

namespace NeronModelInfra
r2nos_namespace_dual

section HomOverBookkeeping

variable {B Y X W : Scheme.{u}}

def schemeHomOverId (f : X ⟶ B) : SchemeHomOver f f :=
  ⟨𝟙 X, Category.id_comp f⟩

@[simp]
theorem schemeHomOverId_coe (f : X ⟶ B) : (schemeHomOverId f).1 = 𝟙 X :=
  rfl

def schemeHomOverComp {g : Y ⟶ B} {f : X ⟶ B} {e : W ⟶ B}
    (φ : SchemeHomOver g f) (ψ : SchemeHomOver f e) : SchemeHomOver g e :=
  ⟨φ.1 ≫ ψ.1, by rw [Category.assoc, ψ.2, φ.2]⟩

@[simp]
theorem schemeHomOverComp_coe {g : Y ⟶ B} {f : X ⟶ B} {e : W ⟶ B}
    (φ : SchemeHomOver g f) (ψ : SchemeHomOver f e) :
    (schemeHomOverComp φ ψ).1 = φ.1 ≫ ψ.1 :=
  rfl

theorem schemeHomOverComp_assoc {V : Scheme.{u}} {g : Y ⟶ B} {f : X ⟶ B} {e : W ⟶ B}
    {d : V ⟶ B} (φ : SchemeHomOver g f) (ψ : SchemeHomOver f e) (χ : SchemeHomOver e d) :
    schemeHomOverComp (schemeHomOverComp φ ψ) χ =
      schemeHomOverComp φ (schemeHomOverComp ψ χ) := by
  apply Subtype.ext
  simp

@[simp]
theorem schemeHomOverComp_id_left {g : Y ⟶ B} {f : X ⟶ B} (φ : SchemeHomOver g f) :
    schemeHomOverComp (schemeHomOverId g) φ = φ := by
  apply Subtype.ext
  simp

@[simp]
theorem schemeHomOverComp_id_right {g : Y ⟶ B} {f : X ⟶ B} (φ : SchemeHomOver g f) :
    schemeHomOverComp φ (schemeHomOverId f) = φ := by
  apply Subtype.ext
  simp

end HomOverBookkeeping

section RestrictFunctoriality

variable (R K : Type u) [CommRing R] [Field K] [Algebra R K]
variable {X Y Z : Scheme.{u}}

theorem genericFibreRestrict_schemeHomOverId (f : X ⟶ Spec (CommRingCat.of R)) :
    genericFibreRestrict R K f f (schemeHomOverId f) =
      schemeHomOverId (pullback.snd f (specGenericFibreInclusion R K)) := by
  apply Subtype.ext
  apply pullback.hom_ext
  · simp [genericFibreRestrict]
  · simp [genericFibreRestrict]

theorem genericFibreRestrict_schemeHomOverComp
    (f : X ⟶ Spec (CommRingCat.of R)) (g : Y ⟶ Spec (CommRingCat.of R))
    (e : Z ⟶ Spec (CommRingCat.of R)) (φ : SchemeHomOver g f) (ψ : SchemeHomOver f e) :
    genericFibreRestrict R K e g (schemeHomOverComp φ ψ) =
      schemeHomOverComp (genericFibreRestrict R K f g φ) (genericFibreRestrict R K e f ψ) := by
  apply Subtype.ext
  apply pullback.hom_ext
  · simp [genericFibreRestrict, pullback.lift_fst, pullback.lift_fst_assoc]
  · simp [genericFibreRestrict, pullback.lift_snd]

theorem genericFibreRestrict_endComp (f : X ⟶ Spec (CommRingCat.of R))
    (φ ψ : SchemeHomOver f f) :
    genericFibreRestrict R K f f (schemeHomOverComp φ ψ) =
      schemeHomOverComp (genericFibreRestrict R K f f φ) (genericFibreRestrict R K f f ψ) :=
  genericFibreRestrict_schemeHomOverComp R K f f f φ ψ

end RestrictFunctoriality

section ExtensionEngines

variable {R K : Type u} [CommRing R] [Field K] [Algebra R K]
variable {X Y : Scheme.{u}}

theorem neronHomRestrict_bijective_of_smooth {f : X ⟶ Spec (CommRingCat.of R)}
    (hf : NeronUniqueExtension R K f) {g : Y ⟶ Spec (CommRingCat.of R)} (hg : Smooth g) :
    Function.Bijective (genericFibreRestrict R K f g) :=
  hf Y g hg

theorem neronEndRestrict_bijective_of_smooth {f : X ⟶ Spec (CommRingCat.of R)}
    (hf : NeronUniqueExtension R K f) (hsm : Smooth f) :
    Function.Bijective (genericFibreRestrict R K f f) :=
  hf X f hsm

variable [IsDomain R] [IsDedekindDomain R] [IsFractionRing R K]
variable {f : X ⟶ Spec (CommRingCat.of R)}

theorem NeronModelPropertyBundle.homRestrict_bijective (h : NeronModelPropertyBundle R K f)
    {g : Y ⟶ Spec (CommRingCat.of R)} (hg : Smooth g) :
    Function.Bijective (genericFibreRestrict R K f g) :=
  h.neronMapping Y g hg

theorem NeronModelPropertyBundle.endRestrict_bijective (h : NeronModelPropertyBundle R K f) :
    Function.Bijective (genericFibreRestrict R K f f) :=
  h.neronMapping X f h.smooth

theorem NeronModelPropertyBundle.existsUnique_endExtension (h : NeronModelPropertyBundle R K f)
    (ψ : SchemeHomOver (pullback.snd f (specGenericFibreInclusion R K))
      (pullback.snd f (specGenericFibreInclusion R K))) :
    ∃! φ : SchemeHomOver f f, genericFibreRestrict R K f f φ = ψ :=
  h.endRestrict_bijective.existsUnique ψ

theorem NeronModelPropertyBundle.exists_endExtension_hom (h : NeronModelPropertyBundle R K f)
    (u : pullback f (specGenericFibreInclusion R K) ⟶
      pullback f (specGenericFibreInclusion R K))
    (hu : u ≫ pullback.snd f (specGenericFibreInclusion R K) =
      pullback.snd f (specGenericFibreInclusion R K)) :
    ∃ (v : X ⟶ X) (hv : v ≫ f = f), (genericFibreRestrict R K f f ⟨v, hv⟩).1 = u := by
  obtain ⟨⟨v, hv⟩, hφ⟩ := h.endRestrict_bijective.surjective ⟨u, hu⟩
  exact ⟨v, hv, congrArg Subtype.val hφ⟩

theorem NeronModelPropertyBundle.endExtension_unique_hom (h : NeronModelPropertyBundle R K f)
    {v₁ v₂ : X ⟶ X} (hv₁ : v₁ ≫ f = f) (hv₂ : v₂ ≫ f = f)
    (huv : (genericFibreRestrict R K f f ⟨v₁, hv₁⟩).1 =
      (genericFibreRestrict R K f f ⟨v₂, hv₂⟩).1) :
    v₁ = v₂ :=
  congrArg Subtype.val (h.endRestrict_bijective.injective (Subtype.ext huv))

theorem NeronModelPropertyBundle.integralPoints_bijective (h : NeronModelPropertyBundle R K f) :
    Function.Bijective
      (genericFibreRestrict R K f (𝟙 (Spec (CommRingCat.of R)))) :=
  h.neronMapping (Spec (CommRingCat.of R)) (𝟙 (Spec (CommRingCat.of R))) inferInstance

end ExtensionEngines

section ExtensionEquiv

variable {R K : Type u} [CommRing R] [Field K] [Algebra R K]
variable [IsDomain R] [IsDedekindDomain R] [IsFractionRing R K]
variable {X : Scheme.{u}} {f : X ⟶ Spec (CommRingCat.of R)}

noncomputable def NeronModelPropertyBundle.endExtensionEquiv
    (h : NeronModelPropertyBundle R K f) :
    SchemeHomOver f f ≃
      SchemeHomOver (pullback.snd f (specGenericFibreInclusion R K))
        (pullback.snd f (specGenericFibreInclusion R K)) :=
  Equiv.ofBijective (genericFibreRestrict R K f f) h.endRestrict_bijective

@[simp]
theorem NeronModelPropertyBundle.endExtensionEquiv_apply (h : NeronModelPropertyBundle R K f)
    (φ : SchemeHomOver f f) :
    h.endExtensionEquiv φ = genericFibreRestrict R K f f φ :=
  rfl

@[simp]
theorem NeronModelPropertyBundle.endExtensionEquiv_symm_restrict
    (h : NeronModelPropertyBundle R K f) (φ : SchemeHomOver f f) :
    h.endExtensionEquiv.symm (genericFibreRestrict R K f f φ) = φ := by
  rw [← h.endExtensionEquiv_apply φ]
  exact h.endExtensionEquiv.symm_apply_apply φ

@[simp]
theorem NeronModelPropertyBundle.restrict_endExtensionEquiv_symm
    (h : NeronModelPropertyBundle R K f)
    (ψ : SchemeHomOver (pullback.snd f (specGenericFibreInclusion R K))
      (pullback.snd f (specGenericFibreInclusion R K))) :
    genericFibreRestrict R K f f (h.endExtensionEquiv.symm ψ) = ψ := by
  rw [← h.endExtensionEquiv_apply]
  exact h.endExtensionEquiv.apply_symm_apply ψ

theorem NeronModelPropertyBundle.endExtensionEquiv_symm_id
    (h : NeronModelPropertyBundle R K f) :
    h.endExtensionEquiv.symm
        (schemeHomOverId (pullback.snd f (specGenericFibreInclusion R K))) =
      schemeHomOverId f := by
  apply h.endRestrict_bijective.injective
  rw [h.restrict_endExtensionEquiv_symm]
  exact (genericFibreRestrict_schemeHomOverId R K f).symm

theorem NeronModelPropertyBundle.endExtensionEquiv_symm_comp
    (h : NeronModelPropertyBundle R K f)
    (ψ₁ ψ₂ : SchemeHomOver (pullback.snd f (specGenericFibreInclusion R K))
      (pullback.snd f (specGenericFibreInclusion R K))) :
    h.endExtensionEquiv.symm (schemeHomOverComp ψ₁ ψ₂) =
      schemeHomOverComp (h.endExtensionEquiv.symm ψ₁) (h.endExtensionEquiv.symm ψ₂) := by
  apply h.endRestrict_bijective.injective
  rw [h.restrict_endExtensionEquiv_symm, genericFibreRestrict_endComp,
    h.restrict_endExtensionEquiv_symm, h.restrict_endExtensionEquiv_symm]

theorem NeronModelPropertyBundle.endExtensionEquiv_symm_commute
    (h : NeronModelPropertyBundle R K f)
    {ψ₁ ψ₂ : SchemeHomOver (pullback.snd f (specGenericFibreInclusion R K))
      (pullback.snd f (specGenericFibreInclusion R K))}
    (hcomm : schemeHomOverComp ψ₁ ψ₂ = schemeHomOverComp ψ₂ ψ₁) :
    schemeHomOverComp (h.endExtensionEquiv.symm ψ₁) (h.endExtensionEquiv.symm ψ₂) =
      schemeHomOverComp (h.endExtensionEquiv.symm ψ₂) (h.endExtensionEquiv.symm ψ₁) := by
  rw [← h.endExtensionEquiv_symm_comp, ← h.endExtensionEquiv_symm_comp, hcomm]

theorem NeronModelPropertyBundle.endExtensionEquiv_symm_involution
    (h : NeronModelPropertyBundle R K f)
    {ψ : SchemeHomOver (pullback.snd f (specGenericFibreInclusion R K))
      (pullback.snd f (specGenericFibreInclusion R K))}
    (hinv : schemeHomOverComp ψ ψ =
      schemeHomOverId (pullback.snd f (specGenericFibreInclusion R K))) :
    schemeHomOverComp (h.endExtensionEquiv.symm ψ) (h.endExtensionEquiv.symm ψ) =
      schemeHomOverId f := by
  rw [← h.endExtensionEquiv_symm_comp, hinv, h.endExtensionEquiv_symm_id]

end ExtensionEquiv

section FamilyLayer

variable {R K : Type u} [CommRing R] [Field K] [Algebra R K]
variable [IsDomain R] [IsDedekindDomain R] [IsFractionRing R K]
variable {X : Scheme.{u}} {f : X ⟶ Spec (CommRingCat.of R)}

theorem NeronModelPropertyBundle.existsUnique_familyExtension
    (h : NeronModelPropertyBundle R K f) {J : Type*}
    (T : J → SchemeHomOver (pullback.snd f (specGenericFibreInclusion R K))
      (pullback.snd f (specGenericFibreInclusion R K))) :
    ∃! S : J → SchemeHomOver f f, ∀ j, genericFibreRestrict R K f f (S j) = T j := by
  refine ⟨fun j => h.endExtensionEquiv.symm (T j),
    fun j => h.restrict_endExtensionEquiv_symm (T j), ?_⟩
  intro S' hS'
  funext j
  rw [← hS' j]
  exact (h.endExtensionEquiv_symm_restrict (S' j)).symm

theorem NeronModelPropertyBundle.familyExtension_relation
    (h : NeronModelPropertyBundle R K f) {J : Type*}
    (T : J → SchemeHomOver (pullback.snd f (specGenericFibreInclusion R K))
      (pullback.snd f (specGenericFibreInclusion R K)))
    {i j k : J} (hrel : schemeHomOverComp (T i) (T j) = T k) :
    schemeHomOverComp (h.endExtensionEquiv.symm (T i)) (h.endExtensionEquiv.symm (T j)) =
      h.endExtensionEquiv.symm (T k) := by
  rw [← hrel]
  exact (h.endExtensionEquiv_symm_comp (T i) (T j)).symm

end FamilyLayer

section SatGates

theorem gate_endRestrict_bijective_trivialGroupScheme_zp (p : ℕ) [Fact p.Prime] :
    Function.Bijective
      (genericFibreRestrict ℤ_[p] ℚ_[p] (𝟙 (Spec (CommRingCat.of ℤ_[p])))
        (𝟙 (Spec (CommRingCat.of ℤ_[p])))) :=
  (gate_neronModelPropertyBundle_trivialGroupScheme_zp p).endRestrict_bijective

theorem gate_endExtensionEquiv_symm_id_trivialGroupScheme_z3 :
    (gate_neronModelPropertyBundle_trivialGroupScheme_z3).endExtensionEquiv.symm
        (schemeHomOverId (pullback.snd (𝟙 (Spec (CommRingCat.of ℤ_[3])))
          (specGenericFibreInclusion ℤ_[3] ℚ_[3]))) =
      schemeHomOverId (𝟙 (Spec (CommRingCat.of ℤ_[3]))) :=
  (gate_neronModelPropertyBundle_trivialGroupScheme_z3).endExtensionEquiv_symm_id

theorem gate_existsUnique_familyExtension_trivialGroupScheme_z3
    (T : ℕ → SchemeHomOver
      (pullback.snd (𝟙 (Spec (CommRingCat.of ℤ_[3]))) (specGenericFibreInclusion ℤ_[3] ℚ_[3]))
      (pullback.snd (𝟙 (Spec (CommRingCat.of ℤ_[3]))) (specGenericFibreInclusion ℤ_[3] ℚ_[3]))) :
    ∃! S : ℕ → SchemeHomOver (𝟙 (Spec (CommRingCat.of ℤ_[3]))) (𝟙 (Spec (CommRingCat.of ℤ_[3]))),
      ∀ j, genericFibreRestrict ℤ_[3] ℚ_[3] (𝟙 (Spec (CommRingCat.of ℤ_[3])))
        (𝟙 (Spec (CommRingCat.of ℤ_[3]))) (S j) = T j :=
  (gate_neronModelPropertyBundle_trivialGroupScheme_z3).existsUnique_familyExtension T

end SatGates

end NeronModelInfra

end

end ZInQ.Contrib.CloudW03NeronSurj.FLT
