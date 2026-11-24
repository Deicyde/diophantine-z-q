/-
NOS-CORE PROBE STAGING COPY (lane C4, 2026-11-17). NOT an H5 edition:
probe world only; it enters H5 only by the lead binding plus C6 review. No recorded port
SHA exists for this module (lead 2026-11-17T06:06Z). Generated deterministically from the pinned
upstream file by the documented lane4 port transform, as reproduced by the located C5 conformance
pair (Thm/S_AlgebraicGeometry_Scheme_Modules_ProjPresentation_exists_of_iso), numeric options
omitted. SOURCE ONLY, UNCOMPILED. Native HELD.

Vendored, unmodified in substance, from the Fermat's Last Theorem Lean development.

  Source project : https://github.com/anthropics/fermats-last-theorem
  Source revision: 6e837e75355538c7f80bab5b956861e86c4eacc2
  Source file    : Definitions/Def_AlgebraicGeometry_ModulesSectionZeroScheme.lean
  Source sha256  : a264518c47209e06f3c8b410d8f617588055c7eabbf19e263eb95eb5a161d25e
  Retrieved      : pinned read-only clone of the upstream FLT sources (6e837e75), byte-for-byte
  Copyright      : 2026 Anthropic, PBC (see ATTRIBUTION.md of the source for third-party credits)
  Licence        : Apache License, Version 2.0 (see Contrib/CloudW03NeronSurj/LICENSE and NOTICE)

NOTICE OF MODIFICATION (Apache-2.0 §4(b)). This file has been changed from the original
(H5 lane4 port to Lean 4.35.0 / Mathlib 56a005855ea17e0b0958f73ec801ae140b0a1679).
Mechanical changes; no statement, hypothesis, definition or proof term was weakened or omitted:
  * 2 `r2nos_namespace_dual` shim line(s) after source `namespace` commands (Mathlib names of the same source namespace stay visible, as in the unprefixed original).
  * 1 `r2nos_open_dual`/`r2nos_open_scoped_dual` shim line(s) after source `open` commands (completes each opened namespace by its other half where the port splits one source root namespace between Mathlib root and the prefix).
  * 1 import of the lane4 Mathlib-db584 compatibility module `ZInQKernel.Contrib.CloudR2NOS.Source.Compat.PresheafOfModulesMonoidal` added (as in every located lane4 port copy).
  * 2 internal `import`(s) retargeted to `ZInQKernel.Contrib.CloudR2NOS.Source.*` / `ZInQKernel.Contrib.CloudW03NeronSurj.Vendor.*` (published W03 duals bound, see ledger) / port utilities.
  * file-level `set_option`s inserted after the port namespace: autoImplicit false; backward.isDefEq.respectTransparency.types false; backward.isDefEq.respectTransparency.instanceSearchTypes false (non-numeric, as in the located C5 conformance copies). NO maxHeartbeats/synthInstance option (numeric options omitted).
  * `import ZInQKernel.Contrib.CloudR2NOS.Source.PortUtilExt` added (port commands) and `open ZInQ.Contrib.CloudW03NeronSurj.FLT` inserted so the source's generalized field notation resolves the isolated declarations exactly as in the unprefixed original.
  * whole file wrapped in `namespace ZInQ.Contrib.CloudW03NeronSurj.FLT … end ZInQ.Contrib.CloudW03NeronSurj.FLT`.
-/

import ZInQKernel.Contrib.CloudR2NOS.Source.Definitions.Def_AlgebraicGeometry_IdealSheafModule
import ZInQKernel.Contrib.CloudR2NOS.Source.Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.PresheafOfModulesMonoidal
import ZInQKernel.Contrib.CloudR2NOS.Source.PortUtilExt

namespace ZInQ.Contrib.CloudW03NeronSurj.FLT

open ZInQ.Contrib.CloudW03NeronSurj.FLT

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory
r2nos_open_dual "CategoryTheory CategoryTheory.Limits MonoidalCategory"

noncomputable section

namespace AlgebraicGeometry
r2nos_namespace_dual

namespace Scheme.Modules
r2nos_namespace_dual

variable {X : Scheme.{u}} {M : X.Modules}

def toUnitSection (U : X.Opens) (r : Γ(X, U)) : Γ(𝟙_ X.Modules, U) := r

def ofUnitSection (U : X.Opens) (m : Γ(𝟙_ X.Modules, U)) : Γ(X, U) := m

@[simp] lemma ofUnitSection_toUnitSection (U : X.Opens) (r : Γ(X, U)) :
    ofUnitSection U (toUnitSection U r) = r := rfl

@[simp] lemma toUnitSection_ofUnitSection (U : X.Opens) (m : Γ(𝟙_ X.Modules, U)) :
    toUnitSection U (ofUnitSection U m) = m := rfl

lemma ofUnitSection_injective (U : X.Opens) : Function.Injective (ofUnitSection (X := X) U) :=
  fun _ _ h => h

lemma ofUnitSection_map {U V : X.Opens} (i : V ⟶ U) (m : Γ(𝟙_ X.Modules, U)) :
    ofUnitSection V ((𝟙_ X.Modules).presheaf.map i.op m) =
      X.presheaf.map i.op (ofUnitSection U m) := rfl

lemma ofUnitSection_smul (U : X.Opens) (r : Γ(X, U)) (m : Γ(𝟙_ X.Modules, U)) :
    ofUnitSection U (r • m) = r * ofUnitSection U m := rfl

def restrictSection (s : 𝟙_ X.Modules ⟶ M) (U : X.Opens) : Γ(M.restrict U.ι, ⊤) :=
  s.app (U.ι ''ᵁ ⊤) (toUnitSection (U.ι ''ᵁ ⊤) 1)

def coeff (s : 𝟙_ X.Modules ⟶ M) (U : X.Opens)
    (φ : M.restrict U.ι ⟶ 𝟙_ (U : Scheme.{u}).Modules) : Γ(X, U) :=
  U.topIso.hom (ofUnitSection ⊤ (φ.app ⊤ (restrictSection s U)))

def coeffIdeal (s : 𝟙_ X.Modules ⟶ M) (U : X.Opens) : Ideal Γ(X, U) :=
  Ideal.span (Set.range (coeff s U))

lemma coeff_mem_coeffIdeal (s : 𝟙_ X.Modules ⟶ M) (U : X.Opens)
    (φ : M.restrict U.ι ⟶ 𝟙_ (U : Scheme.{u}).Modules) : coeff s U φ ∈ coeffIdeal s U :=
  Ideal.subset_span ⟨φ, rfl⟩

def zeroSchemeIdeal (s : 𝟙_ X.Modules ⟶ M) : X.IdealSheafData :=
  sInf {J : X.IdealSheafData | ∀ U : X.affineOpens, coeffIdeal s U.1 ≤ J.ideal U}

abbrev zeroScheme (s : 𝟙_ X.Modules ⟶ M) : Scheme.{u} :=
  (zeroSchemeIdeal s).subscheme

lemma zeroSchemeIdeal_le {s : 𝟙_ X.Modules ⟶ M} {J : X.IdealSheafData}
    (h : ∀ U : X.affineOpens, coeffIdeal s U.1 ≤ J.ideal U) : zeroSchemeIdeal s ≤ J :=
  sInf_le h

lemma le_zeroSchemeIdeal {s : 𝟙_ X.Modules ⟶ M} {K : X.IdealSheafData}
    (h : ∀ J : X.IdealSheafData, (∀ U : X.affineOpens, coeffIdeal s U.1 ≤ J.ideal U) → K ≤ J) :
    K ≤ zeroSchemeIdeal s :=
  le_sInf fun _ hJ => h _ hJ

lemma zeroSchemeIdeal_eq_of_isLeast {s : 𝟙_ X.Modules ⟶ M} {P : X.IdealSheafData}
    (hP : IsLeast {J : X.IdealSheafData | ∀ U : X.affineOpens, coeffIdeal s U.1 ≤ J.ideal U} P) :
    zeroSchemeIdeal s = P :=
  hP.isGLB.sInf_eq

def pullbackSection {X' : Scheme.{u}} (F : X' ⟶ X) (s : 𝟙_ X.Modules ⟶ M) :
    𝟙_ X'.Modules ⟶ (Scheme.Modules.pullback F).obj M :=
  (Scheme.Modules.pullbackUnitIso F).inv ≫ (Scheme.Modules.pullback F).map s

@[simp] lemma pullbackSection_def {X' : Scheme.{u}} (F : X' ⟶ X) (s : 𝟙_ X.Modules ⟶ M) :
    pullbackSection F s =
      (Scheme.Modules.pullbackUnitIso F).inv ≫ (Scheme.Modules.pullback F).map s :=
  rfl

def restrictIsoOfLE {U W : X.Opens} (h : W ≤ U)
    (e : (Scheme.Modules.pullback U.ι).obj M ≅ SheafOfModules.unit (U : Scheme.{u}).ringCatSheaf) :
    M.restrict W.ι ≅ 𝟙_ (W : Scheme.{u}).Modules :=
  (restrictFunctorCongr (X.homOfLE_ι h).symm).app M ≪≫
    (restrictFunctorComp (X.homOfLE h) U.ι).app M ≪≫
    (restrictFunctor (X.homOfLE h)).mapIso ((restrictFunctorIsoPullback U.ι).app M ≪≫ e) ≪≫
    (restrictFunctorIsoPullback (X.homOfLE h)).app _ ≪≫
    Scheme.Modules.pullbackUnitIso (X.homOfLE h)

theorem IsInvertible.exists_restrict_iso (hM : Scheme.Modules.IsInvertible M) {V : X.Opens} {x : X}
    (hx : x ∈ V) :
    ∃ U : X.affineOpens, x ∈ U.1 ∧ U.1 ≤ V ∧
      Nonempty (M.restrict U.1.ι ≅ 𝟙_ (U.1 : Scheme.{u}).Modules) := by
  obtain ⟨U₀, hxU₀, ⟨e⟩⟩ := hM.exists_trivialization x
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, hUle⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open (show x ∈ V ⊓ U₀ from ⟨hx, hxU₀⟩)
      (V ⊓ U₀).isOpen
  exact ⟨⟨U, hU⟩, hxU, fun y hy => (hUle hy).1, ⟨restrictIsoOfLE (fun y hy => (hUle hy).2) e⟩⟩

def sectionDual (s : 𝟙_ X.Modules ⟶ M) : Scheme.Modules.dual M ⟶ 𝟙_ X.Modules :=
  (MonoidalClosed.pre s).app (𝟙_ X.Modules) ≫
    (MonoidalClosed.unitIsoSelf (𝟙_ X.Modules)).hom

end Scheme.Modules

def Scheme.IdealSheafData.invModuleSection {X : Scheme.{u}} (I : X.IdealSheafData) :
    𝟙_ X.Modules ⟶ I.invModule :=
  MonoidalClosed.curry' I.moduleι

end AlgebraicGeometry

end

end ZInQ.Contrib.CloudW03NeronSurj.FLT
