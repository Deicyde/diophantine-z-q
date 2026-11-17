/-
NEW EDITION (H5 lane4 , 2026-11-17, Parent route (E)). NOT a recovery: no recorded port
SHA exists for this module (lead 2026-11-17T06:06Z). Generated deterministically from the pinned
upstream file by the documented lane4 port transform, as reproduced by the located C5 conformance
pair (Thm/S_AlgebraicGeometry_Scheme_Modules_ProjPresentation_exists_of_iso), numeric options
omitted. SOURCE ONLY, UNCOMPILED. Native HELD.

Vendored, unmodified in substance, from the Fermat's Last Theorem Lean development.

  Source project : https://github.com/anthropics/fermats-last-theorem
  Source revision: 6e837e75355538c7f80bab5b956861e86c4eacc2
  Source file    : P2M/Sol/S_AlgebraicGeometry_Scheme_Modules_ProjPresentation_mem_preimage_basicOpen_iff.lean
  Source sha256  : e79b7aabd7b44d8a6540f542197d89d97a240d6f82d56e4ec59c0779f9fda2fd
  Retrieved      : pinned read-only clone ~/flt-src (6e837e75), byte-for-byte
  Copyright      : 2026 Anthropic, PBC (see ATTRIBUTION.md of the source for third-party credits)
  Licence        : Apache License, Version 2.0 (see Contrib/CloudW03NeronSurj/LICENSE and NOTICE)

NOTICE OF MODIFICATION (Apache-2.0 §4(b)). This file has been changed from the original
(H5 lane4 port to Lean 4.35.0 / Mathlib 56a005855ea17e0b0958f73ec801ae140b0a1679).
Mechanical changes; no statement, hypothesis, definition or proof term was weakened or omitted:
  * 5 `p2m_*` command/tactic occurrence(s) renamed to the H76 `w03_*` / lane4 `r2nos_*` port commands.
  * 5 `r2nos_namespace_dual` shim line(s) after source `namespace` commands (Mathlib names of the same source namespace stay visible, as in the unprefixed original).
  * 1 `r2nos_open_dual`/`r2nos_open_scoped_dual` shim line(s) after source `open` commands (completes each opened namespace by its other half where the port splits one source root namespace between Mathlib root and the prefix).
  * 1 import of the lane4 Mathlib-db584 compatibility module `ZInQKernel.Contrib.CloudR2NOS.Source.Compat.PresheafOfModulesMonoidal` added (as in every located lane4 port copy).
  * 3 internal `import`(s) retargeted to `ZInQKernel.Contrib.CloudR2NOS.Source.*` / `ZInQKernel.Contrib.CloudW03NeronSurj.Vendor.*` (published W03 duals bound, see ledger) / port utilities.
  * 2 scope(s) the source leaves open at EOF closed explicitly so the port namespace can be closed (no-op in the original).
  * file-level `set_option`s inserted after the port namespace: autoImplicit false; backward.isDefEq.respectTransparency.types false; backward.isDefEq.respectTransparency.instanceSearchTypes false (non-numeric, as in the located C5 conformance copies). NO maxHeartbeats/synthInstance option (numeric options omitted).
  * `import ZInQKernel.Contrib.CloudR2NOS.Source.PortUtilExt` added (port commands) and `open ZInQ.Contrib.CloudW03NeronSurj.FLT` inserted so the source's generalized field notation resolves the isolated declarations exactly as in the unprefixed original.
  * whole file wrapped in `namespace ZInQ.Contrib.CloudW03NeronSurj.FLT … end ZInQ.Contrib.CloudW03NeronSurj.FLT`.
-/

import Mathlib
import ZInQKernel.Contrib.CloudR2NOS.Source.Definitions.Def_AlgebraicGeometry_ProjSpace
import ZInQKernel.Contrib.CloudR2NOS.Source.Definitions.Def_AlgebraicGeometry_ModulesProjPresentation
import ZInQKernel.Contrib.CloudW03NeronSurj.PortUtil
import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.PresheafOfModulesMonoidal
import ZInQKernel.Contrib.CloudR2NOS.Source.PortUtilExt

namespace ZInQ.Contrib.CloudW03NeronSurj.FLT

open ZInQ.Contrib.CloudW03NeronSurj.FLT

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false

namespace P2MW.S_AlgebraicGeometry_Scheme_Modules_ProjPresentation_mem_preimage_basicOpen_iff
r2nos_namespace_dual

set_option autoImplicit false

w03_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry P2MW.S_AlgebraicGeometry_Scheme_Modules_ProjPresentation_mem_preimage_basicOpen_iff.AlgebraicGeometry"

universe u

open Opposite TopologicalSpace
r2nos_open_dual "Opposite TopologicalSpace"

attribute [local instance] MvPolynomial.gradedAlgebra

namespace AlgebraicGeometry
r2nos_namespace_dual
w03_export "AlgebraicGeometry" "Scheme.Hom Scheme.Hom.germ_stalkMap_apply Spec Scheme Proj.mem_basicOpen Proj Proj.stalkIso' Proj.basicOpen Scheme.Modules Proj.iSup_basicOpen_eq_top Proj.awayToSection ProjectiveSpectrum.Proj.awayToSection_germ ProjSpace.irrelevant_le_span_X ProjSpace.ratio"
namespace Scheme
r2nos_namespace_dual
w03_export "AlgebraicGeometry.Scheme" "mem_basicOpen Hom mk Γ Hom.germ_stalkMap_apply basicOpen Modules Opens Modules.map_smul"
namespace Modules
r2nos_namespace_dual
w03_export "AlgebraicGeometry.Scheme.Modules" "presheaf Hom map_smul ProjPresentation"
w03_open "AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme AlgebraicGeometry"

namespace PresChart
r2nos_namespace_dual

section chart

variable (R : Type u) [CommRing R] (N : ℕ)

local notation "𝒜" => MvPolynomial.homogeneousSubmodule (Fin (N + 1)) R

lemma isUnit_germ_ratio_iff (i j : Fin (N + 1)) (y : Proj 𝒜)
    (hy : y ∈ Proj.basicOpen 𝒜 (MvPolynomial.X j)) :
    IsUnit ((Proj 𝒜).presheaf.germ (Proj.basicOpen 𝒜 (MvPolynomial.X j)) y hy
      (Proj.awayToSection 𝒜 (MvPolynomial.X j) (ProjSpace.ratio R N j i))) ↔
      y ∈ Proj.basicOpen 𝒜 (MvPolynomial.X i) := by
  have hle : Submonoid.powers (MvPolynomial.X j : MvPolynomial (Fin (N + 1)) R) ≤
      y.asHomogeneousIdeal.toIdeal.primeCompl :=
    Submonoid.powers_le.mpr ((Proj.mem_basicOpen 𝒜 _ y).mp hy)
  have h := ConcreteCategory.congr_hom
    (ProjectiveSpectrum.Proj.awayToSection_germ 𝒜 (MvPolynomial.X j) y hy) (ProjSpace.ratio R N j i)
  have h' : (Proj 𝒜).presheaf.germ (Proj.basicOpen 𝒜 (MvPolynomial.X j)) y hy
      (Proj.awayToSection 𝒜 (MvPolynomial.X j) (ProjSpace.ratio R N j i)) =
      (Proj.stalkIso' 𝒜 y).symm (HomogeneousLocalization.mapId 𝒜 hle (ProjSpace.ratio R N j i)) := h
  have e1 : IsUnit ((Proj.stalkIso' 𝒜 y).symm (HomogeneousLocalization.mapId 𝒜 hle (ProjSpace.ratio R N j i))) ↔
      IsUnit (HomogeneousLocalization.mapId 𝒜 hle (ProjSpace.ratio R N j i)) :=
    ⟨fun hu => by simpa using hu.map (Proj.stalkIso' 𝒜 y), fun hu => hu.map _⟩
  rw [h']
  refine e1.trans ?_
  rw [← HomogeneousLocalization.isUnit_iff_isUnit_val, ProjSpace.ratio,
    HomogeneousLocalization.Away.mk, HomogeneousLocalization.map_mk, HomogeneousLocalization.val_mk,
    Localization.mk_eq_mk', IsLocalization.AtPrime.isUnit_mk'_iff, Proj.mem_basicOpen]
  exact Iff.rfl

lemma exists_mem_basicOpen_X (y : Proj 𝒜) : ∃ j : Fin (N + 1), y ∈ Proj.basicOpen 𝒜 (MvPolynomial.X j) := by
  have htop := Proj.iSup_basicOpen_eq_top 𝒜 (MvPolynomial.X : Fin (N + 1) → MvPolynomial (Fin (N + 1)) R)
    (ProjSpace.irrelevant_le_span_X R N)
  have hy : y ∈ (⊤ : (Proj 𝒜).Opens) := trivial
  rw [← htop] at hy
  exact Opens.mem_iSup.mp hy

end chart

section pres

variable {R : Type u} [CommRing R] {X : Scheme.{u}} {f : X ⟶ Spec (.of R)} {M : X.Modules} {N : ℕ}
    (𝔓 : M.ProjPresentation f N)

local notation "𝒜" => MvPolynomial.homogeneousSubmodule (Fin (N + 1)) R

noncomputable abbrev resTop (V : X.Opens) (s : Γ(M, ⊤)) : Γ(M, V) :=
  M.presheaf.map (homOfLE (le_top : V ≤ ⊤)).op s

omit 𝔓 in
lemma res_resTop {V W : X.Opens} (h : W ≤ V) (s : Γ(M, ⊤)) :
    M.presheaf.map (homOfLE h).op (resTop V s) = resTop W s := by
  change (M.presheaf.map (homOfLE (le_top : V ≤ ⊤)).op ≫ M.presheaf.map (homOfLE h).op) s = _
  rw [← CategoryTheory.Functor.map_comp]
  rfl

theorem main (i : Fin (N + 1)) (x : X) :
    x ∈ 𝔓.toProj ⁻¹ᵁ Proj.basicOpen 𝒜 (MvPolynomial.X i) ↔
      ∃ U : X.Opens, x ∈ U ∧ ∀ V : X.Opens, V ≤ U →
        Function.Bijective fun g : Γ(X, V) => g • resTop V (𝔓.σ i) := by
  constructor
  · intro hx
    exact ⟨_, hx, fun V hV => 𝔓.frame i V hV⟩
  · rintro ⟨U, hxU, hU⟩
    obtain ⟨j, hj⟩ := exists_mem_basicOpen_X R N (𝔓.toProj x)

    have hxW : x ∈ U ⊓ 𝔓.toProj ⁻¹ᵁ Proj.basicOpen 𝒜 (MvPolynomial.X j) := ⟨hxU, hj⟩
    have hWU : U ⊓ 𝔓.toProj ⁻¹ᵁ Proj.basicOpen 𝒜 (MvPolynomial.X j) ≤ U := inf_le_left
    have hWj : U ⊓ 𝔓.toProj ⁻¹ᵁ Proj.basicOpen 𝒜 (MvPolynomial.X j) ≤
        𝔓.toProj ⁻¹ᵁ Proj.basicOpen 𝒜 (MvPolynomial.X j) := inf_le_right

    have hρ : X.presheaf.map (homOfLE hWj).op
        (𝔓.toProj.app (Proj.basicOpen 𝒜 (MvPolynomial.X j))
          (Proj.awayToSection 𝒜 (MvPolynomial.X j) (ProjSpace.ratio R N j i))) •
        resTop (U ⊓ 𝔓.toProj ⁻¹ᵁ Proj.basicOpen 𝒜 (MvPolynomial.X j)) (𝔓.σ j) =
        resTop (U ⊓ 𝔓.toProj ⁻¹ᵁ Proj.basicOpen 𝒜 (MvPolynomial.X j)) (𝔓.σ i) := by
      have h := congrArg (M.presheaf.map (homOfLE hWj).op) (𝔓.app_ratio_smul j i)
      rw [Modules.map_smul, res_resTop, res_resTop] at h
      exact h

    obtain ⟨g, hg⟩ := (hU _ hWU).2 (resTop (U ⊓ 𝔓.toProj ⁻¹ᵁ Proj.basicOpen 𝒜 (MvPolynomial.X j)) (𝔓.σ j))
    dsimp only at hg

    have h1 : (g * X.presheaf.map (homOfLE hWj).op
        (𝔓.toProj.app (Proj.basicOpen 𝒜 (MvPolynomial.X j))
          (Proj.awayToSection 𝒜 (MvPolynomial.X j) (ProjSpace.ratio R N j i)))) •
        resTop (U ⊓ 𝔓.toProj ⁻¹ᵁ Proj.basicOpen 𝒜 (MvPolynomial.X j)) (𝔓.σ j) =
        (1 : Γ(X, U ⊓ 𝔓.toProj ⁻¹ᵁ Proj.basicOpen 𝒜 (MvPolynomial.X j))) •
          resTop (U ⊓ 𝔓.toProj ⁻¹ᵁ Proj.basicOpen 𝒜 (MvPolynomial.X j)) (𝔓.σ j) := by
      rw [mul_smul, hρ, hg, one_smul]
    have hunit : IsUnit (X.presheaf.map (homOfLE hWj).op
        (𝔓.toProj.app (Proj.basicOpen 𝒜 (MvPolynomial.X j))
          (Proj.awayToSection 𝒜 (MvPolynomial.X j) (ProjSpace.ratio R N j i)))) := by
      refine isUnit_iff_exists_inv.mpr ⟨g, ?_⟩
      rw [mul_comm]
      exact (𝔓.frame j _ hWj).1 h1

    have hgerm : IsUnit (X.presheaf.germ _ x hxW (X.presheaf.map (homOfLE hWj).op
        (𝔓.toProj.app (Proj.basicOpen 𝒜 (MvPolynomial.X j))
          (Proj.awayToSection 𝒜 (MvPolynomial.X j) (ProjSpace.ratio R N j i))))) := hunit.map _
    rw [TopCat.Presheaf.germ_res_apply] at hgerm
    have hgerm' : IsUnit (X.presheaf.germ (𝔓.toProj ⁻¹ᵁ Proj.basicOpen 𝒜 (MvPolynomial.X j)) x hj
        (𝔓.toProj.app (Proj.basicOpen 𝒜 (MvPolynomial.X j))
          (Proj.awayToSection 𝒜 (MvPolynomial.X j) (ProjSpace.ratio R N j i)))) := hgerm
    rw [← Scheme.Hom.germ_stalkMap_apply] at hgerm'
    haveI : IsLocalHom (ConcreteCategory.hom (𝔓.toProj.stalkMap x)) :=
      inferInstanceAs (IsLocalHom (𝔓.toProj.stalkMap x).hom)
    rw [isUnit_map_iff] at hgerm'
    exact (isUnit_germ_ratio_iff R N i j _ hj).mp hgerm'

end pres

end PresChart

end AlgebraicGeometry.Scheme.Modules

theorem solution
    {R : Type u} [CommRing R] {X : Scheme.{u}} {f : X ⟶ Spec (.of R)} {M : X.Modules} {N : ℕ}
    (𝔓 : M.ProjPresentation f N) (i : Fin (N + 1)) (x : X) :
    x ∈ 𝔓.toProj ⁻¹ᵁ Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) R) (MvPolynomial.X i) ↔
      ∃ U : X.Opens, x ∈ U ∧ ∀ V : X.Opens, V ≤ U →
        Function.Bijective fun g : Γ(X, V) => g • (M.presheaf.map (homOfLE (le_top : V ≤ ⊤)).op (𝔓.σ i) : Γ(M, V)) :=
  AlgebraicGeometry.Scheme.Modules.PresChart.main 𝔓 i x
end S_AlgebraicGeometry_Scheme_Modules_ProjPresentation_mem_preimage_basicOpen_iff
end P2MW

end ZInQ.Contrib.CloudW03NeronSurj.FLT
