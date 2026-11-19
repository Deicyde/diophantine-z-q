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
  Source file    : P2M/Sol/S_AlgebraicGeometry_OModulePresheaf_cechFinite_of_forall_cechFinite_idealPowQuot.lean
  Source sha256  : 396dcb5acc94d5f3f27a55a33e87732aeee82fb490e523db71573b8039eb5de9
  Retrieved      : pinned read-only clone of the upstream FLT sources (6e837e75), byte-for-byte
  Copyright      : 2026 Anthropic, PBC (see ATTRIBUTION.md of the source for third-party credits)
  Licence        : Apache License, Version 2.0 (see Contrib/CloudW03NeronSurj/LICENSE and NOTICE)

NOTICE OF MODIFICATION (Apache-2.0 §4(b)). This file has been changed from the original
(H5 lane4 port to Lean 4.35.0 / Mathlib 56a005855ea17e0b0958f73ec801ae140b0a1679).
Mechanical changes; no statement, hypothesis, definition or proof term was weakened or omitted:
  * 1 `_root_.` reference(s)/declaration head(s) to source-specific names qualified with `ZInQ.Contrib.CloudW03NeronSurj.FLT`.
  * 4 `p2m_*` command/tactic occurrence(s) renamed to the H76 `w03_*` / lane4 `r2nos_*` port commands.
  * 4 `r2nos_namespace_dual` shim line(s) after source `namespace` commands (Mathlib names of the same source namespace stay visible, as in the unprefixed original).
  * 1 `r2nos_open_dual`/`r2nos_open_scoped_dual` shim line(s) after source `open` commands (completes each opened namespace by its other half where the port splits one source root namespace between Mathlib root and the prefix).
  * REMOVED source option(s) (default-options rule): `set_option maxHeartbeats 6400000`; `set_option synthInstance.maxHeartbeats 1600000`; `set_option linter.unusedSectionVars false`; `set_option linter.unusedSimpArgs false`; `set_option linter.unusedVariables false`.
  * 1 import of the lane4 Mathlib-db584 compatibility module `ZInQKernel.Contrib.CloudR2NOS.Source.Compat.PresheafOfModulesMonoidal` added (as in every located lane4 port copy).
  * 5 internal `import`(s) retargeted to `ZInQKernel.Contrib.CloudR2NOS.Source.*` / `ZInQKernel.Contrib.CloudW03NeronSurj.Vendor.*` (published W03 duals bound, see ledger) / port utilities.
  * 2 scope(s) the source leaves open at EOF closed explicitly so the port namespace can be closed (no-op in the original).
  * file-level `set_option`s inserted after the port namespace: autoImplicit false; backward.isDefEq.respectTransparency.types false; backward.isDefEq.respectTransparency.instanceSearchTypes false (non-numeric, as in the located C5 conformance copies). NO maxHeartbeats/synthInstance option (numeric options omitted).
  * `import ZInQKernel.Contrib.CloudR2NOS.Source.PortUtilExt` added (port commands) and `open ZInQ.Contrib.CloudW03NeronSurj.FLT` inserted so the source's generalized field notation resolves the isolated declarations exactly as in the unprefixed original.
  * whole file wrapped in `namespace ZInQ.Contrib.CloudW03NeronSurj.FLT … end ZInQ.Contrib.CloudW03NeronSurj.FLT`.
-/

import Mathlib.AlgebraicGeometry.Morphisms.Separated
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.RingTheory.Localization.Away.Basic
import ZInQKernel.Contrib.CloudR2NOS.Source.Definitions.Def_AlgebraicGeometry_OModulePresheafIdealFiltration
import ZInQKernel.Contrib.CloudR2NOS.Source.Theorems.Thm_AlgebraicGeometry_OModulePresheaf_exists_idealPowSub_eq_bot
import ZInQKernel.Contrib.CloudR2NOS.Source.Theorems.Thm_AlgebraicGeometry_OModulePresheaf_cechFinite_of_affSES_mid
import ZInQKernel.Contrib.CloudR2NOS.Source.Theorems.Thm_AlgebraicGeometry_OModulePresheaf_cechFinite_of_affSES_right
import ZInQKernel.Contrib.CloudW03NeronSurj.PortUtil
import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.PresheafOfModulesMonoidal
import ZInQKernel.Contrib.CloudR2NOS.Source.PortUtilExt

namespace ZInQ.Contrib.CloudW03NeronSurj.FLT

open ZInQ.Contrib.CloudW03NeronSurj.FLT

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false

namespace P2MW.S_AlgebraicGeometry_OModulePresheaf_cechFinite_of_forall_cechFinite_idealPowQuot
r2nos_namespace_dual

set_option autoImplicit false

w03_open "AlgebraicGeometry P2MW.S_AlgebraicGeometry_OModulePresheaf_cechFinite_of_forall_cechFinite_idealPowQuot.AlgebraicGeometry CategoryTheory TopologicalSpace Opposite"

noncomputable section

namespace AlgebraicGeometry
r2nos_namespace_dual
w03_export "AlgebraicGeometry" "IsLocallyNoetherian Spec Scheme Scheme.IdealSheafData.vanishingIdeal IsSeparated Scheme.IdealSheafData OModulePresheaf.idealPowQuot OModulePresheaf.zero OModulePresheaf OModulePresheaf.cochain OModulePresheaf.CechFinite OModulePresheaf.IsCoherent OModulePresheaf.IsQuasicoherent OModulePresheaf.SupportedIn OModulePresheaf.exists_idealPowSub_eq_bot OModulePresheaf.cechFinite_of_affSES_mid OModulePresheaf.cechFinite_of_affSES_right"
namespace OModulePresheaf
r2nos_namespace_dual
w03_export "AlgebraicGeometry.OModulePresheaf" "idealPowSub idealPow idealPowSub_antitone idealPowQuot idealPowSES idealPowZeroSES zero AffSES cochain CechFinite IsCoherent IsQuasicoherent SupportedIn exists_idealPowSub_eq_bot cechFinite_of_affSES_mid cechFinite_of_affSES_right"
namespace G4T
r2nos_namespace_dual
w03_open "AlgebraicGeometry.OModulePresheaf AlgebraicGeometry"

universe u

section Wrappers
variable {R : Type u} [CommRing R] [IsNoetherianRing R] {V : Scheme.{u}} {π : V ⟶ Spec (.of R)} [IsSeparated π]
  {F₁ F₂ F₃ : OModulePresheaf π}
theorem cechFinite_of_affSES_mid' (K : V.OrderedAffineCover) (S : AffSES F₁ F₂ F₃) (h₁ : F₁.CechFinite K)
    (h₃ : F₃.CechFinite K) : F₂.CechFinite K := OModulePresheaf.cechFinite_of_affSES_mid S K h₁ h₃
theorem cechFinite_of_affSES_right' (K : V.OrderedAffineCover) (S : AffSES F₁ F₂ F₃) (h₁ : F₁.CechFinite K)
    (h₂ : F₂.CechFinite K) : F₃.CechFinite K := OModulePresheaf.cechFinite_of_affSES_right S K h₁ h₂
end Wrappers

section ZeroBase

variable {R : Type u} [CommRing R] {V : Scheme.{u}} (π : V ⟶ Spec (.of R))

theorem cechFinite_zero (K : V.OrderedAffineCover) :
    OModulePresheaf.CechFinite (K := K) (OModulePresheaf.zero π) := by
  have hCF : ∀ q, Subsingleton
      (OModulePresheaf.cochain (OModulePresheaf.zero π) K q) :=
    fun q => ⟨fun a b => funext fun s => Subsingleton.elim _ _⟩
  exact ⟨(haveI := hCF 0; ⟨⟨∅, Subsingleton.elim _ _⟩⟩),
    fun i => (haveI := hCF (i + 1); ⟨⟨∅, Subsingleton.elim _ _⟩⟩)⟩

theorem cechFinite_idealPow_of_forall_subsingleton [IsSeparated π]
    (K : V.OrderedAffineCover) (I : V.IdealSheafData) (F : OModulePresheaf π) (N : ℕ)
    (hN : ∀ (q : ℕ) (s : K.Idx q),
      idealPowSub π I F N (K.inter s) = ⊥) :
    OModulePresheaf.CechFinite (K := K) (idealPow π I F N) := by
  have hCF : ∀ q, Subsingleton
      (OModulePresheaf.cochain (idealPow π I F N) K q) := fun q => by
    refine ⟨fun a b => funext fun s => Subtype.ext ?_⟩
    have hav := (Submodule.mem_bot R).mp (hN q s ▸ (a s).2 :
      (idealPowSub π I F N (K.inter s)).subtype (a s) ∈ ⊥)
    have hbv := (Submodule.mem_bot R).mp (hN q s ▸ (b s).2 :
      (idealPowSub π I F N (K.inter s)).subtype (b s) ∈ ⊥)
    exact hav.trans hbv.symm
  exact ⟨(haveI := hCF 0; ⟨⟨∅, Subsingleton.elim _ _⟩⟩),
    fun i => (haveI := hCF (i + 1); ⟨⟨∅, Subsingleton.elim _ _⟩⟩)⟩

theorem exists_cechFinite_idealPow [IsSeparated π] [IsLocallyNoetherian V]
    (K : V.OrderedAffineCover) (Y : Closeds V) (F : OModulePresheaf π)
    (hFc : OModulePresheaf.IsCoherent F) (hFq : OModulePresheaf.IsQuasicoherent F)
    (hFs : OModulePresheaf.SupportedIn F Y) :
    ∃ N, OModulePresheaf.CechFinite (K := K)
      (idealPow π (Scheme.IdealSheafData.vanishingIdeal Y) F N) := by

  let T : Type u := Σ q : Fin (Fintype.card K.ι), K.Idx q
  haveI : Fintype T := inferInstance
  choose Nqs hNqs using fun t : T => OModulePresheaf.exists_idealPowSub_eq_bot π Y F hFc hFq hFs
    ⟨K.inter t.2, K.isAffineOpen_inter π t.2⟩
  refine ⟨Finset.univ.sup Nqs,
    cechFinite_idealPow_of_forall_subsingleton π K _ F _ fun q s => ?_⟩

  rcases lt_or_ge q (Fintype.card K.ι) with hq | hq
  · exact le_bot_iff.mp
      ((hNqs ⟨⟨q, hq⟩, s⟩).symm ▸ idealPowSub_antitone π _ F
        (Finset.le_sup (Finset.mem_univ (⟨⟨q, hq⟩, s⟩ : T))) _)
  · have hcard := Fintype.card_le_of_injective s.1 s.2.injective
    rw [Fintype.card_fin] at hcard; omega

theorem cechFinite_of_forall_cechFinite_idealPowQuot [IsNoetherianRing R] [IsSeparated π]
    [IsLocallyNoetherian V] (K : V.OrderedAffineCover) (Y : Closeds V) (F : OModulePresheaf π)
    (hFc : OModulePresheaf.IsCoherent F) (hFq : OModulePresheaf.IsQuasicoherent F)
    (hFs : OModulePresheaf.SupportedIn F Y)
    (hStep : ∀ k, OModulePresheaf.CechFinite (K := K)
      (idealPowQuot π (Scheme.IdealSheafData.vanishingIdeal Y) F k)) :
    OModulePresheaf.CechFinite (K := K) F := by
  set I := Scheme.IdealSheafData.vanishingIdeal Y
  obtain ⟨N, hN⟩ := exists_cechFinite_idealPow π K Y F hFc hFq hFs

  have hSmul : ∀ j, OModulePresheaf.CechFinite (K := K)
      (idealPow π I F (N - j)) := fun j => by
    induction j with
    | zero => simpa using hN
    | succ j ih =>
      rcases Nat.lt_or_ge j N with hj | hj
      · have heq : N - j = (N - (j + 1)) + 1 := by omega
        exact cechFinite_of_affSES_mid' K
          (idealPowSES π I F (N - (j + 1))) (heq ▸ ih) (hStep _)
      · rw [Nat.sub_eq_zero_of_le (Nat.le_succ_of_le hj)]
        rw [Nat.sub_eq_zero_of_le hj] at ih; exact ih
  exact cechFinite_of_affSES_right' K
    (idealPowZeroSES π I F)
    (cechFinite_zero π K) (by simpa using hSmul N)

end ZeroBase

end AlgebraicGeometry.OModulePresheaf.G4T

end

universe u

open _root_.AlgebraicGeometry _root_.ZInQ.Contrib.CloudW03NeronSurj.FLT.P2MW.S_AlgebraicGeometry_OModulePresheaf_cechFinite_of_forall_cechFinite_idealPowQuot.AlgebraicGeometry in
r2nos_open_dual "_root_.AlgebraicGeometry _root_.ZInQ.Contrib.CloudW03NeronSurj.FLT.P2MW.S_AlgebraicGeometry_OModulePresheaf_cechFinite_of_forall_cechFinite_idealPowQuot.AlgebraicGeometry" in
theorem solution {R : Type u} [CommRing R] [IsNoetherianRing R] {V : Scheme.{u}} (π : V ⟶ Spec (.of R)) [IsSeparated π] [IsLocallyNoetherian V] (K : V.OrderedAffineCover) (Y : TopologicalSpace.Closeds V) (F : OModulePresheaf π) (hFc : F.IsCoherent) (hFq : F.IsQuasicoherent) (hFs : F.SupportedIn Y) (hStep : ∀ k, (OModulePresheaf.idealPowQuot π (Scheme.IdealSheafData.vanishingIdeal Y) F k).CechFinite K) : F.CechFinite K :=
  AlgebraicGeometry.OModulePresheaf.G4T.cechFinite_of_forall_cechFinite_idealPowQuot π K Y F hFc hFq hFs hStep
end S_AlgebraicGeometry_OModulePresheaf_cechFinite_of_forall_cechFinite_idealPowQuot
end P2MW

end ZInQ.Contrib.CloudW03NeronSurj.FLT
