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
  Source file    : P2M/Sol/S_AlgebraicGeometry_eq_of_forall_specMap_quotient_maximalIdeal_pow_comp_eq_of_isSchemeTheoreticallyDominant.lean
  Source sha256  : 21f812a9d23a06d6aed1333e93586b0822315bb8519c61875766eea0acfd4ed3
  Retrieved      : pinned read-only clone of the upstream FLT sources (6e837e75), byte-for-byte
  Copyright      : 2026 Anthropic, PBC (see ATTRIBUTION.md of the source for third-party credits)
  Licence        : Apache License, Version 2.0 (see Contrib/CloudW03NeronSurj/LICENSE and NOTICE)

NOTICE OF MODIFICATION (Apache-2.0 §4(b)). This file has been changed from the original
(H5 lane4 port to Lean 4.35.0 / Mathlib 56a005855ea17e0b0958f73ec801ae140b0a1679).
Mechanical changes; no statement, hypothesis, definition or proof term was weakened or omitted:
  * 3 `p2m_*` command/tactic occurrence(s) renamed to the H76 `w03_*` / lane4 `r2nos_*` port commands.
  * 3 `r2nos_namespace_dual` shim line(s) after source `namespace` commands (Mathlib names of the same source namespace stay visible, as in the unprefixed original).
  * 1 import of the lane4 Mathlib-db584 compatibility module `ZInQKernel.Contrib.CloudR2NOS.Source.Compat.PresheafOfModulesMonoidal` added (as in every located lane4 port copy).
  * 2 internal `import`(s) retargeted to `ZInQKernel.Contrib.CloudR2NOS.Source.*` / `ZInQKernel.Contrib.CloudW03NeronSurj.Vendor.*` (published W03 duals bound, see ledger) / port utilities.
  * 2 scope(s) the source leaves open at EOF closed explicitly so the port namespace can be closed (no-op in the original).
  * file-level `set_option`s inserted after the port namespace: autoImplicit false; backward.isDefEq.respectTransparency.types false; backward.isDefEq.respectTransparency.instanceSearchTypes false (non-numeric, as in the located C5 conformance copies). NO maxHeartbeats/synthInstance option (numeric options omitted).
  * `import ZInQKernel.Contrib.CloudR2NOS.Source.PortUtilExt` added (port commands) and `open ZInQ.Contrib.CloudW03NeronSurj.FLT` inserted so the source's generalized field notation resolves the isolated declarations exactly as in the unprefixed original.
  * whole file wrapped in `namespace ZInQ.Contrib.CloudW03NeronSurj.FLT … end ZInQ.Contrib.CloudW03NeronSurj.FLT`.
-/

import Mathlib
import ZInQKernel.Contrib.CloudR2NOS.Source.Theorems.Thm_AlgebraicGeometry_exists_mem_and_iota_comp_eq_of_forall_specMap_quotient_maximalIdeal_pow_comp_eq
import ZInQKernel.Contrib.CloudW03NeronSurj.PortUtil
import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.PresheafOfModulesMonoidal
import ZInQKernel.Contrib.CloudR2NOS.Source.PortUtilExt

namespace ZInQ.Contrib.CloudW03NeronSurj.FLT

open ZInQ.Contrib.CloudW03NeronSurj.FLT

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false

namespace P2MW.S_AlgebraicGeometry_eq_of_forall_specMap_quotient_maximalIdeal_pow_comp_eq_of_isSchemeTheoreticallyDominant
r2nos_namespace_dual

set_option autoImplicit false

w03_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry P2MW.S_AlgebraicGeometry_eq_of_forall_specMap_quotient_maximalIdeal_pow_comp_eq_of_isSchemeTheoreticallyDominant.AlgebraicGeometry TopologicalSpace Opposite"

universe u

namespace AlgebraicGeometry
r2nos_namespace_dual
w03_export "AlgebraicGeometry" "IsLocallyNoetherian IsClosedImmersion.isIso_iff_ker_eq_bot Scheme.Hom.le_ker_comp Scheme.Hom Opens.isDominant_ι isClosedImmersion_equalizer_ι_left Spec IsIntegral Spec.map Scheme IsSchemeTheoreticallyDominant IsClosedImmersion IsSeparated IsDominant IsSchemeTheoreticallyDominant.of_isDominant exists_mem_and_iota_comp_eq_of_forall_specMap_quotient_maximalIdeal_pow_comp_eq"
namespace InfinitesimalRigidityGlobal
r2nos_namespace_dual
w03_open "AlgebraicGeometry"

theorem eq_of_isSchemeTheoreticallyDominant_comp_eq {W X Y Z : Scheme.{u}} (ι : W ⟶ X)
    [IsSchemeTheoreticallyDominant ι] (f g : X ⟶ Y) (s : Y ⟶ Z) [IsSeparated s]
    (hs : f ≫ s = g ≫ s) (hU : ι ≫ f = ι ≫ g) : f = g := by
  let X' : Over Z := Over.mk (f ≫ s)
  let Y' : Over Z := Over.mk s
  let U' : Over Z := Over.mk (ι ≫ f ≫ s)
  let f' : X' ⟶ Y' := Over.homMk f
  let g' : X' ⟶ Y' := Over.homMk g hs.symm
  let ι' : U' ⟶ X' := Over.homMk ι
  have : IsSeparated Y'.hom := ‹_›
  have hlift : (equalizer.lift ι' (by ext1; exact hU)).left ≫ (equalizer.ι f' g').left = ι := by
    rw [← Over.comp_left, equalizer.lift_ι]
    rfl
  have hker : (equalizer.ι f' g').left.ker = ⊥ := by
    have := Scheme.Hom.le_ker_comp (equalizer.lift ι' (by ext1; exact hU)).left
      (equalizer.ι f' g').left
    rw [hlift] at this
    exact le_bot_iff.mp (this.trans (le_of_eq ι.ker_eq_bot))
  have : IsIso (equalizer.ι f' g').left := IsClosedImmersion.isIso_iff_ker_eq_bot.mpr hker
  have key : (equalizer.ι f' g').left ≫ f = (equalizer.ι f' g').left ≫ g :=
    congr($(equalizer.condition f' g').left)
  simpa using congrArg (fun φ => inv ((equalizer.ι f' g').left) ≫ φ) key

theorem eq_of_forall_jets_eq {X Y Z : Scheme.{u}} [IsLocallyNoetherian X]
    (hX : ∀ U : X.Opens, (U : Set X).Nonempty → IsSchemeTheoreticallyDominant U.ι)
    (f g : X ⟶ Y) (s : Y ⟶ Z) [IsSeparated s] (hs : f ≫ s = g ≫ s) (x : X)
    (h : ∀ n : ℕ,
      Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk
          (IsLocalRing.maximalIdeal (X.presheaf.stalk x) ^ n))) ≫ X.fromSpecStalk x ≫ f =
        Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk
          (IsLocalRing.maximalIdeal (X.presheaf.stalk x) ^ n))) ≫ X.fromSpecStalk x ≫ g) :
    f = g := by
  obtain ⟨U, hxU, hU⟩ :=
    AlgebraicGeometry.exists_mem_and_iota_comp_eq_of_forall_specMap_quotient_maximalIdeal_pow_comp_eq
      f g x h
  haveI : IsSchemeTheoreticallyDominant U.ι := hX U ⟨x, hxU⟩
  exact eq_of_isSchemeTheoreticallyDominant_comp_eq U.ι f g s hs hU

theorem eq_of_forall_jets_eq_of_isIntegral {X Y Z : Scheme.{u}} [IsIntegral X]
    [IsLocallyNoetherian X]
    (f g : X ⟶ Y) (s : Y ⟶ Z) [IsSeparated s] (hs : f ≫ s = g ≫ s) (x : X)
    (h : ∀ n : ℕ,
      Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk
          (IsLocalRing.maximalIdeal (X.presheaf.stalk x) ^ n))) ≫ X.fromSpecStalk x ≫ f =
        Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk
          (IsLocalRing.maximalIdeal (X.presheaf.stalk x) ^ n))) ≫ X.fromSpecStalk x ≫ g) :
    f = g := by
  refine eq_of_forall_jets_eq (fun U hU => ?_) f g s hs x h
  haveI : IsDominant U.ι := AlgebraicGeometry.Opens.isDominant_ι (U.2.dense hU)
  exact IsSchemeTheoreticallyDominant.of_isDominant _

end AlgebraicGeometry.InfinitesimalRigidityGlobal

theorem solution
    {X Y Z : Scheme.{u}} [IsLocallyNoetherian X]
    (hX : ∀ U : X.Opens, (U : Set X).Nonempty → IsSchemeTheoreticallyDominant U.ι)
    (f g : X ⟶ Y) (s : Y ⟶ Z) [IsSeparated s] (hs : f ≫ s = g ≫ s) (x : X)
    (h : ∀ n : ℕ,
      Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk
          (IsLocalRing.maximalIdeal (X.presheaf.stalk x) ^ n))) ≫ X.fromSpecStalk x ≫ f =
        Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk
          (IsLocalRing.maximalIdeal (X.presheaf.stalk x) ^ n))) ≫ X.fromSpecStalk x ≫ g) :
    f = g :=
  AlgebraicGeometry.InfinitesimalRigidityGlobal.eq_of_forall_jets_eq hX f g s hs x h
end S_AlgebraicGeometry_eq_of_forall_specMap_quotient_maximalIdeal_pow_comp_eq_of_isSchemeTheoreticallyDominant
end P2MW

end ZInQ.Contrib.CloudW03NeronSurj.FLT
