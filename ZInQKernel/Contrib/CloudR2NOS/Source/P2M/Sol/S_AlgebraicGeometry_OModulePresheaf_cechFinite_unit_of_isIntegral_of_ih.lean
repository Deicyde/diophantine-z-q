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
  Source file    : P2M/Sol/S_AlgebraicGeometry_OModulePresheaf_cechFinite_unit_of_isIntegral_of_ih.lean
  Source sha256  : 88e90026fe434d6ed78f62dc94119e680bf33932d2cae98bacd7a4ef7e5aaae8
  Retrieved      : pinned read-only clone of the upstream FLT sources (6e837e75), byte-for-byte
  Copyright      : 2026 Anthropic, PBC (see ATTRIBUTION.md of the source for third-party credits)
  Licence        : Apache License, Version 2.0 (see Contrib/CloudW03NeronSurj/LICENSE and NOTICE)

NOTICE OF MODIFICATION (Apache-2.0 §4(b)). This file has been changed from the original
(H5 lane4 port to Lean 4.35.0 / Mathlib 56a005855ea17e0b0958f73ec801ae140b0a1679).
Mechanical changes; no statement, hypothesis, definition or proof term was weakened or omitted:
  * 5 `p2m_*` command/tactic occurrence(s) renamed to the H76 `w03_*` / lane4 `r2nos_*` port commands.
  * 4 `r2nos_namespace_dual` shim line(s) after source `namespace` commands (Mathlib names of the same source namespace stay visible, as in the unprefixed original).
  * 2 `attribute [-simp]`/`[-instance]` guard line(s) -> `r2nos_erase_attr` (unknown or already-erased names warn instead of aborting; these lines only remove simp lemmas/instances).
  * 1 import of the lane4 Mathlib-db584 compatibility module `ZInQKernel.Contrib.CloudR2NOS.Source.Compat.PresheafOfModulesMonoidal` added (as in every located lane4 port copy).
  * 15 internal `import`(s) retargeted to `ZInQKernel.Contrib.CloudR2NOS.Source.*` / `ZInQKernel.Contrib.CloudW03NeronSurj.Vendor.*` (published W03 duals bound, see ledger) / port utilities.
  * 2 scope(s) the source leaves open at EOF closed explicitly so the port namespace can be closed (no-op in the original).
  * file-level `set_option`s inserted after the port namespace: autoImplicit false; backward.isDefEq.respectTransparency.types false; backward.isDefEq.respectTransparency.instanceSearchTypes false (non-numeric, as in the located C5 conformance copies). NO maxHeartbeats/synthInstance option (numeric options omitted).
  * `import ZInQKernel.Contrib.CloudR2NOS.Source.PortUtilExt` added (port commands) and `open ZInQ.Contrib.CloudW03NeronSurj.FLT` inserted so the source's generalized field notation resolves the isolated declarations exactly as in the unprefixed original.
  * whole file wrapped in `namespace ZInQ.Contrib.CloudW03NeronSurj.FLT … end ZInQ.Contrib.CloudW03NeronSurj.FLT`.
-/

import ZInQKernel.Contrib.CloudR2NOS.Source.Definitions.Def_AlgebraicGeometry_OModulePresheafLerayDoubleComplex
import ZInQKernel.Contrib.CloudR2NOS.Source.Definitions.Def_AlgebraicGeometry_ProjSpaceCover
import ZInQKernel.Contrib.CloudR2NOS.Source.Theorems.Thm_AlgebraicGeometry_ChowDatum_nonempty
import ZInQKernel.Contrib.CloudR2NOS.Source.Theorems.Thm_AlgebraicGeometry_ChowDatumProj_nonempty_of
import ZInQKernel.Contrib.CloudR2NOS.Source.Theorems.Thm_AlgebraicGeometry_OModulePresheaf_cechFinite_unit_of_isClosedImmersion_proj
import ZInQKernel.Contrib.CloudR2NOS.Source.Theorems.Thm_AlgebraicGeometry_OModulePresheaf_Leray_nonempty_HTot_equiv
import ZInQKernel.Contrib.CloudR2NOS.Source.Theorems.Thm_AlgebraicGeometry_OModulePresheaf_Leray_nonempty_E2I_equiv
import ZInQKernel.Contrib.CloudR2NOS.Source.Theorems.Thm_AlgebraicGeometry_OModulePresheaf_Leray_isCoherent_relHPresheaf_chow
import ZInQKernel.Contrib.CloudR2NOS.Source.Theorems.Thm_AlgebraicGeometry_OModulePresheaf_Leray_isQuasicoherent_relHPresheaf_chow
import ZInQKernel.Contrib.CloudR2NOS.Source.Theorems.Thm_AlgebraicGeometry_OModulePresheaf_Leray_supportedIn_relHPresheaf_chow
import ZInQKernel.Contrib.CloudR2NOS.Source.Theorems.Thm_AlgebraicGeometry_OModulePresheaf_Leray_exists_chowSES
import ZInQKernel.Contrib.CloudR2NOS.Source.Theorems.Thm_DoubleComplex_Convergence_finite_E2_q0
import ZInQKernel.Contrib.CloudR2NOS.Source.Theorems.Thm_DoubleComplex_boundedSpectralSequence
import ZInQKernel.Contrib.CloudR2NOS.Source.Theorems.Thm_AlgebraicGeometry_OModulePresheaf_cechFinite_of_affSES_left
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.RingTheory.Noetherian.Basic
import ZInQKernel.Contrib.CloudW03NeronSurj.PortUtil
import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.PresheafOfModulesMonoidal
import ZInQKernel.Contrib.CloudR2NOS.Source.PortUtilExt

namespace ZInQ.Contrib.CloudW03NeronSurj.FLT

open ZInQ.Contrib.CloudW03NeronSurj.FLT

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false

namespace P2MW.S_AlgebraicGeometry_OModulePresheaf_cechFinite_unit_of_isIntegral_of_ih
r2nos_namespace_dual
r2nos_erase_attr "instance" "ProjSpaceCech.GradedModule.H.module ProjSpaceCech.GradedModule.H.addCommGroup ProjSpaceCech.GradedModule.sec.instAdd ProjSpaceCech.GradedModule.sec.instNeg ProjSpaceCech.GradedModule.acg ProjSpaceCech.GradedModule.Frac.setoid ProjSpaceCech.GradedModule.modR ProjSpaceCech.GradedModule.sec.instModule ProjSpaceCech.GradedModule.sec.instAddCommGroup ProjSpaceCech.GradedModule.sec.instZero ProjSpaceCech.GradedModule.Presentation.fJ ProjSpaceCech.GradedModule.sec.instSMul ProjSpaceCech.Twist.H.module ProjSpaceCech.Idx.instFintype ProjSpaceCech.Twist.H.addCommGroup ProjSpaceCech.Idx.instDecidableEq ProjSpaceCech.Twist.Mon.instDecidableEq ProjSpaceCech.Twist.cochain.instAddCommGroup ProjSpaceCech.Twist.cochain.instModule AlgebraicGeometry.OModulePresheaf.instSubsingletonObjZero"
r2nos_erase_attr "simp" "ProjSpaceCech.GradedModule.mk.injEq ProjSpaceCech.GradedModule.mk.sizeOf_spec ProjSpaceCech.GradedModule.Frac.mk.sizeOf_spec ProjSpaceCech.GradedModule.Presentation.mk.injEq ProjSpaceCech.GradedModule.Frac.mk.injEq ProjSpaceCech.GradedModule.Presentation.mk.sizeOf_spec ProjSpaceCech.GradedModule.Hom.shift_toLinearMap ProjSpaceCech.GradedModule.Hom.mk.sizeOf_spec ProjSpaceCech.GradedModule.Hom.mk.injEq AlgebraicGeometry.OModulePresheaf.prod_obj AlgebraicGeometry.OModulePresheaf.restrOpen_obj AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.injEq AlgebraicGeometry.OModulePresheaf.pushforward_obj AlgebraicGeometry.OModulePresheaf.im_obj AlgebraicGeometry.OModulePresheaf.pow_obj AlgebraicGeometry.OModulePresheaf.fstHom_app AlgebraicGeometry.OModulePresheaf.ker_obj AlgebraicGeometry.OModulePresheaf.coker_obj AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCover.preimage_U AlgebraicGeometry.OModulePresheaf.sndHom_app"

set_option autoImplicit false

universe u

w03_open "CategoryTheory AlgebraicGeometry P2MW.S_AlgebraicGeometry_OModulePresheaf_cechFinite_unit_of_isIntegral_of_ih.AlgebraicGeometry TopologicalSpace Opposite"

attribute [local instance] MvPolynomial.gradedAlgebra

namespace AlgebraicGeometry
r2nos_namespace_dual
w03_export "AlgebraicGeometry" "IsProper Spec IsIntegral Scheme IsSeparated Scheme.OrderedAffineCover OModulePresheaf OModulePresheaf.cechFinite_iff OModulePresheaf.unit ProjSpace.stdCoverPullback ChowDatum ChowDatumProj ChowDatum.nonempty ChowDatumProj.nonempty_of OModulePresheaf.cechFinite_of_affSES_left"
namespace OModulePresheaf
r2nos_namespace_dual
w03_export "AlgebraicGeometry.OModulePresheaf" "CechFinite cechFinite_iff IsCoherent IsQuasicoherent SupportedIn unit cechFinite_unit_of_isClosedImmersion_proj cechFinite_of_affSES_left"
namespace Leray
r2nos_namespace_dual
w03_export "AlgebraicGeometry.OModulePresheaf.Leray" "LerayDblCpx relHPresheaf nonempty_HTot_equiv nonempty_E2I_equiv isCoherent_relHPresheaf_chow isQuasicoherent_relHPresheaf_chow supportedIn_relHPresheaf_chow exists_chowSES"
w03_open "AlgebraicGeometry.OModulePresheaf.Leray AlgebraicGeometry.OModulePresheaf AlgebraicGeometry"

variable {R : Type u} [CommRing R] [IsNoetherianRing R] {Z : Scheme.{u}}
variable (πZ : Z ⟶ Spec (.of R)) [IsProper πZ] [IsIntegral Z]

theorem chowCompl_lt_top (D : ChowDatumProj πZ) :
    (⟨(D.U : Set Z)ᶜ, D.U.isOpen.isClosed_compl⟩ : Closeds Z) < ⊤ := by
  rw [lt_top_iff_ne_top]
  intro h
  have hU : (D.U : Set Z) = ∅ := by
    have := congrArg (fun C : Closeds Z => (C : Set Z)) h
    simp only [Closeds.coe_top] at this
    exact Set.compl_univ_iff.mp this
  obtain ⟨x, hx⟩ := D.hU_dense.nonempty
  rw [hU] at hx
  exact hx

theorem cechFinite_relHPresheaf_zero_chow (K : Z.OrderedAffineCover) (D : ChowDatumProj πZ)
    (ih : ∀ F : OModulePresheaf πZ, F.IsCoherent → F.IsQuasicoherent →
      ∀ Y' < (⊤ : Closeds Z), F.SupportedIn Y' → F.CechFinite K) :
    (relHPresheaf D.p πZ (ProjSpace.stdCoverPullback D.ιN) 0).CechFinite K := by
  haveI : IsSeparated (D.p ≫ πZ) := inferInstance
  set K' : Scheme.OrderedAffineCover D.V' := ProjSpace.stdCoverPullback D.ιN with hK'
  set LD := LerayDblCpx D.p πZ K K' with hLD
  obtain ⟨conv⟩ := DoubleComplex.boundedSpectralSequence R LD

  have hiva : (OModulePresheaf.unit (D.p ≫ πZ)).CechFinite K' := by
    rw [← D.hoverN]; exact cechFinite_unit_of_isClosedImmersion_proj D.ιN
  rw [OModulePresheaf.cechFinite_iff] at hiva
  have hH : ∀ n, Module.Finite R (DoubleComplex.HTot LD n) := by
    obtain ⟨⟨e0⟩, es⟩ := nonempty_HTot_equiv D.p πZ K K'
    rintro (_ | n)
    · haveI := hiva.1; exact Module.Finite.equiv e0.symm
    · obtain ⟨e⟩ := es n
      haveI := hiva.2 n; exact Module.Finite.equiv e.symm

  obtain ⟨e2z, e2s⟩ := nonempty_E2I_equiv D.p πZ K K'
  have hE₂ : ∀ a b, 1 ≤ b → Module.Finite R (DoubleComplex.E₂I LD a b) := by
    intro a b hb
    have haf : (relHPresheaf D.p πZ K' b).CechFinite K :=
      ih _ (isCoherent_relHPresheaf_chow πZ D b) (isQuasicoherent_relHPresheaf_chow πZ D b) _
        (chowCompl_lt_top πZ D) (supportedIn_relHPresheaf_chow πZ D b hb)
    rw [OModulePresheaf.cechFinite_iff] at haf
    rcases a with _ | a'
    · obtain ⟨e⟩ := e2z b
      haveI := haf.1; exact Module.Finite.equiv e.symm
    · obtain ⟨e⟩ := e2s a' b
      haveI := haf.2 a'; exact Module.Finite.equiv e.symm

  have hE₂0 : ∀ a, Module.Finite R (DoubleComplex.E₂I LD a 0) := by
    intro a
    rcases le_or_gt a LD.N with hle | hgt
    · exact DoubleComplex.Convergence.finite_E2_q0 conv hH hE₂ a hle
    · haveI : Subsingleton (LD.C a 0) := LD.hBound a 0 (Or.inl hgt.le)
      haveI : Subsingleton (DoubleComplex.E₂I LD a 0) := inferInstance
      infer_instance
  rw [OModulePresheaf.cechFinite_iff]
  refine ⟨?_, fun a => ?_⟩
  · obtain ⟨e⟩ := e2z 0
    exact @Module.Finite.equiv _ _ _ _ _ _ _ _ (hE₂0 0) e
  · obtain ⟨e⟩ := e2s a 0
    exact @Module.Finite.equiv _ _ _ _ _ _ _ _ (hE₂0 (a + 1)) e

theorem cechFinite_unit_of_isIntegral_of_ih' (K : Z.OrderedAffineCover)
    (ih : ∀ F : OModulePresheaf πZ, F.IsCoherent → F.IsQuasicoherent →
      ∀ Y' < (⊤ : Closeds Z), F.SupportedIn Y' → F.CechFinite K) :
    (OModulePresheaf.unit πZ).CechFinite K := by
  obtain ⟨D⟩ := ChowDatumProj.nonempty_of πZ (ChowDatum.nonempty πZ)
  have h8 := cechFinite_relHPresheaf_zero_chow πZ K D ih
  obtain ⟨Q, S, hQc, hQq, hQs⟩ := exists_chowSES πZ D
  have hQ : Q.CechFinite K := ih Q hQc hQq _ (chowCompl_lt_top πZ D) hQs
  exact OModulePresheaf.cechFinite_of_affSES_left S.toAffSES K h8 hQ

end AlgebraicGeometry.OModulePresheaf.Leray

theorem solution
    {R : Type u} [CommRing R] [IsNoetherianRing R] {Z : Scheme.{u}} (πZ : Z ⟶ Spec (.of R)) [IsProper πZ]
    [IsIntegral Z] (K : Z.OrderedAffineCover)
    (ih : ∀ F : OModulePresheaf πZ, F.IsCoherent → F.IsQuasicoherent →
      ∀ Y' < (⊤ : TopologicalSpace.Closeds Z), F.SupportedIn Y' → F.CechFinite K) :
    (OModulePresheaf.unit πZ).CechFinite K :=
  AlgebraicGeometry.OModulePresheaf.Leray.cechFinite_unit_of_isIntegral_of_ih' πZ K ih
end S_AlgebraicGeometry_OModulePresheaf_cechFinite_unit_of_isIntegral_of_ih
end P2MW

end ZInQ.Contrib.CloudW03NeronSurj.FLT
