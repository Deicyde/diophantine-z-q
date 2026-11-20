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
  Source file    : P2M/Sol/S_AlgebraicCurve_exists_transcendental_isSeparable_of_finrank_kaehlerDifferential_eq_one.lean
  Source sha256  : 598d62feca3da7cb0764db239d4b42695e646f4fd042173e47fe7399ada72705
  Retrieved      : pinned read-only clone of the upstream FLT sources (6e837e75), byte-for-byte
  Copyright      : 2026 Anthropic, PBC (see ATTRIBUTION.md of the source for third-party credits)
  Licence        : Apache License, Version 2.0 (see Contrib/CloudW03NeronSurj/LICENSE and NOTICE)

NOTICE OF MODIFICATION (Apache-2.0 §4(b)). This file has been changed from the original
(H5 lane4 port to Lean 4.35.0 / Mathlib 56a005855ea17e0b0958f73ec801ae140b0a1679).
Mechanical changes; no statement, hypothesis, definition or proof term was weakened or omitted:
  * 1 `r2nos_namespace_dual` shim line(s) after source `namespace` commands (Mathlib names of the same source namespace stay visible, as in the unprefixed original).
  * 1 `r2nos_open_dual`/`r2nos_open_scoped_dual` shim line(s) after source `open` commands (completes each opened namespace by its other half where the port splits one source root namespace between Mathlib root and the prefix).
  * 1 import of the lane4 Mathlib-db584 compatibility module `ZInQKernel.Contrib.CloudR2NOS.Source.Compat.PresheafOfModulesMonoidal` added (as in every located lane4 port copy).
  * 1 internal `import`(s) retargeted to `ZInQKernel.Contrib.CloudR2NOS.Source.*` / `ZInQKernel.Contrib.CloudW03NeronSurj.Vendor.*` (published W03 duals bound, see ledger) / port utilities.
  * 2 scope(s) the source leaves open at EOF closed explicitly so the port namespace can be closed (no-op in the original).
  * file-level `set_option`s inserted after the port namespace: autoImplicit false; backward.isDefEq.respectTransparency.types false; backward.isDefEq.respectTransparency.instanceSearchTypes false (non-numeric, as in the located C5 conformance copies). NO maxHeartbeats/synthInstance option (numeric options omitted).
  * `import ZInQKernel.Contrib.CloudR2NOS.Source.PortUtilExt` added (port commands) and `open ZInQ.Contrib.CloudW03NeronSurj.FLT` inserted so the source's generalized field notation resolves the isolated declarations exactly as in the unprefixed original.
  * whole file wrapped in `namespace ZInQ.Contrib.CloudW03NeronSurj.FLT … end ZInQ.Contrib.CloudW03NeronSurj.FLT`.
-/

import Mathlib.RingTheory.Unramified.Field
import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
import ZInQKernel.Contrib.CloudW03NeronSurj.PortUtil
import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.PresheafOfModulesMonoidal
import ZInQKernel.Contrib.CloudR2NOS.Source.PortUtilExt

namespace ZInQ.Contrib.CloudW03NeronSurj.FLT

open ZInQ.Contrib.CloudW03NeronSurj.FLT

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false

namespace P2MW.S_AlgebraicCurve_exists_transcendental_isSeparable_of_finrank_kaehlerDifferential_eq_one
r2nos_namespace_dual

set_option autoImplicit false

universe u v

open IntermediateField
r2nos_open_dual "IntermediateField"

theorem solution
    {K : Type u} {F : Type v} [Field K] [Field F] [Algebra K F] [Algebra.EssFiniteType K F]
    [Algebra.Transcendental K F] (hΩ : Module.finrank F Ω[F⁄K] = 1) :
    ∃ t : F, Transcendental K t ∧ FiniteDimensional K⟮t⟯ F ∧ Algebra.IsSeparable K⟮t⟯ F := by
  classical

  obtain ⟨t, ht⟩ : ∃ t : F, KaehlerDifferential.D K F t ≠ 0 := by
    by_contra h
    push Not at h
    have htop : (⊤ : Submodule F Ω[F⁄K]) = ⊥ := by
      rw [← KaehlerDifferential.span_range_derivation, Submodule.span_eq_bot]
      rintro _ ⟨x, rfl⟩
      exact h x
    have h0 : Module.finrank F Ω[F⁄K] = 0 := by
      rw [← finrank_top, htop, finrank_bot]
    omega

  have hspan : ∀ ω : Ω[F⁄K], ∃ c : F, c • KaehlerDifferential.D K F t = ω :=
    (finrank_eq_one_iff_of_nonzero' _ ht).mp hΩ

  have hDt : KaehlerDifferential.D K⟮t⟯ F t = 0 := by
    have h := (KaehlerDifferential.D K⟮t⟯ F).map_algebraMap (AdjoinSimple.gen K t)
    rwa [AdjoinSimple.algebraMap_gen] at h
  have hsub : Subsingleton Ω[F⁄K⟮t⟯] := by
    refine subsingleton_of_forall_eq 0 fun ω => ?_
    obtain ⟨ω₀, rfl⟩ := KaehlerDifferential.map_surjective K K⟮t⟯ F ω
    obtain ⟨c, rfl⟩ := hspan ω₀
    rw [map_smul, KaehlerDifferential.map_D, Algebra.algebraMap_self, RingHom.id_apply, hDt,
      smul_zero]

  haveI : Algebra.FormallyUnramified K⟮t⟯ F := ⟨hsub⟩
  haveI : Algebra.EssFiniteType K⟮t⟯ F := Algebra.EssFiniteType.of_comp K K⟮t⟯ F
  have hsep : Algebra.IsSeparable K⟮t⟯ F := Algebra.FormallyUnramified.isSeparable K⟮t⟯ F
  have hfin : Module.Finite K⟮t⟯ F := Algebra.FormallyUnramified.finite_of_free K⟮t⟯ F

  refine ⟨t, ?_, hfin, hsep⟩
  show ¬IsAlgebraic K t
  intro halg
  haveI : Algebra.IsAlgebraic K K⟮t⟯ := isAlgebraic_adjoin_simple halg.isIntegral
  haveI : Algebra.IsAlgebraic K⟮t⟯ F := Algebra.IsAlgebraic.of_finite K⟮t⟯ F
  have hKF : Algebra.IsAlgebraic K F := Algebra.IsAlgebraic.trans (R := K) (S := K⟮t⟯) (A := F)
  exact Algebra.transcendental_iff_not_isAlgebraic.mp ‹Algebra.Transcendental K F› hKF

#print axioms solution
end S_AlgebraicCurve_exists_transcendental_isSeparable_of_finrank_kaehlerDifferential_eq_one
end P2MW

end ZInQ.Contrib.CloudW03NeronSurj.FLT
