/- Additional modification notice, 2026-11-16: Cloud Batch 3 Worker 13
retargeted only repository module paths into the task-owned CloudB3W13
directories. Canonical mathematical declaration names and statements
are retained. Recovery and later compatibility changes are documented
in the accompanying source manifest and NOTICE. -/
/-
Vendored, unmodified in substance, from the Fermat's Last Theorem Lean development.

  Source project : https://github.com/anthropics/fermats-last-theorem
  Source revision: 6e837e75355538c7f80bab5b956861e86c4eacc2
  Source file    : P2M/Sol/S_AlgebraicGeometry_isReduced_of_smooth_of_field.lean
  Retrieved      : 2026-11-14 (git smart-protocol blob, byte-for-byte; sha256 in lane4 port manifest)
  Copyright      : 2026 Anthropic, PBC (see ATTRIBUTION.md of the source for third-party credits)
  Licence        : Apache License, Version 2.0 (see Contrib/CloudW03NeronSurj/LICENSE and NOTICE)

NOTICE OF MODIFICATION (Apache-2.0 §4(b)). This file has been changed from the original
(H5 lane4 port to Lean 4.35.0 / Mathlib 56a005855ea17e0b0958f73ec801ae140b0a1679, 2026-11-14).
Mechanical changes; no statement, hypothesis, definition or proof term was weakened or
omitted unless listed under manual repairs:
  * 12 `p2m_*` command(s) renamed to the H76 `w03_*` / lane4 `r2nos_*` port commands.
  * 3 `r2nos_namespace_dual` shim line(s) after source `namespace` commands (Mathlib names of the same source namespace stay visible, as in the unprefixed original).
  * 2 declaration(s) named `_root_.X` isolated as `_root_.ZInQ.Contrib.CloudW03NeronSurj.FLT.X`.
  * 1 internal `import`(s) retargeted to `ZInQKernel.Contrib.CloudB3W13Shared.R2NOS.*` / `ZInQKernel.Contrib.CloudW03NeronSurj.Vendor.*` / port utilities.
  * 2 scope(s) the source leaves open at EOF closed explicitly so the port namespace can be closed (Lean closes these implicitly at EOF in the original; no-op).
  * file-level `set_option`s inserted after the port namespace, reproducing the source build environment: autoImplicit false (source lakefile.lean leanOptions); maxHeartbeats 4000000 (source lakefile.lean leanOptions); synthInstance.maxHeartbeats 400000 (source lakefile.lean leanOptions); backward.isDefEq.respectTransparency.types false (source lakefile.lean leanOptions); backward.isDefEq.respectTransparency.instanceSearchTypes false (Lean 4.35 option absent from source Lean 4.33.1; `false` restores 4.33.1 behaviour).
  * `import ZInQKernel.Contrib.CloudB3W13Shared.R2NOS.PortUtilExt` added (port commands) and `open ZInQ.Contrib.CloudW03NeronSurj.FLT` inserted so the source's generalized field notation resolves the isolated declarations exactly as in the unprefixed original.
  * whole file wrapped in `namespace ZInQ.Contrib.CloudW03NeronSurj.FLT … end ZInQ.Contrib.CloudW03NeronSurj.FLT`.
-/

import Mathlib
import ZInQKernel.Contrib.CloudW03NeronSurj.PortUtil
import ZInQKernel.Contrib.CloudB3W13Shared.R2NOS.PortUtilExt

namespace ZInQ.Contrib.CloudW03NeronSurj.FLT

open ZInQ.Contrib.CloudW03NeronSurj.FLT

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false

namespace P2MW.S_AlgebraicGeometry_isReduced_of_smooth_of_field
r2nos_namespace_dual
w03_open "AlgebraicGeometry P2MW.S_AlgebraicGeometry_isReduced_of_smooth_of_field.AlgebraicGeometry CategoryTheory"

universe u

section RingLevel

namespace Algebra w03_export "Algebra" "EssFiniteType IsSmoothAt.exists_isStandardEtale_mvPolynomial linearMap_apply smoothLocus_eq_univ_iff FormallyEtale.iff_formallyUnramified_and_formallySmooth TensorProduct.includeRight Smooth.finitePresentation algebraMap TensorProduct.lid mem_top FormallyUnramified Smooth.formallySmooth smoothLocus FormallyEtale Smooth IsSmoothAt Etale TensorProduct.includeRight_apply Smooth.comp Etale.formallyEtale FormallyUnramified.isReduced_of_field FinitePresentation" namespace Etale w03_export "Algebra.Etale" "finitePresentation comp formallyEtale" end Algebra.Etale
namespace Algebra.Etale
r2nos_namespace_dual
r2nos_open_scoped "Algebra Algebra.Etale" in
private theorem _root_.ZInQ.Contrib.CloudW03NeronSurj.FLT.Algebra.Etale.isReduced_of_field
    {K B : Type*} [Field K] [CommRing B] [Algebra K B] [Algebra.Etale K B] :
    IsReduced B := by
  haveI : Algebra.FormallyUnramified K B :=
    ((Algebra.FormallyEtale.iff_formallyUnramified_and_formallySmooth).mp
      Algebra.Etale.formallyEtale).1
  haveI : Algebra.EssFiniteType K B := inferInstance
  exact Algebra.FormallyUnramified.isReduced_of_field K B

end Algebra.Etale
w03_export "" "Algebra.Etale.isReduced_of_field"
r2nos_open_scoped "Algebra Algebra.Etale" in
theorem Algebra.Etale.isReduced_of_isDomain
    {R B : Type*} [CommRing R] [IsDomain R] [CommRing B] [Algebra R B] [Algebra.Etale R B] :
    IsReduced B := by
  let K := FractionRing R
  haveI : Algebra.Etale K (TensorProduct R K B) := inferInstance
  haveI : IsReduced (TensorProduct R K B) := Algebra.Etale.isReduced_of_field (K := K)
  have hinj : Function.Injective
      (Algebra.TensorProduct.includeRight : B →ₐ[R] TensorProduct R K B) := by
    have hRK : Function.Injective (Algebra.linearMap R K) := IsFractionRing.injective R K
    have hrT : Function.Injective (LinearMap.rTensor B (Algebra.linearMap R K)) :=
      Module.Flat.rTensor_preserves_injective_linearMap (Algebra.linearMap R K) hRK
    intro b₁ b₂ hb
    have key : ∀ b : B, (Algebra.TensorProduct.includeRight : B →ₐ[R] _) b
        = LinearMap.rTensor B (Algebra.linearMap R K) (1 ⊗ₜ[R] b) := by
      intro b
      simp only [Algebra.TensorProduct.includeRight_apply, LinearMap.rTensor_tmul,
        Algebra.linearMap_apply, map_one]
    rw [key, key] at hb
    simpa using congrArg (TensorProduct.lid R B) (hrT hb)
  exact isReduced_of_injective
    (Algebra.TensorProduct.includeRight : B →ₐ[R] TensorProduct R K B) hinj

namespace Algebra w03_export "Algebra" "EssFiniteType IsSmoothAt.exists_isStandardEtale_mvPolynomial linearMap_apply smoothLocus_eq_univ_iff FormallyEtale.iff_formallyUnramified_and_formallySmooth TensorProduct.includeRight Smooth.finitePresentation algebraMap TensorProduct.lid mem_top FormallyUnramified Smooth.formallySmooth smoothLocus FormallyEtale Smooth IsSmoothAt Etale TensorProduct.includeRight_apply Smooth.comp Etale.formallyEtale FormallyUnramified.isReduced_of_field FinitePresentation" namespace Smooth w03_export "Algebra.Smooth" "finitePresentation formallySmooth comp" end Algebra.Smooth
namespace Algebra.Smooth
r2nos_namespace_dual
r2nos_open_scoped "Algebra Algebra.Smooth" in
private theorem _root_.ZInQ.Contrib.CloudW03NeronSurj.FLT.Algebra.Smooth.isReduced_of_field
    {K A : Type*} [Field K] [CommRing A] [Algebra K A] [Algebra.Smooth K A] :
    IsReduced A := by
  haveI hfp : Algebra.FinitePresentation K A := Algebra.Smooth.finitePresentation
  constructor
  intro a ha

  set J : Ideal A := (Ideal.span {a}).annihilator with hJ
  suffices h1 : (1 : A) ∈ J by
    have := (Submodule.mem_annihilator_span_singleton a 1).mp h1
    simpa using this
  by_contra h1
  have hJne : J ≠ ⊤ := fun h => h1 (h ▸ Submodule.mem_top)
  obtain ⟨m, hm, hsub⟩ := Ideal.exists_le_maximal J hJne
  haveI : m.IsPrime := hm.isPrime
  have hsa : Algebra.IsSmoothAt K m := by
    have : (⟨m, hm.isPrime⟩ : PrimeSpectrum A) ∈ Algebra.smoothLocus K A := by
      rw [(Algebra.smoothLocus_eq_univ_iff).mpr Algebra.Smooth.formallySmooth]; trivial
    exact this
  haveI := hsa
  obtain ⟨f, hfm, n, _, hST, hse⟩ :=
    Algebra.IsSmoothAt.exists_isStandardEtale_mvPolynomial (R := K) (S := A) (p := m)
  haveI : Algebra.Etale (MvPolynomial (Fin n) K) (Localization.Away f) := inferInstance
  haveI hAf : IsReduced (Localization.Away f) :=
    Algebra.Etale.isReduced_of_isDomain (R := MvPolynomial (Fin n) K)
  have hzero : algebraMap A (Localization.Away f) a = 0 :=
    (ha.map (algebraMap A (Localization.Away f))).eq_zero
  obtain ⟨⟨_, k, rfl⟩, hk⟩ := (IsLocalization.map_eq_zero_iff (Submonoid.powers f) _ a).mp hzero
  have hfk : f ^ k ∈ J := by
    rw [hJ, Submodule.mem_annihilator_span_singleton]
    rw [smul_eq_mul, hk]
  exact hfm (hm.isPrime.mem_of_pow_mem k (hsub hfk))

end Algebra.Smooth
w03_export "" "Algebra.Smooth.isReduced_of_field"
end RingLevel

section SchemeLevel

private theorem ringHomSmooth_appTop {K : Type u} [Field K] {X : Scheme.{u}}
    [IsAffine X] (g : X ⟶ Spec (CommRingCat.of K)) [Smooth g] :
    RingHom.Smooth ((g.appTop).hom.comp ((Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom)) := by
  exact RingHom.Smooth.comp
    (RingHom.Smooth.of_bijective
      ((Scheme.ΓSpecIso (CommRingCat.of K)).symm.commRingCatIsoToRingEquiv.bijective))
    (HasRingHomProperty.appTop (P := @Smooth) g ‹Smooth g›)

namespace AlgebraicGeometry w03_export "AlgebraicGeometry" "IsAffine Spec Scheme Smooth IsReduced.of_openCover Flat IsReduced Etale HasRingHomProperty.appTop FormallyUnramified isReduced_of_isAffine_isReduced HasRingHomProperty Scheme.ΓSpecIso" end AlgebraicGeometry
r2nos_open_scoped "AlgebraicGeometry" in

theorem AlgebraicGeometry.isReduced_of_smooth_of_field
    {K : Type u} [Field K] {X : Scheme.{u}} (sX : X ⟶ Spec (.of K)) [Smooth sX] :
    IsReduced X := by
  haveI : ∀ i, IsReduced (X.affineCover.X i) := fun i => by
    let U := X.affineCover.X i
    let g : U ⟶ Spec (CommRingCat.of K) := X.affineCover.f i ≫ sX
    haveI : IsAffine U := inferInstance
    haveI : Smooth g := inferInstance
    have hψ := ringHomSmooth_appTop g
    letI : Algebra K Γ(U, ⊤) :=
      ((g.appTop).hom.comp ((Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom)).toAlgebra
    haveI hsm : Algebra.Smooth K Γ(U, ⊤) := hψ
    haveI : _root_.IsReduced ↑Γ(U, ⊤) := Algebra.Smooth.isReduced_of_field (K := K)
    exact isReduced_of_isAffine_isReduced U
  exact IsReduced.of_openCover X X.affineCover

end SchemeLevel

theorem solution {K : Type u} [Field K] {X : Scheme.{u}} (sX : X ⟶ Spec (.of K)) [Smooth sX] :
    IsReduced X :=
  AlgebraicGeometry.isReduced_of_smooth_of_field sX

end S_AlgebraicGeometry_isReduced_of_smooth_of_field
end P2MW

end ZInQ.Contrib.CloudW03NeronSurj.FLT
