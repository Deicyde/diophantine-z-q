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
  Source file    : Definitions/Def_EllipticCurve_FrobeniusTrace.lean
  Source sha256  : 1cc42c05b68c6513dbf53f6ece3dbaed0794191525ecb74caa60f90cb84c8be4
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

import Mathlib.LinearAlgebra.Trace
import Mathlib.RingTheory.Valuation.RamificationGroup
import ZInQKernel.Contrib.CloudR2NOS.Source.Definitions.Def_FLTPrelim_GaloisRep
import ZInQKernel.Contrib.CloudR2NOS.Source.Definitions.Def_FLTPrelim_Ramification
import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.PresheafOfModulesMonoidal
import ZInQKernel.Contrib.CloudR2NOS.Source.PortUtilExt

namespace ZInQ.Contrib.CloudW03NeronSurj.FLT

open ZInQ.Contrib.CloudW03NeronSurj.FLT

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false

noncomputable section

open scoped WeierstrassCurve.Affine
r2nos_open_scoped_dual "WeierstrassCurve.Affine"

namespace WeierstrassCurve.Affine.Point
r2nos_namespace_dual

universe r s v

variable {R : Type r} {S : Type s} {K : Type v} [CommRing R] [CommRing S] [Field K]
  [DecidableEq K] {W' : Affine R} [Algebra R S] [Algebra R K] [Algebra S K]
  [IsScalarTower R S K]

instance instSMulCommClassAlgEquivZModTorsionBy (n : ℕ) :
    SMulCommClass (K ≃ₐ[S] K) (ZMod n) (Submodule.torsionBy ℤ (W'⁄K).Point n) where
  smul_comm σ c x :=
    ZMod.map_smul (DistribSMul.toAddMonoidHom (Submodule.torsionBy ℤ (W'⁄K).Point n) σ) c x

variable (S) in

def galoisRepModuleEnd (W' : Affine R) (n : ℕ) :
    (K ≃ₐ[S] K) →* Module.End (ZMod n) (Submodule.torsionBy ℤ (W'⁄K).Point n) :=
  DistribMulAction.toModuleEnd (ZMod n) (Submodule.torsionBy ℤ (W'⁄K).Point n)

@[simp] lemma galoisRepModuleEnd_apply (W' : Affine R) (n : ℕ) (σ : K ≃ₐ[S] K)
    (x : Submodule.torsionBy ℤ (W'⁄K).Point n) :
    galoisRepModuleEnd S W' n σ x = σ • x :=
  rfl

variable (S) in

def galoisTrace (W' : Affine R) (n : ℕ) (σ : K ≃ₐ[S] K) : ZMod n :=
  LinearMap.trace (ZMod n) (Submodule.torsionBy ℤ (W'⁄K).Point n) (galoisRepModuleEnd S W' n σ)

lemma galoisTrace_def (W' : Affine R) (n : ℕ) (σ : K ≃ₐ[S] K) :
    galoisTrace S W' n σ =
      LinearMap.trace (ZMod n) (Submodule.torsionBy ℤ (W'⁄K).Point n)
        (galoisRepModuleEnd S W' n σ) :=
  rfl

end WeierstrassCurve.Affine.Point

namespace ValuationSubring
r2nos_namespace_dual

variable {K L : Type*} [Field K] [Field L] [Algebra K L]

def IsFrobeniusAt (A : ValuationSubring L) (σ : L ≃ₐ[K] L) (q : ℕ) : Prop :=
  ∃ hσ : σ ∈ A.decompositionSubgroup K,
    ∀ x : IsLocalRing.ResidueField A, (⟨σ, hσ⟩ : A.decompositionSubgroup K) • x = x ^ q

lemma IsFrobeniusAt.mem_decompositionSubgroup {A : ValuationSubring L} {σ : L ≃ₐ[K] L} {q : ℕ}
    (h : A.IsFrobeniusAt σ q) : σ ∈ A.decompositionSubgroup K :=
  h.choose

lemma IsFrobeniusAt.smul_residue_eq {A : ValuationSubring L} {σ : L ≃ₐ[K] L} {q : ℕ}
    (h : A.IsFrobeniusAt σ q) (x : IsLocalRing.ResidueField A) :
    (⟨σ, h.mem_decompositionSubgroup⟩ : A.decompositionSubgroup K) • x = x ^ q :=
  h.choose_spec x

end ValuationSubring

end

end ZInQ.Contrib.CloudW03NeronSurj.FLT
