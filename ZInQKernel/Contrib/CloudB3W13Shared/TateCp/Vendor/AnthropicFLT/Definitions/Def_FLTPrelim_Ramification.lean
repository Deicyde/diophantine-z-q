/- Additional modification notice, 2026-11-16: Cloud Batch 3 Worker 13
retargeted only repository module paths into the task-owned CloudB3W13
directories. Canonical mathematical declaration names and statements
are retained. Recovery and later compatibility changes are documented
in the accompanying source manifest and NOTICE. -/
/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Definitions.Def_FLTPrelim_Ramification
Modification notice (2026-11-15, Cloud Batch-2 Worker 11): local import paths are relocated under
`ZInQKernel.Contrib.CloudB3W13Shared.TateCp.Vendor.AnthropicFLT` (`P2M.Util` resolves to the copy already
vendored by Cloud Worker 2, `ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.P2M.Util`);
mathematical definitions, theorem statements, and proof bodies are unchanged.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib.RingTheory.Valuation.RamificationGroup
import Mathlib.RingTheory.Valuation.ValuationSubring
import ZInQKernel.Contrib.CloudB3W13Shared.TateCp.Vendor.AnthropicFLT.Definitions.Def_FLTPrelim_FreyPackage
import ZInQKernel.Contrib.CloudB3W13Shared.TateCp.Vendor.AnthropicFLT.Definitions.Def_FLTPrelim_GaloisRep

set_option autoImplicit false

noncomputable section

universe u

namespace ValuationSubring

variable {L : Type u} [Field L]

def LiesOverPrime (A : ValuationSubring L) (q : ℕ) : Prop :=
  (q : L) ∈ A.nonunits

variable (K : Type*) [Field K] [Algebra K L]

def inertiaSubgroupIn (A : ValuationSubring L) : Subgroup (L ≃ₐ[K] L) :=
  (A.inertiaSubgroup K).map (A.decompositionSubgroup K).subtype

end ValuationSubring

namespace WeierstrassCurve.Affine.Point

open WeierstrassCurve

variable {R : Type*} {S : Type*} {K : Type*} [CommRing R] [Field S] [Field K]
  [DecidableEq K] [Algebra R S] [Algebra R K] [Algebra S K] [IsScalarTower R S K]

variable (S K) in

def GaloisRepUnramifiedAt (W' : Affine R) (n : ℕ) (q : ℕ) : Prop :=
  ∀ A : ValuationSubring K, A.LiesOverPrime q →
    ∀ σ ∈ A.inertiaSubgroupIn S,
    ∀ x : Submodule.torsionBy ℤ (W'⁄K).Point n, σ • x = x

end WeierstrassCurve.Affine.Point

namespace FreyPackage

open WeierstrassCurve.Affine.Point

def GaloisRepUnramifiedAt (P : FreyPackage) (q : ℕ) : Prop :=
  WeierstrassCurve.Affine.Point.GaloisRepUnramifiedAt (K := AlgebraicClosure ℚ) ℚ
    P.freyCurve P.p q

end FreyPackage

end
