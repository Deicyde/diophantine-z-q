/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Definitions.Def_FreyPackage_GaloisRep
Modified for the Z-in-Q kernel (2026-11-15, task flt-cqj2): local import paths are relocated
(`P2M.Util` is the copy published by Cloud Worker 2) and the upstream lakefile options are set
as `set_option` lines after the imports; any other change is marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Definitions.Def_FLTPrelim_FreyPackage
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Definitions.Def_FLTPrelim_GaloisRep
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Definitions.Def_EllipticCurve_FrobeniusTrace
import Mathlib.LinearAlgebra.FiniteDimensional.Defs

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

set_option autoImplicit false

universe r s v

namespace WeierstrassCurve.Affine.Point

open WeierstrassCurve

variable {R : Type r} {S : Type s} {K : Type v} [CommRing R] [CommRing S] [Field K]
  [DecidableEq K] {W' : Affine R} [Algebra R S] [Algebra R K] [Algebra S K]
  [IsScalarTower R S K]

noncomputable def galoisRep (W' : Affine R) (n : ℕ) :
    (K ≃ₐ[S] K) →*
      (Submodule.torsionBy ℤ (W'⁄K).Point n) ≃ₗ[ZMod n] (Submodule.torsionBy ℤ (W'⁄K).Point n) :=
  DistribMulAction.toModuleAut (ZMod n) (Submodule.torsionBy ℤ (W'⁄K).Point n)

@[simp]
lemma galoisRep_apply {n : ℕ} (σ : K ≃ₐ[S] K) (P : Submodule.torsionBy ℤ (W'⁄K).Point n) :
    galoisRep W' n σ P = σ • P :=
  rfl

end WeierstrassCurve.Affine.Point

namespace FreyPackage

open WeierstrassCurve.Affine.Point
open scoped WeierstrassCurve.Affine

noncomputable local instance instDecEqQbarRepresentation : DecidableEq (AlgebraicClosure ℚ) :=
  Classical.decEq _

noncomputable def freyGaloisRep (P : FreyPackage) :
    (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) →*
      (Submodule.torsionBy ℤ (P.freyCurve⁄(AlgebraicClosure ℚ)).Point P.p) ≃ₗ[ZMod P.p]
        (Submodule.torsionBy ℤ (P.freyCurve⁄(AlgebraicClosure ℚ)).Point P.p) :=
  galoisRep P.freyCurve P.p

end FreyPackage
