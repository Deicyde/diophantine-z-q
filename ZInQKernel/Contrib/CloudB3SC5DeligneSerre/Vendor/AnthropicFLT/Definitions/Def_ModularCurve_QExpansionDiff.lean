/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Definitions.Def_ModularCurve_QExpansionDiff (git blob 1ee4e138915f648a8394a7711a32c7eca9ea33d3, sha256 b80ac7785b149b59663e89b577e8bb31d4906c28b6992d5a5e49849a31933b9d).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib.RingTheory.LaurentSeries
import Mathlib.RingTheory.Kaehler.Basic

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

set_option autoImplicit false

noncomputable section

open HahnSeries

namespace ModularCurve

section Theta

variable (L : Type*) [Field L]

def thetaL : LaurentSeries L →ₗ[L] LaurentSeries L where
  toFun f := single (1 : ℤ) (1 : L) * LaurentSeries.derivative L f
  map_add' f g := by rw [map_add, mul_add]
  map_smul' c f := by
    rw [map_smul, RingHom.id_apply, ← single_zero_mul_eq_smul, ← single_zero_mul_eq_smul,
      mul_left_comm]

variable {L} in

theorem thetaL_apply (f : LaurentSeries L) :
    thetaL L f = single (1 : ℤ) (1 : L) * LaurentSeries.derivative L f :=
  rfl

end Theta

section QExpansionDiff

variable {K F L : Type*} [Field K] [Field F] [Algebra K F] [Field L] [Algebra K L]

def IsQExpansionDiffAlong (σ : F →ₐ[K] LaurentSeries L) (φ : Ω[F⁄K] →ₗ[K] LaurentSeries L) :
    Prop :=
  (∀ x : F, φ (KaehlerDifferential.D K F x) = thetaL L (σ x)) ∧
    ∀ (f : F) (ω : Ω[F⁄K]), φ (f • ω) = σ f * φ ω

open scoped Classical in

def qExpansionDiffAlong (σ : F →ₐ[K] LaurentSeries L) : Ω[F⁄K] →ₗ[K] LaurentSeries L :=
  if h : ∃ φ : Ω[F⁄K] →ₗ[K] LaurentSeries L, IsQExpansionDiffAlong σ φ then h.choose else 0

end QExpansionDiff

end ModularCurve

namespace AlgebraicCurve

section TraceDiff

variable (K F F' : Type*) [Field K] [Field F] [Field F'] [Algebra K F] [Algebra K F']
  [Algebra F F'] [IsScalarTower K F F']

def IsTraceDiff (t : Ω[F'⁄K] →ₗ[F] Ω[F⁄K]) : Prop :=
  ∀ (y : F') (ω : Ω[F⁄K]),
    t (y • KaehlerDifferential.map K K F F' ω) = Algebra.trace F F' y • ω

open scoped Classical in

def traceDiff : Ω[F'⁄K] →ₗ[F] Ω[F⁄K] :=
  if h : ∃ t : Ω[F'⁄K] →ₗ[F] Ω[F⁄K], IsTraceDiff K F F' t then h.choose else 0

end TraceDiff

end AlgebraicCurve

end
