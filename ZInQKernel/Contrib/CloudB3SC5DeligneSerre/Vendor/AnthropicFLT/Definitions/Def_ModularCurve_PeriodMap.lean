/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Definitions.Def_ModularCurve_PeriodMap (git blob 6c3b9e6eebd4ecf8942433264c5c7c6dc61e305f, sha256 f8e6563cf021111e708cf7d769dd7101365a52f710a21542635c71671f7c513f).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib.Analysis.Complex.UpperHalfPlane.MoebiusAction
import Mathlib.Algebra.Module.Hom

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

namespace ModularCurve.Period

open UpperHalfPlane

open scoped MatrixGroups

variable (Γ : Subgroup SL(2, ℤ)) (F : ℍ → ℂ)

def IsEquivariantPrimitive : Prop :=
  ∀ γ : Γ, ∃ c : ℂ, ∀ z : ℍ, F ((γ : SL(2, ℤ)) • z) - F z = c

def IsParabolicHom {A : Type*} [AddCommGroup A] (φ : Additive Γ →+ A) : Prop :=
  ∀ γ : Γ, ((γ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ).trace ^ 2 = 4 → φ (Additive.ofMul γ) = 0

variable {Γ F}

namespace IsEquivariantPrimitive

noncomputable def period (_hF : IsEquivariantPrimitive Γ F) (γ : Γ) : ℂ :=
  F ((γ : SL(2, ℤ)) • UpperHalfPlane.I) - F UpperHalfPlane.I

theorem sub_eq_period (hF : IsEquivariantPrimitive Γ F) (γ : Γ) (z : ℍ) :
    F ((γ : SL(2, ℤ)) • z) - F z = hF.period γ := by
  obtain ⟨c, hc⟩ := hF γ
  rw [hc z, period, hc UpperHalfPlane.I]

@[simp]
theorem period_one (hF : IsEquivariantPrimitive Γ F) : hF.period 1 = 0 := by
  have h := hF.sub_eq_period 1 UpperHalfPlane.I
  simpa using h.symm

theorem period_mul (hF : IsEquivariantPrimitive Γ F) (γ δ : Γ) :
    hF.period (γ * δ) = hF.period γ + hF.period δ := by
  have h1 := hF.sub_eq_period (γ * δ) UpperHalfPlane.I
  have h2 := hF.sub_eq_period γ ((δ : SL(2, ℤ)) • UpperHalfPlane.I)
  have h3 := hF.sub_eq_period δ UpperHalfPlane.I
  have hsmul : ((γ * δ : Γ) : SL(2, ℤ)) • UpperHalfPlane.I
      = (γ : SL(2, ℤ)) • ((δ : SL(2, ℤ)) • UpperHalfPlane.I) := by
    rw [← mul_smul]; rfl
  rw [hsmul] at h1
  linear_combination h2 + h3 - h1

noncomputable def periodHom (hF : IsEquivariantPrimitive Γ F) : Additive Γ →+ ℂ where
  toFun γ := hF.period (Additive.toMul γ)
  map_zero' := hF.period_one
  map_add' γ δ := hF.period_mul (Additive.toMul γ) (Additive.toMul δ)

@[simp]
theorem periodHom_apply (hF : IsEquivariantPrimitive Γ F) (γ : Γ) :
    hF.periodHom (Additive.ofMul γ) = hF.period γ :=
  rfl

end IsEquivariantPrimitive

section ParabolicHoms

variable (R : Type*) [Semiring R] (Γ : Subgroup SL(2, ℤ)) (A : Type*) [AddCommGroup A] [Module R A]

def parabolicHoms : Submodule R (Additive Γ →+ A) where
  carrier := {φ | IsParabolicHom Γ φ}
  zero_mem' := fun _ _ => rfl
  add_mem' := by
    intro φ ψ hφ hψ γ hγ
    show φ (Additive.ofMul γ) + ψ (Additive.ofMul γ) = 0
    rw [hφ γ hγ, hψ γ hγ, add_zero]
  smul_mem' := by
    intro c φ hφ γ hγ
    show c • φ (Additive.ofMul γ) = 0
    rw [hφ γ hγ, smul_zero]

variable {R Γ A}

theorem mem_parabolicHoms_iff {φ : Additive Γ →+ A} : φ ∈ parabolicHoms R Γ A ↔ IsParabolicHom Γ φ :=
  Iff.rfl

end ParabolicHoms

end ModularCurve.Period
