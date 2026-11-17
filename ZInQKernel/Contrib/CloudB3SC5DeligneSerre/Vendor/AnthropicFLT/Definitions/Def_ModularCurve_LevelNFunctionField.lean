/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Definitions.Def_ModularCurve_LevelNFunctionField (git blob d037d4af0a6c39993b7580d3f513670c3e329f29, sha256 63ed19a18eb04ec61f9ac2290f959cd6b12e8c9ca807a5f204779d65a547515e).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Definitions.Def_PeriodPair_Uniformization

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

set_option autoImplicit false

noncomputable section

open UpperHalfPlane

open scoped MatrixGroups

namespace ModularCurve.LevelN

def wp (N : ℕ) (v : Fin 2 → ZMod N) (τ : ℍ) : ℂ :=
  ((2 * (Real.pi : ℂ) * Complex.I) ^ 2)⁻¹ *
    PeriodPair.weierstrassP (PeriodPair.ofTau τ)
      ((((v 0).val : ℂ) * (τ : ℂ) + ((v 1).val : ℂ)) / (N : ℂ))

def fricke (N : ℕ) (v : Fin 2 → ZMod N) (τ : ℍ) : ℂ :=
  -(ModularForm.E₄ τ * ModularForm.E₆ τ / ModularForm.discriminant τ) / 2592 * wp N v τ

def jAnalytic (τ : ℍ) : ℂ :=
  ModularForm.E₄ τ ^ 3 / ModularForm.discriminant τ

def generators (N : ℕ) : Set (ℍ → ℂ) :=
  insert jAnalytic {g : ℍ → ℂ | ∃ v : Fin 2 → ZMod N, v ≠ 0 ∧ g = fricke N v}

def ring (N : ℕ) : Subalgebra ℂ (ℍ → ℂ) :=
  Algebra.adjoin ℂ (generators N)

theorem jAnalytic_mem_generators (N : ℕ) : jAnalytic ∈ generators N :=
  Set.mem_insert _ _

theorem fricke_mem_generators (N : ℕ) {v : Fin 2 → ZMod N} (hv : v ≠ 0) :
    fricke N v ∈ generators N :=
  Set.mem_insert_of_mem _ ⟨v, hv, rfl⟩

theorem jAnalytic_mem (N : ℕ) : jAnalytic ∈ ring N :=
  Algebra.subset_adjoin (jAnalytic_mem_generators N)

theorem fricke_mem (N : ℕ) {v : Fin 2 → ZMod N} (hv : v ≠ 0) : fricke N v ∈ ring N :=
  Algebra.subset_adjoin (fricke_mem_generators N hv)

def jGen (N : ℕ) : ring N :=
  ⟨jAnalytic, jAnalytic_mem N⟩

@[simp]
theorem coe_jGen (N : ℕ) : ((jGen N : ring N) : ℍ → ℂ) = jAnalytic :=
  rfl

end ModularCurve.LevelN

end
