import Mathlib
open Module
noncomputable section
def precompL {k V Ω : Type*} [Field k] [AddCommGroup V] [Module k V] [Field Ω] [Algebra k Ω]
    (T : Module.End k V) : Module.End Ω (V →ₗ[k] Ω) :=
  { toFun := fun φ => φ ∘ₗ T
    map_add' := fun φ ψ => LinearMap.add_comp _ _ _
    map_smul' := fun c φ => LinearMap.smul_comp _ _ _ }

theorem trace_precompL {k V Ω : Type*} [Field k] [AddCommGroup V] [Module k V]
    [FiniteDimensional k V] [Field Ω] [Algebra k Ω] (T : Module.End k V) :
    LinearMap.trace Ω (V →ₗ[k] Ω) (precompL T) = algebraMap k Ω (LinearMap.trace k V T) := by
  sorry
