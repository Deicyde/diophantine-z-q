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
  classical
  set b := Module.finBasis k V
  set e : (Fin (finrank k V) → Ω) ≃ₗ[Ω] (V →ₗ[k] Ω) := b.constr Ω with he
  set B : Basis (Fin (finrank k V)) Ω (V →ₗ[k] Ω) := (Pi.basisFun Ω _).map e with hB
  rw [LinearMap.trace_eq_matrix_trace Ω B, LinearMap.trace_eq_matrix_trace k b, Matrix.trace,
    Matrix.trace, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Matrix.diag_apply, Matrix.diag_apply, LinearMap.toMatrix_apply, LinearMap.toMatrix_apply]
  have hBr : ∀ x, B.repr x i = x (b i) := fun x => by
    rw [hB, Basis.map_repr, LinearEquiv.trans_apply, Pi.basisFun_repr, he, Basis.constr_symm_apply]
  have hBi : B i = b.constr Ω (Pi.single i 1) := by
    rw [hB, Basis.map_apply, Pi.basisFun_apply]
  rw [hBr, hBi]
  show (b.constr Ω (Pi.single i 1)) (T (b i)) = _
  rw [Basis.constr_apply_fintype]
  simp [Pi.single_apply, Algebra.smul_def, Basis.equivFun_apply]
