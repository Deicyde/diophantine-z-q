import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Matrix.FiniteDimensional
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.RingTheory.Adjoin.Basic

/-!
# Full matrix span from traces

The trace pairing on square matrices is nondegenerate in every characteristic.
If two matrix representations have equal traces, the span of the paired image
projects injectively to the second matrix space whenever it projects onto the
first. Comparing dimensions gives surjectivity of the second projection.
-/

namespace ZInQ.MatrixTraceSpan

open Matrix

variable {K ι G : Type*} [Field K] [Fintype ι] [DecidableEq ι] [Monoid G]

/-- A representation's image matrices, after forgetting invertibility. -/
abbrev matrixHom (ρ : G →* GL ι K) : G →* Matrix ι ι K :=
  { toFun := fun g => ↑(ρ g)
    map_one' := by rw [map_one, Units.val_one]
    map_mul' := fun g h => by rw [map_mul, Units.val_mul] }

/-- The linear span of the image is the underlying space of its generated algebra. -/
theorem adjoin_range_toSubmodule (ρ : G →* GL ι K) :
    (Algebra.adjoin K (Set.range (matrixHom ρ))).toSubmodule =
      Submodule.span K (Set.range (matrixHom ρ)) := by
  rw [Algebra.adjoin_eq_span, MonoidHom.mclosure_range]
  rfl

/-- The full linear span transfers along trace equality, without semisimplicity. -/
theorem span_eq_top_of_trace_eq (ρ τ : G →* GL ι K)
    (htrace : ∀ g, (matrixHom ρ g).trace = (matrixHom τ g).trace)
    (hρ : Submodule.span K (Set.range (matrixHom ρ)) = ⊤) :
    Submodule.span K (Set.range (matrixHom τ)) = ⊤ := by
  let M := Matrix ι ι K
  let A : G →* M := matrixHom ρ
  let B : G →* M := matrixHom τ
  let S : Submodule K (M × M) := Submodule.span K (Set.range fun g => (A g, B g))
  let p₁ : S →ₗ[K] M := (LinearMap.fst K M M).comp S.subtype
  let p₂ : S →ₗ[K] M := (LinearMap.snd K M M).comp S.subtype
  have hr₁ : LinearMap.range p₁ = Submodule.span K (Set.range A) := by
    change LinearMap.range ((LinearMap.fst K M M).comp S.subtype) = _
    rw [LinearMap.range_comp, Submodule.range_subtype, Submodule.map_span, ← Set.range_comp]
    rfl
  have hr₂ : LinearMap.range p₂ = Submodule.span K (Set.range B) := by
    change LinearMap.range ((LinearMap.snd K M M).comp S.subtype) = _
    rw [LinearMap.range_comp, Submodule.range_subtype, Submodule.map_span, ← Set.range_comp]
    rfl
  have hsurj : Function.Surjective p₁ := LinearMap.range_eq_top.mp (hr₁.trans hρ)
  have hpair : ∀ x ∈ S, ∀ g, (x.1 * A g).trace = (x.2 * B g).trace := by
    intro x hx g
    induction hx using Submodule.span_induction with
    | mem x hx =>
        obtain ⟨h, rfl⟩ := hx
        change (A h * A g).trace = (B h * B g).trace
        rw [← A.map_mul, ← B.map_mul]
        exact htrace (h * g)
    | zero => simp
    | add x y _ _ hx hy =>
        change ((x.1 + y.1) * A g).trace = ((x.2 + y.2) * B g).trace
        rw [add_mul, add_mul, Matrix.trace_add, Matrix.trace_add, hx, hy]
    | smul c x _ hx =>
        change ((c • x.1) * A g).trace = ((c • x.2) * B g).trace
        rw [smul_mul_assoc, smul_mul_assoc, Matrix.trace_smul, Matrix.trace_smul, hx]
  have hinj : Function.Injective p₂ := by
    apply (LinearMap.ker_eq_bot.mp ?_)
    rw [eq_bot_iff]
    intro x hx
    have hx₂ : (x : M × M).2 = 0 := hx
    have hzero : ∀ y : M, ((x : M × M).1 * y).trace = 0 := by
      intro y
      have hy : y ∈ Submodule.span K (Set.range A) := hρ ▸ Submodule.mem_top
      induction hy using Submodule.span_induction with
      | mem y hy =>
          obtain ⟨g, rfl⟩ := hy
          simpa [hx₂] using hpair x x.property g
      | zero => simp
      | add y z _ _ hy hz => rw [mul_add, Matrix.trace_add, hy, hz, add_zero]
      | smul c y _ hy => rw [mul_smul_comm, Matrix.trace_smul, hy, smul_zero]
    have hx₁ : (x : M × M).1 = 0 := Matrix.ext_iff_trace_mul_right.mpr (by simpa using hzero)
    exact (Submodule.mem_bot K).mpr (Subtype.ext (Prod.ext hx₁ hx₂))
  rw [← hr₂]
  apply Submodule.eq_top_of_finrank_eq
  rw [LinearMap.finrank_range_of_inj hinj]
  exact le_antisymm (LinearMap.finrank_le_finrank_of_injective hinj)
    (LinearMap.finrank_le_finrank_of_surjective hsurj)

/-- Burnside fullness transfers in the same coordinates and over the same field. -/
theorem adjoin_eq_top_of_trace_eq (ρ τ : G →* GL ι K)
    (htrace : ∀ g, (matrixHom ρ g).trace = (matrixHom τ g).trace)
    (hρ : Algebra.adjoin K (Set.range (matrixHom ρ)) = ⊤) :
    Algebra.adjoin K (Set.range (matrixHom τ)) = ⊤ := by
  have hs : Submodule.span K (Set.range (matrixHom ρ)) = ⊤ := by
    rw [← adjoin_range_toSubmodule, hρ]
    rfl
  apply Subalgebra.toSubmodule_injective
  rw [adjoin_range_toSubmodule, span_eq_top_of_trace_eq ρ τ htrace hs]
  rfl

end ZInQ.MatrixTraceSpan
