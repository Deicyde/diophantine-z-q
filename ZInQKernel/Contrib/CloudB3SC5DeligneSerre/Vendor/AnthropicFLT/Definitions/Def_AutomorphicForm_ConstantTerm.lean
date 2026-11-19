/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Definitions.Def_AutomorphicForm_ConstantTerm (git blob 91a8eb8d9f97f80fa0a51275a238a73cba47310f, sha256 95e6933ffa5c01b6f13c12bc45aace85bf45b095ee116f8d5faac1f349a4339f).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

open Matrix MeasureTheory

namespace AutomorphicForm

section Unipotent

variable {R : Type*} [CommRing R]

private theorem unipotent_mul_unipotent (x y : R) :
    !![1, x; 0, 1] * !![1, y; 0, 1] = !![1, x + y; 0, 1] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, add_comm]

def unipotentGL2 (x : R) : GL (Fin 2) R where
  val := !![1, x; 0, 1]
  inv := !![1, -x; 0, 1]
  val_inv := by rw [unipotent_mul_unipotent, add_neg_cancel, Matrix.one_fin_two]
  inv_val := by rw [unipotent_mul_unipotent, neg_add_cancel, Matrix.one_fin_two]

@[simp] theorem unipotentGL2_coe (x : R) :
    (unipotentGL2 x : Matrix (Fin 2) (Fin 2) R) = !![1, x; 0, 1] := rfl

@[simp] theorem unipotentGL2_zero : unipotentGL2 (0 : R) = 1 := by
  ext i j; simp [unipotentGL2, Matrix.one_fin_two]

theorem unipotentGL2_add (x y : R) :
    unipotentGL2 (x + y) = unipotentGL2 x * unipotentGL2 y := by
  ext i j; simp only [unipotentGL2, Units.val_mul, unipotent_mul_unipotent]

def unipotentGL2Hom : Multiplicative R →* GL (Fin 2) R where
  toFun x := unipotentGL2 x.toAdd
  map_one' := unipotentGL2_zero
  map_mul' x y := unipotentGL2_add x.toAdd y.toAdd

end Unipotent

section ConstantTerm

variable {Q : Type*} [MeasurableSpace Q] {G : Type*} [Group G]

def constantTermIntegrand (u : Q → G) (f : G → ℂ) (g : G) : Q → ℂ :=
  fun q => f (u q * g)

noncomputable def constantTerm (μ : Measure Q) (u : Q → G) (f : G → ℂ) (g : G) : ℂ :=
  ∫ q, constantTermIntegrand u f g q ∂μ

@[simp] theorem constantTerm_zero (μ : Measure Q) (u : Q → G) (g : G) :
    constantTerm μ u (fun _ => (0 : ℂ)) g = 0 := by
  simp [constantTerm, constantTermIntegrand]

@[simp] theorem constantTerm_const (μ : Measure Q) [IsProbabilityMeasure μ] (u : Q → G)
    (c : ℂ) (g : G) : constantTerm μ u (fun _ => c) g = c := by
  simp [constantTerm, constantTermIntegrand, integral_const, measureReal_def]

def IsCuspidalFn (μ : Measure Q) (u : Q → G) (f : G → ℂ) : Prop :=
  ∀ g : G, constantTerm μ u f g = 0

end ConstantTerm

end AutomorphicForm
