/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Definitions.Def_AutomorphicForm_WeylIntertwining (git blob 84f50162118ee7646bdeb06984d15212c65f0583, sha256 4a32e14fffa5d87617583322bf69d185e3f931758439fa11549dbbfc49bcb70f).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AutomorphicForm_AdelicLsXi
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AutomorphicForm_ConstantTerm

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

noncomputable section

open Matrix MeasureTheory

namespace AutomorphicForm

section WeylElement

variable {K : Type*} [Field K]

def gl2Weyl : GL (Fin 2) K :=
  ⟨!![0, 1; 1, 0], !![0, 1; 1, 0], by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two], by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two]⟩

@[simp] theorem gl2Weyl_val :
    ((gl2Weyl : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) = !![0, 1; 1, 0] := rfl

theorem gl2Weyl_inv : (gl2Weyl : GL (Fin 2) K)⁻¹ = gl2Weyl := Units.ext rfl

end WeylElement

section Intertwining

variable (R K : Type*) [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K]
  [IsFractionRing R K] [MeasurableSpace (NumberField.AdeleRing R K)]

def adelicWeyl : AdelicGL2 R K :=
  globalPoints R K gl2Weyl

def weylIntertwiningIntegral (ν : Measure (NumberField.AdeleRing R K))
    (f : AdelicGL2 R K → ℂ) (g : AdelicGL2 R K) : ℂ :=
  ∫ x, f ((adelicWeyl R K)⁻¹ * unipotentGL2 x * g) ∂ν

theorem weylIntertwiningIntegral_const (ν : Measure (NumberField.AdeleRing R K))
    [IsProbabilityMeasure ν] (c : ℂ) (g : AdelicGL2 R K) :
    weylIntertwiningIntegral R K ν (fun _ => c) g = c := by
  unfold weylIntertwiningIntegral
  simp [integral_const, measureReal_def]

theorem weylIntertwiningIntegral_zero_measure (f : AdelicGL2 R K → ℂ) (g : AdelicGL2 R K) :
    weylIntertwiningIntegral R K 0 f g = 0 := by
  unfold weylIntertwiningIntegral
  simp

end Intertwining

end AutomorphicForm
