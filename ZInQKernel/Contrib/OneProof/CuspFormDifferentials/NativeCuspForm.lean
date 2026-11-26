import ZInQKernel.Contrib.OneProof.CuspFormDifferentials.ArcAnalytic
import ZInQKernel.Contrib.OneProof.CuspFormDifferentials.NativeValue
import ZInQKernel.Contrib.OneProof.CuspFormDifferentials.WeightTwo
import ZInQKernel.Contrib.OneProof.CuspFormDifferentials.CuspVanishing
import ZInQKernel.Contrib.OneProof.CuspFormDifferentials.Injectivity
import Mathlib.NumberTheory.ModularForms.Basic

/-! The native value of a global differential of the complexified modular curve is a
weight-two cusp form on `Γ₀(N)`, and this defines a complex-linear map from global
differentials to cusp forms. -/

noncomputable section

open AlgebraicGeometry CategoryTheory UpperHalfPlane
open scoped Manifold MatrixGroups ModularForm

namespace ZInQ.Manuscript.RC.CuspFormDifferentials

variable (N : ℕ) [NeZero N]

/-- The native value of a global differential, as a weight-two cusp form on `Γ₀(N)`. -/
def nativeCuspForm (ω : Γ((curveC N).hom.relativeDifferentials, ⊤)) :
    CuspForm (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) 2 where
  toSlashInvariantForm := nativeSlashInvariantForm N (mdifferentiable_arcPoint N) ω
  holo' := mdifferentiable_nativeValue N ω
  zero_at_cusps' hc := nativeValue_isZeroAt_cusps N (mdifferentiable_arcPoint N) ω hc

@[simp]
theorem nativeCuspForm_apply (ω : Γ((curveC N).hom.relativeDifferentials, ⊤)) (τ : ℍ) :
    nativeCuspForm N ω τ = nativeValue N ω τ :=
  rfl

/-- The native value map from global differentials of the complexified modular curve to
weight-two cusp forms on `Γ₀(N)`, linear for the complex structure through the structure
map. -/
def nativeCuspFormMap :
    letI := differentialsModule N
    Γ((curveC N).hom.relativeDifferentials, ⊤) →ₗ[ℂ]
      CuspForm (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) 2 :=
  letI := differentialsModule N
  { toFun := nativeCuspForm N
    map_add' := fun ω ω' => CuspForm.ext fun τ => by
      change nativeValue N (ω + ω') τ = nativeValue N ω τ + nativeValue N ω' τ
      rw [nativeValue_add]
      rfl
    map_smul' := fun c ω => CuspForm.ext fun τ => by
      change nativeValue N (structureMap N c • ω) τ = c • nativeValue N ω τ
      rw [nativeValue_smul]
      rfl }

@[simp]
theorem nativeCuspFormMap_apply (ω : Γ((curveC N).hom.relativeDifferentials, ⊤)) (τ : ℍ) :
    nativeCuspFormMap N ω τ = nativeValue N ω τ :=
  rfl

/-- The native value map is injective: a global differential whose native value vanishes
identically is zero. -/
theorem nativeCuspFormMap_injective :
    letI := differentialsModule N
    Function.Injective (nativeCuspFormMap N) := by
  letI := differentialsModule N
  refine (injective_iff_map_eq_zero (nativeCuspFormMap N)).mpr fun ω hω =>
    eq_zero_of_nativeValue_eq_zero N ω fun τ => ?_
  have h := DFunLike.congr_fun hω τ
  rw [nativeCuspFormMap_apply] at h
  exact h

end ZInQ.Manuscript.RC.CuspFormDifferentials

