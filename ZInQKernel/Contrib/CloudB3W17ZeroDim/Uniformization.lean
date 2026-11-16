import ZInQKernel.HDecomp.Analytic.Uniformization
import ZInQKernel.Contrib.CloudB3W17ZeroDim.Basic

/-!
# Analytic uniformization in dimension zero

This supplies the exact `BPAnalytic.Uniformization.UniformizationLeaf A` for every
complex abelian variety with `A.dim ≤ 0`. The witness has `g = 0` and the zero
lattice, and proves all three fields of the existing coordinate-form predicate.
No existence or analytification leaf is assumed.

This is only the zero-dimensional case. It does not discharge the universally
quantified OneProof field `uniformizationLeafAll`.
-/

open scoped Manifold ContDiff Topology
open CategoryTheory AlgebraicGeometry MonObj Set Filter

noncomputable section

namespace CloudB3W17.ZeroDim

/-- The quotient of the zero-dimensional complex vector space is a singleton. -/
theorem subsingleton_zero_torus :
    Subsingleton (BPAnalytic.Torus (⊥ : Submodule ℤ (Fin 0 → ℂ))) := by
  refine ⟨fun x y => ?_⟩
  obtain ⟨a, rfl⟩ := QuotientAddGroup.mk_surjective x
  obtain ⟨b, rfl⟩ := QuotientAddGroup.mk_surjective y
  exact congrArg (BPAnalytic.proj (⊥ : Submodule ℤ (Fin 0 → ℂ))) (Subsingleton.elim a b)

/-- A singleton point group has the existing strong coordinate-form uniformization with `g = 0`. -/
theorem uniformizationLeaf_of_subsingleton (A : PkgI3.AbVar ℂ) [Subsingleton (A.Pt ℂ)] :
    BPAnalytic.Uniformization.UniformizationLeaf A := by
  have : Subsingleton (BPAnalytic.Torus (⊥ : Submodule ℤ (Fin 0 → ℂ))) :=
    subsingleton_zero_torus
  have : IsZLattice ℝ (⊥ : Submodule ℤ (Fin 0 → ℂ)) := ⟨Subsingleton.elim _ _⟩
  let φ : BPAnalytic.Torus (⊥ : Submodule ℤ (Fin 0 → ℂ)) ≃+ Additive (A.Pt ℂ) :=
    { toFun := fun _ => 0
      invFun := fun _ => 0
      left_inv := fun _ => Subsingleton.elim _ _
      right_inv := fun _ => Subsingleton.elim _ _
      map_add' := fun _ _ => (zero_add _).symm }
  refine ⟨0, ⊥, inferInstance, inferInstance, φ, ?_⟩
  constructor
  · intro U f
    refine ⟨isOpen_discrete _, ?_⟩
    have hF : (fun v : Fin 0 → ℂ => BPAnalytic.Uniformization.evalAt A U f
        (Additive.toMul (φ (BPAnalytic.proj ⊥ v)))) =
        (fun _ : Fin 0 → ℂ => BPAnalytic.Uniformization.evalAt A U f
          (Additive.toMul (φ (BPAnalytic.proj ⊥ 0)))) := by
      funext v
      exact congrArg (fun w => BPAnalytic.Uniformization.evalAt A U f
        (Additive.toMul (φ (BPAnalytic.proj ⊥ w)))) (Subsingleton.elim v 0)
    rw [hF]
    exact analyticOnNhd_const
  · intro v₀
    refine ⟨⊤, (fun i => Fin.elim0 i), ContinuousLinearEquiv.refl ℂ (Fin 0 → ℂ), ?_, ?_⟩
    · simp [BPAnalytic.Uniformization.PtIn]
    · have hF : (fun v i => BPAnalytic.Uniformization.evalAt A ⊤ (Fin.elim0 i)
          (Additive.toMul (φ (BPAnalytic.proj ⊥ v)))) =
          (id : (Fin 0 → ℂ) → (Fin 0 → ℂ)) := Subsingleton.elim _ _
      have he : (ContinuousLinearEquiv.refl ℂ (Fin 0 → ℂ) :
          (Fin 0 → ℂ) →L[ℂ] (Fin 0 → ℂ)) = ContinuousLinearMap.id ℂ (Fin 0 → ℂ) := by
        ext v i
        exact Fin.elim0 i
      rw [hF, he]
      exact hasFDerivAt_id v₀
  · intro v₀ N hN
    refine ⟨⊤, 0, (fun i => Fin.elim0 i), 1, zero_lt_one, ?_, ?_⟩
    · simp [BPAnalytic.Uniformization.PtIn]
    · intro P _ _
      exact ⟨BPAnalytic.proj ⊥ v₀, mem_of_mem_nhds hN, Subsingleton.elim _ _⟩

/-- Every complex abelian variety of algebraic dimension at most zero has the exact strong uniformization. -/
theorem uniformizationLeaf_of_dim_le_zero (A : PkgI3.AbVar ℂ) (hA : A.dim ≤ 0) :
    BPAnalytic.Uniformization.UniformizationLeaf A := by
  have : Subsingleton (A.Pt ℂ) := subsingleton_pts_of_dim_le_zero A hA
  exact uniformizationLeaf_of_subsingleton A

end CloudB3W17.ZeroDim
