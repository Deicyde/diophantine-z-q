import ZInQKernel.HDecomp.Objects
import ZInQKernel.Contrib.CloudB3W17Uniformization.PointProduct
import Mathlib.Geometry.Manifold.Algebra.LieGroup

/-!
# An analytic Lie group structure on genuine abelian-variety points

Attribution: adapted pointwise from host `unif-printed`, Stage 2c,
`UniformizationPrinted.lean` lines 614–695 at
`dbf043a4eb8d977b1d4bf0b03010f915b70bcfb8`. Unlike the host four-printed-leaf
reduction, this theorem takes actual analytic regular-morphism facts on two
fixed point manifolds. No printed, topology, compactness or connectedness leaf
is introduced. It compares product scheme points with pairs of scheme points,
using analytic slice sections to invert the comparison, and then applies the
actual scheme multiplication and inverse maps.
-/

open scoped Manifold ContDiff Topology
open Set Filter CategoryTheory AlgebraicGeometry Limits MonObj MonoidalCategory
  CartesianMonoidalCategory

namespace CloudB3W17Uniformization

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

open PkgI3 (AbVar)

/-- The complex point source object has identity structure morphism. -/
theorem ptObj_hom : (AbVar.ptObj (K := ℂ) ℂ).hom = 𝟙 _ := by
  change Spec.map (CommRingCat.ofHom (algebraMap ℂ ℂ)) = 𝟙 _
  rw [show CommRingCat.ofHom (algebraMap ℂ ℂ) = 𝟙 (CommRingCat.of ℂ) from rfl, Spec.map_id]

private theorem isIso_toUnit_ptObj : IsIso (toUnit (AbVar.ptObj (K := ℂ) ℂ)) := by
  have : IsIso ((Over.forget _).map (toUnit (AbVar.ptObj (K := ℂ) ℂ))) := by
    change IsIso (toUnit (AbVar.ptObj (K := ℂ) ℂ)).left
    rw [Over.toUnit_left, ptObj_hom]
    exact IsIso.id _
  exact isIso_of_reflects_iso _ (Over.forget _)

attribute [local instance] isIso_toUnit_ptObj

section FixedVariety
variable (A : AbVar ℂ)

/-- The product slice at a fixed complex point, as an actual scheme morphism. -/
def secL (Q : A.Pt ℂ) : A.X ⟶ A.X ⊗ A.X :=
  lift (𝟙 A.X) (toUnit A.X ≫ inv (toUnit (AbVar.ptObj (K := ℂ) ℂ)) ≫ Q)

/-- The other product slice, as an actual scheme morphism. -/
def secR (P : A.Pt ℂ) : A.X ⟶ A.X ⊗ A.X :=
  lift (toUnit A.X ≫ inv (toUnit (AbVar.ptObj (K := ℂ) ℂ)) ≫ P) (𝟙 A.X)

private theorem toUnit_inv_comp (P Q : A.Pt ℂ) :
    P ≫ toUnit A.X ≫ inv (toUnit (AbVar.ptObj (K := ℂ) ℂ)) ≫ Q = Q := by
  have : IsIso (toUnit (AbVar.ptObj (K := ℂ) ℂ)) := isIso_toUnit_ptObj
  rw [← Category.assoc, comp_toUnit, IsIso.hom_inv_id_assoc]

theorem comp_secL (P Q : A.Pt ℂ) : P ≫ secL A Q = lift P Q := by
  rw [secL, comp_lift, Category.comp_id, toUnit_inv_comp]

theorem comp_secR (P Q : A.Pt ℂ) : Q ≫ secR A P = lift P Q := by
  rw [secR, comp_lift, Category.comp_id, toUnit_inv_comp]

/-- Actual regular-morphism analyticity on `A` and `A×A` makes abelian points a complex Lie group. -/
theorem lieGroup_of_analyticRegularMaps (g n : ℕ)
    [TopologicalSpace (A.Pt ℂ)]
    [TopologicalSpace (AbVar.ptObj (K := ℂ) ℂ ⟶ A.X ⊗ A.X)]
    [ChartedSpace (Fin g → ℂ) (A.Pt ℂ)]
    [ChartedSpace (Fin n → ℂ) (AbVar.ptObj (K := ℂ) ℂ ⟶ A.X ⊗ A.X)]
    [IsManifold 𝓘(ℂ, Fin g → ℂ) ω (A.Pt ℂ)]
    [IsManifold 𝓘(ℂ, Fin n → ℂ) ω (AbVar.ptObj (K := ℂ) ℂ ⟶ A.X ⊗ A.X)]
    (hreg : ∀ α : A.X ⟶ A.X,
      ContMDiff 𝓘(ℂ, Fin g → ℂ) 𝓘(ℂ, Fin g → ℂ) ω (fun P : A.Pt ℂ => P ≫ α))
    (hreg21 : ∀ α : A.X ⊗ A.X ⟶ A.X,
      ContMDiff 𝓘(ℂ, Fin n → ℂ) 𝓘(ℂ, Fin g → ℂ) ω
        (fun P : AbVar.ptObj (K := ℂ) ℂ ⟶ A.X ⊗ A.X => P ≫ α))
    (hreg12 : ∀ α : A.X ⟶ A.X ⊗ A.X,
      ContMDiff 𝓘(ℂ, Fin g → ℂ) 𝓘(ℂ, Fin n → ℂ) ω (fun P : A.Pt ℂ => P ≫ α)) :
    LieGroup 𝓘(ℂ, Fin g → ℂ) ω (A.Pt ℂ) := by
  set pr : (AbVar.ptObj (K := ℂ) ℂ ⟶ A.X ⊗ A.X) → A.Pt ℂ × A.Pt ℂ :=
    fun R => (R ≫ fst _ _, R ≫ snd _ _) with hprdef
  set σ : A.Pt ℂ × A.Pt ℂ → (AbVar.ptObj (K := ℂ) ℂ ⟶ A.X ⊗ A.X) :=
    fun x => lift x.1 x.2 with hσdef
  have hprσ : ∀ x, pr (σ x) = x := fun x => by simp [hprdef, hσdef]
  have hprinj : Function.Injective pr := by
    intro R R' h
    simp only [hprdef, Prod.mk.injEq] at h
    exact CartesianMonoidalCategory.hom_ext _ _ h.1 h.2
  have hpr : ContMDiff 𝓘(ℂ, Fin n → ℂ) (𝓘(ℂ, Fin g → ℂ).prod 𝓘(ℂ, Fin g → ℂ)) ω pr :=
    (hreg21 (fst _ _)).prodMk (hreg21 (snd _ _))
  have hσ : ContMDiff (𝓘(ℂ, Fin g → ℂ).prod 𝓘(ℂ, Fin g → ℂ)) 𝓘(ℂ, Fin n → ℂ) ω σ := by
    rintro ⟨P₀, Q₀⟩
    have hsurj := surjective_mfderiv_of_sections pr (lift P₀ Q₀) ((hpr _).mdifferentiableAt (by simp))
      (fun P => P ≫ secL A Q₀) (fun Q => Q ≫ secR A P₀) P₀ Q₀
      ((hreg12 _ _).mdifferentiableAt (by simp)) ((hreg12 _ _).mdifferentiableAt (by simp))
      (comp_secL A P₀ Q₀) (comp_secR A P₀ Q₀) (fun P => by simp [hprdef, comp_secL])
      (fun Q => by simp [hprdef, comp_secR])
    have h := contMDiffAt_rightInverse pr (lift P₀ Q₀) (hpr _) hprinj hsurj σ hprσ
    simpa [hprdef] using h
  refine { contMDiff_mul := ?_, contMDiff_inv := ?_ }
  · have h := (hreg21 μ[A.X]).comp hσ
    refine h.congr fun p => ?_
    simp [hσdef, Hom.mul_def]
  · refine (hreg ι[A.X]).congr fun P => ?_
    simp [Hom.inv_def]
end FixedVariety

end
end CloudB3W17Uniformization
