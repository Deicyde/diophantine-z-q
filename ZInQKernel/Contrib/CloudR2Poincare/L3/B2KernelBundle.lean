import ZInQKernel.Contrib.CloudR2Poincare.L3.B2Interface
import ZInQKernel.Contrib.CloudR2Poincare.L2.MumfordSymmetry
import ZInQKernel.Contrib.CloudR2Poincare.L2.NativeSquare
import ZInQKernel.Contrib.CloudR2Poincare.L4.ProductGeometry

/-!
# Mumford's B2 kernel bundle: actual coefficients and rational fibres

The coefficient is precisely m* M ⊗ p1* M⁻¹ ⊗ p2*(M⁻¹ ⊗ N⁻¹), using
the native W07 tensor/dual/pullback operations. Neither B1 nor the single
shared square input is assumed as an instance.
-/

noncomputable section
open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory
open scoped MonObj AlgebraicGeometry.Scheme.Modules

namespace ZInQ.Contrib.CloudR2Poincare.L3

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option linter.style.haveILetI false

universe u
variable {k : Type u} [Field k] (B : PkgI3.AbVar k)

/-- The actual Mumford coefficient sheaf on B×B. -/
def mumfordKernelBundle (M N : B.X.left.Modules) : (B.X ⊗ B.X).left.Modules :=
  (Scheme.Modules.pullback μ[B.X].left).obj M ⊗
    (Scheme.Modules.pullback (fst B.X B.X).left).obj Mᵛ ⊗
      (Scheme.Modules.pullback (snd B.X B.X).left).obj (Mᵛ ⊗ Nᵛ)

instance mumfordKernelBundle_invertible (M N : B.X.left.Modules)
    [M.IsInvertible] [N.IsInvertible] : (mumfordKernelBundle B M N).IsInvertible := by
  dsimp [mumfordKernelBundle]
  infer_instance

/-- First-factor fibre inclusion b×B. -/
def firstSlice (b : 𝟙_ (Over (Spec (.of k))) ⟶ B.X) : B.X ⟶ B.X ⊗ B.X :=
  lift (toUnit B.X ≫ b) (𝟙 B.X)

/-- Second-factor fibre inclusion B×b. -/
def secondSlice (b : 𝟙_ (Over (Spec (.of k))) ⟶ B.X) : B.X ⟶ B.X ⊗ B.X :=
  lift (𝟙 B.X) (toUnit B.X ≫ b)

/-- The complete native Picard class of the Mumford coefficient. -/
theorem mumfordKernelBundle_class (M N : B.X.left.Modules)
    [M.IsInvertible] [N.IsInvertible] :
    Scheme.Pic.mk (mumfordKernelBundle B M N) =
      Scheme.Pic.map μ[B.X].left (Scheme.Pic.mk M) *
        (Scheme.Pic.map (fst B.X B.X).left (Scheme.Pic.mk M))⁻¹ *
        (Scheme.Pic.map (snd B.X B.X).left (Scheme.Pic.mk M))⁻¹ *
        (Scheme.Pic.map (snd B.X B.X).left (Scheme.Pic.mk N))⁻¹ := by
  simp [mumfordKernelBundle, ← Scheme.Pic.map_mk, L1.pic_map_inv, mul_assoc]

/-- Restriction to b×B gives φ_M(b)⊗N⁻¹. -/
theorem mumfordKernelBundle_firstSlice_class (M N : B.X.left.Modules)
    [M.IsInvertible] [N.IsInvertible]
    (b : 𝟙_ (Over (Spec (.of k))) ⟶ B.X) :
    Scheme.Pic.map (firstSlice B b).left (Scheme.Pic.mk (mumfordKernelBundle B M N)) =
      L1.translationClass B.X (Scheme.Pic.mk M) b * (Scheme.Pic.mk N)⁻¹ := by
  have hm : firstSlice B b ≫ μ[B.X] = L1.translate B.X b := by
    simp [firstSlice, L1.translate, MonObj.comp_mul, MonObj.mul_eq_mul]
  have hc : (firstSlice B b ≫ fst B.X B.X).left = B.X.hom ≫ b.left := by
    simp [firstSlice, Over.comp_left]
  simp only [mumfordKernelBundle_class, Scheme.Pic.map_mul, L1.pic_map_inv,
    ← Scheme.Pic.map_comp, ← Over.comp_left, hm, hc]
  rw [L2.pic_map_constant_eq_one]
  simp [firstSlice, L1.translationClass, mul_assoc, ← Scheme.Pic.map_mk]

/-- Restriction to B×b gives φ_M(b), independently of N. -/
theorem mumfordKernelBundle_secondSlice_class (M N : B.X.left.Modules)
    [M.IsInvertible] [N.IsInvertible]
    (b : 𝟙_ (Over (Spec (.of k))) ⟶ B.X) :
    Scheme.Pic.map (secondSlice B b).left (Scheme.Pic.mk (mumfordKernelBundle B M N)) =
      L1.translationClass B.X (Scheme.Pic.mk M) b := by
  have hm : secondSlice B b ≫ μ[B.X] = L1.translate B.X b := by
    simp [secondSlice, L1.translate, MonObj.comp_mul, MonObj.mul_eq_mul, mul_comm]
  have hc : (secondSlice B b ≫ snd B.X B.X).left = B.X.hom ≫ b.left := by
    simp [secondSlice, Over.comp_left]
  simp only [mumfordKernelBundle_class, Scheme.Pic.map_mul, L1.pic_map_inv,
    ← Scheme.Pic.map_comp, ← Over.comp_left, hm, hc]
  rw [L2.pic_map_constant_eq_one, L2.pic_map_constant_eq_one]
  simp [secondSlice, L1.translationClass, ← Scheme.Pic.map_mk]

/-- In particular the actual fibre coefficient along B×0 is trivial. -/
theorem mumfordKernelBundle_zeroSlice_class (M N : B.X.left.Modules)
    [M.IsInvertible] [N.IsInvertible] :
    Scheme.Pic.map (secondSlice B (1 : 𝟙_ (Over (Spec (.of k))) ⟶ B.X)).left
      (Scheme.Pic.mk (mumfordKernelBundle B M N)) = 1 := by
  rw [mumfordKernelBundle_secondSlice_class]
  simp [L1.translationClass, ← Scheme.Pic.map_mk]

/-- Actual sheaf, not only Picard-class, triviality on B×0. -/
theorem mumfordKernelBundle_zeroSlice_iso (M N : B.X.left.Modules)
    [M.IsInvertible] [N.IsInvertible] :
    Nonempty ((Scheme.Modules.pullback
      (secondSlice B (1 : 𝟙_ (Over (Spec (.of k))) ⟶ B.X)).left).obj
      (mumfordKernelBundle B M N) ≅ SheafOfModules.unit B.X.left.ringCatSheaf) := by
  apply (Scheme.Pic.mk_eq_mk_iff _ _).mp
  rw [← Scheme.Pic.map_mk, ← Scheme.Pic.one_eq_mk_unit]
  exact mumfordKernelBundle_zeroSlice_class B M N

end ZInQ.Contrib.CloudR2Poincare.L3
