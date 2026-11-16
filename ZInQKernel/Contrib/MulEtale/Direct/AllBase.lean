import ZInQKernel.Contrib.MulEtale.Direct.FibreMultiplication
import ZInQKernel.Contrib.MulEtale.Direct.Global.SmoothFiberDetector

/-!
# Multiplication étaleness on the given abelian scheme over any commutative ring

The two structural smoothness inputs are the same given abelian-scheme map.
The fibre hypothesis is proved on its actual residue fibres. No field,
Noetherian, DVR, Henselian, nontriviality or positive-index restriction is added.
Acceptance requires this complete source and its dependencies to compile and
pass the independent exact-contract, stored-body and axiom checks.
-/

noncomputable section
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

namespace H101DirectFieldRoute

/-- The unchanged full arbitrary-base H-101 telescope. -/
theorem multiplication_etale (O : Type) [CommRing O]
    (A : Grp (Over (Spec (.of O)))) [PkgI2.IsAbelianScheme A]
    (m : ℕ) (hm : IsUnit (m : O)) :
    Etale ((𝟙 A.X ^ m : A.X ⟶ A.X).left) := by
  letI : Smooth A.X.hom := PkgI2.IsAbelianScheme.smooth
  letI : Smooth ((𝟙 A.X ^ m : A.X ⟶ A.X).left ≫ A.X.hom) := by
    rw [Over.w]
    infer_instance
  exact H101DirectGlobalDetection.etale_of_smooth_structural_and_etale_fibers
    (𝟙 A.X ^ m : A.X ⟶ A.X).left A.X.hom
    (fun s => FibreMultiplication.fiberHom_pow_etale A s m hm)

end H101DirectFieldRoute
