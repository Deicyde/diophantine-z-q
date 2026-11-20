import ZInQKernel.Contrib.OneProof.DirectWeil.FiniteWeilPairing
import ZInQKernel.Contrib.OneProof.DirectWeil.TateFiniteSubgroup

noncomputable section

open CategoryTheory AlgebraicGeometry
open PkgI3 PkgI3.AbVar HDec.WeilPairing
open scoped CategoryTheory.MonObj

namespace PicDict.DirectPairing

/-- A Tate tower killed by a finite-kernel polarization at every level is zero. -/
theorem tate_eq_zero_of_torsionClass_eq_one {K : Type} [Field K] (A : AbVar K) (L : A.X.left.Pic)
    {ℓ : ℕ} [Fact ℓ.Prime] (y : PkgI3.Tate.T ℓ (P A))
    (hfin : {x : A.Pt (AlgebraicClosure K) | polarization A L x = 1}.Finite)
    (hy : ∀ n, torsionClass A L (⟨y.1 n, PkgI3.Tate.pow_smul_eq_zero y.2 n⟩ : tors A (ℓ ^ n)) = 1) :
    y = 0 := by
  exact PkgI3.Tate.eq_zero_of_apply_eq_one_of_finite_kernel (M := P A) (polarization A L) hfin y hy

/-- Finite-level right radicals have zero inverse limit for a finite-kernel polarization. -/
theorem tate_eq_zero_of_finitePairing_eq_zero {K : Type} [Field K] (A : AbVar K) (L : A.X.left.Pic)
    {ℓ : ℕ} [Fact ℓ.Prime] (hℓK : (ℓ : K) ≠ 0) (y : PkgI3.Tate.T ℓ (P A))
    (hfin : {x : A.Pt (AlgebraicClosure K) | polarization A L x = 1}.Finite)
    (hy : ∀ n, ∀ x : tors A (ℓ ^ n),
      finitePairing A L (pow_pos (Fact.out : ℓ.Prime).pos n)
        (by rw [Nat.cast_pow]; exact pow_ne_zero n hℓK)
        x ⟨y.1 n, PkgI3.Tate.pow_smul_eq_zero y.2 n⟩ = 0) : y = 0 :=
  tate_eq_zero_of_torsionClass_eq_one A L y hfin fun n =>
    finitePairing_right_radical A L _ _ _ (hy n)

end PicDict.DirectPairing
