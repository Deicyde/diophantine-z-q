import ZInQKernel.Contrib.OneProof.EllAdic.AdditiveTowerKernelEquivV1
import ZInQKernel.Contrib.OneProof.EllAdic.PadicProEtHOneActualSiteV2
import ZInQKernel.Contrib.OneProof.EllAdic.SmallEtaleResidueHOneReductionV1

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits Opposite

namespace RC53.EllAdic

universe u

local instance actualEtaleHOneEtaleGrothendieck (S : Scheme.{u}) :
    IsGrothendieckAbelian.{u+1} (Sheaf S.smallEtaleTopology Ab.{u+1}) := by
  let : EssentiallySmall.{u+1} S.Etale := inferInstance
  exact Sheaf.isGrothendieckAbelian_of_essentiallySmall S.smallEtaleTopology Ab.{u+1}

/-- Finite constant coefficient cohomology on the actual small étale site. -/
abbrev etaleResidueHOne (S : Scheme.{u}) (p n : ℕ) : Type (u+1) :=
  (etaleConstantResidue S p n).H 1

/-- This transition is cohomology of the literal reduction. -/
noncomputable def etaleResidueHOneReduction (S : Scheme.{u}) (p n : ℕ) :
    etaleResidueHOne S p (n+1) →+ etaleResidueHOne S p n :=
  Sheaf.H.map ((constantSheaf S.smallEtaleTopology Ab.{u+1}).map
    (liftedResidueCoefficientTransition.{u} p (Nat.le_succ n))) 1

/-- The compatible étale families are the kernel of the tower difference. -/
noncomputable def etaleResidueHOneSubShift (S : Scheme.{u}) (p : ℕ) :
    (∀ n, etaleResidueHOne S p n) →+ (∀ n, etaleResidueHOne S p n) where
  toFun x n := x n - etaleResidueHOneReduction S p n (x (n+1))
  map_zero' := by
    funext n
    change (0 : etaleResidueHOne S p n) - etaleResidueHOneReduction S p n 0 = 0
    rw [(etaleResidueHOneReduction S p n).map_zero, sub_self]
  map_add' x y := by
    funext n
    change (x n + y n) - etaleResidueHOneReduction S p n (x (n+1) + y (n+1)) =
      (x n - etaleResidueHOneReduction S p n (x (n+1))) +
      (y n - etaleResidueHOneReduction S p n (y (n+1)))
    rw [map_add, add_sub_add_comm]

private theorem etaleHOneDiff_at (S : Scheme.{u}) (p : ℕ)
    (x : ∀ n, etaleResidueHOne S p n) (n : ℕ) :
    etaleResidueHOneSubShift S p x n = x n - etaleResidueHOneReduction S p n (x (n+1)) := rfl

private theorem proEtHOneDiff_at (S : Scheme.{u}) (p : ℕ)
    (x : ∀ n, liftedFiniteResidueHOne S p n) (n : ℕ) :
    residueHOneSubShift S p x n = x n - liftedFiniteResidueHOneReduction S p n (x (n+1)) := rfl

private theorem etaleHOneActual_square (S : Scheme.{u}) (p n : ℕ)
    (x : etaleResidueHOne S p (n+1)) :
    liftedFiniteResidueHOneReduction S p n (smallEtaleResidueHOneForward S p (n+1) x) =
      smallEtaleResidueHOneForward S p n (etaleResidueHOneReduction S p n x) :=
  smallEtaleResidueHOneForward_reduction S p (Nat.le_succ n) x

/-- This is the equivalence on the same two kernels and actual coordinate maps. -/
noncomputable def etaleResidueHOneCompatibleEquiv_of_bijective (S : Scheme.{u}) (p : ℕ)
    (hf : ∀ n, Function.Bijective (smallEtaleResidueHOneForward S p n)) :
    ↥(etaleResidueHOneSubShift S p).ker ≃+ ↥(residueHOneSubShift S p).ker :=
  @additiveTowerKernelEquiv (etaleResidueHOne S p) (liftedFiniteResidueHOne S p)
    (fun n => inferInstanceAs (AddCommGroup (etaleResidueHOne S p n)))
    (fun n => inferInstanceAs (AddCommGroup (liftedFiniteResidueHOne S p n)))
    (etaleResidueHOneReduction S p) (liftedFiniteResidueHOneReduction S p)
    (etaleResidueHOneSubShift S p) (residueHOneSubShift S p) (etaleHOneDiff_at S p) (proEtHOneDiff_at S p)
    (smallEtaleResidueHOneForward S p) (etaleHOneActual_square S p) hf

noncomputable def ellAdicHOne_actualEtale_equiv_of_bijective (S : Scheme.{u}) (p : ℕ) [Fact p.Prime]
    (hf : ∀ n, Function.Bijective (smallEtaleResidueHOneForward S p n)) :
    S.EllAdicCohomology p 1 ≃+ ↥(etaleResidueHOneSubShift S p).ker :=
  (ellAdicHOne_actualSite_equiv S p).trans (etaleResidueHOneCompatibleEquiv_of_bijective S p hf).symm

theorem ellAdicHOne_actualEtale_equiv_apply_of_bijective (S : Scheme.{u}) (p : ℕ) [Fact p.Prime]
    (hf : ∀ n, Function.Bijective (smallEtaleResidueHOneForward S p n))
    (x : S.EllAdicCohomology p 1) (n : ℕ) :
    smallEtaleResidueHOneForward S p n ((ellAdicHOne_actualEtale_equiv_of_bijective S p hf x).val n) =
      Sheaf.H.map ((continuousResidueProEtSheafCone S p).π.app (op n)) 1 x := by
  let y := ellAdicHOne_actualSite_equiv S p x
  have hre := @additiveTowerKernelEquiv_symm_coordinate (etaleResidueHOne S p) (liftedFiniteResidueHOne S p)
    (fun j => inferInstanceAs (AddCommGroup (etaleResidueHOne S p j)))
    (fun j => inferInstanceAs (AddCommGroup (liftedFiniteResidueHOne S p j)))
    (etaleResidueHOneReduction S p) (liftedFiniteResidueHOneReduction S p)
    (etaleResidueHOneSubShift S p) (residueHOneSubShift S p) (etaleHOneDiff_at S p) (proEtHOneDiff_at S p)
    (smallEtaleResidueHOneForward S p) (etaleHOneActual_square S p) hf y n
  exact hre.trans (ellAdicHOne_actualSite_equiv_apply S p x n)

end RC53.EllAdic
