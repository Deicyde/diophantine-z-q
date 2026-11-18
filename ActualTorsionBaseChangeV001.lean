import ActualFiniteLevelActionV003
import ZInQKernel.Contrib.AbVarBC.Points

/-!
# Native base-change transport of the entire torsion subgroup

The point bijection restricts to a multiplicative bijection on ALL points
killed by the given integer. Both group laws are the original scheme
point laws, not models chosen for the representation.
-/

noncomputable section
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry MonObj

namespace ActualTorsionBaseChange
open ActualFiniteLevel
variable {K Ω : Type} [Field K] [Field Ω] [Algebra K Ω]

def torsionEquiv (A : PkgI3.AbVar K) (m : ℕ) :
    torsionSubgroup (A.baseChange Ω) Ω m ≃* torsionSubgroup A Ω m := by
  let e := ZInQ.Contrib.AbVarBC.bcPt (L := Ω) A Ω
  exact
    { toFun := fun x => ⟨e x.1, by
        change e x.1 ^ m = 1
        rw [← map_pow]
        exact (congrArg e x.2).trans (map_one _)⟩
      invFun := fun x => ⟨e.symm x.1, by
        change e.symm x.1 ^ m = 1
        rw [← map_pow]
        exact (congrArg e.symm x.2).trans (map_one _)⟩
      left_inv := fun x => Subtype.ext (e.symm_apply_apply x.1)
      right_inv := fun x => Subtype.ext (e.apply_symm_apply x.1)
      map_mul' := fun x y => Subtype.ext (map_mul e x.1 y.1) }

lemma torsionEquiv_coe (A : PkgI3.AbVar K) (m : ℕ)
    (x : torsionSubgroup (A.baseChange Ω) Ω m) :
    (torsionEquiv A m x).1 = ZInQ.Contrib.AbVarBC.bcPt (L := Ω) A Ω x.1 := rfl

lemma baseChanged_torsion_eq_original (A : PkgI3.AbVar K) (m : ℕ) :
    Nat.card (torsionSubgroup (A.baseChange Ω) Ω m) = Nat.card (torsionSubgroup A Ω m) :=
  Nat.card_congr (torsionEquiv A m).toEquiv

end ActualTorsionBaseChange
