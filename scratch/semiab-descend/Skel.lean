import ZInQKernel.Contrib.OneProof.PrintedStableHeight
import ZInQKernel.Contrib.OneProof.GeomConnOfRationalPoint

/-! Skeleton: `SemiAbelianDescendsPerfect` from Chevalley over a perfect field, with the glue as `sorry`d
lemmas (development file). -/

noncomputable section

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open DictModels.RaynaudOr ZInQ.HeightSplit

set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false

namespace ZInQ.SemiAbDescend

section Defs

variable {k : Type} [Field k]

/-- The scheme-theoretic kernel of `π : G → B` (fibre product with the unit section of `B`). -/
abbrev kerObj {G B : Over (Spec (CommRingCat.of k))} [GrpObj B] (π : G ⟶ B) :
    Over (Spec (CommRingCat.of k)) :=
  pullback π η[B]

/-- The kernel is a smooth connected affine `k`-scheme. -/
def IsSmoothConnAffineKer {G B : Over (Spec (CommRingCat.of k))} [GrpObj B] (π : G ⟶ B) : Prop :=
  Smooth (kerObj π).hom ∧ IsAffine (kerObj π).left ∧ ConnectedSpace (kerObj π).left

/-- `π : G → B` presents the abelian variety `B` as `G/H`: a faithfully flat homomorphism with smooth
connected affine kernel `H`. -/
def IsChevalleyQuotient {G : Over (Spec (CommRingCat.of k))} [GrpObj G] (B : PkgI3.AbVar k)
    (π : G ⟶ B.X) : Prop :=
  IsMonHom π ∧ Flat π.left ∧ Surjective π.left ∧ IsSmoothConnAffineKer π

end Defs

/-- **LEAF `ChevalleyPerfect`**. -/
def ChevalleyPerfect : Prop :=
  ∀ (k : Type) [Field k] [PerfectField k] (G : Over (Spec (CommRingCat.of k))) [GrpObj G],
    Smooth G.hom → QuasiCompact G.hom → ConnectedSpace G.left →
    (∃ (B : PkgI3.AbVar k) (π : G ⟶ B.X), IsChevalleyQuotient B π) ∧
    ∀ (B₁ B₂ : PkgI3.AbVar k) (π₁ : G ⟶ B₁.X) (π₂ : G ⟶ B₂.X),
      IsChevalleyQuotient B₁ π₁ → IsChevalleyQuotient B₂ π₂ →
      ∀ (T : Over (Spec (CommRingCat.of k))) (x : T ⟶ G), x ≫ π₁ = 1 ↔ x ≫ π₂ = 1

end ZInQ.SemiAbDescend
