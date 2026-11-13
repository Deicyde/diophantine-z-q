import TateFreeness
import AxiomBridge.GeometryDimension

/-
DRAFT — not compiled or kernel-checked yet.

GeometryDimension is a packaging of ONLY the general G0Dim scheme derivations
from mirror83651ea scratch/g0-dim/Dim.lean, not its copied AbVar declarations.
This consumer applies those existing proofs to the genuine HDecomp.Objects A.
No rank, registered T26, C10 or H result is claimed by writing this draft.
-/

noncomputable section

namespace AxiomBridge.TateConsumer

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory
open scoped MonObj

variable {k : Type} [Field k]

/-- The native base-change object has the same original scheme dimension,
using the existing general scheme proof rather than a desired dimension Fact. -/
theorem geometric_dim_eq (A : PkgI3.AbVar k) :
    (A.baseChange (AlgebraicClosure k)).dim = A.dim :=
  G0Dim.dim_baseChange (AlgebraicClosure k) A.X.left A.X.hom

/-- Recover the natural-number dimension of the actual pullback from a
finite dimension witness for the original object. The final theorem below
constructs that witness; it is not an extra registered-provider assumption. -/
theorem tate_finrank_of_dim (A : PkgI3.AbVar k) (ℓ : ℕ) [Fact ℓ.Prime]
    (hℓ : (ℓ : k) ≠ 0) (g : ℕ) (hg : A.dim = (g : WithBot ℕ∞)) :
    Module.finrank ℤ_[ℓ] (A.T ℓ) = 2 * g := by
  let B := A.baseChange (AlgebraicClosure k)
  letI : AlgebraicGeometry.IsAbelianVariety (AlgebraicClosure k) B.X :=
    geometric_isAbelianVariety A
  have hu : IsUnit (ℓ : AlgebraicClosure k) := prime_isUnit_on_geometric_field ℓ hℓ
  have hBg : topologicalKrullDim B.X.left = (g : WithBot ℕ∞) :=
    (geometric_dim_eq A).trans hg
  calc
    Module.finrank ℤ_[ℓ] (A.T ℓ) =
        Module.finrank ℤ_[ℓ] (Stacks.Groupoids.tateModule B.X ℓ) :=
      (geometricTateEquiv A ℓ).finrank_eq
    _ = 2 * Stacks.Groupoids.abelianVarietyDimension B.X :=
      Stacks.Groupoids.finrank_tateModule B.X ℓ hu
    _ = 2 * g := by
      simp [Stacks.Groupoids.abelianVarietyDimension, hBg]

/-- Intended exact whole baseline predicate: all fields and abelian varieties,
all primes invertible in the original field, with no extra dimension, basis,
model or algebraic-closure hypothesis. This declaration remains a draft until
its complete type, body and axiom closure are actually checked. -/
theorem tateModuleFree : PkgI3.TateModuleFree := by
  intro k _ A ℓ _ hℓ
  haveI : Nonempty A.X.left :=
    ⟨η[A.X].left
      (Nonempty.some (inferInstance : Nonempty (Spec (CommRingCat.of k))))⟩
  obtain ⟨g, hg⟩ := G0Dim.dim_finite A.X.left A.X.hom
  have hgA : A.dim = (g : WithBot ℕ∞) := hg
  have hf := tate_free_finite A ℓ hℓ
  refine ⟨hf.1, hf.2, ?_⟩
  have hr := tate_finrank_of_dim A ℓ hℓ g hgA
  rw [hr, hgA]
  norm_cast

end AxiomBridge.TateConsumer

#check AxiomBridge.TateConsumer.tateModuleFree
#print axioms AxiomBridge.TateConsumer.geometric_dim_eq
#print axioms AxiomBridge.TateConsumer.tate_finrank_of_dim
#print axioms AxiomBridge.TateConsumer.tateModuleFree
