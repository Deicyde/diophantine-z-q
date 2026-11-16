import ZInQKernel.HDecomp.QM.Structures

/-!
# D5: explicit transport of kernel data, retaining the carrier

Original dictionary proof, 2026-11-16, W13 D5 with Metamate/agentcloud assistance.
The helpers transport only genuine kernel data. Morphism formulas explicitly
record the carrier equality, so using them never rewrites a dependent FLT goal
whose morphisms are tied definitionally to its original carrier.
-/

noncomputable section

namespace ZInQ.Contrib.CloudB2Shimura.Dictionary.D5

open CategoryTheory AlgebraicGeometry PkgI3 LeafQM

variable {K : Type} [Field K]

/-- Surface dimension transported along an equality of genuine abelian varieties. -/
def surfaceOfEq (P : AV.QML3 K) (B : AbVar K) (h : B = P.A) : B.dim = 2 :=
  h.symm ▸ P.surface

/-- The original quaternion action transported along the equality. -/
def qmOfEq (P : AV.QML3 K) (B : AbVar K) (h : B = P.A) : AV.QMStr B :=
  h.symm ▸ P.q

/-- The original level structure transported along the same equality. -/
def levelOfEq (P : AV.QML3 K) (B : AbVar K) (h : B = P.A) :
    AV.Level3 (qmOfEq P B h) := by
  cases h
  exact P.e

/-- The transported object, with the exact original kernel data. -/
def objectOfEq (P : AV.QML3 K) (B : AbVar K) (h : B = P.A) : AV.QML3 K :=
  ⟨B, surfaceOfEq P B h, qmOfEq P B h, levelOfEq P B h⟩

/-- Explicit carrier transport for the original action. -/
theorem qmOfEq_hom (P : AV.QML3 K) (B : AbVar K) (h : B = P.A)
    (hX : B.X = P.A.X) (a : O) :
    ((qmOfEq P B h).iota a).hom =
      eqToHom hX ≫ (P.q.iota a).hom ≫ eqToHom hX.symm := by
  cases h
  have hr : hX = (rfl : P.A.X = P.A.X) := Subsingleton.elim _ _
  cases hr
  simp only [qmOfEq, eqToHom_refl, Category.id_comp, Category.comp_id]

/-- Explicit carrier transport for the original level point. -/
theorem levelOfEq_pt (P : AV.QML3 K) (B : AbVar K) (h : B = P.A)
    (hX : B.X = P.A.X) (a : O) :
    Additive.toMul ((levelOfEq P B h).eta a) =
      Additive.toMul (P.e.eta a) ≫ eqToHom hX.symm := by
  cases h
  have hr : hX = (rfl : P.A.X = P.A.X) := Subsingleton.elim _ _
  cases hr
  simp only [levelOfEq, eqToHom_refl, Category.comp_id]

/-- The transported object is isomorphic to the original object. This is a
kernel isomorphism, not an assumed model-identification statement. -/
def objectOfEq_iso (P : AV.QML3 K) (B : AbVar K) (h : B = P.A) :
    AV.QML3.Iso (objectOfEq P B h) P := by
  cases h
  exact AV.QML3.Iso.refl P

end ZInQ.Contrib.CloudB2Shimura.Dictionary.D5
