import ZInQKernel.Contrib.OneProof.EGAIV_8_10_5_xii

open CategoryTheory Limits AlgebraicGeometry

namespace EGALimitCopy

/-- Verbatim copy of `ZInQ.Contrib.SpreadOut.EGAIV_8_10_5_xii` (Spread.lean L49 @ 2880fef1). -/
def EGAIV_8_10_5_xii : Prop :=
  ∀ (J : Type) [Preorder J] [IsDirectedOrder J] [Nonempty J] (D : Jᵒᵖ ⥤ Scheme.{0})
    [∀ {i j : Jᵒᵖ} (f : i ⟶ j), IsAffineHom (D.map f)] [∀ i, CompactSpace (D.obj i)]
    [∀ i, QuasiSeparatedSpace (D.obj i)] (c : Cone D), IsLimit c →
    ∀ (i : Jᵒᵖ) (Xi : Over (D.obj i)), LocallyOfFinitePresentation Xi.hom → QuasiCompact Xi.hom →
      QuasiSeparated Xi.hom → IsProper ((Over.pullback (c.π.app i)).obj Xi).hom →
      ∃ (j : Jᵒᵖ) (a : j ⟶ i), IsProper ((Over.pullback (D.map a)).obj Xi).hom

example : EGAIV_8_10_5_xii ↔ ZInQ.Contrib.SpreadOut.EGAIV_8_10_5_xii := Iff.rfl

theorem egaIV_8_10_5_xii_copy : EGAIV_8_10_5_xii :=
  ZInQ.Contrib.EGAProperLimit.egaIV_8_10_5_xii_proof

end EGALimitCopy

#print axioms EGALimitCopy.egaIV_8_10_5_xii_copy
