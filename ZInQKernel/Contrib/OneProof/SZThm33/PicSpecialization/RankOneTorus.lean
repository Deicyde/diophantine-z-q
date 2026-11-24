import ZInQKernel.Contrib.OneProof.FaltingsDict2SplitTorus
import Mathlib.Algebra.MvPolynomial.Equiv

noncomputable section

open CategoryTheory AlgebraicGeometry
open Opposite

namespace ZInQ.ToricOrthogonality

open ZInQ.FaltingsRestate ZInQ.SemiAbDescend

/-- The coordinate algebra of the rank-one split torus is the polynomial
algebra localized at its single variable. -/
def rankOneTorusRingEquiv (k : Type) [Field k] :
    TorusRing k 1 ≃ₐ[k] Localization.Away (Polynomial.X : Polynomial k) := by
  let e := MvPolynomial.uniqueAlgEquiv k (Fin 1)
  let p : MvPolynomial (Fin 1) k := ∏ i : Fin 1, MvPolynomial.X i
  have hp : e p = Polynomial.X := by
    simp [p, e, Fintype.prod_unique]
  let : IsLocalization.Away (e.toAlgHom p) (Localization.Away (Polynomial.X : Polynomial k)) := by
    rw [show e.toAlgHom p = Polynomial.X from hp]
    infer_instance
  refine AlgEquiv.ofBijective (IsLocalization.Away.mapₐ (TorusRing k 1)
    (Localization.Away (Polynomial.X : Polynomial k)) e.toAlgHom p) ⟨?_, ?_⟩
  · exact IsLocalization.Away.mapₐ_injective_of_injective (f := e.toAlgHom) p e.injective
  · exact IsLocalization.Away.mapₐ_surjective_of_surjective (f := e.toAlgHom) p e.surjective

/-- The rank-one split torus is the punctured affine line over the field. -/
def rankOneTorusIso (k : Type) [Field k] :
    splitTorus k 1 ≅ Over.mk (Spec.map (CommRingCat.ofHom
      (algebraMap k (Localization.Away (Polynomial.X : Polynomial k))))) :=
  (algSpec (CommRingCat.of k)).mapIso (CommAlgCat.isoMk (rankOneTorusRingEquiv k)).symm.op

/-- The actual rank-one split torus written as the open affine line. -/
abbrev puncturedLine (k : Type) [Field k] : Over (Spec (.of k)) :=
  Over.mk (Spec.map (CommRingCat.ofHom
    (algebraMap k (Localization.Away (Polynomial.X : Polynomial k)))))

instance puncturedLine_grpObj (k : Type) [Field k] : GrpObj (puncturedLine k) :=
  GrpObj.ofIso (rankOneTorusIso k)

instance rankOneTorusIso_isMonHom (k : Type) [Field k] : IsMonHom (rankOneTorusIso k).hom :=
  isMonHom_ofIso _

end ZInQ.ToricOrthogonality

#print axioms ZInQ.ToricOrthogonality.rankOneTorusIso
