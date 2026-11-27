import ZInQKernel.Contrib.OneProof.SmoothNormal.Normal
import ZInQKernel.Contrib.OneProof.SmoothNormal.Product
import ZInQKernel.Contrib.OneProof.SmoothNormal.Projective

set_option autoImplicit false
noncomputable section
open CategoryTheory AlgebraicGeometry
namespace Y3Buzzard.SmoothNormal

/-!
# The base of the level-`V₁(5)` moduli problem is normal

From EGA IV₄, Prop. (17.5.7) (`EGAIV17_5_7`): the moduli scheme `X` of `BuzzardThm21Cor23V15'`
is smooth over `Spec Z[1/30]`, whose local rings are integrally closed domains, so the local rings
of `X` are integrally closed domains. Hence the ring of every affine open of `X` is noetherian with
integrally closed local rings at its primes (`isNormalNoeth_of_B1`), and so it is a finite product
of integrally closed domains (`exists_piEquiv_of_normal`).

`Projective` then replaces `ProjectiveFEC` in the level-three argument by `EGAIV17_5_7` and
`LocProjNormal` (`y3FullThreeRepZ30_of_printed_locProj`); `LocProjNormal` is the form in which a
printed projectivity theorem for abelian schemes over a normal base will enter.
-/

/-- The ring of every affine open of the moduli scheme `X` of `BuzzardThm21Cor23V15'` is a finite
product of integrally closed domains. -/
theorem affine_piEquiv_of_B1 (hE : EGAIV17_5_7) (hB1 : BuzzardThm21Cor23V15')
    (U : (leafD hB1).X.left.Opens) (hU : IsAffineOpen U) :
    ∃ (n : ℕ) (D : Fin n → Type) (_ : ∀ i, CommRing (D i)) (_ : ∀ i, IsDomain (D i))
      (_ : ∀ i, IsIntegrallyClosed (D i)), Nonempty (Γ((leafD hB1).X.left, U) ≃+* ∀ i, D i) := by
  have h := isNormalNoeth_of_B1 hE hB1 U hU
  have := h.1
  exact exists_piEquiv_of_normal _ h.2

end Y3Buzzard.SmoothNormal
