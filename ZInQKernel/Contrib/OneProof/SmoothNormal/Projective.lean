import ZInQKernel.Contrib.OneProof.SmoothNormal.Normal
import ZInQKernel.Contrib.OneProof.SmoothNormal.ProjectiveGlue
import ZInQKernel.Contrib.OneProof.SmoothNormal.ChainFSA

set_option autoImplicit false
noncomputable section
open CategoryTheory AlgebraicGeometry
namespace Y3Buzzard.SmoothNormal

open ProjGlue

/-!
# From local projectivity over normal affine bases to the moduli target

`LocProjNormal` asks that every false elliptic curve over a `Z[1/30]`-scheme, restricted to an
affine open whose ring is noetherian with integrally closed local rings, have a closed immersion
into a projective space over that ring. It is the form in which a printed projectivity theorem for
abelian schemes over a normal base enters; it is not itself a printed statement. With it and the
normality of the moduli base (`EGAIV17_5_7`), the total space of the universal family has finite
sets in affine opens, which is the only use of `ProjectiveFEC` in the level-three argument.
-/

/-- Local projectivity of false elliptic curves over normal noetherian affine bases. -/
def LocProjNormal : Prop :=
  ∀ (X : Over Z30Base) (A : FEC X.left) (U : X.left.Opens), IsAffineOpen U →
    IsNormalNoeth Γ(X.left, U) →
      ∃ (N : ℕ) (i : (A.F.hom ⁻¹ᵁ U).toScheme ⟶ PNR Γ(X.left, U) N), IsClosedImmersion i

/-- The total space of the universal family has finite sets in affine opens. -/
theorem fsa_A1_of_locProjNormal (hE : EGAIV17_5_7) (hLP : LocProjNormal)
    (hB1 : BuzzardThm21Cor23V15') :
    Y3QuotientDescent.FiniteSetsInAffines (leafD hB1).A.F.left :=
  fsa_A1_of_locallyProjective hB1 (fun R _ => IsNormalNoeth R)
    (fun U hU => isNormalNoeth_of_B1 hE hB1 U hU)
    (fun U hU hN => hLP (leafD hB1).X (leafD hB1).A U hU hN)

/-- `Y3RouteA.Y3FullThreeRepZ30` with `EGAIV17_5_7` and `LocProjNormal` in place of
`ProjectiveFEC`. -/
theorem y3FullThreeRepZ30_of_printed_locProj (hL : XDV15.BuzzardXDV15Lit) (hM3 : MilneProp207 3)
    (hR : MilneRem84) (hBz : BuzzardLemma22Full5) (hMl : MilneThm125Pts)
    (hB4 : ZeroPreservingIsHomLN) (hE : EGAIV17_5_7) (hLP : LocProjNormal)
    (hM5 : MilneProp207 5) : Y3RouteA.Y3FullThreeRepZ30 :=
  y3FullThreeRepZ30_of_printed_xdv15_fsa hL hM3 hR hBz hMl hB4
    (fun hB1 => fsa_A1_of_locProjNormal hE hLP hB1) hM5

end Y3Buzzard.SmoothNormal
