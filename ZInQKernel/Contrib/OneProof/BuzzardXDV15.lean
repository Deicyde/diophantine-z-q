import ZInQKernel.Contrib.OneProof.BuzzardXDV15.Bridge
import ZInQKernel.Contrib.OneProof.BuzzardXDV15.LocSurj
import ZInQKernel.Contrib.OneProof.BuzzardXDV15.Leaf
import ZInQKernel.Contrib.OneProof.SerreRigidityZ30

set_option autoImplicit false
noncomputable section
namespace Y3Buzzard

open XDV15

/-!
# The level-`V₁(5)` moduli input from Buzzard's own definitions

`BuzzardThm21Cor23V15'` used a concrete form of the `V₁(5)`-structures. `XDV15.BuzzardXDV15Lit`
states Buzzard's Thm 2.1 and Cor. 2.3 at `U = V₁(5)` with his own level structures: full level-5
structures as `O`-linear isomorphisms `(O/5O)_T ≅ A[5]_T` (Def. 1.1), their orbits under `V₁(5)`
(with `κ` fixed by `kappa5`), and the étale sheafification over `S`-schemes (Def. 1.2). The
invariant `α ↦ α(diag(0,1))` of Buzzard's proof of Lemma 2.2 identifies these with the concrete
form, from Milne's Prop. 20.7 and Remark 8.4 at `n = 5`.
-/

/-- `BuzzardThm21Cor23V15'` from Buzzard's literal statement, with Milne's Prop. 20.7 and
Remark 8.4 at `n = 5`. -/
theorem b1Prime_of_literal (hL : BuzzardXDV15Lit) (hM5 : MilneProp207 5) (hC5 : GeomCard5) :
    BuzzardThm21Cor23V15' :=
  b1_of_literal (fun S A => invOrb_locallySurjective hM5 hC5 S A) (buzzardXDV15_of_lit hM5 hL)
    hM5 hC5

/-- `Y3RouteA.Y3FullThreeRepZ30` from eight printed inputs, with Buzzard's literal Thm 2.1 and
Cor. 2.3 at `V₁(5)` in place of `BuzzardThm21Cor23V15'`. -/
theorem y3FullThreeRepZ30_of_printed_xdv15 (hL : BuzzardXDV15Lit) (hM3 : MilneProp207 3)
    (hR : MilneRem84) (hBz : BuzzardLemma22Full5) (hMl : MilneThm125Pts)
    (hB4 : ZeroPreservingIsHomLN) (hB6 : ProjectiveFEC) (hM5 : MilneProp207 5) :
    Y3RouteA.Y3FullThreeRepZ30 :=
  y3FullThreeRepZ30_of_printed_buzzard22 (b1Prime_of_literal hL hM5 (geomCard5_of_rem84 hR)) hM3
    hR hBz hMl hB4 hB6 hM5

end Y3Buzzard
