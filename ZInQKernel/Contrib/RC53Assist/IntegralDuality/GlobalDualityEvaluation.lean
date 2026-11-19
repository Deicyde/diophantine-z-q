import ZInQKernel.Contrib.CloudB3RC53.SelmerDuality.Duality

/-!
# Evaluation of the actual global cup adjoint

The global adjoint restricts the Selmer cup formula to a global source and
a compactly supported second source. Both local-condition entries are zero.
The formula therefore depends only on the genuine global and local cups
and the coefficient restriction, not on the chosen local condition or its
isotropy homotopy. This is an identity of the fixed map, not a duality input.
-/

noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace ZInQ.Contrib.RC53Assist.IntegralDuality

open CategoryTheory
open ZInQ.Contrib.CloudB3RC53.PairedFunctional
open ZInQ.Contrib.CloudB3RC53.SelmerDuality

universe u

variable {R : Type u} [CommRing R] {D D' : SelData R}

/-- The fixed global adjoint evaluates by the global cup and the signed local compact cup. -/
theorem globalDualityMap_evaluation (Q : SelPairData D D')
    (tr : (coneCx Q.resE).X 3 →ₗ[R] R)
    (htr : ∀ z, tr ((coneCx Q.resE).d 2 3 rfl z) = 0)
    (i : ℤ) (a : D.G.X i) (b : D'.G.X (3 - i)) (y : D'.L.X (3 - i - 1)) :
    asDual ((globalDualityMap Q tr htr).f i i rfl a)
        ((b, y) : (compactCx D').X (3 - i)) =
      tr ((Q.cupG.P i (3 - i) 3 (by omega) a b,
        sgn i • Q.cupL.P i (3 - i - 1) (3 - 1) (by omega) (D.res.f i i rfl a) y) :
          (coneCx Q.resE).X 3) := by
  change tr (selCupFun Q i (3 - i) 3 (by omega)
      ((a, 0, 0) : selT D i) ((b, 0, y) : selT D' (3 - i))) = _
  simp only [selCupFun, map_zero, LinearMap.zero_apply, zero_add, add_zero]

end ZInQ.Contrib.RC53Assist.IntegralDuality
