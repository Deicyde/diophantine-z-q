import ZInQKernel.Contrib.RC53Assist.HodgeLineBinding.LineComparison
import ZInQKernel.Contrib.RC53Assist.HodgeLineBinding.NonVacuity

/-!
# The invariant differential and the Hodge line of a group model: all modules

* `PointEvaluation`: evaluation of Kähler differentials at a rational point of a local algebra.
* `WeierstrassParameter`: `dx/(2y + a₁x + a₃) = u⁻¹ • d(-x/y)`; Kähler transport.
* `CurveExpansion`: the same identity on the function field of a Weierstrass curve.
* `ProjectiveParameter`: the local parameters `-x/y`, `-1/y` at `O`; stalk maps at points.
* `CurveOrigin`: the value at the origin of a differential regular there.
* `ModelOrigin`: `𝒪_{𝒢,ξ} ≅ 𝒪_{A_L,o}` from actual stalk maps; nonvanishing of wedges.
* `Binding`: the main theorem `hodgeEval_invariantDifferential` and its existence form.
* `Linearity`: compatibility with the constants; `L`-linearity; the regular line.
* `HodgeLine`: `hodgeSpace 1` is an `L`-line spanned by the wedge of the local parameter.
* `LineComparison`: the comparison isomorphism of the regular Kähler line with the Hodge line.
* `NonVacuity`: instances on `ℚ⟦X⟧`, on `y² = x³ - x` over `ℚ`, and over `ℚ`.
-/
