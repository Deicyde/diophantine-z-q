import ZInQKernel.Contrib.RLeaf.X1RationalCusp

/-!
# t40-tate: `TateCuspLaurent` from a torsion point on an elliptic curve over `ℚ((t))`

`TateCuspLaurent` (task rleaf-elliptic, `X1RationalCusp.lean`) asks, for each `N > 0`, for a
point `P` of exact order `N` on `E_j / \overline{ℚ(j)}` and a `ℚ`-embedding
`ℚ(j)(x(P)) → ℚ((t))` under which `j` is not a power series.

This file isolates the analytic input as `TateLaurentTorsion`: for every `N ≥ 2` some elliptic
curve over `ℚ((t))`, with `j`-invariant not a power series, has a `ℚ((t))`-rational point of exact
order `N` (the Tate curve `E_q`, `q = t^N`, with the point `u = t` of Tate's parametrization
`ℚ((t))^× / q^ℤ ≅ E_q(ℚ((t)))`).
-/

namespace ZInQ.RLeaf

open Classical in
/-- **A torsion point of exact order `N` over `ℚ((t))` on a curve with non-integral `j`.**
For every `N ≥ 2` there is an elliptic curve `W` over `ℚ((t))` whose `j`-invariant is not a
power series in `t`, with a `ℚ((t))`-rational point of exact order `N`.

Source: the Tate curve `E_q` over `ℚ((t))` with `q = t^N`; Tate's parametrization
`ℚ((t))^× / q^ℤ ≅ E_q(ℚ((t)))` is a group isomorphism (Tate 1995; Silverman, *Advanced topics in
the arithmetic of elliptic curves*, Thm. V.3.1, UNVERIFIED number), so the class of `t` has exact
order `N`, and `j(E_q) = 1/q + 744 + ⋯` (loc. cit. V.3.1(c)). Published theorem. -/
def TateLaurentTorsion : Prop :=
  ∀ N : ℕ, 2 ≤ N → ∃ (W : WeierstrassCurve (LaurentSeries ℚ)) (_ : W.IsElliptic)
    (P : W.toAffine.Point), addOrderOf P = N ∧
      W.j ∉ Set.range (HahnSeries.ofPowerSeries ℤ ℚ)

end ZInQ.RLeaf
