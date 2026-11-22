import ZInQKernel.Contrib.RLeaf.TateCuspGlue
import ZInQKernel.Contrib.RLeaf.TateCuspTorsion

/-!
# t40-tate: `TateCuspLaurent` is proved

`ZInQ.RLeaf.TateCuspLaurent` (task rleaf-elliptic, `X1RationalCusp.lean`), one of the two inputs
of `x1RationalCusp_of_igusa_tate : IgusaTransitive → TateCuspLaurent → X1RationalCusp`, holds:

* `TateCuspTorsion.tateLaurentTorsion : TateLaurentTorsion` — the Tate curve `E_{t^N}` over the
  complete normed field `ℚ((t))` has the `ℚ((t))`-rational point `t` of exact order `N`, and
  `j(E_{t^N})` is not a power series (Tau Ceti's Tate uniformization homomorphism, backported);
* `tateCuspLaurent_of_tateLaurentTorsion : TateLaurentTorsion → TateCuspLaurent` — `j ↦ j(W)`
  embeds `ℚ(j)` in `ℚ((t))`; over `\overline{ℚ((t))}` the curves `W` and `E_j` (same `j`) are
  related by a change of variables whose `x`-part `x ↦ u²x + r` has `u², r ∈ ℚ((t))`; and by
  counting torsion (leaf T36) the point lifts to a point `P` of exact order `N` of `E_j` over
  `\overline{ℚ(j)}` with `x(P) ↦ ℚ((t))`, which gives the embedding `ℚ(j)(x(P)) → ℚ((t))`.
-/

namespace ZInQ.RLeaf

/-- **`TateCuspLaurent`, proved.** -/
theorem tateCuspLaurent : TateCuspLaurent :=
  tateCuspLaurent_of_tateLaurentTorsion TateCuspTorsion.tateLaurentTorsion

/-- **T40 from Igusa transitivity alone.** -/
theorem x1RationalCusp_of_igusaTransitive (hI : IgusaTransitive) : X1Belyi.X1RationalCusp :=
  x1RationalCusp_of_igusa_tate hI tateCuspLaurent

/-- **T39 from Igusa transitivity alone.** -/
theorem x1ConstantField_of_igusaTransitive (hI : IgusaTransitive) : X1Belyi.X1ConstantField :=
  x1ConstantField_of_igusa_tate hI tateCuspLaurent

end ZInQ.RLeaf

#print axioms ZInQ.RLeaf.tateCuspLaurent
#print axioms ZInQ.RLeaf.x1RationalCusp_of_igusaTransitive
#print axioms ZInQ.RLeaf.x1ConstantField_of_igusaTransitive
