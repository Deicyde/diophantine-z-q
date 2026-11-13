import ZInQKernel.Contrib.RLeaf.TateCusp
import ZInQKernel.Contrib.RLeaf.IgusaLocal

/-!
# T40 (and T39): what remains after t40-tate and t40-igusa

Leaf T40 (`X1Belyi.X1RationalCusp`) was reduced by task rleaf-elliptic to `IgusaTransitive` and
`TateCuspLaurent` (`x1RationalCusp_of_igusa_tate`, ZInQKernel/Contrib/RLeaf/X1RationalCusp.lean).

* `TateCuspLaurent` is proved by task t40-tate (`ZInQ.RLeaf.tateCuspLaurent`,
  ZInQKernel/Contrib/RLeaf/TateCusp.lean), which gives
  `x1RationalCusp_of_igusaTransitive : IgusaTransitive → X1RationalCusp`.
* `IgusaTransitive` is equivalent to `X0Transitive ∧ TateMuN` (`igusaTransitive_iff`,
  ZInQKernel/Contrib/RLeaf/IgusaX0.lean, task t40-igusa); `TateMuN` follows from its local form
  over `\overline{ℚ((1/j))}` (`tateMuN_of_local`, IgusaLocal.lean) or from per-level local forms
  (`tateMuN_of_at`); and `IgusaTransitive` also follows from Igusa's theorem in its usual form
  (`igusaTransitive_of_igusaGL2`, IgusaSL2.lean).

This file records the resulting reductions of T40 and T39.
-/

namespace ZInQ.RLeaf

/-- **T40 from `X₀(N)`-transitivity and the cusp `μ_N`.** -/
theorem x1RationalCusp_of_x0_tateMuN (h0 : X0Transitive) (hT : TateMuN) :
    X1Belyi.X1RationalCusp :=
  x1RationalCusp_of_igusaTransitive (igusaTransitive_of_x0_tateMuN h0 hT)

/-- **T39 from `X₀(N)`-transitivity and the cusp `μ_N`.** -/
theorem x1ConstantField_of_x0_tateMuN (h0 : X0Transitive) (hT : TateMuN) :
    X1Belyi.X1ConstantField :=
  x1ConstantField_of_x1RationalCusp (x1RationalCusp_of_x0_tateMuN h0 hT)

/-- **T40 from `X₀(N)`-transitivity and the Tate curve at `j = ∞` (local form).** -/
theorem x1RationalCusp_of_x0_tateMuNLocal (h0 : X0Transitive) (hT : TateMuNLocal) :
    X1Belyi.X1RationalCusp :=
  x1RationalCusp_of_x0_tateMuN h0 (tateMuN_of_local hT)

/-- **T40 from Igusa's theorem** (`GL₂(ℤ/N)` image, Igusa 1959). -/
theorem x1RationalCusp_of_igusaGL2 (h : IgusaGL2) : X1Belyi.X1RationalCusp :=
  x1RationalCusp_of_igusaTransitive (igusaTransitive_of_igusaGL2 h)

/-- **T40 from the `SL₂` part of Igusa's theorem on `x`-coordinates** (Shimura 1971, Thm 6.6). -/
theorem x1RationalCusp_of_igusaSL2X (h : IgusaSL2X) : X1Belyi.X1RationalCusp :=
  x1RationalCusp_of_igusaTransitive (igusaTransitive_of_igusaSL2X h)

/-- **T39 from the `SL₂` part of Igusa's theorem on `x`-coordinates.** -/
theorem x1ConstantField_of_igusaSL2X (h : IgusaSL2X) : X1Belyi.X1ConstantField :=
  x1ConstantField_of_x1RationalCusp (x1RationalCusp_of_igusaSL2X h)

end ZInQ.RLeaf

#print axioms ZInQ.RLeaf.x1RationalCusp_of_x0_tateMuN
#print axioms ZInQ.RLeaf.x1ConstantField_of_x0_tateMuN
#print axioms ZInQ.RLeaf.x1RationalCusp_of_x0_tateMuNLocal
#print axioms ZInQ.RLeaf.x1RationalCusp_of_igusaGL2
#print axioms ZInQ.RLeaf.x1RationalCusp_of_igusaSL2X
#print axioms ZInQ.RLeaf.x1ConstantField_of_igusaSL2X
