import ZInQKernel.Contrib.RLeaf.IgusaX0

/-! # curve-split: H-41 `ZInQ.RLeaf.X0Transitive` from Igusa's theorem

Row H-41 of `docs/research/frontier.md` (r3): `X0Transitive` (`ZInQKernel/Contrib/RLeaf/IgusaX0.lean`,
imported, not copied). It is a consequence of the published leaf `ZInQ.RLeaf.IgusaSL2X`
(`ZInQKernel/Contrib/RLeaf/IgusaSL2.lean`: Igusa 1959, the `SL₂(ℤ/N)` part of the Galois image on
`E_j[N]`, on `x`-coordinates), and of `ZInQ.RLeaf.IgusaGL2` (Igusa's theorem as usually printed).
The proofs below only compose results proved in `ZInQKernel/Contrib/RLeaf/`.
No `sorry`, no `axiom`. -/

namespace CurveSplit

open ZInQ.RLeaf

/-- **H-41 from the geometric part of Igusa's theorem.** -/
theorem x0Transitive_of_igusaSL2X (h : IgusaSL2X) : X0Transitive :=
  x0Transitive_of_igusaTransitive (igusaTransitive_of_igusaSL2X h)

/-- **H-41 from Igusa's theorem (`GL₂(ℤ/N)`, every basis).** -/
theorem x0Transitive_of_igusaGL2 (h : IgusaGL2) : X0Transitive :=
  x0Transitive_of_igusaSL2X (igusaSL2X_of_igusaGL2 h)

end CurveSplit

#print axioms CurveSplit.x0Transitive_of_igusaSL2X
#print axioms CurveSplit.x0Transitive_of_igusaGL2
