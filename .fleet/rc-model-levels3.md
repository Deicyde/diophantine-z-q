# RC model levels 3 handoff

Under `2 ≤ N`, prime `ell ≥ 5` and `¬ ell ∣ N * N.totient`, `Pinned.Y0Level` gives the smooth affine model over the detector local integers. The exact-order cover has the named short grading and the geometric unit action preserves it. The model takes degree zero on the universal finite-group quotient over the whole short locus.

`Pinned.Y0LevelPoints` identifies its points over every algebraically closed detector field with `PairClasses k N`, including over the algebraic closure of the residue field. The coordinate algebra commutes with arbitrary base change, is flat and finitely presented, and is finite over the actual j-line. Its field fibres are normal of dimension at most one. `Pinned.Y0Level_smooth` gives the smooth structure morphism.

`PMWire.GoodRow` can use this model for `M`, the smoothness theorem for `smoothM`, and the inverse point equivalence for `point` after identifying the adelic labels. `GenericFibreComparison` remains uninstantiated. Its actual generic readings, the Néron extension, pointwise Hecke and Atkin–Lehner specialization, and the same-place comparisons are listed in the [research report](../docs/research/rc-model-levels3.md).

All 19 modules passed the final serialized Lake build. All 124 axiom checks contain only the permitted axioms. Verified source and report commit `e7528d5f4584856223aaf6275cd95e949066d26b`. Resolve the final handoff SHA with `git log -1 --format=%H -- .fleet/rc-model-levels3.md`.
