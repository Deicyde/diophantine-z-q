# Based cusp classes on the modular curve

**Scoped stop.** Every fraction carrying a nonzero genus-partner weight represents cusp `0` of Γ₀(N). The Lean comparison therefore needs just the source chart limit at `0` for the weighted `hAJ`. The checked code builds the pointed Jacobian adapter, evaluates field-valued points by Abel–Jacobi, factors a based scheme morphism, and carries the source limit through that morphism and the chosen continuous uniformization.

All four files in `ZInQKernel/Contrib/OneProof/RC/J0Cusps/` passed serial `lake env lean -j1`. All 16 axiom audits list only `propext`, `Classical.choice`, and `Quot.sound`. No print was added. The concrete call on `X0Branch.model N` was not checked against the full model and Jacobian import closure. The formal rational point `X0Model.cusp N` already exists. Remaining geometry: identify the point at `0` and prove convergence of the (S)-translated chart in the complex scheme topology; identify the full algebraic cusp orbit assignment for the torsion print; realize the specific projective Weierstrass target as a group scheme with its compatible uniformization and specialize the map at `∞`. The exact source limit and target conditions are in [the report](../docs/research/rc-j0-cusps.md).

The at-scale factor uses the rational-scale witness and does not give an independent map. An independently supplied `α q_f` gives a based rational map by composition with Abel–Jacobi; the width-one tail comparison for that map remains open. The inherited Milne citation scope issue at tex 1784 is recorded in the report.

Result SHA: `ad2978976d106254eece41be09bda043255aebaf`. The final branch tip is the handoff commit containing this file.
