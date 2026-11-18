# Appendix F: line indexing complete

At every prime `p ∤ Nℓ₀`, for an order with the given `IsEichler` profile, `lineIndex` identifies `Option (ZMod p)` with the actual locally principal index-`p²` subideals of each chosen class representative. The two charts use the lines through `(1,t)` and `(0,1)`. The integral preimages retain individual kernels even when their target classes coincide.

The proof identifies `I/pI` with the regular right module over `R/pR ≃ M₂(𝔽_p)`. Matrix units give the column description. Away from `p` the neighbour has the same local span as the original ideal; at `p` its index-`p` column lattice has a basis matrix of determinant `p`, giving a local generator. `neighbours` supplies App F's class map, and `adjoint_good` proves `Nᵢⱼ wⱼ = Nⱼᵢ wᵢ` with `classWeight`.

All four Lean files in `ZInQKernel/Contrib/OneProof/RC/LineIndex/` compiled sequentially without warnings. The [66 axiom checks](../scratch/rc-line-index/axioms.md) report only `propext`, `Classical.choice`, and `Quot.sound`. No new prints and no manuscript error in the checked steps. See the [report](../docs/research/rc-line-index.md) for statements and the manuscript check.

Nothing remains in the ideal indexing scope. Level existence, the explicit order's local structure, the adelic and geometric identifications, and the theta frames and modular-parametrization identity are separate.

Proof and report SHA: `0ef523b56325ce46092d12df9b15d512202c158a`. The final handoff commit is the last commit touching this file.
