module

public import Mathlib.Topology.Connected.TotallyDisconnected
import Mathlib.Tactic.CrossRefAttribute

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3

/-!
# The space of connected components

The space `π₀(X) = ConnectedComponents X` is totally disconnected. Every continuous map from
`X` to a totally disconnected space factors continuously through `π₀(X)`.

Both parts are registered directly from Mathlib, together with the continuity and
factorization identities for `Continuous.connectedComponentsLift`.

## References

* [Stacks Project, Tag 08ZL](https://stacks.math.columbia.edu/tag/08ZL)
-/

@[expose] public section

