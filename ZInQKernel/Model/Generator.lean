import ZInQKernel.Model.Generator.InfiniteOrder
import ZInQKernel.Model.Generator.Certificate
import ZInQKernel.Model.Generator.GroupLaw
import ZInQKernel.Model.Generator.Membership
import ZInQKernel.Model.Generator.RawAddition

/-!
# The top level of the elliptic model

Blueprint chapter `model/`, top-level articles.

* `Generator/InfiniteOrder.lean`: `P₀` has infinite order, `ι` is injective.
* `Generator/Certificate.lean`: the generator certificate `2E(K₀) = ℤ P₀` (Proposition 3.1).
* `Generator/GroupLaw.lean`: chord, tangent and opposite points on `E` in coordinates; code coordinates.
* `Generator/Membership.lean`: the semantics of the membership template; accepted inputs are
  the codes `ι(n)`, each with a unique index.
* `Generator/RawAddition.lean`: the semantics of the raw addition template on codes of points
  and on the codes `ι(a)`, `ι(b)`.
-/
