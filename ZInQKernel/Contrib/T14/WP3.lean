import ZInQKernel.Contrib.T14.Main
import ZInQKernel.Contrib.BrauerT14T15.WP3Bridge

/-!
# The descent package's finite-places cochain form of T14, proved outright

`GlueDescent.B2Q.LeafHasse` (glue-descent's form of the Hasse principle, used by B2) follows from
t1415-tc's `leafHasse_of_kummerIndexBound` and `ZInQ.Contrib.T14.kummerIndexBound`.
-/

namespace ZInQ.Contrib.T14

open GlueDescent.B2Q

/-- **`GlueDescent.B2Q.LeafHasse`**, with no hypothesis. -/
theorem leafHasse : LeafHasse :=
  ZInQ.Contrib.BrauerT14T15.leafHasse_of_kummerIndexBound kummerIndexBound

end ZInQ.Contrib.T14
