import ZInQKernel.Contrib.BrauerT14T15.Main
import ZInQKernel.HDecomp.Descent.WP3

/-!
# The descent package's forms of T14/T15, discharged

`ZInQKernel/HDecomp/Descent/WP3.lean` derives glue-descent's `LeafLocalTwo` from T15 and
`LeafHasse` from T14.  With T15 proved (`localH2CardC`) and T14 reduced to `KummerIndexBound`:

* `leafLocalTwo`: `LeafLocalTwo`, proved outright;
* `leafHasse_of_kummerIndexBound`: `LeafHasse` from the Kummer case of the second inequality.
-/

namespace ZInQ.Contrib.BrauerT14T15

open GlueDescent.B2 GlueDescent.B2Q

/-- **glue-descent's `LeafLocalTwo`, proved** (from leaf T15, now a theorem). -/
theorem leafLocalTwo : LeafLocalTwo :=
  GlueWP3.leafLocalTwo_of_T15 localH2CardC

/-- **glue-descent's `LeafHasse` from `KummerIndexBound`.** -/
theorem leafHasse_of_kummerIndexBound (h : KummerIndexBound) : LeafHasse :=
  GlueWP3.leafHasse_of_T14 (brauerHasse2C_of_kummerIndexBound h)
    (brauerReciprocity2C_of_kummerIndexBound h)

end ZInQ.Contrib.BrauerT14T15
