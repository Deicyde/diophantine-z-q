/-
Bridge from the project proof of Brauer–Nesbitt (characteristic zero) to the two existing
baseline leaf names that state the representation form verbatim:

* `PkgI6.BrauerNesbittChar0` (`ZInQKernel/HDecomp/Conductor/I6Base.lean`);
* `GlueC10.BrauerNesbittChar0` (`ZInQKernel/HDecomp/C10/C10.lean`), the hypothesis consumed by
  `GlueC10.iso_of_trace_eq_frob_finite`, `iso_of_trace_eq_on_frob`, `iso_three_of_five` and `c10`.

Both definitions are imported unchanged from main `a5937595cde3e3db00975b81e5171cdef92c801a`;
each theorem below closes the definition by unfolding it to the verbatim body proved in
`ZInQKernel.Contrib.BrauerNesbitt.Representation`. This module adds no hypothesis to either leaf
and does not touch the C10 consumers, which still also take `ChebotarevExists`.
-/
import ZInQKernel.Contrib.BrauerNesbitt.Representation
import ZInQKernel.HDecomp.Conductor.I6Base
import ZInQKernel.HDecomp.C10.C10

namespace ZInQ.Contrib.BrauerNesbitt

/-- The baseline leaf `PkgI6.BrauerNesbittChar0`, proved. -/
theorem pkgI6_brauerNesbittChar0 : PkgI6.BrauerNesbittChar0 :=
  brauerNesbittChar0

/-- The verbatim copy `GlueC10.BrauerNesbittChar0` used by the C10 glue, proved. -/
theorem glueC10_brauerNesbittChar0 : GlueC10.BrauerNesbittChar0 :=
  brauerNesbittChar0

end ZInQ.Contrib.BrauerNesbitt
