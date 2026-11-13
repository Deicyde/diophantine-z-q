import ZInQKernel.Targets.H.T19
import ZInQKernel.Contrib.BrauerNesbitt.Matrix

namespace ZInQ.Contrib.H

/-- Connect the complete arbitrary-group characteristic-zero trace/complement
proof to the reserved closed H target. No additional provider binders occur. -/
theorem T19_holds : ZInQ.Targets.H.T19 :=
  ZInQ.Contrib.BrauerNesbitt.t19

end ZInQ.Contrib.H
