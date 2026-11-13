import ZInQKernel.Targets.H.T13
import ZInQKernel.Contrib.SkolemNoether.Basic

namespace ZInQ.Contrib.H

/-- Connect the complete ambient-central Skolem–Noether proof to the reserved
closed H target. No extra assumptions are introduced. Proof source: PR #42. -/
theorem T13_holds : ZInQ.Targets.H.T13 :=
  ZInQ.Contrib.SkolemNoether.t13

end ZInQ.Contrib.H
