import ZInQKernel.RouteK.Assembly.Realize
import ZInQKernel.RouteK.Assembly.Data
import ZInQKernel.RouteK.Assembly.FirstCurve
import ZInQKernel.RouteK.Assembly.SecondCurve
import ZInQKernel.RouteK.Assembly.DL
import ZInQKernel.RouteK.Assembly.Points
import ZInQKernel.RouteK.Assembly.PoleCompleteness

/-!
# Route K: assembly of the descent lemma

Realization of configurations by actual primes (L5), the two curves of slot-k §2.5, DL, the
passage from points to `PoleSoluble` (L6), and pole completeness from the hypothesis CR₃
(`ZInQ.poleCompleteness_of_certifiedRank`).
-/
