import ZInQKernel.HDecomp.A6.A6
import ZInQKernel.HDecomp.A6.Extend
import ZInQKernel.HDecomp.Assembly
import ZInQKernel.HDecomp.C10.C10
import ZInQKernel.HDecomp.C10.Trace
import ZInQKernel.HDecomp.Conductor.ArtinUpper
import ZInQKernel.HDecomp.Conductor.Breaks
import ZInQKernel.HDecomp.Conductor.D1Local
import ZInQKernel.HDecomp.Conductor.Dyadic
import ZInQKernel.HDecomp.Conductor.I6Base
import ZInQKernel.HDecomp.Conductor.Inflation
import ZInQKernel.HDecomp.Conductor.Level
import ZInQKernel.HDecomp.Conductor.SqrtChar
import ZInQKernel.HDecomp.Descent.B1Quat
import ZInQKernel.HDecomp.Descent.B2Assembly
import ZInQKernel.HDecomp.Descent.B2Glue
import ZInQKernel.HDecomp.Descent.B3Assembly
import ZInQKernel.HDecomp.Descent.Chi
import ZInQKernel.HDecomp.Descent.Cochain
import ZInQKernel.HDecomp.Descent.Constants
import ZInQKernel.HDecomp.Descent.ProjRep
import ZInQKernel.HDecomp.Objects
import ZInQKernel.HDecomp.Repo.A1Quaternion
import ZInQKernel.HDecomp.Repo.Numerics
import ZInQKernel.HDecomp.Repo.PRArith
import ZInQKernel.HDecomp.Repo.TorsionFree

/-! The glue of `docs/research/h-decomposition.md` (task hdec-adopt): every adopted module.
The literature leaves are hypotheses (`def … : Prop`); no `sorry`, no `axiom`. -/
