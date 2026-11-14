import ZInQKernel.OneProof.H.TailO
import ZInQKernel.OneProof.H.TailT

namespace HDec.HSyn.HodgeT

def toG9AbVar {F : Type} [Field F] (A : PkgI4.I3.AbVar F) : ZInQ.Contrib.G9.PkgI4.I3.AbVar F :=
  { X := A.X, grp := A.grp, proper := A.proper, smooth := A.smooth, geomInt := A.geomInt }

set_option maxHeartbeats 200000 in
example {F : Type} [Field F] (A : PkgI4.I3.AbVar F) : (toG9AbVar A).dim = A.dim := rfl

set_option maxHeartbeats 200000 in
example (p : ℕ) [Fact p.Prime] {F : Type} [Field F] (A : PkgI4.I3.AbVar F) :
    (toG9AbVar A).T p = A.T p := rfl

set_option maxHeartbeats 200000 in
example (p : ℕ) [Fact p.Prime] {F : Type} [Field F] (A : PkgI4.I3.AbVar F) :
    (toG9AbVar A).V p = A.V p := rfl


set_option maxHeartbeats 400000 in
example (p : ℕ) [Fact p.Prime] (F : Type) [Field F] [Algebra ℚ_[p] F] [FiniteDimensional ℚ_[p] F]
    (A : PkgI4.I3.AbVar F) (w : ℤ) :
    ZInQ.Contrib.G9.PkgI4.htMultOver p ((toG9AbVar A).galRep p) w = PkgI4.htMultOver p (A.galRep p) w := rfl

set_option maxHeartbeats 400000 in
example (p : ℕ) [Fact p.Prime] (F : Type) [Field F] [Algebra ℚ_[p] F] [FiniteDimensional ℚ_[p] F]
    (A : PkgI4.I3.AbVar F) :
    ZInQ.Contrib.G9.PkgI4.IsDeRhamOver p ((toG9AbVar A).galRep p) ↔ PkgI4.IsDeRhamOver p (A.galRep p) := Iff.rfl

end HDec.HSyn.HodgeT
