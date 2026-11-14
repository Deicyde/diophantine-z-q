import ZInQKernel.OneProof.H.TailO
import ZInQKernel.OneProof.H.TailT

namespace HDec.HSyn.HodgeT

def toG9AbVar {F : Type} [Field F] (A : PkgI4.I3.AbVar F) : ZInQ.Contrib.G9.PkgI4.I3.AbVar F :=
  { X := A.X, grp := A.grp, proper := A.proper, smooth := A.smooth, geomInt := A.geomInt }

set_option maxHeartbeats 400000 in
example (p : ℕ) [Fact p.Prime] (F : Type) [Field F] [Algebra ℚ_[p] F] [FiniteDimensional ℚ_[p] F]
    {V : Type} [AddCommGroup V] [Module ℚ_[p] V] (ρ : Representation ℚ_[p] (Field.absoluteGaloisGroup F) V) :
    ZInQ.Contrib.G9.PkgI4.IsDeRhamOver p ρ ↔ PkgI4.IsDeRhamOver p ρ := Iff.rfl

set_option maxHeartbeats 400000 in
example (p : ℕ) [Fact p.Prime] (F : Type) [Field F] [Algebra ℚ_[p] F] [FiniteDimensional ℚ_[p] F]
    {V : Type} [AddCommGroup V] [Module ℚ_[p] V] (ρ : Representation ℚ_[p] (Field.absoluteGaloisGroup F) V) (w : ℤ) :
    ZInQ.Contrib.G9.PkgI4.htMultOver p ρ w = PkgI4.htMultOver p ρ w := rfl

set_option maxHeartbeats 400000 in
example (p : ℕ) [Fact p.Prime] {F : Type} [Field F] (A : PkgI4.I3.AbVar F) :
    (inferInstance : Module ℚ_[p] ((toG9AbVar A).V p)) = (inferInstance : Module ℚ_[p] (A.V p)) := rfl


set_option maxHeartbeats 400000 in
example (p : ℕ) [Fact p.Prime] {F : Type} [Field F] (A : PkgI4.I3.AbVar F) :
    ((toG9AbVar A).galRep p : Representation ℚ_[p] (Field.absoluteGaloisGroup F) (A.V p)) = A.galRep p := rfl

set_option maxHeartbeats 400000 in
example (p : ℕ) [Fact p.Prime] {F : Type} [Field F] (A : PkgI4.I3.AbVar F) σ :
    ((toG9AbVar A).galT (ℓ := p) σ : A.T p →ₗ[ℤ_[p]] A.T p) = A.galT σ := rfl

end HDec.HSyn.HodgeT
