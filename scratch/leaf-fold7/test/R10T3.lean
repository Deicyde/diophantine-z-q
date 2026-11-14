import ZInQKernel.OneProof.H.TailO
import ZInQKernel.OneProof.H.TailT

namespace HDec.HSyn.HodgeT
open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj

def toG9AbVar {F : Type} [Field F] (A : PkgI4.I3.AbVar F) : ZInQ.Contrib.G9.PkgI4.I3.AbVar F :=
  { X := A.X, grp := A.grp, proper := A.proper, smooth := A.smooth, geomInt := A.geomInt }

set_option maxHeartbeats 400000 in
theorem galT_eq (p : ℕ) [Fact p.Prime] {F : Type} [Field F] (A : PkgI4.I3.AbVar F) (σ : Field.absoluteGaloisGroup F)
    (x : A.T p) (n : ℕ) :
    (((toG9AbVar A).galT (ℓ := p) σ x).1 n : Additive (A.Pt (AlgebraicClosure F))) = (A.galT (ℓ := p) σ x).1 n := rfl


set_option maxHeartbeats 400000 in
theorem galT_eq' (p : ℕ) [Fact p.Prime] {F : Type} [Field F] (A : PkgI4.I3.AbVar F) (σ : Field.absoluteGaloisGroup F) :
    ((toG9AbVar A).galT (ℓ := p) σ : A.T p →ₗ[ℤ_[p]] A.T p) = A.galT (ℓ := p) σ := by
  apply LinearMap.ext; intro x; apply Subtype.ext; funext n; exact galT_eq p A σ x n

set_option maxHeartbeats 400000 in
theorem galRep_eq (p : ℕ) [Fact p.Prime] {F : Type} [Field F] (A : PkgI4.I3.AbVar F) :
    ((toG9AbVar A).galRep p : Representation ℚ_[p] (Field.absoluteGaloisGroup F) (A.V p)) = A.galRep p := by
  apply MonoidHom.ext; intro σ
  change ((toG9AbVar A).galT (ℓ := p) σ).baseChange ℚ_[p] = (A.galT (ℓ := p) σ).baseChange ℚ_[p]
  rw [galT_eq' p A σ]

end HDec.HSyn.HodgeT
