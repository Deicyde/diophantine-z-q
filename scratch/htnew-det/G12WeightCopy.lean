import ZInQKernel.Contrib.OneProof.HTNewDet

/-! htnew-det: verbatim copy of the consumer `HDec.G0Galois.G12Weight` (TailA l.2059), checked `rfl`
against the chain's constant, and the ZInQ.Contrib.HTNewDet results restated against the copy. -/

namespace HDec
namespace G0Galois
namespace HTNewDetCopy
open _root_.PkgI4 (GaloisRep GaloisChar)

/-- Verbatim copy of `G12Weight` (TailA l.2059). -/
def G12WeightCopy : Prop :=
  HSyn.EigenformRepExists → PkgI4.EigenformHT → HSyn.DeligneSerreConseq → HSyn.FrobeniusDense →
  HSyn.BrauerNesbitt →
  ∀ (r : GaloisRep 5 2) (N : ℕ) (k : ℤ) (χ : DirichletCharacter ℂ N) (g : PkgI4.CF N k)
    (ψ : GaloisChar 5) (ιC : PkgI4.Qbar →ₐ[ℚ] ℂ) (ιL : PkgI4.Qbar →ₐ[ℚ] PadicAlgCl 5)
    (S : Finset ℕ),
    0 < N → 1 ≤ k → PkgI4.IsNormalizedEigenform g χ → r.IsIrreducible →
    PkgI4.GaloisRep.HasHTWeightsAtSelf (ρ := r) 5 {0, -1} → r.AttachedUpToTwist ψ ιC ιL g S →
    ∃ n : ℤ, ({n, n + 1 - k} : Multiset ℤ) = {0, -1}

theorem copy_eq : G12WeightCopy = G12Weight := rfl

theorem copy_of_noHighWeight (hSen : SenTwist) (hFI : FiniteImageHT)
    (hNo : ZInQ.Contrib.HTNewDet.NoHighWeightTwist5) : G12WeightCopy :=
  ZInQ.Contrib.HTNewDet.g12Weight_of_noHighWeight hSen hFI hNo

end HTNewDetCopy
end G0Galois
end HDec

#print axioms HDec.G0Galois.HTNewDetCopy.copy_of_noHighWeight
