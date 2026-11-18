import ZInQKernel.Contrib.OneProof.PoleS12.Leaves

/-!
Verbatim bodies of the old modularity and Kolyvagin Props. The shared analytic rank, Sha
and Mathlib objects are imported unchanged. The only adaptation is the namespace.
-/

namespace KolyvWeilFoldOriginal

open ZInQ.Manuscript ZInQ.Manuscript.SelmerTwoPower

/-- The modularity predicate in the old headline's BCDT and Kolyvagin inputs. -/
def IsModular (E : WeierstrassCurve ℚ) : Prop :=
  ∃ (N : ℕ) (_ : 0 < N) (f : CuspForm (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) 2),
    ∀ n : ℕ, 0 < n → (UpperHalfPlane.qExpansion 1 f).coeff n = (E.LFunction n : ℂ)

/-- The old BCDT Prop in the headline. -/
def BCDTThmA : Prop :=
  ∀ E : WeierstrassCurve ℚ, E.IsElliptic → IsModular E

/-- The old Kolyvagin Prop in the headline. -/
def KolyvaginThm1 : Prop :=
  ∀ E : WeierstrassCurve ℚ, E.IsElliptic → IsModular E → AnalyticRankOne E →
    Module.rank ℤ E.toAffine.Point = 1 ∧ Finite (sha E)

example (E : WeierstrassCurve ℚ) : IsModular E = PoleS12.IsModular E := rfl
example : BCDTThmA = PoleS12.BCDTThmA := rfl
example : KolyvaginThm1 = PoleS12.KolyvaginThm1 := rfl

end KolyvWeilFoldOriginal
