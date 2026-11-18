import ZInQKernel.Contrib.OneProof.PoleS12.Leaves

/-!
The three original definitions from `PoleS12/Leaves.lean`, with their names and bodies preserved
in a separate namespace. `AnalyticRankOne` and `sha` resolve to the original genuine definitions.
-/

namespace KolyvWeilOriginal

open ZInQ.Manuscript ZInQ.Manuscript.SelmerTwoPower

/-- Original modularity predicate, `PoleS12/Leaves.lean` L36–38. -/
def IsModular (E : WeierstrassCurve ℚ) : Prop :=
  ∃ (N : ℕ) (_ : 0 < N) (f : CuspForm (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) 2),
    ∀ n : ℕ, 0 < n → (UpperHalfPlane.qExpansion 1 f).coeff n = (E.LFunction n : ℂ)

/-- Original BCDT leaf, `PoleS12/Leaves.lean` L49–50. -/
def BCDTThmA : Prop :=
  ∀ E : WeierstrassCurve ℚ, E.IsElliptic → IsModular E

/-- Original Kolyvagin leaf, `PoleS12/Leaves.lean` L63–65. -/
def KolyvaginThm1 : Prop :=
  ∀ E : WeierstrassCurve ℚ, E.IsElliptic → IsModular E → AnalyticRankOne E →
    Module.rank ℤ E.toAffine.Point = 1 ∧ Finite (sha E)

example (E : WeierstrassCurve ℚ) : IsModular E = PoleS12.IsModular E := rfl
example : BCDTThmA = PoleS12.BCDTThmA := rfl
example : KolyvaginThm1 = PoleS12.KolyvaginThm1 := rfl

end KolyvWeilOriginal
