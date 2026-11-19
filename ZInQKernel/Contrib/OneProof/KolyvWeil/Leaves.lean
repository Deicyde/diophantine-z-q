import ZInQKernel.Contrib.OneProof.KolyvWeil.Parametrization
import ZInQKernel.Contrib.OneProof.SelmerTwoPower

/-!
# The two inputs used in Lemma 5.5

`lem:forward-rank`, tex L1086–1109. The previous AI reading of the cited versions is recorded
at https://github.com/Deicyde/diophantine-z-q/issues/83#issuecomment-6962416523.
-/

namespace ZInQ.Manuscript.KolyvWeil

open SelmerTwoPower (sha)

/-- **Consequence of BCDT Theorem A** (CITED at `lem:forward-rank`, tex L1092; GLUE).
Breuil–Conrad–Diamond–Taylor, *On the modularity of elliptic curves over ℚ: wild 3-adic exercises*,
cited author manuscript, Theorem A (p. 1) and Introduction condition (6) (p. 3); published in
JAMS 14 (2001), 843–939. Condition (6) gives a ℚ-morphism from `X₁(N_E)`. The weak Weil
parametrization here is from `X₀(N_E)`; it uses trivial nebentypus, Shimura's `J₀(N_E)` quotient
and Faltings' isogeny theorem, as in tex L1779–1784 (Milne MF v1.31, Theorem 11.19 and Remark 11.18). -/
def BCDTThmA6 : Prop :=
  ∀ (E : WeierstrassCurve ℚ) [E.IsElliptic], HasWeakWeilParametrization E

/-- Analytic rank r, using the same entire continuation of Mathlib's L-series as
`Manuscript.AnalyticRankOne` (tex `lem:forward-rank`, L1087). -/
def AnalyticRank (E : WeierstrassCurve ℚ) (r : ℕ) : Prop :=
  ∃ F : ℂ → ℂ, Differentiable ℂ F ∧ (∀ s : ℂ, 3 / 2 < s.re → F s = E.LSeries s) ∧
    analyticOrderAt F 1 = r

/-- **Kolyvagin, Theorem 1** (printed form, CITED at `lem:forward-rank`, tex L1093).
*On the Mordell–Weil group and the
Shafarevich–Tate group of modular elliptic curves*, MPIM preprint MPI/90-69 (1990), p. 4.
The hypothesis on p. 3 is a weak Weil parametrization at the conductor. If the analytic rank
is zero or one then the Mordell–Weil rank equals it and Ш(E/ℚ) is finite. The cited preprint
is unrefereed; the LEAF rating is pending the owner's ruling. -/
def KolyvaginThm1Print : Prop :=
  ∀ (E : WeierstrassCurve ℚ) [E.IsElliptic], HasWeakWeilParametrization E →
    ∀ r : ℕ, r ≤ 1 → AnalyticRank E r → Module.rank ℤ E.toAffine.Point = r ∧ Finite (sha E)

/-- The rank-one and finiteness conclusions used at `lem:forward-rank`, from the weak Weil
parametrization followed by Kolyvagin. -/
theorem rankOne_and_finiteSha_of_prints (hB : BCDTThmA6) (hK : KolyvaginThm1Print)
    (E : WeierstrassCurve ℚ) [E.IsElliptic] (hA : AnalyticRankOne E) :
    Module.rank ℤ E.toAffine.Point = 1 ∧ Finite (sha E) := by
  have hA' : AnalyticRank E 1 := by
    simpa only [AnalyticRank, AnalyticRankOne, Nat.cast_one] using hA
  simpa only [Nat.cast_one] using hK E (hB E) 1 le_rfl hA'

end ZInQ.Manuscript.KolyvWeil
