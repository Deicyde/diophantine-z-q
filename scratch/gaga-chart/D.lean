import ZInQKernel.Contrib.OneProof.GAGAChart

open scoped Manifold ContDiff Topology
open Set Filter CategoryTheory AlgebraicGeometry Limits MonObj

noncomputable section

namespace GAGAAn

open UnifPrinted UnifTopology BPAnalytic BPAnalytic.Uniformization
open PkgI3 (AbVar)

/-- GAGA in chart form for *some* `IsAnStr` charts on `A(ℂ)` and `B(ℂ)` (for instance those of `A^an`,
`B^an`). -/
def GAGAChartSome : Prop :=
  ∀ (A B : AbVar ℂ),
    letI := analyticTopology A.X
    letI := analyticTopology B.X
    ∃ (n m : ℕ) (_ : ChartedSpace (Fin n → ℂ) (CPt A.X)) (_ : ChartedSpace (Fin m → ℂ) (CPt B.X)),
      IsAnStr A.X n ∧ IsAnStr B.X m ∧
      ∀ F : CPt A.X → CPt B.X, ContMDiff 𝓘(ℂ, Fin n → ℂ) 𝓘(ℂ, Fin m → ℂ) ω F →
        ∃ f : A.X ⟶ B.X, ∀ P, F P = P ≫ f

/-- **The quantifier over charts in `GAGAChart` adds nothing (proved).** GAGA for one choice of
`IsAnStr` charts gives it for every choice (`contMDiff_id_of_isAnStr`). -/
theorem gagaChart_of_some (h : GAGAChartSome) : GAGAChart := by
  intro A B n m cA cB hA hB F hF
  let tA := analyticTopology A.X
  let tB := analyticTopology B.X
  obtain ⟨n₀, m₀, cA₀, cB₀, hA₀, hB₀, hG⟩ := h A B
  have iA := @contMDiff_id_of_isAnStr A.X n₀ n tA (SGA1Etale.isOpen_ptIn_an) cA₀ cA hA₀ hA
  have iB := @contMDiff_id_of_isAnStr B.X m m₀ tB (SGA1Etale.isOpen_ptIn_an) cB cB₀ hB hB₀
  have inner := @ContMDiff.comp ℂ _ (Fin n₀ → ℂ) _ _ (Fin n₀ → ℂ) _ 𝓘(ℂ, Fin n₀ → ℂ) (CPt A.X) tA
    (Fin n → ℂ) _ _ (Fin n → ℂ) _ 𝓘(ℂ, Fin n → ℂ) (CPt A.X) tA
    (Fin m → ℂ) _ _ (Fin m → ℂ) _ 𝓘(ℂ, Fin m → ℂ) (CPt B.X) tB cA₀ cA cB id ω F hF iA
  have hF₀ := @ContMDiff.comp ℂ _ (Fin n₀ → ℂ) _ _ (Fin n₀ → ℂ) _ 𝓘(ℂ, Fin n₀ → ℂ) (CPt A.X) tA
    (Fin m → ℂ) _ _ (Fin m → ℂ) _ 𝓘(ℂ, Fin m → ℂ) (CPt B.X) tB
    (Fin m₀ → ℂ) _ _ (Fin m₀ → ℂ) _ 𝓘(ℂ, Fin m₀ → ℂ) (CPt B.X) tB cA₀ cB cB₀ (F ∘ id) ω id iB inner
  exact hG F hF₀

#print axioms gagaChart_of_some

end GAGAAn
