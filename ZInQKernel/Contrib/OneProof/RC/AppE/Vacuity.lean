import ZInQKernel.Contrib.OneProof.RC.AppE.Assembly

/-!
# Appendix E: `EvenPhaseData` does not pin down its retained set (a check on the tree's statement)

Lane RC11's structure `EvenPhaseData E L σ D₀` bounds `retained` only from above
(`retained_spec`) and asks `D₀ ∈ retained`. With `retained = {D₀}` and `z = 1` the phase fields
hold trivially (`z_sq` at `D₀` is `1 = ψ(D₀)ψ(D₀)⁻¹`, `rational` at `D₀` is `1 = 1 · 1`), so the
structure is inhabited from lane RC8's print `WaldspurgerNonvanishing` alone, with no Galois
comparison, no Ramsey model and no two-power order. `evenPhaseData_singleton` proves this.

Consequence: a consumer that needs (E.11) on the manuscript's whole filter ("For every retained
positive squarefree `D` in the original `S₀` filter", tex 7800–7801) must ask for it: the
deliverable of this lane, `evenPhaseData_of_prints` / `evenPhaseData_Ecurve`, records
`P.retained = {D | S0Filter S₀ D₀ D}`; the minimum `EvenPhaseData.minimum` is a minimum over
`P.retained` and is only meaningful with that equation.

PROVED.
-/

noncomputable section

namespace ZInQ.Manuscript.RC.AppE

open ZInQ.Manuscript ZInQ.Contrib.CloudB3RC53 ZInQ.Manuscript.RC.PrintsAnalytic UpperHalfPlane

/-- **`EvenPhaseData` with `retained = {D₀}`** (PROVED from lane RC8's PRINT
`WaldspurgerNonvanishing`, `PoleS12.BCDTThmA` and `HasseConvergence`): the structure alone does not
force the comparison on any `D ≠ D₀`. -/
theorem evenPhaseData_singleton (hWN : WaldspurgerNonvanishing) (hB : PoleS12.BCDTThmA)
    (hH : HasseConvergence) {E : WeierstrassCurve ℚ} [hE : E.IsElliptic]
    (L : ZInQ.Manuscript.RC.Even.CentralNormalization E) {σ : ℤ} (hσ : σ = 1 ∨ σ = -1)
    (S₀ : Finset ℕ) (hS₀ : ∀ p ∈ S₀, p.Prime) (h2 : 2 ∈ S₀)
    (hcond : ∀ (N : ℕ) (w : ℤ), RootNumberAt E N w → ∀ p : ℕ, p.Prime → p ∣ N → p ∈ S₀)
    {D₀ : ℕ} (hD₀ : 0 < D₀) (hsq₀ : Squarefree D₀) (hD₀S : ∀ p ∈ S₀, ¬ p ∣ D₀)
    (hL₀ : L.Lstar (σ * D₀) ≠ 0) :
    ∃ P : ZInQ.Manuscript.RC.Even.EvenPhaseData E L σ D₀, P.retained = {D₀} := by
  have hσD₀ := ZInQ.Manuscript.RC.Even.sigma_mul_ne_zero hσ hD₀
  have hA : AnalyticRank (qtwist E ((σ * D₀ : ℤ) : ℚ)) 0 :=
    (ZInQ.Manuscript.RC.GlueSweep.Even.lstar_ne_zero_iff_of_bcdt hB hH L hσD₀).mp hL₀
  obtain ⟨N, hN, hNS, ψ, η, hψη, g, hg, ha₀⟩ := hWN E hE σ hσ S₀ hS₀ h2 hcond D₀ hD₀ hsq₀ hD₀S hA
  have hself := S0Filter.spec hNS (S0Filter.self h2 hD₀ hsq₀ hD₀S)
  have hψ₀ : ψ D₀ ≠ 0 :=
    mulChar_ne_zero_of_isUnit ψ ((ZMod.isUnit_iff_coprime D₀ N).mpr hself.2.2.1)
  refine ⟨{ N := N, hN := hN, ψ := ψ, η := η, hψη := hψη, g := g, hg := hg, ha₀ := ha₀,
            retained := {D₀},
            retained_spec := fun D hD => by rw [Set.mem_singleton_iff.mp hD]; exact hself,
            D₀_mem := Set.mem_singleton D₀,
            z := fun _ => 1,
            z_root := fun _ _ => ⟨0, by simp⟩,
            z_sq := fun D hD => ?_,
            rational := fun D hD => ?_ }, rfl⟩
  · rw [Set.mem_singleton_iff.mp hD, mul_inv_cancel₀ hψ₀, one_pow]
  · refine ⟨1, ?_⟩
    rw [Set.mem_singleton_iff.mp hD, div_self ha₀]
    simp

end ZInQ.Manuscript.RC.AppE
