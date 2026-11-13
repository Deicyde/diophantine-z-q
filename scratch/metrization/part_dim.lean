
/-! ## metrization (2026-11-13): `MetrizationDimUnique`, proved -/

namespace ZInQ.Metrization

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open NumberField DefFaltings

/-- A discrete `ℤ`-submodule of `ℂ^g`, `g ≥ 1`, is not all of `ℂ^g`. -/
theorem exists_not_mem_of_discrete {g : ℕ} (hg : 0 < g) (Λ : Submodule ℤ (Fin g → ℂ))
    [DiscreteTopology Λ] : ∃ z, z ∉ Λ := by
  by_contra! hall
  let e : Fin g → ℂ := Pi.single ⟨0, hg⟩ 1
  let f : ℝ → Λ := fun t => ⟨(t : ℂ) • e, hall _⟩
  have hf : Continuous f :=
    Continuous.subtype_mk (Complex.continuous_ofReal.smul continuous_const) _
  have h1 := PreconnectedSpace.constant inferInstance hf (x := 0) (y := 1)
  have h2 := congrArg (fun x : Λ => (x : Fin g → ℂ) ⟨0, hg⟩) h1
  simp [f, e] at h2

variable {K : Type} [Field K] {A : AbVar K} {L : Type} [Field L] [NumberField L] [Algebra K L]

/-- A metrization of dimension `g ≥ 1` has a nontrivial complex point at every `τ`. -/
theorem metrized_exists_pts_ne_one {g : ℕ} (hg : 0 < g) (M : MetrizedModel A L g)
    (τ : L →+* ℂ) : ∃ p : M.model.Pts τ, p ≠ 1 := by
  obtain ⟨Φ, hΦ, -⟩ := M.arch τ
  haveI := M.hodge.periods_discrete τ
  obtain ⟨z, hz⟩ := exists_not_mem_of_discrete hg (M.hodge.periods τ)
  exact ⟨Φ z, fun h => hz ((hΦ.2.1 z).mp h)⟩

/-- A metrization of dimension `0` forces `𝒢(ℂ)_τ` to be trivial (`Φ : ℂ⁰ → 𝒢(ℂ)_τ` is onto). -/
theorem metrized_pts_subsingleton (M : MetrizedModel A L 0) (τ : L →+* ℂ) :
    Subsingleton (M.model.Pts τ) := by
  obtain ⟨Φ, hΦ, -⟩ := M.arch τ
  refine ⟨fun p q => ?_⟩
  obtain ⟨z, rfl⟩ := hΦ.2.2.1 p
  obtain ⟨w, rfl⟩ := hΦ.2.2.1 q
  rw [Subsingleton.elim z w]

/-- **`MetrizationDimUnique`, proved.** Two metrizations of one group model have the same
dimension. For `g, g' ≥ 1`: `hodgeSpace g = L ⊗ ⋀^g C` is a line for at most one `g ≥ 1`
(`eq_of_finrank_one`, `L` flat over `𝓞_L`). For `g = 0 < g'`: the dimension-`0` uniformization
makes `𝒢(ℂ)_τ` trivial, the dimension-`g'` one (discrete kernel) makes it nontrivial. -/
theorem metrizationDimUnique : ZInQ.G0HeightAdd.MetrizationDimUnique := by
  intro K _ A L _ _ _ g g' M M' h
  obtain ⟨τ⟩ := (inferInstance : Nonempty (L →+* ℂ))
  have key : ∀ {g g' : ℕ} (M : MetrizedModel A L g) (M' : MetrizedModel A L g'),
      M.model = M'.model → g = 0 → g' = 0 := by
    intro g g' M M' h hg0
    subst hg0
    by_contra hg'
    obtain ⟨p, hp⟩ := metrized_exists_pts_ne_one (Nat.pos_of_ne_zero hg') M' τ
    have hs := metrized_pts_subsingleton M τ
    rw [h] at hs
    exact hp (Subsingleton.elim _ _)
  by_cases hg : g = 0
  · rw [hg, key M M' h hg]
  by_cases hg' : g' = 0
  · rw [hg', key M' M h.symm hg']
  haveI : Module.Flat (𝓞 L) L := IsLocalization.flat L (nonZeroDivisors (𝓞 L))
  have h1 := M.hodge.finrank_eq_one
  have h2 := M'.hodge.finrank_eq_one
  rw [← h] at h2
  exact eq_of_finrank_one (R := 𝓞 L) (F := L) (C := M.model.cotangent)
    (Nat.pos_of_ne_zero hg) (Nat.pos_of_ne_zero hg') h1 h2

end ZInQ.Metrization

#print axioms ZInQ.Metrization.metrizationDimUnique
