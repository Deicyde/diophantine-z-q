import ZInQKernel.Contrib.OneProof.HeckePrimeRationality.AllLevelUnipotentAverage

/-!
# Linearity of the actual unipotent projector

The constructed average is complex-linear and is onto the Gamma-one space.
It transports a spanning family if that family is already proved to span the
principal-level space. It does not prove the missing principal Eisenstein
spanning theorem or the unrestricted Hecke-rationality leaf.
-/

noncomputable section

namespace ZInQ.Contrib.HeckePrimeRationality.AllLevelAverage

open UpperHalfPlane CongruenceSubgroup Matrix.SpecialLinearGroup ModularGroup
open scoped MatrixGroups ModularForm

/-- The actual average as a complex-linear map, with both linearity laws proved. -/
def avgLinear (N : ℕ) (hN : 0 < N) (k : ℤ) :
    ModularForm ((Gamma N).map (mapGL ℝ)) k →ₗ[ℂ]
      ModularForm ((Gamma1 N).map (mapGL ℝ)) k where
  toFun := avg N hN k
  map_add' f g := by
    ext τ
    change avg N hN k (f + g) τ = avg N hN k f τ + avg N hN k g τ
    rw [avg_apply, avg_apply, avg_apply]
    simp only [FunLike.coe_add, SlashAction.add_slash, Pi.add_apply, Finset.sum_add_distrib]
    ring
  map_smul' c f := by
    ext τ
    change avg N hN k (c • f) τ = c * avg N hN k f τ
    rw [avg_apply, avg_apply]
    change (N : ℂ)⁻¹ * ∑ j : Fin N, (⇑(c • f) ∣[k] (T ^ (j : ℤ) : SL(2, ℤ))) τ =
      c * ((N : ℂ)⁻¹ * ∑ j : Fin N, (⇑f ∣[k] (T ^ (j : ℤ) : SL(2, ℤ))) τ)
    simp only [FunLike.coe_smul, ModularForm.SL_smul_slash, Pi.smul_apply, smul_eq_mul,
      ← Finset.mul_sum]
    ring

@[simp]
lemma avgLinear_apply (N : ℕ) (hN : 0 < N) (k : ℤ)
    (f : ModularForm ((Gamma N).map (mapGL ℝ)) k) :
    avgLinear N hN k f = avg N hN k f := rfl

/-- Surjectivity is witnessed by the actual restriction, not by a dimension argument. -/
theorem avgLinear_surjective (N : ℕ) (hN : 0 < N) (k : ℤ) :
    Function.Surjective (avgLinear N hN k) := by
  intro g
  exact ⟨ModularForm.restrict Gamma_map_le_Gamma1_map g, avg_restrict N hN k g⟩

/-- A proved principal-level spanning family gives a Gamma-one spanning family
by the explicit projector. The principal spanning premise remains visible. -/
theorem span_averages_of_span_top (N : ℕ) (hN : 0 < N) (k : ℤ)
    (s : Set (ModularForm ((Gamma N).map (mapGL ℝ)) k))
    (hs : Submodule.span ℂ s = ⊤) :
    Submodule.span ℂ ((avgLinear N hN k) '' s) = ⊤ := by
  rw [eq_top_iff]
  intro g _
  have hg : ModularForm.restrict Gamma_map_le_Gamma1_map g ∈ Submodule.span ℂ s := by
    rw [hs]
    exact Submodule.mem_top
  have hmap := Submodule.mem_map_of_mem (f := avgLinear N hN k) hg
  rw [Submodule.map_span] at hmap
  simpa only [avgLinear_apply, avg_restrict] using hmap

end ZInQ.Contrib.HeckePrimeRationality.AllLevelAverage
