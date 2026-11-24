import ZInQKernel.Contrib.OneProof.TateFiniteApproximation
import Mathlib.NumberTheory.Padics.ProperSpace
import Mathlib.RingTheory.Finiteness.Cardinality

/-!
# Limits of the endomorphisms arising from finite torsion quotients

If at level n an integral algebraic endomorphism maps into W modulo ℓ^n
and its image contains a fixed nonzero multiple of W, the ℤ_ℓ-span of
algebraic endomorphisms contains a map whose image lies in W and contains
that same multiple of W. No compatibility of the endomorphisms is needed.
-/

noncomputable section

open Filter Topology PkgI3.AbVar
open scoped TensorProduct CategoryTheory.MonObj

namespace ZInQ.Contrib.TateFiniteApproximation

variable {ℓ : ℕ} [hℓ : Fact ℓ.Prime]

private theorem cluster_mod_powers {H : Type*} [AddCommGroup H] [Module ℤ_[ℓ] H]
    [Module.Finite ℤ_[ℓ] H] (v : ℕ → H) :
    ∃ a : H, ∀ n : ℕ, ∃ j ≥ n, ∃ z : H, v j - a = (ℓ : ℤ_[ℓ])^n • z := by
  classical
  obtain ⟨d, f, hf⟩ := Module.Finite.exists_fin' ℤ_[ℓ] H
  choose t ht using fun n => hf (v n)
  obtain ⟨a, σ, hσ, hlim⟩ := CompactSpace.tendsto_subseq t
  refine ⟨f a, fun n => ?_⟩
  have hpos : (0 : ℝ) < (ℓ : ℝ)^(-(n : ℤ)) := zpow_pos (by exact_mod_cast hℓ.out.pos) _
  have hcoord (i) : ∀ᶠ j in atTop, ‖t (σ j) i - a i‖ < (ℓ : ℝ)^(-(n : ℤ)) := by
    simpa [Function.comp_def, dist_eq_norm] using
      (tendsto_pi_nhds.mp hlim i).eventually (Metric.ball_mem_nhds (a i) hpos)
  obtain ⟨j, hnj, hj⟩ := ((hσ.tendsto_atTop.eventually_ge_atTop n).and (Filter.eventually_all.mpr hcoord)).exists
  have hd (i) : (ℓ : ℤ_[ℓ])^n ∣ t (σ j) i - a i := Ideal.mem_span_singleton.mp
    ((PadicInt.norm_le_pow_iff_mem_span_pow _ _).mp (hj i).le)
  choose z hz using hd
  refine ⟨σ j, hnj, f z, ?_⟩
  rw [← ht, ← map_sub, ← map_smul]
  exact congrArg f (funext hz)

/-- A compactness argument over the finite coefficient module, with Krull
intersection in the target and its quotients. -/
theorem exists_endomorphism_between {M : Type*} [AddCommGroup M] [Module ℤ_[ℓ] M]
    [Module.Finite ℤ_[ℓ] M] (E : Submodule ℤ_[ℓ] (Module.End ℤ_[ℓ] M))
    [Module.Finite ℤ_[ℓ] E] (W : Submodule ℤ_[ℓ] M) (N : ℕ)
    (h : ∀ n : ℕ, ∃ u ∈ E,
      (∀ x : M, ∃ w ∈ W, ∃ z : M, u x - w = (ℓ : ℤ_[ℓ])^n • z) ∧
      ∀ w ∈ W, N • w ∈ LinearMap.range u) :
    ∃ u ∈ E, LinearMap.range u ≤ W ∧ ∀ w ∈ W, N • w ∈ LinearMap.range u := by
  classical
  choose u hu hup hlow using h
  obtain ⟨a, ha⟩ := cluster_mod_powers (ℓ := ℓ) (fun n => (⟨u n, hu n⟩ : E))
  have diff (n : ℕ) : ∃ j ≥ n, ∃ z : Module.End ℤ_[ℓ] M, ∀ x, u j x - a.val x = (ℓ : ℤ_[ℓ])^n • z x := by
    obtain ⟨j, hj, z, h⟩ := ha n
    exact ⟨j, hj, z.val, fun x => congrArg (fun f : E => f.val x) h⟩
  refine ⟨a.val, a.property, ?_, ?_⟩
  · rintro x ⟨v, rfl⟩
    apply mem_of_approx W
    intro n
    obtain ⟨j, hj, z, hz⟩ := diff n
    obtain ⟨w, hw, b, hb⟩ := hup j v
    refine ⟨w, hw, (ℓ : ℤ_[ℓ])^(j-n) • b - z v, ?_⟩
    rw [smul_sub, smul_smul, ← pow_add, Nat.add_sub_of_le hj, ← hb, ← hz]
    abel
  · intro w hw
    apply mem_of_approx (LinearMap.range a.val)
    intro n
    obtain ⟨j, _, z, hz⟩ := diff n
    obtain ⟨v, hv⟩ := hlow j w hw
    exact ⟨a.val v, ⟨v, rfl⟩, z v, hv ▸ hz v⟩

end ZInQ.Contrib.TateFiniteApproximation
