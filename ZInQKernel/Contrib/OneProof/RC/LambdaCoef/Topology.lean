import Mathlib.Topology.Algebra.Nonarchimedean.Bases
import Mathlib.Topology.Algebra.Group.Basic

/-!
# Lane RC28 round 2, part 1: continuity criteria for linearly topologized modules

Manuscript `diophantine_zq.tex` (11/5), tex 2747 (`Λ = ℤ₂[[t]]`), 2836–2838 (`T = T₂E`) and
4976–5200 (height-one fibres): the conditional fixed-character module `T_2E ⊗ Λ(α)` (not a
global moving-character module asserted at tex 2780–2785) and its height-one fibres are linearly
topologized (a basis of neighbourhoods of zero by subgroups), and the Galois action is
continuous. Two general criteria:

* `continuousSMul_of_hasBasis`: a group `G` acting by additive maps on a topological additive group
  `M` whose neighbourhoods of zero have a basis of subgroups `U n` stable under `G`, such that every
  orbit map is continuous at `1` modulo each `U n`, acts continuously (`ContinuousSMul G M`).
* `continuous_of_hasBasis`: an additive map between such groups mapping some `U m` into each `V n`
  is continuous.

Kinds: PROVED.
-/

namespace ZInQ.Manuscript.RC.LambdaCoef

open Filter Topology

/-- **Joint continuity of a linear action from a basis of stable subgroups.** Kind: PROVED. -/
theorem continuousSMul_of_hasBasis {G M : Type*} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [AddCommGroup M] [DistribMulAction G M] [TopologicalSpace M]
    [IsTopologicalAddGroup M] {ι : Type*} (U : ι → AddSubgroup M)
    (hU : (𝓝 (0 : M)).HasBasis (fun _ => True) (fun i => (U i : Set M)))
    (hstab : ∀ (g : G) (i : ι), ∀ x ∈ U i, g • x ∈ U i)
    (horbit : ∀ (v : M) (i : ι), ∀ᶠ g in 𝓝 (1 : G), g • v - v ∈ U i) :
    ContinuousSMul G M := by
  refine ⟨continuous_iff_continuousAt.mpr fun ⟨g₀, v₀⟩ => ?_⟩
  have hb : (𝓝 (g₀ • v₀)).HasBasis (fun _ => True) (fun i => (fun x => g₀ • v₀ + x) '' U i) := by
    have := hU.map (fun x => g₀ • v₀ + x)
    rwa [map_add_left_nhds_zero] at this
  rw [ContinuousAt, hb.tendsto_right_iff]
  intro i _
  -- `g • v - g₀ • v₀ = g • (v - v₀) + g₀ • ((g₀⁻¹ * g) • v₀ - v₀)`
  have h1 : ∀ᶠ p : G × M in 𝓝 (g₀, v₀), p.2 - v₀ ∈ U i := by
    have hc : Tendsto (fun p : G × M => p.2 - v₀) (𝓝 (g₀, v₀)) (𝓝 0) :=
      Continuous.tendsto' (by fun_prop) _ _ (sub_self v₀)
    exact hc (hU.mem_of_mem trivial)
  have h2 : ∀ᶠ p : G × M in 𝓝 (g₀, v₀), (g₀⁻¹ * p.1) • v₀ - v₀ ∈ U i := by
    have hc : Tendsto (fun p : G × M => g₀⁻¹ * p.1) (𝓝 (g₀, v₀)) (𝓝 1) :=
      Continuous.tendsto' (by fun_prop) _ _ (inv_mul_cancel g₀)
    exact hc (horbit v₀ i)
  filter_upwards [h1, h2] with p hp1 hp2
  refine ⟨p.1 • (p.2 - v₀) + g₀ • ((g₀⁻¹ * p.1) • v₀ - v₀),
    (U i).add_mem (hstab _ _ _ hp1) (hstab _ _ _ hp2), ?_⟩
  simp only [smul_sub, smul_smul, mul_inv_cancel_left]
  abel

/-- **An additive map between linearly topologized groups mapping a basic subgroup into each basic
subgroup is continuous.** Kind: PROVED. -/
theorem continuous_of_hasBasis {M N : Type*} [AddCommGroup M] [TopologicalSpace M]
    [IsTopologicalAddGroup M] [AddCommGroup N] [TopologicalSpace N] [IsTopologicalAddGroup N]
    {ι κ : Type*} (U : ι → AddSubgroup M) (V : κ → AddSubgroup N)
    (hU : (𝓝 (0 : M)).HasBasis (fun _ => True) (fun i => (U i : Set M)))
    (hV : (𝓝 (0 : N)).HasBasis (fun _ => True) (fun j => (V j : Set N)))
    (f : M →+ N) (hf : ∀ j, ∃ i, ∀ x ∈ U i, f x ∈ V j) : Continuous f := by
  refine continuous_of_continuousAt_zero f ?_
  rw [ContinuousAt, map_zero, hU.tendsto_iff hV]
  intro j _
  obtain ⟨i, hi⟩ := hf j
  exact ⟨i, trivial, fun x hx => hi x hx⟩

end ZInQ.Manuscript.RC.LambdaCoef
