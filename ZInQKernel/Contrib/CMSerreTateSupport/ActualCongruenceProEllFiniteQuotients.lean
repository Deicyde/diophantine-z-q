import ZInQKernel.Contrib.CMSerreTateSupport.AdicReductionTopologyContinuous

/-!
# The actual congruence kernel is pro-ell

Powers of ell of any element of the genuine residual kernel tend to the
identity in the actual adic matrix topology. Continuity then forces its
image in any discrete group to have ell-power order. This includes ell
at prime two and does not assert torsion freeness at principal depth one.
-/

noncomputable section
set_option autoImplicit false

namespace IntegralCongruence

open Matrix Topology Filter

variable {d : Type*} [Fintype d] [DecidableEq d]
variable (ell : ℕ) [Fact ell.Prime]

def allLevels : GL d ℤ_[ell] →* ((n : ℕ) → GL d (ZMod (ell ^ (n + 1)))) where
  toFun g n := level ell n g
  map_one' := funext fun n => map_one _
  map_mul' g h := funext fun n => map_mul _ g h

theorem allLevels_continuous : Continuous (allLevels (d := d) ell) :=
  continuous_pi (level_continuous ell)

theorem allLevels_injective : Function.Injective (allLevels (d := d) ell) := by
  intro g h hgh
  have hu : g⁻¹ * h = 1 := by
    apply level_separates ell
    intro n
    have hn := congrFun hgh n
    change level ell n g = level ell n h at hn
    simp only [map_mul, map_inv, hn, inv_mul_cancel]
  exact inv_mul_eq_one.mp hu

/-- This is an embedding for the actual matrix topology, by compactness
of matrices over the padic integers and separation by finite residues. -/
theorem allLevels_isClosedEmbedding : IsClosedEmbedding (allLevels (d := d) ell) := by
  haveI : CompactSpace (Matrix d d ℤ_[ell]) := inferInstanceAs (CompactSpace (d → d → ℤ_[ell]))
  haveI : CompactSpace (GL d ℤ_[ell]) := inferInstanceAs (CompactSpace (Matrix d d ℤ_[ell])ˣ)
  exact (allLevels_continuous ell).isClosedEmbedding (allLevels_injective ell)

/-- Actual powers tend to one in the original congruence subgroup topology. -/
theorem congruence_powers_tendsto (g : (residual (d := d) ell).ker) :
    Tendsto (fun N : ℕ => g ^ (ell ^ N)) atTop (𝓝 1) := by
  let E : (residual (d := d) ell).ker → ((n : ℕ) → GL d (ZMod (ell ^ (n + 1)))) :=
    fun x => allLevels ell x.1
  have hE : IsEmbedding E := (allLevels_isClosedEmbedding ell).isEmbedding.comp .subtypeVal
  apply hE.isInducing.tendsto_nhds_iff.mpr
  apply tendsto_pi_nhds.mpr
  intro n
  have hevent : ∀ᶠ N : ℕ in atTop, level ell n (g.1 ^ (ell ^ N)) = 1 := by
    filter_upwards [eventually_ge_atTop n] with N hN
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hN
    rw [map_pow]
    have hnk : ell ^ (n + k) = ell ^ n * ell ^ k := pow_add ell n k
    rw [hnk, pow_mul, adic_kernel_level_power ell n g, one_pow]
  have hT : Tendsto (fun N => level ell n (g.1 ^ (ell ^ N))) atTop (𝓝 (1 : GL d (ZMod (ell ^ (n + 1))))) :=
    Filter.Tendsto.congr' (Filter.Eventually.mono hevent fun _ h => h.symm) tendsto_const_nhds
  simpa [E, allLevels] using hT

/-- Every continuous discrete-group image of the genuine kernel is an
ell-group. In particular this proves the finite-quotient definition of
pro-ell without taking a pro-ell structure as an input. -/
theorem continuous_discrete_image_isPGroup {H : Type*} [Group H]
    [TopologicalSpace H] [DiscreteTopology H]
    (f : (residual (d := d) ell).ker →* H) (hf : Continuous f) : IsPGroup ell f.range := by
  intro x
  obtain ⟨g, hg⟩ := x.2
  have ht := hf.tendsto (1 : (residual (d := d) ell).ker) |>.comp (congruence_powers_tendsto ell g)
  rw [map_one, nhds_discrete] at ht
  obtain ⟨N, hN⟩ := (Filter.tendsto_pure.mp ht).exists
  refine ⟨N, Subtype.ext ?_⟩
  change x.1 ^ (ell ^ N) = 1
  rw [← hg, ← map_pow]
  exact hN

#check congruence_powers_tendsto
#print axioms congruence_powers_tendsto
#check continuous_discrete_image_isPGroup
#print axioms continuous_discrete_image_isPGroup

end IntegralCongruence
