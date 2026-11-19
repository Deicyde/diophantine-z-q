import AdicImageSeparationSeparated
import Mathlib.NumberTheory.Padics.ProperSpace
import Mathlib.Topology.Algebra.Group.Matrix
import Mathlib.Topology.Instances.ZMod

/-!
# Continuity of the actual adic reductions

All topologies are the usual padic topology and the discrete topologies
on finite residue rings, not an assumed continuity structure.
-/

noncomputable section
set_option autoImplicit false

namespace IntegralCongruence

open Matrix Topology Filter

variable (ell : ℕ) [Fact ell.Prime]

/-- The canonical reduction of padic integers is continuous. -/
theorem toZModPow_continuous (n : ℕ) : Continuous (PadicInt.toZModPow (p := ell) n) := by
  apply continuous_of_continuousAt_zero (PadicInt.toZModPow (p := ell) n).toAddMonoidHom
  rw [continuousAt_def]
  intro s hs
  have hs0 : (0 : ZMod (ell ^ n)) ∈ s := mem_of_mem_nhds (by simpa using hs)
  have heps : 0 < (ell : ℝ) ^ (-(n : ℤ)) := zpow_pos (by exact_mod_cast (Fact.out : ell.Prime).pos) _
  apply Filter.mem_of_superset (Metric.ball_mem_nhds (0 : ℤ_[ell]) heps)
  intro x hx
  have hnorm : ‖x‖ ≤ (ell : ℝ) ^ (-(n : ℤ)) := by
    exact le_of_lt (by simpa [Metric.mem_ball, dist_zero_right] using hx)
  have hz : PadicInt.toZModPow n x = 0 := by
    rw [← RingHom.mem_ker, PadicInt.ker_toZModPow]
    exact (PadicInt.norm_le_pow_iff_mem_span_pow x n).mp hnorm
  change PadicInt.toZModPow n x ∈ s
  rw [hz]
  exact hs0

/-- The canonical residual map is continuous. -/
theorem toZMod_continuous : Continuous (PadicInt.toZMod (p := ell)) := by
  apply continuous_of_continuousAt_zero (PadicInt.toZMod (p := ell)).toAddMonoidHom
  rw [continuousAt_def]
  intro s hs
  have hs0 : (0 : ZMod ell) ∈ s := mem_of_mem_nhds (by simpa using hs)
  apply Filter.mem_of_superset (Metric.ball_mem_nhds (0 : ℤ_[ell]) zero_lt_one)
  intro x hx
  have hnorm : ‖x‖ < 1 := by simpa [Metric.mem_ball, dist_zero_right] using hx
  have hz : PadicInt.toZMod x = 0 := by
    rw [← RingHom.mem_ker, PadicInt.ker_toZMod, PadicInt.maximalIdeal_eq_span_p, Ideal.mem_span_singleton]
    exact (PadicInt.norm_lt_one_iff_dvd x).mp hnorm
  change PadicInt.toZMod x ∈ s
  rw [hz]
  exact hs0

variable {d : Type*} [Fintype d] [DecidableEq d]

theorem level_continuous (n : ℕ) : Continuous (level (d := d) ell n) :=
  (toZModPow_continuous ell (n + 1)).generalLinearGroup_map

theorem residual_continuous : Continuous (residual (d := d) ell) :=
  (toZMod_continuous ell).generalLinearGroup_map

#print axioms toZModPow_continuous
#print axioms level_continuous
#print axioms residual_continuous
#check Continuous.isClosedEmbedding
#check IsCompact.elim_finite_subcover
#check IsClosed.isCompact
#check continuous_pi
#check Units.continuous_val

end IntegralCongruence
