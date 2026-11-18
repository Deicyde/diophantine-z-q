import CriticalMellinV003
import Mathlib.Analysis.Normed.Group.Tannery

/-!
# Dominated convergence for signed residue filters

A summable complex coefficient sequence is reconstructed at its first term by
signed filters at the residue classes one and minus one as the modulus grows.
This is an actual limit theorem; no nonvanishing of an L-value is a hypothesis.
-/

noncomputable section

open Complex Filter
open scoped Topology Classical

namespace CriticalTwists

/-- The literal signed multiplier at residues one and minus one modulo `r + 3`. -/
def signedResidueMask (ε : ℂ) (r n : ℕ) : ℂ := by
  letI : NeZero (r + 3) := ⟨by omega⟩
  exact residueIndicator (M := r + 3) 1 n + ε * residueIndicator (M := r + 3) (-1) n

/-- Every residue indicator has norm at most one. -/
theorem norm_residueIndicator_le {M : ℕ} [NeZero M] (u b : ZMod M) :
    ‖residueIndicator u b‖ ≤ 1 := by
  simp only [residueIndicator]
  split_ifs <;> norm_num

/-- A uniform domination independent of the varying modulus. -/
theorem signedResidueMask_norm_le (ε : ℂ) (r n : ℕ) :
    ‖signedResidueMask ε r n‖ ≤ 1 + ‖ε‖ := by
  letI : NeZero (r + 3) := ⟨by omega⟩
  dsimp only [signedResidueMask]
  calc
    _ ≤ ‖residueIndicator (M := r + 3) 1 n‖ +
        ‖ε * residueIndicator (M := r + 3) (-1) n‖ := norm_add_le _ _
    _ = ‖residueIndicator (M := r + 3) 1 n‖ +
        ‖ε‖ * ‖residueIndicator (M := r + 3) (-1) n‖ := by rw [norm_mul]
    _ ≤ 1 + ‖ε‖ := by
      have hp := norm_residueIndicator_le (M := r + 3) 1 (n : ZMod (r + 3))
      have hm := norm_residueIndicator_le (M := r + 3) (-1) (n : ZMod (r + 3))
      nlinarith [norm_nonneg ε]

/-- For each fixed positive index, sufficiently large moduli isolate only index one. -/
theorem signedResidueMask_eventually (ε : ℂ) (n : ℕ) :
    (fun r : ℕ => signedResidueMask ε r n) =ᶠ[atTop]
      fun _ => if n = 1 then 1 else 0 := by
  filter_upwards [eventually_ge_atTop n] with r hr
  letI : NeZero (r + 3) := ⟨by omega⟩
  have hsize : n + 1 < r + 3 := by omega
  have hminus : (n : ZMod (r + 3)) ≠ -1 := by
    intro h
    have hz : ((n + 1 : ℕ) : ZMod (r + 3)) = 0 := by
      simp only [Nat.cast_add, Nat.cast_one, h, neg_add_cancel]
    have hdvd := (ZMod.natCast_eq_zero_iff (n + 1) (r + 3)).mp hz
    exact (Nat.not_dvd_of_pos_of_lt (Nat.succ_pos n) hsize) hdvd
  by_cases hn : n = 1
  · subst n
    simp only [Nat.cast_one] at hminus
    simp [signedResidueMask, residueIndicator, hminus]
  · have hplus : (n : ZMod (r + 3)) ≠ 1 := by
      intro h
      have hc : n % (r + 3) = 1 % (r + 3) :=
        (ZMod.natCast_eq_natCast_iff' n 1 (r + 3)).mp (by simpa using h)
      rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at hc
      exact hn hc
    simp [signedResidueMask, residueIndicator, hplus, hminus, hn]

/-- The actual sum of the signed residue-filtered sequence. -/
def signedResidueSeries (c : ℕ → ℂ) (ε : ℂ) (r : ℕ) : ℂ :=
  ∑' n : ℕ, signedResidueMask ε r n * c n

/-- Signed residue filtering converges to the first coefficient of any summable sequence. -/
theorem signedResidueSeries_tendsto (c : ℕ → ℂ) (hc : Summable c) (ε : ℂ) :
    Tendsto (signedResidueSeries c ε) atTop (𝓝 (c 1)) := by
  have hb : Summable (fun n : ℕ => (1 + ‖ε‖) * ‖c n‖) := hc.norm.mul_left _
  have hp (n : ℕ) : Tendsto (fun r : ℕ => signedResidueMask ε r n * c n) atTop
      (𝓝 (if n = 1 then c 1 else 0)) := by
    have heq : (fun r : ℕ => signedResidueMask ε r n * c n) =ᶠ[atTop]
        fun _ => if n = 1 then c 1 else 0 := by
      filter_upwards [signedResidueMask_eventually ε n] with r hr
      rw [hr]
      split_ifs with hn
      · subst n
        simp
      · simp
    exact tendsto_const_nhds.congr' heq.symm
  have h := tendsto_tsum_of_dominated_convergence hb hp
    (Eventually.of_forall fun r n => by
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_right (signedResidueMask_norm_le ε r n) (norm_nonneg _))
  change Tendsto (fun r : ℕ => ∑' n : ℕ, signedResidueMask ε r n * c n) atTop (𝓝 (c 1))
  simpa only [tsum_ite_eq] using h

/-- Normalization, rather than an L-value hypothesis, supplies eventual nonvanishing. -/
theorem signedResidueSeries_eventually_ne_zero (c : ℕ → ℂ) (hc : Summable c)
    (hc1 : c 1 = 1) (ε : ℂ) : ∀ᶠ r : ℕ in atTop, signedResidueSeries c ε r ≠ 0 := by
  have h := signedResidueSeries_tendsto c hc ε
  rw [hc1] at h
  exact h.eventually (isOpen_compl_singleton.mem_nhds (by simp : (1 : ℂ) ∈ ({0} : Set ℂ)ᶜ))

end CriticalTwists
