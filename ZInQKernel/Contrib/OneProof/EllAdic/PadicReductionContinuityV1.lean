import Mathlib.NumberTheory.Padics.RingHoms
import Mathlib.Topology.LocallyConstant.Basic

set_option autoImplicit false

namespace RC53.EllAdic

/-- Equality of the actual residues is the distance bound defining a congruence ball. -/
theorem padicInt_dist_le_iff_reductions_eq {p : ℕ} [Fact p.Prime] (n : ℕ)
    (a b : ℤ_[p]) :
    dist a b ≤ (p : ℝ) ^ (-(n : ℤ)) ↔
      PadicInt.toZModPow n a = PadicInt.toZModPow n b := by
  rw [dist_eq_norm, PadicInt.norm_le_pow_iff_mem_span_pow,
    ← PadicInt.ker_toZModPow, RingHom.mem_ker, map_sub, sub_eq_zero]

/-- A map into the p-adic integers is continuous exactly when all of its
actual finite reductions are locally constant. The domain can be any
topological space, including the underlying space of a pro-étale object. -/
theorem continuous_iff_locallyConstant_padicReductions {p : ℕ} [Fact p.Prime]
    {U : Type*} [TopologicalSpace U] (f : U → ℤ_[p]) :
    Continuous f ↔ ∀ n : ℕ, IsLocallyConstant (fun x => PadicInt.toZModPow n (f x)) := by
  constructor
  · intro hf n
    apply (IsLocallyConstant.iff_eventually_eq _).2
    intro x
    have hp : 0 < (p : ℝ) := Nat.cast_pos.mpr (Fact.out : p.Prime).pos
    have hfx : ContinuousAt f x := hf.continuousAt
    exact ((Metric.continuousAt_iff'.1 hfx) _ (zpow_pos hp _)).mono fun y hy =>
      (padicInt_dist_le_iff_reductions_eq n (f y) (f x)).1 (le_of_lt hy)
  · intro hf
    apply continuous_iff_continuousAt.2
    intro x
    apply Metric.continuousAt_iff'.2
    intro ε hε
    obtain ⟨n, hn⟩ := PadicInt.exists_pow_neg_lt p hε
    exact ((hf n).eventually_eq x).mono fun y hy =>
      lt_of_le_of_lt ((padicInt_dist_le_iff_reductions_eq n (f y) (f x)).2 hy) hn

end RC53.EllAdic
