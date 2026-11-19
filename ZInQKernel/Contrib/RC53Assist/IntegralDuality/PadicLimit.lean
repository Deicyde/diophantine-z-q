module

public import Mathlib.NumberTheory.Padics.RingHoms
public import Mathlib.Topology.MetricSpace.Cauchy
public import Mathlib.Topology.UniformSpace.UniformApproximation
public import Mathlib.Topology.Instances.ZMod

/-!
# Continuous limits of compatible p-adic coefficient functions

Congruence modulo a power of the prime bounds the p-adic distance. Compatibility of successive
approximations therefore gives a uniform Cauchy sequence, whose continuous limit has all of the
prescribed residues. The domain is an arbitrary topological space.
-/

@[expose] public section

namespace ZInQ.Contrib.RC53Assist.IntegralDuality.PadicLimit

open Filter Set
open scoped Topology

variable {p : ℕ} [Fact p.Prime]

/-- Equality of residues is equivalent to the corresponding distance bound. -/
theorem residue_eq_iff_norm_sub_le (k : ℕ) (a b : ℤ_[p]) :
    PadicInt.toZModPow k a = PadicInt.toZModPow k b ↔
      ‖a - b‖ ≤ (p : ℝ) ^ (-(k : ℤ)) := by
  rw [← sub_eq_zero, ← map_sub, ← RingHom.mem_ker, PadicInt.ker_toZModPow,
    ← PadicInt.norm_le_pow_iff_mem_span_pow]

/-- Equality at a higher level implies equality at every lower level. -/
theorem residue_eq_of_le {k n : ℕ} (hkn : k ≤ n) {a b : ℤ_[p]}
    (h : PadicInt.toZModPow n a = PadicInt.toZModPow n b) :
    PadicInt.toZModPow k a = PadicInt.toZModPow k b := by
  have hc := congrArg (ZMod.cast : ZMod (p ^ n) → ZMod (p ^ k)) h
  simpa only [PadicInt.cast_toZModPow k n hkn] using hc

/-- Residue projections are continuous for the actual p-adic topology. -/
theorem continuous_toZModPow (k : ℕ) : Continuous (PadicInt.toZModPow (p := p) k) := by
  rw [continuous_iff_continuousAt]
  intro a
  rw [ContinuousAt, nhds_discrete (ZMod (p ^ k)), tendsto_pure]
  have hr : 0 < (p : ℝ) ^ (-(k : ℤ)) :=
    zpow_pos (by exact_mod_cast (Fact.out : p.Prime).pos) _
  filter_upwards [Metric.ball_mem_nhds a hr] with b hb
  apply (residue_eq_iff_norm_sub_le k b a).2
  exact (show ‖b - a‖ < (p : ℝ) ^ (-(k : ℤ)) from hb).le

/-- A compatible approximation stays constant at every previously determined residue level. -/
theorem residue_stable {X : Type*} (f : ℕ → X → ℤ_[p])
    (hc : ∀ j x, PadicInt.toZModPow j (f (j + 1) x) = PadicInt.toZModPow j (f j x))
    (k n : ℕ) (hkn : k ≤ n) (x : X) :
    PadicInt.toZModPow k (f n x) = PadicInt.toZModPow k (f k x) := by
  induction n, hkn using Nat.le_induction with
  | base => rfl
  | succ n hkn ih =>
    exact (residue_eq_of_le hkn (hc n x)).trans ih

/-- Continuous compatible approximations have a continuous p-adic limit with all residues fixed. -/
theorem exists_continuous_limit {X : Type*} [TopologicalSpace X] (f : ℕ → X → ℤ_[p])
    (hf : ∀ n, Continuous (f n))
    (hc : ∀ j x, PadicInt.toZModPow j (f (j + 1) x) = PadicInt.toZModPow j (f j x)) :
    ∃ g : X → ℤ_[p], Continuous g ∧
      ∀ j x, PadicInt.toZModPow j (g x) = PadicInt.toZModPow j (f j x) := by
  classical
  have hb : ∀ k m n, k ≤ m → k ≤ n → ∀ x,
      dist (f m x) (f n x) ≤ (p : ℝ) ^ (-(k : ℤ)) := by
    intro k m n hkm hkn x
    rw [dist_eq_norm]
    apply (residue_eq_iff_norm_sub_le k _ _).1
    exact (residue_stable f hc k m hkm x).trans (residue_stable f hc k n hkn x).symm
  have hu : UniformCauchySeqOn f atTop univ := by
    rw [Metric.uniformCauchySeqOn_iff]
    intro ε hε
    obtain ⟨k, hk⟩ := PadicInt.exists_pow_neg_lt p hε
    exact ⟨k, fun m hm n hn x _ => (hb k m n hm hn x).trans_lt hk⟩
  have hpoint : ∀ x, ∃ y : ℤ_[p], Tendsto (fun n => f n x) atTop (𝓝 y) :=
    fun x => cauchySeq_tendsto_of_complete (hu.cauchySeq (mem_univ x))
  choose g hg using hpoint
  have huni : TendstoUniformly f g atTop :=
    tendstoUniformlyOn_univ.1 (hu.tendstoUniformlyOn_of_tendsto (fun x _ => hg x))
  refine ⟨g, huni.continuous (Filter.Eventually.of_forall hf).frequently, ?_⟩
  intro j x
  have hproj := (continuous_toZModPow (p := p) j).tendsto (g x) |>.comp (hg x)
  have heq : ∀ᶠ n : ℕ in atTop,
      PadicInt.toZModPow j (f n x) = PadicInt.toZModPow j (f j x) := by
    filter_upwards [eventually_ge_atTop j] with n hn
    exact residue_stable f hc j n hn x
  exact tendsto_nhds_unique hproj (tendsto_const_nhds.congr' (heq.mono fun _ h => h.symm))

/-- Division by a power of two on its kernel preserves continuity on arbitrary domains. -/
theorem continuous_division_two_pow {X : Type*} [TopologicalSpace X]
    (k : ℕ) (f : X → ℤ_[2]) (hf : Continuous f)
    (hker : ∀ x, PadicInt.toZModPow k (f x) = 0) :
    ∃ g : X → ℤ_[2], Continuous g ∧ ∀ x, (2 : ℤ_[2]) ^ k * g x = f x := by
  have htwo : (2 : ℚ_[2]) ^ k ≠ 0 := pow_ne_zero k two_ne_zero
  have hdvd (x : X) : (2 : ℤ_[2]) ^ k ∣ f x := by
    have hm : f x ∈ RingHom.ker (PadicInt.toZModPow (p := 2) k) :=
      RingHom.mem_ker.mpr (hker x)
    rw [PadicInt.ker_toZModPow, Ideal.mem_span_singleton] at hm
    simpa only [Nat.cast_ofNat] using hm
  have hnorm (x : X) : ‖(f x : ℚ_[2]) * ((2 : ℚ_[2]) ^ k)⁻¹‖ ≤ 1 := by
    obtain ⟨a, ha⟩ := hdvd x
    have hq : (f x : ℚ_[2]) = (2 : ℚ_[2]) ^ k * (a : ℚ_[2]) := by
      simpa only [map_mul, map_pow, map_ofNat, PadicInt.Coe.ringHom_apply] using
        congrArg (PadicInt.Coe.ringHom (p := 2)) ha
    have hcancel : (f x : ℚ_[2]) * ((2 : ℚ_[2]) ^ k)⁻¹ = (a : ℚ_[2]) := by
      rw [hq]
      calc
        ((2 : ℚ_[2]) ^ k * (a : ℚ_[2])) * ((2 : ℚ_[2]) ^ k)⁻¹ =
            (a : ℚ_[2]) * ((2 : ℚ_[2]) ^ k * ((2 : ℚ_[2]) ^ k)⁻¹) := by ac_rfl
        _ = (a : ℚ_[2]) := by rw [mul_inv_cancel₀ htwo, mul_one]
    rw [hcancel]
    exact a.2
  let g : X → ℤ_[2] := fun x => ⟨(f x : ℚ_[2]) * ((2 : ℚ_[2]) ^ k)⁻¹, hnorm x⟩
  refine ⟨g, ?_, ?_⟩
  · exact ((continuous_subtype_val.comp hf).mul continuous_const).subtype_mk _
  · intro x
    apply PadicInt.ext
    change (2 : ℚ_[2]) ^ k * ((f x : ℚ_[2]) * ((2 : ℚ_[2]) ^ k)⁻¹) = (f x : ℚ_[2])
    calc
      (2 : ℚ_[2]) ^ k * ((f x : ℚ_[2]) * ((2 : ℚ_[2]) ^ k)⁻¹) =
          (f x : ℚ_[2]) * ((2 : ℚ_[2]) ^ k * ((2 : ℚ_[2]) ^ k)⁻¹) := by ac_rfl
      _ = (f x : ℚ_[2]) := by rw [mul_inv_cancel₀ htwo, mul_one]

/-- Multiples of the prime power vanish under the corresponding residue projection. -/
theorem toZModPow_prime_pow_mul (k : ℕ) (t : ℤ_[p]) :
    PadicInt.toZModPow k ((p : ℤ_[p]) ^ k * t) = 0 := by
  rw [← Nat.cast_pow, map_mul, map_natCast, ZMod.natCast_self, zero_mul]

/-- The p-adic residue projections jointly separate points. -/
theorem separated (t : ℤ_[p]) (h : ∀ k, PadicInt.toZModPow k t = 0) : t = 0 := by
  apply PadicInt.ext_of_toZModPow.1
  intro k
  simpa only [map_zero] using h k

/-- The ring of p-adic integers has no nonzero element killed by its prime. -/
theorem torsionFree (t : ℤ_[p]) (h : (p : ℤ_[p]) * t = 0) : t = 0 := by
  exact (mul_eq_zero.1 h).resolve_left (by exact_mod_cast (Fact.out : p.Prime).ne_zero)

end ZInQ.Contrib.RC53Assist.IntegralDuality.PadicLimit
