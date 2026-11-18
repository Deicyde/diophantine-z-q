import ZInQKernel.Contrib.OneProof.HeckePrimeRationality.CoprimeProductTraceAffineLines
import Mathlib.Data.Fintype.BigOperators

/-!
# Exact determinant-line character cancellation

The τ-first torsion pairing uses br-as, hence the negative determinant.
The affine-line character sum is p times the phase -ℓds on the surviving
scalar line V=sT, and vanishes off that line.
-/

noncomputable section
set_option autoImplicit false
open scoped BigOperators

namespace ZInQ.Contrib.HeckePrimeRationality.CoprimeProductTrace

/-- The actual residue character in the br-as orientation. -/
def pairing (p : ℕ) (V U : Pair (ZMod p)) : ℂ := phase p (-det V U)

lemma pairing_affine (p : ℕ) [Fact p.Prime] (e : ZMod p)
    (V U T : Pair (ZMod p)) (t : ZMod p) :
    pairing p (scale e V) (U + scale t T) =
      phase p (-e * det V U) * phase p ((-e * det V T) * t) := by
  let : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  unfold pairing
  rw [det_add_right, det_scale_left, det_scale_left, det_scale_right]
  rw [show -(e * det V U + e * (t * det V T)) =
    -e * det V U + (-e * det V T) * t by ring, phase_add]

/-- Literal cancellation over the genuine determinant-fibre subtype. -/
theorem determinant_character_sum (p : ℕ) [Fact p.Prime] (e : ZMod p) (he : e ≠ 0)
    (T : Pair (ZMod p)) (hT : T ≠ 0) (V : Pair (ZMod p)) (d : ZMod p) :
    (∑ U : {U : Pair (ZMod p) // det T U = d}, pairing p (scale e V) U.val) =
      if det T V = 0 then (p : ℂ) * phase p (-e * d * coordinate T V) else 0 := by
  let : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  rw [← (affineLineEquiv T hT d).sum_comp]
  simp only [affineLineEquiv, Equiv.coe_fn_mk]
  simp_rw [pairing_affine, ← Finset.mul_sum]
  rw [sum_phase_mul]
  by_cases hv : det T V = 0
  · have hs := (determinant_kernel T hT V).mp hv
    have hvT : det V T = 0 := by rw [det_swap, hv, neg_zero]
    rw [hvT, mul_zero, if_pos rfl, if_pos hv]
    have hbase : det V (lineBase T d) = coordinate T V * d := by
      nth_rewrite 1 [hs]
      rw [det_scale_left, det_lineBase T hT d]
    rw [hbase]
    have hphase : -e * (coordinate T V * d) = -e * d * coordinate T V := by ring
    rw [hphase, mul_comm]
  · have hvT : det V T ≠ 0 := by
      intro hz
      rw [det_swap, hz, neg_zero] at hv
      exact hv rfl
    have hc : -e * det V T ≠ 0 := mul_ne_zero (neg_ne_zero.mpr he) hvT
    rw [if_neg hc, mul_zero, if_neg hv]

/-- Reindexing the surviving determinant kernel by its actual scalar parameter. -/
theorem sum_kernel_coordinates (p : ℕ) [Fact p.Prime] (T : Pair (ZMod p)) (hT : T ≠ 0)
    (g : Pair (ZMod p) → ℂ) (c : ZMod p) :
    (∑ V : Pair (ZMod p), if det T V = 0 then g V * phase p (c * coordinate T V) else 0) =
      ∑ s : ZMod p, g (scale s T) * phase p (c * s) := by
  classical
  have hs : (∑ V : Pair (ZMod p), if det T V = 0 then g V * phase p (c * coordinate T V) else 0) =
      ∑ V : {V : Pair (ZMod p) // det T V = 0}, g V.val * phase p (c * coordinate T V.val) := by
    calc (∑ V : Pair (ZMod p), if det T V = 0 then g V * phase p (c * coordinate T V) else 0) =
        ∑ V ∈ {V : Pair (ZMod p) | det T V = 0}.toFinset, g V * phase p (c * coordinate T V) := by
          rw [← Finset.sum_filter]
          apply Finset.sum_congr
          · ext V; simp
          · intro V _; rfl
      _ = ∑ V : {V : Pair (ZMod p) // det T V = 0}, g V.val * phase p (c * coordinate T V.val) :=
        Finset.sum_toFinset_eq_subtype (fun V : Pair (ZMod p) => det T V = 0)
          (fun V => g V * phase p (c * coordinate T V))
  rw [hs]
  rw [← (affineLineEquiv T hT 0).sum_comp]
  simp only [affineLineEquiv, Equiv.coe_fn_mk, lineBase_zero, zero_add]
  apply Finset.sum_congr rfl
  intro s _
  have hc := coordinate_line T hT 0 s
  rw [lineBase_zero, zero_add] at hc
  rw [hc]

/-- The complete rank-two determinant-character reduction to finite rank-one correlations. -/
theorem determinant_pair_reduction (p : ℕ) [Fact p.Prime] (e : ZMod p) (he : e ≠ 0)
    (d : ZMod p) (f g : Pair (ZMod p) → ℂ) :
    (∑ T : {T : Pair (ZMod p) // T ≠ 0},
      f T.val * ∑ U : {U : Pair (ZMod p) // det T.val U = d},
        ∑ V : Pair (ZMod p), g V * pairing p (scale e V) U.val) =
      ∑ s : ZMod p, (p : ℂ) * phase p (-e * d * s) *
        ∑ T : {T : Pair (ZMod p) // T ≠ 0}, f T.val * g (scale s T.val) := by
  classical
  have hinner (T : {T : Pair (ZMod p) // T ≠ 0}) :
      (∑ U : {U : Pair (ZMod p) // det T.val U = d},
        ∑ V : Pair (ZMod p), g V * pairing p (scale e V) U.val) =
      (p : ℂ) * ∑ s : ZMod p, g (scale s T.val) * phase p ((-e * d) * s) := by
    rw [Finset.sum_comm]
    simp_rw [← Finset.mul_sum, determinant_character_sum p e he T.val T.property]
    have ht : (∑ V : Pair (ZMod p), g V *
        (if det T.val V = 0 then (p : ℂ) * phase p (-e * d * coordinate T.val V) else 0)) =
        (p : ℂ) * ∑ V : Pair (ZMod p),
          if det T.val V = 0 then g V * phase p ((-e * d) * coordinate T.val V) else 0 := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro V _
      split_ifs <;> ring
    rw [ht, sum_kernel_coordinates p T.val T.property g (-e * d)]
  simp_rw [hinner, mul_assoc, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro s _
  apply Finset.sum_congr rfl
  intro T _
  ring

end ZInQ.Contrib.HeckePrimeRationality.CoprimeProductTrace
