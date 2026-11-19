import ZInQKernel.Contrib.OneProof.RC.OldStageLaw.Grid
import Mathlib.Analysis.Normed.Ring.InfiniteSum
import Mathlib.Analysis.Complex.Periodic

/-! The product of the three line sums is the absolutely convergent sum over
lattice points, with each point counted once. -/

noncomputable section

set_option maxHeartbeats 1000000

namespace ZInQ.Manuscript.RC.OldStageLaw

open Complex
open UpperHalfPlane hiding I
open scoped BigOperators Real

abbrev GridPoint (a : Fin 3 → ℕ) := Grid a × (ℤ × ℤ × ℤ)

def intCoords (n : ℤ × ℤ × ℤ) : Fin 3 → ℤ := ![n.1, n.2.1, n.2.2]

def exponent {a : Fin 3 → ℕ} (p : GridPoint a) : ℝ :=
  ∑ i, (a i : ℝ) * ((intCoords p.2 i : ℝ) + offset p.1 i) ^ 2

private theorem hasSum_three {f g h : ℤ → ℂ} {A B C : ℂ}
    (hf : HasSum f A) (hg : HasSum g B) (hh : HasSum h C) :
    HasSum (fun n : ℤ × ℤ × ℤ => f n.1 * (g n.2.1 * h n.2.2)) (A * (B * C)) := by
  let gh (n : ℤ × ℤ) : ℂ := g n.1 * h n.2
  have hgh : Summable gh := summable_mul_of_summable_norm (f := g) (g := h)
    hg.summable.norm hh.summable.norm
  have hs : HasSum gh (B * C) := HasSum.mul (f := g) (g := h) hg hh hgh
  have hfgh : Summable (fun n : ℤ × (ℤ × ℤ) => f n.1 * gh n.2) :=
    summable_mul_of_summable_norm (f := f) (g := gh) hf.summable.norm hgh.norm
  exact HasSum.mul (f := f) (g := gh) hf hs hfgh

private theorem hasSum_finite_outer {A X : Type*} [Fintype A] {f : A → X → ℂ}
    {v : A → ℂ} (h : ∀ a, HasSum (f a) (v a)) :
    HasSum (fun p : A × X => f p.1 p.2) (∑ a, v a) := by
  have hs : Summable (fun p : A × X => f p.1 p.2) := by
    apply Summable.of_norm
    apply (summable_prod_of_nonneg (fun _ => norm_nonneg _)).mpr
    exact ⟨fun a => (h a).summable.norm, Summable.of_finite⟩
  exact ((hs.hasSum.prod_fiberwise h).unique (hasSum_fintype v)) ▸ hs.hasSum

private theorem kernel_add (z : ℂ) (t s : ℝ) : kernel z (t + s) = kernel z t * kernel z s := by
  rw [kernel, kernel, kernel, ← exp_add, ofReal_add, mul_add]

theorem gridTheta_hasSum {a : Fin 3 → ℕ} [∀ i, NeZero (2 * a i)]
    (ha : ∀ i, 0 < a i) (w : Grid a → ℂ) (z : ℍ) :
    HasSum (fun p : GridPoint a => w p.1 * kernel z (exponent p)) (gridTheta w z) := by
  classical
  let f (r : Grid a) (i : Fin 3) (n : ℤ) := kernel z ((a i : ℝ) * ((n : ℝ) + offset r i) ^ 2)
  have h (r : Grid a) (i : Fin 3) : HasSum (f r i) (line (a i) (offset r i) z) :=
    line_hasSum (Nat.cast_pos.mpr (ha i)) _ z
  let term (r : Grid a) (n : ℤ × ℤ × ℤ) := w r * (f r 0 n.1 * (f r 1 n.2.1 * f r 2 n.2.2))
  have hin (r : Grid a) : HasSum (term r) (w r * ∏ i, line (a i) (offset r i) z) := by
    simpa only [term, Fin.prod_univ_three, mul_assoc] using
      (hasSum_three (h r 0) (h r 1) (h r 2)).mul_left (w r)
  have ht : HasSum (fun p : GridPoint a => term p.1 p.2) (gridTheta w z) :=
    hasSum_finite_outer hin
  convert ht using 1
  funext p
  simp [term, f, exponent, intCoords, Fin.sum_univ_three, kernel_add, mul_assoc]

theorem kernel_nat (z : ℍ) (n : ℕ) :
    kernel z (n : ℝ) = Function.Periodic.qParam 1 (z : ℂ) ^ n := by
  rw [kernel, Function.Periodic.qParam, ofReal_natCast, ← exp_nat_mul]
  congr 1
  simp
  ring

#print axioms hasSum_three
#print axioms hasSum_finite_outer
#print axioms kernel_add
#print axioms gridTheta_hasSum
#print axioms kernel_nat

end ZInQ.Manuscript.RC.OldStageLaw
