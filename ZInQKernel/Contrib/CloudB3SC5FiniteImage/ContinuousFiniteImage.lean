import Mathlib.Analysis.Matrix.Normed
import Mathlib.Topology.Algebra.ClopenNhdofOne
import Mathlib.FieldTheory.Galois.Profinite
import Mathlib.FieldTheory.KrullTopology

/-! # Continuous homomorphisms from profinite groups to `GL_n(ℂ)` have finite image

Supporting edge for cluster C5 (not a proof of any open hypothesis). It shows that the
finite-image clause of a continuous `GL_n(ℂ)`-valued representation of a profinite group is
automatic, by the "no small subgroups" property of `GL_n(ℂ)`.

* `ZInQ.Contrib.CloudB3SC5FiniteImage.eq_one_of_norm_sub_one_pow_two_pow_le`: in a normed
  `ℝ`-algebra, if `‖g ^ (2 ^ k) - 1‖ ≤ r` for every `k` and some `r < 1`, then `g = 1`
  (from `g² - 1 = 2 (g - 1) + (g - 1)²`, so `‖g² - 1‖ ≥ (2 - r) ‖g - 1‖`).
* `ZInQ.Contrib.CloudB3SC5FiniteImage.finite_range_of_continuous`: a continuous homomorphism from
  a compact, zero-dimensional topological group to `GL n ℂ` has finite range.
* `ZInQ.Contrib.CloudB3SC5FiniteImage.finite_range_of_continuous_galQbar`: the same for
  `Gal(ℚ̄/ℚ)` with its Krull topology.

Uses Mathlib only.
-/

namespace ZInQ.Contrib.CloudB3SC5FiniteImage

/-- **No small subgroups, the squaring step.** In a normed `ℝ`-algebra, if every iterated square
`g ^ (2 ^ k)` stays within distance `r < 1` of `1`, then `g = 1`. -/
theorem eq_one_of_norm_sub_one_pow_two_pow_le {A : Type*} [NormedRing A] [NormedAlgebra ℝ A]
    {g : A} {r : ℝ} (hr : r < 1) (h : ∀ k : ℕ, ‖g ^ (2 ^ k) - 1‖ ≤ r) : g = 1 := by
  -- one squaring step
  have step : ∀ x : A, ‖x - 1‖ ≤ r → (2 - r) * ‖x - 1‖ ≤ ‖x ^ 2 - 1‖ := by
    intro x hx
    have hid : x ^ 2 - 1 = (2 : ℝ) • (x - 1) + (x - 1) * (x - 1) := by
      rw [two_smul]; noncomm_ring
    have h2 : ‖(2 : ℝ) • (x - 1)‖ = 2 * ‖x - 1‖ := by
      rw [norm_smul]; norm_num
    have hsq : ‖(x - 1) * (x - 1)‖ ≤ r * ‖x - 1‖ :=
      (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right hx (norm_nonneg _))
    have htri : ‖(2 : ℝ) • (x - 1)‖ - ‖(x - 1) * (x - 1)‖ ≤ ‖x ^ 2 - 1‖ := by
      rw [hid]
      have := norm_sub_le ((2 : ℝ) • (x - 1) + (x - 1) * (x - 1)) ((x - 1) * (x - 1))
      rw [add_sub_cancel_right] at this
      linarith
    nlinarith [h2, hsq, htri]
  -- iterate
  have grow : ∀ k : ℕ, (2 - r) ^ k * ‖g - 1‖ ≤ ‖g ^ (2 ^ k) - 1‖ := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      have e : g ^ (2 ^ (k + 1)) = (g ^ (2 ^ k)) ^ 2 := by
        rw [← pow_mul, pow_succ]
      rw [e, pow_succ, mul_comm ((2 - r) ^ k) (2 - r), mul_assoc]
      have h1 : 0 ≤ 2 - r := by linarith
      exact (mul_le_mul_of_nonneg_left ih h1).trans (step _ (h k))
  by_contra hne
  have hpos : 0 < ‖g - 1‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hne)
  have hr0 : 0 ≤ r := (norm_nonneg _).trans (h 0)
  obtain ⟨k, hk⟩ := pow_unbounded_of_one_lt (r / ‖g - 1‖) (by linarith : (1 : ℝ) < 2 - r)
  have := (grow k).trans (h k)
  rw [div_lt_iff₀ hpos] at hk
  linarith

/-- **Continuous homomorphisms from a profinite group to `GL_n(ℂ)` have finite range.** -/
theorem finite_range_of_continuous {G : Type*} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [CompactSpace G] [ZeroDimensionalSpace G]
    {n : Type*} [Fintype n] [DecidableEq n]
    (ρ : G →* GL n ℂ) (hρ : Continuous ρ) : (Set.range ρ).Finite := by
  -- the `ℓ^∞`-operator norm (a normed `ℝ`-algebra norm; its topology is the product topology)
  let _ : NormedRing (Matrix n n ℂ) := Matrix.linftyOpNormedRing
  let _ : NormedAlgebra ℝ (Matrix n n ℂ) := Matrix.linftyOpNormedAlgebra
  -- the neighbourhood `U` of `1` in `GL n ℂ` with no nontrivial subgroups
  set U : Set (GL n ℂ) := {g | ‖(g : Matrix n n ℂ) - 1‖ < 1 / 2} with hUdef
  have hUopen : IsOpen U := by
    have hc : Continuous fun g : GL n ℂ => ‖(g : Matrix n n ℂ) - 1‖ :=
      continuous_norm.comp (Units.continuous_val.sub continuous_const)
    exact isOpen_lt hc continuous_const
  have h1U : (1 : GL n ℂ) ∈ U := by
    simp [hUdef]
  obtain ⟨H, hH⟩ := ProfiniteGrp.exist_openNormalSubgroup_sub_open_nhds_of_one
    (hUopen.preimage hρ) (by simpa using h1U)
  -- `ρ` kills `H`
  have hker : H.toSubgroup ≤ ρ.ker := by
    intro h hh
    rw [MonoidHom.mem_ker]
    apply Units.ext
    refine eq_one_of_norm_sub_one_pow_two_pow_le (r := 1 / 2) (by norm_num) (fun k => ?_)
    have hmem : h ^ (2 ^ k) ∈ (H : Set G) := H.toSubgroup.pow_mem hh _
    have := hH hmem
    simp only [Set.mem_preimage, hUdef, Set.mem_ofPred_eq, map_pow, Units.val_pow_eq_pow_val] at this
    exact this.le
  have : H.toSubgroup.FiniteIndex := H.toOpenSubgroup.finiteIndex_of_finite_quotient
  have : ρ.ker.FiniteIndex := Subgroup.finiteIndex_of_le hker
  have hfin : Finite ρ.range :=
    Finite.of_equiv _ (QuotientGroup.quotientKerEquivRange ρ).toEquiv
  rw [← MonoidHom.coe_range]
  exact Set.toFinite _

/-- **The case `G_ℚ`.** Every continuous homomorphism `Gal(ℚ̄/ℚ) → GL_n(ℂ)` (Krull topology) has
finite range. -/
theorem finite_range_of_continuous_galQbar {n : Type*} [Fintype n] [DecidableEq n]
    (ρ : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) →* GL n ℂ) (hρ : Continuous ρ) :
    (Set.range ρ).Finite :=
  finite_range_of_continuous ρ hρ

end ZInQ.Contrib.CloudB3SC5FiniteImage
