import ZInQKernel.Contrib.OneProof.T21Proof.Brandt2

/-!
# t21-proof: `f_3(1) = ±3` for every test vector

Task t21-proof. `gT τ` is `−3` on the double coset `B^× H` of `1` (`H = ⟨U_3, ℚ̂^×⟩`) and `1` off it.
It lies in TYZ's `π_ℤ^{U_3}` (`InPiZ`): the three invariances hold by construction, and on TYZ's 8
representatives it takes the value `−3` exactly at `t = 0` and the partner `t*(s)` (`partner_mem`,
`twoRep_ne`), so both orthogonality sums vanish (`sums_check`). A test vector `f_3` generates
`π_ℤ^{U_3}`, so `gT = c f_3` with `c = ±1` (`gT` takes the value `1`), whence `f_3(1) = ±3`.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.style.longLine false
set_option linter.unusedSimpArgs false
set_option linter.deprecated false

noncomputable section

namespace ZInQ.Contrib.T21Proof

open ZInQ.Contrib.TYZDecomp.H29Split IsDedekindDomain NumberField
open scoped Quaternion
open ZInQ.RouteK.Rank5b

/-- The double coset `B^× H` of `1`. -/
def Dset (τ : QNeg 3 →ₐ[ℚ] ℍ[ℚ]) : Set ℍ[AQ] :=
  {y | ∃ γ : ℍ[ℚ], γ ≠ 0 ∧ ∃ h ∈ Hgrp τ, y = qι γ * ↑h}

open Classical in
/-- **The test vector at `n = 3`**: `−3` on `B^× H`, `1` elsewhere. -/
def gT (τ : QNeg 3 →ₐ[ℚ] ℍ[ℚ]) (y : ℍ[AQ]) : ℤ := if y ∈ Dset τ then -3 else 1

theorem one_mem_Dset (τ : QNeg 3 →ₐ[ℚ] ℍ[ℚ]) : (1 : ℍ[AQ]) ∈ Dset τ :=
  ⟨1, one_ne_zero, 1, Subgroup.one_mem _, by simp⟩

theorem qι_mul_mem_iff (τ : QNeg 3 →ₐ[ℚ] ℍ[ℚ]) {γ : ℍ[ℚ]} (hγ : γ ≠ 0) {x : ℍ[AQ]} :
    qι γ * x ∈ Dset τ ↔ x ∈ Dset τ := by
  constructor
  · rintro ⟨γ', hγ', h, hh, e⟩
    refine ⟨γ⁻¹ * γ', mul_ne_zero (inv_ne_zero hγ) hγ', h, hh, ?_⟩
    have : x = qι γ⁻¹ * (qι γ * x) := by
      rw [← mul_assoc, ← map_mul, inv_mul_cancel₀ hγ, map_one, one_mul]
    rw [this, e, map_mul, mul_assoc]
  · rintro ⟨γ', hγ', h, hh, rfl⟩
    exact ⟨γ * γ', mul_ne_zero hγ hγ', h, hh, by rw [map_mul, mul_assoc]⟩

theorem mul_unit_mem_iff (τ : QNeg 3 →ₐ[ℚ] ℍ[ℚ]) {x : ℍ[AQ]} {u : ℍ[AQ]ˣ} (hu : u ∈ Hgrp τ) :
    x * ↑u ∈ Dset τ ↔ x ∈ Dset τ := by
  constructor
  · rintro ⟨γ, hγ, h, hh, e⟩
    refine ⟨γ, hγ, h * u⁻¹, Subgroup.mul_mem _ hh (Subgroup.inv_mem _ hu), ?_⟩
    have : x = x * ↑u * ↑u⁻¹ := by rw [mul_assoc, Units.mul_inv, mul_one]
    rw [this, e, Units.val_mul, mul_assoc]
  · rintro ⟨γ, hγ, h, hh, rfl⟩
    exact ⟨γ, hγ, h * u, Subgroup.mul_mem _ hh hu, by rw [Units.val_mul, mul_assoc]⟩

theorem twoRepQ_zero : twoRepQ ((0, 0, 0) : Fin 2 × Fin 2 × Fin 2) = 1 := by
  ext <;> simp [twoRepQ]

theorem gT_twoRep {τ : QNeg 3 →ₐ[ℚ] ℍ[ℚ]} {s : Signs}
    (hs : τ ((ωK : 𝓞 (QNeg 3)) : QNeg 3) = ωq s) {v : HeightOneSpectrum (𝓞 ℚ)} (hv : IsPlaceTwo v)
    (t : Fin 2 × Fin 2 × Fin 2) :
    gT τ (twoRep v t) = if t = (0, 0, 0) ∨ t = tstar s then -3 else 1 := by
  classical
  by_cases h : t = (0, 0, 0) ∨ t = tstar s
  · rw [if_pos h, gT, if_pos]
    rcases h with rfl | rfl
    · rw [twoRep, twoRepQ_zero, ιAt_one]; exact one_mem_Dset τ
    · obtain ⟨h, hh, e⟩ := partner_mem hs hv
      exact ⟨1, one_ne_zero, h, hh, e⟩
  · rw [if_neg h, gT, if_neg]
    push_neg at h
    rintro ⟨γ, hγ, h', hh', e⟩
    exact twoRep_ne hv s t h.1 h.2 hγ (Hgrp_le_Sg hv hs hh') e

/-- **`gT τ ∈ π_ℤ^{U_3}`.** -/
theorem inPiZ_gT {τ : QNeg 3 →ₐ[ℚ] ℍ[ℚ]} (hτ : AdmissibleTau 3 τ) : InPiZ 3 τ (gT τ) := by
  classical
  obtain ⟨s, hs⟩ := admissible_signs hτ
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro γ hγ x
    simp only [gT, qι_mul_mem_iff τ hγ]
  · intro x u hu
    simp only [gT, mul_unit_mem_iff τ (Subgroup.subset_closure (Or.inl hu))]
  · intro x z
    have : algebraMap AQ ℍ[AQ] (z : AQ) =
        ((Units.map (algebraMap AQ ℍ[AQ]).toMonoidHom z : ℍ[AQ]ˣ) : ℍ[AQ]) := rfl
    rw [this]
    simp only [gT, mul_unit_mem_iff τ (Subgroup.subset_closure (Or.inr ⟨z, rfl⟩))]
  · intro v hv
    simp only [gT_twoRep hs hv]
    exact sums_check s

/-- **Every test vector `f_3` has `f_3(1) = ±3`.** -/
theorem testVector_one {τ : QNeg 3 →ₐ[ℚ] ℍ[ℚ]} (hτ : AdmissibleTau 3 τ) {f : ℍ[AQ] → ℤ}
    (hf : IsTestVector 3 τ f) : f 1 = 3 ∨ f 1 = -3 := by
  classical
  obtain ⟨c, hc⟩ := hf.2 (gT τ) (inPiZ_gT hτ)
  obtain ⟨s, hs⟩ := admissible_signs hτ
  obtain ⟨v, hv⟩ := exists_isPlaceTwo
  have h1 : gT τ 1 = -3 := by rw [gT, if_pos (one_mem_Dset τ)]
  have e1 := hc 1
  rw [Units.val_one, h1] at e1
  set t₁ : Fin 2 × Fin 2 × Fin 2 := (1, 0, 0)
  have ht0 : t₁ ≠ (0, 0, 0) := by decide
  have hts : t₁ ≠ tstar s := by
    intro h
    have := congrArg (fun x => x.2.2) h
    simp [tstar, t₁] at this
  have h2 := gT_twoRep hs hv t₁
  rw [if_neg (by push_neg; exact ⟨ht0, hts⟩)] at h2
  have e2 := hc (ιAtU v (twoRepQ t₁) (twoRepQ_ne_zero t₁))
  have : ((ιAtU v (twoRepQ t₁) (twoRepQ_ne_zero t₁) : ℍ[AQ]ˣ) : ℍ[AQ]) = twoRep v t₁ := rfl
  rw [this, h2] at e2
  rcases Int.eq_one_or_neg_one_of_mul_eq_one' e2.symm with ⟨rfl, _⟩ | ⟨rfl, _⟩
  · right; linarith
  · left; linarith

end ZInQ.Contrib.T21Proof
