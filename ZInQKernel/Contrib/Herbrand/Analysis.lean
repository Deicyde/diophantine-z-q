import ZInQKernel.HDecomp.Conductor.ArtinUpper

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described at
https://www.apache.org/licenses/LICENSE-2.0 .
Authors: The Tau Ceti contributors

Modified for this project: the analytic core of
TauCeti/NumberTheory/LocalField/Herbrand/Basic.lean at
 a6027b1d24fcb935c53bd5b50d11b40991cda418
is proved here for the actual `PkgI6` ring filtration and interval integral on
Mathlib 4.35, with no local-field/finite-residue hypothesis. See
`docs/research/t22-herbrand.md` for exact provenance and scope.
-/

namespace ZInQ.Contrib.Herbrand

open IsLocalRing MeasureTheory Set intervalIntegral

section RealFiltration

variable (A B : Type) [CommRing A] [CommRing B] [Algebra A B] [IsLocalRing B]

/-- The real lower numbering is constant on `(i-1,i]`, including `i=0`.
The ceiling, not the floor, is essential at the right endpoint. -/
theorem lowerRamR_eq_of_sub_one_lt_of_le {i : ℕ} {u : ℝ}
    (hleft : (i : ℝ) - 1 < u) (hright : u ≤ i) :
    PkgI6.lowerRamR A B u = PkgI6.lowerRam A B i := by
  have hu : ¬ u ≤ -1 := by have := Nat.cast_nonneg (α := ℝ) i; linarith
  have hi : ⌈u⌉ = (i : ℤ) := Int.ceil_eq_iff.mpr ⟨by exact_mod_cast hleft, by exact_mod_cast hright⟩
  simp [PkgI6.lowerRamR, hu, hi]

/-- The lower subgroup rule extends to every real index, not just natural indices. -/
theorem lowerRamR_tower (C : Type) [CommRing C] [Algebra A C] [Algebra C B]
    [IsScalarTower A C B] (u : ℝ) :
    PkgI6.lowerRamR C B u =
      (PkgI6.lowerRamR A B u).comap (AlgEquiv.restrictScalarsHom A) := by
  unfold PkgI6.lowerRamR
  split_ifs with hu
  · simp
  · exact PkgI6.lowerRam_tower A B C _

end RealFiltration

section Analysis

variable (A B : Type) [CommRing A] [CommRing B] [Algebra A B] [IsLocalRing B]
  [Finite (B ≃ₐ[A] B)]

/-- On any interval with constant actual lower group, the actual integral is affine. -/
theorem herbrandPhi_sub_of_forall_eq {a b : ℝ} (hab : a ≤ b)
    {H : Subgroup (B ≃ₐ[A] B)}
    (h : ∀ t : ℝ, a < t → t ≤ b → PkgI6.lowerRamR A B t = H) :
    PkgI6.herbrandPhi A B b - PkgI6.herbrandPhi A B a =
      (b - a) * (Nat.card H / Nat.card (PkgI6.lowerRamR A B 0)) := by
  rw [PkgI6.herbrandPhi_eq, PkgI6.herbrandPhi_eq, integral_interval_sub_left
    (PkgI6.hInt_anti A B).intervalIntegrable (PkgI6.hInt_anti A B).intervalIntegrable,
    ← smul_eq_mul, ← intervalIntegral.integral_const]
  refine integral_congr_ae (Filter.Eventually.of_forall fun t ht => ?_)
  rw [uIoc_of_le hab] at ht
  rw [PkgI6.hInt, h t ht.1 ht.2]

theorem continuous_herbrandPhi : Continuous (PkgI6.herbrandPhi A B) :=
  continuous_primitive (fun _ _ => (PkgI6.hInt_anti A B).intervalIntegrable) 0

theorem strictMono_herbrandPhi : StrictMono (PkgI6.herbrandPhi A B) :=
  fun _ _ h => PkgI6.phi_strictMono A B h

/-- The `-1` endpoint is included. The whole group occurs only at that endpoint;
on `(-1,0]` the density is `|G₀|/|G₀|=1`. -/
theorem herbrandPhi_of_le_zero {u : ℝ} (h₁ : -1 ≤ u) (h₀ : u ≤ 0) :
    PkgI6.herbrandPhi A B u = u := by
  have h := herbrandPhi_sub_of_forall_eq A B (a := u) (b := 0) h₀
    (H := PkgI6.lowerRam A B 0) fun t ht₁ ht₂ =>
      lowerRamR_eq_of_sub_one_lt_of_le A B (i := 0) (by simpa using h₁.trans_lt ht₁)
        (by simpa using ht₂)
  have hzero : PkgI6.lowerRamR A B 0 = PkgI6.lowerRam A B 0 := by
    simpa using PkgI6.lowerRamR_nat A B 0
  rw [hzero, div_self (by exact_mod_cast Nat.card_pos.ne'), PkgI6.phi_zero] at h
  linarith

/-- The actual integral takes the whole required half-line onto itself. -/
theorem exists_herbrandPhi_eq {v : ℝ} (hv : -1 ≤ v) :
    ∃ u : ℝ, -1 ≤ u ∧ PkgI6.herbrandPhi A B u = v := by
  set g : ℝ := (Nat.card (PkgI6.lowerRamR A B 0) : ℝ)
  have hg : 0 < g := PkgI6.g0_pos A B
  set b : ℝ := -1 + (v + 1) * g
  have hb : -1 ≤ b := by nlinarith
  have hφb : v ≤ PkgI6.herbrandPhi A B b := by
    have h := PkgI6.phi_sub_ge A B hb
    have hge := PkgI6.hInt_ge A B b
    have hsub : b - -1 = (v + 1) * g := by dsimp [b]; ring
    have hbound : (b - -1) / g ≤
        PkgI6.herbrandPhi A B b - PkgI6.herbrandPhi A B (-1) := by
      calc (b - -1) / g = (b - -1) * (1 / g) := by ring
        _ ≤ (b - -1) * PkgI6.hInt A B b :=
          mul_le_mul_of_nonneg_left hge (by linarith)
        _ ≤ _ := h
    rw [herbrandPhi_of_le_zero A B le_rfl (by norm_num), hsub,
      mul_div_cancel_right₀ _ hg.ne'] at hbound
    linarith
  obtain ⟨u, hu, hφ⟩ := intermediate_value_Icc hb (continuous_herbrandPhi A B).continuousOn
    ⟨(herbrandPhi_of_le_zero A B le_rfl (by norm_num)).trans_le hv, hφb⟩
  exact ⟨u, hu.1, hφ⟩

/-- The actual sInf inverse recovers every real lower index in the required domain. -/
theorem upperRam_herbrandPhi {u : ℝ} (hu : -1 ≤ u) :
    PkgI6.upperRam A B (PkgI6.herbrandPhi A B u) = PkgI6.lowerRamR A B u := by
  have hleast : IsLeast {t : ℝ | -1 ≤ t ∧
      PkgI6.herbrandPhi A B u ≤ PkgI6.herbrandPhi A B t} u := by
    refine ⟨⟨hu, le_rfl⟩, ?_⟩
    rintro t ⟨_, ht⟩
    exact (strictMono_herbrandPhi A B).le_iff_le.mp ht
  simp only [PkgI6.upperRam, hleast.csInf_eq]

/-- For indices below `-1` the baseline's total upper filtration is the whole group. -/
theorem upperRam_of_le_neg_one {v : ℝ} (hv : v ≤ -1) : PkgI6.upperRam A B v = ⊤ := by
  have hleast : IsLeast {u : ℝ | -1 ≤ u ∧ v ≤ PkgI6.herbrandPhi A B u} (-1) := by
    refine ⟨⟨le_rfl, ?_⟩, fun u hu => hu.1⟩
    simpa only [herbrandPhi_of_le_zero A B le_rfl (by norm_num)] using hv
  simp [PkgI6.upperRam, hleast.csInf_eq, PkgI6.lowerRamR]

/-- On `[-1,0]` the actual upper and lower numberings agree. -/
theorem upperRam_of_mem_neg_one_zero {v : ℝ} (hv : -1 ≤ v) (hv₀ : v ≤ 0) :
    PkgI6.upperRam A B v = PkgI6.lowerRamR A B v := by
  simpa only [herbrandPhi_of_le_zero A B hv hv₀] using upperRam_herbrandPhi A B hv

/-- The affine formula on `[m,m+1]`, with the baseline's ceiling convention. -/
theorem herbrandPhi_of_mem_Icc (m : ℕ) {u : ℝ} (h₁ : (m : ℝ) ≤ u)
    (h₂ : u ≤ m + 1) :
    PkgI6.herbrandPhi A B u =
      (∑ i ∈ Finset.Icc 1 m, (Nat.card (PkgI6.lowerRam A B i) : ℝ) +
        (u - m) * Nat.card (PkgI6.lowerRam A B (m + 1))) /
        Nat.card (PkgI6.lowerRam A B 0) := by
  have hstep := herbrandPhi_sub_of_forall_eq A B h₁
    (H := PkgI6.lowerRam A B (m + 1)) fun t ht₁ ht₂ =>
      lowerRamR_eq_of_sub_one_lt_of_le A B (by push_cast; linarith) (by push_cast; linarith)
  have hzero : PkgI6.lowerRamR A B 0 = PkgI6.lowerRam A B 0 := by
    simpa using PkgI6.lowerRamR_nat A B 0
  rw [hzero] at hstep
  induction m generalizing u with
  | zero =>
    rw [Nat.cast_zero, PkgI6.phi_zero] at hstep
    rw [Finset.Icc_eq_empty (by norm_num), Finset.sum_empty]
    linear_combination hstep
  | succ n ih =>
    have hstepn := herbrandPhi_sub_of_forall_eq A B (a := (n : ℝ)) (b := (n + 1 : ℕ))
      (by push_cast; linarith) (H := PkgI6.lowerRam A B (n + 1)) fun t ht₁ ht₂ =>
        lowerRamR_eq_of_sub_one_lt_of_le A B (i := n + 1)
          (by simpa only [Nat.cast_add, Nat.cast_one, add_sub_cancel_right] using ht₁) ht₂
    rw [hzero] at hstepn
    have hn := ih (u := (n + 1 : ℕ)) (by push_cast; linarith) (by push_cast; linarith) hstepn
    rw [Finset.sum_Icc_succ_top (by omega)]
    rw [hn] at hstep
    push_cast at hstep ⊢
    linear_combination hstep

theorem herbrandPhi_nat (m : ℕ) :
    PkgI6.herbrandPhi A B m =
      (∑ i ∈ Finset.Icc 1 m, (Nat.card (PkgI6.lowerRam A B i) : ℝ)) /
        Nat.card (PkgI6.lowerRam A B 0) := by
  rw [herbrandPhi_of_mem_Icc A B m le_rfl (by linarith), sub_self, zero_mul, add_zero]

end Analysis

end ZInQ.Contrib.Herbrand

#print axioms ZInQ.Contrib.Herbrand.herbrandPhi_of_le_zero
#print axioms ZInQ.Contrib.Herbrand.exists_herbrandPhi_eq
#print axioms ZInQ.Contrib.Herbrand.upperRam_herbrandPhi
#print axioms ZInQ.Contrib.Herbrand.herbrandPhi_of_mem_Icc
