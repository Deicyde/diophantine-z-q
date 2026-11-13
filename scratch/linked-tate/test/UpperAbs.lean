import Mathlib

noncomputable section
namespace UATest
variable {p : ℕ} [Fact p.Prime]
abbrev GQp (p : ℕ) [Fact p.Prime] := PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p
abbrev Kbar (p : ℕ) [Fact p.Prime] := PadicAlgCl p
abbrev Fld (p : ℕ) [Fact p.Prime] := IntermediateField ℚ_[p] (Kbar p)
def inertiaSet : Set (GQp p) := {σ | ∀ x : Kbar p, ‖x‖ ≤ 1 → ‖σ x - x‖ < 1}
def IsUnif (L : Fld p) (ϖ : Kbar p) : Prop :=
  ϖ ∈ L ∧ ‖ϖ‖ < 1 ∧ ∀ y ∈ L, ‖y‖ < 1 → ‖y‖ ≤ ‖ϖ‖
def ramSet (L : Fld p) (i : ℕ) : Set (GQp p) :=
  {σ | ∃ ϖ, IsUnif L ϖ ∧ ∀ x ∈ L, ‖x‖ ≤ 1 → ‖σ x - x‖ ≤ ‖ϖ‖ ^ (i + 1)}
def restr (L : Fld p) (σ : GQp p) : L → Kbar p := fun x => σ x
def ramCard (L : Fld p) (i : ℕ) : ℕ := Nat.card (restr L '' ramSet L i)
def IsFinGal (L : Fld p) : Prop := FiniteDimensional ℚ_[p] L ∧ IsGalois ℚ_[p] L
def ramSetR (L : Fld p) (t : ℝ) : Set (GQp p) :=
  if t ≤ -1 then Set.univ else ramSet L ⌈t⌉.toNat
def ramCardR (L : Fld p) (t : ℝ) : ℕ := Nat.card (restr L '' ramSetR L t)
def phiAt (L : Fld p) (u : ℝ) : ℝ :=
  ∫ t in (0 : ℝ)..u, (ramCardR L t : ℝ) / (ramCard L 0 : ℝ)
def upperSet (L : Fld p) (v : ℝ) : Set (GQp p) :=
  ramSetR L (sInf {u : ℝ | -1 ≤ u ∧ v ≤ phiAt L u})
def upperAbs (p : ℕ) [Fact p.Prime] (v : ℝ) : Set (GQp p) :=
  {σ | ∀ L : Fld p, IsFinGal L → σ ∈ upperSet L v}

theorem phiAt_nonpos (L : Fld p) {u : ℝ} (hu : u ≤ 0) : phiAt L u ≤ 0 := by
  unfold phiAt
  rw [intervalIntegral.integral_symm]
  have : 0 ≤ ∫ t in u..(0 : ℝ), (ramCardR L t : ℝ) / (ramCard L 0 : ℝ) :=
    intervalIntegral.integral_nonneg hu (fun _ _ => by positivity)
  linarith

theorem sInf_nonneg_of_pos (L : Fld p) {t : ℝ} (ht : 0 < t) :
    0 ≤ sInf {u : ℝ | -1 ≤ u ∧ t ≤ phiAt L u} := by
  rcases Set.eq_empty_or_nonempty {u : ℝ | -1 ≤ u ∧ t ≤ phiAt L u} with h | h
  · rw [h, Real.sInf_empty]
  · apply le_csInf h
    rintro u ⟨-, hu⟩
    by_contra hneg
    push Not at hneg
    have := phiAt_nonpos L hneg.le
    linarith

theorem upperSet_sub (L : Fld p) {t : ℝ} (ht : 0 < t) (σ : GQp p) (hσ : σ ∈ upperSet L t) :
    ∀ x ∈ L, ‖x‖ ≤ 1 → ‖σ x - x‖ < 1 := by
  have h0 := sInf_nonneg_of_pos L ht
  unfold upperSet ramSetR at hσ
  rw [if_neg (show ¬ _ ≤ (-1 : ℝ) by linarith)] at hσ
  obtain ⟨ϖ, hϖ, hle⟩ := hσ
  intro x hx hx1
  refine lt_of_le_of_lt (hle x hx hx1) ?_
  exact pow_lt_one₀ (norm_nonneg _) hϖ.2.1 (Nat.succ_ne_zero _)

theorem upperAbs_subset_inertiaSet (t : ℝ) (ht : 0 < t) :
    upperAbs p t ⊆ (inertiaSet : Set (GQp p)) := by
  intro σ hσ x hx
  let K : Fld p := IntermediateField.adjoin ℚ_[p] {x}
  haveI hKfin : FiniteDimensional ℚ_[p] K :=
    IntermediateField.adjoin.finiteDimensional (Algebra.IsIntegral.isIntegral x)
  let L : Fld p := IntermediateField.normalClosure ℚ_[p] K (Kbar p)
  have hL : IsFinGal L := ⟨inferInstance, inferInstance⟩
  have hxL : x ∈ L := IntermediateField.le_normalClosure K (IntermediateField.mem_adjoin_simple_self ℚ_[p] x)
  exact upperSet_sub L ht σ (hσ L hL) x hxL hx

end UATest
