import ZInQKernel.HDecomp.Conductor.I6Base

/-! Glue of `docs/research/h-decomposition.md`, adopted by task hdec-adopt from
`scratch/glue-I6-rest/Conductor.lean`.
The literature leaves are hypotheses (`def … : Prop`); no `sorry`, no `axiom`. -/


/-!
# glue-I6-rest: D4, `artinConductor_le_of_upper`, over pkg-I6's definitions

The definitions `lowerRam`, `lowerRamR`, `herbrandPhi`, `upperRam`, `codimInv`, `artinConductor`
are imported from `I6Base` (pkg-I6, Part II).
-/

namespace PkgI6

section Conductor

variable (A B : Type) [CommRing A] [CommRing B] [Algebra A B] [IsLocalRing B]

open IsLocalRing

section Proof

open intervalIntegral

variable [Finite (B ≃ₐ[A] B)]

lemma lowerRam_anti {i j : ℕ} (h : i ≤ j) : lowerRam A B j ≤ lowerRam A B i := by
  intro σ hσ x
  exact Ideal.pow_le_pow_right (by omega) (hσ x)

lemma lowerRamR_anti : Antitone (lowerRamR A B) := by
  intro u u' h
  unfold lowerRamR
  split_ifs with h1 h2 h2
  · exact le_rfl
  · exfalso; linarith
  · exact le_top
  · exact lowerRam_anti A B (Int.toNat_le_toNat (Int.ceil_mono h))

lemma lowerRamR_nat (i : ℕ) : lowerRamR A B i = lowerRam A B i := by
  have : ¬ ((i : ℝ) ≤ -1) := by have := i.cast_nonneg (α := ℝ); linarith
  simp [lowerRamR, this]

/-- The integrand of `herbrandPhi`. -/
noncomputable def hInt (t : ℝ) : ℝ :=
  (Nat.card (lowerRamR A B t) : ℝ) / (Nat.card (lowerRamR A B 0) : ℝ)

lemma g0_pos : (0 : ℝ) < Nat.card (lowerRamR A B 0) := by
  exact_mod_cast Nat.card_pos

lemma hInt_anti : Antitone (hInt A B) := by
  intro u u' h
  unfold hInt
  have := Subgroup.card_le_of_le (lowerRamR_anti A B h)
  gcongr

lemma hInt_ge (t : ℝ) : 1 / (Nat.card (lowerRamR A B 0) : ℝ) ≤ hInt A B t := by
  unfold hInt
  have : (1 : ℝ) ≤ Nat.card (lowerRamR A B t) := by exact_mod_cast Nat.card_pos
  gcongr

lemma hInt_zero : hInt A B 0 = 1 := by
  unfold hInt; exact div_self (g0_pos A B).ne'

lemma herbrandPhi_eq (u : ℝ) : herbrandPhi A B u = ∫ t in (0 : ℝ)..u, hInt A B t := rfl

/-- `φ(u') − φ(u) ≥ (u' − u)·h(u')` for `u ≤ u'` (the integrand is antitone). -/
lemma phi_sub_ge {u u' : ℝ} (h : u ≤ u') :
    (u' - u) * hInt A B u' ≤ herbrandPhi A B u' - herbrandPhi A B u := by
  rw [herbrandPhi_eq, herbrandPhi_eq, integral_interval_sub_left
    (hInt_anti A B).intervalIntegrable (hInt_anti A B).intervalIntegrable]
  have h1 := integral_mono_on h
    (intervalIntegrable_const : IntervalIntegrable (fun _ => hInt A B u') MeasureTheory.volume u u')
    (hInt_anti A B).intervalIntegrable
    (fun x hx => (hInt_anti A B) hx.2)
  simpa [mul_comm] using h1

lemma phi_strictMono {u u' : ℝ} (h : u < u') : herbrandPhi A B u < herbrandPhi A B u' := by
  have h1 := phi_sub_ge A B h.le
  have h2 : 0 < hInt A B u' := lt_of_lt_of_le (by have := g0_pos A B; positivity) (hInt_ge A B u')
  have : 0 < (u' - u) * hInt A B u' := mul_pos (by linarith) h2
  linarith

lemma upperRam_phi_nat (b : ℕ) : upperRam A B (herbrandPhi A B b) = lowerRam A B b := by
  unfold upperRam
  have hb : IsLeast {u : ℝ | -1 ≤ u ∧ herbrandPhi A B b ≤ herbrandPhi A B u} (b : ℝ) := by
    refine ⟨⟨by have := b.cast_nonneg (α := ℝ); linarith, le_rfl⟩, ?_⟩
    rintro u ⟨-, hu⟩
    by_contra hlt
    push Not at hlt
    exact absurd hu (not_le.mpr (phi_strictMono A B hlt))
  rw [hb.csInf_eq, lowerRamR_nat]

lemma phi_zero : herbrandPhi A B 0 = 0 := by simp [herbrandPhi]

/-- `∑_{i ≤ b} |G_i|/|G_0| ≤ 1 + φ(b)`. -/
lemma sum_hInt_le (b : ℕ) :
    ∑ i ∈ Finset.range (b + 1), hInt A B i ≤ 1 + herbrandPhi A B b := by
  induction b with
  | zero => simp [hInt_zero, phi_zero]
  | succ n ih =>
    rw [Finset.sum_range_succ]
    have := phi_sub_ge A B (u := n) (u' := (n + 1 : ℕ)) (by push_cast; linarith)
    push_cast at this ⊢
    nlinarith

lemma phi_nat_ge (i : ℕ) : (i : ℝ) / Nat.card (lowerRamR A B 0) ≤ herbrandPhi A B i := by
  have h1 := phi_sub_ge A B (u := 0) (u' := i) i.cast_nonneg
  have h2 := hInt_ge A B i
  rw [phi_zero, sub_zero, sub_zero] at h1
  have : (i : ℝ) * (1 / Nat.card (lowerRamR A B 0)) ≤ i * hInt A B i :=
    mul_le_mul_of_nonneg_left h2 i.cast_nonneg
  calc (i : ℝ) / Nat.card (lowerRamR A B 0) = i * (1 / Nat.card (lowerRamR A B 0)) := by ring
    _ ≤ _ := this.trans h1

lemma codimInv_eq_zero {k V : Type} [Field k] [AddCommGroup V] [Module k V]
    (ρ : Representation k (B ≃ₐ[A] B) V) (H : Subgroup (B ≃ₐ[A] B)) (h : ∀ σ ∈ H, ρ σ = 1) :
    codimInv A B ρ H = 0 := by
  unfold codimInv
  have htop : Representation.invariants (ρ.comp H.subtype) = ⊤ := by
    rw [Submodule.eq_top_iff']
    intro v
    rw [Representation.mem_invariants]
    intro g
    simp [h g.1 g.2]
  rw [htop, finrank_top, Nat.sub_self]

lemma codimInv_le {k V : Type} [Field k] [AddCommGroup V] [Module k V]
    (ρ : Representation k (B ≃ₐ[A] B) V) (H : Subgroup (B ≃ₐ[A] B)) :
    codimInv A B ρ H ≤ Module.finrank k V := Nat.sub_le _ _

/-- **D4 (GLUE, proved).** pkg-I6's `artinConductor_le_of_upper`. -/
theorem artinConductor_le_of_upper {k V : Type} [Field k] [AddCommGroup V] [Module k V]
    [FiniteDimensional k V]
    (ρ : Representation k (B ≃ₐ[A] B) V) (U : ℝ) (hU : 0 ≤ U)
    (h : ∀ v : ℝ, U < v → ∀ σ ∈ upperRam A B v, ρ σ = 1) :
    (artinConductor A B ρ : ℝ) ≤ Module.finrank k V * (1 + U) := by
  set g0 : ℝ := (Nat.card (lowerRamR A B 0) : ℝ)
  have hg0 := g0_pos A B
  -- indices with nonzero codimension satisfy φ(i) ≤ U
  have hφ : ∀ i : ℕ, codimInv A B ρ (lowerRam A B i) ≠ 0 → herbrandPhi A B i ≤ U := by
    intro i hi
    by_contra hlt
    push Not at hlt
    apply hi
    apply codimInv_eq_zero
    intro σ hσ
    exact h _ hlt σ (by rw [upperRam_phi_nat]; exact hσ)
  set n : ℕ := ⌊U * g0⌋₊ + 1
  have hsupp : ∀ i, n ≤ i → codimInv A B ρ (lowerRam A B i) = 0 := by
    intro i hi
    by_contra hne
    have h1 := (phi_nat_ge A B i).trans (hφ i hne)
    have h2 : (i : ℝ) ≤ U * g0 := by rwa [div_le_iff₀ hg0] at h1
    have h3 : (i : ℝ) < n := by
      have := Nat.lt_floor_add_one (U * g0)
      push_cast [n]; linarith
    have : i < n := by exact_mod_cast h3
    omega
  -- the coefficient in ℚ cast to ℝ is `hInt i`
  have h0 : lowerRamR A B 0 = lowerRam A B 0 := by simpa using lowerRamR_nat A B 0
  have hcoef : ∀ i : ℕ, (((Nat.card (lowerRam A B i) : ℚ) / Nat.card (lowerRam A B 0) : ℚ) : ℝ)
      = hInt A B i := by
    intro i
    simp only [hInt, lowerRamR_nat, h0]
    push_cast; rfl
  have hfin : artinConductor A B ρ = ∑ i ∈ Finset.range n,
      ((Nat.card (lowerRam A B i) : ℚ) / Nat.card (lowerRam A B 0)) *
        (codimInv A B ρ (lowerRam A B i) : ℚ) := by
    unfold artinConductor
    apply finsum_eq_sum_of_support_subset
    intro i hi
    rw [Function.mem_support] at hi
    simp only [Finset.coe_range, Set.mem_Iio]
    by_contra hni
    push Not at hni
    exact hi (by rw [hsupp i hni]; simp)
  have hInt_nn : ∀ t, 0 ≤ hInt A B t := fun t =>
    le_trans (by positivity) (hInt_ge A B t)
  set d : ℝ := (Module.finrank k V : ℝ)
  set T := (Finset.range n).filter (fun i : ℕ => herbrandPhi A B (i : ℝ) ≤ U)
  have hT : ∑ i ∈ T, hInt A B i ≤ 1 + U := by
    rcases T.eq_empty_or_nonempty with hE | hne
    · rw [hE, Finset.sum_empty]; linarith
    · set M := T.max' hne
      have hMT : M ∈ T := T.max'_mem hne
      have hsub : T ⊆ Finset.range (M + 1) := by
        intro i hi
        have := T.le_max' i hi
        simp only [Finset.mem_range]; omega
      calc ∑ i ∈ T, hInt A B i ≤ ∑ i ∈ Finset.range (M + 1), hInt A B i :=
            Finset.sum_le_sum_of_subset_of_nonneg hsub (fun i _ _ => hInt_nn i)
        _ ≤ 1 + herbrandPhi A B M := sum_hInt_le A B M
        _ ≤ 1 + U := by linarith [(Finset.mem_filter.mp hMT).2]
  rw [hfin, Rat.cast_sum]
  calc ∑ i ∈ Finset.range n, ((((Nat.card (lowerRam A B i) : ℚ) / Nat.card (lowerRam A B 0)) *
        (codimInv A B ρ (lowerRam A B i) : ℚ) : ℚ) : ℝ)
      = ∑ i ∈ Finset.range n, hInt A B i * (codimInv A B ρ (lowerRam A B i) : ℝ) := by
        refine Finset.sum_congr rfl (fun i _ => ?_)
        rw [Rat.cast_mul, hcoef, Rat.cast_natCast]
    _ = ∑ i ∈ T, hInt A B i * (codimInv A B ρ (lowerRam A B i) : ℝ) := by
        refine (Finset.sum_filter_of_ne (fun i _ hi => ?_)).symm
        apply hφ i
        intro hc; apply hi; rw [hc]; simp
    _ ≤ ∑ i ∈ T, hInt A B i * d := by
        refine Finset.sum_le_sum (fun i _ => ?_)
        exact mul_le_mul_of_nonneg_left (Nat.cast_le.mpr (codimInv_le A B ρ _) :
          ((codimInv A B ρ (lowerRam A B i) : ℕ) : ℝ) ≤ (Module.finrank k V : ℝ)) (hInt_nn i)
    _ = d * ∑ i ∈ T, hInt A B i := by
        rw [Finset.mul_sum]; exact Finset.sum_congr rfl (fun _ _ => by ring)
    _ ≤ d * (1 + U) := mul_le_mul_of_nonneg_left hT (Nat.cast_nonneg _)

end Proof

end Conductor

end PkgI6

