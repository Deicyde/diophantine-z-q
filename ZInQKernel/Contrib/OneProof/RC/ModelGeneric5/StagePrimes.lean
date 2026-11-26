import Mathlib.NumberTheory.ModularForms.LevelOne.DimensionFormula
import ZInQKernel.Contrib.RC53Assist.NewformGlueG0.HeckeBridge
import ZInQKernel.Contrib.OneProof.RC.StageKummer.Reference

/-! The stage-prime hypotheses of the pinned model `ModelNeron.source h₅ htame h₂`
at `ell := (s.q.stage i).p`, `N := StageKummer.level ℓ`.

* `EcurveZ_disc`: `Δ(E_ℓ) = 2304 ℓ⁶` on the integral model `⟨0, 2ℓ, 0, −3ℓ², 0⟩`.
* `stagePrime_five_le` (`h₅`): every stage prime is at least `5`; it is odd
  (`p ≡ 3 mod 4`) and of good reduction for the integral model, and `3 ∣ 2304`.
* `stagePrime_not_dvd_tame` (`htame`): if the exclusion set of the stage sequence
  contains the primes of `N φ(N)`, no stage prime divides `N φ(N)`. The manuscript
  chooses the place for `l₀` to "exclude two, all bad primes, the support of
  `D_w h_*` and any other finite set" (tex 8366–8368).
* `two_le_newformLevel` (`h₂` from `hN`): a positive newform level is at least `2`,
  since weight-two cusp forms of level one vanish and `a₁(E) = 1`. -/

noncomputable section

open WeierstrassCurve
open ZInQ.Manuscript.RC.Wiring ZInQ.Manuscript.RC.Stages
open scoped MatrixGroups

set_option autoImplicit false
set_option linter.style.haveILetI false

namespace ZInQ.Manuscript.RC.ModelGeneric5

/-- The discriminant of the integral model of `E_ℓ`: `b₂ = 8ℓ`, `b₄ = −6ℓ²`, `b₆ = 0`,
`b₈ = −9ℓ⁴`, so `Δ = 576ℓ⁶ + 1728ℓ⁶ = 2⁸·3²·ℓ⁶`. -/
theorem EcurveZ_disc (ℓ : ℕ) : (EcurveZ ℓ).Δ = 2304 * (ℓ : ℤ) ^ 6 := by
  simp only [EcurveZ, WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄,
    WeierstrassCurve.b₆, WeierstrassCurve.b₈]
  ring

section Stages

open ZInQ.Manuscript.RC.StageKummer ZInQ.Contrib.CloudB3RC53.GenusOdd

variable {ℓ : ℕ} {W : WData ℓ} {I : GenusOddInstance W} {L : ℕ} (s : Setup I L)

/-- Each stage prime is of good reduction for the integral model of `E_ℓ`
(the existing `StageKummer.stageGood`, applied to the setup's own sequence). -/
theorem stagePrime_not_dvd_disc (i : ℕ) :
    ¬ ((s.q.stage i).p : ℤ) ∣ (EcurveZ ℓ).Δ := by
  letI := s.eE; letI := s.eA
  exact stageGood (EcurveZ_baseChange ℓ) rfl rfl s.dat s.w s.hQw s.q i

/-- **`h₅` at every stage prime**: `5 ≤ p`. The prime is `3 mod 4` (`stage_mod_four`)
and does not divide `Δ(E_ℓ) = 2304 ℓ⁶`, while `3 ∣ 2304`. -/
theorem stagePrime_five_le (i : ℕ) : 5 ≤ (s.q.stage i).p := by
  have hp := (s.q.stage i).prime
  have h4 := stage_mod_four s i
  have hgood := stagePrime_not_dvd_disc s i
  rw [EcurveZ_disc] at hgood
  by_contra h
  have h3 : (s.q.stage i).p = 3 := by have := hp.two_le; omega
  apply hgood
  rw [h3]
  exact Dvd.dvd.mul_right (by norm_num) _

/-- **`htame` at every stage prime**: if the exclusion set `s.B` of the stage sequence
contains the prime factors of `N φ(N)`, then no stage prime divides `N φ(N)`
(the sequence avoids `s.B` by `StageSequence.excluded`). -/
theorem stagePrime_not_dvd_tame {N : ℕ} (hN : 0 < N)
    (hB : (N * N.totient).primeFactors ⊆ s.B) (i : ℕ) :
    ¬ (s.q.stage i).p ∣ N * N.totient := by
  intro h
  apply s.q.excluded i
  apply hB
  exact Nat.mem_primeFactors.mpr ⟨(s.q.stage i).prime, h,
    Nat.mul_ne_zero hN.ne' (Nat.totient_pos.mpr hN).ne'⟩

end Stages

/-- The exclusion set used by `exists_detector_stages` contains the chosen finite set. -/
theorem subset_stageExclusions (ℓ : ℕ) (Dw hstar : ℤ) (B : Finset ℕ) :
    B ⊆ stageExclusions ℓ Dw hstar B := by
  intro p hp
  simp only [stageExclusions, Finset.mem_union]
  exact Or.inl (Or.inl (Or.inl hp))

/-- So for every `N > 0`, the sequences of `exists_detector_stages` at the finite set
`(N φ(N)).primeFactors` avoid every prime dividing `N φ(N)`. -/
theorem not_dvd_tame_of_not_mem_stageExclusions {ℓ N p : ℕ} {Dw hstar : ℤ} (hN : 0 < N)
    (hp : p.Prime) (hn : p ∉ stageExclusions ℓ Dw hstar (N * N.totient).primeFactors) :
    ¬ p ∣ N * N.totient := fun h =>
  hn (subset_stageExclusions ℓ Dw hstar _ (Nat.mem_primeFactors.mpr ⟨hp, h,
    Nat.mul_ne_zero hN.ne' (Nat.totient_pos.mpr hN).ne'⟩))

section Level

open ZInQ.Contrib.CloudB3RC53

theorem gamma0_one_eq_top : CongruenceSubgroup.Gamma0 1 = ⊤ := by
  ext A
  simp only [CongruenceSubgroup.Gamma0_mem, Subgroup.mem_top, iff_true]
  exact Subsingleton.elim _ _

theorem gamma0_one_coe :
    ((CongruenceSubgroup.Gamma0 1 : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)) = 𝒮ℒ := by
  rw [gamma0_one_eq_top]
  exact (MonoidHom.range_eq_map _).symm

theorem cuspForm_weight_two_eq_zero {Γ : Subgroup (GL (Fin 2) ℝ)} (hΓ : Γ = 𝒮ℒ)
    (f : CuspForm Γ 2) : f = 0 := by
  subst hΓ
  exact rank_zero_iff_forall_zero.mp (CuspForm.rank_eq_zero_of_weight_lt_twelve (by norm_num)) f

/-- **`h₂` from `hN`**: a positive newform level is at least `2`. At level one the
cusp form is zero (weight two, `CuspForm.rank_eq_zero_of_weight_lt_twelve`), so its
first coefficient vanishes, while `a₁(E) = 1` (`lFunction_one`). -/
theorem two_le_newformLevel {E : WeierstrassCurve ℚ} (hN : 0 < CST.newformLevel E) :
    2 ≤ CST.newformLevel E := by
  have hne := Nat.nonempty_of_pos_sInf hN
  obtain ⟨-, hf⟩ := Nat.sInf_mem hne
  change CST.HasCuspFormAtLevel E (CST.newformLevel E) at hf
  by_contra h
  have h1 : CST.newformLevel E = 1 := by omega
  rw [h1] at hf
  obtain ⟨f, hf⟩ := hf
  have h0 := cuspForm_weight_two_eq_zero gamma0_one_coe f
  have hc := hf 1 one_pos
  rw [ZInQ.Contrib.RC53Assist.NewformGlueG0.lFunction_one, h0, FunLike.coe_zero,
    UpperHalfPlane.qExpansion_zero] at hc
  simp at hc

/-- `h₂` for `ModelNeron.source` at `N := StageKummer.level ℓ`, from the hypothesis
`hN : 0 < StageKummer.level ℓ` of `PMWire.oddStagedOfGoodRows` (Assembly.lean:114). -/
theorem two_le_level {ℓ : ℕ} (hN : 0 < ZInQ.Manuscript.RC.StageKummer.level ℓ) :
    2 ≤ ZInQ.Manuscript.RC.StageKummer.level ℓ :=
  two_le_newformLevel hN

end Level

#print axioms EcurveZ_disc
#print axioms stagePrime_not_dvd_disc
#print axioms stagePrime_five_le
#print axioms stagePrime_not_dvd_tame
#print axioms subset_stageExclusions
#print axioms not_dvd_tame_of_not_mem_stageExclusions
#print axioms two_le_newformLevel
#print axioms two_le_level

end ZInQ.Manuscript.RC.ModelGeneric5
