import ZInQKernel.Contrib.OneProof.RC.BlocksPerU.Fourier

/-! Separate the first weighted transformation from the moving-prime
level calculation. The powers of two in the normalized series add no
analytic assumptions. -/

noncomputable section

namespace ZInQ.Manuscript.RC.BlocksPerU

open ThetaCoeff UpperHalfPlane
open ZInQ.Contrib.CloudB3RC53.CoefficientDictionary
open scoped MatrixGroups Manifold BigOperators

private theorem rescale_threeHalves {O : Type} [CommRing O] {ι : O →+* ℂ}
    {m : ℕ} {ξ : (ZMod m)ˣ →* ℂˣ} {a b : ℕ → O}
    (h : HasThreeHalvesExpansion ι m ξ a) (t : ℂ)
    (hcoeff : ∀ n, ι (b n) = t * ι (a n)) :
    HasThreeHalvesExpansion ι m ξ b := by
  obtain ⟨g, hg, hq⟩ := h
  let g' : ℍ → ℂ := fun z => t * g z
  refine ⟨g', ⟨mdifferentiable_const.mul hg.holo, ?_, ?_⟩, ?_⟩
  · intro γ z
    change t * g ((γ : SL(2, ℤ)) • z) = _
    rw [hg.law γ z]
    dsimp only [g']
    ring
  · intro γ
    obtain ⟨M, A, hA⟩ := isBoundedAtImInfty_iff.mp (hg.cusps γ)
    apply isBoundedAtImInfty_iff.mpr
    refine ⟨‖t‖ * M, A, fun z hz => ?_⟩
    have he : cuspNorm (3 / 2) g' γ z = ‖t‖ * cuspNorm (3 / 2) g γ z := by
      simp [g', cuspNorm, mul_assoc]
    rw [he, norm_mul, norm_norm]
    exact mul_le_mul_of_nonneg_left (hA z hz) (norm_nonneg _)
  · intro z
    simpa only [g', hcoeff, mul_assoc] using (hq z).mul_left t

variable {O K L : Type} [CommRing O] [IsDomain O] [CharZero O] [Field K] [Algebra O K]
    [AddCommGroup L] {ε : L →+ ZMod 2} {T : TypeData L ε} {avoid : Finset ℕ}
variable {M W R N : ℕ} {S : AppF.ThetaStage (Odd.StageRing O M)}
    {δ : ℤ} {adm : ℕ → Prop} {P : Window T.Good S W} {E : Lift S}

theorem normalize_B (ι : O →+* ℂ) (D : Divisions E δ W R adm) {U : Finset ℕ}
    (hU : Admissible S W U) {m : ℕ} {ξ : (ZMod m)ˣ →* ℂˣ}
    (h : HasThreeHalvesExpansion ι m ξ (E.raw U)) :
    HasThreeHalvesExpansion ι m ξ (E.B D hU) := by
  apply rescale_threeHalves h ((2 : ℂ) ^ (-(nU δ U)).toNat / (2 : ℂ) ^ (nU δ U).toNat)
  intro n
  have he := congrArg ι (B_spec E D hU n)
  simp only [map_mul, map_pow, map_ofNat] at he
  have hp : (2 : ℂ) ^ (nU δ U).toNat ≠ 0 := pow_ne_zero _ (by norm_num)
  rw [div_mul_eq_mul_div, eq_div_iff hp, mul_comm (ι (E.B D hU n))]
  exact he

omit [IsDomain O] [CharZero O] in
theorem LevelSetup.old_dvd (Dₗ : LevelSetup P avoid N) : Dₗ.old ∣ N :=
  (congrArg (fun n => Dₗ.old ∣ n) Dₗ.common).mpr (dvd_mul_right _ _)

/-- The first analytic obligation for this stage and pool, with the exact
old level and character specified. The character is the empty-sieve value
of the common character, namely the image of `η · χ₋₁`. -/
def OldStageLaw (κ : K →+* ℂ) (Dₗ : LevelSetup P avoid N)
    (C : DiamondCharacters O (ZMod N)ˣ E.η) : Prop :=
  ∃ ξ : (ZMod Dₗ.old)ˣ →* ℂˣ,
    ξ.comp (ZMod.unitsMap Dₗ.old_dvd) = (Units.map κ).comp (bCharacter (K := K) C ∅) ∧
    StageTernaryTransformation E (κ.comp (algebraMap O K)) Dₗ.old ξ

/-- The moving-prime half-integral level calculation, conditional on the old
stage law. It concerns only the unnormalized Fourier sieves of this one
form. The unary Poisson calculation is a separate input. -/
def MovingSieveLaw (κ : K →+* ℂ) (Dₗ : LevelSetup P avoid N)
    (C : DiamondCharacters O (ZMod N)ˣ E.η) : Prop :=
  OldStageLaw κ Dₗ C →
    ∀ U (hU : U ⊆ P.pool), U.Nonempty →
      ∃ ξ : (ZMod (Dₗ.old * ∏ p ∈ U, p))ˣ →* ℂˣ,
        ξ.comp (ZMod.unitsMap (Dₗ.b_dvd hU)) = (Units.map κ).comp (bCharacter (K := K) C U) ∧
        HasThreeHalvesExpansion (κ.comp (algebraMap O K)) _ ξ (E.raw U)

/-- The independent rank-one Poisson input at each unary dilation. -/
def UnaryStageLaw (κ : K →+* ℂ) (Dₗ : LevelSetup P avoid N)
    (C : DiamondCharacters O (ZMod N)ˣ E.η) : Prop :=
  ∀ U (hU : U ⊆ P.pool) j (hj : j ∈ subscripts U),
    ∃ ξ : (ZMod (Dₗ.old * j))ˣ →* ℂˣ,
      ξ.comp (ZMod.unitsMap (Dₗ.unary_dvd hU hj)) =
        (Units.map κ).comp (unaryCharacter (K := K) C E.parity j) ∧
      HasThreeHalvesExpansion (κ.comp (algebraMap O K)) _ ξ (E.unary j)

/-- The source and sieve laws, unary Poisson law, and ordinary theta law give
the analytic input to the finite constituent construction. -/
theorem blockModularity_of_stage (κ : K →+* ℂ) (Dₗ : LevelSetup P avoid N)
    (D : Divisions E δ W R adm) (C : DiamondCharacters O (ZMod N)ˣ E.η)
    (hOld : OldStageLaw κ Dₗ C) (hSieve : MovingSieveLaw κ Dₗ C)
    (hθ : OrdinaryThetaLaw) (hUnary : UnaryStageLaw κ Dₗ C) :
    BlockModularity κ Dₗ D C := by
  apply blockModularity_of_halfIntegral κ Dₗ D C hθ _ hUnary
  intro U hU
  suffices H : ∃ ξ : (ZMod (Dₗ.old * ∏ p ∈ U, p))ˣ →* ℂˣ,
      ξ.comp (ZMod.unitsMap (Dₗ.b_dvd hU)) = (Units.map κ).comp (bCharacter (K := K) C U) ∧
      HasThreeHalvesExpansion (κ.comp (algebraMap O K)) _ ξ (E.raw U) by
    obtain ⟨ξ, hξ, h⟩ := H
    exact ⟨ξ, hξ, normalize_B _ D (P.admissible U hU) h⟩
  rcases U.eq_empty_or_nonempty with rfl | hn
  · have atOld (m : ℕ) (hm : m ∣ N) (e : m = Dₗ.old) :
        ∃ ξ : (ZMod m)ˣ →* ℂˣ,
          ξ.comp (ZMod.unitsMap hm) = (Units.map κ).comp (bCharacter (K := K) C ∅) ∧
          HasThreeHalvesExpansion (κ.comp (algebraMap O K)) m ξ E.aθ := by
      subst m
      exact hOld
    simpa [Lift.raw, Odd.TL] using atOld _ (Dₗ.b_dvd hU) (by simp)
  · exact hSieve hOld U hU hn

#print axioms rescale_threeHalves
#print axioms normalize_B
#print axioms LevelSetup.old_dvd
#print axioms blockModularity_of_stage

end ZInQ.Manuscript.RC.BlocksPerU
