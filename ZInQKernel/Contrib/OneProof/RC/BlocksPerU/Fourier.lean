import ZInQKernel.Contrib.OneProof.RC.BlocksPerU.ThetaTransform

/-! The positive expansion of the weight-two product is the existing
finite convolution, with no extra modularity input for that product. -/

noncomputable section

namespace ZInQ.Manuscript.RC.BlocksPerU

open ThetaCoeff PrintsAnalytic UpperHalfPlane
open ZInQ.Contrib.CloudB3RC53.CoefficientDictionary
open scoped Manifold BigOperators Classical

set_option maxHeartbeats 800000

private def thetaSquares (n : ℕ) : ℂ := if ∃ k : ℕ, (k + 1) ^ 2 = n then 2 else 0

private def thetaCoeff (n : ℕ) : ℂ := (if n = 0 then 1 else 0) + thetaSquares n

private theorem theta_hasSum (z : ℍ) :
    HasSum (fun n => thetaCoeff n * Function.Periodic.qParam 1 (z : ℂ) ^ n) (thetaFun z) := by
  let q := Function.Periodic.qParam 1 (z : ℂ)
  let s : ℕ → ℕ := fun k => (k + 1) ^ 2
  have hinj : Function.Injective s :=
    (Nat.pow_left_injective (by decide : (2 : ℕ) ≠ 0)).comp Nat.succ_injective
  have hpos : 0 < (2 * (z : ℂ)).im := by
    rw [show (2 : ℂ) = (↑(2 : ℝ) : ℂ) by norm_num, Complex.im_ofReal_mul]
    exact mul_pos (by norm_num) z.im_pos
  have hs : HasSum (fun k => thetaSquares (s k) * q ^ s k) (thetaFun z - 1) := by
    convert (hasSum_nat_jacobiTheta hpos).mul_left 2 using 1
    · funext k
      have h : thetaSquares (s k) = 2 := ite_eq_left ⟨k, rfl⟩
      rw [h]
      congr 1
      dsimp [q, s, Function.Periodic.qParam]
      rw [← Complex.exp_nat_mul]
      push_cast
      congr 1
      ring
    · unfold thetaFun
      ring
  have hzero (n : ℕ) (hn : n ∉ Set.range s) : thetaSquares n * q ^ n = 0 := by
    have hz : thetaSquares n = 0 := ite_eq_right hn
    rw [hz, zero_mul]
  have hsq : HasSum (fun n => thetaSquares n * q ^ n) (thetaFun z - 1) :=
    (hinj.hasSum_iff hzero).mp hs
  have h0 : HasSum (fun n : ℕ => (if n = 0 then (1 : ℂ) else 0) * q ^ n) 1 := by
    convert hasSum_ite_eq 0 (1 : ℂ) using 1
    funext n
    by_cases hn : n = 0 <;> simp [hn]
  convert h0.add hsq using 1
  · funext n; exact add_mul _ _ _
  · ring

private theorem cusp_analytic_of_sum {g : ℍ → ℂ} {a : ℕ → ℂ} (hg : MDiff g)
    (hsum : ∀ z : ℍ, HasSum (fun n => a n * Function.Periodic.qParam 1 (z : ℂ) ^ n) (g z)) :
    AnalyticAt ℂ (cuspFunction 1 g) 0 := by
  have hsum' : ∀ z : ℍ, HasSum (fun n => a n • Function.Periodic.qParam 1 (z : ℂ) ^ n) (g z) :=
    hsum
  apply analyticAt_cuspFunction_zero one_pos _ hg
    (isBoundedAtImInfty_of_hasSum_qExpansion one_pos hsum')
  apply UpperHalfPlane.periodic_comp_ofComplex
  intro z
  apply Eq.symm
  apply (hsum z).unique
  have he : Function.Periodic.qParam 1 (((1 : ℝ) +ᵥ z : ℍ) : ℂ) =
      Function.Periodic.qParam 1 (z : ℂ) := by
    simp [coe_vadd, Function.Periodic.qParam, mul_add, Complex.exp_add, Complex.exp_two_pi_mul_I]
  simpa only [he] using hsum ((1 : ℝ) +ᵥ z)

private theorem theta_convolution {O : Type} [CommRing O] (ι : O →+* ℂ)
    (a : ℕ → O) (n : ℕ) :
    (∑ j ∈ Finset.range (n + 1), thetaCoeff j * ι (a (n - j))) = ι (timesTheta a n) := by
  classical
  rw [timesTheta, map_add, map_mul, map_ofNat, map_sum, Finset.mul_sum]
  simp only [thetaCoeff, add_mul, Finset.sum_add_distrib]
  congr 1
  · rw [Finset.sum_eq_single 0]
    · simp
    · intro i _ hi; simp [hi]
    · simp
  · rw [← Finset.sum_filter_add_sum_filter_not (Finset.range (n + 1))
      (fun j => ∃ k : ℕ, (k + 1) ^ 2 = j)]
    have hzero : (∑ j ∈ (Finset.range (n + 1)).filter
        (fun j => ¬ ∃ k : ℕ, (k + 1) ^ 2 = j), thetaSquares j * ι (a (n - j))) = 0 := by
      apply Finset.sum_eq_zero
      intro j hj
      rw [thetaSquares, ite_eq_right (Finset.mem_filter.mp hj).2, zero_mul]
    rw [hzero, add_zero]
    symm
    apply Finset.sum_bij (fun k _ => k ^ 2)
    · intro k hk
      obtain ⟨hkn, hk2⟩ := Finset.mem_filter.mp hk
      exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega),
        ⟨k - 1, by rw [Nat.sub_add_cancel (Finset.mem_Icc.mp hkn).1]⟩⟩
    · intro k _ l _ h
      exact Nat.pow_left_injective (by decide : (2 : ℕ) ≠ 0) h
    · intro j hj
      obtain ⟨hjn, ⟨k, rfl⟩⟩ := Finset.mem_filter.mp hj
      have hsq : (k + 1) ^ 2 ≤ n := by have := Finset.mem_range.mp hjn; omega
      have hle : k + 1 ≤ (k + 1) ^ 2 := by
        simp [pow_two]
      exact ⟨k + 1, Finset.mem_filter.mpr
        ⟨Finset.mem_Icc.mpr ⟨by omega, hle.trans hsq⟩, hsq⟩, rfl⟩
    · intro k hk
      have hpos := (Finset.mem_Icc.mp (Finset.mem_filter.mp hk).1).1
      rw [thetaSquares, ite_eq_left ⟨k - 1, by rw [Nat.sub_add_cancel hpos]⟩]

/-- The actual coefficient formula for multiplication by ordinary theta. -/
theorem qExpansion_theta_product {O : Type} [CommRing O] (ι : O →+* ℂ)
    {g : ℍ → ℂ} {a : ℕ → O} (hg : MDiff g)
    (hsum : ∀ z : ℍ, HasSum (fun n => ι (a n) * Function.Periodic.qParam 1 (z : ℂ) ^ n) (g z))
    (n : ℕ) : (qExpansion 1 (g * thetaFun)).coeff n = ι (timesTheta a n) := by
  let : FunLike (ℍ → ℂ) ℍ ℂ := ⟨id, fun _ _ h => h⟩
  have hg0 := cusp_analytic_of_sum hg hsum
  have hθ0 := cusp_analytic_of_sum thetaFun_holo theta_hasSum
  have hgc (k : ℕ) : (qExpansion 1 g).coeff k = ι (a k) :=
    (UpperHalfPlane.qExpansion_coeff_unique g one_pos hg0 hsum k).symm
  have hθc (k : ℕ) : (qExpansion 1 thetaFun).coeff k = thetaCoeff k :=
    (UpperHalfPlane.qExpansion_coeff_unique thetaFun one_pos hθ0 theta_hasSum k).symm
  rw [qExpansion_mul hg0 hθ0, mul_comm, PowerSeries.coeff_mul]
  simp only [hθc, hgc]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun i j => thetaCoeff i * ι (a j))]
  simp only [Nat.succ_eq_add_one]
  exact theta_convolution ι a n

variable {O K : Type} [CommRing O] [Field K] [Algebra O K] {m N : ℕ}

/-- Passage from one half-integral block to the exact analytic input of
the constituent construction. -/
theorem weightTwoExpansion_of_halfIntegral (κ : K →+* ℂ) (hm : m ∣ N)
    (χ : (ZMod N)ˣ →* Kˣ) (ξ : (ZMod m)ˣ →* ℂˣ)
    (hχ : ξ.comp (ZMod.unitsMap hm) = (Units.map κ).comp χ)
    (hfour : 4 ∣ m) (hθ : OrdinaryThetaLaw) {a : ℕ → O}
    (h : HasThreeHalvesExpansion (κ.comp (algebraMap O K)) m ξ a) :
    HasWeightTwoExpansion κ hm χ (fun n => algebraMap O K (timesTheta a n)) := by
  obtain ⟨g, hg, hq⟩ := h
  obtain ⟨f, hf, hmem⟩ := theta_product_modular hfour hθ hg
  refine ⟨ξ, f, hχ, hmem, fun n _ => ?_⟩
  rw [hf]
  exact qExpansion_theta_product _ hg.holo hq n

variable [IsDomain O] [CharZero O] {L : Type} [AddCommGroup L] {ε : L →+ ZMod 2}
variable {T : TypeData L ε} {avoid : Finset ℕ} {M W R : ℕ}
variable {S : AppF.ThetaStage (Odd.StageRing O M)} {δ : ℤ} {adm : ℕ → Prop}
variable {P : Window T.Good S W} {E : Lift S}

/-- Apply the product theorem to the two types of half-integral blocks.
The input series here are the pre-product coefficients of the fixed stage,
at their individual levels (tex 9497–9555 and 9620–9625). -/
theorem blockModularity_of_halfIntegral (κ : K →+* ℂ) (Dₗ : LevelSetup P avoid N)
    (D : Divisions E δ W R adm) (C : DiamondCharacters O (ZMod N)ˣ E.η)
    (hθ : OrdinaryThetaLaw)
    (hB : ∀ U (hU : U ⊆ P.pool),
      ∃ ξ : (ZMod (Dₗ.old * ∏ p ∈ U, p))ˣ →* ℂˣ,
        ξ.comp (ZMod.unitsMap (Dₗ.b_dvd hU)) = (Units.map κ).comp (bCharacter (K := K) C U) ∧
        HasThreeHalvesExpansion (κ.comp (algebraMap O K)) _ ξ
          (E.B D (P.admissible U hU)))
    (hUnary : ∀ U (hU : U ⊆ P.pool) j (hj : j ∈ subscripts U),
      ∃ ξ : (ZMod (Dₗ.old * j))ˣ →* ℂˣ,
        ξ.comp (ZMod.unitsMap (Dₗ.unary_dvd hU hj)) =
          (Units.map κ).comp (unaryCharacter (K := K) C E.parity j) ∧
        HasThreeHalvesExpansion (κ.comp (algebraMap O K)) _ ξ (E.unary j)) :
    BlockModularity κ Dₗ D C where
  b U hU := by
    obtain ⟨ξ, hξ, h⟩ := hB U hU
    exact weightTwoExpansion_of_halfIntegral κ _ _ ξ hξ
      (Dₗ.four_dvd.trans (dvd_mul_right _ _)) hθ h
  unary U hU j hj := by
    obtain ⟨ξ, hξ, h⟩ := hUnary U hU j hj
    exact weightTwoExpansion_of_halfIntegral κ _ _ ξ hξ
      (Dₗ.four_dvd.trans (dvd_mul_right _ _)) hθ h

#print axioms theta_hasSum
#print axioms cusp_analytic_of_sum
#print axioms theta_convolution
#print axioms qExpansion_theta_product
#print axioms weightTwoExpansion_of_halfIntegral
#print axioms blockModularity_of_halfIntegral

end ZInQ.Manuscript.RC.BlocksPerU
