import ZInQKernel.Contrib.OneProof.RC.Wiring.UniformSwitch
import ZInQKernel.Contrib.OneProof.RC.Wiring.ClearingComplex3

/-!
# RC inhabitability witnesses, group C: (3.5), height-one regularity, clearing

Witnesses for the leaves `Eq35InputsGenuineG`, `PrimRegularityInputsS`, `ClearingInputsCx` of
`RC/Wiring/Leaves.lean` and the RC structures they carry. No RC file is modified.

* `nonquadInputs_example`: `NonquadInputs ℚ 3 1` (the duality, detection and (5.5a) clauses
  together, `U = F`, `k₀ = 1`), non-vacuous.
* `heightOneSwitchDataAt_nonempty`, `regularityInputsS_one`: RC's own one-stage data (switch clauses
  vacuous: fiber dimension one); `RegularityInputsS 1` through its right disjunct at every
  height-one prime.
* `primRegularityInputsS_of_uPrim_one`: `PrimRegularityInputsS D` for every `D` whose primitive
  coordinates are `1` (no condition on the families).
* `eq35InputsGenuineG_of_jrc`: `Eq35InputsGenuineG W` for every `W` whose `j_rc` is
  `2ω(h) + s(h) + s(hk')`: every conjunct holds at every pair `(h, k')` and every sequence of
  companion pairs (no antecedent is used); the outer switch clause is vacuous (outer dimension one).
* `clearingInputsCx_of_uTilde_zero`: `ClearingInputsCx D` for every `D` with `ũ ≡ 0` (trivial
  remaining complex; E1a and E1b hold with `Δ = 1` and the rank-one pattern at every address).
* `exData`, `exW`: concrete data, so that each leaf is inhabited outright.

**Classification.** PROVED (witness probes).
-/

noncomputable section

namespace ZInQ.Contrib.CloudB3RC53.RCWitness.Switch

open ZInQ.Manuscript ZInQ.Manuscript.RC ZInQ.Manuscript.RC.Wiring ZInQ.Contrib.CloudB3RC53
open ZInQ.Manuscript.RC.Uniform ZInQ.Manuscript.RC.Rings
open ZInQ.Manuscript.RC.Determinant (Lam OO SignGroup ScalarData evK uK sgnChar cleanT)
open Matrix Module

attribute [local instance] Nat.fact_prime_two

/-! ### `NonquadInputs`: duality, detection and (5.5a) together -/

theorem nonquadInputs_example : NonquadInputs ℚ 3 1 := by
  refine ⟨1, 1, 1, one_ne_zero, one_ne_zero, Matrix.one_mul 1,
    finPlane ℚ (Fin 2 → ℚ) (Fin 2 → ℚ), 1, ?_, le_rfl, ?_, ?_⟩
  · have hP := ZInQ.Manuscript.RC.Uniform.crossPairing_isPerfPair (one_ne_zero (α := ℚ))
      (J := (1 : Matrix (Fin 2) (Fin 2) ℚ)) (Matrix.one_mul 1)
    exact ZInQ.Manuscript.RC.Uniform.orthogonal_finPlane _
      (LinearMap.IsPerfPair.bijective_right _).injective 1
  · rw [inf_idem, SwitchInputs.finrank_finPlane]
  · rw [UniformSwitch.finPlane_inf_singPlane, finrank_bot]

/-! ### Height-one regularity -/

theorem heightOneSwitchDataAt_nonempty (P : Ideal Lambda) [P.IsPrime] :
    Nonempty (HeightOneSwitchDataAt P) :=
  ⟨oneStageSwitchData P 1⟩

theorem regularityInputsS_one : RegularityInputsS (1 : FractionRing Lambda) :=
  (regularityInputsS_iff 1).mpr ⟨1, map_one _⟩

theorem inLamHalf_one : InLamHalf (1 : PowerSeries ℚ_[2]) := by
  refine ⟨0, fun n => if n = 0 then 1 else 0, fun n => ?_⟩
  by_cases h : n = 0
  · subst h; simp
  · simp [PowerSeries.coeff_one, h]

theorem primRegularityInputsS_of_uPrim_one {ℓ : ℕ} (D : RCData ℓ)
    (hD : ∀ F x, D.uPrim F x = 1) : PrimRegularityInputsS D :=
  (primRegularityInputsS_iff D).mpr fun _ _ _ _ x => by rw [hD]; exact inLamHalf_one

/-- Concrete interface data (all predicates empty, coordinates `0`). -/
def exData (ℓ : ℕ) : RCData ℓ where
  S := ∅
  prepared _ := False
  Lstar _ := 0
  jgen _ := 0
  jrc _ _ := 0
  hstar := 0
  stages := pure 0
  Mθ := id
  aθ _ _ := 0
  admissible _ _ := False
  δo := 0
  kfin := 0
  uPrim _ _ := 0
  uTilde _ _ := 0

theorem primRegularityInputsS_inhabited (ℓ : ℕ) :
    PrimRegularityInputsS ({ exData ℓ with uPrim := fun _ _ => 1 } : RCData ℓ) :=
  primRegularityInputsS_of_uPrim_one _ fun _ _ => rfl

/-! ### (3.5): `Eq35InputsGenuineG` -/

/-- The exponent `m(h, k') = s(h) + s(hk')`. -/
def mExp (ℓ : ℕ) (h k' : ℤ) : ℕ := shaLength (Etw ℓ h) + shaLength (Etw ℓ (h * k'))

/-- The primitive coordinates `uprim h k' = 2^{m(h,k')} ∈ Λ[1/2]`. -/
def uprimEx (ℓ : ℕ) (h k' : ℤ) : FractionRing Lambda :=
  lambdaHalfToFrac ((2 : LambdaHalf) ^ mExp ℓ h k')

theorem v2_two_pow (m : ℕ) : ZInQ.Manuscript.RC.v2 ((2 : ℚ_[2]) ^ m) = ((m : ℤ) : WithTop ℤ) := by
  rw [ZInQ.Manuscript.RC.v2, AddValuation.map_pow]
  have : Padic.addValuation (2 : ℚ_[2]) = 1 := by
    rw [Padic.addValuation.apply two_ne_zero]
    have := Padic.valuation_p (p := 2)
    exact_mod_cast congrArg (fun z : ℤ => (z : WithTop ℤ)) this
  rw [this, nsmul_one]; rfl

theorem iotaO_uprimEx (ℓ : ℕ) (h k' : ℤ) :
    iotaO (uprimEx ℓ h k') = (2 : FractionRing OO) ^ mExp ℓ h k' := by
  rw [uprimEx, map_pow, map_pow, map_ofNat, map_ofNat]

/-- The genuine outer configuration with inner coordinate `c j`: inner models `0`, cycle `c j`,
functional and complement `1`. -/
def stageEx (𝒰 : Ultrafilter ℕ) (c : ℕ → FractionRing OO) : GenuineOuterStage 𝒰 where
  n := 0
  M := fun _ => 0
  zout := fun _ => 1
  hzout := (exampleGenuineStage 𝒰).hzout
  hzout0 := (exampleGenuineStage 𝒰).hzout0
  z := fun j _ => c j
  lam := fun _ _ => 1
  w := fun _ => Fin.elim0
  y := fun _ _ => 1
  hz := fun _ => by simp
  hlam := fun _ => by simp
  hden := (exampleGenuineStage 𝒰).hden

theorem stageEx_coord (𝒰 : Ultrafilter ℕ) (c : ℕ → FractionRing OO) (j : ℕ) :
    (stageEx 𝒰 c).toStage.coord j = c j := by
  have hden := (exampleGenuineStage 𝒰).hden j
  have hzw : detCols (colsZW (fun _ : Fin 1 => c j) (Fin.elim0 : Fin 0 → Fin 1 → _)) = c j := by
    have : colsZW (fun _ : Fin 1 => c j) (Fin.elim0 : Fin 0 → Fin 1 → _) = fun _ _ => c j := by
      funext i r
      obtain rfl : i = 0 := Fin.eq_of_val_eq (by omega)
      rfl
    rw [this]
    change Matrix.det (Matrix.of fun _ _ : Fin 1 => c j) = c j
    rw [Matrix.det_fin_one]; rfl
  have hd1 : detCols (colsDWY ((0 : Matrix (Fin 1) (Fin 1) OO).map
      (algebraMap OO (FractionRing OO))) Fin.elim0 (fun _ => 1)) = 1 := by
    rw [show ((0 : Matrix (Fin 1) (Fin 1) OO).map (algebraMap OO (FractionRing OO))) = 0 by simp]
    have : colsDWY (0 : Matrix (Fin 1) (Fin 1) (FractionRing OO)) Fin.elim0 (fun _ => 1) =
        fun _ _ => 1 := by
      funext i r
      obtain rfl : i = Fin.last 0 := Fin.eq_of_val_eq (by omega)
      rw [colsDWY, Fin.snoc_last]
    rw [this]
    change Matrix.det (Matrix.of fun _ _ : Fin 1 => (1 : FractionRing OO)) = 1
    rw [Matrix.det_fin_one]; rfl
  change detCols (colsZW (fun _ : Fin 1 => c j) (Fin.elim0 : Fin 0 → Fin 1 → _)) *
      ((fun _ : Fin 1 => (1 : FractionRing OO)) ⬝ᵥ fun _ => 1) /
      detCols (colsDWY ((0 : Matrix (Fin 1) (Fin 1) OO).map (algebraMap OO (FractionRing OO)))
        Fin.elim0 (fun _ => 1)) = c j
  rw [hzw, hd1]
  simp [dotProduct]

theorem vO_two_pow_nonneg (m : ℕ) : (0 : WithTop ℤ) ≤ vO ((2 : FractionRing OO) ^ m) := by
  rw [AddValuation.map_pow, vO_two]
  exact nsmul_nonneg (by norm_num) m

/-- Genuine outer switching data with inner coordinates `c j` of nonnegative valuation. -/
def outerEx (𝒰 : Ultrafilter ℕ) (c : ℕ → FractionRing OO) (hc : ∀ j, 0 ≤ vO (c j)) :
    GenuineOuterSwitchData 𝒰 0 where
  Stage := Unit
  stage _ := stageEx 𝒰 c
  cycle_integral _ j _ := hc j
  functional_bound _ _ _ := by
    change (((-(0 : ℕ) : ℤ)) : WithTop ℤ) ≤ vO 1
    rw [AddValuation.map_one]; rfl
  switch S hs := absurd (finrank_ker_fin_one_le (F' := KOut 𝒰) (stageEx 𝒰 c).toStage.Dout)
    (not_le.mpr hs)

/-- **`Eq35InputsGenuineG W` for every `W` with `j_rc(h, k') = 2ω(h) + s(h) + s(hk')`**: all three
conjuncts at every pair, with `C₀ = 0`, `t = 0`, `err = 0`. -/
theorem eq35InputsGenuineG_of_jrc {ℓ : ℕ} (W : WData ℓ)
    (hjrc : ∀ h k', W.jrc h k' = 2 * (omega h : ℤ) + sFun ℓ h + sFun ℓ (h * k')) :
    Eq35InputsGenuineG W := by
  refine ⟨uprimEx ℓ, 0, fun h k' _ _ _ => ?_, fun h k' _ _ _ uh huh => ?_, fun A inst => ?_⟩
  · exact (regularityInputsS_iff _).mpr ⟨_, rfl⟩
  · have huh' : uh = (2 : LambdaHalf) ^ mExp ℓ h k' := lambdaHalfToFrac_injective huh
    refine ⟨fun _ => 0, 0, fun _ => Nat.zero_le _, le_refl _, ?_⟩
    rw [huh', map_pow, map_ofNat, v2_two_pow]
    congr 1
    rw [hjrc]
    simp only [mExp, sFun, Nat.cast_zero, Finset.sum_const_zero, sub_zero, add_zero]
    push_cast
    ring
  · refine ⟨0, outerEx _ (fun j => iotaO (uprimEx ℓ (inst j).h (inst j).k))
      (fun j => by rw [iotaO_uprimEx]; exact vO_two_pow_nonneg _), (), ?_⟩
    exact Filter.Eventually.of_forall fun j => by
      change vO ((stageEx _ _).toStage.coord j) = _
      rw [stageEx_coord]

/-- Concrete `W` (all of `exData`, `j_rc` as required). -/
def exW (ℓ : ℕ) : WData ℓ :=
  { exData ℓ with
    jrc := fun h k' => 2 * (omega h : ℤ) + sFun ℓ h + sFun ℓ (h * k')
    Partitionable := fun _ => True }

theorem eq35InputsGenuineG_inhabited (ℓ : ℕ) : Eq35InputsGenuineG (exW ℓ) :=
  eq35InputsGenuineG_of_jrc _ fun _ _ => rfl

/-! ### Clearing: `ClearingInputsCx` -/

open ZInQ.Contrib.CloudB3RC53.ClearingComplex in
/-- **`ClearingInputsCx D` for every `D` with `ũ ≡ 0`**: the trivial identification
(`selmerIdentification_trivial`), zero scalar data, `κ = ε = η = 0`, `c = 0`. -/
theorem clearingInputsCx_of_uTilde_zero {ℓ : ℕ} (D : RCData ℓ) (hD : ∀ F x, D.uTilde F x = 0) :
    ClearingInputsCx D := by
  refine ⟨0, 0, 0, 0, fun Co Ce F _ => ?_⟩
  refine ⟨selmerIdentification_trivial F.b, ⟨0, 0, 0, 0, 0, 0⟩, 0, 0, 0, 0, ?_, ?_⟩
  · refine ⟨fun x _ _ => ?_, fun x _ _ => ?_⟩
    · simp [ScalarData.αK]
    · exact ⟨by simp [ScalarData.αK], rfl⟩
  · intro e g hrep x _
    have hg : g x = 0 := by
      ext j
      have := hrep x j
      rw [hD, map_zero] at this
      have h2 : (2 : ℚ_[2]) ^ e x ≠ 0 := pow_ne_zero _ two_ne_zero
      have h0 : ((PowerSeries.coeff j (g x) : ℤ_[2]) : ℚ_[2]) = 0 := by
        rw [eq_div_iff h2, zero_mul] at this; exact this.symm
      simpa using h0
    simp [uK, hg]

theorem clearingInputsCx_inhabited (ℓ : ℕ) : ClearingInputsCx (exData ℓ) :=
  clearingInputsCx_of_uTilde_zero _ fun _ _ => rfl

/-! ### Non-vacuous switch data: `SwitchCoordData`, `CoordStep`, `QuadMixedDims`, `QuadSingleDims`,
and a two-stage `HeightOneSwitchDataAt` whose nonquadratic switch fires -/

section Switches

open ZInQ.Manuscript.RC.Uniform.QuadraticCase

theorem nonquadInputs_three_one (k : Type) [Field k] : NonquadInputs k 3 1 := by
  have hP := crossPairing_isPerfPair (one_ne_zero (α := k)) (J := (1 : Matrix (Fin 2) (Fin 2) k))
    (Matrix.one_mul 1)
  refine ⟨1, 1, 1, one_ne_zero, one_ne_zero, Matrix.one_mul 1,
    finPlane k (Fin 2 → k) (Fin 2 → k), 1, ?_, le_rfl, ?_, ?_⟩
  · exact orthogonal_finPlane _
      (LinearMap.IsPerfPair.bijective_right _).injective 1
  · rw [inf_idem, SwitchInputs.finrank_finPlane]
  · rw [UniformSwitch.finPlane_inf_singPlane, finrank_bot]

/-- `J = diag(1, −1)`. -/
def Jm (K : Type) [Field K] : Matrix (Fin 2) (Fin 2) K := !![1, 0; 0, -1]

theorem Jm_mul_self (K : Type) [Field K] : Jm K * Jm K = 1 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [Jm, Matrix.mul_apply, Fin.sum_univ_two]

/-- The volume form on `Dual (K²)`. -/
def omegaD (K : Type) [Field K] : LinearMap.BilinForm K (Module.Dual K (Fin 2 → K)) :=
  LinearMap.mk₂ K (fun φ ψ => φ (Pi.single 0 1) * ψ (Pi.single 1 1) -
      φ (Pi.single 1 1) * ψ (Pi.single 0 1))
    (fun _ _ _ => by simp only [LinearMap.add_apply]; ring)
    (fun _ _ _ => by simp only [LinearMap.smul_apply, smul_eq_mul]; ring)
    (fun _ _ _ => by simp only [LinearMap.add_apply]; ring)
    (fun _ _ _ => by simp only [LinearMap.smul_apply, smul_eq_mul]; ring)

/-- **Switch-plane data** over any field: `ε = σ = 1`, `J = diag(1, −1)`, `v = e₀`, `f c = c₀ e₀`,
`s c = c₁ e₀`, unit volumes. -/
def scd (K : Type) [Field K] : UniformSwitch.SwitchCoordData K where
  ε := 1
  σ := 1
  J := Jm K
  f := (LinearMap.proj (0 : Fin 2)).smulRight (Pi.single 0 1)
  s := (LinearMap.proj (1 : Fin 2)).smulRight (Pi.single 0 1)
  v := Pi.single 0 1
  ω := omegaD K
  μF := 1
  μS := 1
  x := Pi.single 1 1
  y := Pi.single 1 1
  w := LinearMap.proj 0
  w' := LinearMap.proj 1
  hσ := one_mul 1
  hJ2 := Jm_mul_self K
  hJdet := by simp [Jm, Matrix.det_fin_two]
  hfA := by ext i; fin_cases i <;> simp
  hsA := by ext i; fin_cases i <;> simp
  hfB := by ext i; fin_cases i <;> simp
  hsB := by ext i; fin_cases i <;> simp [Jm, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  hω := fun φ => by simp [omegaD]; ring
  hxw := by
    simp [omegaD, bdryF_apply, crossPairing_apply, weil_apply, Jm]
  hyw := by
    simp [omegaD, bdryS_apply, crossPairing_apply, weil_apply, Jm]

theorem scd_uF (K : Type) [Field K] : (scd K).uF = 1 := by
  simp [UniformSwitch.SwitchCoordData.uF, scd, coordF, vol_apply, omegaD, bdryF_apply,
    crossPairing_apply, weil_apply, Jm]

theorem scd_uS (K : Type) [Field K] : (scd K).uS = -1 := by
  simp [UniformSwitch.SwitchCoordData.uS, scd, coordS, vol_apply, omegaD, bdryS_apply,
    crossPairing_apply, weil_apply, Jm]

/-- **`CoordStep`** over any `ι : A → F` from the switch-plane data (units `1`). -/
def coordStepEx {A F : Type} [CommRing A] [Field F] (ι : A →+* F) :
    UniformSwitch.CoordStep ι 1 (-1) where
  X := scd F
  mF := 1
  mS := 1
  σ₀ := 1
  hmF := isUnit_one
  hmS := isUnit_one
  hμF := (map_one ι).symm
  hμS := (map_one ι).symm
  hσ₀ := (map_one ι).symm
  hu := (scd_uF F).symm
  hu' := (scd_uS F).symm

/-- `J = diag(1, −1)` as a linear map. -/
def JL (k : Type) [Field k] : (Fin 2 → k) →ₗ[k] (Fin 2 → k) := (Jm k).mulVecLin

theorem JL_e0 (k : Type) [Field k] : JL k (Pi.single 0 1) = Pi.single 0 1 := by
  ext i; fin_cases i <;> simp [JL, Jm, Matrix.mulVec, dotProduct, Fin.sum_univ_two]

theorem JL_e1 (k : Type) [Field k] : JL k (Pi.single 1 1) = -Pi.single 1 1 := by
  ext i; fin_cases i <;> simp [JL, Jm, Matrix.mulVec, dotProduct, Fin.sum_univ_two]

theorem crossPair_e0_e1 (k : Type) [Field k] :
    crossPair 1 (JL k) (Pi.single 0 1) (Pi.single 1 1) ≠ 0 := by
  rw [crossPair, JL_e1]; simp [e₂_apply]

theorem crossPair_e1_e0 (k : Type) [Field k] :
    crossPair 1 (JL k) (Pi.single 1 1) (Pi.single 0 1) ≠ 0 := by
  rw [crossPair, JL_e0]; simp [e₂_apply]

theorem e0_ne (k : Type) [Field k] : (Pi.single 0 1 : Fin 2 → k) ≠ 0 := by
  intro h; simpa using congrFun h 0

theorem e1_ne (k : Type) [Field k] : (Pi.single 1 1 : Fin 2 → k) ≠ 0 := by
  intro h; simpa using congrFun h 1

/-- **`QuadMixedDims 2 2 1 1`** (non-vacuous): `U_± = F(e_±)`, `K₀^± = 1`. -/
def quadMixedEx : UniformSwitch.QuadMixedDims (k := ℚ) 2 2 1 1 where
  h2 := two_ne_zero
  ε := 1
  hε := one_ne_zero
  J := JL ℚ
  ep := Pi.single 0 1
  em := Pi.single 1 1
  hp := JL_e0 ℚ
  hm := JL_e1 ℚ
  he := by simp [e₂_apply]
  Up := finAxis (Pi.single 0 1)
  Um := finAxis (Pi.single 1 1)
  hUp := finAxis_selfAnnihilating (crossPair_e0_e1 ℚ)
  hUm := finAxis_selfAnnihilating (crossPair_e1_e0 ℚ)
  hdetp := ⟨(Pi.single 0 1, 0), mem_finAxis.2 ⟨1, by simp⟩, mem_finAxis.2 ⟨1, by simp⟩,
    fun h => e0_ne ℚ (congrArg Prod.fst h)⟩
  hdetm := ⟨(Pi.single 1 1, 0), mem_finAxis.2 ⟨1, by simp⟩, mem_finAxis.2 ⟨1, by simp⟩,
    fun h => e1_ne ℚ (congrArg Prod.fst h)⟩
  kp := 1
  km := 1
  hVp := by rw [inf_idem, finrank_finAxis (e0_ne ℚ)]
  hVm := by rw [inf_idem, finrank_finAxis (e1_ne ℚ)]
  hVp' := by rw [finAxis_inf_singAxis, finrank_bot]
  hVm' := by rw [finAxis_inf_singAxis, finrank_bot]

/-- **`QuadSingleDims 2 1 1`** (non-vacuous): `U_+ = F(e_+)`, `U_- = S(e_+)`, `K₀^+ = 1`. -/
def quadSingleEx : UniformSwitch.QuadSingleDims (k := ℚ) 2 1 1 where
  h2 := two_ne_zero
  ε := 1
  hε := one_ne_zero
  J := JL ℚ
  ep := Pi.single 0 1
  em := Pi.single 1 1
  hp := JL_e0 ℚ
  hm := JL_e1 ℚ
  he := by simp [e₂_apply]
  Up := finAxis (Pi.single 0 1)
  Um := singAxis (Pi.single 0 1)
  hUp := finAxis_selfAnnihilating (crossPair_e0_e1 ℚ)
  hUm := singAxis_selfAnnihilating (crossPair_e1_e0 ℚ)
  hdetp := ⟨(Pi.single 0 1, 0), mem_finAxis.2 ⟨1, by simp⟩, mem_finAxis.2 ⟨1, by simp⟩,
    fun h => e0_ne ℚ (congrArg Prod.fst h)⟩
  kp := 1
  km := 0
  hs := by norm_num
  hVp := by rw [inf_idem, finrank_finAxis (e0_ne ℚ)]
  hVm := by rw [inf_comm, finAxis_inf_singAxis, finrank_bot]
  hVp' := by rw [finAxis_inf_singAxis, finrank_bot]
  hVm' := by rw [inf_idem, finrank_singAxis (e0_ne ℚ)]

variable (P : Ideal Lambda) [P.IsPrime]

/-- The first stage: `[Λ_𝔭³ --0--> Λ_𝔭³]`, class `e₀`, functional `0`, coordinate `1`. -/
def stage3 : UniformSwitch.TwoTermStage (UniformSwitch.toFracAt P) where
  n := 2
  D := 0
  z := Pi.single 0 1
  w := 0
  u := 1
  hz := Matrix.zero_mulVec _
  hw := Matrix.vecMul_zero _
  hu := by
    unfold ZInQ.Manuscript.RC.Central.IsClassFunctionalCoord
    rw [Matrix.map_zero _ (map_zero _), Matrix.adjugate_zero]
    ext i j
    simp only [vecMulVec_apply, Pi.zero_apply, map_zero, mul_zero, Matrix.smul_apply,
      Matrix.zero_apply, smul_zero]

theorem stage3_fiberDim :
    (stage3 P).fiberDim (IsLocalRing.residue (Localization.AtPrime P)) = 3 := by
  have h0 : ((stage3 P).D.map (IsLocalRing.residue (Localization.AtPrime P))).mulVecLin = 0 := by
    apply LinearMap.ext; intro v; ext i
    simp [stage3]; rfl
  rw [UniformSwitch.TwoTermStage.fiberDim, h0, LinearMap.ker_zero, finrank_top, finrank_fin_fun]
  rfl

/-- **Two-stage height-one switching data over the genuine `Λ_𝔭`, with a nonquadratic switch that
fires**: fiber dimension `3 → 1`, coordinates `1 → −1` related by `coordStepEx`,
`NonquadInputs` over the residue field. -/
def twoStageSwitchData : HeightOneSwitchDataAt P where
  Stage := Bool
  stage b := if b then stage3 P else oneStageAt P (-1)
  quadratic := False
  sign _ := LinearMap.id
  sign_invol h := h.elim
  class_ne_zero b := by
    cases b
    · exact fun h => one_ne_zero (congrFun h 0)
    · intro h
      have := congrFun h 0
      change (Pi.single (0 : Fin 3) (1 : Localization.AtPrime P) : Fin 3 → _) 0 = 0 at this
      rw [Pi.single_eq_same] at this
      exact one_ne_zero this
  switch_mixed b _ hs := by
    cases b
    · simp only [Bool.false_eq_true, ↓reduceIte] at hs
      rw [oneStageAt_fiberDim] at hs; omega
    · refine ⟨false, ⟨?_⟩, fun h => h.elim, fun _ => ?_⟩
      · change UniformSwitch.CoordStep _ (1 : FractionRing Lambda)
          (UniformSwitch.toFracAt P (-1))
        rw [map_neg, map_one]
        exact coordStepEx _
      · simp only [↓reduceIte, Bool.false_eq_true]
        rw [stage3_fiberDim, oneStageAt_fiberDim]
        exact nonquadInputs_three_one _
  switch_single _ h := h.elim

end Switches

end ZInQ.Contrib.CloudB3RC53.RCWitness.Switch
