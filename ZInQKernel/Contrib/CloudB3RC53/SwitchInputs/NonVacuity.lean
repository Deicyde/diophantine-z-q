import ZInQKernel.Contrib.CloudB3RC53.SwitchInputs.Plug

/-!
# RC53 SwitchInputs: non-vacuity of the switch models (small genuine examples)

Binding rule (non-vacuity of models used as hypotheses): every structure of the UniformSwitch and
SwitchInputs files that packages a model and is used as a hypothesis gets an inhabitant here, on a
small genuine example over `ℚ`, with nontrivial content (a genuine switch, nonzero detected classes,
a nontrivial involution), so that its fields are shown not to contradict each other.

Common local data: `J₀ = diag(1, −1)` on `ℚ²` (`J₀² = 1`, `det J₀ = −1`), eigenvectors
`e₊ = (1, 0)`, `e₋ = (0, 1)` with `e₂(e₊, e₋) = 1`.

Examples (all PROVED):
* `exQuadMixedDims : QuadMixedDims 2 2 1 1` (mixed signs, a drop by two),
  `exQuadSingleDims : QuadSingleDims 2 1 1` (one sign only), `exNonquadDims : NonquadDims 3 1`;
* `exLocalizationDuality`: `LocalizationDualityInput` for `U = F` (the finite plane);
* `exDetectingPrime`, `exDetectingPrimePlus`: the detecting-prime inputs for nonzero classes `c±`;
* `exSwitchCoordData : SwitchCoordData ℚ` (all fields, `u_F = μ_F`, `u_S = −μ_S`) and a `CoordStep`;
* `exHeightOneSwitchData`: a `HeightOneSwitchData` with a stage of fiber dimension three switching to
  a stage of fiber dimension one (the switch fields genuinely exercised);
* `exOuterSwitchData`: an `OuterSwitchData` with a stage of outer dimension three switching to one
  of outer dimension one (inner coordinates `1`, switch coordinates of valuation zero);
* `exModelStage`, `exOuterOfModels`: a `ModelStage` over `ℤ₂ ⊂ ℚ₂` and the
  `OuterSwitchData.ofModels` built from it (its `minor_link` proved from the outer model);
* `exGaloisCocycleInvolution`: `GaloisCocycleInvolution` for `Γ = ℤ/2`, `Δ = 1`, the sign character,
  `K` concentrated in degree one, `σ = −1` and a nonzero localization (`exGalLoc_ne_zero`);
* Selmer level, over complexes concentrated in degree one (`G = ℚ` with `res = 0`, `U_rel = F ⊕ S`,
  `L = S` with `ι = pr_S`): `exRel : RelaxedLocalization ℚ`, `exSideF`, `exSideS : SwitchSide`, the
  relaxed image `exRel_U : U = F`, the side cohomology `dim H¹(C(U_F)) = 3`, `dim H¹(C(U_S)) = 1`,
  `dim H¹(C(U_str)) = 1`, `exSelmerNonquadStep : SelmerNonquadStep ℚ`, `exSelmerSwitchData` (a
  `SelmerSwitchData` with a genuine switch) and `exSelmerQuadSwitch : SelmerQuadSwitch ℚ id`.

Not constructed here: `SelmerQuadMixedStep` and `SelmerQuadSingleStep` (they need an equivariant
Selmer model on which the involutions act with both signs; their dimension-level counterparts
`QuadMixedDims`, `QuadSingleDims` are inhabited above).
-/

noncomputable section

namespace ZInQ.Contrib.CloudB3RC53.SwitchInputs

open Matrix Module ZInQ.Manuscript.RC.Uniform ZInQ.Manuscript.RC.Uniform.QuadraticCase
  ZInQ.Contrib.CloudB3RC53.UniformSwitch

/-! ### Local data over `ℚ` -/

/-- `J₀ = diag(1, −1)`. -/
def J₀ : Matrix (Fin 2) (Fin 2) ℚ := !![1, 0; 0, -1]

/-- `J₀` as a linear map. -/
def J₀L : (Fin 2 → ℚ) →ₗ[ℚ] (Fin 2 → ℚ) := Matrix.toLin' J₀

/-- `e₊ = (1, 0)`. -/
def eP : Fin 2 → ℚ := ![1, 0]

/-- `e₋ = (0, 1)`. -/
def eM : Fin 2 → ℚ := ![0, 1]

theorem J₀L_eP : J₀L eP = eP := by
  ext i; fin_cases i <;> simp [J₀L, J₀, eP, Matrix.mulVec, dotProduct, Fin.sum_univ_two]

theorem J₀L_eM : J₀L eM = -eM := by
  ext i; fin_cases i <;> simp [J₀L, J₀, eM, Matrix.mulVec, dotProduct, Fin.sum_univ_two]

theorem e₂_eP_eM : e₂ eP eM = 1 := by simp [eP, eM]

theorem e₂_eP_eM_ne : e₂ eP eM ≠ 0 := by rw [e₂_eP_eM]; exact one_ne_zero

theorem eP_ne : eP ≠ 0 := fun h => by simpa [eP] using congrFun h 0

theorem eM_ne : eM ≠ 0 := fun h => by simpa [eM] using congrFun h 1

theorem J₀_sq : J₀ * J₀ = 1 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [J₀, Matrix.mul_apply, Fin.sum_univ_two]

theorem J₀_det : J₀.det = -1 := by simp [J₀, Matrix.det_fin_two]

theorem J₀L_sq : J₀L ∘ₗ J₀L = LinearMap.id := by
  rw [J₀L, ← Matrix.toLin'_mul, J₀_sq, Matrix.toLin'_one]

theorem two_ne_zero_ℚ : (2 : ℚ) ≠ 0 := by norm_num

/-! ### Dimension data -/

theorem exUp_sa : IsSelfAnnihilatingIn (1 : ℚ) J₀L (signPlane eP eM) (finAxis eP) :=
  ((selfAnnihilating_eq_axis two_ne_zero_ℚ 1 one_ne_zero J₀L eP eM J₀L_eP J₀L_eM
    e₂_eP_eM_ne (finAxis eP)).1).2 (Or.inl rfl)

theorem exUm_sa : IsSelfAnnihilatingIn (1 : ℚ) J₀L (signPlane eM eP) (finAxis eM) :=
  ((selfAnnihilating_eq_axis two_ne_zero_ℚ 1 one_ne_zero J₀L eP eM J₀L_eP J₀L_eM
    e₂_eP_eM_ne (finAxis eM)).2).2 (Or.inl rfl)

theorem exUm_sing_sa : IsSelfAnnihilatingIn (1 : ℚ) J₀L (signPlane eM eP) (singAxis eP) :=
  ((selfAnnihilating_eq_axis two_ne_zero_ℚ 1 one_ne_zero J₀L eP eM J₀L_eP J₀L_eM
    e₂_eP_eM_ne (singAxis eP)).2).2 (Or.inr rfl)

theorem mem_finAxis_self (f : Fin 2 → ℚ) : ((f, 0) : (Fin 2 → ℚ) × (Fin 2 → ℚ)) ∈ finAxis f :=
  Submodule.mem_prod.2 ⟨Submodule.mem_span_singleton_self f, Submodule.zero_mem _⟩

theorem pair_ne_zero {f : Fin 2 → ℚ} (hf : f ≠ 0) : ((f, 0) : (Fin 2 → ℚ) × (Fin 2 → ℚ)) ≠ 0 :=
  fun h => hf (congrArg Prod.fst h)

/-- **Mixed signs**: `QuadMixedDims 2 2 1 1` with `U_± = F(e_±)`, `K₀^± ≅ ℚ`: the sign dimensions
`(2, 2)` drop to `(1, 1)`. -/
def exQuadMixedDims : QuadMixedDims (k := ℚ) 2 2 1 1 where
  h2 := two_ne_zero_ℚ
  ε := 1
  hε := one_ne_zero
  J := J₀L
  ep := eP
  em := eM
  hp := J₀L_eP
  hm := J₀L_eM
  he := e₂_eP_eM_ne
  Up := finAxis eP
  Um := finAxis eM
  hUp := exUp_sa
  hUm := exUm_sa
  hdetp := ⟨_, mem_finAxis_self eP, mem_finAxis_self eP, pair_ne_zero eP_ne⟩
  hdetm := ⟨_, mem_finAxis_self eM, mem_finAxis_self eM, pair_ne_zero eM_ne⟩
  kp := 1
  km := 1
  hVp := by rw [inf_idem, finrank_finAxis eP_ne]
  hVm := by rw [inf_idem, finrank_finAxis eM_ne]
  hVp' := by rw [finAxis_inf_singAxis, finrank_bot]
  hVm' := by rw [finAxis_inf_singAxis, finrank_bot]

/-- **One sign only**: `QuadSingleDims 2 1 1` with `U_+ = F(e_+)`, `U_- = S(e_+)`. -/
def exQuadSingleDims : QuadSingleDims (k := ℚ) 2 1 1 where
  h2 := two_ne_zero_ℚ
  ε := 1
  hε := one_ne_zero
  J := J₀L
  ep := eP
  em := eM
  hp := J₀L_eP
  hm := J₀L_eM
  he := e₂_eP_eM_ne
  Up := finAxis eP
  Um := singAxis eP
  hUp := exUp_sa
  hUm := exUm_sing_sa
  hdetp := ⟨_, mem_finAxis_self eP, mem_finAxis_self eP, pair_ne_zero eP_ne⟩
  kp := 1
  km := 0
  hs := by norm_num
  hVp := by rw [inf_idem, finrank_finAxis eP_ne]
  hVm := by rw [inf_comm, finAxis_inf_singAxis, finrank_bot]
  hVp' := by rw [finAxis_inf_singAxis, finrank_bot]
  hVm' := by rw [inf_idem, finrank_singAxis eP_ne]

/-- **A nonquadratic switch**: `NonquadDims 3 1` with `U = F`, `K₀ ≅ ℚ`. -/
def exNonquadDims : NonquadDims (k := ℚ) 3 1 where
  U := finPlane ℚ (Fin 2 → ℚ) (Fin 2 → ℚ)
  hU := rfl
  k0 := 1
  hs := by rw [inf_idem, finrank_finPlane_two]
  hs' := by rw [finPlane_inf_singPlane, finrank_bot]

/-! ### The GLUE inputs on the example -/

/-- **`LocalizationDualityInput` is satisfiable**: for `U = F` and any `ε, σ ≠ 0`, `J² = 1`. -/
theorem exLocalizationDuality (ε σ : ℚ) (hε : ε ≠ 0) (hσ : σ ≠ 0) (J : Matrix (Fin 2) (Fin 2) ℚ)
    (hJ2 : J * J = 1) :
    LocalizationDualityInput ε σ J hε hσ hJ2 (finPlane ℚ (Fin 2 → ℚ) (Fin 2 → ℚ)) := by
  unfold LocalizationDualityInput
  have hperf := crossPairing_isPerfPair hε hJ2
  exact orthogonal_finPlane _ hperf.bijective_right.injective σ

/-- The localization of the example: `V = ℚ²` with sign involution `T = diag(1, −1)`, localizing
`c₊ = e₊ ↦ (e₊, 0)` and `c₋ = e₋ ↦ (e₋, 0)` (injective). -/
def exLoc : (Fin 2 → ℚ) →ₗ[ℚ] (Fin 2 → ℚ) × (Fin 2 → ℚ) := LinearMap.inl ℚ _ _

/-- **`DetectingPrime` with nonzero classes**: `c₊ = e₊ ∈ V₊`, `c₋ = e₋ ∈ V₋` for `T = J₀`. -/
theorem exDetectingPrime : DetectingPrime J₀L exLoc eP eM := fun _ _ =>
  ⟨pair_ne_zero eP_ne, pair_ne_zero eM_ne⟩

/-- **`DetectingPrimePlus` with a nonzero class.** -/
theorem exDetectingPrimePlus : DetectingPrimePlus J₀L exLoc eP := fun _ => pair_ne_zero eP_ne

/-- The hypotheses of `exDetectingPrime` are met: `c₊ ∈ V₊`, `c₋ ∈ V₋`, both nonzero. -/
theorem exDetecting_hyps : J₀L eP = eP ∧ J₀L eM = -eM ∧ eP ≠ 0 ∧ eM ≠ 0 :=
  ⟨J₀L_eP, J₀L_eM, eP_ne, eM_ne⟩

/-! ### Switch coordinate data -/

/-- `b = (e₀, e₁)`, the standard basis of `R = ℚ²`. -/
abbrev bStd : Basis (Fin 2) ℚ (Fin 2 → ℚ) := Pi.basisFun ℚ (Fin 2)

/-- The strict volume form `ω(φ, ψ) = φ(e₀) ψ(e₁) − φ(e₁) ψ(e₀)` on `H²(C_str) = R^∨`. -/
def exOmega : LinearMap.BilinForm ℚ (Module.Dual ℚ (Fin 2 → ℚ)) :=
  LinearMap.mk₂ ℚ (fun φ ψ => φ (bStd 0) * ψ (bStd 1) - φ (bStd 1) * ψ (bStd 0))
    (fun _ _ _ => by simp only [LinearMap.add_apply]; ring)
    (fun _ _ _ => by simp only [LinearMap.smul_apply, smul_eq_mul]; ring)
    (fun _ _ _ => by simp only [LinearMap.add_apply]; ring)
    (fun _ _ _ => by simp only [LinearMap.smul_apply, smul_eq_mul]; ring)

theorem exOmega_apply (φ ψ : Module.Dual ℚ (Fin 2 → ℚ)) :
    exOmega φ ψ = φ (bStd 0) * ψ (bStd 1) - φ (bStd 1) * ψ (bStd 0) := rfl

theorem exOmega_alt : LinearMap.IsAlt exOmega := fun φ => by rw [exOmega_apply]; ring

theorem exOmega_basis : exOmega (bStd.dualBasis 0) (bStd.dualBasis 1) = 1 := by
  rw [exOmega_apply]; simp

/-- The localizations `f = [[1,0],[0,0]]`, `s = [[0,1],[0,0]]` with `v = (1, 0)`: `f e₀ = v`,
`s e₀ = 0`, `f e₁ = 0`, `s e₁ = J₀ v = v`. -/
def exF : (Fin 2 → ℚ) →ₗ[ℚ] (Fin 2 → ℚ) := Matrix.toLin' !![1, 0; 0, 0]

def exS : (Fin 2 → ℚ) →ₗ[ℚ] (Fin 2 → ℚ) := Matrix.toLin' !![0, 1; 0, 0]

theorem exF_A : exF (bStd 0) = eP := by
  ext i; fin_cases i <;> simp [exF, eP, Matrix.mulVec, dotProduct, Fin.sum_univ_two]

theorem exS_A : exS (bStd 0) = 0 := by
  ext i; fin_cases i <;> simp [exS, Matrix.mulVec, dotProduct, Fin.sum_univ_two]

theorem exF_B : exF (bStd 1) = 0 := by
  ext i; fin_cases i <;> simp [exF, Matrix.mulVec, dotProduct, Fin.sum_univ_two]

theorem exS_B : exS (bStd 1) = J₀ *ᵥ eP := by
  ext i; fin_cases i <;> simp [exS, J₀, eP, Matrix.mulVec, dotProduct, Fin.sum_univ_two]

/-- **`SwitchCoordData` on the example** (`ε = σ = 1`, `J = J₀`, `v = e₊`, complements
`x = y = e₁`, `w = e₀^*`, `w' = e₁^*`), with volume normalizations `μ_F, μ_S`; all fields hold. -/
def exSwitchCoordData (μF μS : ℚ) : SwitchCoordData ℚ where
  ε := 1
  σ := 1
  J := J₀
  f := exF
  s := exS
  v := eP
  ω := exOmega
  μF := μF
  μS := μS
  x := eM
  y := eM
  w := bStd.dualBasis 0
  w' := bStd.dualBasis 1
  hσ := by norm_num
  hJ2 := J₀_sq
  hJdet := J₀_det
  hfA := exF_A
  hsA := exS_A
  hfB := exF_B
  hsB := exS_B
  hω := exOmega_alt
  hxw := by
    rw [omega_bdryF bStd J₀_sq exS_A exS_B exOmega_alt, exOmega_basis]
    simp [weil, eP, eM]
  hyw := by
    rw [omega_bdryS bStd exF_A exF_B exOmega_alt, exOmega_basis]
    simp [weil, eP, eM, J₀]

/-! ### A height-one switching datum with a genuine switch -/

/-- The stage of fiber dimension three: `[ℚ³ --0--> ℚ³]`, cycle `e₀`, functional `0`, coordinate
`u` (any `u` is a coordinate since `adj 0 = 0` in size three). -/
def exStage3 (u : ℚ) : TwoTermStage (RingHom.id ℚ) where
  n := 2
  D := 0
  z := ![1, 0, 0]
  w := 0
  u := u
  hz := by simp
  hw := by simp
  hu := by
    unfold ZInQ.Manuscript.RC.Central.IsClassFunctionalCoord
    rw [Matrix.map_zero _ (map_zero _), adjugate_zero, smul_zero]
    ext i j; simp [vecMulVec]

/-- The stage of fiber dimension one: `[ℚ --0--> ℚ]`, cycle `1`, functional `u`, coordinate `u`. -/
def exStage1 (u : ℚ) : TwoTermStage (RingHom.id ℚ) where
  n := 0
  D := 0
  z := fun _ => 1
  w := fun _ => u
  u := u
  hz := by simp
  hw := by simp
  hu := by
    unfold ZInQ.Manuscript.RC.Central.IsClassFunctionalCoord
    rw [adjugate_fin_one]
    ext i j; fin_cases i; fin_cases j; simp [vecMulVec]

theorem fiberDim_zero_matrix (S : TwoTermStage (RingHom.id ℚ)) (hD : S.D = 0) : S.fiberDim (RingHom.id ℚ) = S.n + 1 := by
  have h0 : (S.D.map (RingHom.id ℚ)).mulVecLin = 0 := by
    rw [hD]; apply LinearMap.ext; intro v; ext i; simp
  rw [TwoTermStage.fiberDim, h0, LinearMap.ker_zero, finrank_top, finrank_fin_fun]

theorem exStage3_fiberDim (u : ℚ) : (exStage3 u).fiberDim (RingHom.id ℚ) = 3 :=
  fiberDim_zero_matrix _ rfl

theorem exStage1_fiberDim (u : ℚ) : (exStage1 u).fiberDim (RingHom.id ℚ) = 1 :=
  fiberDim_zero_matrix _ rfl

/-- The coordinate step of the example switch: old coordinate `u_F`, new coordinate `u_S`, unit
normalizations `μ_F = μ_S = 1`. -/
def exCoordStep : CoordStep (RingHom.id ℚ) (exSwitchCoordData 1 1).uF (exSwitchCoordData 1 1).uS where
  X := exSwitchCoordData 1 1
  mF := 1
  mS := 1
  σ₀ := 1
  hmF := isUnit_one
  hmS := isUnit_one
  hμF := rfl
  hμS := rfl
  hσ₀ := rfl
  hu := rfl
  hu' := rfl

/-- **A `HeightOneSwitchData` in which a switch happens**: a nonquadratic configuration of fiber
dimension three switches (`NonquadDims 3 1`, coordinate step `exCoordStep`) to one of fiber
dimension one. -/
def exHeightOneSwitchData : HeightOneSwitchData (RingHom.id ℚ) (RingHom.id ℚ) where
  Stage := Bool
  stage b := if b then exStage3 (exSwitchCoordData 1 1).uF else exStage1 (exSwitchCoordData 1 1).uS
  quadratic := False
  sp _ := 0
  sm _ := 0
  sign_sum h := h.elim
  primitive b := by
    cases b
    · exact ⟨0, by simp [exStage1]⟩
    · exact ⟨0, by simp [exStage3]⟩
  switch_mixed b _ hs := by
    cases b
    · exfalso
      have h1 := exStage1_fiberDim (exSwitchCoordData 1 1).uS
      simp only [Bool.false_eq_true, ↓reduceIte] at hs
      omega
    · refine ⟨false, ⟨exCoordStep⟩, fun h => h.elim, fun _ => ?_⟩
      simp only [↓reduceIte, Bool.false_eq_true]
      rw [exStage3_fiberDim, exStage1_fiberDim]
      exact ⟨exNonquadDims⟩
  switch_single _ h := h.elim

/-- The example genuinely switches: its first stage has fiber dimension three. -/
theorem exHeightOne_switches :
    1 < (exHeightOneSwitchData.stage true).fiberDim (RingHom.id ℚ) := by
  show 1 < (exStage3 _).fiberDim (RingHom.id ℚ)
  rw [exStage3_fiberDim]; norm_num

/-- Regularity is derived from the example data through RC16's process. -/
theorem exHeightOne_regular (b : Bool) :
    ∃ a : ℚ, RingHom.id ℚ a = (exHeightOneSwitchData.stage b).u :=
  regular_of_switchData (fun _ _ h => h) (fun x hx => by
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, isUnit_iff_ne_zero, not_not] at hx
    simp [hx]) exHeightOneSwitchData b

/-! ### The switch coordinates of the example -/

theorem exSwitchCoordData_uF (μF μS : ℚ) : (exSwitchCoordData μF μS).uF = μF := by
  have hden := (exSwitchCoordData μF μS).hxw
  simp only [SwitchCoordData.uF, coordF, vol_apply]
  change μF * weil (exF (bStd 0)) eM * Module.Dual.eval ℚ _ (bStd 0) (bStd.dualBasis 0) /
    exOmega (bdryF 1 1 J₀ exF exS eM) (bStd.dualBasis 0) = μF
  rw [omega_bdryF bStd J₀_sq exS_A exS_B exOmega_alt, exOmega_basis, exF_A]
  simp [weil, eP, eM]

theorem exSwitchCoordData_uS (μF μS : ℚ) : (exSwitchCoordData μF μS).uS = -μS := by
  simp only [SwitchCoordData.uS, coordS, vol_apply]
  change μS * weil (exS (bStd 1)) eM * Module.Dual.eval ℚ _ (bStd 1) (bStd.dualBasis 1) /
    exOmega (bdryS 1 1 J₀ exF exS eM) (bStd.dualBasis 1) = -μS
  rw [omega_bdryS bStd exF_A exF_B exOmega_alt, exOmega_basis, exS_B]
  simp [weil, eP, eM, J₀, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  ring

/-! ### An outer switching datum with a genuine switch -/

/-- The cyclic column list `e₁, e₂, e₀` has determinant one. -/
theorem det_cyclic3 :
    detCols (colsDWY (Matrix.diagonal ![(0 : ℚ), 1, 1]) ![![0, 1, 0], ![0, 0, 1]] ![1, 0, 0]) = 1 := by
  simp only [detCols, colsMat, colsDWY]
  rw [Matrix.det_fin_three]
  simp [Fin.snoc, Matrix.mulVec, dotProduct, Fin.sum_univ_three, Matrix.diagonal]

theorem det_id3 : detCols (colsZW ![(1 : ℚ), 0, 0] ![![0, 1, 0], ![0, 0, 1]]) = 1 := by
  simp only [detCols, colsMat, colsZW]
  rw [Matrix.det_fin_three]
  simp

/-- The configuration of outer dimension three: outer model `0` on `ℚ³`, inner models
`diag(0, 1, 1)` (rank two, as `hden` requires) with cycle and functional `e₀`, complements
`e₁, e₂` and `y = e₀`. Its inner coordinates are all `1`. -/
noncomputable def exOuterStage3 : OuterStage ℚ ℚ ℕ where
  m := 2
  Dout := 0
  zout := ![1, 0, 0]
  hzout := by simp
  hzout0 := fun h => by simpa using congrFun h 0
  n := 2
  D := fun _ => Matrix.diagonal ![0, 1, 1]
  z := fun _ => ![1, 0, 0]
  lam := fun _ => ![1, 0, 0]
  w := fun _ => ![![0, 1, 0], ![0, 0, 1]]
  y := fun _ => ![1, 0, 0]
  hz := fun _ => by ext i; fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three]
  hlam := fun _ => by ext i; fin_cases i <;> simp [Matrix.vecMul, dotProduct, Fin.sum_univ_three]
  hden := fun _ => by rw [det_cyclic3]; exact one_ne_zero

theorem exOuterStage3_outerDim : exOuterStage3.outerDim = 3 := by
  have h0 : (exOuterStage3.Dout).mulVecLin = 0 := by
    apply LinearMap.ext; intro v; ext i; simp [exOuterStage3]; rfl
  rw [OuterStage.outerDim, h0, LinearMap.ker_zero, finrank_top, finrank_fin_fun]; rfl

theorem exOuterStage3_coord (j : ℕ) : exOuterStage3.coord j = 1 := by
  simp only [OuterStage.coord, classFunctionalCoordWith]
  change detCols (colsZW ![(1 : ℚ), 0, 0] ![![0, 1, 0], ![0, 0, 1]]) * (![(1 : ℚ), 0, 0] ⬝ᵥ ![1, 0, 0]) /
    detCols (colsDWY (Matrix.diagonal ![(0 : ℚ), 1, 1]) ![![0, 1, 0], ![0, 0, 1]] ![1, 0, 0]) = 1
  rw [det_id3, det_cyclic3]
  simp [dotProduct, Fin.sum_univ_three]

theorem exampleOuterStage_coord (j : ℕ) : exampleOuterStage.coord j = 1 := by
  simp only [OuterStage.coord, classFunctionalCoordWith]
  have h1 : detCols (colsZW (fun _ : Fin 1 => (1 : ℚ)) Fin.elim0) = 1 := by
    simp only [detCols, colsMat, colsZW]
    rw [Matrix.det_fin_one]; simp
  have h2 := example_hden
  change detCols (colsZW (fun _ : Fin 1 => (1 : ℚ)) Fin.elim0) * ((fun _ : Fin 1 => (1 : ℚ)) ⬝ᵥ
    fun _ => 1) / detCols (colsDWY (0 : Matrix (Fin 1) (Fin 1) ℚ) Fin.elim0 (fun _ => 1)) = 1
  have h3 : detCols (colsDWY (0 : Matrix (Fin 1) (Fin 1) ℚ) Fin.elim0 (fun _ => 1)) = 1 := by
    simp only [detCols, colsMat, colsDWY]
    rw [Matrix.det_fin_one]; simp [Fin.snoc]
  rw [h1, h3]; simp [dotProduct]

theorem vTwo_nonneg_01 (q : ℚ) (hq : q = 0 ∨ q = 1) : (0 : WithTop ℤ) ≤ vTwo q := by
  rcases hq with rfl | rfl
  · simp
  · simp

theorem zero3_minor (k0 j0 : Fin 3) :
    ((0 : Matrix (Fin 3) (Fin 3) ℚ).submatrix k0.succAbove j0.succAbove).det = 0 := by
  have : (0 : Matrix (Fin 3) (Fin 3) ℚ).submatrix k0.succAbove j0.succAbove =
      (0 : Matrix (Fin 2) (Fin 2) ℚ) := by
    ext a b; simp
  rw [this, Matrix.det_zero]

/-- **An `OuterSwitchData` in which a switch happens**: a configuration of outer dimension three
switches (`NonquadDims 3 1` over `K_out = ℚ`, switch coordinates `μ_F = 1`, `μ_S = −1`, valuation
zero) to the configuration of outer dimension one of `exampleOuterData`. -/
noncomputable def exOuterSwitchData (𝒰 : Ultrafilter ℕ) :
    OuterSwitchData (K := ℚ) (Kout := ℚ) (J := ℕ) vTwo 𝒰 0 where
  Stage := Bool
  stage b := if b then exOuterStage3 else exampleOuterStage
  minor_link b k0 j0 h := by
    cases b
    · exact (exampleOuterData 𝒰).minor_link () k0 j0 h
    · exfalso
      exact h (zero3_minor k0 j0)
  cycle_integral b j i := by
    cases b
    · exact vTwo_nonneg_01 _ (Or.inr rfl)
    · change (0 : WithTop ℤ) ≤ vTwo (![(1 : ℚ), 0, 0] i)
      fin_cases i
      · exact vTwo_nonneg_01 _ (Or.inr rfl)
      · exact vTwo_nonneg_01 _ (Or.inl rfl)
      · exact vTwo_nonneg_01 _ (Or.inl rfl)
  functional_bound b j i := by
    cases b
    · simp [exampleOuterStage]
    · change (((-(0 : ℕ) : ℤ)) : WithTop ℤ) ≤ vTwo (![(1 : ℚ), 0, 0] i)
      simp only [Nat.cast_zero, neg_zero, WithTop.coe_zero]
      fin_cases i
      · exact vTwo_nonneg_01 _ (Or.inr rfl)
      · exact vTwo_nonneg_01 _ (Or.inl rfl)
      · exact vTwo_nonneg_01 _ (Or.inl rfl)
  switch b hs := by
    cases b
    · exfalso
      change 1 < exampleOuterStage.outerDim at hs
      rw [exampleOuterStage_outerDim] at hs
      exact lt_irrefl 1 hs
    · refine ⟨false, ?_, Filter.Eventually.of_forall fun j => ⟨exSwitchCoordData 1 (-1), ?_, ?_, ?_, ?_⟩⟩
      · change Nonempty (NonquadDims exOuterStage3.outerDim exampleOuterStage.outerDim)
        rw [exOuterStage3_outerDim, exampleOuterStage_outerDim]
        exact ⟨exNonquadDims⟩
      · change vTwo 1 = 0; simp
      · change vTwo (-1) = 0; simp
      · change exOuterStage3.coord j = _
        rw [exOuterStage3_coord, exSwitchCoordData_uF]
      · change exampleOuterStage.coord j = _
        rw [exampleOuterStage_coord, exSwitchCoordData_uS, neg_neg]

theorem exOuter_switches (𝒰 : Ultrafilter ℕ) : 1 < ((exOuterSwitchData 𝒰).stage true).outerDim := by
  change 1 < exOuterStage3.outerDim
  rw [exOuterStage3_outerDim]; norm_num

/-! ### An outer model stage (`ModelStage`) -/

section ModelExample

open ZInQ.Manuscript.RC.Limits

/-- **A `ModelStage`** over `R = ℤ₂`, `ϖ = 2`, `K = ℚ₂`: inner models `[ℤ₂ --0--> ℤ₂]`, outer kernel
vector `1`, cycle, functional and complement `1`. -/
noncomputable def exModelStage (𝒰 : Ultrafilter ℕ) : ModelStage 𝒰 (2 : ℤ_[2]) ℚ_[2] where
  n := 0
  M := fun _ => 0
  zout := fun _ => 1
  hzout := by
    have : outerMatrix 𝒰 (2 : ℤ_[2]) (fun _ : ℕ => (0 : Matrix (Fin 1) (Fin 1) ℤ_[2])) = 0 := by
      ext a b; simp [outerMatrix]; rfl
    rw [this, Matrix.map_zero _ (map_zero _), Matrix.zero_mulVec]
  hzout0 := fun h => one_ne_zero (congrFun h 0)
  z := fun _ _ => 1
  lam := fun _ _ => 1
  w := fun _ => Fin.elim0
  y := fun _ _ => 1
  hz := fun _ => by rw [Matrix.map_zero _ (map_zero _)]; simp
  hlam := fun _ => by rw [Matrix.map_zero _ (map_zero _)]; simp
  hden := fun _ => by
    simp only [detCols, colsMat, colsDWY]
    rw [Matrix.det_fin_one]; simp [Fin.snoc]

theorem exModelStage_outerDim (𝒰 : Ultrafilter ℕ) : (exModelStage 𝒰).toOuterStage.outerDim = 1 := by
  have h0 : ((exModelStage 𝒰).toOuterStage.Dout).mulVecLin = 0 := by
    have : outerMatrix 𝒰 (2 : ℤ_[2]) (fun _ : ℕ => (0 : Matrix (Fin 1) (Fin 1) ℤ_[2])) = 0 := by
      ext a b; simp [outerMatrix]; rfl
    apply LinearMap.ext; intro v; ext i
    simp [ModelStage.toOuterStage, exModelStage, this]; rfl
  rw [OuterStage.outerDim, h0, LinearMap.ker_zero, finrank_top, finrank_fin_fun]; rfl

/-- **`OuterSwitchData.ofModels` is inhabited** (with its `minor_link` proved from the outer model):
one model stage of outer dimension one, the `2`-adic valuation of `ℚ₂`. -/
noncomputable def exOuterOfModels (𝒰 : Ultrafilter ℕ) :
    OuterSwitchData (Kout := FractionRing (OInf 𝒰 (2 : ℤ_[2]))) (Padic.addValuation (p := 2)) 𝒰 0 :=
  OuterSwitchData.ofModels (Padic.addValuation (p := 2)) (Subtype.coe_injective)
    isPiAdicOn_padic Unit (fun _ => exModelStage 𝒰)
    (fun _ _ _ => by simp [ModelStage.toOuterStage, exModelStage])
    (fun _ _ _ => by simp [ModelStage.toOuterStage, exModelStage])
    (fun _ hs => by rw [exModelStage_outerDim] at hs; exact absurd hs (lt_irrefl 1))

end ModelExample

/-! ### The Galois cocycle involution (`GaloisCocycleInvolution`) -/

section GaloisExample

open CategoryTheory

/-- `Γ = ℤ/2` (multiplicatively), `Δ = 1` of index two, `τ` the generator. -/
abbrev Γ₂ : Type := Multiplicative (ZMod 2)

def τ₂ : Γ₂ := Multiplicative.ofAdd 1

theorem bot_index_two : (⊥ : Subgroup Γ₂).index = 2 := by
  rw [Subgroup.index_bot, Nat.card_eq_fintype_card]; rfl

theorem τ₂_not_mem : τ₂ ∉ (⊥ : Subgroup Γ₂) := by
  rw [Subgroup.mem_bot]; decide

theorem τ₂_sq : τ₂ * τ₂ = 1 := by decide

/-- The sign character `ρ(τ) = −1` on `T = ℚ`: `ρ(g) = (−1)^{val g}`. -/
def signρ : Γ₂ →* (ℚ →ₗ[ℚ] ℚ) where
  toFun g := (-1) ^ (Multiplicative.toAdd g).val
  map_one' := by simp
  map_mul' a b := by
    rw [toAdd_mul, ZMod.val_add, ← neg_one_pow_eq_pow_mod_two, pow_add]

/-- The complex `K` concentrated in degree one with `K¹ = (Δ → ℚ)`. -/
noncomputable abbrev exK : CochainComplex (ModuleCat.{0} ℚ) ℤ :=
  (HomologicalComplex.single (ModuleCat ℚ) (ComplexShape.up ℤ) 1).obj
    (ModuleCat.of ℚ (↥(⊥ : Subgroup Γ₂) → ℚ))

/-- The cochain model `ev : K¹ ≅ (Δ → ℚ)`. -/
noncomputable def exEv : exK.X 1 →ₗ[ℚ] (↥(⊥ : Subgroup Γ₂) → ℚ) :=
  (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 1
    (ModuleCat.of ℚ (↥(⊥ : Subgroup Γ₂) → ℚ))).hom.hom

/-- The localization `v ↦ (v(1) e₋, 0)` through `H¹(K) ≅ (Δ → ℚ)`. -/
noncomputable def exGalLoc : exK.homology 1 →ₗ[ℚ] (Fin 2 → ℚ) × (Fin 2 → ℚ) :=
  LinearMap.inl ℚ _ _ ∘ₗ (LinearMap.smulRight (LinearMap.proj (1 : ↥(⊥ : Subgroup Γ₂))) eM) ∘ₗ
    (HomologicalComplex.singleObjHomologySelfIso (ComplexShape.up ℤ) 1
      (ModuleCat.of ℚ (↥(⊥ : Subgroup Γ₂) → ℚ))).hom.hom

theorem J₀L_det : LinearMap.det J₀L = -1 := by
  rw [J₀L, LinearMap.det_toLin', J₀_det]

theorem cocycleAct_sign (c : ↥(⊥ : Subgroup Γ₂) → ℚ) :
    cocycleAct (⊥ : Subgroup Γ₂) bot_index_two τ₂ signρ c = -c := by
  ext g
  simp only [cocycleAct, LinearMap.coe_mk, AddHom.coe_mk, Pi.neg_apply]
  have hg : conjSub (⊥ : Subgroup Γ₂) bot_index_two τ₂ g = g := Subsingleton.elim _ _
  rw [hg]
  have hv : (1 : ZMod 2).val = 1 := rfl
  simp [signρ, τ₂, hv]

/-- **`GaloisCocycleInvolution` is satisfiable with a nontrivial involution and a nonzero
localization**: `σ = −1` on `K` (the cocycle action of the sign character), `J_ℓ = J₀`, and the
localization into the `−1`-eigenline `F(e₋)` of the local involution. -/
theorem exGaloisCocycleInvolution :
    GaloisCocycleInvolution (⊥ : Subgroup Γ₂) bot_index_two τ₂ τ₂_not_mem τ₂_sq signρ exK exEv
      J₀L J₀L_sq J₀L_det exGalLoc := by
  refine ⟨(HomologicalComplex.single (ModuleCat ℚ) (ComplexShape.up ℤ) 1).map (-𝟙 _), ?_, ?_, ?_⟩
  · rw [← CategoryTheory.Functor.map_comp, Preadditive.neg_comp_neg, Category.comp_id,
      CategoryTheory.Functor.map_id]
  · intro x
    rw [cocycleAct_sign]
    simp only [exEv, HomologicalComplex.single_map_f_self]
    simp
  · intro v
    have hn := HomologicalComplex.singleObjHomologySelfIso_hom_naturality (ComplexShape.up ℤ) 1
      (-𝟙 (ModuleCat.of ℚ (↥(⊥ : Subgroup Γ₂) → ℚ)))
    have hv := congrArg (fun f => ModuleCat.Hom.hom f v) hn
    simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at hv
    simp only [exGalLoc, LinearMap.comp_apply, hv]
    ext i <;> simp [localInv, J₀L_eM]

/-- The localization of the example is nonzero. -/
theorem exGalLoc_ne_zero : exGalLoc ≠ 0 := by
  intro h
  have := congrArg (fun f => f ((HomologicalComplex.singleObjHomologySelfIso (ComplexShape.up ℤ) 1
      (ModuleCat.of ℚ (↥(⊥ : Subgroup Γ₂) → ℚ))).inv.hom (fun _ => 1))) h
  simp only [exGalLoc, LinearMap.comp_apply, LinearMap.zero_apply] at this
  have h2 := congrArg (fun z : (Fin 2 → ℚ) × (Fin 2 → ℚ) => z.1 1) this
  simp [eM] at h2

end GaloisExample

/-! ### Selmer-level models: complexes concentrated in degree one -/

section SelmerExample

open CategoryTheory ZInQ.Contrib.CloudB3RC53.PairedFunctional ZInQ.Contrib.CloudB3RC53.SelmerDuality

/-- `dimAt a n = a` for `n = 1`, `0` otherwise. -/
def dimAt (a : ℕ) (n : ℤ) : ℕ := if n = 1 then a else 0

theorem dimAt_one (a : ℕ) : dimAt a 1 = a := by unfold dimAt; simp

theorem dimAt_ne (a : ℕ) {n : ℤ} (h : n ≠ 1) : dimAt a n = 0 := by unfold dimAt; simp [h]

/-- The module `ℚ^a` in degree one, `0` elsewhere. -/
abbrev Pn (a : ℕ) (n : ℤ) : ModuleCat.{0} ℚ := ModuleCat.of ℚ (Fin (dimAt a n) → ℚ)

/-- `F ⊕ S = ℚ² × ℚ²` in degree one, `0` elsewhere. -/
abbrev Qn (n : ℤ) : ModuleCat.{0} ℚ :=
  ModuleCat.of ℚ ((Fin (dimAt 2 n) → ℚ) × (Fin (dimAt 2 n) → ℚ))

/-- A complex with zero differentials. -/
abbrev zGCx (X : ℤ → ModuleCat.{0} ℚ) : GCx ℚ := ⟨X, fun _ _ _ => 0, fun _ _ _ _ _ _ => rfl⟩

/-- A chain map between complexes with zero differentials, from a family of linear maps. -/
def zHom {X Y : ℤ → ModuleCat.{0} ℚ} (φ : ∀ n, X n →ₗ[ℚ] Y n) : GHom (zGCx X) (zGCx Y) where
  f n m h := by subst h; exact φ n
  comm i i₁ j j₁ hij h₁ h₂ hj x := by
    subst hij hj
    change φ i₁ 0 = 0
    exact map_zero _

theorem subsingleton_dimAt (a : ℕ) {n : ℤ} (h : n ≠ 1) : Subsingleton (Fin (dimAt a n) → ℚ) := by
  rw [dimAt_ne a h]; infer_instance

theorem concDegOne_Pn (a : ℕ) : ConcDegOne (zGCx (Pn a)) := fun _ h =>
  subsingleton_dimAt a h

theorem concDegOne_Qn : ConcDegOne (zGCx Qn) := fun n h => by
  have := subsingleton_dimAt 2 h
  change Subsingleton ((Fin (dimAt 2 n) → ℚ) × (Fin (dimAt 2 n) → ℚ))
  infer_instance

/-- `ℚ^{dimAt a 1} ≃ ℚ^a`. -/
def eqvA (a : ℕ) : (Fin (dimAt a 1) → ℚ) ≃ₗ[ℚ] (Fin a → ℚ) :=
  LinearEquiv.funCongrLeft ℚ ℚ (finCongr (dimAt_one a)).symm

/-- The zero module in every degree (the strict condition `D⁰ = 0` of the example). -/
abbrev Zn (_ : ℤ) : ModuleCat.{0} ℚ := ModuleCat.of ℚ (Fin 0 → ℚ)

/-- **The relaxed Selmer data of the example**: `G = ℚ` (one global class, `res = 0`), the relaxed
condition `U_rel = F ⊕ S`, the full local complex `L = S` with `ι = pr_S`, all in degree one; the
relaxed quotient `W_rel = F ⊕ S`, `g_R = id`. -/
def exRelD : SelData ℚ where
  G := zGCx (Pn 1)
  U := zGCx Qn
  L := zGCx (Pn 2)
  res := zHom fun _ => 0
  ι := zHom fun _ => LinearMap.snd ℚ _ _

def exRel : RelaxedLocalization ℚ where
  D := exRelD
  Wrel := zGCx Qn
  gR := zHom fun _ => LinearMap.id
  eR := (eqvA 2).prodCongr (eqvA 2)
  hWrel := concDegOne_Qn

/-- The finite side: `U_F = F` (`f₁ = inl`), `W₂ = S` (`g₂ = snd`), `U_str = 0`, `W₁ = F`. -/
def exSideF : SwitchSide exRel (finPlane ℚ (Fin 2 → ℚ) (Fin 2 → ℚ)) where
  U₁ := zGCx (Pn 2)
  Ustr := zGCx Zn
  W₁ := zGCx (Pn 2)
  W₂ := zGCx (Pn 2)
  f₁ := zHom fun _ => LinearMap.inl ℚ _ _
  g₂ := zHom fun _ => LinearMap.snd ℚ _ _
  fs := zHom fun _ => 0
  g₁ := zHom fun _ => LinearMap.id
  i := zHom fun _ => LinearMap.inl ℚ _ _
  p := zHom fun _ => LinearMap.snd ℚ _ _
  hfg₂ _ _ := rfl
  f₁_inj _ := LinearMap.inl_injective
  g₂_surj _ := LinearMap.snd_surjective
  ex₂ _ u h := ⟨u.1, Prod.ext rfl h.symm⟩
  hfg₁ _ _ := by change (0 : Fin _ → ℚ) = 0; rfl
  fs_inj _ := fun _ _ _ => Subsingleton.elim _ _
  g₁_surj _ := Function.surjective_id
  ex₁ _ u h := ⟨0, by change (0 : Fin _ → ℚ) = u; exact h.symm⟩
  hRF _ _ := rfl
  hpR _ _ := rfl
  hW₁ := concDegOne_Pn 2
  hW₂ := concDegOne_Pn 2
  i_inj := LinearMap.inl_injective
  ip_exact y := ⟨fun h => ⟨y.1, Prod.ext rfl h.symm⟩, fun ⟨x, hx⟩ => by rw [← hx]; rfl⟩
  hP := by
    ext z
    simp only [LinearMap.mem_range, LinearMap.coe_comp, Function.comp_apply, mem_finPlane]
    constructor
    · rintro ⟨x, rfl⟩
      change (eqvA 2) 0 = 0
      exact map_zero _
    · intro hz
      refine ⟨(eqvA 2).symm z.1, Prod.ext ?_ ?_⟩
      · change (eqvA 2) ((eqvA 2).symm z.1) = z.1
        exact LinearEquiv.apply_symm_apply _ _
      · change (eqvA 2) 0 = z.2
        rw [map_zero, hz]

/-- The singular side: `U_S = S` (`f₁ = inr`), `W₂ = F` (`g₂ = fst`), `U_str = 0`, `W₁ = S`. -/
def exSideS : SwitchSide exRel (singPlane ℚ (Fin 2 → ℚ) (Fin 2 → ℚ)) where
  U₁ := zGCx (Pn 2)
  Ustr := zGCx Zn
  W₁ := zGCx (Pn 2)
  W₂ := zGCx (Pn 2)
  f₁ := zHom fun _ => LinearMap.inr ℚ _ _
  g₂ := zHom fun _ => LinearMap.fst ℚ _ _
  fs := zHom fun _ => 0
  g₁ := zHom fun _ => LinearMap.id
  i := zHom fun _ => LinearMap.inr ℚ _ _
  p := zHom fun _ => LinearMap.fst ℚ _ _
  hfg₂ _ _ := rfl
  f₁_inj _ := LinearMap.inr_injective
  g₂_surj _ := LinearMap.fst_surjective
  ex₂ _ u h := ⟨u.2, Prod.ext h.symm rfl⟩
  hfg₁ _ _ := by change (0 : Fin _ → ℚ) = 0; rfl
  fs_inj _ := fun _ _ _ => Subsingleton.elim _ _
  g₁_surj _ := Function.surjective_id
  ex₁ _ u h := ⟨0, by change (0 : Fin _ → ℚ) = u; exact h.symm⟩
  hRF _ _ := rfl
  hpR _ _ := rfl
  hW₁ := concDegOne_Pn 2
  hW₂ := concDegOne_Pn 2
  i_inj := LinearMap.inr_injective
  ip_exact y := ⟨fun h => ⟨y.2, Prod.ext h.symm rfl⟩, fun ⟨x, hx⟩ => by rw [← hx]; rfl⟩
  hP := by
    ext z
    simp only [LinearMap.mem_range, LinearMap.coe_comp, Function.comp_apply, mem_singPlane]
    constructor
    · rintro ⟨x, rfl⟩
      change (eqvA 2) 0 = 0
      exact map_zero _
    · intro hz
      refine ⟨(eqvA 2).symm z.2, Prod.ext ?_ ?_⟩
      · change (eqvA 2) 0 = z.1
        rw [map_zero, hz]
      · change (eqvA 2) ((eqvA 2).symm z.2) = z.2
        exact LinearEquiv.apply_symm_apply _ _

/-- `H¹ = K¹` when both differentials at degree one vanish. -/
theorem finrank_h1_of_d_zero (K : CochainComplex (ModuleCat.{0} ℚ) ℤ) (h01 : K.d 0 1 = 0)
    (h12 : K.d 1 2 = 0) : finrank ℚ (K.homology 1) = finrank ℚ (K.X 1) :=
  LinearEquiv.finrank_eq
    ((K.isoHomologyπ 0 1 (by simp) h01).symm ≪≫ K.iCyclesIso 1 2 (by simp) h12).toLinearEquiv

theorem selCx_d01_zero (D : SelData ℚ) (h : Subsingleton (D.G.X 0 × D.U.X 0 × D.L.X (0 - 1))) :
    (selCx D).toCC.d 0 1 = 0 := by
  have : Subsingleton ((selCx D).toCC.X 0) := h
  ext x
  rw [Subsingleton.elim x 0, map_zero]
  rfl

theorem sub3 (a b c : ℕ) {n m : ℤ} (hn : n ≠ 1) (hm : m ≠ 1) :
    Subsingleton ((Fin (dimAt a n) → ℚ) × (Fin (dimAt b n) → ℚ) × (Fin (dimAt c m) → ℚ)) := by
  have := subsingleton_dimAt a hn
  have := subsingleton_dimAt b hn
  have := subsingleton_dimAt c hm
  infer_instance

/-- **The relaxed localization image is the finite plane**, `U ≤ F` (a relaxed class `(a, u, x)` has
`res a − ι u = −u_S = 0`). -/
theorem exRel_U_le : exRel.U ≤ finPlane ℚ (Fin 2 → ℚ) (Fin 2 → ℚ) := by
  intro z hz
  obtain ⟨c, ⟨c', rfl⟩, rfl⟩ := hz
  set K := (selCx exRel.D).toCC
  obtain ⟨y, rfl⟩ : ∃ y, (K.homologyπ 1).hom y = c' :=
    (ModuleCat.epi_iff_surjective _).mp inferInstance c'
  have hnat := congrArg (fun f => ModuleCat.Hom.hom f y)
    (HomologicalComplex.homologyπ_naturality (GHom.toCC (quotMap exRel.D exRel.gR)) 1)
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at hnat
  rw [mem_finPlane]
  simp only [LinearEquiv.coe_coe, LinearEquiv.trans_apply]
  rw [hnat, h1Equiv_apply]
  have hπ := congrArg (fun f => ModuleCat.Hom.hom f
    ((HomologicalComplex.cyclesMap (GHom.toCC (quotMap exRel.D exRel.gR)) 1).hom y))
    (homologyπ_h1Iso exRel.Wrel exRel.hWrel)
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at hπ
  rw [hπ]
  have hi := congrArg (fun f => ModuleCat.Hom.hom f y)
    (HomologicalComplex.cyclesMap_i (GHom.toCC (quotMap exRel.D exRel.gR)) 1)
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at hi
  rw [hi]
  have hd := congrArg (fun f => ModuleCat.Hom.hom f y) (K.iCycles_d 1 2)
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_zero,
    LinearMap.zero_apply] at hd
  erw [GCx.toCC_d_hom _ 1 2 rfl] at hd
  generalize (K.iCycles 1).hom y = w at hd ⊢
  obtain ⟨a, u, x⟩ := w
  have h3 := congrArg (fun q => q.2.2) hd
  change (0 : (Fin (dimAt 1 1) → ℚ) →ₗ[ℚ] _) a - u.2 - 0 = 0 at h3
  have h0a : (0 : (Fin (dimAt 1 1) → ℚ) →ₗ[ℚ] (Fin (dimAt 2 1) → ℚ)) a = 0 := rfl
  have h4 : (u : (Fin (dimAt 2 1) → ℚ) × (Fin (dimAt 2 1) → ℚ)).2 = 0 := by
    rw [h0a, zero_sub, sub_zero, neg_eq_zero] at h3
    exact h3
  change (eqvA 2) (u : (Fin (dimAt 2 1) → ℚ) × (Fin (dimAt 2 1) → ℚ)).2 = 0
  rw [h4, map_zero]

theorem lin_sub_sub_zero {M N : Type} [AddCommGroup M] [Module ℚ M] [AddCommGroup N] [Module ℚ N]
    (f : M →ₗ[ℚ] N) (hf : f = 0) (a : M) (b : N) (hb : b = 0) : f a - b - 0 = 0 := by
  simp [hf, hb]

theorem finrank_selX1 (D : SelData ℚ) [FiniteDimensional ℚ (D.G.X 1)]
    [FiniteDimensional ℚ (D.U.X 1)] [FiniteDimensional ℚ (D.L.X (1 - 1))] :
    finrank ℚ ((selCx D).toCC.X 1) =
      finrank ℚ (D.G.X 1) + (finrank ℚ (D.U.X 1) + finrank ℚ (D.L.X (1 - 1))) := by
  change finrank ℚ (D.G.X 1 × D.U.X 1 × D.L.X (1 - 1)) = _
  rw [Module.finrank_prod, Module.finrank_prod]

theorem exSideF_d12 : (selCx exSideF.Dside).toCC.d 1 2 = 0 := by
  ext c
  erw [GCx.toCC_d_hom _ 1 2 rfl]
  obtain ⟨a, u, x⟩ := c
  refine Prod.ext rfl (Prod.ext rfl ?_)
  change (0 : (Fin (dimAt 1 1) → ℚ) →ₗ[ℚ] _) a -
    (LinearMap.snd ℚ (Fin (dimAt 2 1) → ℚ) (Fin (dimAt 2 1) → ℚ))
      ((LinearMap.inl ℚ (Fin (dimAt 2 1) → ℚ) (Fin (dimAt 2 1) → ℚ)) u) - 0 = 0
  exact lin_sub_sub_zero _ rfl a _ rfl

theorem exSideF_h1 : finrank ℚ ((selCx exSideF.Dside).toCC.homology 1) = 3 := by
  rw [finrank_h1_of_d_zero _ (selCx_d01_zero _ (sub3 1 2 2 (by norm_num) (by norm_num)))
    exSideF_d12]
  haveI : FiniteDimensional ℚ (exSideF.Dside.G.X 1) :=
    (inferInstance : FiniteDimensional ℚ (Fin (dimAt 1 1) → ℚ))
  haveI : FiniteDimensional ℚ (exSideF.Dside.U.X 1) :=
    (inferInstance : FiniteDimensional ℚ (Fin (dimAt 2 1) → ℚ))
  haveI : FiniteDimensional ℚ (exSideF.Dside.L.X (1 - 1)) :=
    (inferInstance : FiniteDimensional ℚ (Fin (dimAt 2 (1 - 1)) → ℚ))
  rw [finrank_selX1]
  change finrank ℚ (Fin (dimAt 1 1) → ℚ) + (finrank ℚ (Fin (dimAt 2 1) → ℚ) +
    finrank ℚ (Fin (dimAt 2 (1 - 1)) → ℚ)) = 3
  simp only [Module.finrank_fin_fun]
  simp [dimAt]

theorem exSideF_str_d12 : (selCx exSideF.Dstr).toCC.d 1 2 = 0 := by
  ext c
  erw [GCx.toCC_d_hom _ 1 2 rfl]
  obtain ⟨a, u, x⟩ := c
  have hu : u = 0 := Subsingleton.elim (α := Fin 0 → ℚ) _ _
  subst hu
  refine Prod.ext rfl (Prod.ext rfl ?_)
  change (0 : (Fin (dimAt 1 1) → ℚ) →ₗ[ℚ] (Fin (dimAt 2 1) → ℚ)) a - _ - 0 = 0
  exact lin_sub_sub_zero _ rfl a _ (map_zero _)

theorem exSideF_str : finrank ℚ ((selCx exSideF.Dstr).toCC.homology 1) = 1 := by
  have h0 : Subsingleton (exSideF.Dstr.G.X 0 × exSideF.Dstr.U.X 0 × exSideF.Dstr.L.X (0 - 1)) := by
    have := subsingleton_dimAt 1 (n := 0) (by norm_num)
    have := subsingleton_dimAt 2 (n := 0 - 1) (by norm_num)
    change Subsingleton ((Fin (dimAt 1 0) → ℚ) × (Fin 0 → ℚ) × (Fin (dimAt 2 (0 - 1)) → ℚ))
    infer_instance
  rw [finrank_h1_of_d_zero _ (selCx_d01_zero _ h0) exSideF_str_d12]
  haveI : FiniteDimensional ℚ (exSideF.Dstr.G.X 1) :=
    (inferInstance : FiniteDimensional ℚ (Fin (dimAt 1 1) → ℚ))
  haveI : FiniteDimensional ℚ (exSideF.Dstr.U.X 1) :=
    (inferInstance : FiniteDimensional ℚ (Fin 0 → ℚ))
  haveI : FiniteDimensional ℚ (exSideF.Dstr.L.X (1 - 1)) :=
    (inferInstance : FiniteDimensional ℚ (Fin (dimAt 2 (1 - 1)) → ℚ))
  rw [finrank_selX1]
  change finrank ℚ (Fin (dimAt 1 1) → ℚ) + (finrank ℚ (Fin 0 → ℚ) +
    finrank ℚ (Fin (dimAt 2 (1 - 1)) → ℚ)) = 1
  simp only [Module.finrank_fin_fun]
  simp [dimAt]

theorem exSideS_str_d12 : (selCx exSideS.Dstr).toCC.d 1 2 = 0 := by
  ext c
  erw [GCx.toCC_d_hom _ 1 2 rfl]
  obtain ⟨a, u, x⟩ := c
  have hu : u = 0 := Subsingleton.elim (α := Fin 0 → ℚ) _ _
  subst hu
  refine Prod.ext rfl (Prod.ext rfl ?_)
  change (0 : (Fin (dimAt 1 1) → ℚ) →ₗ[ℚ] (Fin (dimAt 2 1) → ℚ)) a - _ - 0 = 0
  exact lin_sub_sub_zero _ rfl a _ (map_zero _)

theorem exSideS_str : finrank ℚ ((selCx exSideS.Dstr).toCC.homology 1) = 1 := by
  have h0 : Subsingleton (exSideS.Dstr.G.X 0 × exSideS.Dstr.U.X 0 × exSideS.Dstr.L.X (0 - 1)) := by
    have := subsingleton_dimAt 1 (n := 0) (by norm_num)
    have := subsingleton_dimAt 2 (n := 0 - 1) (by norm_num)
    change Subsingleton ((Fin (dimAt 1 0) → ℚ) × (Fin 0 → ℚ) × (Fin (dimAt 2 (0 - 1)) → ℚ))
    infer_instance
  rw [finrank_h1_of_d_zero _ (selCx_d01_zero _ h0) exSideS_str_d12]
  haveI : FiniteDimensional ℚ (exSideS.Dstr.G.X 1) :=
    (inferInstance : FiniteDimensional ℚ (Fin (dimAt 1 1) → ℚ))
  haveI : FiniteDimensional ℚ (exSideS.Dstr.U.X 1) :=
    (inferInstance : FiniteDimensional ℚ (Fin 0 → ℚ))
  haveI : FiniteDimensional ℚ (exSideS.Dstr.L.X (1 - 1)) :=
    (inferInstance : FiniteDimensional ℚ (Fin (dimAt 2 (1 - 1)) → ℚ))
  rw [finrank_selX1]
  change finrank ℚ (Fin (dimAt 1 1) → ℚ) + (finrank ℚ (Fin 0 → ℚ) +
    finrank ℚ (Fin (dimAt 2 (1 - 1)) → ℚ)) = 1
  simp only [Module.finrank_fin_fun]
  simp [dimAt]

/-- **`U = F`** for the example. -/
theorem exRel_U : exRel.U = finPlane ℚ (Fin 2 → ℚ) (Fin 2 → ℚ) := by
  haveI : FiniteDimensional ℚ (exRel.D.G.X 1) :=
    (inferInstance : FiniteDimensional ℚ (Fin (dimAt 1 1) → ℚ))
  haveI : FiniteDimensional ℚ (exRel.D.L.X 0) :=
    (inferInstance : FiniteDimensional ℚ (Fin (dimAt 2 0) → ℚ))
  haveI : FiniteDimensional ℚ (exSideF.U₁.X 1) :=
    (inferInstance : FiniteDimensional ℚ (Fin (dimAt 2 1) → ℚ))
  haveI : FiniteDimensional ℚ (exSideS.U₁.X 1) :=
    (inferInstance : FiniteDimensional ℚ (Fin (dimAt 2 1) → ℚ))
  have h := (switchDims_of_selmerData exRel exSideF exSideS).1
  rw [exSideF_h1, exSideF_str] at h
  have h2 : finrank ℚ ↥(exRel.U ⊓ finPlane ℚ (Fin 2 → ℚ) (Fin 2 → ℚ)) =
      finrank ℚ ↥(finPlane ℚ (Fin 2 → ℚ) (Fin 2 → ℚ)) := by
    rw [finrank_finPlane_two]; omega
  have hF : exRel.U ⊓ finPlane ℚ (Fin 2 → ℚ) (Fin 2 → ℚ) = finPlane ℚ (Fin 2 → ℚ) (Fin 2 → ℚ) :=
    Submodule.eq_of_le_of_finrank_eq inf_le_right h2
  exact le_antisymm exRel_U_le (hF ▸ inf_le_left)

theorem exSideS_h1 : finrank ℚ ((selCx exSideS.Dside).toCC.homology 1) = 1 := by
  haveI : FiniteDimensional ℚ (exRel.D.G.X 1) :=
    (inferInstance : FiniteDimensional ℚ (Fin (dimAt 1 1) → ℚ))
  haveI : FiniteDimensional ℚ (exRel.D.L.X 0) :=
    (inferInstance : FiniteDimensional ℚ (Fin (dimAt 2 0) → ℚ))
  haveI : FiniteDimensional ℚ (exSideF.U₁.X 1) :=
    (inferInstance : FiniteDimensional ℚ (Fin (dimAt 2 1) → ℚ))
  haveI : FiniteDimensional ℚ (exSideS.U₁.X 1) :=
    (inferInstance : FiniteDimensional ℚ (Fin (dimAt 2 1) → ℚ))
  have h := (switchDims_of_selmerData exRel exSideF exSideS).2
  rw [exSideS_str, exRel_U, finPlane_inf_singPlane, finrank_bot] at h
  exact h

/-- **`SelmerNonquadStep` is inhabited** by the example (duality: `U = F` is Lagrangian; detection:
`F ≤ U`). -/
def exSelmerNonquadStep : SelmerNonquadStep ℚ where
  R := exRel
  SF := exSideF
  SS := exSideS
  fG := (inferInstance : FiniteDimensional ℚ (Fin (dimAt 1 1) → ℚ))
  fL := (inferInstance : FiniteDimensional ℚ (Fin (dimAt 2 0) → ℚ))
  fF := (inferInstance : FiniteDimensional ℚ (Fin (dimAt 2 1) → ℚ))
  fS := (inferInstance : FiniteDimensional ℚ (Fin (dimAt 2 1) → ℚ))
  hk0 := by rw [exSideF_str, exSideS_str]
  ε := 1
  σ := 1
  J := J₀
  hε := one_ne_zero
  hσ := one_ne_zero
  hJ2 := J₀_sq
  hdual := by
    unfold LocalizationDualityInput
    rw [exRel_U]
    exact exLocalizationDuality 1 1 one_ne_zero one_ne_zero J₀ J₀_sq
  hdet := exRel_U.ge

/-- **`SelmerSwitchData` with a genuine switch**: the stages of fiber dimensions three and one of
`exHeightOneSwitchData`, whose switch is given at the Selmer level by `exSelmerNonquadStep` with
`dim H¹(C(U_F)) = 3`, `dim H¹(C(U_S)) = 1`. -/
noncomputable def exSelmerSwitchData : SelmerSwitchData (k := ℚ) (RingHom.id ℚ) (RingHom.id ℚ) where
  Stage := Bool
  stage := exHeightOneSwitchData.stage
  quadratic := False
  sp _ := 0
  sm _ := 0
  sign_sum h := h.elim
  primitive := exHeightOneSwitchData.primitive
  switch_mixed b _ hs := by
    cases b
    · exfalso
      have h1 := exStage1_fiberDim (exSwitchCoordData 1 1).uS
      change 1 < (exStage1 _).fiberDim (RingHom.id ℚ) at hs
      omega
    · refine ⟨false, ⟨exCoordStep⟩, fun h => h.elim, fun _ => ⟨exSelmerNonquadStep, ?_, ?_⟩⟩
      · change (exStage3 _).fiberDim (RingHom.id ℚ) = _
        rw [exStage3_fiberDim]; exact exSideF_h1.symm
      · change (exStage1 _).fiberDim (RingHom.id ℚ) = _
        rw [exStage1_fiberDim]; exact exSideS_h1.symm
  switch_single _ h := h.elim

theorem exSelmerSwitch_regular (b : Bool) :
    ∃ a : ℚ, RingHom.id ℚ a = (exSelmerSwitchData.stage b).u :=
  regular_of_selmerSwitchData (fun _ _ h => h) (fun x hx => by
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, isUnit_iff_ne_zero, not_not] at hx
    simp [hx]) exSelmerSwitchData b

/-- `H¹ ≅ K¹` when both differentials at degree one vanish. -/
noncomputable def h1IsoOfZero (K : CochainComplex (ModuleCat.{0} ℚ) ℤ) (h01 : K.d 0 1 = 0)
    (h12 : K.d 1 2 = 0) : K.homology 1 ≅ K.X 1 :=
  (K.isoHomologyπ 0 1 (by simp) h01).symm ≪≫ K.iCyclesIso 1 2 (by simp) h12

theorem exStr_h0 : Subsingleton ((Fin (dimAt 1 0) → ℚ) × (Fin 0 → ℚ) × (Fin (dimAt 2 (0 - 1)) → ℚ)) := by
  have := subsingleton_dimAt 1 (n := 0) (by norm_num)
  have := subsingleton_dimAt 2 (n := 0 - 1) (by norm_num)
  infer_instance

theorem exRel_lam_snd (v : (selCx exRel.D).toCC.homology 1) : (exRel.lam v).2 = 0 := by
  have h : exRel.lam v ∈ exRel.U := by rw [← RelaxedLocalization.range_lam]; exact ⟨v, rfl⟩
  rw [exRel_U, mem_finPlane] at h
  exact h

theorem exSideS_βS_zero (v : (selCx exSideS.Dside).toCC.homology 1) : exSideS.βS v = 0 := by
  have h := LinearMap.congr_fun exSideS.lam_gamma_S v
  change exRel.lam (H1 (changeMap exRel.D exSideS.f₁) v) = inrS (exSideS.βS v) at h
  have h2 := congrArg Prod.snd h
  rw [exRel_lam_snd] at h2
  exact h2.symm

/-- **`SelmerQuadSwitch` is inhabited** by the example with `J = id` and all involutions the identity
(the singular localization vanishes and the relaxed image is `F`, so the sign conditions hold). This
checks that its fields do not contradict each other; it is not a genuine quadratic example (`J = id`
has no `−1` eigenvector, so it cannot feed `SelmerQuadMixedStep`). -/
noncomputable def exSelmerQuadSwitch : SelmerQuadSwitch ℚ LinearMap.id where
  R := exRel
  SF := exSideF
  SS := exSideS
  fG := (inferInstance : FiniteDimensional ℚ (Fin (dimAt 1 1) → ℚ))
  fL := (inferInstance : FiniteDimensional ℚ (Fin (dimAt 2 0) → ℚ))
  fF := (inferInstance : FiniteDimensional ℚ (Fin (dimAt 2 1) → ℚ))
  fS := (inferInstance : FiniteDimensional ℚ (Fin (dimAt 2 1) → ℚ))
  eK := (h1IsoOfZero _ (selCx_d01_zero _ exStr_h0) exSideS_str_d12).toLinearEquiv.trans
    (h1IsoOfZero _ (selCx_d01_zero _ exStr_h0) exSideF_str_d12).toLinearEquiv.symm
  σK := LinearMap.id
  σV := LinearMap.id
  σV' := LinearMap.id
  σr := LinearMap.id
  hK := LinearMap.id_comp _
  hV := LinearMap.id_comp _
  hV' := LinearMap.id_comp _
  hr := LinearMap.id_comp _
  hα' := LinearMap.ext fun _ => rfl
  hβ' := LinearMap.ext fun _ => rfl
  hγ' := LinearMap.ext fun _ => rfl
  hα'' := LinearMap.ext fun _ => rfl
  hβ'' := by
    ext1 v
    simp only [LinearMap.comp_apply, LinearMap.id_apply, LinearMap.neg_apply, exSideS_βS_zero,
      neg_zero]
  hγ'' := LinearMap.ext fun _ => rfl
  hl := by
    ext1 v
    simp only [LinearMap.comp_apply, LinearMap.id_apply, localInv_apply, LinearMap.neg_apply]
    refine Prod.ext rfl ?_
    rw [exRel_lam_snd, neg_zero]

end SelmerExample

end ZInQ.Contrib.CloudB3RC53.SwitchInputs
