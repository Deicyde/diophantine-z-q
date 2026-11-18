import ZInQKernel.Contrib.CloudB3RC53.UniformSwitch.Regularity

/-!
# RC53 UniformSwitch: the outer switching process from inner and outer models and switch data

Proposition `ex:limits-uniform-lower-bound`, proof, tex L4927–4972. RC16 formalizes the outer
descent as `ZInQ.Manuscript.RC.Uniform.OuterSwitchProcess` (`RC/Uniform/OuterContradiction.lean`),
consumed by `uniform_lower_bound_of_switchProcess`. This file builds an instance from genuine data:

* each configuration carries its **outer model** `D_out` over a field `K_out` (in the text the
  fraction field of the outer DVR `𝒪_∞`) with the outer image `z_out` of the primitive inner cycles,
  and its **inner minimal models** `[K^{n+1} --D_j--> K^{n+1}]` with cycles `z_j`, closed functionals
  `λ_j` and complements, over the field `K` (`= Frac 𝒪`) with its valuation `v`;
* `outerDim` is **computed**: `dim ker D_out`;
* `coord` is the inner class-functional coordinate `classFunctionalCoordWith D_j z_j λ_j w_j y_j`
  (RC16's `Determinant.lean`).

Fields of `OuterSwitchProcess`:
* `pos` — **PROVED** from the nonzero outer kernel vector `z_out` (tex 4938–4940: "the inner kernels
  have primitive vectors whose outer image is nonzero, so the outer kernel dimension `s` is at least
  one").
* `terminal` — **PROVED** (via `terminalData_of_minimalModels_eventually`, the form of RC16's
  `terminalData_of_minimalModels` with the inner minors nonzero only on an outer-large set): at
  `s = 1` some maximal minor of `D_out` is nonzero (`exists_minor_ne_zero_of_finrank_ker_eq_one`);
  the GLUE link `minor_link` (a nonzero outer minor is the class of non-negligible, integral inner
  minors, nonzero on an outer-large set, tex 4706–4714, 4957–4959) gives the inner minors; integral
  cycles and `v λ ≥ −a` (the paired functional, exponent `a`) give the Schur/Cramer terminal data
  (tex 4957–4961).
* `switch` — **PROVED from GLUE inputs**: the outer dimension drop from `NonquadDims` over `K_out`
  (detection: relaxed image = finite plane; (5.5a)), and the equality of inner valuations on an
  outer-large set from RC16's `switch_equal_valuation` applied to per-instance switch data
  `SwitchCoordData` with unit volume normalizations (tex 4940–4950).

The stages are not yet tied to the genuine fibre models (see the caveat on `OuterSwitchData`).

Round 3 change (lane RC0, field shape): `minor_link` asks the inner minors to be nonzero on an
outer-large set (`∀ᶠ j in 𝒰`) instead of at every instance. This is Elliot's statement ("Its inner
minors have one finite valuation `b` on an outer-large set", tex 4958–4959), and it is what the
genuine outer model gives (batch 3's `SwitchInputs.minorLinkEventually_proof`): a sequence of minors
can vanish on a `𝒰`-small set without changing its class in `𝒪_∞`. RC16's process
`OuterSwitchProcess` is unchanged (its terminal field is already stated along `𝒰`).
-/

noncomputable section

namespace ZInQ.Contrib.CloudB3RC53.UniformSwitch

open Matrix Module Filter ZInQ.Manuscript.RC.Uniform

variable {K : Type*} [Field K] (v : AddValuation K (WithTop ℤ)) {J : Type*} (𝒰 : Ultrafilter J)
  {Kout : Type*} [Field Kout]

/-- A configuration of the outer process: the outer model with the outer image of the primitive
inner cycles, and the inner minimal models of one fixed size with cycles, closed functionals and
admissible complements (tex 4927–4940). -/
structure OuterStage (Kout : Type*) [Field Kout] (K : Type*) [Field K] (J : Type*) where
  m : ℕ
  Dout : Matrix (Fin (m + 1)) (Fin (m + 1)) Kout
  zout : Fin (m + 1) → Kout
  hzout : Dout *ᵥ zout = 0
  hzout0 : zout ≠ 0
  n : ℕ
  D : J → Matrix (Fin (n + 1)) (Fin (n + 1)) K
  z : J → Fin (n + 1) → K
  lam : J → Fin (n + 1) → K
  w : J → Fin n → Fin (n + 1) → K
  y : J → Fin (n + 1) → K
  hz : ∀ j, D j *ᵥ z j = 0
  hlam : ∀ j, lam j ᵥ* D j = 0
  hden : ∀ j, detCols (colsDWY (D j) (w j) (y j)) ≠ 0

/-- The outer kernel dimension `s = dim ker D_out`. -/
def OuterStage.outerDim (S : OuterStage Kout K J) : ℕ :=
  finrank Kout (LinearMap.ker S.Dout.mulVecLin)

/-- The inner class-functional coordinates `u_j`. -/
def OuterStage.coord (S : OuterStage Kout K J) (j : J) : K :=
  classFunctionalCoordWith (S.D j) (S.z j) (S.lam j) (S.w j) (S.y j)

/-- **`pos`**: the outer kernel dimension is at least one (tex 4938–4940). PROVED. -/
theorem OuterStage.one_le_outerDim (S : OuterStage Kout K J) : 1 ≤ S.outerDim := by
  rw [Nat.one_le_iff_ne_zero]
  intro h0
  have hmem : S.zout ∈ LinearMap.ker S.Dout.mulVecLin := by
    rw [LinearMap.mem_ker, mulVecLin_apply, S.hzout]
  rw [Submodule.finrank_eq_zero.mp h0, Submodule.mem_bot] at hmem
  exact S.hzout0 hmem

/-- **The terminal data from the minimal models, along the ultrafilter** (tex 4957–4961): RC16's
`terminalData_of_minimalModels` with the inner minors `Δ_j` nonzero only on an outer-large set
(Elliot: "Its inner minors have one finite valuation `b` on an outer-large set"). The Schur/Cramer
relation `u_j Δ_j = ±z_j(j₀) λ_j(k₀)` (RC16's `classFunctionalCoord_cramer`) is used at the
instances where `Δ_j ≠ 0`, which is all the terminal field of `OuterSwitchProcess` asks. PROVED. -/
theorem terminalData_of_minimalModels_eventually (a n : ℕ)
    (D : J → Matrix (Fin (n + 1)) (Fin (n + 1)) K) (z lam : J → Fin (n + 1) → K)
    (w : J → Fin n → Fin (n + 1) → K) (y : J → Fin (n + 1) → K) (k0 j0 : Fin (n + 1))
    (hz : ∀ j, D j *ᵥ z j = 0) (hlam : ∀ j, lam j ᵥ* D j = 0)
    (hden : ∀ j, detCols (colsDWY (D j) (w j) (y j)) ≠ 0)
    (hΔ0 : ∀ᶠ j in (𝒰 : Filter J), ((D j).submatrix k0.succAbove j0.succAbove).det ≠ 0)
    (hα : ∀ᶠ j in (𝒰 : Filter J), (0 : WithTop ℤ) ≤ v (z j j0))
    (hβ : ∀ᶠ j in (𝒰 : Filter J), (((-a : ℤ)) : WithTop ℤ) ≤ v (lam j k0))
    (hΔint : ∀ᶠ j in (𝒰 : Filter J),
      (0 : WithTop ℤ) ≤ v (((D j).submatrix k0.succAbove j0.succAbove).det))
    (hΔ : ¬ OuterNegligible v 𝒰 (fun j => ((D j).submatrix k0.succAbove j0.succAbove).det)) :
    ∃ (α β Δ s : J → K), (∀ j, s j = 1 ∨ s j = -1) ∧
      (∀ᶠ j in (𝒰 : Filter J),
        classFunctionalCoordWith (D j) (z j) (lam j) (w j) (y j) * Δ j = s j * (α j * β j)) ∧
      (∀ᶠ j in (𝒰 : Filter J), (0 : WithTop ℤ) ≤ v (α j)) ∧
      (∀ᶠ j in (𝒰 : Filter J), (((-a : ℤ)) : WithTop ℤ) ≤ v (β j)) ∧
      (∀ᶠ j in (𝒰 : Filter J), (0 : WithTop ℤ) ≤ v (Δ j)) ∧
      ¬ OuterNegligible v 𝒰 Δ := by
  refine ⟨fun j => z j j0, fun j => lam j k0,
    fun j => ((D j).submatrix k0.succAbove j0.succAbove).det,
    fun _ => (-1) ^ (n + (j0 : ℕ) + (k0 : ℕ)), fun _ => cramerSign_eq_or n j0 k0,
    hΔ0.mono fun j hj => ?_, hα, hβ, hΔint, hΔ⟩
  exact (classFunctionalCoord_cramer (D j) (z j) (lam j) (hz j) (hlam j) k0 j0 hj
    (w j) (y j) (hden j)).1

/-- **The outer switching data** (tex 4927–4964). GLUE fields, each with the hypotheses of RC16's
cores in its type:
* `minor_link` (tex 4706–4714, 4957–4959): a nonzero maximal minor of the outer model is the class
  in `𝒪_∞` of the inner minors at the same position, which are then nonzero on an outer-large set,
  integral and not negligible;
* `cycle_integral`, `functional_bound`: the inner cycles are integral and `v λ_j ≥ −a` (the
  paired-functional exponent `a`);
* `switch`: for `s > 1`, a next configuration whose outer dimension satisfies (5.5a) with the
  relaxed image the finite plane (`NonquadDims`), and per-instance switch data identifying the old and
  new inner coordinates with the finite and singular switch coordinates, with unit normalizations,
  on an outer-large set.

Caveat: the stages are not tied to the genuine fibre models; a one-stage datum of fibre dimension 1
(no switch demanded) satisfies the structure (`exampleOuterData`), so as a hypothesis it is
equivalent to its conclusion (compare RC's `regularityInputsS_iff`). Linking the stages to the
genuine fibre models is pending. -/
structure OuterSwitchData (a : ℕ) where
  Stage : Type
  stage : Stage → OuterStage Kout K J
  minor_link : ∀ S (k0 j0 : Fin ((stage S).m + 1)),
    ((stage S).Dout.submatrix k0.succAbove j0.succAbove).det ≠ 0 →
    ∃ (k1 j1 : Fin ((stage S).n + 1)),
      (∀ᶠ j in (𝒰 : Filter J), (((stage S).D j).submatrix k1.succAbove j1.succAbove).det ≠ 0) ∧
      (∀ᶠ j in (𝒰 : Filter J),
        (0 : WithTop ℤ) ≤ v ((((stage S).D j).submatrix k1.succAbove j1.succAbove).det)) ∧
      ¬ OuterNegligible v 𝒰 (fun j => (((stage S).D j).submatrix k1.succAbove j1.succAbove).det)
  cycle_integral : ∀ S j i, (0 : WithTop ℤ) ≤ v ((stage S).z j i)
  functional_bound : ∀ S j i, (((-a : ℤ)) : WithTop ℤ) ≤ v ((stage S).lam j i)
  switch : ∀ S, 1 < (stage S).outerDim → ∃ S',
    Nonempty (NonquadDims (k := Kout) (stage S).outerDim (stage S').outerDim) ∧
    ∀ᶠ j in (𝒰 : Filter J), ∃ X : SwitchCoordData K,
      v X.μF = 0 ∧ v X.μS = 0 ∧ (stage S).coord j = X.uF ∧ (stage S').coord j = X.uS

/-- **The instance of RC16's `OuterSwitchProcess`** built from the outer switching data
(tex 4927–4964). `pos` and `terminal` are proved from the models; `switch` from the GLUE inputs
through `NonquadDims.drop` and RC16's `switch_equal_valuation`. PROVED. -/
def OuterSwitchData.toProcess {a : ℕ} (P : OuterSwitchData (Kout := Kout) v 𝒰 a) :
    OuterSwitchProcess v 𝒰 a where
  Stage := P.Stage
  outerDim S := (P.stage S).outerDim
  coord S := (P.stage S).coord
  pos S := (P.stage S).one_le_outerDim
  switch S hs := by
    obtain ⟨S', ⟨N⟩, hX⟩ := P.switch S hs
    refine ⟨S', N.drop, ?_⟩
    filter_upwards [hX] with j ⟨X, hF, hS, h1, h2⟩
    rw [h1, h2]
    exact (switch_equal_valuation (Pi.basisFun K (Fin 2)) X.hσ X.hJ2 X.hJdet X.hfA X.hsA X.hfB
      X.hsB X.hω v hF hS X.hxw X.hyw).symm
  terminal S h1 := by
    obtain ⟨k0, j0, hk⟩ := exists_minor_ne_zero_of_finrank_ker_eq_one (P.stage S).Dout h1
    obtain ⟨k1, j1, hΔ0, hΔint, hΔ⟩ := P.minor_link S k0 j0 hk
    exact terminalData_of_minimalModels_eventually v 𝒰 a (P.stage S).n (P.stage S).D (P.stage S).z
      (P.stage S).lam (P.stage S).w (P.stage S).y k1 j1 (P.stage S).hz (P.stage S).hlam
      (P.stage S).hden hΔ0 (Eventually.of_forall fun j => P.cycle_integral S j j1)
      (Eventually.of_forall fun j => P.functional_bound S j k1) hΔint hΔ

/-- **(5.5) from outer switching data** (tex 4909–4964), through RC16's
`uniform_lower_bound_of_switchProcess`: if for every sequence of instances there is outer switching
data along the fixed nonprincipal ultrafilter whose starting configuration has the primitive
coordinates' valuations, then `v u_prim ≥ −C` uniformly. PROVED (from the GLUE inputs). -/
theorem uniform_lower_bound_of_switchData {Inst : Type*} (uprim : Inst → K)
    (inputs : ∀ inst : ℕ → Inst, ∃ (a : ℕ)
      (P : OuterSwitchData (Kout := Kout) (J := ℕ) v (Filter.hyperfilter ℕ) a) (S₀ : P.Stage),
      ∀ᶠ j in ((Filter.hyperfilter ℕ : Ultrafilter ℕ) : Filter ℕ),
        v ((P.stage S₀).coord j) = v (uprim (inst j))) :
    ∃ C : ℕ, ∀ i, (((-C : ℤ)) : WithTop ℤ) ≤ v (uprim i) :=
  uniform_lower_bound_of_switchProcess v uprim fun inst => by
    obtain ⟨a, P, S₀, h⟩ := inputs inst
    exact ⟨a, P.toProcess v _, S₀, h⟩

/-! ### Non-vacuity -/

theorem example_hden : detCols (colsDWY (0 : Matrix (Fin 1) (Fin 1) ℚ) Fin.elim0 (fun _ => 1)) ≠ 0 := by
  have : colsDWY (0 : Matrix (Fin 1) (Fin 1) ℚ) Fin.elim0 (fun _ => 1) = fun _ _ => 1 := by
    funext i r
    obtain rfl : i = Fin.last 0 := Fin.eq_of_val_eq (by omega)
    rw [colsDWY, Fin.snoc_last]
  rw [this]
  change Matrix.det (Matrix.of fun _ _ : Fin 1 => (1 : ℚ)) ≠ 0
  rw [Matrix.det_fin_one]; simp

theorem example_minor : ((0 : Matrix (Fin 1) (Fin 1) ℚ).submatrix (0 : Fin 1).succAbove
    (0 : Fin 1).succAbove).det = 1 := Matrix.det_isEmpty

/-- The single configuration of the example: outer model `[ℚ --0--> ℚ]`, inner models
`[ℚ --0--> ℚ]` with cycle, functional and complement `1`. -/
noncomputable def exampleOuterStage : OuterStage ℚ ℚ ℕ where
  m := 0
  Dout := 0
  zout := fun _ => 1
  hzout := by simp
  hzout0 := fun h => by simpa using congrFun h 0
  n := 0
  D := fun _ => 0
  z := fun _ _ => 1
  lam := fun _ _ => 1
  w := fun _ => Fin.elim0
  y := fun _ _ => 1
  hz := fun _ => by simp
  hlam := fun _ => by simp
  hden := fun _ => example_hden

theorem exampleOuterStage_outerDim : exampleOuterStage.outerDim = 1 := by
  have h0 : (exampleOuterStage.Dout).mulVecLin = 0 := by
    apply LinearMap.ext; intro v; ext i; simp [exampleOuterStage]; rfl
  rw [OuterStage.outerDim, h0, LinearMap.ker_zero, finrank_top, finrank_fin_fun]; rfl

/-- **Non-vacuity of `OuterSwitchData`** over `K = K_out = ℚ` with the 2-adic valuation: one
configuration of outer dimension one, minors `1`. PROVED. -/
noncomputable def exampleOuterData (𝒰 : Ultrafilter ℕ) : OuterSwitchData (K := ℚ) (Kout := ℚ)
    (J := ℕ) vTwo 𝒰 0 where
  Stage := Unit
  stage _ := exampleOuterStage
  minor_link _ k0 j0 _ := ⟨(0 : Fin 1), (0 : Fin 1),
    Eventually.of_forall fun _ h => one_ne_zero (example_minor.symm.trans h),
    Eventually.of_forall fun _ =>
      (le_of_eq (by rw [AddValuation.map_one] : (0 : WithTop ℤ) = vTwo 1)).trans_eq
        (congrArg vTwo example_minor).symm,
    fun h => by
      obtain ⟨j, hj⟩ := (h 1).exists
      have hj' : ((1 : ℤ) : WithTop ℤ) ≤ vTwo 1 := hj.trans_eq (congrArg vTwo example_minor)
      rw [AddValuation.map_one] at hj'
      have hj := hj'
      have : ((1 : ℤ) : WithTop ℤ) ≤ ((0 : ℤ) : WithTop ℤ) := by simpa using hj
      exact absurd (WithTop.coe_le_coe.mp this) (by norm_num)⟩
  cycle_integral _ _ _ := by simp [exampleOuterStage]
  functional_bound _ _ _ := by simp [exampleOuterStage]
  switch S hs := by
    exfalso
    have h1 : exampleOuterStage.outerDim = 1 := exampleOuterStage_outerDim
    exact absurd (h1 ▸ hs : 1 < 1) (lt_irrefl 1)

end ZInQ.Contrib.CloudB3RC53.UniformSwitch
