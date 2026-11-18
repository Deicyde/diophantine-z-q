import ZInQKernel.Contrib.CloudB3RC53.SwitchInputs.OuterIntegral

/-!
# RC53 SwitchInputs: the outer switching data tied to the actual instances

Proposition `ex:limits-uniform-lower-bound`, proof, tex L4927–4972 (the outer switching), with the
outer ring (5.3) of tex L4706–4714.

**Why this file.** The truth check of the switch area (review `GlueTruth`, Part B, item D2) found
`OuterSwitchData` / `OuterSwitchStep` conclusion-shaped: their stages are free, so a one-stage
datum (outer dimension one, inner functional chosen so that the coordinate is `uprim (inst j)`)
inhabits the hypothesis of `uniform_lower_bound_of_switchData` for every sequence, i.e. the
hypothesis is equivalent to the uniform bound itself. Here the stages are no longer data of the
hypothesis:

* `InstanceModel ϖ K n`: the minimal-model data of ONE instance — an integral two-term model `M`
  over the DVR `R`, the actual class `zR` (an integral cycle, primitive: some coordinate is not
  divisible by `ϖ`), the actual paired functional `lamR` (integral and closed, exponent `a = 0`
  from `ex:arith-paired-functional`), and an admissible complement `(w, y)` for the coordinate.
  Its class-functional coordinate `coordOf` is COMPUTED (`classFunctionalCoordWith`), not chosen.
* `GenuineOuterModels`: a FIXED family of switched minimal models, `model i l` for every instance
  `i` and every list `l` of derivative-prime labels (the minimal model of the actual Selmer
  complex of `i` after the switches `l`), of size `nOf l`; `model i []` is the actual minimal model
  of `i`. This is a parameter of everything below — the genuine Selmer construction of the
  configurations (tex L4940–4950: "one new derivative prime gives a rank-two localization"), not a
  field that a proof could fill in at will.
* `configStage`: the outer stage of a sequence of instances at the configuration `l`. Its inner
  models are `model (inst j) l`, its outer model is RC6's genuine outer matrix in `Frac 𝒪_∞`, and
  its outer kernel vector is the outer image of the actual classes. That this vector is nonzero is
  PROVED from primitivity (tex L4938–4940: "the inner kernels have primitive vectors whose outer
  image is nonzero").
* `GenuineOuterSwitchData G inst`: the only remaining input is, for each configuration `l` of outer
  dimension `> 1`, a CHOICE OF PRIME `p` together with the switch GLUE `OuterSwitchStep` between the
  DETERMINED stages `l` and `l ++ [p]`. These are Elliot's switch lemma (dimension drop, unit
  relation of the coordinates; tex L4940–4950) for the actual configurations. They can no longer
  be satisfied by inventing stages.

Results:
* `GenuineOuterSwitchData.toOuterSwitchData`: the old `OuterSwitchData`, with stages `configStage`
  (`minor_link`, `cycle_integral`, `functional_bound` PROVED, as in `ofIntegralModels`).
* `coord_start`: the coordinate of the starting stage at `j` is the actual coordinate
  `coordOf (model (inst j) [])`, by computation.
* `outer_collapse_forces`: a datum that needs no switch at the start (outer dimension one) forces
  the outer kernel of the ACTUAL minimal models to have dimension one, a condition on the instances
  and not a free choice; `start_outerDim` identifies the starting outer dimension with that kernel.
* `uniform_lower_bound_of_genuine` (5.5): the uniform lower bound for the actual coordinates, from
  `GenuineOuterSwitchData` for every sequence of instances.
* Non-vacuity (LESSON 2): `exGenuineModels` over `ℤ₂ ⊂ ℚ₂` (constant instances `[ℤ₂ --0--> ℤ₂]`
  with class and functional `1`) and `exGenuineOuterSwitchData`, whose starting outer dimension is
  FORCED to be one (`exGenuine_start_outerDim`). As recorded in `OuterIntegral.lean`, with genuine
  integral models an outer dimension `> 1` makes `v u_j → −∞`, so switch-exercising genuine data
  exist only inside Elliot's proof by contradiction (tex L4935).

DEPARTURE (form only): the switched models of one configuration are taken to have a common size
`nOf l` (the sizes are bounded by (5.1), so they are constant on an outer-large set, tex
L4936–4937 "fixing the bounded `n` on an outer-large set"), and the derivative primes of a switch
are recorded by a label `p : P` common to the instances of the sequence.
-/

noncomputable section

namespace ZInQ.Contrib.CloudB3RC53.SwitchInputs

open Module Matrix Filter ZInQ.Manuscript.RC.Limits ZInQ.Manuscript.RC.Uniform
  ZInQ.Contrib.CloudB3RC53.UniformSwitch

section Genuine

variable {R : Type} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] {ϖ : R}
  [Fact (Irreducible ϖ)] {K : Type} [Field K] [Algebra R K]

set_option linter.unusedSectionVars false

variable (ϖ K) in
/-- **The minimal-model data of one instance** (tex L4927–4940, L4957–4961): an integral two-term
model `M` over `R`, the actual class `zR` (an integral cycle, primitive), the actual paired
functional `lamR` (integral and closed, `ex:arith-paired-functional` with `a = 0`), and an
admissible complement `(w, y)`. -/
structure InstanceModel (n : ℕ) where
  M : Matrix (Fin (n + 1)) (Fin (n + 1)) R
  zR : Fin (n + 1) → R
  lamR : Fin (n + 1) → R
  hz : M *ᵥ zR = 0
  hlam : lamR ᵥ* M = 0
  w : Fin n → Fin (n + 1) → K
  y : Fin (n + 1) → K
  hden : detCols (colsDWY (M.map (algebraMap R K)) w y) ≠ 0
  hprim : ∃ i, ¬ ϖ ∣ zR i

/-- The class-functional coordinate of an instance, computed from its actual data (RC16
`classFunctionalCoordWith`). -/
def InstanceModel.coordOf {n : ℕ} (X : InstanceModel ϖ K n) : K :=
  classFunctionalCoordWith (X.M.map (algebraMap R K)) (fun i => algebraMap R K (X.zR i))
    (fun i => algebraMap R K (X.lamR i)) X.w X.y

variable (ϖ K) in
/-- **The genuine switched minimal models** (tex L4940–4950): for every instance `i : Inst` and
every list `l` of derivative-prime labels, the minimal model of the actual Selmer complex of `i`
after the switches `l`, of size `nOf l`. A fixed family: `model i []` is the actual minimal model
of `i`. -/
structure GenuineOuterModels (Inst P : Type) where
  nOf : List P → ℕ
  model : Inst → (l : List P) → InstanceModel ϖ K (nOf l)

theorem InstanceModel.map_mulVec {n : ℕ} (X : InstanceModel ϖ K n) :
    X.M.map (algebraMap R K) *ᵥ (fun i => algebraMap R K (X.zR i)) = 0 := by
  ext a
  have h := congrFun X.hz a
  simp only [Matrix.mulVec, dotProduct, Matrix.map_apply, Pi.zero_apply] at h ⊢
  rw [← map_zero (algebraMap R K), ← h, map_sum]
  exact Finset.sum_congr rfl fun b _ => (map_mul _ _ _).symm

theorem InstanceModel.map_vecMul {n : ℕ} (X : InstanceModel ϖ K n) :
    (fun i => algebraMap R K (X.lamR i)) ᵥ* X.M.map (algebraMap R K) = 0 := by
  ext a
  have h := congrFun X.hlam a
  simp only [Matrix.vecMul, dotProduct, Matrix.map_apply, Pi.zero_apply] at h ⊢
  rw [← map_zero (algebraMap R K), ← h, map_sum]
  exact Finset.sum_congr rfl fun b _ => (map_mul _ _ _).symm

variable {J : Type} (𝒰 : Ultrafilter J)

/-- The outer image of the actual classes of a sequence of instance models (tex L4938–4940). -/
def outerClass {n : ℕ} (X : J → InstanceModel ϖ K n) : Fin (n + 1) → FractionRing (OInf 𝒰 ϖ) :=
  fun a => algebraMap (OInf 𝒰 ϖ) (FractionRing (OInf 𝒰 ϖ)) (outerVec 𝒰 ϖ (fun j => (X j).zR) a)

set_option synthInstance.maxHeartbeats 400000 in
theorem outerClass_mem_ker {n : ℕ} (X : J → InstanceModel ϖ K n) :
    (outerMatrix 𝒰 ϖ (fun j => (X j).M)).map (algebraMap (OInf 𝒰 ϖ) (FractionRing (OInf 𝒰 ϖ)))
      *ᵥ outerClass 𝒰 X = 0 := by
  have h0 : outerMatrix 𝒰 ϖ (fun j => (X j).M) *ᵥ outerVec 𝒰 ϖ (fun j => (X j).zR) = 0 := by
    rw [outerMatrix_mulVec]
    have : (fun j => (X j).M *ᵥ (X j).zR) = fun _ => 0 := funext fun j => (X j).hz
    rw [this, outerVec_eq_zero_iff]
    intro a
    exact mem_infinitesimals_of_eventually_eq_zero 𝒰 ϖ (Eventually.of_forall fun _ => rfl)
  ext a
  have h := congrFun h0 a
  simp only [Matrix.mulVec, dotProduct, Matrix.map_apply, Pi.zero_apply, outerClass] at h ⊢
  rw [← (algebraMap (OInf 𝒰 ϖ) (FractionRing (OInf 𝒰 ϖ))).map_zero, ← h, map_sum]
  exact Finset.sum_congr rfl fun b _ => (map_mul _ _ _).symm

/-- **The outer class is nonzero** (tex L4938–4940: "the inner kernels have primitive vectors whose
outer image is nonzero"): primitivity of the actual classes makes some coordinate sequence not
infinitesimal. PROVED. -/
theorem outerClass_ne_zero {n : ℕ} (X : J → InstanceModel ϖ K n) : outerClass 𝒰 X ≠ 0 := by
  choose idx hidx using fun j => (X j).hprim
  -- one coordinate is primitive on an outer-large set
  have hcover : (⋃ i ∈ (Set.univ : Set (Fin (n + 1))), {j | idx j = i}) ∈ 𝒰 := by
    apply Filter.univ_mem'
    intro j
    simp
  obtain ⟨i, -, hi⟩ := (Ultrafilter.finite_biUnion_mem_iff Set.finite_univ).mp hcover
  intro h
  have hzero := congrFun h i
  simp only [outerClass, Pi.zero_apply] at hzero
  have hinj := IsFractionRing.injective (OInf 𝒰 ϖ) (FractionRing (OInf 𝒰 ϖ))
  rw [← map_zero (algebraMap (OInf 𝒰 ϖ) (FractionRing (OInf 𝒰 ϖ))), hinj.eq_iff] at hzero
  have hmem : (fun j => (X j).zR i) ∈ infinitesimals 𝒰 ϖ := by
    have := (outerVec_eq_zero_iff 𝒰 ϖ (fun j => (X j).zR)).mp
    simp only [outerVec, toOInf_eq_zero_iff] at hzero
    exact hzero
  have h1 := (mem_infinitesimals.mp hmem) 1
  have hbad : ∀ᶠ j in (𝒰 : Filter J), False := by
    filter_upwards [h1, (show {j | idx j = i} ∈ 𝒰 from hi)] with j hj hji
    have := hidx j
    rw [show idx j = i from hji] at this
    exact this (by simpa using hj)
  exact (Filter.eventually_false_iff_eq_bot.mp hbad) |> fun hb => (Ultrafilter.neBot 𝒰).ne hb

/-- **The outer stage of a sequence of instances** (tex L4927–4961): inner models, classes,
functionals and complements are those of the instance models; the outer model is RC6's genuine outer
matrix, and the outer kernel vector is the outer image of the actual classes. Determined by the
sequence. -/
def configStage {n : ℕ} (X : J → InstanceModel ϖ K n) : IntegralModelStage 𝒰 ϖ K where
  base :=
    { n := n
      M := fun j => (X j).M
      zout := outerClass 𝒰 X
      hzout := outerClass_mem_ker 𝒰 X
      hzout0 := outerClass_ne_zero 𝒰 X
      z := fun j i => algebraMap R K ((X j).zR i)
      lam := fun j i => algebraMap R K ((X j).lamR i)
      w := fun j => (X j).w
      y := fun j => (X j).y
      hz := fun j => (X j).map_mulVec
      hlam := fun j => (X j).map_vecMul
      hden := fun j => (X j).hden }
  zR := fun j => (X j).zR
  lamR := fun j => (X j).lamR
  hzR := fun _ _ => rfl
  hlamR := fun _ _ => rfl

/-- The stage of the configuration `l` along a sequence of instances. -/
def GenuineOuterModels.stage {Inst P : Type} (G : GenuineOuterModels ϖ K Inst P) (inst : J → Inst)
    (l : List P) : IntegralModelStage 𝒰 ϖ K :=
  configStage 𝒰 (fun j => G.model (inst j) l)

variable (v : AddValuation K (WithTop ℤ))

/-- **The outer switching data of the actual instances** (tex L4927–4964). For a fixed family `G`
of genuine switched minimal models and a sequence `inst` of instances, the only input is: at every
configuration `l` of outer dimension `> 1`, a derivative-prime label `p` and the switch GLUE
`OuterSwitchStep` between the DETERMINED stages `l` and `l ++ [p]` (Elliot's switch lemma for the
actual configurations: the outer dimension drops by two, the inner coordinates are related by
units; tex L4940–4950; the coordinate part can be supplied by `outerCoords_of_switch` /
`StageLink`, the dimension part by `SelmerNonquadStep`). -/
structure GenuineOuterSwitchData {Inst P : Type} (G : GenuineOuterModels ϖ K Inst P)
    (inst : J → Inst) : Prop where
  step : ∀ l : List P, 1 < (G.stage 𝒰 inst l).base.toOuterStage.outerDim →
    ∃ p : P, Nonempty (OuterSwitchStep (G.stage 𝒰 inst l).base.toOuterStage
      (G.stage 𝒰 inst (l ++ [p])).base.toOuterStage)

variable {𝒰 v}

/-- **The old `OuterSwitchData` from the genuine one** (stages `List P`, stage `l` the determined
`configStage`; `minor_link`, `cycle_integral`, `functional_bound` PROVED by `ofIntegralModels`).
PROVED. -/
def GenuineOuterSwitchData.toOuterSwitchData {Inst P : Type} {G : GenuineOuterModels ϖ K Inst P}
    {inst : J → Inst} (H : GenuineOuterSwitchData 𝒰 G inst)
    (hinj : Function.Injective (algebraMap R K)) (hv : IsPiAdicOn ϖ v) (a : ℕ) :
    OuterSwitchData (Kout := FractionRing (OInf 𝒰 ϖ)) v 𝒰 a :=
  OuterSwitchData.ofIntegralModels v hinj hv a (List P) (fun l => G.stage 𝒰 inst l)
    (fun l hl => by
      obtain ⟨p, hp⟩ := H.step l hl
      exact ⟨l ++ [p], hp⟩)

/-- **The starting coordinate is the actual coordinate** (tex L4935–4940): at the starting
configuration `[]`, the inner coordinate at `j` is the computed coordinate of the actual minimal
model of `inst j`. PROVED (by computation). -/
theorem GenuineOuterSwitchData.coord_start {Inst P : Type} {G : GenuineOuterModels ϖ K Inst P}
    {inst : J → Inst} (H : GenuineOuterSwitchData 𝒰 G inst)
    (hinj : Function.Injective (algebraMap R K)) (hv : IsPiAdicOn ϖ v) (a : ℕ) (j : J) :
    ((H.toOuterSwitchData hinj hv a).stage []).coord j = (G.model (inst j) []).coordOf :=
  rfl

/-- **The starting outer dimension is that of the actual minimal models**: the outer dimension of
the starting stage is the dimension of the kernel of the genuine outer matrix of the actual minimal
models `model (inst j) []` (RC6 `outerMatrix`, in `Frac 𝒪_∞`). PROVED (by computation). -/
theorem GenuineOuterSwitchData.start_outerDim {Inst P : Type} {G : GenuineOuterModels ϖ K Inst P}
    {inst : J → Inst} (H : GenuineOuterSwitchData 𝒰 G inst)
    (hinj : Function.Injective (algebraMap R K)) (hv : IsPiAdicOn ϖ v) (a : ℕ) :
    ((H.toOuterSwitchData hinj hv a).stage []).outerDim =
      finrank (FractionRing (OInf 𝒰 ϖ)) (LinearMap.ker
        ((outerMatrix 𝒰 ϖ (fun j => (G.model (inst j) []).M)).map
          (algebraMap (OInf 𝒰 ϖ) (FractionRing (OInf 𝒰 ϖ)))).mulVecLin) :=
  rfl

/-- **The one-stage collapse is no longer available** (review `GlueTruth` D2): if the genuine data
need no switch at the start (outer dimension one), then the outer kernel of the ACTUAL minimal models
of the instances has dimension one — a condition on the instances, not a free choice of stage.
PROVED. -/
theorem GenuineOuterSwitchData.outer_collapse_forces {Inst P : Type}
    {G : GenuineOuterModels ϖ K Inst P} {inst : J → Inst} (H : GenuineOuterSwitchData 𝒰 G inst)
    (hinj : Function.Injective (algebraMap R K)) (hv : IsPiAdicOn ϖ v) (a : ℕ)
    (h1 : ((H.toOuterSwitchData hinj hv a).stage []).outerDim = 1) :
    finrank (FractionRing (OInf 𝒰 ϖ)) (LinearMap.ker
        ((outerMatrix 𝒰 ϖ (fun j => (G.model (inst j) []).M)).map
          (algebraMap (OInf 𝒰 ϖ) (FractionRing (OInf 𝒰 ϖ)))).mulVecLin) = 1 := by
  rw [← H.start_outerDim hinj hv a]; exact h1

/-- **The uniform lower bound (5.5) from the genuine outer switching data** (tex L4909–4972). Let
`G` be the family of genuine switched minimal models of the instances `Inst` (over the DVR `R`, with
`v` the `ϖ`-adic valuation on `K`). If for every sequence of instances the genuine outer switching
data exist along the fixed nonprincipal ultrafilter, then the actual coordinates
`coordOf (model i [])` are bounded below uniformly. Classification: PROVED (from the inputs; the
inputs are Elliot's switch lemma for the determined configurations). -/
theorem uniform_lower_bound_of_genuine {Inst P : Type} (G : GenuineOuterModels ϖ K Inst P)
    (hinj : Function.Injective (algebraMap R K)) (hv : IsPiAdicOn ϖ v)
    (inputs : ∀ inst : ℕ → Inst, GenuineOuterSwitchData (Filter.hyperfilter ℕ) G inst) :
    ∃ C : ℕ, ∀ i, (((-C : ℤ)) : WithTop ℤ) ≤ v (G.model i []).coordOf :=
  uniform_lower_bound_of_switchData v (fun i => (G.model i []).coordOf) fun inst =>
    ⟨0, (inputs inst).toOuterSwitchData hinj hv 0, [], Eventually.of_forall fun _ => rfl⟩

end Genuine

/-! ### Non-vacuity (LESSON 2) -/

section Examples

/-- The constant instance model `[ℤ₂ --0--> ℤ₂]` with actual class and functional `1` (primitive),
over `K = ℚ₂`. -/
noncomputable def exInstanceModel : InstanceModel (2 : ℤ_[2]) ℚ_[2] 0 where
  M := 0
  zR := fun _ => 1
  lamR := fun _ => 1
  hz := by simp
  hlam := by simp
  w := Fin.elim0
  y := fun _ => 1
  hden := (exModelStage (Filter.hyperfilter ℕ)).hden 0
  hprim := ⟨0, fun h => by
    have := PadicInt.norm_le_one (1 : ℤ_[2])
    obtain ⟨c, hc⟩ := h
    have h2 : ‖(2 : ℤ_[2])‖ < 1 := by
      rw [PadicInt.norm_lt_one_iff_dvd]; exact ⟨1, by norm_num⟩
    have h3 : ‖(1 : ℤ_[2])‖ = ‖(2 : ℤ_[2])‖ * ‖c‖ := by rw [hc, norm_mul]
    rw [norm_one] at h3
    have := PadicInt.norm_le_one c
    nlinarith [norm_nonneg (2 : ℤ_[2]), norm_nonneg c]⟩

/-- The genuine family of constant models (every configuration is `exInstanceModel`). -/
noncomputable def exGenuineModels : GenuineOuterModels (2 : ℤ_[2]) ℚ_[2] Unit Unit where
  nOf := fun _ => 0
  model := fun _ _ => exInstanceModel

/-- **The starting outer dimension of the constant instances is forced to be one**: the genuine
outer matrix of the actual models is `0` of size `1`, whose kernel is the whole line. -/
theorem exGenuine_start_outerDim (𝒰 : Ultrafilter ℕ) (inst : ℕ → Unit) :
    (exGenuineModels.stage 𝒰 inst []).base.toOuterStage.outerDim = 1 := by
  have h0 : (exGenuineModels.stage 𝒰 inst []).base.toOuterStage.Dout = 0 := by
    ext a b
    simp only [GenuineOuterModels.stage, configStage, ModelStage.toOuterStage, exGenuineModels,
      exInstanceModel, outerMatrix, Matrix.map_apply, Matrix.zero_apply]
    exact (algebraMap (OInf 𝒰 (2 : ℤ_[2])) (FractionRing (OInf 𝒰 (2 : ℤ_[2])))).map_zero
  unfold OuterStage.outerDim
  rw [h0, Matrix.mulVecLin_zero, LinearMap.ker_zero, finrank_top, Module.finrank_fin_fun]
  rfl

/-- **`GenuineOuterSwitchData` is inhabited** by the constant instances: the starting outer
dimension is forced to be one, so no switch is required (and none can be invented). -/
theorem exGenuineOuterSwitchData (𝒰 : Ultrafilter ℕ) (inst : ℕ → Unit) :
    GenuineOuterSwitchData 𝒰 exGenuineModels inst where
  step l hl := by
    have : (exGenuineModels.stage 𝒰 inst l).base.toOuterStage.outerDim = 1 := by
      have hl' : exGenuineModels.stage 𝒰 inst l = exGenuineModels.stage 𝒰 inst [] := rfl
      rw [hl']; exact exGenuine_start_outerDim 𝒰 inst
    omega

/-- **The uniform bound for the constant instances** from the genuine data (consistency check of
`uniform_lower_bound_of_genuine`). -/
theorem exGenuine_uniform_bound :
    ∃ C : ℕ, ∀ i, (((-C : ℤ)) : WithTop ℤ) ≤
      (Padic.addValuation (p := 2)) (exGenuineModels.model i []).coordOf :=
  uniform_lower_bound_of_genuine exGenuineModels Subtype.coe_injective isPiAdicOn_padic
    (fun inst => exGenuineOuterSwitchData _ inst)

end Examples

end ZInQ.Contrib.CloudB3RC53.SwitchInputs
