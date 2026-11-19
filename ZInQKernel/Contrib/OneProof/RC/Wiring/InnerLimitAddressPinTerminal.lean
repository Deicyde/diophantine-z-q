import ZInQKernel.Contrib.OneProof.RC.Wiring.InnerLimitAddressPin
import ZInQKernel.Contrib.OneProof.RC.Wiring.InnerLimitSwitchBridge

/-!
**Theorem 5.3, Lane RC0 round 17: the collapse of the pinned leaf is exactly the terminal case**

Proposition `ex:limits-uniform-lower-bound`, height-one regularity (tex 4976–5200). The switching
argument stops when the fibre dimension is one: "the terminal complex has one free generator in
each of degrees one and two; its differential is zero" (tex 5154–5164).
`InnerLimitSwitchPinned.terminal_of_stationary` shows that a stationary configuration family with
the faithful pin forces `dim H¹ = 1` of the finite fibre of the retained limit. This file proves
the converse, so that the collapse is exactly the terminal case at a nonquadratic prime.

* `homotopyEquiv_hom_inv_one` (PROVED): a homotopy equivalence onto a complex whose differentials
  around degree one vanish is a section in degree one.
* `MovingRetainedLimit.finiteFibreModel`, `finiteStage_residue_zero`, `fiberDim_finiteStage`
  (PROVED): the finite fibre of the retained limit is homotopy equivalent to the two-term fibre
  complex of the stage of an integral model `Dfin` of its finite side; that stage reduces to zero
  and its fibre dimension is `dim H¹` of the finite fibre.
* `NonquadraticAt`, `IsGenuineFamilyAt.not_quadratic_iff`, `not_nonquadraticAt_of_mem`,
  `two_ne_zero_of_not_nonquadraticAt`, `InnerLimitSwitchPinned.nonquadraticAt` (PROVED): for a
  genuine family (`t = X`) nonquadratic is a condition on `𝔭` alone (tex 5005–5008), it fails
  when `X ∈ 𝔭` or `X + 2 ∈ 𝔭`, pinned inputs over a genuine family force it, and at a quadratic
  height-one prime `2 ≠ 0` in `k(𝔭)`.
* `stageCollapseFamily`, `stageCollapseFrame`, `stageCollapseHomology`: the one-configuration
  family over a model of a residually zero stage, with the actual class and functional
  transported so that the frame's `hz0`, `hw0` hold exactly, its frame, and its homology-level
  data with signs (no switch is demanded at fibre dimension one).
* `terminalFamily` (with `terminalFamily_fibre`, `terminalFamily_not_quadratic_iff`,
  `terminalFamily_isGenuine`, `terminalFamily_next`), `terminalPinned` (with
  `terminalPinned_stage`), `terminalHomology`: from a genuine realization `G` of the finite fibre
  (`e`), an integral model `Dfin` with nonzero class and `dim H¹ = 1`, the pinned inputs with
  `stage := fun _ => Dfin.stage` (at a nonquadratic prime), resp. the quadratic-branch data.
* `regularityInputsILPAt_of_terminal` (PROVED): the faithful-pin clause `RegularityInputsILPAt`
  at a height-one prime from these terminal data (both branches).
* `collapse_iff_terminal`, `collapse_iff_terminal_of_nonquadratic` (PROVED): a genuine
  stationary family with the pin and nonquadratic pinned inputs at `Dfin.stage` exists if and only
  if `𝔭` is nonquadratic, `dim H¹ = 1` for the finite fibre, the finite fibre has a genuine
  realization and the class of `Dfin` is nonzero (and `u` is the coordinate of `Dfin`).

The nonquadratic hypothesis cannot be dropped from the pinned construction: the frame of
`InnerLimitSwitchPinned` asks `¬ Φ.quadratic`, and for a genuine family this is `t̄ (t̄ + 2) ≠ 0`
in `k(𝔭)`, false at `𝔭 = (X)` and `𝔭 = (X + 2)` (`InnerLimitSwitchPinned.nonquadraticAt`,
`not_nonquadraticAt_of_mem`); there the quadratic branch of the clause is used instead.
-/

noncomputable section

namespace ZInQ.Manuscript.RC.Wiring

open CategoryTheory NumberField IsDedekindDomain Matrix Module
open ZInQ.Manuscript ZInQ.Manuscript.RC ZInQ.Contrib.CloudB3RC53
open ZInQ.Contrib.CloudB3RC53.PairedFunctional ZInQ.Contrib.CloudB3RC53.UniformSwitch
open ZInQ.Contrib.CloudB3RC53.SwitchInputs
open ZInQ.Manuscript.RC.Uniform (Lambda)
open ZInQ.Manuscript.RC.Limits (stageIdeal_tendsToZero)
open ZInQ.Manuscript.RC.CoefModules (ActualConj)
open ZInQ.Manuscript.RC.LambdaCoef (HasFullTwoTorsion)
open ZInQ.Contrib.RC53Assist.InnerLimitMoving (IntegralMatrixStageData selmerStages
  derivativeDiagram retainedRestrictionStages canonicalMatrixModel)
open ZInQ.Contrib.RC53Assist.SwitchWiring (finite_side_data)
open scoped PowerSeries.WithPiTopology

/-! **Transport of the actual class** -/

section Transport

/-- **A homotopy equivalence onto a complex with zero differentials around degree one is a
section in degree one**: if `T.d 0 1 = 0` and `T.d 1 2 = 0`, then `e.hom ∘ e.inv` is the
identity of `T¹`, by the homotopy `e.inv ≫ e.hom ∼ 𝟙` (used for the two-term fibre of a
residually zero stage, tex 4986–4992). Kind: PROVED. -/
theorem homotopyEquiv_hom_inv_one {R : Type} [Ring R]
    {C T : CochainComplex (ModuleCat.{0} R) ℤ} (e : HomotopyEquiv C T) (h01 : T.d 0 1 = 0)
    (h12 : T.d 1 2 = 0) (x : T.X 1) : (e.hom.f 1).hom ((e.inv.f 1).hom x) = x := by
  have hh := e.homotopyInvHomId.comm 1
  rw [dNext_eq _ (show (ComplexShape.up ℤ).Rel 1 2 from rfl),
    prevD_eq _ (show (ComplexShape.up ℤ).Rel 0 1 from rfl), h12, h01,
    Limits.zero_comp, Limits.comp_zero, zero_add, zero_add] at hh
  have := congrArg (fun f => (ModuleCat.Hom.hom f) x) hh
  simpa using this

end Transport

/-! **The finite fibre and the stage of its integral model** -/

section FiniteModel

variable {P : Ideal Lambda} [P.IsPrime] {K : Type} [Field K] [NumberField K]
  {W : WeierstrassCurve K} {Fam : MovingStageFamily W}

/-- **The finite fibre is modelled by the stage of an integral model of the finite side** (tex
4385–4451, 4976–4996, 5040–5054): the literal finite side datum (`finite_side_data`) followed by
the chain-level side-to-stage equivalence `retainedFibreChainEquiv`. Kind: PROVED. -/
def MovingRetainedLimit.finiteFibreModel (L : MovingRetainedLimit Fam)
    (Dfin : IntegralMatrixStageData stageIdeal_tendsToZero L.hU
      (algebraMap Lambda (Localization.AtPrime P)) (UniformSwitch.toFracAt P)
      (selmerStages (derivativeDiagram L.C (retainedRestrictionStages L.D) .finite))) :
    HomotopyEquiv (L.finiteFibre P).toCC (twoTermFiberComplex (resAt P) Dfin.stage) :=
  (HomotopyEquiv.ofIso (eqToIso (congrArg (fun X : SelData (ResAt P) => (selCx X).toCC)
      (finite_side_data L.hU P L.C L.D)))).trans
    (retainedFibreChainEquiv L.hU P L.C L.D .finite Dfin)

/-- **The stage of the integral model reduces to zero**: `d ⊗ k = 0` (tex 4986–4987), by the
minimality of the computed model. Kind: PROVED. -/
theorem MovingRetainedLimit.finiteStage_residue_zero (L : MovingRetainedLimit Fam)
    (Dfin : IntegralMatrixStageData stageIdeal_tendsToZero L.hU
      (algebraMap Lambda (Localization.AtPrime P)) (UniformSwitch.toFracAt P)
      (selmerStages (derivativeDiagram L.C (retainedRestrictionStages L.D) .finite))) :
    Dfin.stage.D.map (resAt P) = 0 :=
  (canonicalMatrixModel stageIdeal_tendsToZero L.hU (algebraMap Lambda (Localization.AtPrime P))
    _ Dfin.shape).matrix_residue_zero

/-- **The fibre dimension of the stage of the integral model is `dim H¹` of the finite fibre**
(tex 4976–4996: `s = dim_k H¹(C ⊗ k)`). Kind: PROVED. -/
theorem MovingRetainedLimit.fiberDim_finiteStage (L : MovingRetainedLimit Fam)
    (Dfin : IntegralMatrixStageData stageIdeal_tendsToZero L.hU
      (algebraMap Lambda (Localization.AtPrime P)) (UniformSwitch.toFracAt P)
      (selmerStages (derivativeDiagram L.C (retainedRestrictionStages L.D) .finite))) :
    Dfin.stage.fiberDim (resAt P) = finrank (ResAt P) ((L.finiteFibre P).toCC.homology 1) := by
  rw [← finrank_h1_twoTermFiberComplex (resAt P) Dfin.stage]
  exact ((L.finiteFibreModel Dfin).toHomologyIso 1).toLinearEquiv.finrank_eq.symm

end FiniteModel

/-! **Nonquadratic specializations** -/

section Nonquadratic

variable {P : Ideal Lambda} [P.IsPrime]

variable (P) in
/-- **The specialization at `𝔭` is nonquadratic** for the genuine moving variable `t = X`:
`t̄ (t̄ + 2) ≠ 0` in `k(𝔭)` (tex 5005–5008: quadraticity forces `t (t + 2) = 0` in `k`, so the
only quadratic primes are `(t)` and `(t + 2)`). Kind: definition. -/
def NonquadraticAt : Prop :=
  ¬ resAt P (algebraMap Lambda (Localization.AtPrime P) PowerSeries.X) *
      (resAt P (algebraMap Lambda (Localization.AtPrime P) PowerSeries.X) + 2) = 0

/-- **For a genuine family, nonquadratic is a condition on `𝔭`** (tex 5005–5008): the moving
variable of a family genuine at `𝔭` is `t = X`. Kind: PROVED. -/
theorem IsGenuineFamilyAt.not_quadratic_iff
    {Φ : SwitchFamily (ResAt P) (Localization.AtPrime P)} (hΦ : IsGenuineFamilyAt P Φ) :
    ¬ Φ.quadratic (resAt P) ↔ NonquadraticAt P := by
  rw [NonquadraticAt, SwitchFamily.quadratic, hΦ.2]

/-- **At a quadratic height-one prime `2` is nonzero in `k(𝔭)`** (tex 4976–4980, 5005–5008): if
`t̄ (t̄ + 2) = 0` and `2 = 0` in `k(𝔭)`, then `𝔭` contains `X` and `2`, so it strictly contains the
prime `(X)` of height at least one, and `𝔭` has height at least two. Kind: PROVED. -/
theorem two_ne_zero_of_not_nonquadraticAt (hP : P.height = 1) (hq : ¬ NonquadraticAt P) :
    (2 : ResAt P) ≠ 0 := by
  have hq' := not_not.mp hq
  intro h2
  have hmem : ∀ a : Lambda, resAt P (algebraMap Lambda (Localization.AtPrime P) a) = 0 →
      a ∈ P := fun a ha => by
    rwa [IsLocalRing.residue_eq_zero_iff,
      IsLocalization.AtPrime.to_map_mem_maximal_iff (Localization.AtPrime P) P a] at ha
  have h2P : (2 : Lambda) ∈ P := hmem 2 (by simp only [map_ofNat]; exact h2)
  have hXP : (PowerSeries.X : Lambda) ∈ P := by
    have hprod := hmem (PowerSeries.X * (PowerSeries.X + 2))
      (by simp only [map_mul, map_add, map_ofNat]; exact hq')
    rcases (‹P.IsPrime›).mem_or_mem hprod with hX | hX2
    · exact hX
    · simpa using P.sub_mem hX2 h2P
  have hXne : (PowerSeries.X : Lambda) ≠ 0 := PowerSeries.X_ne_zero
  have : (Ideal.span {(PowerSeries.X : Lambda)}).IsPrime :=
    (Ideal.span_singleton_prime hXne).mpr PowerSeries.X_prime
  have hlt : Ideal.span {(PowerSeries.X : Lambda)} < P := by
    refine lt_of_le_of_ne ((Ideal.span_singleton_le_iff_mem P).mpr hXP) fun heq => ?_
    rw [← heq, Ideal.mem_span_singleton, PowerSeries.X_dvd_iff, map_ofNat] at h2P
    exact two_ne_zero h2P
  have h1 : 1 ≤ (Ideal.span {(PowerSeries.X : Lambda)}).height :=
    Ideal.one_le_height_span_singleton_of_mem_nonZeroDivisors
      (mem_nonZeroDivisors_of_ne_zero hXne)
  have h3 := Ideal.height_add_one_le_of_lt_of_isPrime hlt
  rw [hP] at h3
  have h4 : (1 : ℕ∞) + 1 ≤ 1 := le_trans (add_le_add h1 le_rfl) h3
  exact absurd h4 (by norm_num)

/-- **The two quadratic primes**: if `X ∈ 𝔭` or `X + 2 ∈ 𝔭` (`𝔭 = (t)` or `(t + 2)`, tex
5005–5008), the specialization at `𝔭` is quadratic. Kind: PROVED. -/
theorem not_nonquadraticAt_of_mem
    (hX : (PowerSeries.X : Lambda) ∈ P ∨ PowerSeries.X + 2 ∈ P) : ¬ NonquadraticAt P := by
  have hres : ∀ a : Lambda, a ∈ P →
      resAt P (algebraMap Lambda (Localization.AtPrime P) a) = 0 := fun a ha =>
    (IsLocalRing.residue_eq_zero_iff _).2
      ((IsLocalization.AtPrime.to_map_mem_maximal_iff (Localization.AtPrime P) P a).2 ha)
  intro hnq
  apply hnq
  rcases hX with hX | hX
  · rw [hres _ hX, zero_mul]
  · have h2 := hres _ hX
    simp only [map_add, map_ofNat] at h2
    rw [h2, mul_zero]

end Nonquadratic

/-! **Pinned inputs over a genuine family live at nonquadratic primes** -/

section PinnedNonquadratic

variable {P : Ideal Lambda} [P.IsPrime] {F : Type} [Field F] {K : Type} [Field K]
  [NumberField K] {S : Set (HeightOneSpectrum (𝓞 K))} {Cn : ActualConj K S}
  {W : WeierstrassCurve K} {hW : W.map (Cn.κ : K →+* K) = W} [W.IsElliptic]
  [HasFullTwoTorsion K S W] {ℓ : ℕ} {h : ℤ} {A : AddressMovingFamily ℓ h W}
  {Φ : SwitchFamily (ResAt P) (Localization.AtPrime P)} {ι : Localization.AtPrime P →+* F}
  {u : F}

/-- **Pinned inputs over a genuine family force a nonquadratic prime** (tex 5005–5008): their
frame asks `¬ Φ.quadratic`, which for a genuine family is `NonquadraticAt`; so at a prime
containing `X` or `X + 2` there are none (`not_nonquadraticAt_of_mem`). Kind: PROVED. -/
theorem InnerLimitSwitchPinned.nonquadraticAt (X : InnerLimitSwitchPinned P Cn hW A Φ ι u)
    (hΦ : IsGenuineFamilyAt P Φ) : NonquadraticAt P :=
  hΦ.not_quadratic_iff.mp X.hnq

end PinnedNonquadratic

/-! **The one-configuration family over a residually zero stage** -/

section StageCollapse

variable {P : Ideal Lambda} [P.IsPrime] {F : Type} [Field F] {ι : Localization.AtPrime P →+* F}

/-- **The one-configuration family over a model of a residually zero stage** (tex 4976–4992,
5154–5164): one configuration without successor, fibre `G`, the genuine moving variable `t = X`,
actual class the preimage under the model `M` of the stage class and actual functional the stage
row pulled back along `M` (the transport of `collapseFamily`). Kind: definition. -/
def stageCollapseFamily (G : SelData (ResAt P)) {S : TwoTermStage ι}
    (hS : S.D.map (resAt P) = 0)
    (M : HomotopyEquiv (selCx G).toCC (twoTermFiberComplex (resAt P) S)) :
    SwitchFamily (ResAt P) (Localization.AtPrime P) where
  Config := Unit
  Prime := Empty
  actual := ()
  next c _ := c
  fibre _ := G
  t := algebraMap Lambda (Localization.AtPrime P) PowerSeries.X
  zAct := (M.inv.f 1).hom (fun i => resAt P (S.z i))
  hzAct := by
    have h := congrArg (fun f => (ModuleCat.Hom.hom f) (fun i => resAt P (S.z i)))
      (M.inv.comm 1 2)
    refine h.trans ?_
    simp only [twoTermFiberComplex_d_eq_zero S hS 1 2, Limits.zero_comp]
    rfl
  lamAct :=
    { toFun := fun y =>
        (fun i => resAt P (S.w i)) ⬝ᵥ ((M.hom.f 2).hom y : Fin (S.n + 1) → ResAt P)
      map_add' := fun y y' => by
        rw [map_add]
        exact dotProduct_add _ _ _
      map_smul' := fun c y => by
        change (fun i => resAt P (S.w i)) ⬝ᵥ
          ((M.hom.f 2).hom (c • y) : Fin (S.n + 1) → ResAt P) = _
        rw [map_smul]
        exact dotProduct_smul _ _ _ }
  hlamAct y := by
    change (fun i => resAt P (S.w i)) ⬝ᵥ ((M.hom.f 2).hom (((selCx G).toCC.d 1 2).hom y) :
      Fin (S.n + 1) → ResAt P) = 0
    have h := congrArg (fun f => (ModuleCat.Hom.hom f) y) (M.hom.comm 1 2)
    have h' : (M.hom.f 2).hom (((selCx G).toCC.d 1 2).hom y) = 0 := by
      refine h.symm.trans ?_
      simp [twoTermFiberComplex_d_eq_zero S hS 1 2]
    exact (congrArg (fun v : Fin (S.n + 1) → ResAt P => (fun i => resAt P (S.w i)) ⬝ᵥ v)
      h').trans (dotProduct_zero _)

/-- **The frame of the one-configuration family** (tex 4976–4996, 5005–5008): the stage `S` with
the model `M`, the actual class and functional transported exactly (`homotopyEquiv_hom_inv_one`:
the two-term fibre of a residually zero stage has zero differentials), the starting coordinate
`S.u`, the nonquadratic specialization, and the class nonzero (tex 4992). Kind: PROVED. -/
def stageCollapseFrame (G : SelData (ResAt P)) {S : TwoTermStage ι}
    (hS : S.D.map (resAt P) = 0)
    (M : HomotopyEquiv (selCx G).toCC (twoTermFiberComplex (resAt P) S))
    (hnq : NonquadraticAt P) (hz : ∃ i, S.z i ≠ 0) :
    SwitchModelFrame (stageCollapseFamily G hS M) ι (resAt P) S.u where
  stage _ := S
  model _ := M
  hz0 := homotopyEquiv_hom_inv_one M (twoTermFiberComplex_d_eq_zero S hS 0 1)
    (twoTermFiberComplex_d_eq_zero S hS 1 2) _
  hw0 _ := rfl
  hu0 := rfl
  hnq := hnq
  class_ne_zero _ _ := hz

/-- **The homology-level data of the one-configuration family** (tex 4976–4996, 5009–5054,
5154–5164): the same stage, model, class, functional and coordinate, the identity signs, and no
switch, since the fibre dimension is one. Kind: PROVED. -/
def stageCollapseHomology (G : SelData (ResAt P)) {S : TwoTermStage ι}
    (hS : S.D.map (resAt P) = 0)
    (M : HomotopyEquiv (selCx G).toCC (twoTermFiberComplex (resAt P) S))
    (h2 : (stageCollapseFamily G hS M).quadratic (resAt P) → (2 : ResAt P) ≠ 0)
    (hz : ∃ i, S.z i ≠ 0) (hs : S.fiberDim (resAt P) = 1) :
    HomologySwitchDataPK (stageCollapseFamily G hS M) ι (resAt P) S.u where
  stage _ := S
  model _ := M
  hz0 := homotopyEquiv_hom_inv_one M (twoTermFiberComplex_d_eq_zero S hS 0 1)
    (twoTermFiberComplex_d_eq_zero S hS 1 2) _
  hw0 _ := rfl
  hu0 := rfl
  σ _ := LinearMap.id
  h2 := h2
  hσ _ _ := LinearMap.id_comp _
  class_ne_zero _ _ := hz
  switch_mixed _ _ _ h1 := absurd (h1.trans_eq hs) (lt_irrefl 1)
  switch_single _ _ _ _ h1 := absurd (h1.trans_eq hs) (lt_irrefl 1)

end StageCollapse

/-! **The terminal construction** -/

section Terminal

variable {P : Ideal Lambda} [P.IsPrime] {K : Type} [Field K] [NumberField K]
  {S : Set (HeightOneSpectrum (𝓞 K))} {W : WeierstrassCurve K} {Fam : MovingStageFamily W}
  {ℓ : ℕ} {h : ℤ}

/-- **The terminal family** (tex 4976–4996, 5154–5164): the one-configuration family with fibre
a complex `G` homotopy equivalent (`e`) to the finite fibre of the retained limit `L`, modelled by
the stage of the integral model `Dfin` of its finite side (`finiteFibreModel`). Kind: definition.
-/
def terminalFamily (L : MovingRetainedLimit Fam)
    (Dfin : IntegralMatrixStageData stageIdeal_tendsToZero L.hU
      (algebraMap Lambda (Localization.AtPrime P)) (UniformSwitch.toFracAt P)
      (selmerStages (derivativeDiagram L.C (retainedRestrictionStages L.D) .finite)))
    (G : SelData (ResAt P)) (e : HomotopyEquiv (selCx G).toCC (L.finiteFibre P).toCC) :
    SwitchFamily (ResAt P) (Localization.AtPrime P) :=
  stageCollapseFamily G (L.finiteStage_residue_zero Dfin) (e.trans (L.finiteFibreModel Dfin))

/-- The only fibre of the terminal family is `G` (tex 4976–4980). Kind: PROVED. -/
theorem terminalFamily_fibre (L : MovingRetainedLimit Fam)
    (Dfin : IntegralMatrixStageData stageIdeal_tendsToZero L.hU
      (algebraMap Lambda (Localization.AtPrime P)) (UniformSwitch.toFracAt P)
      (selmerStages (derivativeDiagram L.C (retainedRestrictionStages L.D) .finite)))
    (G : SelData (ResAt P)) (e : HomotopyEquiv (selCx G).toCC (L.finiteFibre P).toCC)
    (c : (terminalFamily L Dfin G e).Config) : (terminalFamily L Dfin G e).fibre c = G :=
  rfl

/-- **The terminal family is nonquadratic exactly at a nonquadratic prime** (tex 5005–5008): its
moving variable is `t = X`. Kind: PROVED. -/
theorem terminalFamily_not_quadratic_iff (L : MovingRetainedLimit Fam)
    (Dfin : IntegralMatrixStageData stageIdeal_tendsToZero L.hU
      (algebraMap Lambda (Localization.AtPrime P)) (UniformSwitch.toFracAt P)
      (selmerStages (derivativeDiagram L.C (retainedRestrictionStages L.D) .finite)))
    (G : SelData (ResAt P)) (e : HomotopyEquiv (selCx G).toCC (L.finiteFibre P).toCC) :
    ¬ (terminalFamily L Dfin G e).quadratic (resAt P) ↔ NonquadraticAt P :=
  Iff.rfl

/-- **The terminal family is genuine as soon as `G` is** (tex 3455–3463, 4976–4980): its only
fibre is `G` and its moving variable is `t = X`. Kind: PROVED. -/
theorem terminalFamily_isGenuine (L : MovingRetainedLimit Fam)
    (Dfin : IntegralMatrixStageData stageIdeal_tendsToZero L.hU
      (algebraMap Lambda (Localization.AtPrime P)) (UniformSwitch.toFracAt P)
      (selmerStages (derivativeDiagram L.C (retainedRestrictionStages L.D) .finite)))
    {G : SelData (ResAt P)} (hG : IsGaloisSelData G)
    (e : HomotopyEquiv (selCx G).toCC (L.finiteFibre P).toCC) :
    IsGenuineFamilyAt P (terminalFamily L Dfin G e) :=
  ⟨fun _ => hG, rfl⟩

/-- **The terminal family is stationary** (tex 5154–5164): no configuration has a proper
successor. Kind: PROVED. -/
theorem terminalFamily_next (L : MovingRetainedLimit Fam)
    (Dfin : IntegralMatrixStageData stageIdeal_tendsToZero L.hU
      (algebraMap Lambda (Localization.AtPrime P)) (UniformSwitch.toFracAt P)
      (selmerStages (derivativeDiagram L.C (retainedRestrictionStages L.D) .finite)))
    (G : SelData (ResAt P)) (e : HomotopyEquiv (selCx G).toCC (L.finiteFibre P).toCC)
    (c : (terminalFamily L Dfin G e).Config) (p : (terminalFamily L Dfin G e).Prime) :
    (terminalFamily L Dfin G e).next c p = c :=
  rfl

variable [W.IsElliptic] [HasFullTwoTorsion K S W]

/-- **The pinned inputs of the terminal case** (tex 4976–5003, 5154–5164): over
the terminal family, at a nonquadratic prime, with nonzero class of `Dfin` and `dim H¹ = 1` of
the finite fibre, the pinned inputs whose stage is `Dfin.stage` at every configuration, with
model `e` followed by `finiteFibreModel` and starting coordinate the coordinate of `Dfin`; the
step field is vacuous since the fibre dimension is one (`fiberDim_finiteStage`). Kind: PROVED. -/
def terminalPinned (Cn : ActualConj K S) (hW : W.map (Cn.κ : K →+* K) = W)
    (A : AddressMovingFamily ℓ h W) (L : MovingRetainedLimit Fam)
    (Dfin : IntegralMatrixStageData stageIdeal_tendsToZero L.hU
      (algebraMap Lambda (Localization.AtPrime P)) (UniformSwitch.toFracAt P)
      (selmerStages (derivativeDiagram L.C (retainedRestrictionStages L.D) .finite)))
    (G : SelData (ResAt P)) (e : HomotopyEquiv (selCx G).toCC (L.finiteFibre P).toCC)
    (hnq : NonquadraticAt P) (hz : ∃ i, Dfin.stage.z i ≠ 0)
    (hdim : finrank (ResAt P) ((L.finiteFibre P).toCC.homology 1) = 1) :
    InnerLimitSwitchPinned P Cn hW A (terminalFamily L Dfin G e) (UniformSwitch.toFracAt P)
      Dfin.stage.u where
  toSwitchModelFrame := stageCollapseFrame G (L.finiteStage_residue_zero Dfin)
    (e.trans (L.finiteFibreModel Dfin)) hnq hz
  step _ _ h1 :=
    absurd (h1.trans_eq ((L.fiberDim_finiteStage Dfin).trans hdim)) (lt_irrefl 1)

/-- The stage of the terminal pinned inputs is `Dfin.stage` (tex 4986–4992). Kind: PROVED. -/
theorem terminalPinned_stage (Cn : ActualConj K S) (hW : W.map (Cn.κ : K →+* K) = W)
    (A : AddressMovingFamily ℓ h W) (L : MovingRetainedLimit Fam)
    (Dfin : IntegralMatrixStageData stageIdeal_tendsToZero L.hU
      (algebraMap Lambda (Localization.AtPrime P)) (UniformSwitch.toFracAt P)
      (selmerStages (derivativeDiagram L.C (retainedRestrictionStages L.D) .finite)))
    (G : SelData (ResAt P)) (e : HomotopyEquiv (selCx G).toCC (L.finiteFibre P).toCC)
    (hnq : NonquadraticAt P) (hz : ∃ i, Dfin.stage.z i ≠ 0)
    (hdim : finrank (ResAt P) ((L.finiteFibre P).toCC.homology 1) = 1)
    (c : (terminalFamily L Dfin G e).Config) :
    (terminalPinned Cn hW A L Dfin G e hnq hz hdim).stage c = Dfin.stage :=
  rfl

/-- **The quadratic-branch data of the terminal case** (tex 5004–5054, 5154–5164): at a
height-one prime, homology-level data over the terminal family whose stage is `Dfin.stage`, with
the identity signs (`2 ≠ 0` at a quadratic height-one prime) and no switch. Kind: PROVED. -/
def terminalHomology (hP : P.height = 1) (L : MovingRetainedLimit Fam)
    (Dfin : IntegralMatrixStageData stageIdeal_tendsToZero L.hU
      (algebraMap Lambda (Localization.AtPrime P)) (UniformSwitch.toFracAt P)
      (selmerStages (derivativeDiagram L.C (retainedRestrictionStages L.D) .finite)))
    (G : SelData (ResAt P)) (e : HomotopyEquiv (selCx G).toCC (L.finiteFibre P).toCC)
    (hz : ∃ i, Dfin.stage.z i ≠ 0)
    (hdim : finrank (ResAt P) ((L.finiteFibre P).toCC.homology 1) = 1) :
    HomologySwitchDataPK (terminalFamily L Dfin G e) (UniformSwitch.toFracAt P) (resAt P)
      Dfin.stage.u :=
  stageCollapseHomology G (L.finiteStage_residue_zero Dfin) (e.trans (L.finiteFibreModel Dfin))
    (fun hq => two_ne_zero_of_not_nonquadraticAt hP (not_not.mpr hq)) hz
    ((L.fiberDim_finiteStage Dfin).trans hdim)

end Terminal

/-! **The faithful-pin clause from the terminal case** -/

section Leaf

/-- **The faithful-pin clause at a height-one prime from the terminal data** (tex 4976–5200,
5154–5164): given the field `K` with places, the actual conjugation and the curve
`W = E_ℓ ⊗ K` with full two-torsion, the address's moving family `A`, a retained limit `L` of it,
an integral model `Dfin` of its finite side at `𝔭` with nonzero class and coordinate `u`, a
genuine realization `G` of the finite fibre (`e`), and `dim H¹ = 1` of the finite fibre,
`RegularityInputsILPAt ℓ h k u 𝔭` holds: through `terminalPinned` at a nonquadratic prime and
through `terminalHomology` at a quadratic one. Kind: PROVED. -/
theorem regularityInputsILPAt_of_terminal {ℓ : ℕ} {h k : ℤ} {u : FractionRing Lambda}
    {P : Ideal Lambda} [P.IsPrime] (hP : P.height = 1) (K : Type) [Field K] [NumberField K]
    (S : Set (HeightOneSpectrum (𝓞 K))) (Cn : ActualConj K S) (W : WeierstrassCurve K)
    (hW : W.map (Cn.κ : K →+* K) = W) [W.IsElliptic] [HasFullTwoTorsion K S W]
    (hWE : W = (Ecurve ℓ).baseChange K) (hK2 : Module.finrank ℚ K = 2)
    (hk : ∃ sk : K, sk ^ 2 = (k : K)) (A : AddressMovingFamily ℓ h W)
    (L : MovingRetainedLimit A.Fam)
    (Dfin : IntegralMatrixStageData stageIdeal_tendsToZero L.hU
      (algebraMap Lambda (Localization.AtPrime P)) (UniformSwitch.toFracAt P)
      (selmerStages (derivativeDiagram L.C (retainedRestrictionStages L.D) .finite)))
    (G : SelData (ResAt P)) (hG : IsGaloisSelData G)
    (e : HomotopyEquiv (selCx G).toCC (L.finiteFibre P).toCC) (hz : ∃ i, Dfin.stage.z i ≠ 0)
    (hdim : finrank (ResAt P) ((L.finiteFibre P).toCC.homology 1) = 1)
    (hu : Dfin.stage.u = u) : RegularityInputsILPAt ℓ h k u P := by
  subst hu
  refine ⟨terminalFamily L Dfin G e, terminalFamily_isGenuine L Dfin hG e, K, inferInstance,
    inferInstance, S, Cn, W, hW, inferInstance, inferInstance, hWE, hK2, hk, A, L, Dfin, ⟨e⟩, ?_⟩
  by_cases hq : (terminalFamily L Dfin G e).quadratic (resAt P)
  · exact Or.inr ⟨hq, terminalHomology hP L Dfin G e hz hdim, rfl⟩
  · exact Or.inl ⟨terminalPinned Cn hW A L Dfin G e
      ((terminalFamily_not_quadratic_iff L Dfin G e).mp hq) hz hdim, rfl⟩

end Leaf

/-! **The collapse is exactly the terminal case** -/

section Collapse

variable {P : Ideal Lambda} [P.IsPrime] {K : Type} [Field K] [NumberField K]
  {S : Set (HeightOneSpectrum (𝓞 K))} (Cn : ActualConj K S) {W : WeierstrassCurve K}
  (hW : W.map (Cn.κ : K →+* K) = W) [W.IsElliptic] [HasFullTwoTorsion K S W] {ℓ : ℕ} {h : ℤ}

/-- **The collapse is exactly the terminal case** (tex 4976–5008, 5154–5164): at a height-one
prime, for the address's moving family `A`, a retained limit `L` and an integral model `Dfin` of
its finite side, there is a family genuine at `𝔭`, stationary, with its actual fibre homotopy
equivalent to the finite fibre of `L` and with nonquadratic pinned inputs starting at `u` whose
actual stage is `Dfin.stage`, if and only if `𝔭` is nonquadratic, `dim H¹ = 1` for the finite
fibre, the finite fibre has a genuine realization, the class of `Dfin` is nonzero and `u` is the
coordinate of `Dfin`. Forward: `terminal_of_stationary`, `class_ne_zero`, `hnq`, `hu0`; backward:
`terminalPinned`. Kind: PROVED. -/
theorem collapse_iff_terminal (hP : P.height = 1) {u : FractionRing Lambda}
    (A : AddressMovingFamily ℓ h W) {Fam : MovingStageFamily W} (L : MovingRetainedLimit Fam)
    (Dfin : IntegralMatrixStageData stageIdeal_tendsToZero L.hU
      (algebraMap Lambda (Localization.AtPrime P)) (UniformSwitch.toFracAt P)
      (selmerStages (derivativeDiagram L.C (retainedRestrictionStages L.D) .finite))) :
    (∃ Φ : SwitchFamily (ResAt P) (Localization.AtPrime P), IsGenuineFamilyAt P Φ ∧
      (∀ c p, Φ.next c p = c) ∧
      Nonempty (HomotopyEquiv (selCx (Φ.fibre Φ.actual)).toCC (L.finiteFibre P).toCC) ∧
      ∃ X : InnerLimitSwitchPinned P Cn hW A Φ (UniformSwitch.toFracAt P) u,
        X.stage Φ.actual = Dfin.stage) ↔
    NonquadraticAt P ∧ finrank (ResAt P) ((L.finiteFibre P).toCC.homology 1) = 1 ∧
      (∃ G : SelData (ResAt P), IsGaloisSelData G ∧
        Nonempty (HomotopyEquiv (selCx G).toCC (L.finiteFibre P).toCC)) ∧
      (∃ i, Dfin.stage.z i ≠ 0) ∧ Dfin.stage.u = u := by
  constructor
  · rintro ⟨Φ, hΦ, hstat, ⟨e⟩, X, hX⟩
    refine ⟨X.nonquadraticAt hΦ, X.terminal_of_stationary hP L e hstat,
      ⟨Φ.fibre Φ.actual, hΦ.1 Φ.actual, ⟨e⟩⟩, ?_, ?_⟩
    · rw [← hX]
      exact X.class_ne_zero Φ.actual Reach.start
    · rw [← hX]
      exact X.hu0
  · rintro ⟨hnq, hdim, ⟨G, hG, ⟨e⟩⟩, hz, rfl⟩
    exact ⟨terminalFamily L Dfin G e, terminalFamily_isGenuine L Dfin hG e,
      terminalFamily_next L Dfin G e, ⟨e⟩, terminalPinned Cn hW A L Dfin G e hnq hz hdim, rfl⟩

/-- **The collapse is exactly the terminal case at a nonquadratic prime** (tex 4976–5008,
5154–5164), with pinned inputs starting at the coordinate of `Dfin`: a genuine stationary family
with the pin and such inputs exists if and only if `dim H¹ = 1` for the finite fibre, the finite
fibre has a genuine realization and the class of `Dfin` is nonzero. Kind: PROVED. -/
theorem collapse_iff_terminal_of_nonquadratic (hP : P.height = 1) (hnq : NonquadraticAt P)
    (A : AddressMovingFamily ℓ h W) {Fam : MovingStageFamily W} (L : MovingRetainedLimit Fam)
    (Dfin : IntegralMatrixStageData stageIdeal_tendsToZero L.hU
      (algebraMap Lambda (Localization.AtPrime P)) (UniformSwitch.toFracAt P)
      (selmerStages (derivativeDiagram L.C (retainedRestrictionStages L.D) .finite))) :
    (∃ Φ : SwitchFamily (ResAt P) (Localization.AtPrime P), IsGenuineFamilyAt P Φ ∧
      (∀ c p, Φ.next c p = c) ∧
      Nonempty (HomotopyEquiv (selCx (Φ.fibre Φ.actual)).toCC (L.finiteFibre P).toCC) ∧
      ∃ X : InnerLimitSwitchPinned P Cn hW A Φ (UniformSwitch.toFracAt P) Dfin.stage.u,
        X.stage Φ.actual = Dfin.stage) ↔
    finrank (ResAt P) ((L.finiteFibre P).toCC.homology 1) = 1 ∧
      (∃ G : SelData (ResAt P), IsGaloisSelData G ∧
        Nonempty (HomotopyEquiv (selCx G).toCC (L.finiteFibre P).toCC)) ∧
      ∃ i, Dfin.stage.z i ≠ 0 :=
  (collapse_iff_terminal Cn hW hP A L Dfin).trans
    ⟨fun ⟨_, h1, h2, h3, _⟩ => ⟨h1, h2, h3⟩, fun ⟨h1, h2, h3⟩ => ⟨hnq, h1, h2, h3, rfl⟩⟩

end Collapse

end ZInQ.Manuscript.RC.Wiring
