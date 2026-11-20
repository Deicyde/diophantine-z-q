import ZInQKernel.Contrib.OneProof.RC.Wiring.CommonCoordinate19Staged
import ZInQKernel.Contrib.OneProof.RC.Wiring.CommonCoordinate18Pin

/-!
# The step identities derived from a class provider, on the presentation with staged supports

Manuscript `diophantine_zq.tex`, Lemma `ex:arith-common-coordinate` (tex 4142–4194, 4157–4172)
through the inner limit of Lemma `ex:limits-inner-limit` (tex 4385–4451), on the presentation
`StagedPresentation` (`CommonCoordinate19Staged.lean`: the support of the coefficients at the
stage `s` is `S₀ s ⊇ Sr(s)`, the moving character is the family's).

As `CommonCoordinate18Pin.lean`, with the objects of the stage `s` over the support `S₀ s`:

* `stagedConds_injective`, `stagedConds_surjective₀`, `stagedEU_surjective₀` (PROVED): the old
  conditions are injective in degree one and surjective in degree zero, the inflations surjective
  in degree zero (lane E2's `stageCondK_injective`, `stageCondK_surjective₀`,
  `genuineιq_surjective₀`);
* **`StageClassesAtS P s`**: a class provider at the stage `s` (global classes, their global
  identities with the leaf's point factors, local lifts); `StageClassesAtS.zero`;
* **`exists_stepHyps_providerS`** (PROVED): the step identities `CMStepHyps` of the chain at a
  positive stage are derived from the pins, the provider's identities and lane RC30's retention;
* **`StageChainsS`** (no fields for the global classes, the boundaries, the coboundaries or the
  step identities), `StageChainsS.hstep`, `StageChainsS.limV`, **`GenuineStageSTUS`** with the
  end identifications, and **`GenuineStageSTUS.toLimitSTE`**: the inner-limit data
  `CommonCoordinateLimitSTE` of the address at the family's ultrafilter.

Kinds: definitions and PROVED.
-/

noncomputable section

namespace ZInQ.Manuscript.RC.Wiring

open NumberField IsDedekindDomain
open Matrix Filter ZInQ.Manuscript ZInQ.Manuscript.RC ZInQ.Manuscript.RC.Central
  ZInQ.Manuscript.RC.Uniform ZInQ.Contrib.CloudB3RC53 ZInQ.Contrib.CloudB3RC53.CommonCoordinate
open ZInQ.Manuscript.RC.Limits (stageIdeal SplitInclusion MilneADT_I_2_8)
open ZInQ.Contrib.CloudB3RC53.PairedFunctional
open ZInQ.Manuscript.RC.SelmerComplex ZInQ.Contrib.CloudB3RC53.UnramifiedComplex
  ZInQ.Contrib.CloudB3RC53.RankCounts
open ZInQ.Manuscript.RC.CoefModules ZInQ.Manuscript.RC.LambdaCoef
open ZInQ.Manuscript.RC.HeegnerAlgebra (Acoef)
open ZInQ.Manuscript.RC.Local (IwasawaGenerators GenuineCochainsInjective)
open ZInQ.Contrib.CloudB3E2.NormCochain (stageCondK_injective stageCondK_surjective₀
  genuineιq_surjective₀ stageIsoA)
open scoped PowerSeries.WithPiTopology

attribute [local instance] TopRep.distribMulAction TopRep.smulCommClass

variable {ℓ : ℕ} [(Ecurve ℓ).IsElliptic] {C : TateCoef (Ecurve ℓ)} {D : RCData ℓ}
  {Fam : Family} {x : Addr Fam.b} {Ψ : FamilyMovingCharacter C.K ℓ Fam.Q}
  (P : StagedPresentation C D Fam x Ψ)

/-! ### The local maps of the staged presentation -/

section LocalMaps

/-- **The old conditions are injective in degree one** at a positive stage (lane E2's
`stageCondK_injective`; tex 2743–2760). Kind: PROVED. -/
theorem stagedConds_injective (t : ℕ) (v₀ : Places C.K (P.S₀ (t + 1))) :
    Function.Injective (((famConds P (t + 1) (t + 1)).i v₀).f 1 1 rfl) := by
  let _ := acoefTop (t + 1)
  have _ := acoefTop_discrete (t + 1)
  let _ := stageIsoA (t + 1)
  exact stageCondK_injective (P.hS (t + 1)) ((Ecurve ℓ).baseChange C.K) (t + 1) (P.sh (t + 1))
    (P.hs (t + 1)) (P.hs0 (t + 1)) (HasFullTwoTorsion.full (t + 1)) (P.ξ (t + 1))
    (P.ψf (t + 1) (t + 1)) P.Pk (P.hΨ (t + 1) (t + 1)) (StageRing (t + 1)) v₀

/-- **The old conditions are surjective in degree zero** at a positive stage (lane E2's
`stageCondK_surjective₀`; tex 2743–2760). Kind: PROVED. -/
theorem stagedConds_surjective₀ (t : ℕ) (v₀ : Places C.K (P.S₀ (t + 1))) :
    Function.Surjective (((famConds P (t + 1) (t + 1)).i v₀).f 0 0 rfl) := by
  let _ := acoefTop (t + 1)
  have _ := acoefTop_discrete (t + 1)
  let _ := stageIsoA (t + 1)
  exact stageCondK_surjective₀ (P.hS (t + 1)) ((Ecurve ℓ).baseChange C.K) (t + 1)
    (P.sh (t + 1)) (P.hs (t + 1)) (P.hs0 (t + 1)) (HasFullTwoTorsion.full (t + 1)) (P.ξ (t + 1))
    (P.ψf (t + 1) (t + 1)) P.Pk (P.hΨ (t + 1) (t + 1)) (StageRing (t + 1)) v₀

/-- **The genuine inflations are surjective in degree zero** (lane E2's
`genuineιq_surjective₀`, along `urId`; tex 3470–3487). Kind: PROVED. -/
theorem stagedEU_surjective₀ (s : ℕ) (j : P.ι × Bool) :
    Function.Surjective ((famEU P s s j).i.f 0 0 rfl) := by
  rw [famEU_i P s s j]
  exact genuineιq_surjective₀ (P.place s j) _ _ _
    (urId_bijective (StageRing s) _ (P.hS s) (newPlace (P.place s j) (P.hwp s j))).2

end LocalMaps

/-! ### Class providers -/

section Provider

/-- **A class provider at the stage `s`** (tex 4157–4172): global classes `g_j` of the
coefficient module of the stage, the global identities `g_{i+1} = e_i g_i + d b_i` with the leaf's
point factors at the stage, and local lifts of `g_j` at the conditions of the support `C_{T_j}`.
The zero classes form a provider (`StageClassesAtS.zero`): the leaf pins the provider to the
Kummer classes of the actual Heegner points. Kind: definition (data). -/
structure StageClassesAtS (s : ℕ) : Type where
  /-- the global classes -/
  g : ℕ → (globalCx (StageRing s) (GKS C.K (P.S s)) (famM P s s)).X 1
  /-- the global identities at the steps -/
  hG : ∀ i < P.ps.length,
    ∃ bG : (globalCx (StageRing s) (GKS C.K (P.S s)) (famM P s s)).X 0,
      g (i + 1) = pointFactor (((leafFrobΛ C Fam x P.ps).map (stageMk s)).a i)
          (((leafFrobΛ C Fam x P.ps).map (stageMk s)).z i)
          (((leafFrobΛ C Fam x P.ps).map (stageMk s)).zi i) • g i +
        (globalCx (StageRing s) (GKS C.K (P.S s)) (famM P s s)).d 0 1 rfl bG
  /-- the local lifts at the conditions of the supports -/
  hloc : ∀ j ≤ P.ps.length, ∃ u : (piCx (presCondS C.K (P.S₀ s) (P.S s) (StageRing s)
      (famM P s s) (famConds P s s) (P.place s) (famX P s s) (famEU P s s)
      (chainT P.pidx j)).U).X 1,
    (piMap (presCondS C.K (P.S₀ s) (P.S s) (StageRing s) (famM P s s) (famConds P s s)
      (P.place s) (famX P s s) (famEU P s s) (chainT P.pidx j)).i).f 1 1 rfl u =
      (resS (StageRing s) (GKS C.K (P.S s)) (presGv C.K (P.S₀ s) (P.S s) (P.place s))
        (presLoc C.K (P.S₀ s) (P.S s) (P.place s)) (famM P s s)).f 1 1 rfl (g j)

/-- **The zero provider** (tex 4157–4172). Kind: definition. -/
def StageClassesAtS.zero (s : ℕ) : StageClassesAtS P s where
  g _ := 0
  hG _ _ := ⟨0, by rw [smul_zero, map_zero, add_zero]⟩
  hloc _ _ := ⟨0, by rw [map_zero, map_zero]⟩

variable {P} {s : ℕ}

open Classical in
/-- The provider's classes, extended by `0` beyond the chain. Kind: definition. -/
def StageClassesAtS.gx (HC : StageClassesAtS P s) (j : ℕ) :
    (globalCx (StageRing s) (GKS C.K (P.S s)) (famM P s s)).X 1 :=
  if j ≤ P.ps.length then HC.g j else 0

open Classical in
/-- The chosen local lifts of the provider's classes, `0` beyond the chain. Kind: definition. -/
def StageClassesAtS.ux (HC : StageClassesAtS P s) (j : ℕ) :
    (piCx (presCondS C.K (P.S₀ s) (P.S s) (StageRing s) (famM P s s) (famConds P s s)
      (P.place s) (famX P s s) (famEU P s s) (chainT P.pidx j)).U).X 1 :=
  if hj : j ≤ P.ps.length then Classical.choose (HC.hloc j hj) else 0

/-- The chosen lifts lift the extended classes (tex 4157–4172). Kind: PROVED. -/
theorem StageClassesAtS.hux (HC : StageClassesAtS P s) (j : ℕ) :
    (piMap (presCondS C.K (P.S₀ s) (P.S s) (StageRing s) (famM P s s) (famConds P s s)
      (P.place s) (famX P s s) (famEU P s s) (chainT P.pidx j)).i).f 1 1 rfl (HC.ux j) =
      (resS (StageRing s) (GKS C.K (P.S s)) (presGv C.K (P.S₀ s) (P.S s) (P.place s))
        (presLoc C.K (P.S₀ s) (P.S s) (P.place s)) (famM P s s)).f 1 1 rfl (HC.gx j) := by
  by_cases hj : j ≤ P.ps.length
  · simp only [StageClassesAtS.ux, StageClassesAtS.gx, hj, ↓reduceDIte, ↓reduceIte]
    exact Classical.choose_spec (HC.hloc j hj)
  · simp only [StageClassesAtS.ux, StageClassesAtS.gx, hj, ↓reduceDIte, ↓reduceIte, map_zero]

/-- The extended classes satisfy the global identities at the steps (tex 4157–4172).
Kind: PROVED. -/
theorem StageClassesAtS.hGx (HC : StageClassesAtS P s) {i : ℕ} (hi : i < P.ps.length) :
    ∃ bG : (globalCx (StageRing s) (GKS C.K (P.S s)) (famM P s s)).X 0,
      HC.gx (i + 1) = pointFactor (((leafFrobΛ C Fam x P.ps).map (stageMk s)).a i)
          (((leafFrobΛ C Fam x P.ps).map (stageMk s)).z i)
          (((leafFrobΛ C Fam x P.ps).map (stageMk s)).zi i) • HC.gx i +
        (globalCx (StageRing s) (GKS C.K (P.S s)) (famM P s s)).d 0 1 rfl bG := by
  have h1 : i + 1 ≤ P.ps.length := hi
  have h2 : i ≤ P.ps.length := hi.le
  simp only [StageClassesAtS.gx, h1, h2, ↓reduceIte]
  exact HC.hG i hi

end Provider

/-! ### The step identities derived from a provider -/

section Chains

variable [∀ s, DecidableEq (Places C.K (P.S₀ s))]

/-- The leaf's traces at the stage (tex 4169). Kind: definition. -/
abbrev leafTrS (s : ℕ) (i : ℕ) : StageRing s := ((leafFrobΛ C Fam x P.ps).map (stageMk s)).a i

variable {P}

/-- **The step identities of a stage chain are derived from a provider** (tex 4157–4172,
4385–4451): at a positive stage, from the pins of the classes and the functionals, the point
factors and the Frobenius data (`exists_stepHyps_of_E2_RC30`, with the old conditions and the
inflations of the stage). Kind: PROVED. -/
theorem exists_stepHyps_providerS {h28 : MilneADT_I_2_8} {hI : IwasawaGenerators}
    {hInj : GenuineCochainsInjective} {s m0 m1 m2 : ℕ} (hs : 0 < s)
    (gs : GenuineStageSteps C.K (P.S₀ s) (P.S s) (famM P s) (famConds P s) (P.place s)
      (famX P s) (famEU P s) s m0 m1 m2 P.pidx P.ps.length)
    (HC : StageClassesAtS P s)
    (hz0 : gs.st0.z = presClass C.K (P.S₀ s) (P.S s) (famM P s) (famConds P s) (P.place s)
      (famX P s) (famEU P s) s ∅ (HC.gx 0) (HC.ux 0))
    (hzR : ∀ i, gs.zR i = presClass C.K (P.S₀ s) (P.S s) (famM P s) (famConds P s) (P.place s)
      (famX P s) (famEU P s) s (chainT P.pidx (i + 1)) (HC.gx (i + 1)) (HC.ux (i + 1)))
    (R : ∀ i (hi : i < P.ps.length), StepRetention C.K (P.S₀ s) (P.S s) (famM P s)
      (famConds P s) (P.place s) (famX P s) (famEU P s) s (chainT P.pidx i) (P.pidx i)
      (gs.hnew i hi))
    (he : ∀ i (hi : i < P.ps.length),
      (R i hi).e = pointFactor (leafTrS P s i) (gs.z i) (gs.zi i))
    (hR : ∀ i (hi : i < P.ps.length), gs.lamR i =
      pairedFun (R i hi).I.toPlaceRetentionG.toRetainedPairing.QR
        ((R i hi).tr : (coneCx (R i hi).I.toPlaceRetentionG.toRetainedPairing.QR.resE).X 3
          →ₗ[StageRing s] StageRing s) (R i hi).zS)
    (hP : ∀ i (hi : i < P.ps.length), (cmState (gs.toChainM h28 hI hInj) i hi.le).lam =
      pairedFun (R i hi).I.toPlaceRetentionG.toRetainedPairing.QP (R i hi).tr (R i hi).zP)
    (hfrob : StageFrobAt (Cx := stagedCx P) (Ex := stagedSw P) (leafFrobΛ C Fam x P.ps) s
      (gs.toChainM h28 hI hInj) (leafTrS P s)) :
    ∃ (bw : ∀ i, (genCx C.K (P.S₀ s) (P.S s) (famM P s) (famConds P s) (P.place s) (famX P s)
        (famEU P s) s (insert (P.pidx i) (chainT P.pidx i))).X 0)
      (μ : ∀ i, (genCx C.K (P.S₀ s) (P.S s) (famM P s) (famConds P s) (P.place s) (famX P s)
        (famEU P s) s (chainT P.pidx i)).X 3 →ₗ[StageRing s] StageRing s),
      CMStepHyps (gs.toChainM h28 hI hInj) (leafTrS P s) bw μ := by
  obtain ⟨t, rfl⟩ : ∃ t, s = t + 1 := ⟨s - 1, by omega⟩
  have hG : ∀ i, ∃ bG : (globalCx (StageRing (t + 1)) (GKS C.K (P.S (t + 1)))
      (famM P (t + 1) (t + 1))).X 0,
      i < P.ps.length → HC.gx (i + 1) = pointFactor (leafTrS P (t + 1) i)
        ((gs.toChainM h28 hI hInj).z i) ((gs.toChainM h28 hI hInj).zi i) • HC.gx i +
        (globalCx (StageRing (t + 1)) (GKS C.K (P.S (t + 1))) (famM P (t + 1) (t + 1))).d 0 1
          rfl bG := by
    intro i
    by_cases hi : i < P.ps.length
    · obtain ⟨bG, hbG⟩ := HC.hGx hi
      obtain ⟨-, -, hz, hzi, -⟩ := hfrob i hi
      refine ⟨bG, fun _ => ?_⟩
      rw [← hz, ← hzi]
      exact hbG
    · exact ⟨0, fun h => absurd h hi⟩
  choose bG hbG using hG
  exact exists_stepHyps_of_E2_RC30 (gs.toChainM h28 hI hInj) (leafTrS P (t + 1)) HC.gx HC.ux
    HC.hux hz0 hzR bG hbG (stagedConds_injective P t) (stagedConds_surjective₀ P t)
    (stagedEU_surjective₀ P (t + 1)) gs.hnew R he hR hP

end Chains

/-! ### The genuine stage chains with the classes of a provider -/

section Structure

variable [∀ s, DecidableEq (Places C.K (P.S₀ s))]

/-- **The genuine stage chains of one address with the classes of a provider, on the staged
presentation** (tex 4142–4194, 4157–4172, 4385–4451): at the retained stages `G` (all positive),
the genuine data of the chain on the objects of the stage, with the classes pinned to the
presentation's classes of the provider's global classes, the functionals pinned to lane RC30's
paired functionals of a retention (the retention `R` is a free GLUE field, so these paired
functionals are free), and the leaf's Frobenius data (a GLUE field, PROVED for the chains of
`stagedSteps`, `stagedSteps_stageFrobAt`). There are no fields for the global classes, the
boundaries, the coboundaries or the step identities. Kind: definition (data). -/
structure StageChainsS (h28 : MilneADT_I_2_8) (hI : IwasawaGenerators)
    (hInj : GenuineCochainsInjective) (G : Set ℕ) (HC : ∀ s, s ∈ G → StageClassesAtS P s) :
    Type 1 where
  /-- the retained stages are positive (definition) -/
  hpos : ∀ s ∈ G, 0 < s
  /-- the rank of the model of `C_∅` in degree `0` (ELLIOT: bounded ranks; tex 4401–4406) -/
  m0 : ℕ
  /-- the rank of the model of `C_∅` in degree `1` besides the class (ELLIOT; tex 4401–4406) -/
  m1 : ℕ
  /-- the rank of the model of `C_∅` in degree `3` (ELLIOT; tex 4401–4406) -/
  m2 : ℕ
  /-- the genuine data of the chain at the retained stages (data and named inputs; on the staged
  presentation, `stagedSteps`; tex 3455–3498, 4142–4194) -/
  gs : ∀ s, s ∈ G → GenuineStageSteps C.K (P.S₀ s) (P.S s) (famM P s) (famConds P s) (P.place s)
    (famX P s) (famEU P s) s m0 m1 m2 P.pidx P.ps.length
  /-- the primitive class of `C_∅` is the class of the provider's first class (pin; tex 4153) -/
  hz0 : ∀ s (h : s ∈ G), (gs s h).st0.z = presClass C.K (P.S₀ s) (P.S s) (famM P s)
    (famConds P s) (P.place s) (famX P s) (famEU P s) s ∅ ((HC s h).gx 0) ((HC s h).ux 0)
  /-- the relaxed classes are the classes of the provider's classes (pin; tex 4169–4171) -/
  hzR : ∀ s (h : s ∈ G) i, (gs s h).zR i = presClass C.K (P.S₀ s) (P.S s) (famM P s)
    (famConds P s) (P.place s) (famX P s) (famEU P s) s (chainT P.pidx (i + 1))
      ((HC s h).gx (i + 1)) ((HC s h).ux (i + 1))
  /-- lane RC30's retention at the switches (GLUE; tex 4160–4172; free: not pinned to the text's
  paired side, so the paired functionals of `hR`, `hP` are free) -/
  R : ∀ s (h : s ∈ G) i (hi : i < P.ps.length), StepRetention C.K (P.S₀ s) (P.S s) (famM P s)
    (famConds P s) (P.place s) (famX P s) (famEU P s) s (chainT P.pidx i) (P.pidx i)
      ((gs s h).hnew i hi)
  /-- the retention's point factor is the leaf's (definition; tex 4158, 4169) -/
  he : ∀ s (h : s ∈ G) i (hi : i < P.ps.length),
    (R s h i hi).e = pointFactor (leafTrS P s i) ((gs s h).z i) ((gs s h).zi i)
  /-- the relaxed functionals are the retention's paired functionals (pin; tex 4171–4172) -/
  hR : ∀ s (h : s ∈ G) i (hi : i < P.ps.length), (gs s h).lamR i =
    pairedFun (R s h i hi).I.toPlaceRetentionG.toRetainedPairing.QR
      ((R s h i hi).tr : (coneCx (R s h i hi).I.toPlaceRetentionG.toRetainedPairing.QR.resE).X 3
        →ₗ[StageRing s] StageRing s) (R s h i hi).zS
  /-- the primitive functional of each step is the retention's (pin; tex 4171–4172) -/
  hP : ∀ s (h : s ∈ G) i (hi : i < P.ps.length),
    (cmState ((gs s h).toChainM h28 hI hInj) i hi.le).lam =
      pairedFun (R s h i hi).I.toPlaceRetentionG.toRetainedPairing.QP (R s h i hi).tr
        (R s h i hi).zP
  /-- the leaf's Frobenius data (GLUE: the Frobenius identifications; PROVED for the chains of
  `stagedSteps`, `stagedSteps_stageFrobAt`; tex 4144–4145, 4176–4184) -/
  hfrob : ∀ s (h : s ∈ G),
    StageFrobAt (Cx := stagedCx P) (Ex := stagedSw P) (leafFrobΛ C Fam x P.ps) s
      ((gs s h).toChainM h28 hI hInj) (leafTrS P s)

variable {P} {h28 : MilneADT_I_2_8} {hI : IwasawaGenerators} {hInj : GenuineCochainsInjective}
  {G : Set ℕ} {HC : ∀ s, s ∈ G → StageClassesAtS P s}

/-- **The step identities hold at every retained stage** (PROVED;
`exists_stepHyps_providerS`). -/
theorem StageChainsS.ex (Q : StageChainsS P h28 hI hInj G HC) :
    ∀ s (h : s ∈ G), ∃ (bw : ∀ i, (genCx C.K (P.S₀ s) (P.S s) (famM P s) (famConds P s)
        (P.place s) (famX P s) (famEU P s) s (insert (P.pidx i) (chainT P.pidx i))).X 0)
      (μ : ∀ i, (genCx C.K (P.S₀ s) (P.S s) (famM P s) (famConds P s) (P.place s) (famX P s)
        (famEU P s) s (chainT P.pidx i)).X 3 →ₗ[StageRing s] StageRing s),
      CMStepHyps ((Q.gs s h).toChainM h28 hI hInj) (leafTrS P s) bw μ :=
  fun s h => exists_stepHyps_providerS (Q.hpos s h) (Q.gs s h) (HC s h) (Q.hz0 s h) (Q.hzR s h)
    (Q.R s h) (Q.he s h) (Q.hR s h) (Q.hP s h) (Q.hfrob s h)

/-- The chosen boundaries of the norm identities (tex 4169–4171). Kind: definition. -/
noncomputable def StageChainsS.bw (Q : StageChainsS P h28 hI hInj G HC) (s : ℕ) :
    ∀ i, (genCx C.K (P.S₀ s) (P.S s) (famM P s) (famConds P s) (P.place s) (famX P s)
      (famEU P s) s (insert (P.pidx i) (chainT P.pidx i))).X 0 :=
  (chooseOn Q.ex s).1

/-- The chosen coboundaries of the functional relations (tex 4171–4172). Kind: definition. -/
noncomputable def StageChainsS.μ (Q : StageChainsS P h28 hI hInj G HC) (s : ℕ) :
    ∀ i, (genCx C.K (P.S₀ s) (P.S s) (famM P s) (famConds P s) (P.place s) (famX P s)
      (famEU P s) s (chainT P.pidx i)).X 3 →ₗ[StageRing s] StageRing s :=
  (chooseOn Q.ex s).2

/-- **The step identities with the chosen witnesses** (tex 4157–4172). Kind: PROVED. -/
theorem StageChainsS.hstep (Q : StageChainsS P h28 hI hInj G HC) :
    ∀ s (h : s ∈ G), CMStepHyps ((Q.gs s h).toChainM h28 hI hInj) (leafTrS P s) (Q.bw s)
      (Q.μ s) :=
  chooseOn_spec Q.ex

/-- **The lifted matrix data of the staged chains** (tex 4385–4451). Kind: definition. -/
noncomputable def StageChainsS.mats (Q : StageChainsS P h28 hI hInj G HC) :
    ℕ → ChainMat LamI Q.m0 Q.m1 Q.m2 :=
  stageMatsOn (Cx := stagedCx P) (Ex := stagedSw P) G
    (fun s h => (Q.gs s h).toChainM h28 hI hInj) Q.bw Q.μ

/-- **Their identities at `U`-many stages** (tex 4385–4451): from the derived step identities and
the leaf's Frobenius data. Kind: PROVED. -/
theorem StageChainsS.mats_hs (Q : StageChainsS P h28 hI hInj G HC) (U : Ultrafilter ℕ)
    (hG : ∀ᶠ s in (U : Filter ℕ), s ∈ G) :
    ∀ᶠ s in (U : Filter ℕ), (Q.mats s).Holds (stageIdeal s) (leafFrobΛ C Fam x P.ps)
      P.ps.length :=
  stageMatsOn_hs (Cx := stagedCx P) (Ex := stagedSw P) G
    (fun s h => (Q.gs s h).toChainM h28 hI hInj) Q.bw Q.μ (leafFrobΛ C Fam x P.ps) U
    (leafTrS P) hG Q.hstep Q.hfrob

/-- **The coordinates of the limit chain** (tex 4185–4193, 4401–4406, 4444–4448): the values of
the chain over `Frac Λ` of the ultralimit of the stage data. Kind: definition. -/
noncomputable def StageChainsS.limV (Q : StageChainsS P h28 hI hInj G HC) (U : Ultrafilter ℕ)
    (hU : (U : Filter ℕ) ≤ cofinite) (hG : ∀ᶠ s in (U : Filter ℕ), s ∈ G) (i : ℕ) : FracLam :=
  (fracChain Q.mats U).chainV (fracChain_holds Q.mats hU _ _ (Q.mats_hs U hG)) i

/-- **The genuine stage chains of one address with the classes of a provider, on the staged
presentation, at a fixed ultrafilter** (tex 4142–4194, 4385–4451): the chains on `U`-many stages
and the end identifications with the leaf's data (`ũ_x` up to the text's unit `ε_x ∈ Λ^×`, `1`
when `U_x = ∅`). Kind: definition (data). -/
structure GenuineStageSTUS (P : StagedPresentation C D Fam x Ψ)
    [∀ s, DecidableEq (Places C.K (P.S₀ s))] (h28 : MilneADT_I_2_8) (hI : IwasawaGenerators)
    (hInj : GenuineCochainsInjective) (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ cofinite)
    (G : Set ℕ) (HC : ∀ s, s ∈ G → StageClassesAtS P s) : Type 1 where
  /-- the graph primes are primes of good reduction (definition: admissibility; tex 4143) -/
  hgood : ∀ q ∈ Fam.Q, Nonvanishing.GoodAt (Ecurve ℓ) q
  /-- the retained stages are `U`-many (ELLIOT: the ranks are fixed along `U`; tex 4401–4406) -/
  hG : ∀ᶠ s in (U : Filter ℕ), s ∈ G
  /-- the chains at the retained stages -/
  pre : StageChainsS P h28 hI hInj G HC
  /-- the primitive coordinate of the limit has `t`-expansion `u_{prim,x}` (definition of
  `u_{prim,x}` in the normalized basis; tex 4153, 4185–4193) -/
  hprim : IsTExpansion (pre.limV U hU hG 0) (D.uPrim Fam x)
  /-- the corrected coordinate at `U_x` is `ũ_x` up to the text's unit (definition of `ũ_x`;
  tex 4147, 4150–4152, 4187–4194; given `hprim`, exactly the target identity
  `ũ_x = ε_x u_{prim,x}`) -/
  htildeE : ∃ ε : Lambdaˣ, (P.ps = [] → ε = 1) ∧
    IsTExpansion (lamToF (ε : Lambda) * (etaF ℓ Fam x * pre.limV U hU hG P.ps.length))
      (D.uTilde Fam x)

/-- **The inner-limit data of the address from the staged chains** (tex 4142–4194, 4385–4451):
`CommonCoordinateLimitSTE` at the family's ultrafilter; the step identities are derived
(`StageChainsS.hstep`). Kind: definition. -/
noncomputable def GenuineStageSTUS.toLimitSTE {U : Ultrafilter ℕ}
    {hU : (U : Filter ℕ) ≤ cofinite} (Gs : GenuineStageSTUS P h28 hI hInj U hU G HC) :
    CommonCoordinateLimitSTE C D Fam x U hU where
  hprime := P.hprime
  hgood := Gs.hgood
  ps := P.ps
  hnd := P.hnd
  hps := P.hps
  f := leafFrobΛ C Fam x P.ps
  hf := leafFrob_leafFrobΛ C Fam x P.hprime P.hps
  m0 := Gs.pre.m0
  m1 := Gs.pre.m1
  m2 := Gs.pre.m2
  c := Gs.pre.mats
  hs := Gs.pre.mats_hs U Gs.hG
  hprim := Gs.hprim
  htildeE := Gs.htildeE

end Structure

end ZInQ.Manuscript.RC.Wiring
