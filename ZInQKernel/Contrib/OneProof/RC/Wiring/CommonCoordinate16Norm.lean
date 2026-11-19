import ZInQKernel.Contrib.OneProof.RC.Wiring.CommonCoordinate16Bridge
import ZInQKernel.Contrib.CloudB3E2Norm.H20Pres

/-!
# The norm identities of the genuine chain from lane E2's presentation norm identity

Manuscript `diophantine_zq.tex`, Lemma `ex:arith-common-coordinate` (tex 4157–4170: "the actual
norm identity is `z_R = e_q i(z_P)`, with its retained boundary") on the genuine chain of the one
presentation at a coefficient stage (tex 4385–4451).

Lane E2's `hnorm_pres` (`CloudB3E2Norm/H20Pres.lean`) proves the norm identity at one switch for
classes it constructs. Along a chain the class of a support `T_i` is used twice: as the relaxed
class of step `i − 1` and as the primitive class of step `i`. So the classes are fixed once, by
their global and local components, and the identity at every step is lane E2's
`hnorm_changeIncl` for these components:

* `presClass s T g u`: the class `(g, u, 0)` of the support complex `C_T` with global component
  `g` and local component `u`;
* `cmState_z_of_presClass`: the class of every state of a chain built from such classes;
* **`exists_bw_hnorm`**: if the classes of the chain are `presClass (g_i) (u_i)` with
  `ι(u_i) = res(g_i)` and the global identities `g_{i+1} = e_i g_i + d b_{G,i}` hold, the norm
  identities of the steps hold, with boundaries `(b_{G,i}, b_{U,i}, 0)` (lane E2's
  `presι_injective`, `exists_presLift₀`, `hnorm_changeIncl`);
* **`exists_stepHyps_of_E2_RC30`**: with lane RC30's retention data at the switches
  (`exists_stepHyps_of_switchRetention`), the step inputs `CMStepHyps` of the chain, with chosen
  boundaries and coboundaries;
* **`exists_stepData_on`**: one choice over the stages of a set `G`, the fields `bw`, `μ`, `hstep`
  of `GenuineStageSTU`.

The global identities and the local lifts at a stage are lane E2's push of the Shapiro-level
identities (`stage_globalK`, `stage_oldLiftK`, `stage_urLiftK` in `H20PresStage.lean`; from the
named inputs of `h1_shapiro` and the unramified lifts `hur_actualUH`).

Kinds: definitions and PROVED.
-/

noncomputable section

namespace ZInQ.Manuscript.RC.Wiring

open NumberField IsDedekindDomain
open Matrix ZInQ.Manuscript.RC.Central
open ZInQ.Manuscript.RC.Limits (stageIdeal SplitInclusion)
open ZInQ.Contrib.CloudB3RC53.PairedFunctional
open ZInQ.Manuscript.RC.SelmerComplex ZInQ.Contrib.CloudB3RC53.UnramifiedComplex
  ZInQ.Contrib.CloudB3RC53.RankCounts ZInQ.Contrib.CloudB3RC53.SelmerDuality
open ZInQ.Contrib.CloudB3RC53.CommonCoordinate (pairedFun)
open ZInQ.Contrib.CloudB3E2.NormCochain (hnorm_changeIncl presι_injective exists_presLift₀)
open scoped PowerSeries.WithPiTopology

section Norm

attribute [local instance] TopRep.distribMulAction TopRep.smulCommClass

variable {K : Type} [Field K] [NumberField K] {S₀ S : Set (HeightOneSpectrum (𝓞 K))}
  [DecidableEq (Places K S₀)] [∀ s, TopologicalSpace (StageRing s)]
  {M : ℕ → Type} [∀ s, AddCommGroup (M s)] [∀ s, Module (StageRing s) (M s)]
  [∀ s, DistribMulAction (GKS K S) (M s)] [∀ s, SMulCommClass (GKS K S) (StageRing s) (M s)]
  [∀ s, TopologicalSpace (M s)] [∀ s, DiscreteTopology (M s)]
  [∀ s, ContinuousSMul (GKS K S) (M s)]
  {Δ : ∀ s, LocalConditions (StageRing s) (GKS K S) (fun v : Places K S₀ => Gloc K v.1)
    (fun v => locMap K S v.1) (M s)}
  {ι : Type} [DecidableEq ι] {place : ι × Bool → Places K S}
  {X : ∀ s, (j : ι × Bool) → TopRep.{0} (StageRing s) (GUr K (place j).1)}
  {EU : ∀ s j, SplitInclusion (genuineUq K S (StageRing s) (place j) (X s j))
    (genuineLq K S (StageRing s) (M s) (place j))}

variable (K S₀ S M Δ place X EU) in
/-- **The class of a support with given global and local components** (tex 4157–4170,
3455–3463): `(g, u, 0)` in `C_T¹ = G¹ × U_T¹ × L⁰`. Kind: definition. -/
abbrev presClass (s : ℕ) (T : Finset ι) (g : (globalCx (StageRing s) (GKS K S) (M s)).X 1)
    (u : (piCx (presCondS K S₀ S (StageRing s) (M s) (Δ s) place (X s) (EU s) T).U).X 1) :
    (genCx K S₀ S M Δ place X EU s T).X 1 :=
  ((g, u, 0) : selT (suppDataS K S₀ S (StageRing s) (M s) (Δ s) place (X s) (EU s) T) 1)

omit [DecidableEq (Places K S₀)] in
/-- **The classes of the states of a chain built from fixed classes** (tex 4185–4193): if the
class at `∅` and the relaxed classes are the classes `presClass (g_i) (u_i)` of the supports, so is
the class of every state. Kind: PROVED. -/
theorem cmState_z_of_presClass {s m0 m1 m2 : ℕ} {pidx : ℕ → ι} {n : ℕ}
    (cd : CMChainData (genCx K S₀ S M Δ place X EU s) (genSw K S₀ S M Δ place X EU s) m0 m1 m2
      pidx n)
    (g : ℕ → (globalCx (StageRing s) (GKS K S) (M s)).X 1)
    (u : ∀ i, (piCx (presCondS K S₀ S (StageRing s) (M s) (Δ s) place (X s) (EU s)
      (chainT pidx i)).U).X 1)
    (hz0 : cd.st0.z = presClass K S₀ S M Δ place X EU s ∅ (g 0) (u 0))
    (hzR : ∀ i, cd.zR i = presClass K S₀ S M Δ place X EU s (chainT pidx (i + 1)) (g (i + 1))
      (u (i + 1))) :
    ∀ i (h : i ≤ n), (cmState cd i h).z =
      presClass K S₀ S M Δ place X EU s (chainT pidx i) (g i) (u i)
  | 0, _ => hz0
  | i + 1, _ => hzR i

omit [DecidableEq (Places K S₀)] in
/-- **The norm identities of the chain from the global identities** (tex 4157–4170, 4385–4451):
if the classes of the chain are `presClass (g_i) (u_i)` with `ι(u_i) = res(g_i)`, and
`g_{i+1} = e_i g_i + d b_{G,i}` for the steps `i < n`, then with the boundaries
`(b_{G,i}, b_{U,i}, 0)` (`b_{U,i}` a local lift of `res(b_{G,i})`) every step satisfies the norm
identity `z_{R,i} = e_i · i(z_i) + d b_i` (lane E2's `hnorm_changeIncl`). Kind: PROVED. -/
theorem exists_bw_hnorm {s m0 m1 m2 : ℕ} {pidx : ℕ → ι} {n : ℕ}
    (cd : CMChainData (genCx K S₀ S M Δ place X EU s) (genSw K S₀ S M Δ place X EU s) m0 m1 m2
      pidx n)
    (g : ℕ → (globalCx (StageRing s) (GKS K S) (M s)).X 1)
    (u : ∀ i, (piCx (presCondS K S₀ S (StageRing s) (M s) (Δ s) place (X s) (EU s)
      (chainT pidx i)).U).X 1)
    (hu : ∀ i, (piMap (presCondS K S₀ S (StageRing s) (M s) (Δ s) place (X s) (EU s)
      (chainT pidx i)).i).f 1 1 rfl (u i) =
        (resS (StageRing s) (GKS K S) (presGv K S₀ S place) (presLoc K S₀ S place) (M s)).f 1 1
          rfl (g i))
    (hz0 : cd.st0.z = presClass K S₀ S M Δ place X EU s ∅ (g 0) (u 0))
    (hzR : ∀ i, cd.zR i = presClass K S₀ S M Δ place X EU s (chainT pidx (i + 1)) (g (i + 1))
      (u (i + 1)))
    (e : ℕ → StageRing s) (bG : ℕ → (globalCx (StageRing s) (GKS K S) (M s)).X 0)
    (hG : ∀ i, i < n → g (i + 1) = e i • g i +
      (globalCx (StageRing s) (GKS K S) (M s)).d 0 1 rfl (bG i))
    (hιold : ∀ v₀, Function.Injective (((Δ s).i v₀).f 1 1 rfl))
    (hsold : ∀ v₀, Function.Surjective (((Δ s).i v₀).f 0 0 rfl))
    (hsEU : ∀ j, Function.Surjective ((EU s j).i.f 0 0 rfl)) :
    ∃ bw : ∀ i, (genCx K S₀ S M Δ place X EU s (insert (pidx i) (chainT pidx i))).X 0,
      ∀ i (h : i < n), cd.zR i = e i •
          (genSw K S₀ S M Δ place X EU s (chainT pidx i) (pidx i)).i.f 1 1 rfl
            (cmState cd i h.le).z +
        (genCx K S₀ S M Δ place X EU s (insert (pidx i) (chainT pidx i))).d 0 1 rfl (bw i) := by
  have hbU : ∀ i, ∃ bU, (piMap (presCondS K S₀ S (StageRing s) (M s) (Δ s) place (X s) (EU s)
      (insert (pidx i) (chainT pidx i))).i).f 0 0 rfl bU =
        (resS (StageRing s) (GKS K S) (presGv K S₀ S place) (presLoc K S₀ S place) (M s)).f 0 0
          rfl (bG i) := fun i =>
    exists_presLift₀ K S₀ S (StageRing s) (M s) (Δ s) place (X s) (EU s) _ hsold hsEU _
  choose bU hbU using hbU
  refine ⟨fun i => ((bG i, bU i, 0) : selT (suppDataS K S₀ S (StageRing s) (M s) (Δ s) place
    (X s) (EU s) (insert (pidx i) (chainT pidx i))) 0), fun i h => ?_⟩
  rw [hzR i, cmState_z_of_presClass cd g u hz0 hzR i h.le]
  exact hnorm_changeIncl (presCondInclS K S₀ S (StageRing s) (M s) (Δ s) place (X s) (EU s)
      (chainT pidx i) (pidx i)) (g (i + 1)) (g i) (u (i + 1)) (u i) (e i) (bG i) (bU i)
    (presι_injective K S₀ S (StageRing s) (M s) (Δ s) place (X s) (EU s) _ hιold) (hu (i + 1))
    (hu i) (hG i h) (hbU i)

/-- **The step inputs of a genuine stage chain from lanes E2 and RC30** (tex 4157–4172,
4385–4451): the norm identities from the global identities and the fixed classes
(`exists_bw_hnorm`, lane E2), the functional relations from the retention data at the switches
(`exists_stepHyps_of_switchRetention`, lane RC30), at the point factors
`e_i = a_i − z_i − z_i⁻¹`. Kind: PROVED. -/
theorem exists_stepHyps_of_E2_RC30 {s m0 m1 m2 : ℕ} {pidx : ℕ → ι} {n : ℕ}
    (cd : CMChainData (genCx K S₀ S M Δ place X EU s) (genSw K S₀ S M Δ place X EU s) m0 m1 m2
      pidx n)
    (ta : ℕ → StageRing s)
    (g : ℕ → (globalCx (StageRing s) (GKS K S) (M s)).X 1)
    (u : ∀ i, (piCx (presCondS K S₀ S (StageRing s) (M s) (Δ s) place (X s) (EU s)
      (chainT pidx i)).U).X 1)
    (hu : ∀ i, (piMap (presCondS K S₀ S (StageRing s) (M s) (Δ s) place (X s) (EU s)
      (chainT pidx i)).i).f 1 1 rfl (u i) =
        (resS (StageRing s) (GKS K S) (presGv K S₀ S place) (presLoc K S₀ S place) (M s)).f 1 1
          rfl (g i))
    (hz0 : cd.st0.z = presClass K S₀ S M Δ place X EU s ∅ (g 0) (u 0))
    (hzR : ∀ i, cd.zR i = presClass K S₀ S M Δ place X EU s (chainT pidx (i + 1)) (g (i + 1))
      (u (i + 1)))
    (bG : ℕ → (globalCx (StageRing s) (GKS K S) (M s)).X 0)
    (hG : ∀ i, i < n → g (i + 1) = pointFactor (ta i) (cd.z i) (cd.zi i) • g i +
      (globalCx (StageRing s) (GKS K S) (M s)).d 0 1 rfl (bG i))
    (hιold : ∀ v₀, Function.Injective (((Δ s).i v₀).f 1 1 rfl))
    (hsold : ∀ v₀, Function.Surjective (((Δ s).i v₀).f 0 0 rfl))
    (hsEU : ∀ j, Function.Surjective ((EU s j).i.f 0 0 rfl))
    (hp : ∀ i, i < n → pidx i ∉ chainT pidx i)
    (R : ∀ i (h : i < n), StepRetention K S₀ S M Δ place X EU s (chainT pidx i) (pidx i) (hp i h))
    (he : ∀ i (h : i < n), (R i h).e = pointFactor (ta i) (cd.z i) (cd.zi i))
    (hR : ∀ i (h : i < n), cd.lamR i =
      pairedFun (R i h).I.toPlaceRetentionG.toRetainedPairing.QR
        ((R i h).tr : (coneCx (R i h).I.toPlaceRetentionG.toRetainedPairing.QR.resE).X 3 →ₗ[
          StageRing s] StageRing s) (R i h).zS)
    (hP : ∀ i (h : i < n), (cmState cd i h.le).lam =
      pairedFun (R i h).I.toPlaceRetentionG.toRetainedPairing.QP (R i h).tr (R i h).zP) :
    ∃ (bw : ∀ i, (genCx K S₀ S M Δ place X EU s (insert (pidx i) (chainT pidx i))).X 0)
      (μ : ∀ i, (genCx K S₀ S M Δ place X EU s (chainT pidx i)).X 3 →ₗ[StageRing s] StageRing s),
      CMStepHyps cd ta bw μ := by
  obtain ⟨bw, hbw⟩ := exists_bw_hnorm cd g u hu hz0 hzR
    (fun i => pointFactor (ta i) (cd.z i) (cd.zi i)) bG hG hιold hsold hsEU
  obtain ⟨μ, hμ⟩ := exists_stepHyps_of_switchRetention cd ta bw hbw hp R he hR hP
  exact ⟨bw, μ, hμ⟩

end Norm

/-! ### The step data of the genuine chains on a set of stages -/

section StepData

attribute [local instance] TopRep.distribMulAction TopRep.smulCommClass

variable {K : Type} [Field K] [NumberField K] {S₀ S : Set (HeightOneSpectrum (𝓞 K))}
  [DecidableEq (Places K S₀)] [∀ s, TopologicalSpace (StageRing s)]
  {M : ℕ → Type} [∀ s, AddCommGroup (M s)] [∀ s, Module (StageRing s) (M s)]
  [∀ s, DistribMulAction (GKS K S) (M s)] [∀ s, SMulCommClass (GKS K S) (StageRing s) (M s)]
  [∀ s, TopologicalSpace (M s)] [∀ s, DiscreteTopology (M s)]
  [∀ s, ContinuousSMul (GKS K S) (M s)]
  {Δ : ∀ s, LocalConditions (StageRing s) (GKS K S) (fun v : Places K S₀ => Gloc K v.1)
    (fun v => locMap K S v.1) (M s)}
  {ι : Type} [DecidableEq ι] {place : ι × Bool → Places K S}
  {X : ∀ s, (j : ι × Bool) → TopRep.{0} (StageRing s) (GUr K (place j).1)}
  {EU : ∀ s j, SplitInclusion (genuineUq K S (StageRing s) (place j) (X s j))
    (genuineLq K S (StageRing s) (M s) (place j))}
  [∀ s, Module.Free (StageRing s) (M s)] [∀ s, Finite (M s)]
  [∀ s j, ContinuousSMul (GUr K (place j).1) (X s j).V] [∀ s j, DiscreteTopology (X s j).V]
  [∀ s j, Finite (X s j).V]

/-- **The step data of the genuine chains on a set of stages** (tex 4157–4172, 4385–4451): if at
every stage of `G` the step inputs hold for some boundaries and coboundaries (for instance by
`exists_stepHyps_of_E2_RC30`, from lane E2's global identities and lane RC30's retention data),
one choice of boundaries and coboundaries for all stages gives the fields `bw`, `μ`, `hstep` of
`GenuineStageSTU`. Kind: PROVED. -/
theorem exists_stepData_on {hT : ZInQ.Manuscript.RC.Local.TameCochainQuasiIso}
    {hI : ZInQ.Manuscript.RC.Local.IwasawaGenerators}
    {hInj : ZInQ.Manuscript.RC.Local.GenuineCochainsInjective} {m0 m1 m2 : ℕ} {pidx : ℕ → ι}
    {n : ℕ} (G : Set ℕ)
    (gs : ∀ s, s ∈ G → GenuineStageSteps K S₀ S M Δ place X EU s m0 m1 m2 pidx n)
    (ta : ∀ s, ℕ → StageRing s)
    (hE : ∀ s (h : s ∈ G), ∃ (bw : ∀ i, (genCx K S₀ S M Δ place X EU s
        (insert (pidx i) (chainT pidx i))).X 0)
      (μ : ∀ i, (genCx K S₀ S M Δ place X EU s (chainT pidx i)).X 3 →ₗ[StageRing s] StageRing s),
      CMStepHyps ((gs s h).toChain hT hI hInj) (ta s) bw μ) :
    ∃ (bw : ∀ s i, (genCx K S₀ S M Δ place X EU s (insert (pidx i) (chainT pidx i))).X 0)
      (μ : ∀ s i, (genCx K S₀ S M Δ place X EU s (chainT pidx i)).X 3 →ₗ[StageRing s]
        StageRing s),
      ∀ s (h : s ∈ G), CMStepHyps ((gs s h).toChain hT hI hInj) (ta s) (bw s) (μ s) := by
  classical
  refine ⟨fun s => if h : s ∈ G then Classical.choose (hE s h) else 0,
    fun s => if h : s ∈ G then Classical.choose (Classical.choose_spec (hE s h)) else 0,
    fun s h => ?_⟩
  simp only [h, ↓reduceDIte]
  exact Classical.choose_spec (Classical.choose_spec (hE s h))

end StepData

end ZInQ.Manuscript.RC.Wiring
