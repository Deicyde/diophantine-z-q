import ZInQKernel.Contrib.OneProof.RC.Wiring.CommonCoordinate17Chain
import ZInQKernel.Contrib.OneProof.RC.Wiring.CommonCoordinate17Unit

/-!
# The genuine stage chains with the classes and functionals pinned, one ultrafilter per family

Manuscript `diophantine_zq.tex`, Lemma `ex:arith-common-coordinate` (tex 4142–4194) through the
inner limit of Lemma `ex:limits-inner-limit` (tex 4385–4451).

`GenuineStageSTUE` is `GenuineStageSTUM` with three changes:

* the ultrafilter is a parameter, fixed once per family (tex 4401–4404: "Fix one nonprincipal
  ultrafilter on coefficient stages"), not a field chosen per address;
* the classes are pinned to the presentation's classes of global cocycles (`presClass` of a global
  class and local components agreeing with its restriction; the form of lane E2's pushed classes)
  and the relaxed functionals to the paired functionals of lane RC30's retention at the switches
  (`StepRetention`), consecutive functionals agreeing;
* the end identification at `U_x` carries the text's unit: `∃ ε ∈ Λ^×` with
  `ũ_x = ε η_x v_n` (tex 4147, 4151–4152, 4187–4194), and `ε = 1` when `U_x = ∅` (where
  `ũ_x = η_x u_{prim,x}` by definition, tex 4150).

The coordinates are those of the iterated cone bases: a normalization of the text's retained
integral bases (tex 3886–3888), which the text replaces by the retained models at the cost of a sign
and unit-disk determinants (tex 4189–4193). The sign is `1` identically (`chainSign_eq_one`) and
each step of the chain has `ε = q⁻⁴`, so the pinned form would force `ε_x = ∏_{q ∈ U_x} q⁻⁴`; the
existential `ε` restores the text's freedom. Only the matrix identities pass to the limit: the
retained homotopy inverses and the maps to the original cochains (tex 4403–4404, 4448–4450) are not
carried, and the identification of the limit model with the genuine Λ-adic complexes is the
content of `hprim` and `htildeE`.

What stays existential in a leaf built on this structure (the review's item R9-7): the
presentation's parameters (its objects are pinned in `CommonCoordinate17Actual.lean`), the order of
the primes, the models of `C_∅` and their ranks, the global classes (pinned only through the norm
identity in `hstep`; their identification with the Kummer classes of the actual points is lane
E2's open repair of the ambient module at the switch primes), the cup-product data of the retention
(data, not pinned; the genuine cup product of Nekovář 6.2.5–6.4.3 is the intended instance), the
splittings of the unramified inclusions and the boundaries and coboundaries of the step identities.

Kinds: definitions.
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
open ZInQ.Manuscript.RC.Local (IwasawaGenerators GenuineCochainsInjective)
open scoped PowerSeries.WithPiTopology

section Pinned

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
  {ℓ : ℕ} [(Ecurve ℓ).IsElliptic]

variable (K S₀ S M Δ place X EU) in
/-- **The genuine stage chains of one address, pinned, at a fixed ultrafilter** (tex 4142–4194,
4385–4451): the fields of `GenuineStageSTUM` without the ultrafilter (a parameter, one per family,
tex 4401–4404), with the classes and relaxed functionals pinned (lane E2's form of the classes,
lane RC30's paired functionals) and the end identification at `U_x` up to the text's unit. Each
field's kind and tex lines are in its docstring. Kind: definition (data). -/
structure GenuineStageSTUE (h28 : MilneADT_I_2_8) (hI : IwasawaGenerators)
    (hInj : GenuineCochainsInjective) (C : TateCoef (Ecurve ℓ)) (D : RCData ℓ) (Fam : Family)
    (x : Addr Fam.b) (pidx : ℕ → ι) (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ cofinite) :
    Type 1 where
  /-- the graph primes are odd primes (definition: admissibility of the final family;
  tex 2678–2680, 4143) -/
  hprime : ∀ q ∈ Fam.Q, q.Prime ∧ q ≠ 2
  /-- the graph primes are primes of good reduction (definition: admissibility; tex 4143) -/
  hgood : ∀ q ∈ Fam.Q, Nonvanishing.GoodAt (Ecurve ℓ) q
  /-- the order in which the unused primes are relaxed (definition; tex 4142–4146) -/
  ps : List ℕ
  /-- each unused prime is relaxed once (definition; tex 4142–4146) -/
  hnd : ps.Nodup
  /-- the chain relaxes exactly the unused primes (definition; tex 4142–4146) -/
  hps : ps.toFinset = unusedAt Fam x
  /-- the rank of the model of `C_∅` in degree `0` (ELLIOT: bounded ranks; tex 4401–4406) -/
  m0 : ℕ
  /-- the rank of the model of `C_∅` in degree `1` besides the class (ELLIOT; tex 4401–4406) -/
  m1 : ℕ
  /-- the rank of the model of `C_∅` in degree `3` (ELLIOT; tex 4401–4406) -/
  m2 : ℕ
  /-- the retained stages (ELLIOT: the ranks are fixed along `U`, `exists_shape_fixed`;
  tex 4401–4406) -/
  G : Set ℕ
  /-- they are `U`-many (ELLIOT; tex 4401–4406) -/
  hG : ∀ᶠ s in (U : Filter ℕ), s ∈ G
  /-- the genuine data of the chain at the retained stages (data and named inputs, listed in
  `CommonCoordinate17Leaf.lean`; tex 3455–3498, 4142–4194) -/
  gs : ∀ s, s ∈ G → GenuineStageSteps K S₀ S M Δ place X EU s m0 m1 m2 pidx ps.length
  /-- the traces at the stages (definition: `a_q` at the stage; tex 4169) -/
  a : ∀ s, ℕ → StageRing s
  /-- the global classes at the retained stages (data: lane E2's pushed global classes; their
  identification with the Kummer classes of the actual points is open; tex 4169–4171) -/
  g : ∀ s, s ∈ G → ℕ → (globalCx (StageRing s) (GKS K S) (M s)).X 1
  /-- the local components of the classes (data; tex 4169–4171) -/
  u : ∀ s (_ : s ∈ G) i, (piCx (presCondS K S₀ S (StageRing s) (M s) (Δ s) place (X s) (EU s)
    (chainT pidx i)).U).X 1
  /-- they agree with the restrictions of the global classes (definition of the presentation's
  classes; tex 4169–4171) -/
  hu : ∀ s (h : s ∈ G) i, (piMap (presCondS K S₀ S (StageRing s) (M s) (Δ s) place (X s) (EU s)
    (chainT pidx i)).i).f 1 1 rfl (u s h i) =
      (resS (StageRing s) (GKS K S) (presGv K S₀ S place) (presLoc K S₀ S place) (M s)).f 1 1
        rfl (g s h i)
  /-- the primitive class of `C_∅` is the class of the first global class (pin; tex 4153) -/
  hz0 : ∀ s (h : s ∈ G), (gs s h).st0.z = presClass K S₀ S M Δ place X EU s ∅ (g s h 0) (u s h 0)
  /-- the relaxed classes are the classes of the global classes (pin; tex 4169–4171) -/
  hzR : ∀ s (h : s ∈ G) i, (gs s h).zR i =
    presClass K S₀ S M Δ place X EU s (chainT pidx (i + 1)) (g s h (i + 1)) (u s h (i + 1))
  /-- lane RC30's retention at the switches (GLUE: the cup-product data are not pinned; the
  genuine cup product of Nekovář 6.2.5–6.4.3 is the intended instance; tex 4160–4172) -/
  R : ∀ s (h : s ∈ G) i (hi : i < ps.length),
    StepRetention K S₀ S M Δ place X EU s (chainT pidx i) (pidx i) ((gs s h).hnew i hi)
  /-- the retention's point factor is the step's (definition; tex 4158, 4169) -/
  he : ∀ s (h : s ∈ G) i (hi : i < ps.length),
    (R s h i hi).e = pointFactor (a s i) ((gs s h).z i) ((gs s h).zi i)
  /-- the relaxed functionals are the retention's paired functionals (pin; tex 4171–4172) -/
  hR : ∀ s (h : s ∈ G) i (hi : i < ps.length), (gs s h).lamR i =
    pairedFun (R s h i hi).I.toPlaceRetentionG.toRetainedPairing.QR
      ((R s h i hi).tr : (coneCx (R s h i hi).I.toPlaceRetentionG.toRetainedPairing.QR.resE).X 3
        →ₗ[StageRing s] StageRing s) (R s h i hi).zS
  /-- the primitive functional of each step is the retention's (pin; tex 4171–4172) -/
  hP : ∀ s (h : s ∈ G) i (hi : i < ps.length),
    (cmState ((gs s h).toChainM h28 hI hInj) i hi.le).lam =
      pairedFun (R s h i hi).I.toPlaceRetentionG.toRetainedPairing.QP (R s h i hi).tr
        (R s h i hi).zP
  /-- the boundaries of the norm identities (data; lane E2's retained boundaries;
  tex 4169–4171) -/
  bw : ∀ s i, (genCx K S₀ S M Δ place X EU s (insert (pidx i) (chainT pidx i))).X 0
  /-- the coboundaries of the functional relations (data; lane RC30's retention with
  self-injectivity, `exists_stepHyps_of_switchRetention`; tex 4171–4172) -/
  μ : ∀ s i, (genCx K S₀ S M Δ place X EU s (chainT pidx i)).X 3 →ₗ[StageRing s] StageRing s
  /-- the step inputs at the retained stages: the norm identity with its retained boundary (the
  explicit step input, GLUE: lane E2's norm identity, tex 4157–4171) and the functional relation
  up to a coboundary (GLUE: lane RC30; tex 4171–4172) -/
  hstep : ∀ s (h : s ∈ G), CMStepHyps ((gs s h).toChainM h28 hI hInj) (a s) (bw s) (μ s)
  /-- the leaf's Frobenius data at the retained stages (GLUE: the Frobenius identifications,
  discharged on the actual presentation by `CommonCoordinate17Actual.lean`;
  tex 4144–4145, 4176–4184) -/
  hfrob : ∀ s (h : s ∈ G),
    StageFrobAt (leafFrobΛ C Fam x ps) s ((gs s h).toChainM h28 hI hInj) (a s)
  /-- the primitive coordinate of the limit has `t`-expansion `u_{prim,x}` (definition of
  `u_{prim,x}` in the normalized basis; tex 4153, 4185–4193) -/
  hprim : IsTExpansion
    ((fracChain (stageMatsOn G (fun s h => (gs s h).toChainM h28 hI hInj) bw μ) U).chainV
      (fracChain_holds _ hU _ _ (stageMatsOn_hs G _ bw μ _ U a hG hstep hfrob)) 0)
    (D.uPrim Fam x)
  /-- the corrected coordinate at `U_x` is `ũ_x` up to the text's unit `ε ∈ Λ^×`, with `ε = 1`
  when `U_x = ∅` (definition of `ũ_x = η_x u_{rel,x}` with `u_{rel,x}` in the retained basis;
  tex 4147, 4150–4152, 4187–4194) -/
  htildeE : ∃ ε : Lambdaˣ, (ps = [] → ε = 1) ∧ IsTExpansion (lamToF (ε : Lambda) * (etaF ℓ Fam x *
    (fracChain (stageMatsOn G (fun s h => (gs s h).toChainM h28 hI hInj) bw μ) U).chainV
      (fracChain_holds _ hU _ _ (stageMatsOn_hs G _ bw μ _ U a hG hstep hfrob)) ps.length))
    (D.uTilde Fam x)

/-- **The inner-limit data of one address from the pinned genuine stage chains** (tex 4142–4194,
4385–4451): `CommonCoordinateLimitSTE` at the family's ultrafilter. Kind: definition. -/
def GenuineStageSTUE.toLimitSTE {h28 : MilneADT_I_2_8} {hI : IwasawaGenerators}
    {hInj : GenuineCochainsInjective} {C : TateCoef (Ecurve ℓ)} {D : RCData ℓ} {Fam : Family}
    {x : Addr Fam.b} {pidx : ℕ → ι} {U : Ultrafilter ℕ} {hU : (U : Filter ℕ) ≤ cofinite}
    (Gs : GenuineStageSTUE K S₀ S M Δ place X EU h28 hI hInj C D Fam x pidx U hU) :
    CommonCoordinateLimitSTE C D Fam x U hU where
  hprime := Gs.hprime
  hgood := Gs.hgood
  ps := Gs.ps
  hnd := Gs.hnd
  hps := Gs.hps
  f := leafFrobΛ C Fam x Gs.ps
  hf := leafFrob_leafFrobΛ C Fam x Gs.hprime Gs.hps
  m0 := Gs.m0
  m1 := Gs.m1
  m2 := Gs.m2
  c := stageMatsOn Gs.G (fun s h => (Gs.gs s h).toChainM h28 hI hInj) Gs.bw Gs.μ
  hs := stageMatsOn_hs Gs.G _ Gs.bw Gs.μ _ U Gs.a Gs.hG Gs.hstep Gs.hfrob
  hprim := Gs.hprim
  htildeE := Gs.htildeE

/-- **The step inputs of a pinned chain follow from the pins and the global norm identity**
(tex 4157–4172): for the pinned classes, functionals and retention of one retained stage, lane
E2's global identities `g_{i+1} = e_i g_i + d b_i` with the injectivity and surjectivity of the old
conditions give boundaries and coboundaries for which the step inputs hold
(`exists_stepHyps_of_E2_RC30`). Kind: PROVED. -/
theorem GenuineStageSTUE.exists_stepHyps {h28 : MilneADT_I_2_8} {hI : IwasawaGenerators}
    {hInj : GenuineCochainsInjective} {C : TateCoef (Ecurve ℓ)} {D : RCData ℓ} {Fam : Family}
    {x : Addr Fam.b} {pidx : ℕ → ι} {U : Ultrafilter ℕ} {hU : (U : Filter ℕ) ≤ cofinite}
    (Gs : GenuineStageSTUE K S₀ S M Δ place X EU h28 hI hInj C D Fam x pidx U hU) {s : ℕ}
    (h : s ∈ Gs.G) (bG : ℕ → (globalCx (StageRing s) (GKS K S) (M s)).X 0)
    (hGl : ∀ i, i < Gs.ps.length → Gs.g s h (i + 1) =
      pointFactor (Gs.a s i) ((Gs.gs s h).z i) ((Gs.gs s h).zi i) • Gs.g s h i +
        (globalCx (StageRing s) (GKS K S) (M s)).d 0 1 rfl (bG i))
    (hιold : ∀ v₀, Function.Injective (((Δ s).i v₀).f 1 1 rfl))
    (hsold : ∀ v₀, Function.Surjective (((Δ s).i v₀).f 0 0 rfl))
    (hsEU : ∀ j, Function.Surjective ((EU s j).i.f 0 0 rfl)) :
    ∃ (bw : ∀ i, (genCx K S₀ S M Δ place X EU s (insert (pidx i) (chainT pidx i))).X 0)
      (μ : ∀ i, (genCx K S₀ S M Δ place X EU s (chainT pidx i)).X 3 →ₗ[StageRing s] StageRing s),
      CMStepHyps ((Gs.gs s h).toChainM h28 hI hInj) (Gs.a s) bw μ :=
  exists_stepHyps_of_E2_RC30 ((Gs.gs s h).toChainM h28 hI hInj) (Gs.a s) (Gs.g s h) (Gs.u s h)
    (Gs.hu s h) (Gs.hz0 s h) (Gs.hzR s h) bG hGl hιold hsold hsEU (Gs.gs s h).hnew (Gs.R s h)
    (Gs.he s h) (Gs.hR s h) (Gs.hP s h)

end Pinned

end ZInQ.Manuscript.RC.Wiring
