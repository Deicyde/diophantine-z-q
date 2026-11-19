import ZInQKernel.Contrib.OneProof.RC.Wiring.CommonCoordinate16Norm
import ZInQKernel.Contrib.OneProof.RC.Local.TameDevissage

/-!
# The genuine stage chains from the literature: the switch retractions from Milne

Manuscript `diophantine_zq.tex`, Lemma `ex:arith-common-coordinate` (tex 4142–4194, 4176–4184)
on the genuine chain of the one presentation at the coefficient stages (tex 4385–4451).

The retractions of the quotients of the switches onto the two singular blocks were obtained in
round eleven from `TameCochainQuasiIso`; the dévissage of `TameDevissage.lean` replaces that input
by the PRINT `MilneADT_I_2_8` (`exists_retract_twoPlaces_place_stage_milne`):

* **`exists_suppSwitchRetractS_milne`**: the retraction of the quotient of `suppSwitchS T p`
  onto `twoSingCx F q z z⁻¹`, from `MilneADT_I_2_8`, `IwasawaGenerators` and
  `GenuineCochainsInjective`;
* `GenuineStageSteps.toChainM`: the genuine stage chain with these retractions;
* **`GenuineStageSTUM`**, **`GenuineStageSTUM.toLimitST`**: the genuine stage chains of the leaf on
  a `U`-large set of stages, with the literature inputs `MilneADT_I_2_8`, `IwasawaGenerators` and
  `GenuineCochainsInjective` in place of `TameCochainQuasiIso`, give `CommonCoordinateLimitST`;

Kinds: definitions and PROVED.
-/

noncomputable section

namespace ZInQ.Manuscript.RC.Wiring

open NumberField IsDedekindDomain
open Matrix Filter ZInQ.Manuscript ZInQ.Manuscript.RC ZInQ.Manuscript.RC.Central
  ZInQ.Manuscript.RC.Uniform ZInQ.Contrib.CloudB3RC53 ZInQ.Contrib.CloudB3RC53.CommonCoordinate
open ZInQ.Manuscript.RC.Limits (stageIdeal SplitInclusion MilneADT_I_2_8 GRetract)
open ZInQ.Contrib.CloudB3RC53.PairedFunctional
open ZInQ.Manuscript.RC.SelmerComplex ZInQ.Contrib.CloudB3RC53.UnramifiedComplex
  ZInQ.Contrib.CloudB3RC53.RankCounts
open ZInQ.Manuscript.RC.Local (twoSingCx IwasawaGenerators GenuineCochainsInjective
  exists_retract_twoPlaces_place_stage_milne)
open scoped PowerSeries.WithPiTopology

/-! ### The switch retractions from Milne -/

section Switch

attribute [local instance] TopRep.distribMulAction TopRep.smulCommClass

variable (K : Type) [Field K] [NumberField K] (S₀ S : Set (HeightOneSpectrum (𝓞 K)))
  (k : Type) [CommRing k] [TopologicalSpace k]
  (M : Type) [AddCommGroup M] [Module k M] [DistribMulAction (GKS K S) M]
  [SMulCommClass (GKS K S) k M] [TopologicalSpace M] [DiscreteTopology M]
  [ContinuousSMul (GKS K S) M]
  (Δ : LocalConditions k (GKS K S) (fun v : Places K S₀ => Gloc K v.1)
    (fun v => locMap K S v.1) M)
  {ι : Type} [DecidableEq ι] (place : ι × Bool → Places K S)
  (X : (j : ι × Bool) → TopRep.{0} k (GUr K (place j).1))
  (EU : ∀ j, SplitInclusion (genuineUq K S k (place j) (X j)) (genuineLq K S k M (place j)))
  [DecidableEq (Places K S₀)]

/-- **The retraction of the quotient of a switch, from the literature** (tex 4176–4184,
4385–4451): lane RC32's `exists_suppSwitchRetractS` with `TameCochainQuasiIso` replaced by the
PRINT `MilneADT_I_2_8` (`exists_retract_twoPlaces_place_stage_milne`). Kind: PROVED. -/
theorem exists_suppSwitchRetractS_milne (h28 : MilneADT_I_2_8) (hI : IwasawaGenerators)
    (hInj : GenuineCochainsInjective) [IsNoetherianRing k] [Module.Injective k k]
    [Module.Free k M] [Finite M] (hexp : ∃ n : ℕ, ∀ m : M, (2 ^ n) • m = 0) (T : Finset ι)
    (p : ι) (hp : p ∉ T) (q : ℕ) (hq : Odd q) (Fr : Matrix (Fin 2) (Fin 2) k) (z zi : k)
    [∀ j, ContinuousSMul (GUr K (place j).1) (X j).V] [∀ j, DiscreteTopology (X j).V]
    [∀ j, Finite (X j).V] (f : ∀ j, (X j).V →ₗ[k] M)
    (hf : ∀ j (g : Gloc K (place j).1) (x : (X j).V),
      f j (resUr K (place j).1 g • x) = locMap K S (place j).1 g • f j x)
    (hbij : ∀ j, Function.Bijective (f j))
    (hqc : ∀ c : Bool, q = Nat.card (𝓞 K ⧸ (place (p, c)).1.asIdeal))
    (hE : ∀ j, (EU j).i = ofCCHom (urToLocal_galois K S (place j) (X j) (f j) (hf j)))
    (b₁ : (X (p, false)).V ≃ₗ[k] (Fin 2 → k))
    (hb₁ : ∀ v, b₁ (frob (eUr K (place (p, false)).1) (X (p, false)) v) =
      Matrix.toLin' (z • Fr) (b₁ v))
    (b₂ : (X (p, true)).V ≃ₗ[k] (Fin 2 → k))
    (hb₂ : ∀ v, b₂ (frob (eUr K (place (p, true)).1) (X (p, true)) v) =
      Matrix.toLin' (zi • Fr) (b₂ v)) :
    Nonempty (GRetract (suppSwitchS K S₀ S k M Δ place X EU T p).quotientCx
      (twoSingCx Fr q z zi)) := by
  obtain ⟨R⟩ := exists_retract_twoPlaces_place_stage_milne h28 hI hInj hexp q hq Fr z zi
    (place (p, false)) (X (p, false)) (f (p, false)) (hf (p, false)) (hbij (p, false))
    (hqc false) (EU (p, false)) (hE (p, false)) b₁ hb₁ (place (p, true)) (X (p, true))
    (f (p, true)) (hf (p, true)) (hbij (p, true)) (hqc true) (EU (p, true)) (hE (p, true))
    b₂ hb₂
  exact ⟨suppSwitchRetractS K S₀ S k M Δ place X EU T p hp R⟩

end Switch

/-! ### The genuine stage chains with the literature retractions -/

section Genuine

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

/-- **The genuine stage chain with the literature retractions** (tex 4142–4194, 4176–4184,
4385–4451): `GenuineStageSteps.toChain` with the retractions of `exists_suppSwitchRetractS_milne`
(`MilneADT_I_2_8`, `IwasawaGenerators`, `GenuineCochainsInjective`). Kind: definition. -/
def GenuineStageSteps.toChainM (h28 : MilneADT_I_2_8) (hI : IwasawaGenerators)
    (hInj : GenuineCochainsInjective) {s m0 m1 m2 : ℕ} {pidx : ℕ → ι} {n : ℕ}
    (G : GenuineStageSteps K S₀ S M Δ place X EU s m0 m1 m2 pidx n) :
    CMChainData (genCx K S₀ S M Δ place X EU s) (genSw K S₀ S M Δ place X EU s) m0 m1 m2 pidx n
    where
  st0 := G.st0
  Fr := G.Fr
  q := G.q
  z := G.z
  zi := G.zi
  RQ i h := Classical.choice (exists_suppSwitchRetractS_milne K S₀ S (StageRing s) (M s) (Δ s)
    place (X s) (EU s) h28 hI hInj G.hexp (chainT pidx i) (pidx i) (G.hnew i h) (G.q i)
    (G.hqodd i h) (G.Fr i) (G.z i) (G.zi i) G.f G.hf G.hbij (G.hqc i h) G.hE (G.b₁ i)
    (G.hb₁ i h) (G.b₂ i) (G.hb₂ i h))
  zR := G.zR
  hzR := G.hzR
  lamR := G.lamR
  hlamR := G.hlamR

variable {ℓ : ℕ} [(Ecurve ℓ).IsElliptic]

variable (K S₀ S M Δ place X EU) in
/-- **The genuine stage chains of the leaf from the literature** (tex 4142–4194, 4385–4451): as
`GenuineStageSTU`, with the retractions of the switch quotients from `MilneADT_I_2_8`,
`IwasawaGenerators` and `GenuineCochainsInjective` (no `TameCochainQuasiIso`).
Kind: definition (data). -/
structure GenuineStageSTUM (h28 : MilneADT_I_2_8) (hI : IwasawaGenerators)
    (hInj : GenuineCochainsInjective) (C : TateCoef (Ecurve ℓ)) (D : RCData ℓ) (Fam : Family)
    (x : Addr Fam.b) (pidx : ℕ → ι) : Type where
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
  /-- the ultrafilter on the coefficient stages (definition; tex 4401–4406) -/
  U : Ultrafilter ℕ
  /-- it is nonprincipal (definition; tex 4401–4406) -/
  hU : (U : Filter ℕ) ≤ cofinite
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
  /-- the boundaries of the norm identities (GLUE: lane E2's retained boundaries;
  tex 4169–4171) -/
  bw : ∀ s i, (genCx K S₀ S M Δ place X EU s (insert (pidx i) (chainT pidx i))).X 0
  /-- the coboundaries of the functional relations (GLUE: lane RC30's retention with
  self-injectivity; tex 4171–4172) -/
  μ : ∀ s i, (genCx K S₀ S M Δ place X EU s (chainT pidx i)).X 3 →ₗ[StageRing s] StageRing s
  /-- the step inputs at the retained stages: the norm identity and the functional relation on
  the genuine complexes (GLUE: `exists_stepHyps_of_E2_RC30`; tex 4169–4172) -/
  hstep : ∀ s (h : s ∈ G), CMStepHyps ((gs s h).toChainM h28 hI hInj) (a s) (bw s) (μ s)
  /-- the leaf's Frobenius data at the retained stages (GLUE: the Frobenius identifications;
  tex 4144–4145, 4176–4184) -/
  hfrob : ∀ s (h : s ∈ G),
    StageFrobAt (leafFrobΛ C Fam x ps) s ((gs s h).toChainM h28 hI hInj) (a s)
  /-- the primitive coordinate of the limit has `t`-expansion `u_{prim,x}` (definition of
  `u_{prim,x}`; tex 4153, 4185–4193) -/
  hprim : IsTExpansion
    ((fracChain (stageMatsOn G (fun s h => (gs s h).toChainM h28 hI hInj) bw μ) U).chainV
      (fracChain_holds _ hU _ _ (stageMatsOn_hs G _ bw μ _ U a hG hstep hfrob)) 0)
    (D.uPrim Fam x)
  /-- the corrected coordinate of the limit at `U_x` has `t`-expansion `ũ_x` (definition of
  `ũ_x`; tex 4150–4151, 4185–4193) -/
  htilde : IsTExpansion (etaF ℓ Fam x *
    (fracChain (stageMatsOn G (fun s h => (gs s h).toChainM h28 hI hInj) bw μ) U).chainV
      (fracChain_holds _ hU _ _ (stageMatsOn_hs G _ bw μ _ U a hG hstep hfrob)) ps.length)
    (D.uTilde Fam x)

/-- **The inner-limit data of the leaf from the genuine stage chains and the literature**
(tex 4142–4194, 4385–4451): `CommonCoordinateLimitST`. Kind: definition. -/
def GenuineStageSTUM.toLimitST {h28 : MilneADT_I_2_8} {hI : IwasawaGenerators}
    {hInj : GenuineCochainsInjective} {C : TateCoef (Ecurve ℓ)} {D : RCData ℓ} {Fam : Family}
    {x : Addr Fam.b} {pidx : ℕ → ι}
    (Gs : GenuineStageSTUM K S₀ S M Δ place X EU h28 hI hInj C D Fam x pidx) :
    CommonCoordinateLimitST C D Fam x where
  hprime := Gs.hprime
  hgood := Gs.hgood
  ps := Gs.ps
  hnd := Gs.hnd
  hps := Gs.hps
  f := leafFrobΛ C Fam x Gs.ps
  hf := leafFrob_leafFrobΛ C Fam x Gs.hprime Gs.hps
  U := Gs.U
  hU := Gs.hU
  m0 := Gs.m0
  m1 := Gs.m1
  m2 := Gs.m2
  c := stageMatsOn Gs.G (fun s h => (Gs.gs s h).toChainM h28 hI hInj) Gs.bw Gs.μ
  hs := stageMatsOn_hs Gs.G _ Gs.bw Gs.μ _ Gs.U Gs.a Gs.hG Gs.hstep Gs.hfrob
  hprim := Gs.hprim
  htilde := Gs.htilde

end Genuine

end ZInQ.Manuscript.RC.Wiring
