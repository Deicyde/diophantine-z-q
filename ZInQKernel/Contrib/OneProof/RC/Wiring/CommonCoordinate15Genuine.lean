import ZInQKernel.Contrib.OneProof.RC.Wiring.CommonCoordinate15Leaf

/-!
# The genuine stage chains of the leaf

Manuscript `diophantine_zq.tex`, Lemma `ex:arith-common-coordinate` (tex 4142–4194) on the genuine
support complexes of the one presentation (tex 3470–3498, 4142–4194) at the coefficient stages
`A_s = Λ ⧸ (2^s, t^s)` of the inner limit (tex 4385–4451).

* `genCx`, `genSw`: the genuine support complexes `C_T` and switches `C_T ⊂ C_{T ∪ {p}}` of the one
  presentation at the stage `A_s` (`suppCxS`, `suppSwitchS`; the splits `EU` of the genuine
  inflations exist over the self-injective stage rings, `exists_genuineSplitsS`).
* `GenuineStageSteps`: the genuine data of one chain at one stage — the model of `C_∅` with the
  primitive class and functional, the Frobenius data of the steps, the relaxed classes and
  functionals, and the tame inputs of the steps (the equivariant identifications `f`, the residue
  cardinalities, the Frobenius bases of the two places).
* **`GenuineStageSteps.toChain`**: the stage chain, with the retractions of the quotients of the
  switches onto the two singular blocks PROVED from `TameCochainQuasiIso`, `IwasawaGenerators`
  and `GenuineCochainsInjective` (`exists_suppSwitchRetractS`).
* **`GenuineStageST`**, `GenuineStageST.toStageChains`, **`GenuineStageST.toLimitST`**: the
  genuine stage chains of the leaf, with the step inputs (the norm identity with its boundary and
  the functional relation up to a coboundary), the leaf's Frobenius data at `U`-many stages and the
  end expansions of the limit, give round ten's `CommonCoordinateLimitST`, hence the current leaf.

Kinds: definitions and PROVED.
-/

noncomputable section

namespace ZInQ.Manuscript.RC.Wiring

open NumberField IsDedekindDomain
open Matrix Filter ZInQ.Manuscript ZInQ.Manuscript.RC ZInQ.Manuscript.RC.Central
  ZInQ.Manuscript.RC.Uniform ZInQ.Contrib.CloudB3RC53 ZInQ.Contrib.CloudB3RC53.CommonCoordinate
open ZInQ.Manuscript.RC.Limits (stageIdeal SplitInclusion)
open ZInQ.Contrib.CloudB3RC53.PairedFunctional
open ZInQ.Manuscript.RC.SelmerComplex ZInQ.Contrib.CloudB3RC53.UnramifiedComplex
  ZInQ.Contrib.CloudB3RC53.RankCounts
open ZInQ.Manuscript.RC.Local (twoSingCx IwasawaGenerators TameCochainQuasiIso
  GenuineCochainsInjective)
open scoped PowerSeries.WithPiTopology

section Genuine

attribute [local instance] TopRep.distribMulAction TopRep.smulCommClass

variable (K : Type) [Field K] [NumberField K] (S₀ S : Set (HeightOneSpectrum (𝓞 K)))
  [DecidableEq (Places K S₀)] [∀ s, TopologicalSpace (StageRing s)]
  (M : ℕ → Type) [∀ s, AddCommGroup (M s)] [∀ s, Module (StageRing s) (M s)]
  [∀ s, DistribMulAction (GKS K S) (M s)] [∀ s, SMulCommClass (GKS K S) (StageRing s) (M s)]
  [∀ s, TopologicalSpace (M s)] [∀ s, DiscreteTopology (M s)]
  [∀ s, ContinuousSMul (GKS K S) (M s)]
  (Δ : ∀ s, LocalConditions (StageRing s) (GKS K S) (fun v : Places K S₀ => Gloc K v.1)
    (fun v => locMap K S v.1) (M s))
  {ι : Type} [DecidableEq ι] (place : ι × Bool → Places K S)
  (X : ∀ s, (j : ι × Bool) → TopRep.{0} (StageRing s) (GUr K (place j).1))
  (EU : ∀ s j, SplitInclusion (genuineUq K S (StageRing s) (place j) (X s j))
    (genuineLq K S (StageRing s) (M s) (place j)))

variable [∀ s, Module.Free (StageRing s) (M s)] [∀ s, Finite (M s)]
  [∀ s j, ContinuousSMul (GUr K (place j).1) (X s j).V] [∀ s j, DiscreteTopology (X s j).V]
  [∀ s j, Finite (X s j).V]

/-- **The genuine support complexes at the stage `A_s`** (tex 3470–3498, 4142–4194, 4385–4451).
Kind: definition. -/
abbrev genCx (s : ℕ) : Finset ι → GCx (StageRing s) :=
  suppCxS K S₀ S (StageRing s) (M s) (Δ s) place (X s) (EU s)

/-- **The genuine switches at the stage `A_s`** (tex 4142–4194, 4385–4451). Kind: definition. -/
abbrev genSw (s : ℕ) (T : Finset ι) (p : ι) :
    SplitInclusion (genCx K S₀ S M Δ place X EU s T) (genCx K S₀ S M Δ place X EU s (insert p T)) :=
  suppSwitchS K S₀ S (StageRing s) (M s) (Δ s) place (X s) (EU s) T p

/-- **The genuine data of one chain at one stage** (tex 4142–4194, 4176–4184, 4385–4451): the
chain relaxes the indices `pidx 0, …, pidx (n−1)` (each new); the model of `C_∅` of ranks
`(m₀, m₁, m₂)` with the primitive class and functional; the Frobenius data and the relaxed classes
and functionals of the steps; and the tame inputs: the equivariant identifications `f` of the
unramified representations with `M`, the splits `EU` being the genuine inflations, `M` of
`2`-power exponent, the odd residue cardinalities of the two places of each step, and the bases of
the two places in which the Frobenius is `z F` and `z⁻¹ F`. Kind: definition (data). -/
structure GenuineStageSteps (s m0 m1 m2 : ℕ) (pidx : ℕ → ι) (n : ℕ) : Type where
  /-- each relaxed index is new -/
  hnew : ∀ i < n, pidx i ∉ chainT pidx i
  /-- the state at the empty support: the model of `C_∅`, the primitive class and functional -/
  st0 : CMState m0 m1 m2 (genCx K S₀ S M Δ place X EU s ∅) 0
  /-- the Frobenius matrices of the steps -/
  Fr : ℕ → Matrix (Fin 2) (Fin 2) (StageRing s)
  /-- the residue cardinalities of the steps -/
  q : ℕ → ℕ
  /-- the points of the steps -/
  z : ℕ → StageRing s
  /-- the inverse points of the steps -/
  zi : ℕ → StageRing s
  /-- the relaxed classes -/
  zR : ∀ i, (genCx K S₀ S M Δ place X EU s (insert (pidx i) (chainT pidx i))).X 1
  /-- they are cycles -/
  hzR : ∀ i, (genCx K S₀ S M Δ place X EU s (insert (pidx i) (chainT pidx i))).d 1 2 rfl
    (zR i) = 0
  /-- the relaxed functionals -/
  lamR : ∀ i, (genCx K S₀ S M Δ place X EU s (insert (pidx i) (chainT pidx i))).X 2 →ₗ[StageRing s]
    StageRing s
  /-- they are closed -/
  hlamR : ∀ i, lamR i ∘ₗ
    (genCx K S₀ S M Δ place X EU s (insert (pidx i) (chainT pidx i))).d 1 2 rfl = 0
  /-- the equivariant identifications of the unramified representations -/
  f : ∀ j, (X s j).V →ₗ[StageRing s] M s
  /-- their equivariance -/
  hf : ∀ j (g : Gloc K (place j).1) (v : (X s j).V),
    f j (resUr K (place j).1 g • v) = locMap K S (place j).1 g • f j v
  /-- they are bijective -/
  hbij : ∀ j, Function.Bijective (f j)
  /-- the splits are the genuine inflations -/
  hE : ∀ j, (EU s j).i = ofCCHom (urToLocal_galois K S (place j) (X s j) (f j) (hf j))
  /-- `M` has `2`-power exponent -/
  hexp : ∃ e : ℕ, ∀ m : M s, (2 ^ e) • m = 0
  /-- the residue cardinalities are odd -/
  hqodd : ∀ i < n, Odd (q i)
  /-- they are the residue cardinalities of the two places -/
  hqc : ∀ i < n, ∀ c : Bool, q i = Nat.card (𝓞 K ⧸ (place (pidx i, c)).1.asIdeal)
  /-- the basis at the first place -/
  b₁ : ∀ i, (X s (pidx i, false)).V ≃ₗ[StageRing s] (Fin 2 → StageRing s)
  /-- the Frobenius is `z F` at the first place -/
  hb₁ : ∀ i < n, ∀ v, b₁ i (frob (eUr K (place (pidx i, false)).1) (X s (pidx i, false)) v) =
    Matrix.toLin' (z i • Fr i) (b₁ i v)
  /-- the basis at the second place -/
  b₂ : ∀ i, (X s (pidx i, true)).V ≃ₗ[StageRing s] (Fin 2 → StageRing s)
  /-- the Frobenius is `z⁻¹ F` at the second place -/
  hb₂ : ∀ i < n, ∀ v, b₂ i (frob (eUr K (place (pidx i, true)).1) (X s (pidx i, true)) v) =
    Matrix.toLin' (zi i • Fr i) (b₂ i v)

variable {K S₀ S M Δ place X EU}

/-- **The genuine stage chain** (tex 4142–4194, 4176–4184, 4385–4451): the retraction of the
quotient of each switch onto the two singular blocks is lane RC31's stage retraction
(`exists_suppSwitchRetractS`: `TameCochainQuasiIso`, `IwasawaGenerators`,
`GenuineCochainsInjective`, the stage ring Noetherian and self-injective). Kind: definition. -/
def GenuineStageSteps.toChain (hT : TameCochainQuasiIso) (hI : IwasawaGenerators)
    (hInj : GenuineCochainsInjective) {s m0 m1 m2 : ℕ} {pidx : ℕ → ι} {n : ℕ}
    (G : GenuineStageSteps K S₀ S M Δ place X EU s m0 m1 m2 pidx n) :
    CMChainData (genCx K S₀ S M Δ place X EU s) (genSw K S₀ S M Δ place X EU s) m0 m1 m2 pidx n
    where
  st0 := G.st0
  Fr := G.Fr
  q := G.q
  z := G.z
  zi := G.zi
  RQ i h := Classical.choice (exists_suppSwitchRetractS K S₀ S (StageRing s) (M s) (Δ s) place
    (X s) (EU s) hT hI hInj G.hexp (chainT pidx i) (pidx i) (G.hnew i h) (G.q i) (G.hqodd i h)
    (G.Fr i) (G.z i) (G.zi i) G.f G.hf G.hbij (G.hqc i h) G.hE (G.b₁ i) (G.hb₁ i h) (G.b₂ i)
    (G.hb₂ i h))
  zR := G.zR
  hzR := G.hzR
  lamR := G.lamR
  hlamR := G.hlamR

variable {ℓ : ℕ} [(Ecurve ℓ).IsElliptic]

variable (K S₀ S M Δ place X EU) in
/-- **The genuine stage chains of the leaf** (tex 4142–4194, 4385–4451): the graph primes are
good odd primes; an order `ps` of the unused primes, relaxed along the indices `pidx`; a
nonprincipal ultrafilter on the stages; the ranks of the models of `C_∅`; the genuine data of the
chain at every stage; the boundaries, coboundaries and traces; at `U`-many stages the step inputs
(the norm identity with its boundary — lane E2's stage norm identity, `hzR_stage_of_E2`, after
the adapter to the presentation — and the functional relation up to a coboundary —
`exists_cob_of_natural_stage` from lane RC30's naturality) and the leaf's Frobenius data; and the
primitive and corrected expansions of the end coordinates of the limit chain.
Kind: definition (data). -/
structure GenuineStageST (hT : TameCochainQuasiIso) (hI : IwasawaGenerators)
    (hInj : GenuineCochainsInjective) (C : TateCoef (Ecurve ℓ)) (D : RCData ℓ) (Fam : Family)
    (x : Addr Fam.b) (pidx : ℕ → ι) : Type where
  /-- the graph primes are odd primes (tex 2678–2680, 4143) -/
  hprime : ∀ q ∈ Fam.Q, q.Prime ∧ q ≠ 2
  /-- the graph primes are primes of good reduction (tex 4143) -/
  hgood : ∀ q ∈ Fam.Q, Nonvanishing.GoodAt (Ecurve ℓ) q
  /-- the order in which the unused primes are relaxed -/
  ps : List ℕ
  /-- each unused prime is relaxed once -/
  hnd : ps.Nodup
  /-- the chain relaxes exactly the unused primes -/
  hps : ps.toFinset = unusedAt Fam x
  /-- the ultrafilter on the coefficient stages -/
  U : Ultrafilter ℕ
  /-- it is nonprincipal -/
  hU : (U : Filter ℕ) ≤ cofinite
  /-- the rank of the model of `C_∅` in degree `0` -/
  m0 : ℕ
  /-- the rank of the model of `C_∅` in degree `1` (besides the class) -/
  m1 : ℕ
  /-- the rank of the model of `C_∅` in degree `3` -/
  m2 : ℕ
  /-- the genuine data of the chain at every stage -/
  gs : ∀ s, GenuineStageSteps K S₀ S M Δ place X EU s m0 m1 m2 pidx ps.length
  /-- the traces at the stages -/
  a : ∀ s, ℕ → StageRing s
  /-- the boundaries of the norm identities -/
  bw : ∀ s i, (genCx K S₀ S M Δ place X EU s (insert (pidx i) (chainT pidx i))).X 0
  /-- the coboundaries of the functional relations -/
  μ : ∀ s i, (genCx K S₀ S M Δ place X EU s (chainT pidx i)).X 3 →ₗ[StageRing s] StageRing s
  /-- the step inputs at `U`-many stages -/
  hstep : ∀ᶠ s in (U : Filter ℕ), CMStepHyps ((gs s).toChain hT hI hInj) (a s) (bw s) (μ s)
  /-- the leaf's Frobenius data at `U`-many stages -/
  hfrob : ∀ᶠ s in (U : Filter ℕ),
    StageFrobAt (leafFrobΛ C Fam x ps) s ((gs s).toChain hT hI hInj) (a s)
  /-- the primitive coordinate of the limit has `t`-expansion `u_{prim,x}` (tex 4153) -/
  hprim : IsTExpansion ((fracChain (stageMats (fun s => (gs s).toChain hT hI hInj) bw μ) U).chainV
    (fracChain_holds _ hU _ _ (stageMats_hs _ bw μ _ U a hstep hfrob)) 0) (D.uPrim Fam x)
  /-- the corrected coordinate of the limit at `U_x` has `t`-expansion `ũ_x` (tex 4150–4151).
  Conclusion-shaped: since `chainSign = 1` and each step has `ε = q⁻⁴`,
  `η_x v_n = (∏_{q∈U_x} q⁻⁴) v₀`, so given `hprim` this field is equivalent to
  `ũ_x = (∏_{q∈U_x} q⁻⁴) u_{prim,x}`, the conclusion of Lemma `ex:arith-common-coordinate` with
  the unit pinned (stronger than the text's `ε_x ∈ Λ^×`, whose unit-disk factors, tex 4189–4193,
  are absorbed into the choice of the model and class of `C_∅`). The text's `ũ = η u_rel` is one
  common family (tex 4224–4225); that is not represented. -/
  htilde : IsTExpansion (etaF ℓ Fam x *
    (fracChain (stageMats (fun s => (gs s).toChain hT hI hInj) bw μ) U).chainV
      (fracChain_holds _ hU _ _ (stageMats_hs _ bw μ _ U a hstep hfrob)) ps.length)
    (D.uTilde Fam x)

/-- **The genuine stage chains as stage chains of the presentation** (tex 4142–4194,
4385–4451). Kind: definition. -/
def GenuineStageST.toStageChains {hT : TameCochainQuasiIso} {hI : IwasawaGenerators}
    {hInj : GenuineCochainsInjective} {C : TateCoef (Ecurve ℓ)} {D : RCData ℓ} {Fam : Family}
    {x : Addr Fam.b} {pidx : ℕ → ι}
    (G : GenuineStageST K S₀ S M Δ place X EU hT hI hInj C D Fam x pidx) :
    StageChainsST C D Fam x (genCx K S₀ S M Δ place X EU) (genSw K S₀ S M Δ place X EU) pidx where
  hprime := G.hprime
  hgood := G.hgood
  ps := G.ps
  hnd := G.hnd
  hps := G.hps
  U := G.U
  hU := G.hU
  m0 := G.m0
  m1 := G.m1
  m2 := G.m2
  cd s := (G.gs s).toChain hT hI hInj
  a := G.a
  bw := G.bw
  μ := G.μ
  hstep := G.hstep
  hfrob := G.hfrob
  hprim := G.hprim
  htilde := G.htilde

/-- **The inner-limit data of the leaf from the genuine stage chains** (tex 4142–4194,
4385–4451): `CommonCoordinateLimitST`, hence (with `commonCoordinateTarget_of_limit`) the current
leaf and (4.7). Kind: definition. -/
def GenuineStageST.toLimitST {hT : TameCochainQuasiIso} {hI : IwasawaGenerators}
    {hInj : GenuineCochainsInjective} {C : TateCoef (Ecurve ℓ)} {D : RCData ℓ} {Fam : Family}
    {x : Addr Fam.b} {pidx : ℕ → ι}
    (G : GenuineStageST K S₀ S M Δ place X EU hT hI hInj C D Fam x pidx) :
    CommonCoordinateLimitST C D Fam x :=
  G.toStageChains.toLimitST

end Genuine

end ZInQ.Manuscript.RC.Wiring
