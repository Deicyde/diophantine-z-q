import ZInQKernel.Contrib.OneProof.RC.Wiring.CommonCoordinate16Model

/-!
# The genuine stage chains on a set of stages; the end identifications

Manuscript `diophantine_zq.tex`, Lemma `ex:arith-common-coordinate` (tex 4142–4194, 4185–4193)
through the inner limit of Lemma `ex:limits-inner-limit` (tex 4385–4451).

The models of `C_∅` exist at the stages where the residual ranks have the fixed shape
(`exists_genuine_st0`, `exists_shape_fixed`): a `U`-large set of stages, not all of them. The
leaf data are therefore needed on a `U`-large set only:

* `ChainMat.zeroMat`; `stageMatsOn`, **`stageMatsOn_hs`**: the lifted matrix data of stage chains
  given on a set `G` of stages (zero elsewhere), with their identities at `U`-many stages when `G`
  is `U`-large.
* **`GenuineStageSTU`**, **`GenuineStageSTU.toLimitST`**: the genuine stage chains of the leaf
  on a `U`-large set of stages (their initial states from `exists_genuine_st0`, their retractions
  of the switch quotients from the tame inputs) give `CommonCoordinateLimitST`, hence the current
  leaf.

**The end identifications** (tex 4185–4193): the text's coordinate `u_T` is taken in the
retained integral basis (tex 3886–3888); here it is normalized to the iterated cone basis of
`C_T`, which the text replaces by the retained models at the cost of a sign and unit-disk
determinants (tex 4189–4193); the coordinate is the Knudsen–Mumford coordinate of the class and
functional of `C_T` in that basis. The leaf asks `u_∅ = u_prim` and `η u_{U_x} = ũ`. On the limit
chain over `Frac Λ`:

* `fracChain_v_zero`: the first value `v₀` is the coordinate `vPrim 0` of the model of `C_∅` at the
  limit primitive class and functional;
* `fracChain_v_end`: the last value is `v_n = σ_n · vPrim n`, the coordinate of the model of
  `C_{U_x}` (the iterated cone) at the last relaxed class and functional, times the sign `σ_n`;
  `σ = 1` identically (`chainSign_eq_one`); the orientations are compatible by construction;
* **`hprim_htilde_iff_ends`**: the leaf's `hprim` and `htilde` are exactly
  `IsTExpansion (vPrim 0) u_prim` and `IsTExpansion (η σ_n vPrim n) ũ` (`LeafEnds`).

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

/-! ### Stage data on a set of stages -/

/-- **The zero matrix data** (tex 4385–4451: the data at the stages outside the retained set).
Kind: definition. -/
def ChainMat.zeroMat (R : Type) [CommRing R] (m0 m1 m2 : ℕ) : ChainMat R m0 m1 m2 where
  d0 := 0
  d1 := 0
  d2 := 0
  Q _ := 0
  V _ := 0
  B _ := 0
  zP0 := 0
  lP0 := 0
  z _ := 0
  l _ := 0
  w _ := 0
  ν _ := 0

section StagesOn

variable {ι : Type} [DecidableEq ι] {Cx : ∀ s, Finset ι → GCx (StageRing s)}
  {Ex : ∀ s (T : Finset ι) (p : ι), SplitInclusion (Cx s T) (Cx s (insert p T))}
  {m0 m1 m2 : ℕ} {pidx : ℕ → ι} {n : ℕ}

open scoped Classical in
/-- **The lifted matrix data of stage chains on a set of stages** (tex 4385–4451): at a stage of
`G` the lifted data of the chain, zero elsewhere. Kind: definition. -/
def stageMatsOn (G : Set ℕ) (cd : ∀ s, s ∈ G → CMChainData (Cx s) (Ex s) m0 m1 m2 pidx n)
    (bw : ∀ s i, (Cx s (insert (pidx i) (chainT pidx i))).X 0)
    (μ : ∀ s i, (Cx s (chainT pidx i)).X 3 →ₗ[StageRing s] StageRing s) :
    ℕ → ChainMat LamI m0 m1 m2 :=
  fun s => if h : s ∈ G then stageLift s ((cd s h).toChainMat (bw s) (μ s))
    else ChainMat.zeroMat LamI m0 m1 m2

/-- **Their identities at `U`-many stages** (tex 4385–4451): when `G` is `U`-large, with the step
inputs and the leaf's Frobenius data on `G`. Kind: PROVED. -/
theorem stageMatsOn_hs (G : Set ℕ) (cd : ∀ s, s ∈ G → CMChainData (Cx s) (Ex s) m0 m1 m2 pidx n)
    (bw : ∀ s i, (Cx s (insert (pidx i) (chainT pidx i))).X 0)
    (μ : ∀ s i, (Cx s (chainT pidx i)).X 3 →ₗ[StageRing s] StageRing s) (f : FrobSeq LamI)
    (U : Ultrafilter ℕ) (a : ∀ s, ℕ → StageRing s) (hG : ∀ᶠ s in (U : Filter ℕ), s ∈ G)
    (hstep : ∀ s (h : s ∈ G), CMStepHyps (cd s h) (a s) (bw s) (μ s))
    (hfrob : ∀ s (h : s ∈ G), StageFrobAt f s (cd s h) (a s)) :
    ∀ᶠ s in (U : Filter ℕ), (stageMatsOn G cd bw μ s).Holds (stageIdeal s) f n := by
  filter_upwards [hG] with s hs
  have e : stageMatsOn G cd bw μ s = stageLift s ((cd s hs).toChainMat (bw s) (μ s)) :=
    dite_eq_left hs
  rw [e]
  have h2 := hfrob s hs
  exact stageLift_holds s _ f n (toChainMat_holds (cd s hs) (bw s) (μ s) (a s) (hstep s hs) _
    (fun i hi => (h2 i hi).1) (fun i hi => (h2 i hi).2.1) (fun i hi => (h2 i hi).2.2.1)
    (fun i hi => (h2 i hi).2.2.2.1) (fun i hi => (h2 i hi).2.2.2.2))

end StagesOn

/-! ### The genuine stage chains on a `U`-large set of stages -/

section GenuineU

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
/-- **The genuine stage chains of the leaf on a `U`-large set of stages** (tex 4142–4194,
4385–4451): as `GenuineStageST`, with the genuine data of the chain given at the stages of a
`U`-large set `G` (the stages where the initial state exists: `exists_genuine_st0`, with the shape
fixed by `exists_shape_fixed`), and the step inputs and the leaf's Frobenius data on `G`.
Kind: definition (data). -/
structure GenuineStageSTU (hT : TameCochainQuasiIso) (hI : IwasawaGenerators)
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
  /-- the retained stages -/
  G : Set ℕ
  /-- they are `U`-many -/
  hG : ∀ᶠ s in (U : Filter ℕ), s ∈ G
  /-- the genuine data of the chain at the retained stages -/
  gs : ∀ s, s ∈ G → GenuineStageSteps K S₀ S M Δ place X EU s m0 m1 m2 pidx ps.length
  /-- the traces at the stages -/
  a : ∀ s, ℕ → StageRing s
  /-- the boundaries of the norm identities -/
  bw : ∀ s i, (genCx K S₀ S M Δ place X EU s (insert (pidx i) (chainT pidx i))).X 0
  /-- the coboundaries of the functional relations -/
  μ : ∀ s i, (genCx K S₀ S M Δ place X EU s (chainT pidx i)).X 3 →ₗ[StageRing s] StageRing s
  /-- the step inputs at the retained stages -/
  hstep : ∀ s (h : s ∈ G), CMStepHyps ((gs s h).toChain hT hI hInj) (a s) (bw s) (μ s)
  /-- the leaf's Frobenius data at the retained stages -/
  hfrob : ∀ s (h : s ∈ G),
    StageFrobAt (leafFrobΛ C Fam x ps) s ((gs s h).toChain hT hI hInj) (a s)
  /-- the primitive coordinate of the limit has `t`-expansion `u_{prim,x}` (tex 4153) -/
  hprim : IsTExpansion
    ((fracChain (stageMatsOn G (fun s h => (gs s h).toChain hT hI hInj) bw μ) U).chainV
      (fracChain_holds _ hU _ _ (stageMatsOn_hs G _ bw μ _ U a hG hstep hfrob)) 0)
    (D.uPrim Fam x)
  /-- the corrected coordinate of the limit at `U_x` has `t`-expansion `ũ_x` (tex 4150–4151).
  Conclusion-shaped: since `chainSign = 1` and each step has `ε = q⁻⁴`,
  `η_x v_n = (∏_{q∈U_x} q⁻⁴) v₀`, so given `hprim` this field is equivalent to
  `ũ_x = (∏_{q∈U_x} q⁻⁴) u_{prim,x}`, the conclusion of Lemma `ex:arith-common-coordinate` with
  the unit pinned (stronger than the text's `ε_x ∈ Λ^×`, whose unit-disk factors, tex 4189–4193,
  are absorbed into the choice of the model and class of `C_∅`). The text's `ũ = η u_rel` is one
  common family (tex 4224–4225); that is not represented. -/
  htilde : IsTExpansion (etaF ℓ Fam x *
    (fracChain (stageMatsOn G (fun s h => (gs s h).toChain hT hI hInj) bw μ) U).chainV
      (fracChain_holds _ hU _ _ (stageMatsOn_hs G _ bw μ _ U a hG hstep hfrob)) ps.length)
    (D.uTilde Fam x)

/-- **The inner-limit data of the leaf from the genuine stage chains on a `U`-large set of
stages** (tex 4142–4194, 4385–4451): `CommonCoordinateLimitST`, hence (with
`commonCoordinateTarget_of_limit`) the current leaf and (4.7). Kind: definition. -/
def GenuineStageSTU.toLimitST {hT : TameCochainQuasiIso} {hI : IwasawaGenerators}
    {hInj : GenuineCochainsInjective} {C : TateCoef (Ecurve ℓ)} {D : RCData ℓ} {Fam : Family}
    {x : Addr Fam.b} {pidx : ℕ → ι}
    (Gs : GenuineStageSTU K S₀ S M Δ place X EU hT hI hInj C D Fam x pidx) :
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
  c := stageMatsOn Gs.G (fun s h => (Gs.gs s h).toChain hT hI hInj) Gs.bw Gs.μ
  hs := stageMatsOn_hs Gs.G _ Gs.bw Gs.μ _ Gs.U Gs.a Gs.hG Gs.hstep Gs.hfrob
  hprim := Gs.hprim
  htilde := Gs.htilde

end GenuineU

/-! ### The end identifications -/

section Ends

variable {m0 m1 m2 : ℕ} (c : ℕ → ChainMat LamI m0 m1 m2) {U : Ultrafilter ℕ}
  (hU : (U : Filter ℕ) ≤ cofinite) (f : FrobSeq LamI) (n : ℕ)
  (hs : ∀ᶠ s in (U : Filter ℕ), (c s).Holds (stageIdeal s) f n)

/-- **The first value is the coordinate of `C_∅`** (tex 4185–4193): on the limit chain over
`Frac Λ`, `v₀` is the Knudsen–Mumford coordinate of the model of `C_∅` at the limit primitive
class and functional. Kind: PROVED (definitional). -/
theorem fracChain_v_zero :
    (fracChain c U).chainV (fracChain_holds c hU f n hs) 0 =
      (fracChain c U).vPrim (fracChain_holds c hU f n hs) 0 (Nat.zero_le n) :=
  rfl

/-- **The last value is the signed coordinate of `C_{U_x}`** (tex 4185–4193): `v_n = σ_n vPrim n`,
the coordinate of the iterated cone model of the full support at the last relaxed class and
functional, times the sign `σ_n`; `σ = 1` identically (`chainSign_eq_one`); the orientations are
compatible by construction. Kind: PROVED. -/
theorem fracChain_v_end :
    (fracChain c U).chainV (fracChain_holds c hU f n hs) n =
      ((chainSign m0 m1 m2 n : ℤ) : FracLam) *
        (fracChain c U).vPrim (fracChain_holds c hU f n hs) n le_rfl := by
  rw [(fracChain c U).vPrim_eq_chainV (fracChain_holds c hU f n hs) n le_rfl, ← mul_assoc,
    ← Int.cast_mul, ← Units.val_mul, Int.units_mul_self, Units.val_one, Int.cast_one, one_mul]

/-- **The end identifications of the leaf** (tex 4150–4153, 4185–4193): the coordinate of `C_∅`
at the primitive data has `t`-expansion `u_prim`, and `η` times the signed coordinate of
`C_{U_x}` at the last relaxed data has `t`-expansion `ũ`. Kind: definition. -/
def LeafEnds (η uP uT : FracLam) (hasExp : FracLam → FracLam → Prop) : Prop :=
  hasExp ((fracChain c U).vPrim (fracChain_holds c hU f n hs) 0 (Nat.zero_le n)) uP ∧
    hasExp (η * (((chainSign m0 m1 m2 n : ℤ) : FracLam) *
      (fracChain c U).vPrim (fracChain_holds c hU f n hs) n le_rfl)) uT

/-- **The leaf's end conditions are the end identifications** (tex 4150–4153, 4185–4193): the
fields `hprim`, `htilde` of `CommonCoordinateLimitST` hold exactly when the coordinate of `C_∅`
and the signed coordinate of `C_{U_x}` have the text's expansions. Kind: PROVED. -/
theorem hprim_htilde_iff_ends (η uP uT : FracLam) (hasExp : FracLam → FracLam → Prop) :
    (hasExp ((fracChain c U).chainV (fracChain_holds c hU f n hs) 0) uP ∧
      hasExp (η * (fracChain c U).chainV (fracChain_holds c hU f n hs) n) uT) ↔
      LeafEnds c hU f n hs η uP uT hasExp := by
  unfold LeafEnds
  rw [fracChain_v_zero c hU f n hs, fracChain_v_end c hU f n hs]

end Ends

end ZInQ.Manuscript.RC.Wiring
