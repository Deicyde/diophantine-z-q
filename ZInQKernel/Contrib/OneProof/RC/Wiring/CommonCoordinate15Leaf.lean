import ZInQKernel.Contrib.OneProof.RC.Wiring.CommonCoordinate15Holds
import ZInQKernel.Contrib.OneProof.RC.Wiring.CommonCoordinate15PresS
import ZInQKernel.Contrib.OneProof.RC.Wiring.CommonCoordinate15StageInputs

/-!
# The inner limit of the genuine stage chains: the common-coordinate leaf

Manuscript `diophantine_zq.tex`, Lemma `ex:arith-common-coordinate` (tex 4142–4194) in the
iterated mapping-cone bases (tex 4185–4193), through the inner limit of Lemma
`ex:limits-inner-limit` (tex 4385–4451).

At every coefficient stage `A_s = Λ ⧸ (2^s, t^s)` a chain of switches of a presentation of the
support complexes (`CMChainData`) gives matrix data satisfying all the identities exactly
(`toChainMat_holds`); their lifts to `Λ` satisfy them modulo the stage ideal (`stageLift_holds`),
which is the hypothesis of round ten's inner limit.

* `StageRing`, `stageMk`, `StageFrobAt`: the stage ring, the reduction, and the agreement of the
  Frobenius data of a stage chain with the leaf's at the stage.
* `stageMats`, **`stageMats_hs`**: the lifted matrix data of a family of stage chains, and their
  identities modulo the stage ideals at `U`-many stages.
* **`exists_stepHyps_of_natural`**: over a self-injective coefficient ring (the stage rings), the
  step inputs follow from the norm identity with its boundary and the naturality of the
  functionals on cocycles (lane RC30), the coboundaries `μ_i` being chosen.
* **`StageChainsST`**, **`StageChainsST.toLimitST`**: stage chains of any presentation, with the
  step inputs and the leaf's Frobenius data at `U`-many stages and the end expansions of the
  limit, give round ten's `CommonCoordinateLimitST`; `CommonCoordinateInputsStages`,
  **`commonCoordinateTarget_of_stages`**: hence (4.7).
* `genCx`, `genSw`: the genuine support complexes and switches of lane RC32's one presentation at
  the stage rings (`suppCxS`, `suppSwitchS`).
* **`GenuineStageST`**, **`GenuineStageST.toLimitST`**: the genuine stage chains, with the
  retractions of the quotients of the switches PROVED from the tame inputs
  (`exists_suppSwitchRetractS`: `TameCochainQuasiIso`, `IwasawaGenerators`,
  `GenuineCochainsInjective`) and the Frobenius bases of the two places, give
  `CommonCoordinateLimitST`.

Kinds: definitions and PROVED.
-/

noncomputable section

namespace ZInQ.Manuscript.RC.Wiring

open Matrix Filter ZInQ.Manuscript ZInQ.Manuscript.RC ZInQ.Manuscript.RC.Central
  ZInQ.Manuscript.RC.Uniform ZInQ.Contrib.CloudB3RC53 ZInQ.Contrib.CloudB3RC53.CommonCoordinate
open ZInQ.Manuscript.RC.Limits (stageIdeal SplitInclusion)
open ZInQ.Contrib.CloudB3RC53.PairedFunctional
open ZInQ.Manuscript.RC.Local (twoSingCx)
open scoped PowerSeries.WithPiTopology

/-! ### Stage chains and their lifts -/

/-- **The coefficient stage** `A_s = Λ ⧸ (2^s, t^s)` (tex 4385–4451). Kind: definition. -/
abbrev StageRing (s : ℕ) : Type := LamI ⧸ stageIdeal s

/-- The reduction `Λ → A_s` (tex 4385–4451). Kind: definition. -/
abbrev stageMk (s : ℕ) : LamI →+* StageRing s := Ideal.Quotient.mk (stageIdeal s)

section Stages

variable {ι : Type} [DecidableEq ι] {Cx : ∀ s, Finset ι → GCx (StageRing s)}
  {Ex : ∀ s (T : Finset ι) (p : ι), SplitInclusion (Cx s T) (Cx s (insert p T))}
  {m0 m1 m2 : ℕ} {pidx : ℕ → ι} {n : ℕ}

/-- **The Frobenius data of a stage chain are the leaf's at the stage** (tex 4145, 4176–4184,
4385–4451): at the steps `i < n`, the images in `A_s` of the Frobenius data `f` over `Λ` are the
chain's Frobenius matrix, residue cardinality, point and inverse point, and the traces `a`.
Kind: definition. -/
def StageFrobAt (f : FrobSeq LamI) (s : ℕ) (cd : CMChainData (Cx s) (Ex s) m0 m1 m2 pidx n)
    (a : ℕ → StageRing s) : Prop :=
  ∀ i < n, (f.map (stageMk s)).Fr i = cd.Fr i ∧ (f.map (stageMk s)).q i = (cd.q i : StageRing s) ∧
    (f.map (stageMk s)).z i = cd.z i ∧ (f.map (stageMk s)).zi i = cd.zi i ∧
      (f.map (stageMk s)).a i = a i

/-- **The lifted matrix data of a family of stage chains** (tex 4385–4451): at every stage `s`, the
matrix data of the chain over `A_s`, lifted entrywise to `Λ`. Kind: definition. -/
def stageMats (cd : ∀ s, CMChainData (Cx s) (Ex s) m0 m1 m2 pidx n)
    (bw : ∀ s i, (Cx s (insert (pidx i) (chainT pidx i))).X 0)
    (μ : ∀ s i, (Cx s (chainT pidx i)).X 3 →ₗ[StageRing s] StageRing s) :
    ℕ → ChainMat LamI m0 m1 m2 :=
  fun s => stageLift s ((cd s).toChainMat (bw s) (μ s))

/-- **The lifted stage data satisfy the identities modulo the stage ideals at `U`-many stages**
(tex 4385–4451): from the step inputs and the leaf's Frobenius data at `U`-many stages.
Kind: PROVED. -/
theorem stageMats_hs (cd : ∀ s, CMChainData (Cx s) (Ex s) m0 m1 m2 pidx n)
    (bw : ∀ s i, (Cx s (insert (pidx i) (chainT pidx i))).X 0)
    (μ : ∀ s i, (Cx s (chainT pidx i)).X 3 →ₗ[StageRing s] StageRing s) (f : FrobSeq LamI)
    (U : Ultrafilter ℕ) (a : ∀ s, ℕ → StageRing s)
    (hstep : ∀ᶠ s in (U : Filter ℕ), CMStepHyps (cd s) (a s) (bw s) (μ s))
    (hfrob : ∀ᶠ s in (U : Filter ℕ), StageFrobAt f s (cd s) (a s)) :
    ∀ᶠ s in (U : Filter ℕ), (stageMats cd bw μ s).Holds (stageIdeal s) f n :=
  (hstep.and hfrob).mono fun s h => stageLift_holds s _ f n
    (toChainMat_holds (cd s) (bw s) (μ s) (a s) h.1 _ (fun i hi => (h.2 i hi).1)
      (fun i hi => (h.2 i hi).2.1) (fun i hi => (h.2 i hi).2.2.1)
      (fun i hi => (h.2 i hi).2.2.2.1) (fun i hi => (h.2 i hi).2.2.2.2))

end Stages

section Natural

variable {A : Type} [CommRing A] [Module.Injective A A] {ι : Type} [DecidableEq ι]
  {C : Finset ι → GCx A} {E : ∀ (T : Finset ι) (p : ι), SplitInclusion (C T) (C (insert p T))}
  {m0 m1 m2 : ℕ} {ps : ℕ → ι} {n : ℕ} (cd : CMChainData C E m0 m1 m2 ps n)

/-- **The step inputs from the norm identity and the naturality of the functionals, over a
self-injective coefficient ring** (tex 4169–4172, 4385–4451): if the relaxed functionals restrict
to `e_i` times the primitive ones on cocycles (lane RC30's naturality), the coboundaries `μ_i` of
the functional relation exist (`exists_cob_of_natural_inj`; the stage rings are self-injective).
Kind: PROVED. -/
theorem exists_stepHyps_of_natural (a : ℕ → A) (bw : ∀ i, (C (insert (ps i) (chainT ps i))).X 0)
    (hnorm : ∀ i (h : i < n), cd.zR i = pointFactor (a i) (cd.z i) (cd.zi i) •
        (E (chainT ps i) (ps i)).i.f 1 1 rfl (cmState cd i h.le).z +
      (C (insert (ps i) (chainT ps i))).d 0 1 rfl (bw i))
    (hnat : ∀ i (h : i < n), ∀ w, (C (chainT ps i)).d 2 3 rfl w = 0 →
      cd.lamR i ((E (chainT ps i) (ps i)).i.f 2 2 rfl w) =
        pointFactor (a i) (cd.z i) (cd.zi i) * (cmState cd i h.le).lam w) :
    ∃ μ : ∀ i, (C (chainT ps i)).X 3 →ₗ[A] A, CMStepHyps cd a bw μ := by
  have hμ : ∀ i (h : i < n), ∃ μ : (C (chainT ps i)).X 3 →ₗ[A] A,
      cd.lamR i ∘ₗ (E (chainT ps i) (ps i)).i.f 2 2 rfl =
        pointFactor (a i) (cd.z i) (cd.zi i) • (cmState cd i h.le).lam +
          μ ∘ₗ (C (chainT ps i)).d 2 3 rfl :=
    fun i h => exists_cob_of_natural_inj (E (chainT ps i) (ps i)).i (cd.lamR i)
      (cmState cd i h.le).lam _ (hnat i h)
  refine ⟨fun i => if h : i < n then Classical.choose (hμ i h) else 0, hnorm, fun i h => ?_⟩
  show _ = _ + (if h' : i < n then Classical.choose (hμ i h') else 0) ∘ₗ _
  rw [dite_eq_left h]
  exact Classical.choose_spec (hμ i h)

end Natural

section Leaf

variable {ℓ : ℕ} [(Ecurve ℓ).IsElliptic]

/-- **Stage chains of a presentation for the leaf** (tex 4142–4194, 4385–4451): the graph primes
are good odd primes; an order `ps` of the unused primes; a nonprincipal ultrafilter on the stages;
the ranks `(m₀, m₁, m₂)` of the models of `C_∅`; at every stage a chain of `|ps|` switches of the
presentation `Cx s` along the index sequence `pidx`, with boundaries `b`, coboundaries `μ` and
traces `a`; at `U`-many stages the step inputs and the leaf's Frobenius data; and the primitive
and corrected `t`-expansions of the end coordinates of the limit chain. Kind: definition (data). -/
structure StageChainsST (C : TateCoef (Ecurve ℓ)) (D : RCData ℓ) (Fam : Family)
    (x : Addr Fam.b) {ι : Type} [DecidableEq ι] (Cx : ∀ s, Finset ι → GCx (StageRing s))
    (Ex : ∀ s (T : Finset ι) (p : ι), SplitInclusion (Cx s T) (Cx s (insert p T)))
    (pidx : ℕ → ι) : Type where
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
  /-- the stage chains -/
  cd : ∀ s, CMChainData (Cx s) (Ex s) m0 m1 m2 pidx ps.length
  /-- the traces at the stages -/
  a : ∀ s, ℕ → StageRing s
  /-- the boundaries of the norm identities -/
  bw : ∀ s i, (Cx s (insert (pidx i) (chainT pidx i))).X 0
  /-- the coboundaries of the functional relations -/
  μ : ∀ s i, (Cx s (chainT pidx i)).X 3 →ₗ[StageRing s] StageRing s
  /-- the step inputs at `U`-many stages -/
  hstep : ∀ᶠ s in (U : Filter ℕ), CMStepHyps (cd s) (a s) (bw s) (μ s)
  /-- the leaf's Frobenius data at `U`-many stages -/
  hfrob : ∀ᶠ s in (U : Filter ℕ), StageFrobAt (leafFrobΛ C Fam x ps) s (cd s) (a s)
  /-- the primitive coordinate of the limit has `t`-expansion `u_{prim,x}` (tex 4153) -/
  hprim : IsTExpansion ((fracChain (stageMats cd bw μ) U).chainV
    (fracChain_holds _ hU _ _ (stageMats_hs cd bw μ _ U a hstep hfrob)) 0) (D.uPrim Fam x)
  /-- the corrected coordinate of the limit at `U_x` has `t`-expansion `ũ_x` (tex 4150–4151).
  Conclusion-shaped: since `chainSign = 1` and each step has `ε = q⁻⁴`,
  `η_x v_n = (∏_{q∈U_x} q⁻⁴) v₀`, so given `hprim` this field is equivalent to
  `ũ_x = (∏_{q∈U_x} q⁻⁴) u_{prim,x}`, the conclusion of Lemma `ex:arith-common-coordinate` with
  the unit pinned (stronger than the text's `ε_x ∈ Λ^×`, whose unit-disk factors, tex 4189–4193,
  are absorbed into the choice of the model and class of `C_∅`). The text's `ũ = η u_rel` is one
  common family (tex 4224–4225); that is not represented. -/
  htilde : IsTExpansion (etaF ℓ Fam x * (fracChain (stageMats cd bw μ) U).chainV
    (fracChain_holds _ hU _ _ (stageMats_hs cd bw μ _ U a hstep hfrob)) ps.length)
    (D.uTilde Fam x)

/-- **The inner-limit data of the leaf from stage chains** (tex 4142–4194, 4385–4451): the lifted
stage matrix data, with the leaf's Frobenius data over `Λ` (`leafFrobΛ`). Kind: definition. -/
def StageChainsST.toLimitST {C : TateCoef (Ecurve ℓ)} {D : RCData ℓ} {Fam : Family}
    {x : Addr Fam.b} {ι : Type} [DecidableEq ι] {Cx : ∀ s, Finset ι → GCx (StageRing s)}
    {Ex : ∀ s (T : Finset ι) (p : ι), SplitInclusion (Cx s T) (Cx s (insert p T))}
    {pidx : ℕ → ι} (G : StageChainsST C D Fam x Cx Ex pidx) :
    CommonCoordinateLimitST C D Fam x where
  hprime := G.hprime
  hgood := G.hgood
  ps := G.ps
  hnd := G.hnd
  hps := G.hps
  f := leafFrobΛ C Fam x G.ps
  hf := leafFrob_leafFrobΛ C Fam x G.hprime G.hps
  U := G.U
  hU := G.hU
  m0 := G.m0
  m1 := G.m1
  m2 := G.m2
  c := stageMats G.cd G.bw G.μ
  hs := stageMats_hs G.cd G.bw G.μ _ G.U G.a G.hstep G.hfrob
  hprim := G.hprim
  htilde := G.htilde

end Leaf

/-- **The common-coordinate inputs from stage chains** (tex 4142–4194, 4385–4451): `E_ℓ`
elliptic, a coefficient datum, and at every address of every final family stage chains of some
presentation of the support complexes. Kind: definition. -/
def CommonCoordinateInputsStages {ℓ : ℕ} (D : RCData ℓ) : Prop :=
  ∃ (hE : (Ecurve ℓ).IsElliptic) (C : TateCoef (Ecurve ℓ)),
    ∀ Co Ce : ℤ, ∀ F : Family, D.FinalFamilyAt Co Ce F → ∀ x : Addr F.b,
      ∃ (ι : Type) (_ : DecidableEq ι) (Cx : ∀ s, Finset ι → GCx (StageRing s))
        (Ex : ∀ s (T : Finset ι) (p : ι), SplitInclusion (Cx s T) (Cx s (insert p T)))
        (pidx : ℕ → ι), Nonempty (@StageChainsST ℓ hE C D F x ι _ Cx Ex pidx)

/-- **The inner-limit inputs from stage chains** (tex 4142–4194, 4385–4451). Kind: PROVED. -/
theorem commonCoordinateInputsLimit_of_stages {ℓ : ℕ} {D : RCData ℓ}
    (h : CommonCoordinateInputsStages D) : CommonCoordinateInputsLimit D := by
  obtain ⟨hE, C, hT⟩ := h
  refine ⟨hE, C, fun Co Ce F hF x => ?_⟩
  obtain ⟨ι, _, Cx, Ex, pidx, ⟨G⟩⟩ := hT Co Ce F hF x
  exact ⟨G.toLimitST⟩

/-- **(4.7) from stage chains** (tex 4142–4194, 4385–4451): `RCSteps.common_coordinate`.
Kind: PROVED. -/
theorem commonCoordinateTarget_of_stages {ℓ : ℕ} {D : RCData ℓ}
    (h : CommonCoordinateInputsStages D) : CommonCoordinateTarget D :=
  commonCoordinateTarget_of_limit (commonCoordinateInputsLimit_of_stages h)

end ZInQ.Manuscript.RC.Wiring
