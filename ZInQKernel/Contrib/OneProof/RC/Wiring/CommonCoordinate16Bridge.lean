import ZInQKernel.Contrib.OneProof.RC.Wiring.CommonCoordinate16Leaf
import ZInQKernel.Contrib.OneProof.RC.Wiring.CommonCoordinate16Retention

/-!
# The functional relations of the genuine chain from lane RC30's retention at the switches

Manuscript `diophantine_zq.tex`, Lemma `ex:arith-common-coordinate` (tex 4157–4172: "naturality
of the cup pairing gives `β_R(v, iw) = β_P(jv, w)` … consequently `λ_R ∘ i = e_q λ_P`") on the
genuine chain of the one presentation at a coefficient stage (tex 4385–4451).

* `StepRetention`: the retention data of one switch `suppSwitchS (T_i) (p_i)` of the chain (lane
  RC30's `PlaceRetentionG` through `SwitchRetentionInputs`), with the paired strict lift `z_S`
  of the orthogonal class `z_{P⊥}` with factor `e`.
* **`exists_stepHyps_of_switchRetention`**: at a stage, if the relaxed and the primitive
  functionals of every step are the paired functionals of the retention data
  (`λ_{R,i} = β_R(z_S, ·)`, `λ_i = β_P(z_{P⊥}, ·)`), the factors are the point factors and the norm
  identities hold, then the step inputs `CMStepHyps` hold with chosen coboundaries
  (`switch_natural_switch`, `exists_stepHyps_of_natural`; the stage rings are self-injective).

Kinds: definitions and PROVED.
-/

noncomputable section

namespace ZInQ.Manuscript.RC.Wiring

open NumberField IsDedekindDomain
open Matrix ZInQ.Manuscript.RC.Central
open ZInQ.Manuscript.RC.Limits (stageIdeal SplitInclusion)
open ZInQ.Contrib.CloudB3RC53.PairedFunctional
open ZInQ.Manuscript.RC.SelmerComplex ZInQ.Contrib.CloudB3RC53.UnramifiedComplex
  ZInQ.Contrib.CloudB3RC53.RankCounts
open ZInQ.Contrib.CloudB3RC53.SelmerDuality (changeMap)
open ZInQ.Contrib.CloudB3RC53.CommonCoordinate (pairedFun)
open scoped PowerSeries.WithPiTopology

section Bridge

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
/-- **The retention data of one switch of the chain** (tex 4157–4172): lane RC30's retention
inputs for `suppSwitchS T p` (`SwitchRetentionInputs`), a trace killing the coboundaries, the
paired strict lift `z_S` of the orthogonal class `z_{P⊥}` with factor `e` and its boundary.
Kind: definition (data). -/
structure StepRetention (s : ℕ) (T : Finset ι) (p : ι) (hp : p ∉ T) : Type 1 where
  /-- the orthogonal Selmer data -/
  DPp : SelData (StageRing s)
  /-- the strict local conditions -/
  US : GCx (StageRing s)
  /-- their inclusion -/
  fS : GHom US DPp.U
  /-- lane RC30's retention inputs at the switch -/
  I : SwitchRetentionInputs K S₀ S (StageRing s) (M s) (Δ s) place (X s) (EU s) T p hp DPp fS
  /-- the trace -/
  tr : (coneCx I.toPlaceRetentionG.toRetainedPairing.QP.resE).X 3 →ₗ[StageRing s] StageRing s
  /-- it kills the coboundaries -/
  htr : ∀ x, tr ((coneCx I.toPlaceRetentionG.toRetainedPairing.QP.resE).d 2 3 rfl x) = 0
  /-- the strict class -/
  zS : (selCx (selRestrict DPp fS)).X 1
  /-- the orthogonal class -/
  zP : (selCx DPp).X 1
  /-- the factor of the paired strict lift -/
  e : StageRing s
  /-- its boundary -/
  b : (selCx DPp).X 0
  /-- the paired strict lift `j z_S = e z_{P⊥} + d b` -/
  hlift : (changeMap DPp fS).f 1 1 rfl zS = e • zP + (selCx DPp).d 0 1 rfl b

/-- **The step inputs of a genuine stage chain from lane RC30's retention** (tex 4157–4172,
4385–4451): if every step `i < n` has retention data whose paired functionals are the relaxed
functional of the step and the functional of the state, with factor the point factor, and the
norm identities hold, the step inputs hold with chosen coboundaries. Kind: PROVED. -/
theorem exists_stepHyps_of_switchRetention {s m0 m1 m2 : ℕ} {pidx : ℕ → ι} {n : ℕ}
    (cd : CMChainData (genCx K S₀ S M Δ place X EU s) (genSw K S₀ S M Δ place X EU s) m0 m1 m2
      pidx n)
    (a : ℕ → StageRing s)
    (bw : ∀ i, (genCx K S₀ S M Δ place X EU s (insert (pidx i) (chainT pidx i))).X 0)
    (hnorm : ∀ i (h : i < n), cd.zR i = pointFactor (a i) (cd.z i) (cd.zi i) •
        (genSw K S₀ S M Δ place X EU s (chainT pidx i) (pidx i)).i.f 1 1 rfl
          (cmState cd i h.le).z +
      (genCx K S₀ S M Δ place X EU s (insert (pidx i) (chainT pidx i))).d 0 1 rfl (bw i))
    (hp : ∀ i, i < n → pidx i ∉ chainT pidx i)
    (R : ∀ i (h : i < n), StepRetention K S₀ S M Δ place X EU s (chainT pidx i) (pidx i) (hp i h))
    (he : ∀ i (h : i < n), (R i h).e = pointFactor (a i) (cd.z i) (cd.zi i))
    (hR : ∀ i (h : i < n), cd.lamR i =
      pairedFun (R i h).I.toPlaceRetentionG.toRetainedPairing.QR
        ((R i h).tr : (coneCx (R i h).I.toPlaceRetentionG.toRetainedPairing.QR.resE).X 3 →ₗ[
          StageRing s] StageRing s) (R i h).zS)
    (hP : ∀ i (h : i < n), (cmState cd i h.le).lam =
      pairedFun (R i h).I.toPlaceRetentionG.toRetainedPairing.QP (R i h).tr (R i h).zP) :
    ∃ μ : ∀ i, (genCx K S₀ S M Δ place X EU s (chainT pidx i)).X 3 →ₗ[StageRing s] StageRing s,
      CMStepHyps cd a bw μ := by
  refine exists_stepHyps_of_natural cd a bw hnorm fun i h w hw => ?_
  rw [hR i h, hP i h, ← he i h]
  exact switch_natural_switch (R i h).I (R i h).tr (R i h).htr (R i h).zS (R i h).zP
    (R i h).e (R i h).b (R i h).hlift w hw

end Bridge

end ZInQ.Manuscript.RC.Wiring
