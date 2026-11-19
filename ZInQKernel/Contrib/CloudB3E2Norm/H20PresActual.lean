import ZInQKernel.Contrib.CloudB3E2Norm.H20Pres

/-!
# The norm identity on the one presentation for the actual data

Manuscript `diophantine_zq.tex`, Lemma `ex:arith-common-coordinate` (tex 4142–4194) on lane RC32's
one presentation of the support complexes, for lane RC29's actual stage data over `A_i`
(tex 3203–3215, 3257–3290, 3471–3487, 4385–4451).

`H20Pres.hnorm_pres` gives the norm identity at a switch of the presentation from a global identity
and per-place lifts. This file supplies those inputs for the actual data — the stage module `MinS`,
RC29's actual old conditions (`stageConditions`: Kummer at `P`, full at `S₀ − P`) and the genuine
unramified conditions `genuineιq` (with `urRep`/`urId`) at the places above the unused primes — from
the corresponding Shapiro-level inputs over `ℤ[Δ]` (`H20Actual.lean`), by the coefficient push
(H20) `ℤ[Δ] → A_i`:

* `stageCond_injective`, `stageCond_surjective₀` (PROVED): the old conditions are injective in
  degree one and surjective in degree zero.
* `genuineιq_surjective₀` (PROVED): the genuine unramified condition with `f_q = urId` is surjective
  in degree zero.
* `stage_oldLift` (PROVED): an old lift of a Shapiro-level class gives an old lift of its push (the
  Kummer image is pushed into the Kummer image, `kummer_push_mem`, `cocyclePush`).
* `stage_urLift` (PROVED): an unramified lift of a Shapiro-level class at a new place gives one of
  its push (`wPushUr`, degree one).
* `stage_global` (PROVED): the global identity `a_R = e a_P + d b_G` is pushed (`cmap_d0`).
* **`hnorm_pres_actual`** (PROVED): the norm identity `z_R = e · i(z) + d b` at the switch
  `T → T ∪ {p}` of the presentation for the actual stage data, for the pushes of Shapiro-level
  classes with a Shapiro-level global identity, Shapiro-level old lifts, and Shapiro-level
  unramified lifts (of `a_R` at the places above `q ∉ T ∪ {p}`, of `a_P` at those above `q ∉ T`);
  the point factor is `φ(e₁)`.

Kinds: PROVED.
-/

noncomputable section

namespace ZInQ.Contrib.CloudB3E2.NormCochain

open ZInQ.Contrib.CloudB3RC53.HeegnerCohomology.TwistedTransfer
open ZInQ.Manuscript.RC.Wiring ZInQ.Manuscript.RC.SelmerComplex ZInQ.Manuscript.RC.CoefModules
open ZInQ.Manuscript.RC.KummerMaps ZInQ.Manuscript.RC.Limits
open ZInQ.Manuscript.RC.HeegnerAlgebra (Acoef)
open ZInQ.Contrib.CloudB3RC53.UnramifiedComplex ZInQ.Contrib.CloudB3RC53.RankCounts
open ZInQ.Contrib.CloudB3RC53.SelmerDuality ZInQ.Contrib.CloudB3RC53.PairedFunctional
open NumberField IsDedekindDomain

attribute [local instance] TopRep.distribMulAction TopRep.smulCommClass groupRingTop

set_option linter.unusedSectionVars false

/-! ### The genuine unramified condition is surjective in degree zero -/

section UrSurj

variable {K : Type} [Field K] [NumberField K] {S : Set (HeightOneSpectrum (𝓞 K))} (w : Places K S)
  {k : Type} [CommRing k] [TopologicalSpace k] {M : Type} [AddCommGroup M]
  [Module k M] [DistribMulAction (GKS K S) M] [SMulCommClass (GKS K S) k M]
  [TopologicalSpace M] [DiscreteTopology M] [ContinuousSMul (GKS K S) M]
  (X : TopRep.{0} k (GUr K w.1)) [ContinuousSMul (GUr K w.1) X.V] [DiscreteTopology X.V]
  [Finite X.V] (fq : X.V →ₗ[k] M)
  (hfq : ∀ (g : Gloc K w.1) (x : X.V), fq (resUr K w.1 g • x) = locMap K S w.1 g • fq x)

/-- **The genuine unramified condition is surjective in degree zero when `f_q` is** (PROVED):
`ι_q⁰` is `x ↦ const f_q(x)`. -/
theorem genuineιq_surjective₀ (hsurj : Function.Surjective fq) :
    Function.Surjective ((genuineιq K S k M w X fq hfq).f 0 0 rfl) := by
  intro c
  obtain ⟨x, hx⟩ := hsurj (c.1 Fin.elim0)
  refine ⟨(urG0 (S := S) w X).inv.hom x, ?_⟩
  rw [genuineιq_f0, iso_inv_hom_apply']
  apply Subtype.ext
  funext g
  exact hx.trans (congrArg c.1 (Subsingleton.elim Fin.elim0 g))

end UrSurj

/-! ### The actual inputs at the stage -/

section Actual

variable {K : Type} [Field K] [NumberField K] {S S₀ : Set (HeightOneSpectrum (𝓞 K))}
  (hS : S₀ ⊆ S) (W : WeierstrassCurve K) [W.IsElliptic] (i : ℕ) [NeZero i] (s : KS K S₀) {h : K}
  (hs : s ^ 2 = algebraMap K (KS K S₀) h) (hs0 : s ≠ 0) (hFull : FullTorsion K S₀ W (2 ^ i))
  [TopologicalSpace (Acoef i)] [DiscreteTopology (Acoef i)]
  {Δ : Type} [CommGroup Δ] [Finite Δ] (π : GKS K S₀ →* Δ) (ψ : Δ →* (Acoef i)ˣ)
  [IsOpenKer (alphaShap s hs hs0 π)] [IsOpenKer (alphaStage i s hs hs0 π ψ)]
  (P : Set (HeightOneSpectrum (𝓞 K))) (hψ : Function.Injective ψ) (hΨ : PsiTrivialAt2N i π ψ P)

open scoped Classical in
/-- **The actual old conditions are injective in degree one** (PROVED). -/
theorem stageCond_injective (v : Places K S₀) :
    Function.Injective (((stageConditions hS W i s hs hs0 hFull π ψ P hΨ).i v).f 1 1 rfl) := by
  change Function.Injective ((actLCondA hS W i s hs hs0 hFull P (alphaStage i s hs hs0 π ψ)
    (isLocallyQuadAt_stage i s hs hs0 π ψ hΨ) ⟨v.1, hS v.2⟩).i.f 1 1 rfl)
  by_cases hP : v.1 ∈ P
  · rw [actLCondA_of_P hS W i s hs hs0 hFull P (alphaStage i s hs hs0 π ψ)
      (isLocallyQuadAt_stage i s hs hs0 π ψ hΨ) (v := ⟨v.1, hS v.2⟩) v.2 hP]
    exact cocycleConditionι_injective _ _ 1
  · rw [actLCondA_of_notP hS W i s hs hs0 hFull P (alphaStage i s hs hs0 π ψ)
      (isLocallyQuadAt_stage i s hs hs0 π ψ hΨ) (v := ⟨v.1, hS v.2⟩) v.2 hP]
    exact fun _ _ h => h

open scoped Classical in
/-- **The actual old conditions are surjective in degree zero** (PROVED). -/
theorem stageCond_surjective₀ (v : Places K S₀) :
    Function.Surjective (((stageConditions hS W i s hs hs0 hFull π ψ P hΨ).i v).f 0 0 rfl) := by
  change Function.Surjective ((actLCondA hS W i s hs hs0 hFull P (alphaStage i s hs hs0 π ψ)
    (isLocallyQuadAt_stage i s hs hs0 π ψ hΨ) ⟨v.1, hS v.2⟩).i.f 0 0 rfl)
  by_cases hP : v.1 ∈ P
  · rw [actLCondA_of_P hS W i s hs hs0 hFull P (alphaStage i s hs hs0 π ψ)
      (isLocallyQuadAt_stage i s hs hs0 π ψ hΨ) (v := ⟨v.1, hS v.2⟩) v.2 hP]
    exact fun b => ⟨⟨b, trivial⟩, rfl⟩
  · rw [actLCondA_of_notP hS W i s hs hs0 hFull P (alphaStage i s hs hs0 π ψ)
      (isLocallyQuadAt_stage i s hs hs0 π ψ hΨ) (v := ⟨v.1, hS v.2⟩) v.2 hP]
    exact fun b => ⟨b, rfl⟩

/-- The push of global cochains `ℤ[Δ] → A_i`. -/
abbrev gPush (n : ℕ) :
    (globalCx (MonoidAlgebra ℤ Δ) (GKS K S) (shapMod hS W i s hs hs0 π)).X n →ₛₗ[h20RingHom ψ]
      (globalCx (Acoef i) (GKS K S) (MinS hS W i (alphaStage i s hs hs0 π ψ))).X n :=
  cmapCx (h20RingHom ψ) (shapPush hS W i s hs hs0 π ψ) n

open scoped Classical in
/-- **Old lifts survive the push** (PROVED; tex 3262–3270): a lift of `res_v a₁` through the
Shapiro-level old condition gives a lift of `res_v (push a₁)` through RC29's actual condition. -/
theorem stage_oldLift (v : Places K S₀)
    (a₁ : (globalCx (MonoidAlgebra ℤ Δ) (GKS K S) (shapMod hS W i s hs hs0 π)).X 1)
    (h₁ : ∃ u, ((shapConditions hS W i s hs hs0 hFull π ψ P hψ hΨ).i v).f 1 1 rfl u =
      (resS (MonoidAlgebra ℤ Δ) (GKS K S) (fun v : Places K S₀ => Gloc K v.1)
        (fun v => locMap K S v.1) (shapMod hS W i s hs hs0 π)).f 1 1 rfl a₁ v) :
    ∃ u, ((stageConditions hS W i s hs hs0 hFull π ψ P hΨ).i v).f 1 1 rfl u =
      (resS (Acoef i) (GKS K S) (fun v : Places K S₀ => Gloc K v.1)
        (fun v => locMap K S v.1) (MinS hS W i (alphaStage i s hs hs0 π ψ))).f 1 1 rfl
        (gPush hS W i s hs hs0 π ψ 1 a₁) v := by
  change ∃ u, (shapCond hS W i s hs hs0 hFull π ψ P hψ hΨ v).i.f 1 1 rfl u = _ at h₁
  change ∃ u, (actLCondA hS W i s hs hs0 hFull P (alphaStage i s hs hs0 π ψ)
    (isLocallyQuadAt_stage i s hs hs0 π ψ hΨ) ⟨v.1, hS v.2⟩).i.f 1 1 rfl u =
      cmap (h20RingHom ψ) (resPush (h20RingHom ψ) (shapPush hS W i s hs hs0 π ψ) v.1) 1
        ((resS (MonoidAlgebra ℤ Δ) (GKS K S) (fun v : Places K S₀ => Gloc K v.1)
          (fun v => locMap K S v.1) (shapMod hS W i s hs hs0 π)).f 1 1 rfl a₁ v)
  by_cases hP : v.1 ∈ P
  · rw [actLCondA_of_P hS W i s hs hs0 hFull P (alphaStage i s hs hs0 π ψ)
      (isLocallyQuadAt_stage i s hs hs0 π ψ hΨ) (v := ⟨v.1, hS v.2⟩) v.2 hP]
    have e : shapCond hS W i s hs hs0 hFull π ψ P hψ hΨ v =
        (haveI := isElliptic_localTwist W (ne_zero_of_sqrt s hs hs0) v.1
        kummerAt ⟨v.1, hS v.2⟩ (localTwist W h v.1) (2 ^ i) (shapIota hS W i s hs hs0 hFull π _)
          (shapIota_smul hS W i s hs hs0 hFull π _
            (isLocallyQuadAtGen_shap i s hs hs0 π ψ hψ hΨ hP))) := by
      unfold shapCond
      exact dite_eq_left_of_eq_true (eq_true hP)
    rw [e] at h₁
    obtain ⟨u, hu⟩ := h₁
    have := isElliptic_localTwist W (ne_zero_of_sqrt s hs hs0) v.1
    have hmem := (u : condP _ 1).2
    change (u : condP _ 1).1 = _ at hu
    rw [hu] at hmem
    exact ⟨⟨_, cocyclePush (h20RingHom ψ)
      (resPush (h20RingHom ψ) (shapPush hS W i s hs hs0 π ψ) v.1)
      (resPush_equivariant (h20RingHom ψ) (shapPush hS W i s hs hs0 π ψ)
        (shapPush_smul hS W i s hs hs0 π ψ) v.1) _ _
      (fun _ hz => kummer_push_mem (h20RingHom ψ)
        (resPush (h20RingHom ψ) (shapPush hS W i s hs hs0 π ψ) v.1) _ _
        (shapIota_push hS W i s hs hs0 hFull π ψ ⟨v.1, hS v.2⟩) hz) hmem⟩, rfl⟩
  · rw [actLCondA_of_notP hS W i s hs hs0 hFull P (alphaStage i s hs hs0 π ψ)
      (isLocallyQuadAt_stage i s hs hs0 π ψ hΨ) (v := ⟨v.1, hS v.2⟩) v.2 hP]
    exact ⟨_, rfl⟩

/-- **Unramified lifts survive the push** (PROVED; tex 3471–3487): a lift of `res_w a₁` through
the Shapiro-level genuine unramified condition at `w ∉ S₀` gives a lift of `res_w (push a₁)`
through the stage one (`wPushUr`, degree one). -/
theorem stage_urLift (w : Places K S) (hw : w.1 ∉ S₀)
    [ContinuousSMul (GUr K w.1)
      (urRep (MonoidAlgebra ℤ Δ) (shapMod₀ W i s hs hs0 π) (newPlace w hw)).V]
    [ContinuousSMul (GUr K w.1)
      (urRep (Acoef i) (Mcoef K S₀ W i (alphaStage i s hs hs0 π ψ)) (newPlace w hw)).V]
    (a₁ : (globalCx (MonoidAlgebra ℤ Δ) (GKS K S) (shapMod hS W i s hs hs0 π)).X 1)
    (h₁ : ∃ u, (genuineιq K S (MonoidAlgebra ℤ Δ) (shapMod hS W i s hs hs0 π) w
        (urRep (MonoidAlgebra ℤ Δ) (shapMod₀ W i s hs hs0 π) (newPlace w hw))
        (urId hS (MonoidAlgebra ℤ Δ) (shapMod₀ W i s hs hs0 π) (newPlace w hw))
        (urId_compat hS (MonoidAlgebra ℤ Δ) (shapMod₀ W i s hs hs0 π) w hw)).f 1 1 rfl u =
      (natHom (resCochains (k := MonoidAlgebra ℤ Δ) (M := shapMod hS W i s hs hs0 π)
        (locMap K S w.1))).f 1 1 rfl a₁) :
    ∃ u, (genuineιq K S (Acoef i) (MinS hS W i (alphaStage i s hs hs0 π ψ)) w
        (urRep (Acoef i) (Mcoef K S₀ W i (alphaStage i s hs hs0 π ψ)) (newPlace w hw))
        (urId hS (Acoef i) (Mcoef K S₀ W i (alphaStage i s hs hs0 π ψ)) (newPlace w hw))
        (urId_compat hS (Acoef i) (Mcoef K S₀ W i (alphaStage i s hs hs0 π ψ)) w hw)).f 1 1 rfl u =
      (natHom (resCochains (k := Acoef i) (M := MinS hS W i (alphaStage i s hs hs0 π ψ))
        (locMap K S w.1))).f 1 1 rfl (gPush hS W i s hs hs0 π ψ 1 a₁) := by
  obtain ⟨u, hu⟩ := h₁
  let WP := wPushUr (h20RingHom ψ) (shapPush hS W i s hs hs0 π ψ)
    (shapPush_smul hS W i s hs hs0 π ψ) w
    (urRep (MonoidAlgebra ℤ Δ) (shapMod₀ W i s hs hs0 π) (newPlace w hw))
    (urRep (Acoef i) (Mcoef K S₀ W i (alphaStage i s hs hs0 π ψ)) (newPlace w hw))
    (urId hS (MonoidAlgebra ℤ Δ) (shapMod₀ W i s hs hs0 π) (newPlace w hw))
    (urId_compat hS (MonoidAlgebra ℤ Δ) (shapMod₀ W i s hs hs0 π) w hw)
    (urId hS (Acoef i) (Mcoef K S₀ W i (alphaStage i s hs hs0 π ψ)) (newPlace w hw))
    (urId_compat hS (Acoef i) (Mcoef K S₀ W i (alphaStage i s hs hs0 π ψ)) w hw)
    (urPush W i s hs hs0 π ψ w hw) (urPush_smul W i s hs hs0 π ψ w hw) (fun _ => rfl)
  refine ⟨WP.w1 u, ?_⟩
  rw [← WP.hι1 u, hu]
  rfl

/-- **The global identity survives the push** (PROVED): `push a_R = φ(e) push a_P + d (push b_G)`. -/
theorem stage_global
    (aR aP : (globalCx (MonoidAlgebra ℤ Δ) (GKS K S) (shapMod hS W i s hs hs0 π)).X 1)
    (e : MonoidAlgebra ℤ Δ)
    (bG : (globalCx (MonoidAlgebra ℤ Δ) (GKS K S) (shapMod hS W i s hs hs0 π)).X 0)
    (hG : aR = e • aP + (globalCx (MonoidAlgebra ℤ Δ) (GKS K S) (shapMod hS W i s hs hs0 π)).d 0 1
      rfl bG) :
    gPush hS W i s hs hs0 π ψ 1 aR = h20RingHom ψ e • gPush hS W i s hs hs0 π ψ 1 aP +
      (globalCx (Acoef i) (GKS K S) (MinS hS W i (alphaStage i s hs hs0 π ψ))).d 0 1 rfl
        (gPush hS W i s hs hs0 π ψ 0 bG) := by
  rw [hG, map_add, LinearMap.map_smulₛₗ]
  congr 1
  exact cmap_d0 (h20RingHom ψ) (shapPush hS W i s hs hs0 π ψ)
    (shapPush_smul hS W i s hs hs0 π ψ) bG

variable [DecidableEq (Places K S₀)] {ι : Type} [DecidableEq ι] (place : ι × Bool → Places K S)
  (hw : ∀ j, (place j).1 ∉ S₀)
  [∀ j, ContinuousSMul (GUr K (place j).1)
    (urRep (MonoidAlgebra ℤ Δ) (shapMod₀ W i s hs hs0 π) (newPlace (place j) (hw j))).V]
  [∀ j, ContinuousSMul (GUr K (place j).1)
    (urRep (Acoef i) (Mcoef K S₀ W i (alphaStage i s hs hs0 π ψ)) (newPlace (place j) (hw j))).V]
  (EU : ∀ j, SplitInclusion
    (genuineUq K S (Acoef i) (place j)
      (urRep (Acoef i) (Mcoef K S₀ W i (alphaStage i s hs hs0 π ψ)) (newPlace (place j) (hw j))))
    (genuineLq K S (Acoef i) (MinS hS W i (alphaStage i s hs hs0 π ψ)) (place j)))
  (hE : ∀ j, (EU j).i = genuineιq K S (Acoef i) (MinS hS W i (alphaStage i s hs hs0 π ψ)) (place j)
    (urRep (Acoef i) (Mcoef K S₀ W i (alphaStage i s hs hs0 π ψ)) (newPlace (place j) (hw j)))
    (urId hS (Acoef i) (Mcoef K S₀ W i (alphaStage i s hs hs0 π ψ)) (newPlace (place j) (hw j)))
    (urId_compat hS (Acoef i) (Mcoef K S₀ W i (alphaStage i s hs hs0 π ψ)) (place j) (hw j)))

include hE in
/-- **The norm identity at a switch of the presentation for the actual stage data** (PROVED;
tex 3203–3215, 3257–3290, 3471–3487, 4157–4170, 4385–4451): on lane RC32's presentation over
`A_i` with RC29's actual old conditions and the genuine unramified conditions (`EU j` the genuine
inflation of `urRep` along `urId`), the pushes of Shapiro-level classes `a_R`, `a_P` with a
Shapiro-level identity `a_R = e a_P + d b_G`, Shapiro-level old lifts and Shapiro-level unramified
lifts (of `a_R` above `q ∉ T ∪ {p}`, of `a_P` above `q ∉ T`) have strict lifts with
`z_R = φ(e) · i(z) + d b` at the switch `T → T ∪ {p}` (the input `hnorm` of `CMStepHyps`). -/
theorem hnorm_pres_actual (T : Finset ι) (p : ι)
    (aR aP : (globalCx (MonoidAlgebra ℤ Δ) (GKS K S) (shapMod hS W i s hs hs0 π)).X 1)
    (e : MonoidAlgebra ℤ Δ)
    (bG : (globalCx (MonoidAlgebra ℤ Δ) (GKS K S) (shapMod hS W i s hs hs0 π)).X 0)
    (hG : aR = e • aP + (globalCx (MonoidAlgebra ℤ Δ) (GKS K S) (shapMod hS W i s hs hs0 π)).d 0 1
      rfl bG)
    (holdR : ∀ v₀, ∃ u, ((shapConditions hS W i s hs hs0 hFull π ψ P hψ hΨ).i v₀).f 1 1 rfl u =
      (resS (MonoidAlgebra ℤ Δ) (GKS K S) (fun v : Places K S₀ => Gloc K v.1)
        (fun v => locMap K S v.1) (shapMod hS W i s hs hs0 π)).f 1 1 rfl aR v₀)
    (holdP : ∀ v₀, ∃ u, ((shapConditions hS W i s hs hs0 hFull π ψ P hψ hΨ).i v₀).f 1 1 rfl u =
      (resS (MonoidAlgebra ℤ Δ) (GKS K S) (fun v : Places K S₀ => Gloc K v.1)
        (fun v => locMap K S v.1) (shapMod hS W i s hs hs0 π)).f 1 1 rfl aP v₀)
    (hurR : ∀ j, j.1 ∉ insert p T → ∃ u,
      (genuineιq K S (MonoidAlgebra ℤ Δ) (shapMod hS W i s hs hs0 π) (place j)
        (urRep (MonoidAlgebra ℤ Δ) (shapMod₀ W i s hs hs0 π) (newPlace (place j) (hw j)))
        (urId hS (MonoidAlgebra ℤ Δ) (shapMod₀ W i s hs hs0 π) (newPlace (place j) (hw j)))
        (urId_compat hS (MonoidAlgebra ℤ Δ) (shapMod₀ W i s hs hs0 π) (place j) (hw j))).f 1 1 rfl
          u =
      (natHom (resCochains (k := MonoidAlgebra ℤ Δ) (M := shapMod hS W i s hs hs0 π)
        (locMap K S (place j).1))).f 1 1 rfl aR)
    (hurP : ∀ j, j.1 ∉ T → ∃ u,
      (genuineιq K S (MonoidAlgebra ℤ Δ) (shapMod hS W i s hs hs0 π) (place j)
        (urRep (MonoidAlgebra ℤ Δ) (shapMod₀ W i s hs hs0 π) (newPlace (place j) (hw j)))
        (urId hS (MonoidAlgebra ℤ Δ) (shapMod₀ W i s hs hs0 π) (newPlace (place j) (hw j)))
        (urId_compat hS (MonoidAlgebra ℤ Δ) (shapMod₀ W i s hs hs0 π) (place j) (hw j))).f 1 1 rfl
          u =
      (natHom (resCochains (k := MonoidAlgebra ℤ Δ) (M := shapMod hS W i s hs hs0 π)
        (locMap K S (place j).1))).f 1 1 rfl aP) :
    ∃ (zR : (suppCxS K S₀ S (Acoef i) (MinS hS W i (alphaStage i s hs hs0 π ψ))
        (stageConditions hS W i s hs hs0 hFull π ψ P hΨ) place
        (fun j => urRep (Acoef i) (Mcoef K S₀ W i (alphaStage i s hs hs0 π ψ))
          (newPlace (place j) (hw j))) EU (insert p T)).X 1)
      (z : (suppCxS K S₀ S (Acoef i) (MinS hS W i (alphaStage i s hs hs0 π ψ))
        (stageConditions hS W i s hs hs0 hFull π ψ P hΨ) place
        (fun j => urRep (Acoef i) (Mcoef K S₀ W i (alphaStage i s hs hs0 π ψ))
          (newPlace (place j) (hw j))) EU T).X 1)
      (b : (suppCxS K S₀ S (Acoef i) (MinS hS W i (alphaStage i s hs hs0 π ψ))
        (stageConditions hS W i s hs hs0 hFull π ψ P hΨ) place
        (fun j => urRep (Acoef i) (Mcoef K S₀ W i (alphaStage i s hs hs0 π ψ))
          (newPlace (place j) (hw j))) EU (insert p T)).X 0),
      zR.1 = gPush hS W i s hs hs0 π ψ 1 aR ∧ z.1 = gPush hS W i s hs hs0 π ψ 1 aP ∧
      zR = h20RingHom ψ e • (suppSwitchS K S₀ S (Acoef i) (MinS hS W i (alphaStage i s hs hs0 π ψ))
          (stageConditions hS W i s hs hs0 hFull π ψ P hΨ) place
          (fun j => urRep (Acoef i) (Mcoef K S₀ W i (alphaStage i s hs hs0 π ψ))
            (newPlace (place j) (hw j))) EU T p).i.f 1 1 rfl z +
        (suppCxS K S₀ S (Acoef i) (MinS hS W i (alphaStage i s hs hs0 π ψ))
          (stageConditions hS W i s hs hs0 hFull π ψ P hΨ) place
          (fun j => urRep (Acoef i) (Mcoef K S₀ W i (alphaStage i s hs hs0 π ψ))
            (newPlace (place j) (hw j))) EU (insert p T)).d 0 1 rfl b :=
  hnorm_pres K S₀ S (Acoef i) (MinS hS W i (alphaStage i s hs hs0 π ψ))
    (stageConditions hS W i s hs hs0 hFull π ψ P hΨ) place
    (fun j => urRep (Acoef i) (Mcoef K S₀ W i (alphaStage i s hs hs0 π ψ))
      (newPlace (place j) (hw j))) EU T p
    (gPush hS W i s hs hs0 π ψ 1 aR) (gPush hS W i s hs hs0 π ψ 1 aP) (h20RingHom ψ e)
    (gPush hS W i s hs hs0 π ψ 0 bG)
    (stageCond_injective hS W i s hs hs0 hFull π ψ P hΨ)
    (stageCond_surjective₀ hS W i s hs hs0 hFull π ψ P hΨ)
    (fun j => by
      rw [hE j]
      exact genuineιq_surjective₀ (place j) _ _ _ Function.surjective_id)
    (stage_global hS W i s hs hs0 π ψ aR aP e bG hG)
    (fun v₀ => stage_oldLift hS W i s hs hs0 hFull π ψ P hψ hΨ v₀ aR (holdR v₀))
    (fun v₀ => stage_oldLift hS W i s hs hs0 hFull π ψ P hψ hΨ v₀ aP (holdP v₀))
    (fun j hj => by
      rw [hE j]
      exact stage_urLift hS W i s hs hs0 π ψ (place j) (hw j) aR (hurR j hj))
    (fun j hj => by
      rw [hE j]
      exact stage_urLift hS W i s hs hs0 π ψ (place j) (hw j) aP (hurP j hj))

end Actual

end ZInQ.Contrib.CloudB3E2.NormCochain
