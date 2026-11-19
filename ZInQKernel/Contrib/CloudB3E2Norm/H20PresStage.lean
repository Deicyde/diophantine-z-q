import ZInQKernel.Contrib.CloudB3E2Norm.H20PresAssembly

/-!
# The norm identity on the one presentation over any stage ring isomorphic to `A_i`

Manuscript `diophantine_zq.tex`, Lemma `ex:arith-common-coordinate` (tex 4142–4194, 4157–4170) at
the stages of the inner limit (tex 4385–4451: `A_s = Λ ⧸ (2^s, t^s) ≅ (ℤ/2^s)[t]/t^s`, tex 2725,
2747).

`H20PresActual.lean` instantiates lane RC32's one presentation (`suppCxS`) over `A_i = Acoef i`.
Lane RC32's consumers (`GenuineStageSteps`, `CMStepHyps`) work over `StageRing s = Λ ⧸ stageIdeal s`,
which is isomorphic to `A_s` (`Limits.stageEquiv`, with `StageA s = Acoef s` definitionally). This
file makes the actual instance generic over a commutative ring `k` with a ring isomorphism
`e : k ≃+* A_i`:

* `mcoefModuleK`, `mcoefSMulCommK` (local instances): `M_i = Mcoef` and hence `MinS` (its inflation)
  as `k`-modules through `e`; the Galois actions commute with `k`.
* `condK`, **`stageCondsK`** (definitions): lane RC29's actual old conditions over `k` (the Kummer
  condition of `kummerIotaS` at `v ∈ P`, the full condition at `S₀ − P`).
* `phiK = e⁻¹ ∘ φ` (`φ = h20RingHom ψ`), `shapPushK`, `urPushK`, `gPushK` (definitions): the
  coefficient push `ℤ[Δ] → k` of the Shapiro-level module, of the unramified modules and of global
  cochains.
* `stageCondK_injective`, `stageCondK_surjective₀`, `stage_oldLiftK`, `stage_urLiftK`,
  `stage_globalK` (PROVED): as in `H20PresActual.lean`, over `k`.
* **`hnorm_presK`** (PROVED): the norm identity at the switch `T → T ∪ {p}` of the presentation over
  `k` (module `MinS`, conditions `stageCondsK`, unramified representations `urRep k`, splits `EU j`
  the genuine inflations along `urId`) for the pushes of Shapiro-level classes, from Shapiro-level
  inputs; point factor `phiK e₁`.
* **`hnorm_pres_of_transferK`** (PROVED): the same from the named inputs of `h1_shapiro` and the
  unramified lifts (which `H20AmbientS.hur_actualS` supplies for the ambient module of points;
  `H20Untwisted.hur_actualUH` when the fixed fields of the transfer subgroups lie in `K_{S₀}`).

For lane RC32's stages take `k = StageRing s = Λ ⧸ stageIdeal s` with `stageIsoA s`
(`e = stageEquiv s`; `StageA s = Acoef s` by `rfl`). The splits match lane RC32's
`GenuineStageSteps.hE` with `X s j = urRep k M_i` and `f j = urId` (bijective) by definition
(`genuineιq` is `ofCCHom (urToLocal_galois …)`).

Kinds: definitions and PROVED.
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

/-- **A stage ring isomorphic to `A_i`**: a ring isomorphism `k ≃+* A_i` (for lane RC32's stages,
`stageEquiv s : Λ ⧸ stageIdeal s ≃+* A_s`). Kind: definition (class). -/
class StageIsoA (k : Type) [CommRing k] (i : ℕ) : Type where
  /-- the isomorphism -/
  e : k ≃+* Acoef i

/-- The isomorphism of a `StageIsoA`. Kind: definition. -/
abbrev eK (k : Type) [CommRing k] (i : ℕ) [StageIsoA k i] : k ≃+* Acoef i := StageIsoA.e

/-- **Lane RC32's stages**: `StageRing s = Λ ⧸ stageIdeal s ≃+* A_s` (`stageEquiv s`;
`StageA s = Acoef s` by `rfl`). Kind: definition. -/
@[reducible] def stageIsoA (s : ℕ) : StageIsoA (StageRing s) s := ⟨stageEquiv s⟩

section StageK

variable {K : Type} [Field K] [NumberField K] {S S₀ : Set (HeightOneSpectrum (𝓞 K))}
  (hS : S₀ ⊆ S) (W : WeierstrassCurve K) [W.IsElliptic] (i : ℕ) [NeZero i] (s : KS K S₀) {h : K}
  (hs : s ^ 2 = algebraMap K (KS K S₀) h) (hs0 : s ≠ 0) (hFull : FullTorsion K S₀ W (2 ^ i))
  [TopologicalSpace (Acoef i)] [DiscreteTopology (Acoef i)]
  {Δ : Type} [CommGroup Δ] [Finite Δ] (π : GKS K S₀ →* Δ) (ψ : Δ →* (Acoef i)ˣ)
  [IsOpenKer (alphaShap s hs hs0 π)] [IsOpenKer (alphaStage i s hs hs0 π ψ)]
  (P : Set (HeightOneSpectrum (𝓞 K))) (hψ : Function.Injective ψ) (hΨ : PsiTrivialAt2N i π ψ P)
  (k : Type) [CommRing k] [TopologicalSpace k] [DiscreteTopology k] [StageIsoA k i]

/-- `M_i` as a `k`-module through `e`. Kind: definition. -/
abbrev mcoefModuleK : Module k (Mcoef K S₀ W i (alphaStage i s hs hs0 π ψ)) :=
  Module.compHom _ (eK k i).toRingHom

attribute [local instance] mcoefModuleK

theorem smul_def_K (c : k) (m : Mcoef K S₀ W i (alphaStage i s hs hs0 π ψ)) :
    c • m = eK k i c • m := rfl

/-- The Galois action on `M_i` commutes with `k`. Kind: PROVED. -/
instance mcoefSMulCommK :
    SMulCommClass (GKS K S₀) k (Mcoef K S₀ W i (alphaStage i s hs hs0 π ψ)) :=
  ⟨fun g c m => by
    rw [smul_def_K, smul_def_K]
    exact smul_comm g (eK k i c) m⟩

instance mcoefContinuousConstSMulK :
    ContinuousConstSMul k (MinS hS W i (alphaStage i s hs hs0 π ψ)) :=
  ⟨fun _ => continuous_of_discreteTopology⟩

open scoped Classical in
/-- **Lane RC29's actual old condition at `v ∈ S₀` over `k`** (the Kummer condition of
`kummerIotaS` at `v ∈ P`, the full condition otherwise). Kind: definition. -/
def condK (v : Places K S₀) :
    CondAt K S k (MinS hS W i (alphaStage i s hs hs0 π ψ)) ⟨v.1, hS v.2⟩ :=
  if hP : v.1 ∈ P then
    haveI := isElliptic_localTwist W (ne_zero_of_sqrt s hs hs0) v.1
    kummerAt ⟨v.1, hS v.2⟩ (localTwist W h v.1) (2 ^ i)
      (kummerIotaS hS W i s hs hs0 (alphaStage i s hs hs0 π ψ) hFull ⟨v.1, hS v.2⟩)
      (kummerIotaS_smul hS W i s hs hs0 (alphaStage i s hs hs0 π ψ) hFull ⟨v.1, hS v.2⟩
        (isLocallyQuadAt_stage i s hs hs0 π ψ hΨ v.1 hP))
  else fullAt K S k (MinS hS W i (alphaStage i s hs hs0 π ψ)) ⟨v.1, hS v.2⟩

/-- **The actual old conditions over `k`**. Kind: definition. -/
def stageCondsK : LocalConditions k (GKS K S) (fun v : Places K S₀ => Gloc K v.1)
    (fun v => locMap K S v.1) (MinS hS W i (alphaStage i s hs hs0 π ψ)) where
  U v := (condK hS W i s hs hs0 hFull π ψ P hΨ k v).U
  i v := (condK hS W i s hs hs0 hFull π ψ P hΨ k v).i

/-- The coefficient ring map `ℤ[Δ] → k`, `e⁻¹ ∘ φ`. Kind: definition. -/
abbrev phiK : MonoidAlgebra ℤ Δ →+* k := (eK k i).symm.toRingHom.comp (h20RingHom ψ)

/-- The push `ℤ[Δ] ⊗ T → M_i` over `k`. Kind: definition. -/
def shapPushK : shapMod hS W i s hs hs0 π →ₛₗ[phiK i ψ k]
    MinS hS W i (alphaStage i s hs hs0 π ψ) where
  toFun := shapPush hS W i s hs hs0 π ψ
  map_add' := map_add _
  map_smul' r m := by
    change shapPush hS W i s hs hs0 π ψ (r • m) = eK k i ((eK k i).symm (h20RingHom ψ r)) • _
    rw [RingEquiv.apply_symm_apply]
    exact LinearMap.map_smulₛₗ _ r m

theorem shapPushK_smul (g : GKS K S) (m : shapMod hS W i s hs hs0 π) :
    shapPushK hS W i s hs hs0 π ψ k (g • m) = g • shapPushK hS W i s hs hs0 π ψ k m :=
  shapPush_smul hS W i s hs hs0 π ψ g m

/-- The push of global cochains `ℤ[Δ] → k`. Kind: definition. -/
abbrev gPushK (n : ℕ) :
    (globalCx (MonoidAlgebra ℤ Δ) (GKS K S) (shapMod hS W i s hs hs0 π)).X n →ₛₗ[phiK i ψ k]
      (globalCx k (GKS K S) (MinS hS W i (alphaStage i s hs hs0 π ψ))).X n :=
  cmapCx (phiK i ψ k) (shapPushK hS W i s hs hs0 π ψ k) n

/-- The push of the unramified modules at `w ∉ S₀` over `k`. Kind: definition. -/
def urPushK (w : Places K S) (hw : w.1 ∉ S₀) :
    (urRep (MonoidAlgebra ℤ Δ) (shapMod₀ W i s hs hs0 π) (newPlace w hw)).V →ₛₗ[phiK i ψ k]
      (urRep k (Mcoef K S₀ W i (alphaStage i s hs hs0 π ψ)) (newPlace w hw)).V where
  toFun := shapPush₀ W i s hs hs0 π ψ
  map_add' := map_add _
  map_smul' r m := by
    change shapPush₀ W i s hs hs0 π ψ (r • m) = eK k i ((eK k i).symm (h20RingHom ψ r)) • _
    rw [RingEquiv.apply_symm_apply]
    exact LinearMap.map_smulₛₗ _ r m

theorem urPushK_smul (w : Places K S) (hw : w.1 ∉ S₀) (γ : GUr K w.1)
    (x : (urRep (MonoidAlgebra ℤ Δ) (shapMod₀ W i s hs hs0 π) (newPlace w hw)).V) :
    urPushK W i s hs hs0 π ψ k w hw (γ • x) = γ • urPushK W i s hs hs0 π ψ k w hw x :=
  shapPush₀_smul W i s hs hs0 π ψ (urFactor K (newPlace w hw) γ) x

open scoped Classical in
/-- The actual old conditions over `k` are injective in degree one. Kind: PROVED. -/
theorem stageCondK_injective (v : Places K S₀) :
    Function.Injective (((stageCondsK hS W i s hs hs0 hFull π ψ P hΨ k).i v).f 1 1 rfl) := by
  change Function.Injective ((condK hS W i s hs hs0 hFull π ψ P hΨ k v).i.f 1 1 rfl)
  unfold condK
  exact condAt_dite _ _ (fun c => Function.Injective (c.i.f 1 1 rfl))
    (fun _ => cocycleConditionι_injective _ _ 1) (fun _ _ _ hab => hab)

open scoped Classical in
/-- The actual old conditions over `k` are surjective in degree zero. Kind: PROVED. -/
theorem stageCondK_surjective₀ (v : Places K S₀) :
    Function.Surjective (((stageCondsK hS W i s hs hs0 hFull π ψ P hΨ k).i v).f 0 0 rfl) := by
  change Function.Surjective ((condK hS W i s hs hs0 hFull π ψ P hΨ k v).i.f 0 0 rfl)
  by_cases hP : v.1 ∈ P
  · have e₂ : condK hS W i s hs hs0 hFull π ψ P hΨ k v =
        (haveI := isElliptic_localTwist W (ne_zero_of_sqrt s hs hs0) v.1
        kummerAt ⟨v.1, hS v.2⟩ (localTwist W h v.1) (2 ^ i)
          (kummerIotaS hS W i s hs hs0 (alphaStage i s hs hs0 π ψ) hFull ⟨v.1, hS v.2⟩)
          (kummerIotaS_smul hS W i s hs hs0 (alphaStage i s hs hs0 π ψ) hFull ⟨v.1, hS v.2⟩
            (isLocallyQuadAt_stage i s hs hs0 π ψ hΨ v.1 hP))) := by
      unfold condK
      exact dite_eq_left_of_eq_true (eq_true hP)
    rw [e₂]
    intro b
    exact ⟨⟨b, trivial⟩, rfl⟩
  · have e₂ : condK hS W i s hs hs0 hFull π ψ P hΨ k v =
        fullAt K S k (MinS hS W i (alphaStage i s hs hs0 π ψ)) ⟨v.1, hS v.2⟩ := by
      unfold condK
      exact dite_eq_right_of_eq_false (eq_false hP)
    rw [e₂]
    exact fun b => ⟨b, rfl⟩

open scoped Classical in
/-- **Old lifts survive the push to `k`** (PROVED; tex 3262–3270). -/
theorem stage_oldLiftK (v : Places K S₀)
    (a₁ : (globalCx (MonoidAlgebra ℤ Δ) (GKS K S) (shapMod hS W i s hs hs0 π)).X 1)
    (h₁ : ∃ u, ((shapConditions hS W i s hs hs0 hFull π ψ P hψ hΨ).i v).f 1 1 rfl u =
      (resS (MonoidAlgebra ℤ Δ) (GKS K S) (fun v : Places K S₀ => Gloc K v.1)
        (fun v => locMap K S v.1) (shapMod hS W i s hs hs0 π)).f 1 1 rfl a₁ v) :
    ∃ u, ((stageCondsK hS W i s hs hs0 hFull π ψ P hΨ k).i v).f 1 1 rfl u =
      (resS k (GKS K S) (fun v : Places K S₀ => Gloc K v.1)
        (fun v => locMap K S v.1) (MinS hS W i (alphaStage i s hs hs0 π ψ))).f 1 1 rfl
        (gPushK hS W i s hs hs0 π ψ k 1 a₁) v := by
  change ∃ u, (shapCond hS W i s hs hs0 hFull π ψ P hψ hΨ v).i.f 1 1 rfl u = _ at h₁
  change ∃ u, (condK hS W i s hs hs0 hFull π ψ P hΨ k v).i.f 1 1 rfl u =
      cmap (phiK i ψ k) (resPush (phiK i ψ k) (shapPushK hS W i s hs hs0 π ψ k) v.1) 1
        ((resS (MonoidAlgebra ℤ Δ) (GKS K S) (fun v : Places K S₀ => Gloc K v.1)
          (fun v => locMap K S v.1) (shapMod hS W i s hs hs0 π)).f 1 1 rfl a₁ v)
  by_cases hP : v.1 ∈ P
  · have e₁ : shapCond hS W i s hs hs0 hFull π ψ P hψ hΨ v =
        (haveI := isElliptic_localTwist W (ne_zero_of_sqrt s hs hs0) v.1
        kummerAt ⟨v.1, hS v.2⟩ (localTwist W h v.1) (2 ^ i) (shapIota hS W i s hs hs0 hFull π _)
          (shapIota_smul hS W i s hs hs0 hFull π _
            (isLocallyQuadAtGen_shap i s hs hs0 π ψ hψ hΨ hP))) := by
      unfold shapCond
      exact dite_eq_left_of_eq_true (eq_true hP)
    have e₂ : condK hS W i s hs hs0 hFull π ψ P hΨ k v =
        (haveI := isElliptic_localTwist W (ne_zero_of_sqrt s hs hs0) v.1
        kummerAt ⟨v.1, hS v.2⟩ (localTwist W h v.1) (2 ^ i)
          (kummerIotaS hS W i s hs hs0 (alphaStage i s hs hs0 π ψ) hFull ⟨v.1, hS v.2⟩)
          (kummerIotaS_smul hS W i s hs hs0 (alphaStage i s hs hs0 π ψ) hFull ⟨v.1, hS v.2⟩
            (isLocallyQuadAt_stage i s hs hs0 π ψ hΨ v.1 hP))) := by
      unfold condK
      exact dite_eq_left_of_eq_true (eq_true hP)
    rw [e₁] at h₁
    rw [e₂]
    obtain ⟨u, hu⟩ := h₁
    have := isElliptic_localTwist W (ne_zero_of_sqrt s hs hs0) v.1
    have hmem := (u : condP _ 1).2
    change (u : condP _ 1).1 = _ at hu
    rw [hu] at hmem
    exact ⟨⟨_, cocyclePush (phiK i ψ k)
      (resPush (phiK i ψ k) (shapPushK hS W i s hs hs0 π ψ k) v.1)
      (resPush_equivariant (phiK i ψ k) (shapPushK hS W i s hs hs0 π ψ k)
        (shapPushK_smul hS W i s hs hs0 π ψ k) v.1) _ _
      (fun _ hz => kummer_push_mem (phiK i ψ k)
        (resPush (phiK i ψ k) (shapPushK hS W i s hs hs0 π ψ k) v.1) _ _
        (shapIota_push hS W i s hs hs0 hFull π ψ ⟨v.1, hS v.2⟩) hz) hmem⟩, rfl⟩
  · have e₂ : condK hS W i s hs hs0 hFull π ψ P hΨ k v =
        fullAt K S k (MinS hS W i (alphaStage i s hs hs0 π ψ)) ⟨v.1, hS v.2⟩ := by
      unfold condK
      exact dite_eq_right_of_eq_false (eq_false hP)
    rw [e₂]
    exact ⟨_, rfl⟩

/-- **Unramified lifts survive the push to `k`** (PROVED; tex 3471–3487; `wPushUr`). -/
theorem stage_urLiftK (w : Places K S) (hw : w.1 ∉ S₀)
    [ContinuousSMul (GUr K w.1)
      (urRep (MonoidAlgebra ℤ Δ) (shapMod₀ W i s hs hs0 π) (newPlace w hw)).V]
    [ContinuousSMul (GUr K w.1)
      (urRep k (Mcoef K S₀ W i (alphaStage i s hs hs0 π ψ)) (newPlace w hw)).V]
    (a₁ : (globalCx (MonoidAlgebra ℤ Δ) (GKS K S) (shapMod hS W i s hs hs0 π)).X 1)
    (h₁ : ∃ u, (genuineιq K S (MonoidAlgebra ℤ Δ) (shapMod hS W i s hs hs0 π) w
        (urRep (MonoidAlgebra ℤ Δ) (shapMod₀ W i s hs hs0 π) (newPlace w hw))
        (urId hS (MonoidAlgebra ℤ Δ) (shapMod₀ W i s hs hs0 π) (newPlace w hw))
        (urId_compat hS (MonoidAlgebra ℤ Δ) (shapMod₀ W i s hs hs0 π) w hw)).f 1 1 rfl u =
      (natHom (resCochains (k := MonoidAlgebra ℤ Δ) (M := shapMod hS W i s hs hs0 π)
        (locMap K S w.1))).f 1 1 rfl a₁) :
    ∃ u, (genuineιq K S k (MinS hS W i (alphaStage i s hs hs0 π ψ)) w
        (urRep k (Mcoef K S₀ W i (alphaStage i s hs hs0 π ψ)) (newPlace w hw))
        (urId hS k (Mcoef K S₀ W i (alphaStage i s hs hs0 π ψ)) (newPlace w hw))
        (urId_compat hS k (Mcoef K S₀ W i (alphaStage i s hs hs0 π ψ)) w hw)).f 1 1 rfl u =
      (natHom (resCochains (k := k) (M := MinS hS W i (alphaStage i s hs hs0 π ψ))
        (locMap K S w.1))).f 1 1 rfl (gPushK hS W i s hs hs0 π ψ k 1 a₁) := by
  obtain ⟨u, hu⟩ := h₁
  let WP := wPushUr (phiK i ψ k) (shapPushK hS W i s hs hs0 π ψ k)
    (shapPushK_smul hS W i s hs hs0 π ψ k) w
    (urRep (MonoidAlgebra ℤ Δ) (shapMod₀ W i s hs hs0 π) (newPlace w hw))
    (urRep k (Mcoef K S₀ W i (alphaStage i s hs hs0 π ψ)) (newPlace w hw))
    (urId hS (MonoidAlgebra ℤ Δ) (shapMod₀ W i s hs hs0 π) (newPlace w hw))
    (urId_compat hS (MonoidAlgebra ℤ Δ) (shapMod₀ W i s hs hs0 π) w hw)
    (urId hS k (Mcoef K S₀ W i (alphaStage i s hs hs0 π ψ)) (newPlace w hw))
    (urId_compat hS k (Mcoef K S₀ W i (alphaStage i s hs hs0 π ψ)) w hw)
    (urPushK W i s hs hs0 π ψ k w hw) (urPushK_smul W i s hs hs0 π ψ k w hw)
    (fun _ => rfl)
  refine ⟨WP.w1 u, ?_⟩
  rw [← WP.hι1 u, hu]
  rfl

/-- **The global identity survives the push to `k`** (PROVED). -/
theorem stage_globalK
    (aR aP : (globalCx (MonoidAlgebra ℤ Δ) (GKS K S) (shapMod hS W i s hs hs0 π)).X 1)
    (e₁ : MonoidAlgebra ℤ Δ)
    (bG : (globalCx (MonoidAlgebra ℤ Δ) (GKS K S) (shapMod hS W i s hs hs0 π)).X 0)
    (hG : aR = e₁ • aP + (globalCx (MonoidAlgebra ℤ Δ) (GKS K S) (shapMod hS W i s hs hs0 π)).d 0 1
      rfl bG) :
    gPushK hS W i s hs hs0 π ψ k 1 aR = phiK i ψ k e₁ • gPushK hS W i s hs hs0 π ψ k 1 aP +
      (globalCx k (GKS K S) (MinS hS W i (alphaStage i s hs hs0 π ψ))).d 0 1 rfl
        (gPushK hS W i s hs hs0 π ψ k 0 bG) := by
  rw [hG, map_add, LinearMap.map_smulₛₗ]
  congr 1
  exact cmap_d0 (phiK i ψ k) (shapPushK hS W i s hs hs0 π ψ k)
    (shapPushK_smul hS W i s hs hs0 π ψ k) bG

variable [DecidableEq (Places K S₀)] {ι : Type} [DecidableEq ι] (place : ι × Bool → Places K S)
  (hw : ∀ j, (place j).1 ∉ S₀)
  [∀ j, ContinuousSMul (GUr K (place j).1)
    (urRep (MonoidAlgebra ℤ Δ) (shapMod₀ W i s hs hs0 π) (newPlace (place j) (hw j))).V]
  [∀ j, ContinuousSMul (GUr K (place j).1)
    (urRep k (Mcoef K S₀ W i (alphaStage i s hs hs0 π ψ)) (newPlace (place j) (hw j))).V]
  (EU : ∀ j, SplitInclusion
    (genuineUq K S k (place j)
      (urRep k (Mcoef K S₀ W i (alphaStage i s hs hs0 π ψ)) (newPlace (place j) (hw j))))
    (genuineLq K S k (MinS hS W i (alphaStage i s hs hs0 π ψ)) (place j)))
  (hE : ∀ j, (EU j).i = genuineιq K S k (MinS hS W i (alphaStage i s hs hs0 π ψ)) (place j)
    (urRep k (Mcoef K S₀ W i (alphaStage i s hs hs0 π ψ)) (newPlace (place j) (hw j)))
    (urId hS k (Mcoef K S₀ W i (alphaStage i s hs hs0 π ψ)) (newPlace (place j) (hw j)))
    (urId_compat hS k (Mcoef K S₀ W i (alphaStage i s hs hs0 π ψ)) (place j) (hw j)))

include hE in
/-- **The norm identity at a switch of the presentation over `k`** (PROVED; tex 3203–3215,
3257–3290, 3471–3487, 4157–4170, 4385–4451): as `H20PresActual.hnorm_pres_actual`, over any ring
`k` with `k ≃+* A_i` (for lane RC32's stages `StageRing s`, `stageIsoA s`); point factor
`phiK e₁`. -/
theorem hnorm_presK (Tp : Finset ι) (p : ι)
    (aR aP : (globalCx (MonoidAlgebra ℤ Δ) (GKS K S) (shapMod hS W i s hs hs0 π)).X 1)
    (e₁ : MonoidAlgebra ℤ Δ)
    (bG : (globalCx (MonoidAlgebra ℤ Δ) (GKS K S) (shapMod hS W i s hs hs0 π)).X 0)
    (hG : aR = e₁ • aP + (globalCx (MonoidAlgebra ℤ Δ) (GKS K S) (shapMod hS W i s hs hs0 π)).d 0 1
      rfl bG)
    (holdR : ∀ v₀, ∃ u, ((shapConditions hS W i s hs hs0 hFull π ψ P hψ hΨ).i v₀).f 1 1 rfl u =
      (resS (MonoidAlgebra ℤ Δ) (GKS K S) (fun v : Places K S₀ => Gloc K v.1)
        (fun v => locMap K S v.1) (shapMod hS W i s hs hs0 π)).f 1 1 rfl aR v₀)
    (holdP : ∀ v₀, ∃ u, ((shapConditions hS W i s hs hs0 hFull π ψ P hψ hΨ).i v₀).f 1 1 rfl u =
      (resS (MonoidAlgebra ℤ Δ) (GKS K S) (fun v : Places K S₀ => Gloc K v.1)
        (fun v => locMap K S v.1) (shapMod hS W i s hs hs0 π)).f 1 1 rfl aP v₀)
    (hurR : ∀ j, j.1 ∉ insert p Tp → ∃ u,
      (genuineιq K S (MonoidAlgebra ℤ Δ) (shapMod hS W i s hs hs0 π) (place j)
        (urRep (MonoidAlgebra ℤ Δ) (shapMod₀ W i s hs hs0 π) (newPlace (place j) (hw j)))
        (urId hS (MonoidAlgebra ℤ Δ) (shapMod₀ W i s hs hs0 π) (newPlace (place j) (hw j)))
        (urId_compat hS (MonoidAlgebra ℤ Δ) (shapMod₀ W i s hs hs0 π) (place j) (hw j))).f 1 1 rfl
          u =
      (natHom (resCochains (k := MonoidAlgebra ℤ Δ) (M := shapMod hS W i s hs hs0 π)
        (locMap K S (place j).1))).f 1 1 rfl aR)
    (hurP : ∀ j, j.1 ∉ Tp → ∃ u,
      (genuineιq K S (MonoidAlgebra ℤ Δ) (shapMod hS W i s hs hs0 π) (place j)
        (urRep (MonoidAlgebra ℤ Δ) (shapMod₀ W i s hs hs0 π) (newPlace (place j) (hw j)))
        (urId hS (MonoidAlgebra ℤ Δ) (shapMod₀ W i s hs hs0 π) (newPlace (place j) (hw j)))
        (urId_compat hS (MonoidAlgebra ℤ Δ) (shapMod₀ W i s hs hs0 π) (place j) (hw j))).f 1 1 rfl
          u =
      (natHom (resCochains (k := MonoidAlgebra ℤ Δ) (M := shapMod hS W i s hs hs0 π)
        (locMap K S (place j).1))).f 1 1 rfl aP) :
    ∃ (zR : (suppCxS K S₀ S k (MinS hS W i (alphaStage i s hs hs0 π ψ))
        (stageCondsK hS W i s hs hs0 hFull π ψ P hΨ k) place
        (fun j => urRep k (Mcoef K S₀ W i (alphaStage i s hs hs0 π ψ)) (newPlace (place j) (hw j))) EU (insert p Tp)).X 1)
      (z : (suppCxS K S₀ S k (MinS hS W i (alphaStage i s hs hs0 π ψ))
        (stageCondsK hS W i s hs hs0 hFull π ψ P hΨ k) place
        (fun j => urRep k (Mcoef K S₀ W i (alphaStage i s hs hs0 π ψ)) (newPlace (place j) (hw j))) EU Tp).X 1)
      (b : (suppCxS K S₀ S k (MinS hS W i (alphaStage i s hs hs0 π ψ))
        (stageCondsK hS W i s hs hs0 hFull π ψ P hΨ k) place
        (fun j => urRep k (Mcoef K S₀ W i (alphaStage i s hs hs0 π ψ)) (newPlace (place j) (hw j))) EU (insert p Tp)).X 0),
      zR.1 = gPushK hS W i s hs hs0 π ψ k 1 aR ∧ z.1 = gPushK hS W i s hs hs0 π ψ k 1 aP ∧
      zR = phiK i ψ k e₁ • (suppSwitchS K S₀ S k (MinS hS W i (alphaStage i s hs hs0 π ψ))
          (stageCondsK hS W i s hs hs0 hFull π ψ P hΨ k) place
          (fun j => urRep k (Mcoef K S₀ W i (alphaStage i s hs hs0 π ψ)) (newPlace (place j) (hw j))) EU Tp p).i.f 1 1 rfl z +
        (suppCxS K S₀ S k (MinS hS W i (alphaStage i s hs hs0 π ψ))
        (stageCondsK hS W i s hs hs0 hFull π ψ P hΨ k) place
        (fun j => urRep k (Mcoef K S₀ W i (alphaStage i s hs hs0 π ψ)) (newPlace (place j) (hw j))) EU (insert p Tp)).d 0 1 rfl b :=
  hnorm_pres K S₀ S k (MinS hS W i (alphaStage i s hs hs0 π ψ))
    (stageCondsK hS W i s hs hs0 hFull π ψ P hΨ k) place
    (fun j => urRep k (Mcoef K S₀ W i (alphaStage i s hs hs0 π ψ)) (newPlace (place j) (hw j))) EU Tp p
    (gPushK hS W i s hs hs0 π ψ k 1 aR) (gPushK hS W i s hs hs0 π ψ k 1 aP) (phiK i ψ k e₁)
    (gPushK hS W i s hs hs0 π ψ k 0 bG)
    (stageCondK_injective hS W i s hs hs0 hFull π ψ P hΨ k)
    (stageCondK_surjective₀ hS W i s hs hs0 hFull π ψ P hΨ k)
    (fun j => by
      rw [hE j]
      exact genuineιq_surjective₀ (place j) _ _ _ Function.surjective_id)
    (stage_globalK hS W i s hs hs0 π ψ k aR aP e₁ bG hG)
    (fun v₀ => stage_oldLiftK hS W i s hs hs0 hFull π ψ P hψ hΨ k v₀ aR (holdR v₀))
    (fun v₀ => stage_oldLiftK hS W i s hs hs0 hFull π ψ P hψ hΨ k v₀ aP (holdP v₀))
    (fun j hj => by
      rw [hE j]
      exact stage_urLiftK hS W i s hs hs0 π ψ k (place j) (hw j) aR (hurR j hj))
    (fun j hj => by
      rw [hE j]
      exact stage_urLiftK hS W i s hs hs0 π ψ k (place j) (hw j) aP (hurP j hj))

variable {D : Type} [AddCommGroup D] [Module (MonoidAlgebra ℤ Δ) D]
  (ρ : GKS K S →* Module.End (MonoidAlgebra ℤ Δ) D)
  (HP HR : Subgroup (GKS K S)) [HP.Normal] [HR.Normal] [Fintype (GKS K S ⧸ HP)]
  [Fintype (GKS K S ⧸ HR)]
  (rP : GKS K S ⧸ HP → GKS K S) (hrP : ∀ δ, ((rP δ : GKS K S) : GKS K S ⧸ HP) = δ)
  (rR : GKS K S ⧸ HR → GKS K S) (hrR : ∀ δ, ((rR δ : GKS K S) : GKS K S ⧸ HR) = δ)
  (θP : GKS K S ⧸ HP →* (MonoidAlgebra ℤ Δ)ˣ) (θR : GKS K S ⧸ HR →* (MonoidAlgebra ℤ Δ)ˣ)
  (U : Subgroup HP) (hU : ∀ h : HP, h ∈ U ↔ (h : GKS K S) ∈ HR) [Fintype (HP ⧸ U)]
  (t : HP ⧸ U → HP) (ht : ∀ τ : HP ⧸ U, (QuotientGroup.mk (t τ) : HP ⧸ U) = τ)

open scoped Classical in
include hrP hrR hU ht hE hψ in
/-- **The norm identity at each switch of the presentation over `k` from the transfer inputs**
(PROVED; tex 4142–4194, 4157–4170, 4385–4451): the input `hnorm` of lane RC32's `CMStepHyps` over
any stage ring `k ≃+* A_i` (for lane RC32's `StageRing s`: `stageIsoA s`), from the named inputs of
`h1_shapiro` and the unramified lifts (`H20AmbientS.hur_actualS`; `H20Untwisted.hur_actualUH` when
the fixed fields of the transfer subgroups lie in `K_{S₀}`); point factor `phiK (e_q)`. -/
theorem hnorm_pres_of_transferK (Tp : Finset ι) (p : ι)
    (aR aP : (globalCx (MonoidAlgebra ℤ Δ) (GKS K S) (shapMod hS W i s hs hs0 π)).X 1)
    (hle : HR ≤ HP)
    (hθ : ∀ x : GKS K S, ((θR (x : GKS K S ⧸ HR) : (MonoidAlgebra ℤ Δ)ˣ) : MonoidAlgebra ℤ Δ) =
      θP (x : GKS K S ⧸ HP))
    (a : ℤ) (σ : GKS K S) {yR yP QR QP : D}
    (hQR : ((2 ^ i : ℕ) : ℤ) • QR = yR) (hQP : ((2 ^ i : ℕ) : ℤ) • QP = yP)
    (hfixR : ∀ h ∈ HR, ρ h yR = yR) (hfixP : ∀ h ∈ HP, ρ h yP = yP)
    (hnorm : ∑ τ : HP ⧸ U, ρ (t τ : GKS K S) yR = a • yP - ρ σ yP - ρ σ⁻¹ yP)
    (ιD : shapMod hS W i s hs hs0 π →ₗ[MonoidAlgebra ℤ Δ] D) (hι : Function.Injective ιD)
    (hιeq : ∀ (g : GKS K S) (m : shapMod hS W i s hs hs0 π), ιD (g • m) = R HR ρ θR g (ιD m))
    (htors : ∀ x : D, ((2 ^ i : ℕ) : ℤ) • x = 0 → ∃ m, ιD m = x)
    (hzR : ∀ g : Fin 1 → GKS K S,
      ιD (gval (A := MonoidAlgebra ℤ Δ) (M := shapMod hS W i s hs hs0 π) aR g) =
        T HR rR hrR ρ θR 1 (kummerCochain ρ HR QR) g)
    (hzP : ∀ g : Fin 1 → GKS K S,
      ιD (gval (A := MonoidAlgebra ℤ Δ) (M := shapMod hS W i s hs hs0 π) aP g) =
        T HP rP hrP ρ θP 1 (kummerCochain ρ HP QP) g)
    (hinR : ∀ v : Places K S₀, v.1 ∈ P →
      haveI := isElliptic_localTwist W (ne_zero_of_sqrt s hs hs0) v.1
      OldPlaceInput ρ HR rR θR v.1 (localTwist W h v.1) (2 ^ i)
        (shapIota hS W i s hs hs0 hFull π ⟨v.1, hS v.2⟩) ιD yR)
    (hinP : ∀ v : Places K S₀, v.1 ∈ P →
      haveI := isElliptic_localTwist W (ne_zero_of_sqrt s hs hs0) v.1
      OldPlaceInput ρ HP rP θP v.1 (localTwist W h v.1) (2 ^ i)
        (shapIota hS W i s hs hs0 hFull π ⟨v.1, hS v.2⟩) ιD yP)
    (hurR : ∀ j, j.1 ∉ insert p Tp → ∃ u,
      (genuineιq K S (MonoidAlgebra ℤ Δ) (shapMod hS W i s hs hs0 π) (place j)
        (urRep (MonoidAlgebra ℤ Δ) (shapMod₀ W i s hs hs0 π) (newPlace (place j) (hw j)))
        (urId hS (MonoidAlgebra ℤ Δ) (shapMod₀ W i s hs hs0 π) (newPlace (place j) (hw j)))
        (urId_compat hS (MonoidAlgebra ℤ Δ) (shapMod₀ W i s hs hs0 π) (place j) (hw j))).f 1 1 rfl
          u =
      (natHom (resCochains (k := MonoidAlgebra ℤ Δ) (M := shapMod hS W i s hs hs0 π)
        (locMap K S (place j).1))).f 1 1 rfl aR)
    (hurP : ∀ j, j.1 ∉ Tp → ∃ u,
      (genuineιq K S (MonoidAlgebra ℤ Δ) (shapMod hS W i s hs hs0 π) (place j)
        (urRep (MonoidAlgebra ℤ Δ) (shapMod₀ W i s hs hs0 π) (newPlace (place j) (hw j)))
        (urId hS (MonoidAlgebra ℤ Δ) (shapMod₀ W i s hs hs0 π) (newPlace (place j) (hw j)))
        (urId_compat hS (MonoidAlgebra ℤ Δ) (shapMod₀ W i s hs hs0 π) (place j) (hw j))).f 1 1 rfl
          u =
      (natHom (resCochains (k := MonoidAlgebra ℤ Δ) (M := shapMod hS W i s hs hs0 π)
        (locMap K S (place j).1))).f 1 1 rfl aP) :
    ∃ (zR : (suppCxS K S₀ S k (MinS hS W i (alphaStage i s hs hs0 π ψ))
        (stageCondsK hS W i s hs hs0 hFull π ψ P hΨ k) place
        (fun j => urRep k (Mcoef K S₀ W i (alphaStage i s hs hs0 π ψ)) (newPlace (place j) (hw j))) EU (insert p Tp)).X 1)
      (z : (suppCxS K S₀ S k (MinS hS W i (alphaStage i s hs hs0 π ψ))
        (stageCondsK hS W i s hs hs0 hFull π ψ P hΨ k) place
        (fun j => urRep k (Mcoef K S₀ W i (alphaStage i s hs hs0 π ψ)) (newPlace (place j) (hw j))) EU Tp).X 1)
      (b : (suppCxS K S₀ S k (MinS hS W i (alphaStage i s hs hs0 π ψ))
        (stageCondsK hS W i s hs hs0 hFull π ψ P hΨ k) place
        (fun j => urRep k (Mcoef K S₀ W i (alphaStage i s hs hs0 π ψ)) (newPlace (place j) (hw j))) EU (insert p Tp)).X 0),
      zR.1 = gPushK hS W i s hs hs0 π ψ k 1 aR ∧ z.1 = gPushK hS W i s hs hs0 π ψ k 1 aP ∧
      zR = phiK i ψ k (eq_ HP θP a σ) • (suppSwitchS K S₀ S k (MinS hS W i (alphaStage i s hs hs0 π ψ))
          (stageCondsK hS W i s hs hs0 hFull π ψ P hΨ k) place
          (fun j => urRep k (Mcoef K S₀ W i (alphaStage i s hs hs0 π ψ)) (newPlace (place j) (hw j))) EU Tp p).i.f 1 1 rfl z +
        (suppCxS K S₀ S k (MinS hS W i (alphaStage i s hs hs0 π ψ))
        (stageCondsK hS W i s hs hs0 hFull π ψ P hΨ k) place
        (fun j => urRep k (Mcoef K S₀ W i (alphaStage i s hs hs0 π ψ)) (newPlace (place j) (hw j))) EU (insert p Tp)).d 0 1 rfl b := by
  have hιeqP : ∀ (g : GKS K S) (m : shapMod hS W i s hs hs0 π),
      ιD (g • m) = R HP ρ θP g (ιD m) :=
    fun g m => by rw [hιeq]; simp only [R, hθ]
  obtain ⟨bG, hG⟩ := hG_of_transfer ρ HP HR rP hrP rR hrR θP θR U hU t ht hle hθ
    ((2 ^ i : ℕ) : ℤ) a σ hQR hQP hfixR hfixP hnorm ιD hι hιeq htors aR aP hzR hzP
  obtain ⟨uR, huR⟩ := exists_oldLift_shap hS W i s hs hs0 hFull π ψ P hψ hΨ ρ HR rR hrR θR ιD
    hιeq hQR hinR aR hzR
  obtain ⟨uP, huP⟩ := exists_oldLift_shap hS W i s hs hs0 hFull π ψ P hψ hΨ ρ HP rP hrP θP ιD
    hιeqP hQP hinP aP hzP
  exact hnorm_presK hS W i s hs hs0 hFull π ψ P hψ hΨ k place hw EU hE Tp p aR aP
    (eq_ HP θP a σ) bG hG (fun v₀ => ⟨uR v₀, congrFun huR v₀⟩) (fun v₀ => ⟨uP v₀, congrFun huP v₀⟩)
    hurR hurP

end StageK

end ZInQ.Contrib.CloudB3E2.NormCochain
