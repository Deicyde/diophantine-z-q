import ZInQKernel.Contrib.CloudB3E2Norm.H20PresActual

/-!
# The norm identity on the one presentation from the transfer inputs

Manuscript `diophantine_zq.tex`, Lemma `ex:arith-common-coordinate` (tex 4142–4194, 4157–4170) on
lane RC32's one presentation of the support complexes for lane RC29's actual stage data
(tex 3203–3215, 3257–3290, 3471–3487, 4385–4451).

**`hnorm_pres_actual_of_transfer`** (PROVED): at each switch `C_T ⊂ C_{T ∪ {p}}` of the
presentation over `A_i`, the pushes of the transferred Shapiro-level classes `a_R`, `a_P` (carried
by `ι` to `𝒯_{θ_R}(κ(Q_R))` and `𝒯_{θ_P}(κ(Q_P))`) have strict lifts with
`z_R = φ(e_q) · i(z) + d b`, `e_q = a_q − z − z⁻¹` with `z = θ(σ_q)` (for the untwisted instance
`z = χ_h(σ_q)[π σ_q]`) — the input `hnorm` of lane RC32's
`CMStepHyps` — from the same named inputs as `H20Assembly.h1_shapiro`:

* the norm relation `hnorm` (`H20DictFields.hnorm_of_full_anchor`, from the unweighted norm
  relations, derived from the Cai–Chen–Liu print `CCLThm2_15AppliedWithUnits`), the division
  points `hQR`, `hQP`, the fixedness `hfixR`, `hfixP`, the coefficient/twist data `ι`, `hι`, `hιeq`,
  `htors` (`H20Twist.lean`), the classes `hzR`, `hzP` (`GlobalCochain.exists_gval_eq_transfer`);
* the old-place inputs `hinR`, `hinP` (`OldPlaceInput`; `H20Twist.oldPlaceInput_actual` reduces
  each to its realization `hreal`);
* the unramified lifts at the places above the unused primes: of `a_R` above `q ∉ T ∪ {p}` and of
  `a_P` above `q ∉ T` (`hPw`; for the ambient module of points and the transfer subgroup
  `ker(π ∘ infl)`, `H20Inertia.hPw_actual` gives each of them with no further input).

The global identity is `GlobalCochain.hG_of_transfer`, the old lifts `H20Assembly.exists_oldLift_shap`,
and the rest is `H20PresActual.hnorm_pres_actual`.

**`hur_actual`** (PROVED): for the ambient module of points (`ambRho`, `ambIota`) and the transfer
subgroup `ker(π ∘ infl)` with `θ = thetaPi`, the unramified lifts `hurR`/`hurP` hold at every place
above an unused prime (`H20Inertia.hPw_actual`).

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

section Assembly

variable {K : Type} [Field K] [NumberField K] {S S₀ : Set (HeightOneSpectrum (𝓞 K))}
  (hS : S₀ ⊆ S) (W : WeierstrassCurve K) [W.IsElliptic] (i : ℕ) [NeZero i] (s : KS K S₀) {h : K}
  (hs : s ^ 2 = algebraMap K (KS K S₀) h) (hs0 : s ≠ 0) (hFull : FullTorsion K S₀ W (2 ^ i))
  [TopologicalSpace (Acoef i)] [DiscreteTopology (Acoef i)]
  {Δ : Type} [CommGroup Δ] [Finite Δ] (π : GKS K S₀ →* Δ) (ψ : Δ →* (Acoef i)ˣ)
  [IsOpenKer (alphaShap s hs hs0 π)] [IsOpenKer (alphaStage i s hs hs0 π ψ)]
  (P : Set (HeightOneSpectrum (𝓞 K))) (hψ : Function.Injective ψ) (hΨ : PsiTrivialAt2N i π ψ P)
  {D : Type} [AddCommGroup D] [Module (MonoidAlgebra ℤ Δ) D]
  (ρ : GKS K S →* Module.End (MonoidAlgebra ℤ Δ) D)
  (HP HR : Subgroup (GKS K S)) [HP.Normal] [HR.Normal] [Fintype (GKS K S ⧸ HP)]
  [Fintype (GKS K S ⧸ HR)]
  (rP : GKS K S ⧸ HP → GKS K S) (hrP : ∀ δ, ((rP δ : GKS K S) : GKS K S ⧸ HP) = δ)
  (rR : GKS K S ⧸ HR → GKS K S) (hrR : ∀ δ, ((rR δ : GKS K S) : GKS K S ⧸ HR) = δ)
  (θP : GKS K S ⧸ HP →* (MonoidAlgebra ℤ Δ)ˣ) (θR : GKS K S ⧸ HR →* (MonoidAlgebra ℤ Δ)ˣ)
  (U : Subgroup HP) (hU : ∀ h : HP, h ∈ U ↔ (h : GKS K S) ∈ HR) [Fintype (HP ⧸ U)]
  (t : HP ⧸ U → HP) (ht : ∀ τ : HP ⧸ U, (QuotientGroup.mk (t τ) : HP ⧸ U) = τ)
  [DecidableEq (Places K S₀)] {ι : Type} [DecidableEq ι] (place : ι × Bool → Places K S)
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

open scoped Classical in
include hrP hrR hU ht hE hψ in
/-- **The norm identity at each switch of the presentation from the transfer inputs** (PROVED;
tex 4142–4194, 4157–4170, 3203–3215, 3257–3290, 3471–3487, 4385–4451): the input `hnorm` of lane
RC32's `CMStepHyps` for RC29's actual stage data, with point factor `φ(e_q)`. -/
theorem hnorm_pres_actual_of_transfer (Tp : Finset ι) (p : ι)
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
    ∃ (zR : (suppCxS K S₀ S (Acoef i) (MinS hS W i (alphaStage i s hs hs0 π ψ))
        (stageConditions hS W i s hs hs0 hFull π ψ P hΨ) place
        (fun j => urRep (Acoef i) (Mcoef K S₀ W i (alphaStage i s hs hs0 π ψ))
          (newPlace (place j) (hw j))) EU (insert p Tp)).X 1)
      (z : (suppCxS K S₀ S (Acoef i) (MinS hS W i (alphaStage i s hs hs0 π ψ))
        (stageConditions hS W i s hs hs0 hFull π ψ P hΨ) place
        (fun j => urRep (Acoef i) (Mcoef K S₀ W i (alphaStage i s hs hs0 π ψ))
          (newPlace (place j) (hw j))) EU Tp).X 1)
      (b : (suppCxS K S₀ S (Acoef i) (MinS hS W i (alphaStage i s hs hs0 π ψ))
        (stageConditions hS W i s hs hs0 hFull π ψ P hΨ) place
        (fun j => urRep (Acoef i) (Mcoef K S₀ W i (alphaStage i s hs hs0 π ψ))
          (newPlace (place j) (hw j))) EU (insert p Tp)).X 0),
      zR.1 = gPush hS W i s hs hs0 π ψ 1 aR ∧ z.1 = gPush hS W i s hs hs0 π ψ 1 aP ∧
      zR = h20RingHom ψ (eq_ HP θP a σ) •
          (suppSwitchS K S₀ S (Acoef i) (MinS hS W i (alphaStage i s hs hs0 π ψ))
          (stageConditions hS W i s hs hs0 hFull π ψ P hΨ) place
          (fun j => urRep (Acoef i) (Mcoef K S₀ W i (alphaStage i s hs hs0 π ψ))
            (newPlace (place j) (hw j))) EU Tp p).i.f 1 1 rfl z +
        (suppCxS K S₀ S (Acoef i) (MinS hS W i (alphaStage i s hs hs0 π ψ))
          (stageConditions hS W i s hs hs0 hFull π ψ P hΨ) place
          (fun j => urRep (Acoef i) (Mcoef K S₀ W i (alphaStage i s hs hs0 π ψ))
            (newPlace (place j) (hw j))) EU (insert p Tp)).d 0 1 rfl b := by
  have hιeqP : ∀ (g : GKS K S) (m : shapMod hS W i s hs hs0 π),
      ιD (g • m) = R HP ρ θP g (ιD m) :=
    fun g m => by rw [hιeq]; simp only [R, hθ]
  obtain ⟨bG, hG⟩ := hG_of_transfer ρ HP HR rP hrP rR hrR θP θR U hU t ht hle hθ
    ((2 ^ i : ℕ) : ℤ) a σ hQR hQP hfixR hfixP hnorm ιD hι hιeq htors aR aP hzR hzP
  obtain ⟨uR, huR⟩ := exists_oldLift_shap hS W i s hs hs0 hFull π ψ P hψ hΨ ρ HR rR hrR θR ιD
    hιeq hQR hinR aR hzR
  obtain ⟨uP, huP⟩ := exists_oldLift_shap hS W i s hs hs0 hFull π ψ P hψ hΨ ρ HP rP hrP θP ιD
    hιeqP hQP hinP aP hzP
  exact hnorm_pres_actual hS W i s hs hs0 hFull π ψ P hψ hΨ place hw EU hE Tp p aR aP
    (eq_ HP θP a σ) bG hG (fun v₀ => ⟨uR v₀, congrFun huR v₀⟩) (fun v₀ => ⟨uP v₀, congrFun huP v₀⟩)
    hurR hurP

end Assembly

/-! ### The unramified lifts for the ambient module of points -/

section Unramified

variable {K : Type} [Field K] [NumberField K] {S S₀ : Set (HeightOneSpectrum (𝓞 K))}
  (hS : S₀ ⊆ S) (W : WeierstrassCurve K) [W.IsElliptic] (i : ℕ) [NeZero i] (s : KS K S₀) {h : K}
  (hs : s ^ 2 = algebraMap K (KS K S₀) h) (hs0 : s ≠ 0)
  [TopologicalSpace (Acoef i)] [DiscreteTopology (Acoef i)]
  {Δ : Type} [CommGroup Δ] [Finite Δ] (π : GKS K S₀ →* Δ) [IsOpenKer (alphaShap s hs hs0 π)]
  {ι : Type} (place : ι × Bool → Places K S) (hw : ∀ j, (place j).1 ∉ S₀)
  [∀ j, ContinuousSMul (GUr K (place j).1)
    (urRep (MonoidAlgebra ℤ Δ) (shapMod₀ W i s hs hs0 π) (newPlace (place j) (hw j))).V]

/-- **The unramified lifts `hurR`/`hurP` for the ambient module of points** (PROVED;
`H20Inertia.hPw_actual`): a genuine class carried by `ambIota` to `𝒯_{[π]}(κ(Q))` over the transfer
subgroup `ker(π ∘ infl)` has an unramified lift at every place above an unused prime.
**Superseded for the wiring** (see `H20Untwisted.lean`): the statement is valid, but with the
`χ_h`-twisted ambient module the norm relation needed by `h1_shapiro` holds only when `χ_h(σ_q) =
1`, and the point factor loses the text's sign `z = χ_h(σ_q) Ψ(σ_q)` (tex 3915, 4158–4172); wire the
untwisted instance instead (for the relaxed points over a ramified ring class field, the ambient
module over a larger support, `H20AmbientS.hur_actualS`). -/
theorem hur_actual [Fintype (GKS K S ⧸ (piInfl hS π).ker)]
    (r : GKS K S ⧸ (piInfl hS π).ker → GKS K S)
    (hr : ∀ δ, ((r δ : GKS K S) : GKS K S ⧸ (piInfl hS π).ker) = δ)
    (kk : ℤ) {Q y : ambD hS W s hs hs0 (Δ := Δ)} (hQ : kk • Q = y)
    (a : (globalCx (MonoidAlgebra ℤ Δ) (GKS K S) (shapMod hS W i s hs hs0 π)).X 1)
    (hz : ∀ g : Fin 1 → GKS K S,
      ambIota hS W i s hs hs0 π (gval (A := MonoidAlgebra ℤ Δ) (M := shapMod hS W i s hs hs0 π) a g) =
        T (piInfl hS π).ker r hr (ambRho hS W s hs hs0 (Δ := Δ)) (thetaPi hS π) 1
          (kummerCochain (ambRho hS W s hs hs0 (Δ := Δ)) (piInfl hS π).ker Q) g)
    (j : ι × Bool) :
    ∃ u, (genuineιq K S (MonoidAlgebra ℤ Δ) (shapMod hS W i s hs hs0 π) (place j)
        (urRep (MonoidAlgebra ℤ Δ) (shapMod₀ W i s hs hs0 π) (newPlace (place j) (hw j)))
        (urId hS (MonoidAlgebra ℤ Δ) (shapMod₀ W i s hs hs0 π) (newPlace (place j) (hw j)))
        (urId_compat hS (MonoidAlgebra ℤ Δ) (shapMod₀ W i s hs hs0 π) (place j) (hw j))).f 1 1 rfl
          u =
      (natHom (resCochains (k := MonoidAlgebra ℤ Δ) (M := shapMod hS W i s hs hs0 π)
        (locMap K S (place j).1))).f 1 1 rfl a :=
  hPw_actual hS W i s hs hs0 π (place j) (hw j) r hr kk hQ a hz

end Unramified

end ZInQ.Contrib.CloudB3E2.NormCochain
