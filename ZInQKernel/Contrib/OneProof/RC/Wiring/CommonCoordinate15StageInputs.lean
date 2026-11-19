import ZInQKernel.Contrib.OneProof.RC.Wiring.RetentionGenuineFunctionals
import ZInQKernel.Contrib.CloudB3E2Norm.H20Assembly
import ZInQKernel.Contrib.CloudB3RC53.SelmerDuality.SelfInjective
import ZInQKernel.Contrib.OneProof.RC.Limits.Ultralimit

/-!
# The step inputs of the chain of relaxations at a stage ring

Manuscript `diophantine_zq.tex`, proof of Lemma `ex:arith-common-coordinate` (tex 4157–4194: "The
actual norm identity is `z_R = e_q i(z_P)`, with its retained boundary", "Consequently
`λ_R ∘ i = e_q λ_P`"), read at a finite coefficient stage of the inner limit (Lemma
`ex:limits-inner-limit`, tex 4385–4451; the stages `A_i = (ℤ/2^i)[t]/t^i ≅ Λ ⧸ (2^i, t^i)`,
tex 2725, 2747). Lane RC32's chain of relaxations (`CommonCoordinate13Chain.lean`, `ChainHyps`)
takes at every step the norm identity with its retained boundary and the functional relation on
cocycles; this file supplies the stage-ring forms of these step inputs.

## (a) The functional relation up to a coboundary over a self-injective ring

* `exists_comp_of_vanish_inj` (PROVED): over a self-injective commutative ring `A`
  (`Module.Injective A A`), a functional `δ` vanishing on `ker d` is `μ ∘ d`: `δ` factors
  through `V ⧸ ker d ≃ range d ⊆ W` and extends from `range d` to `W` by injectivity of `A`. The
  field case is `exists_comp_of_vanish` (`CommonCoordinate12Cob.lean`).
* `exists_cob_of_natural_inj` (PROVED): for a chain map `i : C_P → C_R` of complexes over `A`
  and functionals with `λ_R(i w) = e λ_P(w)` on the cocycles `w ∈ C_P²`, some `μ : C_P³ → A`
  gives `λ_R ∘ i = e λ_P + μ ∘ d` on all of `C_P²` (the shape of the input `hlamR` of
  `SupportTriangle.kmStep_of_supportTriangle_cob`).

## (b) The functional relation from retention at a stage ring

* `PlaceRetentionG.exists_cob_inj` (PROVED): lane RC30's
  `PlaceRetentionG.pairedFunctional_natural` (over any commutative ring) with (a): for retention
  data `PR`, the paired functionals `λ_R = pairedFun PR.toRetainedPairing.QR tr z_S` and
  `λ_P = pairedFun PR.toRetainedPairing.QP tr z_{P⊥}` satisfy `λ_R ∘ i = e λ_P + μ ∘ d` on
  `C_P²`, `i = changeMap DR fP`, over a self-injective coefficient ring (by (d), every stage ring
  is one).

## (c) The stage norm identity of lane E2: its statement and its named inputs

Lane E2's theorem `ZInQ.Contrib.CloudB3E2.NormCochain.hzR_stage_actual_of_inputs`
(`H20Assembly.lean`; proved there by `h1_shapiro`, the Shapiro-level identity over `ℤ[Δ]`,
followed by `hzR_stage_actual`, the coefficient push (H20) to `A_i`, `H20Actual.lean`) has the
exact statement below: the section variables of its file first, in their order, then its own
binders; it is stated under `open scoped Classical`, with the local instances
`TopRep.distribMulAction`, `TopRep.smulCommClass`, `groupRingTop`. `hzR_stage_of_E2` restates it
with the same binders and the same conclusion.

```
theorem hzR_stage_actual_of_inputs {K : Type} [Field K] [NumberField K]
    {S S₀ : Set (HeightOneSpectrum (𝓞 K))} (hS : S₀ ⊆ S) (W : WeierstrassCurve K)
    [W.IsElliptic] (i : ℕ) [NeZero i] (s : KS K S₀) {h : K}
    (hs : s ^ 2 = algebraMap K (KS K S₀) h) (hs0 : s ≠ 0) (hFull : FullTorsion K S₀ W (2 ^ i))
    [TopologicalSpace (Acoef i)] [DiscreteTopology (Acoef i)]
    {Δ : Type} [CommGroup Δ] [Finite Δ] (π : GKS K S₀ →* Δ) (ψ : Δ →* (Acoef i)ˣ)
    [IsOpenKer (alphaShap s hs hs0 π)] [IsOpenKer (alphaStage i s hs hs0 π ψ)]
    (P : Set (HeightOneSpectrum (𝓞 K))) (hψ : Function.Injective ψ)
    (hΨ : PsiTrivialAt2N i π ψ P)
    {D : Type} [AddCommGroup D] [Module (MonoidAlgebra ℤ Δ) D]
    (ρ : GKS K S →* Module.End (MonoidAlgebra ℤ Δ) D)
    (HP HR : Subgroup (GKS K S)) [HP.Normal] [HR.Normal] [Fintype (GKS K S ⧸ HP)]
    [Fintype (GKS K S ⧸ HR)]
    (rP : GKS K S ⧸ HP → GKS K S) (hrP : ∀ δ, ((rP δ : GKS K S) : GKS K S ⧸ HP) = δ)
    (rR : GKS K S ⧸ HR → GKS K S) (hrR : ∀ δ, ((rR δ : GKS K S) : GKS K S ⧸ HR) = δ)
    (θP : GKS K S ⧸ HP →* (MonoidAlgebra ℤ Δ)ˣ) (θR : GKS K S ⧸ HR →* (MonoidAlgebra ℤ Δ)ˣ)
    (U : Subgroup HP) (hU : ∀ h : HP, h ∈ U ↔ (h : GKS K S) ∈ HR) [Fintype (HP ⧸ U)]
    (t : HP ⧸ U → HP) (ht : ∀ τ : HP ⧸ U, (QuotientGroup.mk (t τ) : HP ⧸ U) = τ)
    (w : Places K S) (hw : w.1 ∉ S₀)
    [ContinuousSMul (GUr K w.1)
      (urRep (MonoidAlgebra ℤ Δ) (shapMod₀ W i s hs hs0 π) (newPlace w hw)).V]
    [ContinuousSMul (GUr K w.1)
      (urRep (Acoef i) (Mcoef K S₀ W i (alphaStage i s hs hs0 π ψ)) (newPlace w hw)).V]
    (aR aP : (globalCx (MonoidAlgebra ℤ Δ) (GKS K S) (shapMod hS W i s hs hs0 π)).X 1)
    (hle : HR ≤ HP)
    (hθ : ∀ x : GKS K S, ((θR (x : GKS K S ⧸ HR) : (MonoidAlgebra ℤ Δ)ˣ) : MonoidAlgebra ℤ Δ) =
      θP (x : GKS K S ⧸ HP))
    (a : ℤ) (σ : GKS K S) {yR yP QR QP : D}
    (hQR : ((2 ^ i : ℕ) : ℤ) • QR = yR) (hQP : ((2 ^ i : ℕ) : ℤ) • QP = yP)
    (hfixR : ∀ h ∈ HR, ρ h yR = yR) (hfixP : ∀ h ∈ HP, ρ h yP = yP)
    (hnorm : ∑ τ : HP ⧸ U, ρ (t τ : GKS K S) yR = a • yP - ρ σ yP - ρ σ⁻¹ yP)
    (ι : shapMod hS W i s hs hs0 π →ₗ[MonoidAlgebra ℤ Δ] D) (hι : Function.Injective ι)
    (hιeq : ∀ (g : GKS K S) (m : shapMod hS W i s hs hs0 π), ι (g • m) = R HR ρ θR g (ι m))
    (htors : ∀ x : D, ((2 ^ i : ℕ) : ℤ) • x = 0 → ∃ m, ι m = x)
    (hzR : ∀ g : Fin 1 → GKS K S,
      ι (gval (A := MonoidAlgebra ℤ Δ) (M := shapMod hS W i s hs hs0 π) aR g) =
        T HR rR hrR ρ θR 1 (kummerCochain ρ HR QR) g)
    (hzP : ∀ g : Fin 1 → GKS K S,
      ι (gval (A := MonoidAlgebra ℤ Δ) (M := shapMod hS W i s hs hs0 π) aP g) =
        T HP rP hrP ρ θP 1 (kummerCochain ρ HP QP) g)
    (hinR : ∀ v : Places K S₀, v.1 ∈ P →
      haveI := isElliptic_localTwist W (ne_zero_of_sqrt s hs hs0) v.1
      OldPlaceInput ρ HR rR θR v.1 (localTwist W h v.1) (2 ^ i)
        (shapIota hS W i s hs hs0 hFull π ⟨v.1, hS v.2⟩) ι yR)
    (hinP : ∀ v : Places K S₀, v.1 ∈ P →
      haveI := isElliptic_localTwist W (ne_zero_of_sqrt s hs hs0) v.1
      OldPlaceInput ρ HP rP θP v.1 (localTwist W h v.1) (2 ^ i)
        (shapIota hS W i s hs hs0 hFull π ⟨v.1, hS v.2⟩) ι yP)
    (hPw : ∃ y : (genuineUq K S (MonoidAlgebra ℤ Δ) w
        (urRep (MonoidAlgebra ℤ Δ) (shapMod₀ W i s hs hs0 π) (newPlace w hw))).X 1,
      (genuineιq K S (MonoidAlgebra ℤ Δ) (shapMod hS W i s hs hs0 π) w
        (urRep (MonoidAlgebra ℤ Δ) (shapMod₀ W i s hs hs0 π) (newPlace w hw))
        (urId hS (MonoidAlgebra ℤ Δ) (shapMod₀ W i s hs hs0 π) (newPlace w hw))
        (urId_compat hS (MonoidAlgebra ℤ Δ) (shapMod₀ W i s hs hs0 π) w hw)).f 1 1 rfl y =
      (stageRes K S (MonoidAlgebra ℤ Δ) (shapMod hS W i s hs hs0 π) w).f 1 1 rfl aP) :
    ∃ (zR₂ : (selCx (stageRelaxed K S₀ S (Acoef i) (MinS hS W i (alphaStage i s hs hs0 π ψ))
        (stageConditions hS W i s hs hs0 hFull π ψ P hΨ) w)).X 1)
      (zP₂ : (selCx (selRestrict (stageRelaxed K S₀ S (Acoef i)
        (MinS hS W i (alphaStage i s hs hs0 π ψ))
        (stageConditions hS W i s hs hs0 hFull π ψ P hΨ) w)
        (primToRel (stageOld K S₀ S (Acoef i) (MinS hS W i (alphaStage i s hs hs0 π ψ))
          (stageConditions hS W i s hs hs0 hFull π ψ P hΨ))
          (stageRes K S (Acoef i) (MinS hS W i (alphaStage i s hs hs0 π ψ)) w)
          (genuineιq K S (Acoef i) (MinS hS W i (alphaStage i s hs hs0 π ψ)) w
            (urRep (Acoef i) (Mcoef K S₀ W i (alphaStage i s hs hs0 π ψ)) (newPlace w hw))
            (urId hS (Acoef i) (Mcoef K S₀ W i (alphaStage i s hs hs0 π ψ)) (newPlace w hw))
            (urId_compat hS (Acoef i) (Mcoef K S₀ W i (alphaStage i s hs hs0 π ψ)) w
              hw))))).X 1),
      ∃ b, zR₂ = h20RingHom ψ (eq_ HP θP a σ) • (changeMap _ _).f 1 1 rfl zP₂ +
        (selCx _).d 0 1 rfl b
```

Its named inputs, grouped as lane E2's file groups them:

* mathematical: the ELLIOT input `hΨ : PsiTrivialAt2N i π ψ P` (the moving character is trivial
  on the decomposition groups at the places of `P`, above `2N`; tex 2729, 3431, 3500–3506) with
  `hψ : Function.Injective ψ` (automatic for `Δ = im Ψ_i`, `moving_spec`); GLUE
  `LocalTwistIdentification` and the realization `hreal`, both inside `OldPlaceInput` (`hinR`
  for `y_R`, `hinP` for `y_P`; tex 3251–3270); the norm relation `hnorm` of the Heegner points
  (tex 4157–4170); the unramified localization `hPw` of the primitive class at `w`
  (tex 3471–3487); GLUE `hFull : FullTorsion K S₀ W (2 ^ i)` (lane RC28);
* structural (properties of the chosen ambient module of points `D` and coefficient embedding
  `ι`): `hfixR`, `hfixP` (the points `y_R`, `y_P` are defined over `H_R`, `H_P`), `hQR`, `hQP`
  (their division points), the character compatibility `hθ` and `hle : HR ≤ HP`, `hι`, `hιeq`
  (`ι` is injective and equivariant), `htors` (torsion lifting), `hzR`, `hzP` (the classes `aR`,
  `aP` are carried to `𝒯_θ(κ(Q_R))`, `𝒯_θ(κ(Q_P))`);
* infrastructure instances: `[IsOpenKer (alphaShap s hs hs0 π)]` and
  `[IsOpenKer (alphaStage i s hs hs0 π ψ)]` (open kernels of the characters;
  `isOpenKer_alphaShap`, `isOpenKer_alphaStage`), and the two
  `[ContinuousSMul (GUr K w.1) (urRep … (newPlace w hw)).V]` (discreteness of the unramified
  modules; `urRep_hyps_actual`).

The other binders are the setting: the curve `W` over `K`, `hS : S₀ ⊆ S`, the stage `i`, the
square root `s` of `h` (`hs`, `hs0`), a discrete topology on `A_i`, the finite group `Δ` with
`π`, `ψ`, the set of places `P`, the module of points `D` with `ρ`, the normal subgroups `HP`,
`HR` with section representatives `rP`, `rR` (`hrP`, `hrR`), the characters `θP`, `θR`, the
subgroup `U` with coset representatives `t` (`hU`, `ht`), the new place `w ∉ S₀` (`hw`), the
global cochains `aR`, `aP`, the integer `a`, `σ`, the points `yR`, `yP`, `QR`, `QP` and `ι`.
Which Selmer data and inclusion the conclusion is about, and what an adapter to round 9's
presentation would need, is recorded in the docstring of `hzR_stage_of_E2`.

## (d) Stage-ring instances: what the tree has, and what is added

In the tree: `acoef_selfInjective i : Module.Injective (Acoef i) (Acoef i)`, with
`selfInjective_of_frobeniusForm` (the RC53 group, `SelmerDuality/SelfInjective.lean`, namespace
`ZInQ.Contrib.CloudB3RC53.SelmerDuality`), a theorem and not an instance (it is used through
`have` in `StageProjectionModel.lean` and `AcoefDuality.lean`); `Lambda`, `stageIdeal`,
`StageA` and `stageEquiv : Λ ⧸ stageIdeal s ≃+* StageA s` (`RC/Limits/Ultralimit.lean`), where
`StageA s` and RC10's `Acoef s` are the same type (`stageA_eq_acoef`, `rfl`). Not found (in the
inner-limit files `RC53Assist/InnerLimitArith`, in `Ultralimit.lean` and the rest of
`RC/Limits`, in lane E2's `StageRing.lean` and its directory, in `RC/HeegnerAlgebra`,
`SelmerDuality` and `RC/Wiring`): a Noetherian statement for `Λ ⧸ stageIdeal s` or `A_s`, a
self-injectivity statement for `Λ ⧸ stageIdeal s`, and an instance form of either. Added here
(all PROVED):

* `acoef_moduleInjective` (instance): `Module.Injective (Acoef i) (Acoef i)`;
* `stageQuot_moduleInjective` (instance): `Λ ⧸ stageIdeal s` is self-injective, transported from
  `acoef_selfInjective` along `stageEquiv` (Mathlib's `Module.Injective.of_ringEquiv`);
* `stageQuot_isNoetherianRing`, `acoef_isNoetherianRing`: found by Mathlib's instances (for
  `Λ ⧸ stageIdeal s`: `ℤ₂` is a discrete valuation ring, power series over a Noetherian ring are
  Noetherian, a quotient of a Noetherian ring is Noetherian);
* `stageQuot_finite` (instance), `stageQuot_isArtinianRing`: `Λ ⧸ stageIdeal s` is finite, hence
  Artinian (Mathlib finds `Finite (Acoef s)`);
* `exists_cob_of_natural_acoef`, `exists_cob_of_natural_stage`: (a) at `A_i` and at
  `Λ ⧸ stageIdeal s`, through these instances.

Kinds: PROVED (the stage norm identity from lane E2's named inputs in (c)).
-/

noncomputable section

namespace ZInQ.Manuscript.RC.Wiring

open ZInQ.Contrib.CloudB3RC53.PairedFunctional ZInQ.Contrib.CloudB3RC53.SelmerDuality
  ZInQ.Contrib.CloudB3RC53.CommonCoordinate ZInQ.Manuscript.RC.SelmerComplex
open ZInQ.Manuscript.RC.HeegnerAlgebra (Acoef)

/-! ### (a) The functional relation up to a coboundary over a self-injective ring -/

/-- **A functional vanishing on the kernel factors through the map, over a self-injective ring**
(tex 4170–4177; the field case is `exists_comp_of_vanish`): if `A` is self-injective and `δ`
vanishes on `ker d`, then `δ = μ ∘ d` for some `μ : W → A`. The functional `δ` factors through
`V ⧸ ker d ≃ range d` (`Submodule.liftQ`, `LinearMap.quotKerEquivRange`), and the functional on
`range d ⊆ W` extends to `W` because `A` is an injective `A`-module (`Module.Injective.out`).
Kind: PROVED. -/
theorem exists_comp_of_vanish_inj {A V W : Type} [CommRing A] [Module.Injective A A]
    [AddCommGroup V] [Module A V] [AddCommGroup W] [Module A W] (d : V →ₗ[A] W)
    (δ : V →ₗ[A] A) (h : ∀ v, d v = 0 → δ v = 0) : ∃ μ : W →ₗ[A] A, δ = μ ∘ₗ d := by
  have hle : LinearMap.ker d ≤ LinearMap.ker δ := fun v hv => h v hv
  obtain ⟨μ, hμ⟩ := Module.Injective.out (R := A) (Q := A) (LinearMap.range d).subtype
    (Submodule.injective_subtype _)
    ((LinearMap.ker d).liftQ δ hle ∘ₗ d.quotKerEquivRange.symm.toLinearMap)
  refine ⟨μ, LinearMap.ext fun v => ?_⟩
  have hv := hμ ⟨d v, LinearMap.mem_range_self d v⟩
  rw [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearMap.quotKerEquivRange_symm_apply_image,
    Submodule.mkQ_apply, Submodule.liftQ_apply] at hv
  exact hv.symm

/-- **The functional relation on cocycles holds up to a coboundary, over a self-injective ring**
(tex 4157–4194, 4170–4177): for complexes `C_P`, `C_R` over `A`, a chain map `i : C_P → C_R`,
functionals `λ_R`, `λ_P` in degree two and `e : A` with `λ_R(i w) = e λ_P(w)` for every cocycle
`w ∈ C_P²`, some `μ : C_P³ → A` gives `λ_R ∘ i = e λ_P + μ ∘ d` (the input `hlamR` of
`SupportTriangle.kmStep_of_supportTriangle_cob`, here over a self-injective ring).
Kind: PROVED. -/
theorem exists_cob_of_natural_inj {A : Type} [CommRing A] [Module.Injective A A]
    {CP CR : GCx A} (i : GHom CP CR) (lamR : CR.X 2 →ₗ[A] A) (lamP : CP.X 2 →ₗ[A] A) (e : A)
    (hnat : ∀ w, CP.d 2 3 rfl w = 0 → lamR (i.f 2 2 rfl w) = e * lamP w) :
    ∃ μ : CP.X 3 →ₗ[A] A, lamR ∘ₗ i.f 2 2 rfl = e • lamP + μ ∘ₗ CP.d 2 3 rfl := by
  obtain ⟨μ, hμ⟩ := exists_comp_of_vanish_inj (CP.d 2 3 rfl)
    (lamR ∘ₗ i.f 2 2 rfl - e • lamP) fun w hw => by
      change lamR (i.f 2 2 rfl w) - e * lamP w = 0
      rw [hnat w hw, sub_self]
  refine ⟨μ, ?_⟩
  rw [← hμ]
  abel

/-! ### (b) The functional relation from retention at a stage ring -/

/-- **The functional relation from retention, up to a coboundary, at a self-injective
coefficient ring** (tex 4157–4177): for lane RC30's retention data `PR`, a trace `tr` killing
coboundaries and the paired strict lift `j z_S = e z_{P⊥} + d b` (`hlift`), the paired
functionals `λ_R = pairedFun PR.toRetainedPairing.QR tr z_S` and
`λ_P = pairedFun PR.toRetainedPairing.QP tr z_{P⊥}` satisfy `λ_R ∘ i = e λ_P + μ ∘ d` on `C_P²`
for some `μ`, with `i = changeMap DR fP`. Lane RC30's `PlaceRetentionG.pairedFunctional_natural`
gives the relation on cocycles over any commutative ring; `exists_cob_of_natural_inj` gives the
rest. Kind: PROVED. -/
theorem PlaceRetentionG.exists_cob_inj {A : Type} [CommRing A] [Module.Injective A A]
    {DR DPp : SelData A} {UP US : GCx A} {fP : GHom UP DR.U} {fS : GHom US DPp.U}
    {Lq Uq : GCx A} {ιq : GHom Uq Lq} (PR : PlaceRetentionG DR DPp fP fS Lq Uq ιq)
    (tr : (coneCx PR.toRetainedPairing.QP.resE).X 3 →ₗ[A] A)
    (htr : ∀ x, tr ((coneCx PR.toRetainedPairing.QP.resE).d 2 3 rfl x) = 0)
    (zS : (selCx (selRestrict DPp fS)).X 1) (zPp : (selCx DPp).X 1) (e : A)
    (b : (selCx DPp).X 0)
    (hlift : (changeMap DPp fS).f 1 1 rfl zS = e • zPp + (selCx DPp).d 0 1 rfl b) :
    ∃ μ : (selCx (selRestrict DR fP)).X 3 →ₗ[A] A,
      pairedFun PR.toRetainedPairing.QR
          (tr : (coneCx PR.toRetainedPairing.QR.resE).X 3 →ₗ[A] A) zS ∘ₗ
        (changeMap DR fP).f 2 2 rfl =
      e • pairedFun PR.toRetainedPairing.QP tr zPp +
        μ ∘ₗ (selCx (selRestrict DR fP)).d 2 3 rfl :=
  exists_cob_of_natural_inj (changeMap DR fP)
    (pairedFun PR.toRetainedPairing.QR
      (tr : (coneCx PR.toRetainedPairing.QR.resE).X 3 →ₗ[A] A) zS)
    (pairedFun PR.toRetainedPairing.QP tr zPp) e fun w hw =>
      PR.pairedFunctional_natural tr htr zS zPp e b hlift w hw

/-! ### (c) The stage norm identity of lane E2 -/

section E2Stage

open ZInQ.Contrib.CloudB3E2.NormCochain
open ZInQ.Contrib.CloudB3RC53.UnramifiedComplex ZInQ.Contrib.CloudB3RC53.RankCounts
open ZInQ.Contrib.CloudB3RC53.HeegnerCohomology.TwistedTransfer
open ZInQ.Manuscript.RC.CoefModules ZInQ.Manuscript.RC.KummerMaps
open NumberField IsDedekindDomain

attribute [local instance] TopRep.distribMulAction TopRep.smulCommClass groupRingTop

open scoped Classical in
/-- **The stage norm identity of lane E2, re-exported** (tex 4142–4185, 4157–4170, 3203–3290):
lane E2's `hzR_stage_actual_of_inputs` with the same binders, in the same order, and the same
conclusion (its statement and its named inputs are recorded in the module docstring); the proof
is its application.

*The data of the conclusion.* The coefficient ring is the stage `A_i = Acoef i`; the module is
lane RC29's `MinS hS W i α`, `α = alphaStage i s hs hs0 π ψ`; the old conditions are
`stageConditions … P hΨ` on `Places K S₀` only (lane RC29's `actLCondA`: Kummer at `P`, full at
`S₀ − P`).
* Relaxed data: `stageRelaxed K S₀ S (Acoef i) (MinS …) (stageConditions …) w`, by definition
  `relaxedAt (stageOld …) (stageRes … w)`, i.e. `addPlace (stageOld …) (stageRes … w) (idGHom _)`:
  lane RC32's round-7 `addPlace`/`relaxedAt` (`CommonCoordinate11Selmer.lean`) on lane RC26's
  genuine Selmer data `stageOld … = selData …`. Over a field these are literally lane RC32's
  `genuineOld`, `genuineRes`, `genuineRelaxed` (`stageRelaxed_eq_genuineRelaxed`, `rfl`); lane E2
  restates them over a commutative ring, here `A_i`.
* Primitive data: `selRestrict (stageRelaxed … w) (primToRel (stageOld …) (stageRes … w) ι_w)`
  with `ι_w = genuineιq … (urRep …) (urId …) (urId_compat …)`, lane RC30's genuine unramified
  condition at `w` on lane RC26's unramified module; it equals
  `addPlace (stageOld …) (stageRes … w) ι_w` (`selRestrict_relaxedAt`), the shape of lane RC32's
  `genuinePrimitive`.
* Inclusion: `changeMap (stageRelaxed … w) (primToRel …) : C_P → C_R`,
  `(a, u, x) ↦ (a, primToRel u, x)`, lane RC30's `i`.
* Classes: `zR₂`, `zP₂` are existential; neither their origin nor their cocycle property is
  recorded. In the proof, `zR₂` is the coefficient push along `h20RingHom ψ` (`relaxedPush`,
  `SelPush.push1`) of the Shapiro-level strict lift `strictLift … aR uR` over `ℤ[Δ]`, and `zP₂`
  is a pushed class of `strictLiftP … aP uP` (`h20CoefficientPush_genuine`), with `uR`, `uP`
  from `h1_shapiro`. The point factor is `h20RingHom ψ (eq_ HP θP a σ)`: the image under
  `[δ] ↦ ψ(δ)` of `a − θP(σ) − θP(σ)⁻¹ ∈ ℤ[Δ]` (lane E2: `a_q − ψ(σ_q) − ψ(σ_q)⁻¹` for the
  text's characters).

*An adapter to round 9's presentation (described, not attempted).* Round 9's support complexes
are `suppCx T = selCx (selData k (GKS K S) (presGv …) (presLoc …) M (presCond … T))`, with the
inclusions `suppIncl T p = changeIncl (presCondIncl T p)` (lane RC26's comparison `condMap`,
`(a, u, x) ↦ (a, φ u, x)`). An adapter from the data above would need:
1. the ring: `presCond`, `suppData`, `suppCx`, `presSplit`, `suppIncl` are declared over
   `[Field k] [TopologicalSpace k]`; they must be restated over `[CommRing k]` (with the
   topology), as lane E2 restated `genuineOld` as `stageOld`, to take `k = A_i`;
2. the places: round 9 indexes all local data by `Places K S₀ ⊕ (ι × Bool)` in one product, lane
   E2 by the binary product of the old places `Places K S₀` and the single new place `w`; one
   needs a degreewise isomorphism of Selmer complexes (the identity on the global part, the
   reindexing of the product over `Places K S₀ ⊕ (ι × Bool)` as the old product times the places
   above `ι`, with the places above `p` split off, on the local and condition parts) commuting
   with the differentials and with the inclusions (`changeMap … primToRel` against `suppIncl`),
   to carry `zR₂`, `zP₂` and the boundary `b`;
3. the conditions: lane E2's old conditions are `stageConditions` on `S₀` alone and it relaxes
   one place `w`, while round 9's `C_T` carries both places above every prime of `ι` (full above
   `T`, unramified elsewhere) and switches the pair `(p, false)`, `(p, true)`. So `h1_shapiro`
   (`exists_oldLift_shap`, `shapConditions_ι_injective`, `shapConditions_ι_surjective`, `hPw`)
   and `h20ConditionsPush_actual` must be generalized to old conditions on `S₀` and the places
   above `ι`, and to two new places, with an unramified-localization input like `hPw` at every
   place above a prime outside `T` (the full conditions need nothing);
4. the coefficients: `k = A_i`, `M = MinS hS W i α`, `X j = urRep (Acoef i) (Mcoef …) (newPlace …)`
   and split inclusions `EU j` of the genuine unramified conditions with
   `(EU j).i = genuineιq …` (`condι_false`); over `A_i` a degreewise complement of the inflation
   is a genuine input, not automatic as over a field.
Finally the chain must take its classes to be these `zR₂`, `zP₂`, with their cocycle property
proved separately. From lane E2's named inputs. Kind: PROVED. -/
theorem hzR_stage_of_E2 {K : Type} [Field K] [NumberField K]
    {S S₀ : Set (HeightOneSpectrum (𝓞 K))} (hS : S₀ ⊆ S) (W : WeierstrassCurve K)
    [W.IsElliptic] (i : ℕ) [NeZero i] (s : KS K S₀) {h : K}
    (hs : s ^ 2 = algebraMap K (KS K S₀) h) (hs0 : s ≠ 0) (hFull : FullTorsion K S₀ W (2 ^ i))
    [TopologicalSpace (Acoef i)] [DiscreteTopology (Acoef i)]
    {Δ : Type} [CommGroup Δ] [Finite Δ] (π : GKS K S₀ →* Δ) (ψ : Δ →* (Acoef i)ˣ)
    [IsOpenKer (alphaShap s hs hs0 π)] [IsOpenKer (alphaStage i s hs hs0 π ψ)]
    (P : Set (HeightOneSpectrum (𝓞 K))) (hψ : Function.Injective ψ)
    (hΨ : PsiTrivialAt2N i π ψ P)
    {D : Type} [AddCommGroup D] [Module (MonoidAlgebra ℤ Δ) D]
    (ρ : GKS K S →* Module.End (MonoidAlgebra ℤ Δ) D)
    (HP HR : Subgroup (GKS K S)) [HP.Normal] [HR.Normal] [Fintype (GKS K S ⧸ HP)]
    [Fintype (GKS K S ⧸ HR)]
    (rP : GKS K S ⧸ HP → GKS K S) (hrP : ∀ δ, ((rP δ : GKS K S) : GKS K S ⧸ HP) = δ)
    (rR : GKS K S ⧸ HR → GKS K S) (hrR : ∀ δ, ((rR δ : GKS K S) : GKS K S ⧸ HR) = δ)
    (θP : GKS K S ⧸ HP →* (MonoidAlgebra ℤ Δ)ˣ) (θR : GKS K S ⧸ HR →* (MonoidAlgebra ℤ Δ)ˣ)
    (U : Subgroup HP) (hU : ∀ h : HP, h ∈ U ↔ (h : GKS K S) ∈ HR) [Fintype (HP ⧸ U)]
    (t : HP ⧸ U → HP) (ht : ∀ τ : HP ⧸ U, (QuotientGroup.mk (t τ) : HP ⧸ U) = τ)
    (w : Places K S) (hw : w.1 ∉ S₀)
    [ContinuousSMul (GUr K w.1)
      (urRep (MonoidAlgebra ℤ Δ) (shapMod₀ W i s hs hs0 π) (newPlace w hw)).V]
    [ContinuousSMul (GUr K w.1)
      (urRep (Acoef i) (Mcoef K S₀ W i (alphaStage i s hs hs0 π ψ)) (newPlace w hw)).V]
    (aR aP : (globalCx (MonoidAlgebra ℤ Δ) (GKS K S) (shapMod hS W i s hs hs0 π)).X 1)
    (hle : HR ≤ HP)
    (hθ : ∀ x : GKS K S, ((θR (x : GKS K S ⧸ HR) : (MonoidAlgebra ℤ Δ)ˣ) : MonoidAlgebra ℤ Δ) =
      θP (x : GKS K S ⧸ HP))
    (a : ℤ) (σ : GKS K S) {yR yP QR QP : D}
    (hQR : ((2 ^ i : ℕ) : ℤ) • QR = yR) (hQP : ((2 ^ i : ℕ) : ℤ) • QP = yP)
    (hfixR : ∀ h ∈ HR, ρ h yR = yR) (hfixP : ∀ h ∈ HP, ρ h yP = yP)
    (hnorm : ∑ τ : HP ⧸ U, ρ (t τ : GKS K S) yR = a • yP - ρ σ yP - ρ σ⁻¹ yP)
    (ι : shapMod hS W i s hs hs0 π →ₗ[MonoidAlgebra ℤ Δ] D) (hι : Function.Injective ι)
    (hιeq : ∀ (g : GKS K S) (m : shapMod hS W i s hs hs0 π), ι (g • m) = R HR ρ θR g (ι m))
    (htors : ∀ x : D, ((2 ^ i : ℕ) : ℤ) • x = 0 → ∃ m, ι m = x)
    (hzR : ∀ g : Fin 1 → GKS K S,
      ι (gval (A := MonoidAlgebra ℤ Δ) (M := shapMod hS W i s hs hs0 π) aR g) =
        T HR rR hrR ρ θR 1 (kummerCochain ρ HR QR) g)
    (hzP : ∀ g : Fin 1 → GKS K S,
      ι (gval (A := MonoidAlgebra ℤ Δ) (M := shapMod hS W i s hs hs0 π) aP g) =
        T HP rP hrP ρ θP 1 (kummerCochain ρ HP QP) g)
    (hinR : ∀ v : Places K S₀, v.1 ∈ P →
      haveI := isElliptic_localTwist W (ne_zero_of_sqrt s hs hs0) v.1
      OldPlaceInput ρ HR rR θR v.1 (localTwist W h v.1) (2 ^ i)
        (shapIota hS W i s hs hs0 hFull π ⟨v.1, hS v.2⟩) ι yR)
    (hinP : ∀ v : Places K S₀, v.1 ∈ P →
      haveI := isElliptic_localTwist W (ne_zero_of_sqrt s hs hs0) v.1
      OldPlaceInput ρ HP rP θP v.1 (localTwist W h v.1) (2 ^ i)
        (shapIota hS W i s hs hs0 hFull π ⟨v.1, hS v.2⟩) ι yP)
    (hPw : ∃ y : (genuineUq K S (MonoidAlgebra ℤ Δ) w
        (urRep (MonoidAlgebra ℤ Δ) (shapMod₀ W i s hs hs0 π) (newPlace w hw))).X 1,
      (genuineιq K S (MonoidAlgebra ℤ Δ) (shapMod hS W i s hs hs0 π) w
        (urRep (MonoidAlgebra ℤ Δ) (shapMod₀ W i s hs hs0 π) (newPlace w hw))
        (urId hS (MonoidAlgebra ℤ Δ) (shapMod₀ W i s hs hs0 π) (newPlace w hw))
        (urId_compat hS (MonoidAlgebra ℤ Δ) (shapMod₀ W i s hs hs0 π) w hw)).f 1 1 rfl y =
      (stageRes K S (MonoidAlgebra ℤ Δ) (shapMod hS W i s hs hs0 π) w).f 1 1 rfl aP) :
    ∃ (zR₂ : (selCx (stageRelaxed K S₀ S (Acoef i) (MinS hS W i (alphaStage i s hs hs0 π ψ))
        (stageConditions hS W i s hs hs0 hFull π ψ P hΨ) w)).X 1)
      (zP₂ : (selCx (selRestrict (stageRelaxed K S₀ S (Acoef i)
        (MinS hS W i (alphaStage i s hs hs0 π ψ))
        (stageConditions hS W i s hs hs0 hFull π ψ P hΨ) w)
        (primToRel (stageOld K S₀ S (Acoef i) (MinS hS W i (alphaStage i s hs hs0 π ψ))
          (stageConditions hS W i s hs hs0 hFull π ψ P hΨ))
          (stageRes K S (Acoef i) (MinS hS W i (alphaStage i s hs hs0 π ψ)) w)
          (genuineιq K S (Acoef i) (MinS hS W i (alphaStage i s hs hs0 π ψ)) w
            (urRep (Acoef i) (Mcoef K S₀ W i (alphaStage i s hs hs0 π ψ)) (newPlace w hw))
            (urId hS (Acoef i) (Mcoef K S₀ W i (alphaStage i s hs hs0 π ψ)) (newPlace w hw))
            (urId_compat hS (Acoef i) (Mcoef K S₀ W i (alphaStage i s hs hs0 π ψ)) w
              hw))))).X 1),
      ∃ b, zR₂ = h20RingHom ψ (eq_ HP θP a σ) • (changeMap _ _).f 1 1 rfl zP₂ +
        (selCx _).d 0 1 rfl b :=
  hzR_stage_actual_of_inputs hS W i s hs hs0 hFull π ψ P hψ hΨ ρ HP HR rP hrP rR hrR θP θR U hU
    t ht w hw aR aP hle hθ a σ hQR hQP hfixR hfixP hnorm ι hι hιeq htors hzR hzP hinR hinP hPw

end E2Stage

/-! ### (d) Stage-ring instances -/

section StageRing

open ZInQ.Manuscript.RC.Limits (Lambda stageIdeal stageEquiv StageA)

/-- **The inner-limit stage is RC10's coefficient ring**: `StageA s` (`Ultralimit.lean`) and
`Acoef s` are the same type `(ℤ/2^s)[t]/t^s` (tex 2725, 2747). Kind: PROVED. -/
theorem stageA_eq_acoef (s : ℕ) : StageA s = Acoef s := rfl

/-- **`A_i` is self-injective, as an instance** (tex 2725, 3465–3467: the finite Frobenius rings
`A_i`): the RC53 group's `acoef_selfInjective`. Kind: PROVED. -/
instance acoef_moduleInjective (i : ℕ) : Module.Injective (Acoef i) (Acoef i) :=
  acoef_selfInjective i

/-- **`Λ ⧸ (2^s, t^s)` is self-injective, as an instance** (tex 2725, 2747, 3465–3467):
`acoef_selfInjective` transported along `stageEquiv s : Λ ⧸ (2^s, t^s) ≃+* A_s` by Mathlib's
`Module.Injective.of_ringEquiv`. Kind: PROVED. -/
instance stageQuot_moduleInjective (s : ℕ) :
    Module.Injective (Lambda ⧸ stageIdeal s) (Lambda ⧸ stageIdeal s) :=
  haveI : Module.Injective (StageA s) (StageA s) := acoef_selfInjective s
  Module.Injective.of_ringEquiv (stageEquiv s).symm (stageEquiv s).symm.toSemilinearEquiv

/-- **`Λ ⧸ (2^s, t^s)` is Noetherian** (tex 2747): found by Mathlib's instances (`ℤ₂` is a
discrete valuation ring, power series over a Noetherian ring are Noetherian, a quotient of a
Noetherian ring is Noetherian). Kind: PROVED. -/
theorem stageQuot_isNoetherianRing (s : ℕ) : IsNoetherianRing (Lambda ⧸ stageIdeal s) :=
  inferInstance

/-- **`A_i` is Noetherian** (tex 2725): found by Mathlib's instances. Kind: PROVED. -/
theorem acoef_isNoetherianRing (i : ℕ) : IsNoetherianRing (Acoef i) :=
  inferInstance

/-- **`Λ ⧸ (2^s, t^s)` is finite, as an instance** (tex 2725, 2747): it is isomorphic to `A_s`
(`stageEquiv`), whose finiteness Mathlib finds. Kind: PROVED. -/
instance stageQuot_finite (s : ℕ) : Finite (Lambda ⧸ stageIdeal s) :=
  Finite.of_equiv (StageA s) (stageEquiv s).symm.toEquiv

/-- **`Λ ⧸ (2^s, t^s)` is Artinian** (tex 4392: the inner limit works over Artin local rings;
this is the Artinian half), as a finite ring. Kind: PROVED. -/
theorem stageQuot_isArtinianRing (s : ℕ) : IsArtinianRing (Lambda ⧸ stageIdeal s) :=
  inferInstance

/-- **The functional relation up to a coboundary at a stage ring `A_i`** (tex 4157–4194,
4385–4451): `exists_cob_of_natural_inj` at `A = Acoef i`, through `acoef_moduleInjective`.
Kind: PROVED. -/
theorem exists_cob_of_natural_acoef (i : ℕ) {CP CR : GCx (Acoef i)} (f : GHom CP CR)
    (lamR : CR.X 2 →ₗ[Acoef i] Acoef i) (lamP : CP.X 2 →ₗ[Acoef i] Acoef i) (e : Acoef i)
    (hnat : ∀ w, CP.d 2 3 rfl w = 0 → lamR (f.f 2 2 rfl w) = e * lamP w) :
    ∃ μ : CP.X 3 →ₗ[Acoef i] Acoef i, lamR ∘ₗ f.f 2 2 rfl = e • lamP + μ ∘ₗ CP.d 2 3 rfl :=
  exists_cob_of_natural_inj f lamR lamP e hnat

/-- **The functional relation up to a coboundary at a stage ring `Λ ⧸ (2^s, t^s)`**
(tex 4157–4194, 4385–4451): `exists_cob_of_natural_inj` at `A = Λ ⧸ stageIdeal s`, through
`stageQuot_moduleInjective`. Kind: PROVED. -/
theorem exists_cob_of_natural_stage (s : ℕ) {CP CR : GCx (Lambda ⧸ stageIdeal s)}
    (f : GHom CP CR) (lamR : CR.X 2 →ₗ[Lambda ⧸ stageIdeal s] Lambda ⧸ stageIdeal s)
    (lamP : CP.X 2 →ₗ[Lambda ⧸ stageIdeal s] Lambda ⧸ stageIdeal s) (e : Lambda ⧸ stageIdeal s)
    (hnat : ∀ w, CP.d 2 3 rfl w = 0 → lamR (f.f 2 2 rfl w) = e * lamP w) :
    ∃ μ : CP.X 3 →ₗ[Lambda ⧸ stageIdeal s] Lambda ⧸ stageIdeal s,
      lamR ∘ₗ f.f 2 2 rfl = e • lamP + μ ∘ₗ CP.d 2 3 rfl :=
  exists_cob_of_natural_inj f lamR lamP e hnat

end StageRing

end ZInQ.Manuscript.RC.Wiring
