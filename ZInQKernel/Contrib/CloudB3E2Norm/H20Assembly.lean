import ZInQKernel.Contrib.CloudB3E2Norm.H20Bridge

/-!
# The Shapiro-level norm identity `h₁` for the actual data, assembled

Manuscript `diophantine_zq.tex`, tex 4142–4185 (Theorem 5.3, the common-coordinate step), with the
old local conditions of paragraph 5 (tex 3413–3440) and their survival under (H20) (tex 3251–3270).

`hzR_stage_actual` (`H20Actual.lean`) turns the Shapiro-level norm identity with retained boundary
`z_R¹ = e₁ • i(z_P¹) + d b` over `ℤ[Δ]` into the stage identity over `A_i`. This file assembles that
hypothesis `h₁` from the chain of this directory, for the strict lifts of the transferred Kummer
classes:

* `shapConditions_ι_injective`, `shapConditions_ι_surjective` (PROVED): the old conditions (Kummer
  at `P`, full at `S₀ − P`) are injective in degree one and surjective in degree zero (the
  hypotheses `hιold`, `hsold`).
* `exists_oldLift_shap` (PROVED): the localizations of a class carried to `𝒯_θ(κ(Q))` lie in the
  old conditions: at `v ∈ P` by `res_mem_kummer_at` (`LocalIdentity.lean`) from `OldPlaceInput`
  (`LocalTwistIdentification` + the realization of the points), at `v ∈ S₀ − P` trivially.
* **`h1_shapiro`** (PROVED): the Shapiro-level identity `h₁` for the strict lifts of the relaxed
  class `a_R` and the primitive class `a_P`, from: the transfer inputs of `hzR_stage_of_strictLifts`
  (`StageRing.lean`: the norm relation `hnorm`, `hθ`, `H_R ≤ H_P`, division points, `ι` injective
  with torsion lifting, the classes carried to `𝒯_θ(κ(Q))`), `OldPlaceInput` at the places of `P`
  for both points, and the unramified localization of `a_P` at the new place `w` (`hPw`).
* **`hzR_stage_actual_of_inputs`** (PROVED): the stage norm identity for lane RC29's actual data
  from the same inputs (`h1_shapiro` + `hzR_stage_actual`).

Named inputs left (mathematical): ELLIOT `PsiTrivialAt2N` (tex 2729, 3431, 3500–3506), with `ψ`
injective (for `Δ = im Ψ_i` automatic, `moving_spec`); GLUE `LocalTwistIdentification` and the
realization `hreal` (inside `OldPlaceInput`, for `y_R` and `y_P`, tex 3251–3270); the norm relation
`hnorm` of the Heegner points (tex 4157–4170); the unramified localization of the primitive class
at `w` (`hPw`, tex 3471–3487); GLUE `FullTorsion`. Structural inputs (properties of the chosen
ambient module of points and coefficient embedding): the points `y_R`, `y_P` fixed by `H_R`, `H_P`
(`hfixR`, `hfixP`: they are defined over `H_R`, `H_P`), their division points (`hQR`, `hQP`), the
character compatibility `hθ` and `H_R ≤ H_P`, the coefficient embedding `ι` injective and
equivariant (`hι`, `hιeq`) with torsion lifting (`htors`), and the classes carried to `𝒯_θ(κ(Q))`
(`hzR`, `hzP`). Infrastructure instances: open kernels of the characters (`isOpenKer_alphaShap`,
`isOpenKer_alphaStage`) and discreteness of the unramified modules (`urRep_hyps_actual`).

Non-vacuity: the hypotheses are those of results with witnesses in this directory
(`nonVacuity_transversal` for the transfer inputs, `nonVacuity_localTwist_identity` and
`nonVacuity_oldPlaceInput` for `OldPlaceInput`, `nonVacuity_psiTrivial`, `urRep_hyps_actual`);
`shapConditions_ι_injective`/`_surjective` are unconditional.

Kinds: PROVED (from the named inputs).
-/

noncomputable section

namespace ZInQ.Contrib.CloudB3E2.NormCochain

open ZInQ.Contrib.CloudB3RC53.PairedFunctional ZInQ.Contrib.CloudB3RC53.SelmerDuality
open ZInQ.Contrib.CloudB3RC53.UnramifiedComplex ZInQ.Contrib.CloudB3RC53.RankCounts
open ZInQ.Contrib.CloudB3RC53.HeegnerCohomology.TwistedTransfer
open ZInQ.Manuscript.RC.Wiring ZInQ.Manuscript.RC.SelmerComplex ZInQ.Manuscript.RC.CoefModules
open ZInQ.Manuscript.RC.KummerMaps
open ZInQ.Manuscript.RC.HeegnerAlgebra (Acoef)
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

/-- A property of both branches holds for a dependent `if` of local conditions. Kind: PROVED. -/
theorem condAt_dite {k M : Type} [CommRing k] [AddCommGroup M] [Module k M]
    [DistribMulAction (GKS K S) M] [SMulCommClass (GKS K S) k M] [TopologicalSpace M]
    [DiscreteTopology M] [ContinuousSMul (GKS K S) M] {v : Places K S} {p : Prop} [Decidable p]
    (c₁ : p → CondAt K S k M v) (c₂ : ¬p → CondAt K S k M v) (Pr : CondAt K S k M v → Prop)
    (h₁ : ∀ hp, Pr (c₁ hp)) (h₂ : ∀ hp, Pr (c₂ hp)) : Pr (dite p c₁ c₂) := by
  by_cases hp : p
  · rw [dite_eq_left_of_eq_true (eq_true hp)]; exact h₁ hp
  · rw [dite_eq_right_of_eq_false (eq_false hp)]; exact h₂ hp

open scoped Classical in
/-- One old condition is injective in degree one. Kind: PROVED. -/
theorem shapCond_injective (v : Places K S₀) :
    Function.Injective ((shapCond hS W i s hs hs0 hFull π ψ P hψ hΨ v).i.f 1 1 rfl) := by
  unfold shapCond
  exact condAt_dite _ _ (fun c => Function.Injective (c.i.f 1 1 rfl))
    (fun _ => cocycleConditionι_injective _ _ 1) (fun _ _ _ hab => hab)

open scoped Classical in
/-- One old condition is surjective in degree zero. Kind: PROVED. -/
theorem shapCond_surjective (v : Places K S₀)
    (b : (locAt K S (MonoidAlgebra ℤ Δ) (shapMod hS W i s hs hs0 π) ⟨v.1, hS v.2⟩).X 0) :
    ∃ x, (shapCond hS W i s hs hs0 hFull π ψ P hψ hΨ v).i.f 0 0 rfl x = b := by
  unfold shapCond
  exact condAt_dite _ _ (fun c => ∃ x, c.i.f 0 0 rfl x = b)
    (fun _ => ⟨⟨b, trivial⟩, rfl⟩) (fun _ => ⟨b, rfl⟩)

/-- **The old conditions are injective in degree one** (PROVED): `hιold`. -/
theorem shapConditions_ι_injective :
    Function.Injective ((stageOld K S₀ S (MonoidAlgebra ℤ Δ) (shapMod hS W i s hs hs0 π)
      (shapConditions hS W i s hs hs0 hFull π ψ P hψ hΨ)).ι.f 1 1 rfl) := fun _ _ hxy =>
  funext fun v => shapCond_injective hS W i s hs hs0 hFull π ψ P hψ hΨ v (congrFun hxy v)

/-- **The old conditions are surjective in degree zero** (PROVED): `hsold`. -/
theorem shapConditions_ι_surjective
    (y : (stageOld K S₀ S (MonoidAlgebra ℤ Δ) (shapMod hS W i s hs hs0 π)
      (shapConditions hS W i s hs hs0 hFull π ψ P hψ hΨ)).L.X 0) :
    ∃ x, (stageOld K S₀ S (MonoidAlgebra ℤ Δ) (shapMod hS W i s hs hs0 π)
      (shapConditions hS W i s hs hs0 hFull π ψ P hψ hΨ)).ι.f 0 0 rfl x = y := by
  choose x hx using fun v => shapCond_surjective hS W i s hs hs0 hFull π ψ P hψ hΨ v (y v)
  exact ⟨x, funext hx⟩

open scoped Classical in
include hFull in
/-- The old lift at one place. Kind: PROVED. -/
theorem exists_oldLift_shap_at {D : Type} [AddCommGroup D] [Module (MonoidAlgebra ℤ Δ) D]
    (ρ : GKS K S →* Module.End (MonoidAlgebra ℤ Δ) D) (H : Subgroup (GKS K S)) [H.Normal]
    [Fintype (GKS K S ⧸ H)] (r : GKS K S ⧸ H → GKS K S)
    (hr : ∀ δ, ((r δ : GKS K S) : GKS K S ⧸ H) = δ) (θ : GKS K S ⧸ H →* (MonoidAlgebra ℤ Δ)ˣ)
    (ι : shapMod hS W i s hs hs0 π →ₗ[MonoidAlgebra ℤ Δ] D)
    (hιeq : ∀ (g : GKS K S) (x : shapMod hS W i s hs hs0 π), ι (g • x) = R H ρ θ g (ι x))
    {Q y : D} (hQ : ((2 ^ i : ℕ) : ℤ) • Q = y)
    (hin : ∀ v : Places K S₀, v.1 ∈ P →
      haveI := isElliptic_localTwist W (ne_zero_of_sqrt s hs hs0) v.1
      OldPlaceInput ρ H r θ v.1 (localTwist W h v.1) (2 ^ i)
        (shapIota hS W i s hs hs0 hFull π ⟨v.1, hS v.2⟩) ι y)
    (aT : (globalCx (MonoidAlgebra ℤ Δ) (GKS K S) (shapMod hS W i s hs hs0 π)).X 1)
    (hz : ∀ g : Fin 1 → GKS K S,
      ι (gval (A := MonoidAlgebra ℤ Δ) (M := shapMod hS W i s hs hs0 π) aT g) =
        T H r hr ρ θ 1 (kummerCochain ρ H Q) g)
    (v : Places K S₀) :
    ∃ u : (shapCond hS W i s hs hs0 hFull π ψ P hψ hΨ v).U.X 1,
      (shapCond hS W i s hs hs0 hFull π ψ P hψ hΨ v).i.f 1 1 rfl u =
        (natHom (resCochains (k := MonoidAlgebra ℤ Δ) (M := shapMod hS W i s hs hs0 π)
          (locMap K S v.1))).f 1 1 rfl aT := by
  unfold shapCond
  by_cases hP : v.1 ∈ P
  swap
  · rw [dite_eq_right_of_eq_false (eq_false hP)]
    exact ⟨_, rfl⟩
  rw [dite_eq_left_of_eq_true (eq_true hP)]
  have := isElliptic_localTwist W (ne_zero_of_sqrt s hs hs0) v.1
  obtain ⟨L, _, _, _, _, ψL, jB, hT, J, sJ, a, Pt, hreal⟩ := hin v hP
  exact res_mem_kummer_at ρ H r hr θ v.1 (localTwist W h v.1) (2 ^ i)
    (shapIota hS W i s hs hs0 hFull π ⟨v.1, hS v.2⟩)
    (shapIota_smul hS W i s hs hs0 hFull π ⟨v.1, hS v.2⟩
      (isLocallyQuadAtGen_shap i s hs hs0 π ψ hψ hΨ hP)) ψL jB ι hιeq hT hQ sJ a Pt hreal aT hz

open scoped Classical in
include hFull in
/-- **The old lift for the Shapiro-level conditions** (PROVED): at `v ∈ P` from `OldPlaceInput`
(`res_mem_kummer_at`, `LocalIdentity.lean`), at `v ∈ S₀ − P` (full condition) trivially. -/
theorem exists_oldLift_shap {D : Type} [AddCommGroup D] [Module (MonoidAlgebra ℤ Δ) D]
    (ρ : GKS K S →* Module.End (MonoidAlgebra ℤ Δ) D) (H : Subgroup (GKS K S)) [H.Normal]
    [Fintype (GKS K S ⧸ H)] (r : GKS K S ⧸ H → GKS K S)
    (hr : ∀ δ, ((r δ : GKS K S) : GKS K S ⧸ H) = δ) (θ : GKS K S ⧸ H →* (MonoidAlgebra ℤ Δ)ˣ)
    (ι : shapMod hS W i s hs hs0 π →ₗ[MonoidAlgebra ℤ Δ] D)
    (hιeq : ∀ (g : GKS K S) (x : shapMod hS W i s hs hs0 π), ι (g • x) = R H ρ θ g (ι x))
    {Q y : D} (hQ : ((2 ^ i : ℕ) : ℤ) • Q = y)
    (hin : ∀ v : Places K S₀, v.1 ∈ P →
      haveI := isElliptic_localTwist W (ne_zero_of_sqrt s hs hs0) v.1
      OldPlaceInput ρ H r θ v.1 (localTwist W h v.1) (2 ^ i)
        (shapIota hS W i s hs hs0 hFull π ⟨v.1, hS v.2⟩) ι y)
    (aT : (globalCx (MonoidAlgebra ℤ Δ) (GKS K S) (shapMod hS W i s hs hs0 π)).X 1)
    (hz : ∀ g : Fin 1 → GKS K S,
      ι (gval (A := MonoidAlgebra ℤ Δ) (M := shapMod hS W i s hs hs0 π) aT g) =
        T H r hr ρ θ 1 (kummerCochain ρ H Q) g) :
    ∃ u : (stageOld K S₀ S (MonoidAlgebra ℤ Δ) (shapMod hS W i s hs hs0 π)
        (shapConditions hS W i s hs hs0 hFull π ψ P hψ hΨ)).U.X 1,
      (stageOld K S₀ S (MonoidAlgebra ℤ Δ) (shapMod hS W i s hs hs0 π)
        (shapConditions hS W i s hs hs0 hFull π ψ P hψ hΨ)).ι.f 1 1 rfl u =
      (stageOld K S₀ S (MonoidAlgebra ℤ Δ) (shapMod hS W i s hs hs0 π)
        (shapConditions hS W i s hs hs0 hFull π ψ P hψ hΨ)).res.f 1 1 rfl aT := by
  exact exists_lift_selData _ aT fun v =>
    exists_oldLift_shap_at hS W i s hs hs0 hFull π ψ P hψ hΨ ρ H r hr θ ι hιeq hQ hin aT hz v

end Assembly

section H1

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
  (w : Places K S) (hw : w.1 ∉ S₀)
  [ContinuousSMul (GUr K w.1)
    (urRep (MonoidAlgebra ℤ Δ) (shapMod₀ W i s hs hs0 π) (newPlace w hw)).V]
  [ContinuousSMul (GUr K w.1)
    (urRep (Acoef i) (Mcoef K S₀ W i (alphaStage i s hs hs0 π ψ)) (newPlace w hw)).V]

/-- The Shapiro-level primitive map at `w` (identity on the old conditions, the unramified
condition `genuineιq` at `w`). Kind: definition. -/
abbrev shapPrim :=
  primToRel (stageOld K S₀ S (MonoidAlgebra ℤ Δ) (shapMod hS W i s hs hs0 π)
      (shapConditions hS W i s hs hs0 hFull π ψ P hψ hΨ))
    (stageRes K S (MonoidAlgebra ℤ Δ) (shapMod hS W i s hs hs0 π) w)
    (genuineιq K S (MonoidAlgebra ℤ Δ) (shapMod hS W i s hs hs0 π) w
      (urRep (MonoidAlgebra ℤ Δ) (shapMod₀ W i s hs hs0 π) (newPlace w hw))
      (urId hS (MonoidAlgebra ℤ Δ) (shapMod₀ W i s hs hs0 π) (newPlace w hw))
      (urId_compat hS (MonoidAlgebra ℤ Δ) (shapMod₀ W i s hs hs0 π) w hw))

open scoped Classical in
include hrP hrR hU ht in
/-- **The Shapiro-level norm identity `h₁` for the actual data** (PROVED from the named inputs):
there are strict lifts `u_R`, `u_P` of the transferred classes `a_R`, `a_P` with
`strictLift(a_R, u_R) = e_q • i(strictLiftP(a_P, u_P)) + d b` in the Shapiro-level relaxed Selmer
complex (old conditions: Kummer at `P`, full at `S₀ − P`; unramified at `w` for the primitive). -/
theorem h1_shapiro
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
    ∃ (uR : (stageRelaxed K S₀ S (MonoidAlgebra ℤ Δ) (shapMod hS W i s hs hs0 π)
        (shapConditions hS W i s hs hs0 hFull π ψ P hψ hΨ) w).U.X 1)
      (uP : (prodCx (stageOld K S₀ S (MonoidAlgebra ℤ Δ) (shapMod hS W i s hs hs0 π)
        (shapConditions hS W i s hs hs0 hFull π ψ P hψ hΨ)).U
        (genuineUq K S (MonoidAlgebra ℤ Δ) w
          (urRep (MonoidAlgebra ℤ Δ) (shapMod₀ W i s hs hs0 π) (newPlace w hw)))).X 1),
      ∃ b, strictLift (stageRelaxed K S₀ S (MonoidAlgebra ℤ Δ) (shapMod hS W i s hs hs0 π)
          (shapConditions hS W i s hs hs0 hFull π ψ P hψ hΨ) w) aR uR =
        eq_ HP θP a σ • (changeMap _ (shapPrim hS W i s hs hs0 hFull π ψ P hψ hΨ w hw)).f 1 1 rfl
          (strictLiftP _ (shapPrim hS W i s hs hs0 hFull π ψ P hψ hΨ w hw) aP uP) +
        (selCx (stageRelaxed K S₀ S (MonoidAlgebra ℤ Δ) (shapMod hS W i s hs hs0 π)
          (shapConditions hS W i s hs hs0 hFull π ψ P hψ hΨ) w)).d 0 1 rfl b := by
  have hιeqP : ∀ (g : GKS K S) (m : shapMod hS W i s hs hs0 π), ι (g • m) = R HP ρ θP g (ι m) :=
    fun g m => by rw [hιeq]; simp only [R, hθ]
  obtain ⟨uR, huR⟩ := exists_lift_relaxedAt (stageOld K S₀ S (MonoidAlgebra ℤ Δ)
      (shapMod hS W i s hs hs0 π) (shapConditions hS W i s hs hs0 hFull π ψ P hψ hΨ))
    (stageRes K S (MonoidAlgebra ℤ Δ) (shapMod hS W i s hs hs0 π) w) aR
    (exists_oldLift_shap hS W i s hs hs0 hFull π ψ P hψ hΨ ρ HR rR hrR θR ι hιeq hQR hinR aR hzR)
  obtain ⟨uP, huP⟩ := exists_hPloc_primToRel (stageOld K S₀ S (MonoidAlgebra ℤ Δ)
      (shapMod hS W i s hs hs0 π) (shapConditions hS W i s hs hs0 hFull π ψ P hψ hΨ))
    (stageRes K S (MonoidAlgebra ℤ Δ) (shapMod hS W i s hs hs0 π) w)
    (genuineιq K S (MonoidAlgebra ℤ Δ) (shapMod hS W i s hs hs0 π) w
      (urRep (MonoidAlgebra ℤ Δ) (shapMod₀ W i s hs hs0 π) (newPlace w hw))
      (urId hS (MonoidAlgebra ℤ Δ) (shapMod₀ W i s hs hs0 π) (newPlace w hw))
      (urId_compat hS (MonoidAlgebra ℤ Δ) (shapMod₀ W i s hs hs0 π) w hw)) aP
    (exists_oldLift_shap hS W i s hs hs0 hFull π ψ P hψ hΨ ρ HP rP hrP θP ι hιeqP hQP hinP aP hzP)
    hPw
  exact ⟨uR, uP, hzR_stage_of_strictLifts ρ HP HR rP hrP rR hrR θP θR U hU t ht _ w _ aR aP uR uP
    (shapConditions_ι_injective hS W i s hs hs0 hFull π ψ P hψ hΨ)
    (shapConditions_ι_surjective hS W i s hs hs0 hFull π ψ P hψ hΨ) huR huP hle hθ
    ((2 ^ i : ℕ) : ℤ) a σ hQR hQP hfixR hfixP hnorm ι hι hιeq htors hzR hzP⟩

open scoped Classical in
include hrP hrR hU ht hψ in
/-- **The stage norm identity for lane RC29's actual data from the named inputs** (PROVED;
`h1_shapiro` + `hzR_stage_actual`): there are stage classes over `A_i` for RC29's actual
conditions with `z_R² = φ(e_q) • i(z_P²) + d b`, `φ(e_q) = a_q − z − z⁻¹` with `z = φ(θ(σ_q))` (for
the untwisted instance `z = χ_h(σ_q) ψ(π σ_q)`). -/
theorem hzR_stage_actual_of_inputs
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
        (MinS hS W i (alphaStage i s hs hs0 π ψ)) (stageConditions hS W i s hs hs0 hFull π ψ P hΨ) w)
        (primToRel (stageOld K S₀ S (Acoef i) (MinS hS W i (alphaStage i s hs hs0 π ψ))
          (stageConditions hS W i s hs hs0 hFull π ψ P hΨ))
          (stageRes K S (Acoef i) (MinS hS W i (alphaStage i s hs hs0 π ψ)) w)
          (genuineιq K S (Acoef i) (MinS hS W i (alphaStage i s hs hs0 π ψ)) w
            (urRep (Acoef i) (Mcoef K S₀ W i (alphaStage i s hs hs0 π ψ)) (newPlace w hw))
            (urId hS (Acoef i) (Mcoef K S₀ W i (alphaStage i s hs hs0 π ψ)) (newPlace w hw))
            (urId_compat hS (Acoef i) (Mcoef K S₀ W i (alphaStage i s hs hs0 π ψ)) w hw))))).X 1),
      ∃ b, zR₂ = h20RingHom ψ (eq_ HP θP a σ) • (changeMap _ _).f 1 1 rfl zP₂ +
        (selCx _).d 0 1 rfl b := by
  obtain ⟨uR, uP, h₁⟩ := h1_shapiro hS W i s hs hs0 hFull π ψ P hψ hΨ ρ HP HR rP hrP rR hrR θP θR
    U hU t ht w hw aR aP hle hθ a σ hQR hQP hfixR hfixP hnorm ι hι hιeq htors hzR hzP hinR hinP hPw
  exact hzR_stage_actual hS W i s hs hs0 hFull π ψ P hψ hΨ w hw _ _ _ h₁

end H1

end ZInQ.Contrib.CloudB3E2.NormCochain
