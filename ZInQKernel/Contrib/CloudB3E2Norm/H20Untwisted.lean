import ZInQKernel.Contrib.CloudB3E2Norm.H20Transport
import ZInQKernel.Contrib.CloudB3E2Norm.H20PresAssembly

/-!
# The untwisted ambient module of points: the actual instance with the sign of the text

Manuscript `diophantine_zq.tex`, tex 3915 and 4158–4172 (the point factor `e_q = a_q − z − z⁻¹` with
`z = χ_h(σ_q) Ψ(σ_q)`: the sign `χ_h(σ_q)` is retained in `z`), tex 2914–2936 (the norm relations
(4.1)), tex 3251–3270 and 3471–3487.

The generic Shapiro-level identity `H20Assembly.h1_shapiro` (and its consumers
`hnorm_pres_of_transferK`, the adapter to lane RC32's presentation) takes an ambient module `D` with
an action `ρ` and a transfer character `θ`, the norm relation in the form
`∑_τ ρ(t_τ) y_R = a y_P − ρ(σ) y_P − ρ(σ)⁻¹ y_P`, and gives the point factor `a − θ(σ) − θ(σ)⁻¹`.

`H20Twist.lean` instantiated it with the `χ_h`-twisted ambient module `(ℤ[Δ] ⊗ E(K_{S₀}))(χ_h)` and
`θ = [π]`. There `ρ(σ) = χ_h(σ) · σ`, so the plain norm relation (4.1) on `E` gives the required form
only when `χ_h(σ_q) = 1`, and the point factor `a − [π σ] − [π σ]⁻¹` loses the sign. **This file is
the correct instance**: the *untwisted* ambient module `ℤ[Δ] ⊗ E(K_{S₀})` with the plain Galois
action `ρ₀` and the transfer character `θ = χ_h · [π]` (the Shapiro-level character `alphaShap`,
through `G_{K,S} → G_{K,S₀}`). The required form is then the plain norm relation, and the point
factor is `a − z − z⁻¹` with `z = θ(σ) = χ_h(σ)[π σ]`, the text's (`thetaU_apply`).

**Superseded for the relaxed points.** The ambient points here lie over `K_{S₀}`, the support of
the coefficient module; the Heegner point `y_{dq}` lies over `H_{dq}`, ramified at the switch prime
`q ∉ S₀`, so it is not such a point. `H20AmbientS.lean` takes the ambient points over a larger
support `S₁` (the same `ambU`, with point support `S₁`) and replaces `hker` by inertia hypotheses.

* `ambU₀`, `ambU`, `ambRhoU`, `ambIotaU`, `alphaInfl`, **`thetaU`** (definitions), `thetaU_apply`.
* **`ambIotaU_equivariant`** (PROVED): `hιeq` for `(ambU, ρ₀, thetaU)`.
* `locPsiU`, `psiU₀_smul`; **`localTwistIdentificationU`**, **`oldPlaceInputU`** (PROVED): the
  coefficient/twist identification at `v ∈ P` (for `θ` restricting to `χ_h` on `p_v(G_{K_v})`;
  `thetaU_local` from the ELLIOT input), with the local module, `ψ`, `j_B` of `H20Twist.lean`.
* `inertiaFixesU`, `inertiaImage_le_U`, `ambIotaU_injective`, **`hPw_actualU`**, **`hur_actualU`**
  (PROVED): `hPw` and the unramified lifts for the presentation, with no further input.
* **Arbitrary transfer subgroups** `H ≤ ker(χ_h [π] ∘ infl)` (for the text `G_{H_R} ≤ G_{H_P}`):
  `thetaH`, `thetaH_compat` (the `hθ` of `h1_shapiro`), **`ambIotaU_equivariantH`**, `thetaH_local`,
  **`hPw_actualUH`**, **`hur_actualUH`** (for `H ⊇ ker(G_{K,S} → G_{K,S₀})`). The special case
  `H = ker(χ_h [π] ∘ infl)` is `thetaU`, `ambIotaU_equivariant`, `hPw_actualU`, `hur_actualU`.
* `dictJU`, `ambRhoU_oneTmul`, **`heegnerTransportOn_of_dictionaryU`** (PROVED): the transport of
  the Heegner point data into the untwisted ambient module from the explicit `ℚ̄ → K̄` dictionary of
  `H20Transport.lean`, with no condition on `χ_h`.

Kinds: definitions and PROVED.
-/

noncomputable section

namespace ZInQ.Contrib.CloudB3E2.NormCochain

open ZInQ.Contrib.CloudB3RC53.HeegnerCohomology.TwistedTransfer
open ZInQ.Manuscript.RC.PrintsArith
open ZInQ.Manuscript.RC.Wiring ZInQ.Manuscript.RC.SelmerComplex ZInQ.Manuscript.RC.CoefModules
open ZInQ.Manuscript.RC.KummerMaps
open ZInQ.Manuscript.RC.HeegnerAlgebra (Acoef)
open ZInQ.Contrib.CloudB3RC53.UnramifiedComplex ZInQ.Contrib.CloudB3RC53.RankCounts
open NumberField IsDedekindDomain TensorProduct WeierstrassCurve
open scoped WeierstrassCurve

attribute [local instance] groupRingTop ptSAction TopRep.distribMulAction TopRep.smulCommClass

set_option linter.unusedSectionVars false

/-! ### The untwisted ambient module -/

section U0

variable {K : Type} [Field K] [NumberField K] (S₀ : Set (HeightOneSpectrum (𝓞 K)))
  (W : WeierstrassCurve K) (Δ : Type) [CommGroup Δ]

/-- **The untwisted ambient module of points over `G_{K,S₀}`**: `ℤ[Δ] ⊗ E(K_{S₀})` with the plain
Galois action. Kind: definition. -/
abbrev ambU₀ : Type :=
  CoefMod (MonoidAlgebra ℤ Δ) (1 : GKS K S₀ →* (MonoidAlgebra ℤ Δ)ˣ) (PtS K S₀ W)

end U0

section Objects

variable {K : Type} [Field K] [NumberField K] {S S₀ : Set (HeightOneSpectrum (𝓞 K))}
  (hS : S₀ ⊆ S) (W : WeierstrassCurve K) [W.IsElliptic] (i : ℕ) [NeZero i] (s : KS K S₀) {h : K}
  (hs : s ^ 2 = algebraMap K (KS K S₀) h) (hs0 : s ≠ 0)
  {Δ : Type} [CommGroup Δ] [Finite Δ] (π : GKS K S₀ →* Δ)

/-- **The untwisted ambient module over `G_{K,S}`** (inflated). Kind: definition. -/
abbrev ambU (Δ : Type) [CommGroup Δ] : Type := ResMod (inflMap K hS) (ambU₀ S₀ W Δ)

/-- `ρ₀` on the untwisted ambient module. Kind: definition. -/
abbrev ambRhoU (Δ : Type) [CommGroup Δ] : GKS K S →* Module.End (MonoidAlgebra ℤ Δ) (ambU hS W Δ) :=
  DistribMulAction.toModuleEnd (MonoidAlgebra ℤ Δ) (ambU hS W Δ)

/-- **`ι = 1 ⊗ incl : shapMod → ambU`**. Kind: definition. -/
def ambIotaU : shapMod hS W i s hs hs0 π →ₗ[MonoidAlgebra ℤ Δ] ambU hS W Δ :=
  LinearMap.baseChange (MonoidAlgebra ℤ Δ) (torsIncl K S₀ W i)

/-- The Shapiro-level character `χ_h · [π]` on `G_{K,S}`. Kind: definition. -/
abbrev alphaInfl : GKS K S →* (MonoidAlgebra ℤ Δ)ˣ :=
  (alphaShap s hs hs0 π).comp (inflMap K hS : GKS K S →* GKS K S₀)

/-- **The transfer character `θ = χ_h · [π]`** of `G_{K,S} / ker(χ_h · [π])`. Kind: definition. -/
def thetaU : GKS K S ⧸ (alphaInfl hS s hs hs0 π).ker →* (MonoidAlgebra ℤ Δ)ˣ :=
  QuotientGroup.lift _ (alphaInfl hS s hs hs0 π) le_rfl

/-- **`θ(σ) = χ_h(σ) [π σ]`**: the point factor `a − θ(σ) − θ(σ)⁻¹` is the text's `a − z − z⁻¹`
with `z = χ_h(σ_q) Ψ(σ_q)` (tex 3915, 4158–4172). Kind: PROVED. -/
theorem thetaU_apply (g : GKS K S) :
    ((thetaU hS s hs hs0 π (g : GKS K S ⧸ (alphaInfl hS s hs hs0 π).ker) :
      (MonoidAlgebra ℤ Δ)ˣ) : MonoidAlgebra ℤ Δ) =
      ((quadChar s hs hs0 (inflMap K hS g) : ℤˣ) : MonoidAlgebra ℤ Δ) *
        MonoidAlgebra.of ℤ Δ (π (inflMap K hS g)) := by
  change ((alphaShap s hs hs0 π (inflMap K hS g) : (MonoidAlgebra ℤ Δ)ˣ) : MonoidAlgebra ℤ Δ) = _
  simp [alphaShap, charMul_apply, univChar, intUnitsTo]

end Objects

/-! ### The equivariance of `ι` -/

section Iota

variable {K : Type} [Field K] [NumberField K] {S S₀ : Set (HeightOneSpectrum (𝓞 K))}
  (hS : S₀ ⊆ S) (W : WeierstrassCurve K) [W.IsElliptic] (i : ℕ) [NeZero i] (s : KS K S₀) {h : K}
  (hs : s ^ 2 = algebraMap K (KS K S₀) h) (hs0 : s ≠ 0)
  [TopologicalSpace (Acoef i)] [DiscreteTopology (Acoef i)]
  {Δ : Type} [CommGroup Δ] [Finite Δ] (π : GKS K S₀ →* Δ)

/-- `ι` on the uninflated modules. Kind: definition. -/
def iotaU₀ : shapMod₀ W i s hs hs0 π →ₗ[MonoidAlgebra ℤ Δ] ambU₀ S₀ W Δ :=
  LinearMap.baseChange (MonoidAlgebra ℤ Δ) (torsIncl K S₀ W i)

/-- `ι₀(g m) = α(g) · g ι₀(m)`, `α = χ_h [π]`. Kind: PROVED. -/
theorem iotaU₀_smul (g₀ : GKS K S₀) (m : shapMod₀ W i s hs hs0 π) :
    iotaU₀ W i s hs hs0 π (g₀ • m) =
      ((alphaShap s hs hs0 π g₀ : (MonoidAlgebra ℤ Δ)ˣ) : MonoidAlgebra ℤ Δ) •
        (g₀ • iotaU₀ W i s hs hs0 π m) := by
  refine TensorProduct.induction_on (R := ℤ) (M := MonoidAlgebra ℤ Δ) (N := TorsT S₀ W i)
    (motive := fun z => iotaU₀ W i s hs hs0 π (g₀ • (show shapMod₀ W i s hs hs0 π from z)) =
      ((alphaShap s hs hs0 π g₀ : (MonoidAlgebra ℤ Δ)ˣ) : MonoidAlgebra ℤ Δ) •
        (g₀ • iotaU₀ W i s hs hs0 π (show shapMod₀ W i s hs hs0 π from z))) m ?_ ?_ ?_
  · change iotaU₀ W i s hs hs0 π (g₀ • (0 : shapMod₀ W i s hs hs0 π)) =
      _ • (g₀ • iotaU₀ W i s hs hs0 π 0)
    rw [smul_zero, map_zero, smul_zero, smul_zero]
  · intro a t
    have h1 := CoefMod.smul_tmul (MonoidAlgebra ℤ Δ) (alphaShap s hs hs0 π) (TorsT S₀ W i) g₀ a t
    have h2 := CoefMod.smul_tmul (MonoidAlgebra ℤ Δ) (1 : GKS K S₀ →* (MonoidAlgebra ℤ Δ)ˣ)
      (PtS K S₀ W) g₀ a (t : PtS K S₀ W)
    change iotaU₀ W i s hs hs0 π (g₀ • CoefMod.equiv _ _ _ (a ⊗ₜ t)) =
      _ • (g₀ • iotaU₀ W i s hs hs0 π (CoefMod.equiv _ _ _ (a ⊗ₜ t)))
    rw [h1]
    change (CoefMod.equiv _ _ _ (_ ⊗ₜ ((g₀ • t : TorsT S₀ W i) : PtS K S₀ W)) : ambU₀ S₀ W Δ) =
      _ • (g₀ • (CoefMod.equiv _ _ _ (a ⊗ₜ (t : PtS K S₀ W)) : ambU₀ S₀ W Δ))
    rw [h2]
    change (_ ⊗ₜ ((g₀ • t : TorsT S₀ W i) : PtS K S₀ W) : MonoidAlgebra ℤ Δ ⊗[ℤ] PtS K S₀ W) =
      ((alphaShap s hs hs0 π g₀ : (MonoidAlgebra ℤ Δ)ˣ) : MonoidAlgebra ℤ Δ) •
        (_ ⊗ₜ (g₀ • (t : PtS K S₀ W)) : MonoidAlgebra ℤ Δ ⊗[ℤ] PtS K S₀ W)
    rw [TensorProduct.smul_tmul', smul_eq_mul]
    congr 1
    simp
  · intro x y hx hy
    change iotaU₀ W i s hs hs0 π (g₀ • ((show shapMod₀ W i s hs hs0 π from x) +
        (show shapMod₀ W i s hs hs0 π from y))) =
      _ • (g₀ • iotaU₀ W i s hs hs0 π ((show shapMod₀ W i s hs hs0 π from x) +
        (show shapMod₀ W i s hs hs0 π from y)))
    rw [smul_add, map_add, hx, hy, map_add, smul_add, smul_add]

/-- **`ι` intertwines the Shapiro-level action with `R = θ ρ₀`**, `θ = thetaU` (PROVED): the
hypothesis `hιeq` of `h1_shapiro` for the untwisted ambient module. -/
theorem ambIotaU_equivariant (g : GKS K S) (m : shapMod hS W i s hs hs0 π) :
    ambIotaU hS W i s hs hs0 π (g • m) =
      R (alphaInfl hS s hs hs0 π).ker (ambRhoU hS W Δ) (thetaU hS s hs hs0 π) g
        (ambIotaU hS W i s hs hs0 π m) :=
  iotaU₀_smul W i s hs hs0 π (inflMap K hS g) m

/-- `ι` is injective (`ℤ[Δ]` flat). Kind: PROVED. -/
theorem ambIotaU_injective : Function.Injective (ambIotaU hS W i s hs hs0 π) := by
  have h := Module.Flat.lTensor_preserves_injective_linearMap (M := MonoidAlgebra ℤ Δ)
    (torsIncl K S₀ W i) Subtype.val_injective
  intro x y hxy
  apply h
  have := hxy
  change LinearMap.baseChange _ _ x = LinearMap.baseChange _ _ y at this
  rwa [LinearMap.baseChange_eq_lTensor] at this

end Iota

/-! ### The coefficient/twist identification -/

section Local

variable {K : Type} [Field K] [NumberField K] {S S₀ : Set (HeightOneSpectrum (𝓞 K))}
  (hS : S₀ ⊆ S) (W : WeierstrassCurve K) [W.IsElliptic] (i : ℕ) [NeZero i] (s : KS K S₀) {h : K}
  (hs : s ^ 2 = algebraMap K (KS K S₀) h) (hs0 : s ≠ 0) (hFull : FullTorsion K S₀ W (2 ^ i))
  [TopologicalSpace (Acoef i)] [DiscreteTopology (Acoef i)]
  {Δ : Type} [CommGroup Δ] [Finite Δ] (π : GKS K S₀ →* Δ)

/-- `1 ⊗ compPt` on the uninflated untwisted ambient module. Kind: definition. -/
def psiU₀ (v : HeightOneSpectrum (𝓞 K)) :
    ambU₀ S₀ W Δ →ₗ[MonoidAlgebra ℤ Δ] locL W s hs hs0 v Δ :=
  LinearMap.baseChange (MonoidAlgebra ℤ Δ) (compPt (S := S₀) W v).toIntLinearMap

/-- `ψ = 1 ⊗ compPt` on the untwisted ambient module. Kind: definition. -/
def locPsiU (v : HeightOneSpectrum (𝓞 K)) :
    ambU hS W Δ →ₗ[MonoidAlgebra ℤ Δ] locL W s hs hs0 v Δ :=
  psiU₀ W s hs hs0 v

/-- `ψ ∘ ι` agrees with the twisted instance (the same map on the same tensor product).
Kind: PROVED. -/
theorem locPsiU_iota (v : HeightOneSpectrum (𝓞 K)) (x : shapMod hS W i s hs hs0 π) :
    locPsiU hS W s hs hs0 v (ambIotaU hS W i s hs hs0 π x) =
      locPsi hS W s hs hs0 v (ambIota hS W i s hs hs0 π x) := rfl

/-- `ψ(g x) = χ_h(g) · σ ψ(x)` for `g = p_v(σ)`, i.e. `χ_h(p_v σ) ψ(p_v(σ) x) = σ ψ(x)`.
Kind: PROVED. -/
theorem psiU₀_smul (v : HeightOneSpectrum (𝓞 K)) (σ : Gloc K v) (x : ambU₀ S₀ W Δ) :
    ((chiZ s hs hs0 (Δ := Δ) (locMap K S₀ v σ) : (MonoidAlgebra ℤ Δ)ˣ) : MonoidAlgebra ℤ Δ) •
      psiU₀ W s hs hs0 v (locMap K S₀ v σ • x) = σ • psiU₀ W s hs hs0 v x := by
  refine TensorProduct.induction_on (R := ℤ) (M := MonoidAlgebra ℤ Δ) (N := PtS K S₀ W)
    (motive := fun z => ((chiZ s hs hs0 (Δ := Δ) (locMap K S₀ v σ) : (MonoidAlgebra ℤ Δ)ˣ) :
        MonoidAlgebra ℤ Δ) • psiU₀ W s hs hs0 v
          (locMap K S₀ v σ • (show ambU₀ S₀ W Δ from z)) =
      σ • psiU₀ W s hs hs0 v (show ambU₀ S₀ W Δ from z)) x ?_ ?_ ?_
  · change _ • psiU₀ W s hs hs0 v (locMap K S₀ v σ • (0 : ambU₀ S₀ W Δ)) =
      σ • psiU₀ W s hs hs0 v (0 : ambU₀ S₀ W Δ)
    simp only [smul_zero, map_zero]
  · intro a P
    have h1 := CoefMod.smul_tmul (MonoidAlgebra ℤ Δ) (1 : GKS K S₀ →* (MonoidAlgebra ℤ Δ)ˣ)
      (PtS K S₀ W) (locMap K S₀ v σ) a P
    have h2 := CoefMod.smul_tmul (MonoidAlgebra ℤ Δ)
      ((chiZ s hs hs0 (Δ := Δ)).comp (locMap K S₀ v : Gloc K v →* GKS K S₀)) (PtV W v) σ a
      (compPt (S := S₀) W v P)
    change _ • psiU₀ W s hs hs0 v (locMap K S₀ v σ • CoefMod.equiv _ _ _ (a ⊗ₜ P)) =
      σ • psiU₀ W s hs hs0 v (CoefMod.equiv _ _ _ (a ⊗ₜ P))
    rw [h1]
    change _ • (CoefMod.equiv _ _ _ (_ ⊗ₜ compPt (S := S₀) W v (locMap K S₀ v σ • P)) :
        locL W s hs hs0 v Δ) = σ • CoefMod.equiv _ _ _ (a ⊗ₜ compPt (S := S₀) W v P)
    rw [h2, ptS_smul_def, compPt_smul]
    change (_ ⊗ₜ _ : MonoidAlgebra ℤ Δ ⊗[ℤ] PtV W v) = (_ ⊗ₜ _ : MonoidAlgebra ℤ Δ ⊗[ℤ] PtV W v)
    simp
  · intro x y hx hy
    change _ • psiU₀ W s hs hs0 v (locMap K S₀ v σ • ((show ambU₀ S₀ W Δ from x) +
        (show ambU₀ S₀ W Δ from y))) =
      σ • psiU₀ W s hs hs0 v ((show ambU₀ S₀ W Δ from x) + (show ambU₀ S₀ W Δ from y))
    rw [smul_add, map_add, smul_add, hx, hy, map_add, smul_add]

/-- `χ_h(p_v σ) ψ(p_v(σ) x) = σ ψ(x)`. Kind: PROVED. -/
theorem psiU_smul (v : HeightOneSpectrum (𝓞 K)) (σ : Gloc K v) (x : ambU hS W Δ) :
    ((chiZ s hs hs0 (Δ := Δ) (locMap K S₀ v σ) : (MonoidAlgebra ℤ Δ)ˣ) : MonoidAlgebra ℤ Δ) •
      locPsiU hS W s hs hs0 v (locMap K S v σ • x) = σ • locPsiU hS W s hs hs0 v x := by
  change _ • psiU₀ W s hs hs0 v
      (inflMap K hS (locMap K S v σ) • (show ambU₀ S₀ W Δ from x)) =
    σ • psiU₀ W s hs hs0 v (show ambU₀ S₀ W Δ from x)
  rw [locMap_compat K hS v σ]
  exact psiU₀_smul W s hs hs0 v σ x

open scoped Classical in
/-- **`LocalTwistIdentification` for the untwisted ambient module** (PROVED; tex 3251–3270,
3413–3438): at an old place `v ∈ P`, for any normal `H` and character `θ` restricting to `χ_h` on
`p_v(G_{K_v})`, with `ι = ambIotaU`, `ψ = locPsiU`, `j_B = locJB`. -/
theorem localTwistIdentificationU (v : Places K S) (H : Subgroup (GKS K S)) [H.Normal]
    (θ : GKS K S ⧸ H →* (MonoidAlgebra ℤ Δ)ˣ)
    (hθ : ∀ σ : Gloc K v.1, θ ((locMap K S v.1 σ : GKS K S) : GKS K S ⧸ H) =
      chiZ s hs hs0 (Δ := Δ) (locMap K S₀ v.1 σ))
    [(localTwist W h v.1).IsElliptic] :
    LocalTwistIdentification (ambRhoU hS W Δ) H θ (ambIotaU hS W i s hs hs0 π)
      (localTwist W h v.1) (2 ^ i) (locMap K S v.1 : Gloc K v.1 →* GKS K S)
      ((ofResModAdd (locMap K S v.1) (shapMod hS W i s hs hs0 π)).comp
        (shapIota hS W i s hs hs0 hFull π v))
      (locPsiU hS W s hs hs0 v.1) (locJB W s hs hs0 v.1 (Δ := Δ)) := by
  obtain ⟨h1, h2, -, h4, h5⟩ := localTwistIdentification_actual hS W i s hs hs0 hFull π v ⊥
    (1 : GKS K S ⧸ (⊥ : Subgroup (GKS K S)) →* (MonoidAlgebra ℤ Δ)ˣ) (fun _ => rfl)
  refine ⟨h1, h2, fun σ x => ?_, h4, h5⟩
  change locPsiU hS W s hs hs0 v.1 ((((θ ((locMap K S v.1 σ : GKS K S) : GKS K S ⧸ H) :
    (MonoidAlgebra ℤ Δ)ˣ) : MonoidAlgebra ℤ Δ) • ambRhoU hS W Δ (locMap K S v.1 σ)) x) = _
  rw [hθ σ, LinearMap.smul_apply, LinearMap.map_smul]
  exact psiU_smul hS W s hs hs0 v.1 σ x

open scoped Classical in
/-- **`OldPlaceInput` for the untwisted ambient module from the realization alone** (PROVED). -/
theorem oldPlaceInputU (v : Places K S) (H : Subgroup (GKS K S)) [H.Normal]
    [Fintype (GKS K S ⧸ H)] (r : GKS K S ⧸ H → GKS K S)
    (θ : GKS K S ⧸ H →* (MonoidAlgebra ℤ Δ)ˣ)
    (hθ : ∀ σ : Gloc K v.1, θ ((locMap K S v.1 σ : GKS K S) : GKS K S ⧸ H) =
      chiZ s hs hs0 (Δ := Δ) (locMap K S₀ v.1 σ))
    [(localTwist W h v.1).IsElliptic] (y : ambU hS W Δ)
    {J : Type} (sJ : Finset J) (a : J → MonoidAlgebra ℤ Δ)
    (P : J → (localTwist W h v.1).toAffine.Point)
    (hreal : locPsiU hS W s hs hs0 v.1 (wsum (ambRhoU hS W Δ) H r θ y) =
      ∑ j ∈ sJ, a j • locJB W s hs hs0 v.1 (Δ := Δ)
        (basePt (v.1.adicCompletion K) (localTwist W h v.1) (P j))) :
    OldPlaceInput (ambRhoU hS W Δ) H r θ v.1 (localTwist W h v.1) (2 ^ i)
      (shapIota hS W i s hs hs0 hFull π v) (ambIotaU hS W i s hs hs0 π) y :=
  ⟨locL W s hs hs0 v.1 Δ, inferInstance, inferInstance, inferInstance, inferInstance,
    locPsiU hS W s hs hs0 v.1, locJB W s hs hs0 v.1 (Δ := Δ),
    localTwistIdentificationU hS W i s hs hs0 hFull π v H θ hθ, J, sJ, a, P, hreal⟩

/-- **`θ = χ_h [π]` restricts to `χ_h` at the places of `P`** (PROVED from the ELLIOT input). -/
theorem thetaU_local {P : Set (HeightOneSpectrum (𝓞 K))} (ψ : Δ →* (Acoef i)ˣ)
    (hψ : Function.Injective ψ) (hΨ : PsiTrivialAt2N i π ψ P) {v : HeightOneSpectrum (𝓞 K)}
    (hv : v ∈ P) (σ : Gloc K v) :
    thetaU hS s hs hs0 π ((locMap K S v σ : GKS K S) : GKS K S ⧸ (alphaInfl hS s hs hs0 π).ker) =
      chiZ s hs hs0 (Δ := Δ) (locMap K S₀ v σ) := by
  change alphaShap s hs hs0 π (inflMap K hS (locMap K S v σ)) = _
  rw [locMap_compat K hS v σ, alphaShap, charMul_apply, MonoidHom.comp_apply,
    MonoidHom.comp_apply, pi_trivial_of_psi i π ψ hψ hΨ hv σ, map_one, mul_one]

end Local

/-! ### `hPw` and the unramified lifts -/

section Unramified

variable {K : Type} [Field K] [NumberField K] {S S₀ : Set (HeightOneSpectrum (𝓞 K))}
  (hS : S₀ ⊆ S) (W : WeierstrassCurve K) [W.IsElliptic] (i : ℕ) [NeZero i] (s : KS K S₀) {h : K}
  (hs : s ^ 2 = algebraMap K (KS K S₀) h) (hs0 : s ≠ 0)
  [TopologicalSpace (Acoef i)] [DiscreteTopology (Acoef i)]
  {Δ : Type} [CommGroup Δ] [Finite Δ] (π : GKS K S₀ →* Δ) (w : Places K S) (hw : w.1 ∉ S₀)

include hw in
/-- `InertiaFixesDivisionPoint` for the untwisted ambient module (inflated from `G_{K,S₀}`).
Kind: PROVED. -/
theorem inertiaFixesU (Q : ambU hS W Δ) :
    InertiaFixesDivisionPoint (ambRhoU hS W Δ) (inertiaImage w) Q :=
  inertiaFixes_of_inflated hS w hw _ fun g hg => by
    change (inflMap K hS g • (show ambU₀ S₀ W Δ from Q) : ambU₀ S₀ W Δ) = Q
    rw [hg, one_smul]

include hw in
/-- The inertia image at `w ∉ S₀` lies in `ker(χ_h [π] ∘ infl)`. Kind: PROVED. -/
theorem inertiaImage_le_U :
    inertiaImage w ⊆ ((alphaInfl hS s hs hs0 π).ker : Set (GKS K S)) :=
  inertiaImage_le_of_ker hS w hw _ fun g hg => by
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply]
    change alphaShap s hs hs0 π (inflMap K hS g) = 1
    rw [hg, map_one]

include hw in
/-- **`hPw` for the untwisted ambient module** (PROVED; tex 3471–3487). -/
theorem hPw_actualU [IsOpenKer (alphaShap s hs hs0 π)]
    [Fintype (GKS K S ⧸ (alphaInfl hS s hs hs0 π).ker)]
    (r : GKS K S ⧸ (alphaInfl hS s hs hs0 π).ker → GKS K S)
    (hr : ∀ δ, ((r δ : GKS K S) : GKS K S ⧸ (alphaInfl hS s hs hs0 π).ker) = δ)
    [ContinuousSMul (GUr K w.1)
      (urRep (MonoidAlgebra ℤ Δ) (shapMod₀ W i s hs hs0 π) (newPlace w hw)).V]
    (kk : ℤ) {Q y : ambU hS W Δ} (hQ : kk • Q = y)
    (a : (globalCx (MonoidAlgebra ℤ Δ) (GKS K S) (shapMod hS W i s hs hs0 π)).X 1)
    (hz : ∀ g : Fin 1 → GKS K S,
      ambIotaU hS W i s hs hs0 π
          (gval (A := MonoidAlgebra ℤ Δ) (M := shapMod hS W i s hs hs0 π) a g) =
        T (alphaInfl hS s hs hs0 π).ker r hr (ambRhoU hS W Δ) (thetaU hS s hs hs0 π) 1
          (kummerCochain (ambRhoU hS W Δ) (alphaInfl hS s hs hs0 π).ker Q) g) :
    ∃ y : (genuineUq K S (MonoidAlgebra ℤ Δ) w
        (urRep (MonoidAlgebra ℤ Δ) (shapMod₀ W i s hs hs0 π) (newPlace w hw))).X 1,
      (genuineιq K S (MonoidAlgebra ℤ Δ) (shapMod hS W i s hs hs0 π) w
        (urRep (MonoidAlgebra ℤ Δ) (shapMod₀ W i s hs hs0 π) (newPlace w hw))
        (urId hS (MonoidAlgebra ℤ Δ) (shapMod₀ W i s hs hs0 π) (newPlace w hw))
        (urId_compat hS (MonoidAlgebra ℤ Δ) (shapMod₀ W i s hs hs0 π) w hw)).f 1 1 rfl y =
      (stageRes K S (MonoidAlgebra ℤ Δ) (shapMod hS W i s hs hs0 π) w).f 1 1 rfl a :=
  hPw_of_transfer hS (MonoidAlgebra ℤ Δ) (shapMod₀ W i s hs hs0 π) (ambRhoU hS W Δ)
    (alphaInfl hS s hs hs0 π).ker r hr (thetaU hS s hs hs0 π) (ambIotaU hS W i s hs hs0 π)
    (ambIotaU_injective hS W i s hs hs0 π) (ambIotaU_equivariant hS W i s hs hs0 π) w hw kk hQ a
    hz (inertiaImage_le_U hS s hs hs0 π w hw) (inertiaFixesU hS W w hw Q)

end Unramified

section UnramifiedLifts

variable {K : Type} [Field K] [NumberField K] {S S₀ : Set (HeightOneSpectrum (𝓞 K))}
  (hS : S₀ ⊆ S) (W : WeierstrassCurve K) [W.IsElliptic] (i : ℕ) [NeZero i] (s : KS K S₀) {h : K}
  (hs : s ^ 2 = algebraMap K (KS K S₀) h) (hs0 : s ≠ 0)
  [TopologicalSpace (Acoef i)] [DiscreteTopology (Acoef i)]
  {Δ : Type} [CommGroup Δ] [Finite Δ] (π : GKS K S₀ →* Δ) [IsOpenKer (alphaShap s hs hs0 π)]
  {ι : Type} (place : ι × Bool → Places K S) (hw : ∀ j, (place j).1 ∉ S₀)
  [∀ j, ContinuousSMul (GUr K (place j).1)
    (urRep (MonoidAlgebra ℤ Δ) (shapMod₀ W i s hs hs0 π) (newPlace (place j) (hw j))).V]

/-- **The unramified lifts `hurR`/`hurP` for the untwisted ambient module** (PROVED;
`hPw_actualU`): a genuine class carried by `ambIotaU` to `𝒯_θ(κ(Q))`, `θ = χ_h [π]`, has an
unramified lift at every place above an unused prime. -/
theorem hur_actualU [Fintype (GKS K S ⧸ (alphaInfl hS s hs hs0 π).ker)]
    (r : GKS K S ⧸ (alphaInfl hS s hs hs0 π).ker → GKS K S)
    (hr : ∀ δ, ((r δ : GKS K S) : GKS K S ⧸ (alphaInfl hS s hs hs0 π).ker) = δ)
    (kk : ℤ) {Q y : ambU hS W Δ} (hQ : kk • Q = y)
    (a : (globalCx (MonoidAlgebra ℤ Δ) (GKS K S) (shapMod hS W i s hs hs0 π)).X 1)
    (hz : ∀ g : Fin 1 → GKS K S,
      ambIotaU hS W i s hs hs0 π
          (gval (A := MonoidAlgebra ℤ Δ) (M := shapMod hS W i s hs hs0 π) a g) =
        T (alphaInfl hS s hs hs0 π).ker r hr (ambRhoU hS W Δ) (thetaU hS s hs hs0 π) 1
          (kummerCochain (ambRhoU hS W Δ) (alphaInfl hS s hs hs0 π).ker Q) g)
    (j : ι × Bool) :
    ∃ u, (genuineιq K S (MonoidAlgebra ℤ Δ) (shapMod hS W i s hs hs0 π) (place j)
        (urRep (MonoidAlgebra ℤ Δ) (shapMod₀ W i s hs hs0 π) (newPlace (place j) (hw j)))
        (urId hS (MonoidAlgebra ℤ Δ) (shapMod₀ W i s hs hs0 π) (newPlace (place j) (hw j)))
        (urId_compat hS (MonoidAlgebra ℤ Δ) (shapMod₀ W i s hs hs0 π) (place j) (hw j))).f 1 1 rfl
          u =
      (natHom (resCochains (k := MonoidAlgebra ℤ Δ) (M := shapMod hS W i s hs hs0 π)
        (locMap K S (place j).1))).f 1 1 rfl a :=
  hPw_actualU hS W i s hs hs0 π (place j) (hw j) r hr kk hQ a hz

end UnramifiedLifts

/-! ### Arbitrary transfer subgroups `H ≤ ker(χ_h [π] ∘ infl)` -/

section General

variable {K : Type} [Field K] [NumberField K] {S S₀ : Set (HeightOneSpectrum (𝓞 K))}
  (hS : S₀ ⊆ S) (W : WeierstrassCurve K) [W.IsElliptic] (i : ℕ) [NeZero i] (s : KS K S₀) {h : K}
  (hs : s ^ 2 = algebraMap K (KS K S₀) h) (hs0 : s ≠ 0)
  [TopologicalSpace (Acoef i)] [DiscreteTopology (Acoef i)]
  {Δ : Type} [CommGroup Δ] [Finite Δ] (π : GKS K S₀ →* Δ)
  (H : Subgroup (GKS K S)) [H.Normal] (hH : H ≤ (alphaInfl hS s hs hs0 π).ker)

/-- **The transfer character `θ_H = χ_h [π]` of `G_{K,S}/H`** for a normal `H` on which `χ_h [π]`
is trivial (for the text: `H = G_{H_R}`, `G_{H_P}`). Kind: definition. -/
def thetaH : GKS K S ⧸ H →* (MonoidAlgebra ℤ Δ)ˣ :=
  QuotientGroup.lift H (alphaInfl hS s hs hs0 π) hH

theorem thetaH_mk (g : GKS K S) :
    thetaH hS s hs hs0 π H hH (g : GKS K S ⧸ H) = alphaShap s hs hs0 π (inflMap K hS g) := rfl

/-- **The compatibility `hθ` of `h1_shapiro`** for two transfer subgroups (PROVED): both
characters are `χ_h [π]`. -/
theorem thetaH_compat (H' : Subgroup (GKS K S)) [H'.Normal]
    (hH' : H' ≤ (alphaInfl hS s hs hs0 π).ker) (x : GKS K S) :
    ((thetaH hS s hs hs0 π H hH (x : GKS K S ⧸ H) : (MonoidAlgebra ℤ Δ)ˣ) : MonoidAlgebra ℤ Δ) =
      thetaH hS s hs hs0 π H' hH' (x : GKS K S ⧸ H') := rfl

/-- **`hιeq` for an arbitrary transfer subgroup `H ≤ ker(χ_h [π] ∘ infl)`** (PROVED). -/
theorem ambIotaU_equivariantH (g : GKS K S) (m : shapMod hS W i s hs hs0 π) :
    ambIotaU hS W i s hs hs0 π (g • m) =
      R H (ambRhoU hS W Δ) (thetaH hS s hs hs0 π H hH) g (ambIotaU hS W i s hs hs0 π m) :=
  iotaU₀_smul W i s hs hs0 π (inflMap K hS g) m

/-- **`θ_H` restricts to `χ_h` at the places of `P`** (PROVED from the ELLIOT input). -/
theorem thetaH_local {P : Set (HeightOneSpectrum (𝓞 K))} (ψ : Δ →* (Acoef i)ˣ)
    (hψ : Function.Injective ψ) (hΨ : PsiTrivialAt2N i π ψ P) {v : HeightOneSpectrum (𝓞 K)}
    (hv : v ∈ P) (σ : Gloc K v) :
    thetaH hS s hs hs0 π H hH ((locMap K S v σ : GKS K S) : GKS K S ⧸ H) =
      chiZ s hs hs0 (Δ := Δ) (locMap K S₀ v σ) :=
  thetaU_local hS i s hs hs0 π ψ hψ hΨ hv σ

variable (w : Places K S) (hw : w.1 ∉ S₀)

include hw in
/-- **`hPw` for the untwisted ambient module and an arbitrary transfer subgroup** (PROVED; tex
3471–3487): for `H` containing `ker(G_{K,S} → G_{K,S₀})` (its fixed field lies in `K_{S₀}`; for a
ring class field `H_f` this holds only when the primes dividing `f` lie in `S₀`,
`RingClassKS.ringClassField_le_KS`; it fails for `H_{dq}` at a switch prime `q ∉ S₀`, where
`H20AmbientS.hPw_actualS` applies). -/
theorem hPw_actualUH [IsOpenKer (alphaShap s hs hs0 π)] [Fintype (GKS K S ⧸ H)]
    (hker : ∀ g : GKS K S, inflMap K hS g = 1 → g ∈ H)
    (r : GKS K S ⧸ H → GKS K S) (hr : ∀ δ, ((r δ : GKS K S) : GKS K S ⧸ H) = δ)
    [ContinuousSMul (GUr K w.1)
      (urRep (MonoidAlgebra ℤ Δ) (shapMod₀ W i s hs hs0 π) (newPlace w hw)).V]
    (kk : ℤ) {Q y : ambU hS W Δ} (hQ : kk • Q = y)
    (a : (globalCx (MonoidAlgebra ℤ Δ) (GKS K S) (shapMod hS W i s hs hs0 π)).X 1)
    (hz : ∀ g : Fin 1 → GKS K S,
      ambIotaU hS W i s hs hs0 π
          (gval (A := MonoidAlgebra ℤ Δ) (M := shapMod hS W i s hs hs0 π) a g) =
        T H r hr (ambRhoU hS W Δ) (thetaH hS s hs hs0 π H hH) 1
          (kummerCochain (ambRhoU hS W Δ) H Q) g) :
    ∃ y : (genuineUq K S (MonoidAlgebra ℤ Δ) w
        (urRep (MonoidAlgebra ℤ Δ) (shapMod₀ W i s hs hs0 π) (newPlace w hw))).X 1,
      (genuineιq K S (MonoidAlgebra ℤ Δ) (shapMod hS W i s hs hs0 π) w
        (urRep (MonoidAlgebra ℤ Δ) (shapMod₀ W i s hs hs0 π) (newPlace w hw))
        (urId hS (MonoidAlgebra ℤ Δ) (shapMod₀ W i s hs hs0 π) (newPlace w hw))
        (urId_compat hS (MonoidAlgebra ℤ Δ) (shapMod₀ W i s hs hs0 π) w hw)).f 1 1 rfl y =
      (stageRes K S (MonoidAlgebra ℤ Δ) (shapMod hS W i s hs hs0 π) w).f 1 1 rfl a :=
  hPw_of_transfer hS (MonoidAlgebra ℤ Δ) (shapMod₀ W i s hs hs0 π) (ambRhoU hS W Δ)
    H r hr (thetaH hS s hs hs0 π H hH) (ambIotaU hS W i s hs hs0 π)
    (ambIotaU_injective hS W i s hs hs0 π) (ambIotaU_equivariantH hS W i s hs hs0 π H hH) w hw kk
    hQ a hz (inertiaImage_le_of_ker hS w hw H hker) (inertiaFixesU hS W w hw Q)

end General

section GeneralLifts

variable {K : Type} [Field K] [NumberField K] {S S₀ : Set (HeightOneSpectrum (𝓞 K))}
  (hS : S₀ ⊆ S) (W : WeierstrassCurve K) [W.IsElliptic] (i : ℕ) [NeZero i] (s : KS K S₀) {h : K}
  (hs : s ^ 2 = algebraMap K (KS K S₀) h) (hs0 : s ≠ 0)
  [TopologicalSpace (Acoef i)] [DiscreteTopology (Acoef i)]
  {Δ : Type} [CommGroup Δ] [Finite Δ] (π : GKS K S₀ →* Δ) [IsOpenKer (alphaShap s hs hs0 π)]
  (H : Subgroup (GKS K S)) [H.Normal] (hH : H ≤ (alphaInfl hS s hs hs0 π).ker)
  {ι : Type} (place : ι × Bool → Places K S) (hw : ∀ j, (place j).1 ∉ S₀)
  [∀ j, ContinuousSMul (GUr K (place j).1)
    (urRep (MonoidAlgebra ℤ Δ) (shapMod₀ W i s hs hs0 π) (newPlace (place j) (hw j))).V]

/-- **The unramified lifts `hurR`/`hurP` for an arbitrary transfer subgroup** (PROVED;
`hPw_actualUH`): for `H ≤ ker(χ_h [π] ∘ infl)` containing `ker(G_{K,S} → G_{K,S₀})` (e.g.
`H = G_{H_R}` only when `H_R ⊆ K_{S₀}`; at a switch prime outside `S₀` use
`H20AmbientS.hur_actualS`). -/
theorem hur_actualUH [Fintype (GKS K S ⧸ H)]
    (hker : ∀ g : GKS K S, inflMap K hS g = 1 → g ∈ H)
    (r : GKS K S ⧸ H → GKS K S) (hr : ∀ δ, ((r δ : GKS K S) : GKS K S ⧸ H) = δ)
    (kk : ℤ) {Q y : ambU hS W Δ} (hQ : kk • Q = y)
    (a : (globalCx (MonoidAlgebra ℤ Δ) (GKS K S) (shapMod hS W i s hs hs0 π)).X 1)
    (hz : ∀ g : Fin 1 → GKS K S,
      ambIotaU hS W i s hs hs0 π
          (gval (A := MonoidAlgebra ℤ Δ) (M := shapMod hS W i s hs hs0 π) a g) =
        T H r hr (ambRhoU hS W Δ) (thetaH hS s hs hs0 π H hH) 1
          (kummerCochain (ambRhoU hS W Δ) H Q) g)
    (j : ι × Bool) :
    ∃ u, (genuineιq K S (MonoidAlgebra ℤ Δ) (shapMod hS W i s hs hs0 π) (place j)
        (urRep (MonoidAlgebra ℤ Δ) (shapMod₀ W i s hs hs0 π) (newPlace (place j) (hw j)))
        (urId hS (MonoidAlgebra ℤ Δ) (shapMod₀ W i s hs hs0 π) (newPlace (place j) (hw j)))
        (urId_compat hS (MonoidAlgebra ℤ Δ) (shapMod₀ W i s hs hs0 π) (place j) (hw j))).f 1 1 rfl
          u =
      (natHom (resCochains (k := MonoidAlgebra ℤ Δ) (M := shapMod hS W i s hs hs0 π)
        (locMap K S (place j).1))).f 1 1 rfl a :=
  hPw_actualUH hS W i s hs hs0 π H hH (place j) (hw j) hker r hr kk hQ a hz

end GeneralLifts

/-! ### The transport into the untwisted ambient module -/

section Transport

variable {K : Type} [Field K] [NumberField K] (E : WeierstrassCurve ℚ)
  {S S₀ : Set (HeightOneSpectrum (𝓞 K))} (hS : S₀ ⊆ S) [(E.baseChange K).IsElliptic]
  {Δ : Type} [CommGroup Δ] [Finite Δ]

/-- `x ↦ 1 ⊗ x` on the points of `E(ℚ̄)` realized in `E(K_{S₀})`, into the untwisted ambient
module. Kind: definition. -/
def dictJU (κ : Qbar →ₐ[ℚ] AlgebraicClosure K) :
    dictΛ (S₀ := S₀) E κ →+ ambU hS (E.baseChange K) Δ :=
  (TensorProduct.mk ℤ (MonoidAlgebra ℤ Δ) (PtS K S₀ (E.baseChange K)) 1).toAddMonoidHom.comp
    (preS E κ)

/-- The value of `dictJU` at a realized point. Kind: PROVED. -/
theorem dictJU_apply (κ : Qbar →ₐ[ℚ] AlgebraicClosure K) (x : (E⁄Qbar).toAffine.Point)
    (P : PtS K S₀ (E.baseChange K)) (hx : compQ E κ x = incS S₀ (E.baseChange K) P) :
    dictJU E hS (Δ := Δ) κ ⟨x, ⟨P, hx.symm⟩⟩ =
      ((1 : MonoidAlgebra ℤ Δ) ⊗ₜ P : MonoidAlgebra ℤ Δ ⊗[ℤ] PtS K S₀ (E.baseChange K)) := by
  change (1 : MonoidAlgebra ℤ Δ) ⊗ₜ[ℤ] preS (S₀ := S₀) E κ ⟨x, ⟨P, hx.symm⟩⟩ = _
  rw [preS_eq E κ x P hx]

/-- `ρ₀(g)(1 ⊗ P) = 1 ⊗ g P`. Kind: PROVED. -/
theorem ambRhoU_oneTmul (g : GKS K S) (P : PtS K S₀ (E.baseChange K)) :
    ambRhoU hS (E.baseChange K) Δ g
      ((1 : MonoidAlgebra ℤ Δ) ⊗ₜ P : MonoidAlgebra ℤ Δ ⊗[ℤ] PtS K S₀ (E.baseChange K)) =
      ((1 : MonoidAlgebra ℤ Δ) ⊗ₜ (inflMap K hS g • P) :
        MonoidAlgebra ℤ Δ ⊗[ℤ] PtS K S₀ (E.baseChange K)) := by
  have h1 := CoefMod.smul_tmul (MonoidAlgebra ℤ Δ) (1 : GKS K S₀ →* (MonoidAlgebra ℤ Δ)ˣ)
    (PtS K S₀ (E.baseChange K)) (inflMap K hS g) 1 P
  change (inflMap K hS g • CoefMod.equiv _ _ _ ((1 : MonoidAlgebra ℤ Δ) ⊗ₜ P) :
    ambU₀ S₀ (E.baseChange K) Δ) = CoefMod.equiv _ _ _ (_ ⊗ₜ _)
  rw [h1]
  congr 2
  simp

variable (HP : Subgroup (GKS K S)) (U : Subgroup HP) [Fintype (HP ⧸ U)] (t : HP ⧸ U → HP)

/-- **`HeegnerTransportOn` into the untwisted ambient module from the explicit `ℚ̄ → K̄`
dictionary** (PROVED; tex 2914–2936): the realization of `y_{dq}`, `y_d` in `E(K_{S₀})` along `κ`
and the matching of `relGal d q` with the transversal and of `frob` with `σ`; no condition on
`χ_h` (its sign is carried by `θ = χ_h [π]`, `thetaU_apply`). -/
theorem heegnerTransportOn_of_dictionaryU (D : HeegnerPointData E) (d q : ℕ) (σ : GKS K S)
    (κ : Qbar →ₐ[ℚ] AlgebraicClosure K) (PR PP : PtS K S₀ (E.baseChange K))
    (hR : compQ E κ (D.y (d * q)) = incS S₀ (E.baseChange K) PR)
    (hP : compQ E κ (D.y d) = incS S₀ (E.baseChange K) PP)
    (e : HP ⧸ U ≃ D.relGal d q)
    (hτ : ∀ τ, compQ E κ (Affine.Point.map (e τ).1.toAlgHom (D.y (d * q))) =
      incS S₀ (E.baseChange K) (inflMap K hS (t τ : GKS K S) • PR))
    (hf : compQ E κ (Affine.Point.map (D.frob d q).toAlgHom (D.y d)) =
      incS S₀ (E.baseChange K) (inflMap K hS σ • PP))
    (hfi : compQ E κ (Affine.Point.map (D.frob d q)⁻¹.toAlgHom (D.y d)) =
      incS S₀ (E.baseChange K) (inflMap K hS σ⁻¹ • PP)) :
    HeegnerTransportOn (ambRhoU hS (E.baseChange K) Δ) HP U t D d q σ
      ((1 : MonoidAlgebra ℤ Δ) ⊗ₜ PR : MonoidAlgebra ℤ Δ ⊗[ℤ] PtS K S₀ (E.baseChange K))
      ((1 : MonoidAlgebra ℤ Δ) ⊗ₜ PP : MonoidAlgebra ℤ Δ ⊗[ℤ] PtS K S₀ (E.baseChange K)) := by
  refine ⟨_, dictJU E hS (Δ := Δ) κ, e, ⟨PR, hR.symm⟩, ⟨PP, hP.symm⟩,
    fun τ => ⟨_, (hτ τ).symm⟩, ⟨_, hf.symm⟩, ⟨_, hfi.symm⟩,
    dictJU_apply E hS κ _ PR hR, dictJU_apply E hS κ _ PP hP, fun τ => ?_, ?_, ?_⟩
  · rw [dictJU_apply E hS κ _ _ (hτ τ)]
    exact ambRhoU_oneTmul E hS _ PR
  · rw [dictJU_apply E hS κ _ _ hf]
    exact (ambRhoU_oneTmul E hS _ PP).symm
  · rw [dictJU_apply E hS κ _ _ hfi]
    exact (ambRhoU_oneTmul E hS _ PP).symm

end Transport

end ZInQ.Contrib.CloudB3E2.NormCochain
