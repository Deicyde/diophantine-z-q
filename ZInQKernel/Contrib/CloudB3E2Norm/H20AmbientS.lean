import ZInQKernel.Contrib.CloudB3E2Norm.H20Real
import ZInQKernel.Contrib.CloudB3E2Norm.H20DictFields

/-!
# The ambient module of points over a larger support

Manuscript `diophantine_zq.tex`, tex 2914–2936, 3080–3084, 3251–3262, 3471–3487, 4157–4170.

**Why.** `H20Untwisted.lean` takes the ambient module of points to be `ℤ[Δ] ⊗ E(K_{S₀})` with `S₀`
the support of the coefficient module. The Heegner point `y_{dq}` of a step of the chain lies over
the ring class field `H_{dq}`, which is ramified at the switch prime `q`; the switch primes lie
outside `S₀` (the unramified conditions of the presentation sit there), so `y_{dq}` is not a point
of `E(K_{S₀})`, and the hypothesis `hker` of `hPw_actualUH` (the fixed field of the transfer
subgroup inside `K_{S₀}`) fails for `H = G_{H_{dq}}`. **This file** takes the ambient points over a
larger support `S₁` (`S₀ ⊆ S₁ ⊆ S`; for the text `S₁` contains the primes of the chain), keeps the
coefficient module over `S₀`, and replaces `hker` by the inertia hypotheses at the place used.

* `ksIncl`, `ptMap` (definitions): `K_{S₀} ⊆ K_{S₁}` and `E(K_{S₀}) → E(K_{S₁})`; `ptMap_injective`,
  `ksIncl_infl`, `ptMap_smul`, `inflMap_trans`, `compPt_ptMap` (PROVED).
* The ambient module `ambU h1 W Δ = ℤ[Δ] ⊗ E(K_{S₁})` (`H20Untwisted`, with point support `S₁`),
  the transfer character `thetaH hS s hs hs0 π H hH = χ_h [π]` of the coefficient module
  (unchanged).
* `ambIotaS` (definition), **`ambIotaS_equivariantH`**, `ambIotaS_injective` (PROVED):
  `ι = 1 ⊗ incl` from the coefficient module into the ambient module, and the hypothesis `hιeq`
  of `h1_shapiro`.
* `locPsiS`, `psiS_smul`, `locPsiS_iota`, **`localTwistIdentificationS`**, **`oldPlaceInputS`**
  (PROVED): the coefficient/twist identification at `v ∈ P`.
* `realFS`, `realXS`, `smul_realXS`, `exists_twist_pointS`, `psi_wsumS`, **`hreal_actualS`**,
  **`oldPlaceInput_of_pointS`** (PROVED): the realization (local Mackey on points) for a point
  `P ∈ E(K_{S₁})` fixed by the transfer subgroup, and the old-place input from it.
* `ptMapT`, `ptMapT_smul`, `inertiaFixes_of_support` (PROVED): a point coming from `E(K_{S''})`
  with `w ∉ S''` is fixed by the inertia at `w`; **`hPw_actualS`**, **`hur_actualS`** (PROVED):
  `hPw` and the unramified lifts with the hypotheses `hunr : inertiaImage w ⊆ H` and
  `InertiaFixesDivisionPoint` (no `hker`).

The Heegner dictionary (`H20Dictionary`, `H20DictFields`) and the transport
(`heegnerTransportOn_of_dictionaryU`) are stated for the ambient module of any point support and
apply with point support `S₁` (their `S₀ := S₁`).

Kinds: definitions and PROVED.
-/

noncomputable section

namespace ZInQ.Contrib.CloudB3E2.NormCochain

open ZInQ.Contrib.CloudB3RC53.HeegnerCohomology.TwistedTransfer
open ZInQ.Manuscript.RC.Wiring ZInQ.Manuscript.RC.SelmerComplex ZInQ.Manuscript.RC.CoefModules
open ZInQ.Manuscript.RC.KummerMaps
open ZInQ.Manuscript.RC.HeegnerAlgebra (Acoef)
open ZInQ.Contrib.CloudB3RC53.RankCounts (unramifiedOutside unramifiedOutside_mono resAbs
  resAbs_apply_coe resAbs_surjective resUnr_comp)
open ZInQ.Contrib.CloudB3RC53.UnramifiedComplex
open ZInQ.Contrib.CloudB3RC53.RankCounts (GUr)
open NumberField IsDedekindDomain TensorProduct WeierstrassCurve

attribute [local instance] groupRingTop ptSAction TopRep.distribMulAction TopRep.smulCommClass

set_option linter.unusedSectionVars false

/-! ### The point map `E(K_{S₀}) → E(K_{S₁})` -/

section PtMap

variable {K : Type} [Field K] [NumberField K] {S₀ S₁ : Set (HeightOneSpectrum (𝓞 K))}
  (h01 : S₀ ⊆ S₁) (W : WeierstrassCurve K)

/-- `K_{S₀} ⊆ K_{S₁}`. Kind: definition. -/
def ksIncl : KS K S₀ →ₐ[K] KS K S₁ :=
  IntermediateField.inclusion (unramifiedOutside_mono K h01)

theorem coe_ksIncl (x : KS K S₀) : ((ksIncl h01 x : KS K S₁) : AlgebraicClosure K) = x :=
  IntermediateField.coe_inclusion _ x

/-- **`E(K_{S₀}) → E(K_{S₁})`**. Kind: definition. -/
def ptMap : PtS K S₀ W →+ PtS K S₁ W := Affine.Point.map (W' := W) (ksIncl h01)

theorem ptMap_injective : Function.Injective (ptMap h01 W) :=
  Affine.Point.map_injective (W' := W) (ksIncl h01)

/-- The restriction `G_{K,S₁} → G_{K,S₀}` is compatible with `K_{S₀} ⊆ K_{S₁}`. Kind: PROVED. -/
theorem ksIncl_infl (g : GKS K S₁) (x : KS K S₀) :
    ksIncl h01 (galS K S₀ (inflMap K h01 g) x) = galS K S₁ g (ksIncl h01 x) := by
  obtain ⟨σ, rfl⟩ := resAbs_surjective K S₁ g
  rw [show inflMap K h01 (resAbs K S₁ σ) = resAbs K S₀ σ from resUnr_comp K h01 σ]
  apply Subtype.ext
  simp only [galS, coe_ksIncl, resAbs_apply_coe]

/-- **`ptMap` is equivariant**: `ptMap(infl(g) P) = g ptMap(P)`. Kind: PROVED. -/
theorem ptMap_smul (g : GKS K S₁) (P : PtS K S₀ W) :
    ptMap h01 W (inflMap K h01 g • P) = g • ptMap h01 W P := by
  have hφ : (ksIncl h01).comp (galS K S₀ (inflMap K h01 g)).toAlgHom =
      (galS K S₁ g).toAlgHom.comp (ksIncl h01) :=
    AlgHom.ext fun x => ksIncl_infl h01 g x
  rw [ptS_smul_def, ptS_smul_def, ptMap, Affine.Point.map_map, Affine.Point.map_map, hφ]

/-- **The restrictions compose**: `G_{K,S} → G_{K,S₁} → G_{K,S₀}`. Kind: PROVED. -/
theorem inflMap_trans {S : Set (HeightOneSpectrum (𝓞 K))} (h1 : S₁ ⊆ S) (g : GKS K S) :
    inflMap K (h01.trans h1) g = inflMap K h01 (inflMap K h1 g) := by
  obtain ⟨σ, rfl⟩ := resAbs_surjective K S g
  rw [show inflMap K h1 (resAbs K S σ) = resAbs K S₁ σ from resUnr_comp K h1 σ]
  exact (resUnr_comp K (h01.trans h1) σ).trans (resUnr_comp K h01 σ).symm

/-- The embeddings `K_{S₀} ⊆ K_{S₁} → K̄_v` agree. Kind: PROVED. -/
theorem embS_ksIncl (v : HeightOneSpectrum (𝓞 K)) (x : KS K S₀) :
    embS K S₁ v (ksIncl h01 x) = embS K S₀ v x :=
  congrArg (decompEmb K v) (coe_ksIncl h01 x)

theorem ptMap_some {x y : KS K S₀} (hxy : (W.baseChange (KS K S₀)).toAffine.Nonsingular x y) :
    ∃ h', ptMap h01 W (Affine.Point.some x y hxy) =
      Affine.Point.some (ksIncl h01 x) (ksIncl h01 y) h' :=
  ⟨_, Affine.Point.map_some _ _⟩

/-- **`compPt` is compatible with `ptMap`**. Kind: PROVED. -/
theorem compPt_ptMap (v : HeightOneSpectrum (𝓞 K)) (P : PtS K S₀ W) :
    compPt (S := S₁) W v (ptMap h01 W P) = compPt (S := S₀) W v P := by
  rcases P with _ | ⟨x, y, hxy⟩
  · rw [← Affine.Point.zero_def, map_zero, map_zero, map_zero]
  · obtain ⟨h', e⟩ := ptMap_some h01 W hxy
    rw [e]
    simp only [compPt_some, embS_ksIncl]

end PtMap


/-! ### `ι = 1 ⊗ incl` into the ambient module over `S₁` -/

section Iota

variable {K : Type} [Field K] [NumberField K] {S S₀ S₁ : Set (HeightOneSpectrum (𝓞 K))}
  (hS : S₀ ⊆ S) (h01 : S₀ ⊆ S₁) (h1 : S₁ ⊆ S) (W : WeierstrassCurve K) [W.IsElliptic] (i : ℕ)
  [NeZero i] (s : KS K S₀) {h : K} (hs : s ^ 2 = algebraMap K (KS K S₀) h) (hs0 : s ≠ 0)
  [TopologicalSpace (Acoef i)] [DiscreteTopology (Acoef i)]
  {Δ : Type} [CommGroup Δ] [Finite Δ] (π : GKS K S₀ →* Δ)

/-- `E(K_{S₀})[2^i] → E(K_{S₁})`. Kind: definition. -/
def torsInclS : TorsT S₀ W i →ₗ[ℤ] PtS K S₁ W :=
  (ptMap h01 W).toIntLinearMap ∘ₗ torsIncl K S₀ W i

/-- `ι` on the uninflated modules. Kind: definition. -/
def iotaS₀ : shapMod₀ W i s hs hs0 π →ₗ[MonoidAlgebra ℤ Δ] ambU₀ S₁ W Δ :=
  LinearMap.baseChange (MonoidAlgebra ℤ Δ) (torsInclS h01 W i)

/-- `ι₀(infl(g) m) = α(infl g) · g ι₀(m)`. Kind: PROVED. -/
theorem iotaS₀_smul (g₁ : GKS K S₁) (m : shapMod₀ W i s hs hs0 π) :
    iotaS₀ h01 W i s hs hs0 π (inflMap K h01 g₁ • m) =
      ((alphaShap s hs hs0 π (inflMap K h01 g₁) : (MonoidAlgebra ℤ Δ)ˣ) : MonoidAlgebra ℤ Δ) •
        (g₁ • iotaS₀ h01 W i s hs hs0 π m) := by
  set g₀ := inflMap K h01 g₁
  refine TensorProduct.induction_on (R := ℤ) (M := MonoidAlgebra ℤ Δ) (N := TorsT S₀ W i)
    (motive := fun z => iotaS₀ h01 W i s hs hs0 π (g₀ • (show shapMod₀ W i s hs hs0 π from z)) =
      ((alphaShap s hs hs0 π g₀ : (MonoidAlgebra ℤ Δ)ˣ) : MonoidAlgebra ℤ Δ) •
        (g₁ • iotaS₀ h01 W i s hs hs0 π (show shapMod₀ W i s hs hs0 π from z))) m ?_ ?_ ?_
  · change iotaS₀ h01 W i s hs hs0 π (g₀ • (0 : shapMod₀ W i s hs hs0 π)) =
      _ • (g₁ • iotaS₀ h01 W i s hs hs0 π 0)
    rw [smul_zero, map_zero, smul_zero, smul_zero]
  · intro a t
    have h1' := CoefMod.smul_tmul (MonoidAlgebra ℤ Δ) (alphaShap s hs hs0 π) (TorsT S₀ W i) g₀ a t
    have h2 := CoefMod.smul_tmul (MonoidAlgebra ℤ Δ) (1 : GKS K S₁ →* (MonoidAlgebra ℤ Δ)ˣ)
      (PtS K S₁ W) g₁ a (ptMap h01 W (t : PtS K S₀ W))
    change iotaS₀ h01 W i s hs hs0 π (g₀ • CoefMod.equiv _ _ _ (a ⊗ₜ t)) =
      _ • (g₁ • iotaS₀ h01 W i s hs hs0 π (CoefMod.equiv _ _ _ (a ⊗ₜ t)))
    rw [h1']
    change (CoefMod.equiv _ _ _ (_ ⊗ₜ ptMap h01 W ((g₀ • t : TorsT S₀ W i) : PtS K S₀ W)) :
        ambU₀ S₁ W Δ) =
      _ • (g₁ • (CoefMod.equiv _ _ _ (a ⊗ₜ ptMap h01 W (t : PtS K S₀ W)) : ambU₀ S₁ W Δ))
    rw [h2]
    change (_ ⊗ₜ ptMap h01 W ((g₀ • t : TorsT S₀ W i) : PtS K S₀ W) :
        MonoidAlgebra ℤ Δ ⊗[ℤ] PtS K S₁ W) =
      ((alphaShap s hs hs0 π g₀ : (MonoidAlgebra ℤ Δ)ˣ) : MonoidAlgebra ℤ Δ) •
        (_ ⊗ₜ (g₁ • ptMap h01 W (t : PtS K S₀ W)) : MonoidAlgebra ℤ Δ ⊗[ℤ] PtS K S₁ W)
    rw [TensorProduct.smul_tmul', smul_eq_mul, ← ptMap_smul h01 W g₁]
    congr 1
    simp
  · intro x y hx hy
    change iotaS₀ h01 W i s hs hs0 π (g₀ • ((show shapMod₀ W i s hs hs0 π from x) +
        (show shapMod₀ W i s hs hs0 π from y))) =
      _ • (g₁ • iotaS₀ h01 W i s hs hs0 π ((show shapMod₀ W i s hs hs0 π from x) +
        (show shapMod₀ W i s hs hs0 π from y)))
    rw [smul_add, map_add, hx, hy, map_add, smul_add, smul_add]

/-- **`ι = 1 ⊗ incl : shapMod → ℤ[Δ] ⊗ E(K_{S₁})`**. Kind: definition. -/
def ambIotaS : shapMod hS W i s hs hs0 π →ₗ[MonoidAlgebra ℤ Δ] ambU h1 W Δ :=
  iotaS₀ h01 W i s hs hs0 π

variable (H : Subgroup (GKS K S)) [H.Normal] (hH : H ≤ (alphaInfl hS s hs hs0 π).ker)

/-- **`hιeq` for the ambient module over `S₁`** and any transfer subgroup
`H ≤ ker(χ_h [π] ∘ infl)`, with `θ = χ_h [π]` (PROVED). -/
theorem ambIotaS_equivariantH (g : GKS K S) (m : shapMod hS W i s hs hs0 π) :
    ambIotaS hS h01 h1 W i s hs hs0 π (g • m) =
      R H (ambRhoU h1 W Δ) (thetaH hS s hs hs0 π H hH) g (ambIotaS hS h01 h1 W i s hs hs0 π m) := by
  change iotaS₀ h01 W i s hs hs0 π (inflMap K hS g • (show shapMod₀ W i s hs hs0 π from m)) =
    ((alphaShap s hs hs0 π (inflMap K hS g) : (MonoidAlgebra ℤ Δ)ˣ) : MonoidAlgebra ℤ Δ) •
      (inflMap K h1 g • iotaS₀ h01 W i s hs hs0 π m)
  rw [show inflMap K hS g = inflMap K h01 (inflMap K h1 g) from inflMap_trans h01 h1 g]
  exact iotaS₀_smul h01 W i s hs hs0 π (inflMap K h1 g) m

/-- `ι` is injective (`ℤ[Δ]` flat). Kind: PROVED. -/
theorem ambIotaS_injective : Function.Injective (ambIotaS hS h01 h1 W i s hs hs0 π) := by
  have h := Module.Flat.lTensor_preserves_injective_linearMap (M := MonoidAlgebra ℤ Δ)
    (torsInclS h01 W i) ((ptMap_injective h01 W).comp Subtype.val_injective)
  intro x y hxy
  apply h
  have := hxy
  change LinearMap.baseChange _ _ x = LinearMap.baseChange _ _ y at this
  rwa [LinearMap.baseChange_eq_lTensor] at this

end Iota

/-! ### The coefficient/twist identification at `v ∈ P` -/

section Local

variable {K : Type} [Field K] [NumberField K] {S S₀ S₁ : Set (HeightOneSpectrum (𝓞 K))}
  (hS : S₀ ⊆ S) (h01 : S₀ ⊆ S₁) (h1 : S₁ ⊆ S) (W : WeierstrassCurve K) [W.IsElliptic] (i : ℕ)
  [NeZero i] (s : KS K S₀) {h : K} (hs : s ^ 2 = algebraMap K (KS K S₀) h) (hs0 : s ≠ 0)
  (hFull : FullTorsion K S₀ W (2 ^ i))
  [TopologicalSpace (Acoef i)] [DiscreteTopology (Acoef i)]
  {Δ : Type} [CommGroup Δ] [Finite Δ] (π : GKS K S₀ →* Δ)

/-- `1 ⊗ compPt` on `ℤ[Δ] ⊗ E(K_{S₁})` into the local module twisted by `χ_h ∘ p_v`.
Kind: definition. -/
def psiS₀ (v : HeightOneSpectrum (𝓞 K)) :
    ambU₀ S₁ W Δ →ₗ[MonoidAlgebra ℤ Δ] locL W s hs hs0 v Δ :=
  LinearMap.baseChange (MonoidAlgebra ℤ Δ) (compPt (S := S₁) W v).toIntLinearMap

/-- `ψ = 1 ⊗ compPt` on the ambient module over `S₁`. Kind: definition. -/
def locPsiS (v : HeightOneSpectrum (𝓞 K)) :
    ambU h1 W Δ →ₗ[MonoidAlgebra ℤ Δ] locL W s hs hs0 v Δ :=
  psiS₀ (S₁ := S₁) W s hs hs0 v

/-- `χ_h(p_v σ) ψ(p_v(σ) x) = σ ψ(x)` on the uninflated module. Kind: PROVED. -/
theorem psiS₀_smul (v : HeightOneSpectrum (𝓞 K)) (σ : Gloc K v) (x : ambU₀ S₁ W Δ) :
    ((chiZ s hs hs0 (Δ := Δ) (locMap K S₀ v σ) : (MonoidAlgebra ℤ Δ)ˣ) : MonoidAlgebra ℤ Δ) •
      psiS₀ W s hs hs0 v (locMap K S₁ v σ • x) = σ • psiS₀ W s hs hs0 v x := by
  refine TensorProduct.induction_on (R := ℤ) (M := MonoidAlgebra ℤ Δ) (N := PtS K S₁ W)
    (motive := fun z => ((chiZ s hs hs0 (Δ := Δ) (locMap K S₀ v σ) : (MonoidAlgebra ℤ Δ)ˣ) :
        MonoidAlgebra ℤ Δ) • psiS₀ W s hs hs0 v
          (locMap K S₁ v σ • (show ambU₀ S₁ W Δ from z)) =
      σ • psiS₀ W s hs hs0 v (show ambU₀ S₁ W Δ from z)) x ?_ ?_ ?_
  · change _ • psiS₀ W s hs hs0 v (locMap K S₁ v σ • (0 : ambU₀ S₁ W Δ)) =
      σ • psiS₀ W s hs hs0 v (0 : ambU₀ S₁ W Δ)
    simp only [smul_zero, map_zero]
  · intro a P
    have h1' := CoefMod.smul_tmul (MonoidAlgebra ℤ Δ) (1 : GKS K S₁ →* (MonoidAlgebra ℤ Δ)ˣ)
      (PtS K S₁ W) (locMap K S₁ v σ) a P
    have h2 := CoefMod.smul_tmul (MonoidAlgebra ℤ Δ)
      ((chiZ s hs hs0 (Δ := Δ)).comp (locMap K S₀ v : Gloc K v →* GKS K S₀)) (PtV W v) σ a
      (compPt (S := S₁) W v P)
    change _ • psiS₀ W s hs hs0 v (locMap K S₁ v σ • CoefMod.equiv _ _ _ (a ⊗ₜ P)) =
      σ • psiS₀ W s hs hs0 v (CoefMod.equiv _ _ _ (a ⊗ₜ P))
    rw [h1']
    change _ • (CoefMod.equiv _ _ _ (_ ⊗ₜ compPt (S := S₁) W v (locMap K S₁ v σ • P)) :
        locL W s hs hs0 v Δ) = σ • CoefMod.equiv _ _ _ (a ⊗ₜ compPt (S := S₁) W v P)
    rw [h2, ptS_smul_def, compPt_smul]
    change (_ ⊗ₜ _ : MonoidAlgebra ℤ Δ ⊗[ℤ] PtV W v) = (_ ⊗ₜ _ : MonoidAlgebra ℤ Δ ⊗[ℤ] PtV W v)
    simp
  · intro x y hx hy
    change _ • psiS₀ W s hs hs0 v (locMap K S₁ v σ • ((show ambU₀ S₁ W Δ from x) +
        (show ambU₀ S₁ W Δ from y))) =
      σ • psiS₀ W s hs hs0 v ((show ambU₀ S₁ W Δ from x) + (show ambU₀ S₁ W Δ from y))
    rw [smul_add, map_add, smul_add, hx, hy, map_add, smul_add]

/-- `χ_h(p_v σ) ψ(p_v(σ) x) = σ ψ(x)`. Kind: PROVED. -/
theorem psiS_smul (v : HeightOneSpectrum (𝓞 K)) (σ : Gloc K v) (x : ambU h1 W Δ) :
    ((chiZ s hs hs0 (Δ := Δ) (locMap K S₀ v σ) : (MonoidAlgebra ℤ Δ)ˣ) : MonoidAlgebra ℤ Δ) •
      locPsiS h1 W s hs hs0 v (locMap K S v σ • x) = σ • locPsiS h1 W s hs hs0 v x := by
  change _ • psiS₀ W s hs hs0 v
      (inflMap K h1 (locMap K S v σ) • (show ambU₀ S₁ W Δ from x)) =
    σ • psiS₀ W s hs hs0 v (show ambU₀ S₁ W Δ from x)
  rw [locMap_compat K h1 v σ]
  exact psiS₀_smul W s hs hs0 v σ x

/-- **`ψ ∘ ι` is the twisted instance's `ψ ∘ ι`** (`compPt_ptMap`). Kind: PROVED. -/
theorem locPsiS_iota (v : HeightOneSpectrum (𝓞 K)) (x : shapMod hS W i s hs hs0 π) :
    locPsiS h1 W s hs hs0 v (ambIotaS hS h01 h1 W i s hs hs0 π x) =
      locPsi hS W s hs hs0 v (ambIota hS W i s hs hs0 π x) := by
  change (LinearMap.baseChange (MonoidAlgebra ℤ Δ) (compPt (S := S₁) W v).toIntLinearMap)
      ((LinearMap.baseChange (MonoidAlgebra ℤ Δ) (torsInclS h01 W i))
        (show MonoidAlgebra ℤ Δ ⊗[ℤ] TorsT S₀ W i from x)) =
    (LinearMap.baseChange (MonoidAlgebra ℤ Δ) (compPt (S := S₀) W v).toIntLinearMap)
      ((LinearMap.baseChange (MonoidAlgebra ℤ Δ) (torsIncl K S₀ W i))
        (show MonoidAlgebra ℤ Δ ⊗[ℤ] TorsT S₀ W i from x))
  rw [← LinearMap.comp_apply, ← LinearMap.baseChange_comp, ← LinearMap.comp_apply,
    ← LinearMap.baseChange_comp]
  congr 2
  refine LinearMap.ext fun t => ?_
  exact compPt_ptMap h01 W v (t : PtS K S₀ W)

open scoped Classical in
/-- **`LocalTwistIdentification` for the ambient module over `S₁`** (PROVED; tex 3251–3270,
3413–3438). -/
theorem localTwistIdentificationS (v : Places K S) (H : Subgroup (GKS K S)) [H.Normal]
    (θ : GKS K S ⧸ H →* (MonoidAlgebra ℤ Δ)ˣ)
    (hθ : ∀ σ : Gloc K v.1, θ ((locMap K S v.1 σ : GKS K S) : GKS K S ⧸ H) =
      chiZ s hs hs0 (Δ := Δ) (locMap K S₀ v.1 σ))
    [(localTwist W h v.1).IsElliptic] :
    LocalTwistIdentification (ambRhoU h1 W Δ) H θ (ambIotaS hS h01 h1 W i s hs hs0 π)
      (localTwist W h v.1) (2 ^ i) (locMap K S v.1 : Gloc K v.1 →* GKS K S)
      ((ofResModAdd (locMap K S v.1) (shapMod hS W i s hs hs0 π)).comp
        (shapIota hS W i s hs hs0 hFull π v))
      (locPsiS h1 W s hs hs0 v.1) (locJB W s hs hs0 v.1 (Δ := Δ)) := by
  obtain ⟨h1', h2, -, h4, h5⟩ := localTwistIdentification_actual hS W i s hs hs0 hFull π v ⊥
    (1 : GKS K S ⧸ (⊥ : Subgroup (GKS K S)) →* (MonoidAlgebra ℤ Δ)ˣ) (fun _ => rfl)
  have hc : ∀ x, locPsiS h1 W s hs hs0 v.1 (ambIotaS hS h01 h1 W i s hs hs0 π x) =
      locPsi hS W s hs hs0 v.1 (ambIota hS W i s hs hs0 π x) :=
    locPsiS_iota hS h01 h1 W i s hs hs0 π v.1
  refine ⟨fun x y hxy => h1' (by simpa only [hc] using hxy), fun x hx => ?_, fun σ x => ?_, h4,
    fun t => (hc _).trans (h5 t)⟩
  · obtain ⟨m₀, hm₀⟩ := h2 x hx
    exact ⟨m₀, (hc m₀).trans hm₀⟩
  · change locPsiS h1 W s hs hs0 v.1 ((((θ ((locMap K S v.1 σ : GKS K S) : GKS K S ⧸ H) :
      (MonoidAlgebra ℤ Δ)ˣ) : MonoidAlgebra ℤ Δ) • ambRhoU h1 W Δ (locMap K S v.1 σ)) x) = _
    rw [hθ σ, LinearMap.smul_apply, LinearMap.map_smul]
    exact psiS_smul h1 W s hs hs0 v.1 σ x

open scoped Classical in
/-- **`OldPlaceInput` for the ambient module over `S₁` from the realization** (PROVED). -/
theorem oldPlaceInputS (v : Places K S) (H : Subgroup (GKS K S)) [H.Normal]
    [Fintype (GKS K S ⧸ H)] (r : GKS K S ⧸ H → GKS K S)
    (θ : GKS K S ⧸ H →* (MonoidAlgebra ℤ Δ)ˣ)
    (hθ : ∀ σ : Gloc K v.1, θ ((locMap K S v.1 σ : GKS K S) : GKS K S ⧸ H) =
      chiZ s hs hs0 (Δ := Δ) (locMap K S₀ v.1 σ))
    [(localTwist W h v.1).IsElliptic] (y : ambU h1 W Δ)
    {J : Type} (sJ : Finset J) (a : J → MonoidAlgebra ℤ Δ)
    (P : J → (localTwist W h v.1).toAffine.Point)
    (hreal : locPsiS h1 W s hs hs0 v.1 (wsum (ambRhoU h1 W Δ) H r θ y) =
      ∑ j ∈ sJ, a j • locJB W s hs hs0 v.1 (Δ := Δ)
        (basePt (v.1.adicCompletion K) (localTwist W h v.1) (P j))) :
    OldPlaceInput (ambRhoU h1 W Δ) H r θ v.1 (localTwist W h v.1) (2 ^ i)
      (shapIota hS W i s hs hs0 hFull π v) (ambIotaS hS h01 h1 W i s hs hs0 π) y :=
  ⟨locL W s hs hs0 v.1 Δ, inferInstance, inferInstance, inferInstance, inferInstance,
    locPsiS h1 W s hs hs0 v.1, locJB W s hs hs0 v.1 (Δ := Δ),
    localTwistIdentificationS hS h01 h1 W i s hs hs0 hFull π v H θ hθ, J, sJ, a, P, hreal⟩

end Local

/-! ### The realization for a point over `S₁` -/

section Real

open scoped Classical

variable {K : Type} [Field K] [NumberField K] {S S₀ S₁ : Set (HeightOneSpectrum (𝓞 K))}
  (hS : S₀ ⊆ S) (h1 : S₁ ⊆ S) (W : WeierstrassCurve K) [W.IsElliptic] (s : KS K S₀) {h : K}
  (hs : s ^ 2 = algebraMap K (KS K S₀) h) (hs0 : s ≠ 0)
  {Δ : Type} [CommGroup Δ] [Fintype Δ] (π : GKS K S₀ →* Δ)
  (H : Subgroup (GKS K S)) [H.Normal] (hH : H ≤ (alphaInfl hS s hs hs0 π).ker)
  [Fintype (GKS K S ⧸ H)] (r : GKS K S ⧸ H → GKS K S)
  (hr : ∀ δ, ((r δ : GKS K S) : GKS K S ⧸ H) = δ)
  (P : PtS K S₁ W) (v : HeightOneSpectrum (𝓞 K))

/-- The summand `χ_h(r_δ) · j(r_δ P) ∈ E(K̄_v)` for `P ∈ E(K_{S₁})`. Kind: definition. -/
def realFS (δ : GKS K S ⧸ H) : PtV W v :=
  ((quadChar s hs hs0 (gR hS H r δ) : ℤˣ) : ℤ) •
    compPt (S := S₁) W v (inflMap K h1 (r δ) • P)

/-- **`X_d = ∑_{δ : π(r_δ) = d} χ_h(r_δ) · j(r_δ P)`**. Kind: definition. -/
def realXS (d : Δ) : PtV W v :=
  ∑ δ with π (gR hS H r δ) = d, realFS hS h1 W s hs hs0 H r P v δ

include hH hr in
/-- **The local Mackey step on one summand** for `P ∈ E(K_{S₁})` fixed by `H` (PROVED). -/
theorem smul_realFS (hP : ∀ x ∈ H, inflMap K h1 x • P = P) (σ : Gloc K v)
    (hv : π (locMap K S₀ v σ) = 1) (δ : GKS K S ⧸ H) :
    σ • realFS hS h1 W s hs hs0 H r P v δ =
        ((quadChar s hs hs0 (locMap K S₀ v σ) : ℤˣ) : ℤ) •
          realFS hS h1 W s hs hs0 H r P v ((locMap K S v σ : GKS K S ⧸ H) * δ) ∧
      π (gR hS H r ((locMap K S v σ : GKS K S ⧸ H) * δ)) = π (gR hS H r δ) := by
  obtain ⟨x, hx, hxe⟩ := coset_rel H r hr (locMap K S v σ) δ
  obtain ⟨hχx, hπx⟩ := chi_pi_of_mem hS s hs hs0 π H hH hx
  have hinfl : locMap K S₀ v σ * gR hS H r δ =
      gR hS H r ((locMap K S v σ : GKS K S ⧸ H) * δ) * inflMap K hS x := by
    rw [← locMap_compat K hS v σ]
    simp only [gR, ← map_mul, hxe]
  have hinfl1 : locMap K S₁ v σ * inflMap K h1 (r δ) =
      inflMap K h1 (r ((locMap K S v σ : GKS K S ⧸ H) * δ)) * inflMap K h1 x := by
    rw [← locMap_compat K h1 v σ]
    simp only [← map_mul, hxe]
  set δ' := (locMap K S v σ : GKS K S ⧸ H) * δ
  have hpt : locMap K S₁ v σ • (inflMap K h1 (r δ) • P) = inflMap K h1 (r δ') • P := by
    rw [← mul_smul, hinfl1, mul_smul, hP x hx]
  have hchi : quadChar s hs hs0 (gR hS H r δ) =
      quadChar s hs hs0 (locMap K S₀ v σ) * quadChar s hs hs0 (gR hS H r δ') := by
    have := congrArg (quadChar s hs hs0) hinfl
    rw [map_mul, map_mul, hχx, mul_one] at this
    rw [← this, ← mul_assoc, Int.units_mul_self, one_mul]
  refine ⟨?_, ?_⟩
  · rw [realFS, smul_comm, ← compPt_smul, ← ptS_smul_def, hpt, hchi, Units.val_mul, mul_smul]
    rfl
  · have := congrArg π hinfl
    rw [map_mul, map_mul, hv, one_mul, hπx, mul_one] at this
    exact this.symm

include hH hr in
/-- **`σ X_d = χ_h(σ) X_d`** (PROVED; tex 3251–3262). -/
theorem smul_realXS (hP : ∀ x ∈ H, inflMap K h1 x • P = P) (σ : Gloc K v)
    (hv : π (locMap K S₀ v σ) = 1) (d : Δ) :
    σ • realXS hS h1 W s hs hs0 π H r P v d =
      ((quadChar s hs hs0 (locMap K S₀ v σ) : ℤˣ) : ℤ) • realXS hS h1 W s hs hs0 π H r P v d := by
  have key := smul_realFS hS h1 W s hs hs0 π H hH r hr P v hP σ hv
  rw [realXS, Finset.sum_filter, Finset.smul_sum, Finset.smul_sum]
  simp_rw [smul_ite, smul_zero]
  have hstep : ∀ δ : GKS K S ⧸ H,
      (if π (gR hS H r δ) = d then σ • realFS hS h1 W s hs hs0 H r P v δ else 0) =
        (fun δ' => if π (gR hS H r δ') = d then
          ((quadChar s hs hs0 (locMap K S₀ v σ) : ℤˣ) : ℤ) • realFS hS h1 W s hs hs0 H r P v δ'
          else 0) ((Equiv.mulLeft ((locMap K S v σ : GKS K S) : GKS K S ⧸ H)) δ) := by
    intro δ
    simp only [Equiv.coe_mulLeft]
    rw [(key δ).1]
    simp only [(key δ).2]
  rw [Finset.sum_congr rfl fun δ _ => hstep δ]
  exact Equiv.sum_comp (Equiv.mulLeft ((locMap K S v σ : GKS K S) : GKS K S ⧸ H))
    (fun δ' => if π (gR hS H r δ') = d then
      ((quadChar s hs hs0 (locMap K S₀ v σ) : ℤˣ) : ℤ) • realFS hS h1 W s hs hs0 H r P v δ'
      else 0)

include hH hr in
/-- **`X_d` is the image of a point of the local twist over `K_v`** (PROVED; tex 3251–3262). -/
theorem exists_twist_pointS (hP : ∀ x ∈ H, inflMap K h1 x • P = P)
    (hloc : ∀ σ : Gloc K v, π (locMap K S₀ v σ) = 1) (d : Δ) :
    ∃ Q : (localTwist W h v).toAffine.Point,
      twistPt (W.baseChange (v.adicCompletion K)) (algebraMap K (v.adicCompletion K) h)
          two_ne_zero (localSqrt_ne_zero s hs0 v) (localSqrt_sq s hs v)
          (basePt (v.adicCompletion K) (localTwist W h v) Q) =
        realXS hS h1 W s hs hs0 π H r P v d := by
  set tw := twistPt (W.baseChange (v.adicCompletion K)) (algebraMap K (v.adicCompletion K) h)
    two_ne_zero (localSqrt_ne_zero s hs0 v) (localSqrt_sq s hs v)
  have hfix : ∀ σ : Field.absoluteGaloisGroup (v.adicCompletion K),
      σ • tw.symm (realXS hS h1 W s hs hs0 π H r P v d) =
        tw.symm (realXS hS h1 W s hs hs0 π H r P v d) := by
    intro σ
    apply tw.injective
    rw [twistPt_smul, tw.apply_symm_apply,
      smul_realXS hS h1 W s hs hs0 π H hH r hr P v hP σ (hloc σ) d,
      twistSign_localSqrt (S := S₀) s hs hs0 v σ, smul_smul, ← Units.val_mul, Int.units_mul_self,
      Units.val_one, one_smul]
  obtain ⟨Q, hQ⟩ := ZInQ.Manuscript.RC.CoefModules.exists_basePt_of_fixed hfix
  exact ⟨Q, by rw [hQ, tw.apply_symm_apply]⟩

include hr in
/-- **The localized weighted sum, grouped by the fibres of `δ ↦ π(r_δ)`** (PROVED). -/
theorem psi_wsumS :
    locPsiS h1 W s hs hs0 v (wsum (ambRhoU h1 W Δ) H r (thetaH hS s hs hs0 π H hH)
      ((1 : MonoidAlgebra ℤ Δ) ⊗ₜ P : MonoidAlgebra ℤ Δ ⊗[ℤ] PtS K S₁ W)) =
      ∑ d : Δ, tL W s hs hs0 v (MonoidAlgebra.of ℤ Δ d) (realXS hS h1 W s hs hs0 π H r P v d) := by
  have hterm : ∀ δ : GKS K S ⧸ H,
      locPsiS h1 W s hs hs0 v (R H (ambRhoU h1 W Δ) (thetaH hS s hs hs0 π H hH) (r δ)
        ((1 : MonoidAlgebra ℤ Δ) ⊗ₜ P : MonoidAlgebra ℤ Δ ⊗[ℤ] PtS K S₁ W)) =
      tL W s hs hs0 v (MonoidAlgebra.of ℤ Δ (π (gR hS H r δ)))
        (realFS hS h1 W s hs hs0 H r P v δ) := by
    intro δ
    change locPsiS h1 W s hs hs0 v
      (((thetaH hS s hs hs0 π H hH ((r δ : GKS K S) : GKS K S ⧸ H) : (MonoidAlgebra ℤ Δ)ˣ) :
        MonoidAlgebra ℤ Δ) • ambRhoU h1 W Δ (r δ)
          ((1 : MonoidAlgebra ℤ Δ) ⊗ₜ P : MonoidAlgebra ℤ Δ ⊗[ℤ] PtS K S₁ W)) = _
    rw [LinearMap.map_smul, ambRhoU_oneTmul' h1 W P, thetaH_mk, alphaShap_val]
    change ((((quadChar s hs hs0 (gR hS H r δ) : ℤˣ) : ℤ) : MonoidAlgebra ℤ Δ) *
        MonoidAlgebra.of ℤ Δ (π (gR hS H r δ))) •
      ((1 : MonoidAlgebra ℤ Δ) ⊗ₜ compPt (S := S₁) W v (inflMap K h1 (r δ) • P) :
        MonoidAlgebra ℤ Δ ⊗[ℤ] PtV W v) = _
    rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one, realFS]
    change _ = (MonoidAlgebra.of ℤ Δ (π (gR hS H r δ)) ⊗ₜ
      (((quadChar s hs hs0 (gR hS H r δ) : ℤˣ) : ℤ) •
        compPt (S := S₁) W v (inflMap K h1 (r δ) • P)) : MonoidAlgebra ℤ Δ ⊗[ℤ] PtV W v)
    rw [TensorProduct.tmul_smul, TensorProduct.smul_tmul', zsmul_eq_mul]
  change locPsiS h1 W s hs hs0 v (∑ δ : GKS K S ⧸ H, R H (ambRhoU h1 W Δ)
    (thetaH hS s hs hs0 π H hH) (r δ)
      ((1 : MonoidAlgebra ℤ Δ) ⊗ₜ P : MonoidAlgebra ℤ Δ ⊗[ℤ] PtS K S₁ W)) = _
  rw [map_sum, Finset.sum_congr rfl fun δ _ => hterm δ]
  rw [← Finset.sum_fiberwise Finset.univ (fun δ => π (gR hS H r δ))]
  refine Finset.sum_congr rfl fun d _ => ?_
  rw [realXS, tL_sum]
  refine Finset.sum_congr rfl fun δ hδ => ?_
  rw [(Finset.mem_filter.1 hδ).2]

end Real

section Hreal

open scoped Classical

variable {K : Type} [Field K] [NumberField K] {S S₀ S₁ : Set (HeightOneSpectrum (𝓞 K))}
  (hS : S₀ ⊆ S) (h01 : S₀ ⊆ S₁) (h1 : S₁ ⊆ S) (W : WeierstrassCurve K) [W.IsElliptic] (i : ℕ)
  [NeZero i] (s : KS K S₀) {h : K} (hs : s ^ 2 = algebraMap K (KS K S₀) h) (hs0 : s ≠ 0)
  (hFull : FullTorsion K S₀ W (2 ^ i))
  [TopologicalSpace (Acoef i)] [DiscreteTopology (Acoef i)]
  {Δ : Type} [CommGroup Δ] [Fintype Δ] (π : GKS K S₀ →* Δ)
  (H : Subgroup (GKS K S)) [H.Normal] (hH : H ≤ (alphaInfl hS s hs hs0 π).ker)
  [Fintype (GKS K S ⧸ H)] (r : GKS K S ⧸ H → GKS K S)
  (hr : ∀ δ, ((r δ : GKS K S) : GKS K S ⧸ H) = δ)
  (P : PtS K S₁ W)

include hH hr in
/-- **The realization `hreal` for a point over `S₁`** (PROVED; tex 3251–3262): for
`P ∈ E(K_{S₁})` fixed by the transfer subgroup and a place `v` at which `π` is trivial on the
decomposition group, `ψ(∑_δ θ_H(r_δ) ρ₀(r_δ)(1 ⊗ P)) = ∑_d [d] · j_B(Q_d)`, `Q_d ∈ B(K_v)`. -/
theorem hreal_actualS (hP : ∀ x ∈ H, inflMap K h1 x • P = P) (v : HeightOneSpectrum (𝓞 K))
    (hloc : ∀ σ : Gloc K v, π (locMap K S₀ v σ) = 1) :
    ∃ Q : Δ → (localTwist W h v).toAffine.Point,
      locPsiS h1 W s hs hs0 v (wsum (ambRhoU h1 W Δ) H r (thetaH hS s hs hs0 π H hH)
        ((1 : MonoidAlgebra ℤ Δ) ⊗ₜ P : MonoidAlgebra ℤ Δ ⊗[ℤ] PtS K S₁ W)) =
        ∑ d ∈ Finset.univ, MonoidAlgebra.of ℤ Δ d • locJB W s hs hs0 v (Δ := Δ)
          (basePt (v.adicCompletion K) (localTwist W h v) (Q d)) := by
  choose Q hQ using exists_twist_pointS hS h1 W s hs hs0 π H hH r hr P v hP hloc
  refine ⟨Q, ?_⟩
  rw [psi_wsumS hS h1 W s hs hs0 π H hH r hr P v]
  refine Finset.sum_congr rfl fun d _ => ?_
  change _ = MonoidAlgebra.of ℤ Δ d • ((1 : MonoidAlgebra ℤ Δ) ⊗ₜ
    twistPt (W.baseChange (v.adicCompletion K)) (algebraMap K (v.adicCompletion K) h)
      two_ne_zero (localSqrt_ne_zero s hs0 v) (localSqrt_sq s hs v)
      (basePt (v.adicCompletion K) (localTwist W h v) (Q d)) : MonoidAlgebra ℤ Δ ⊗[ℤ] PtV W v)
  rw [hQ d, TensorProduct.smul_tmul', smul_eq_mul, mul_one]

include hH hr in
/-- **The old-place input for a point over `S₁` fixed by the transfer subgroup** (PROVED;
tex 3251–3270), with no input beyond the ELLIOT `PsiTrivialAt2N`. -/
theorem oldPlaceInput_of_pointS {Pl : Set (HeightOneSpectrum (𝓞 K))} (ψ : Δ →* (Acoef i)ˣ)
    (hψ : Function.Injective ψ) (hΨ : PsiTrivialAt2N i π ψ Pl)
    (hP : ∀ x ∈ H, inflMap K h1 x • P = P) (v : Places K S) (hv : v.1 ∈ Pl)
    [(localTwist W h v.1).IsElliptic] :
    OldPlaceInput (ambRhoU h1 W Δ) H r (thetaH hS s hs hs0 π H hH) v.1 (localTwist W h v.1)
      (2 ^ i) (shapIota hS W i s hs hs0 hFull π v) (ambIotaS hS h01 h1 W i s hs hs0 π)
      ((1 : MonoidAlgebra ℤ Δ) ⊗ₜ P : MonoidAlgebra ℤ Δ ⊗[ℤ] PtS K S₁ W) := by
  obtain ⟨Q, hQ⟩ := hreal_actualS hS h1 W s hs hs0 π H hH r hr P hP v.1
    (fun σ => pi_trivial_of_psi i π ψ hψ hΨ hv σ)
  exact oldPlaceInputS hS h01 h1 W i s hs hs0 hFull π v H r (thetaH hS s hs hs0 π H hH)
    (fun σ => thetaH_local hS i s hs hs0 π H hH ψ hψ hΨ hv σ) _ Finset.univ
    (fun d => MonoidAlgebra.of ℤ Δ d) Q hQ

end Hreal

/-! ### Inertia, `hPw` and the unramified lifts -/

section Inertia

variable {K : Type} [Field K] [NumberField K] {S S₁ S'' : Set (HeightOneSpectrum (𝓞 K))}
  (h1 : S₁ ⊆ S) (h'' : S'' ⊆ S₁) (W : WeierstrassCurve K) (Δ : Type) [CommGroup Δ]

/-- `1 ⊗ ptMap : ℤ[Δ] ⊗ E(K_{S''}) → ℤ[Δ] ⊗ E(K_{S₁})`. Kind: definition. -/
def ptMapT : ambU₀ S'' W Δ →ₗ[MonoidAlgebra ℤ Δ] ambU₀ S₁ W Δ :=
  LinearMap.baseChange (MonoidAlgebra ℤ Δ) (ptMap h'' W).toIntLinearMap

/-- `g · (1 ⊗ ptMap)(q) = (1 ⊗ ptMap)(infl(g) q)`. Kind: PROVED. -/
theorem ptMapT_smul (g₁ : GKS K S₁) (q : ambU₀ S'' W Δ) :
    g₁ • ptMapT h'' W Δ q = ptMapT h'' W Δ (inflMap K h'' g₁ • q) := by
  refine TensorProduct.induction_on (R := ℤ) (M := MonoidAlgebra ℤ Δ) (N := PtS K S'' W)
    (motive := fun z => g₁ • ptMapT h'' W Δ (show ambU₀ S'' W Δ from z) =
      ptMapT h'' W Δ (inflMap K h'' g₁ • (show ambU₀ S'' W Δ from z))) q ?_ ?_ ?_
  · change g₁ • ptMapT h'' W Δ (0 : ambU₀ S'' W Δ) =
      ptMapT h'' W Δ (inflMap K h'' g₁ • (0 : ambU₀ S'' W Δ))
    rw [map_zero, smul_zero, smul_zero, map_zero]
  · intro a P
    have h1' := CoefMod.smul_tmul (MonoidAlgebra ℤ Δ) (1 : GKS K S₁ →* (MonoidAlgebra ℤ Δ)ˣ)
      (PtS K S₁ W) g₁ a (ptMap h'' W P)
    have h2 := CoefMod.smul_tmul (MonoidAlgebra ℤ Δ) (1 : GKS K S'' →* (MonoidAlgebra ℤ Δ)ˣ)
      (PtS K S'' W) (inflMap K h'' g₁) a P
    change g₁ • (CoefMod.equiv _ _ _ (a ⊗ₜ ptMap h'' W P) : ambU₀ S₁ W Δ) =
      ptMapT h'' W Δ (inflMap K h'' g₁ • CoefMod.equiv _ _ _ (a ⊗ₜ P))
    rw [h1', h2]
    change (_ ⊗ₜ (g₁ • ptMap h'' W P) : MonoidAlgebra ℤ Δ ⊗[ℤ] PtS K S₁ W) =
      (_ ⊗ₜ ptMap h'' W (inflMap K h'' g₁ • P) : MonoidAlgebra ℤ Δ ⊗[ℤ] PtS K S₁ W)
    rw [ptMap_smul h'' W g₁ P]
    simp
  · intro x y hx hy
    change g₁ • ptMapT h'' W Δ ((show ambU₀ S'' W Δ from x) + (show ambU₀ S'' W Δ from y)) =
      ptMapT h'' W Δ (inflMap K h'' g₁ • ((show ambU₀ S'' W Δ from x) +
        (show ambU₀ S'' W Δ from y)))
    rw [map_add, smul_add, hx, hy, smul_add, map_add]

/-- **A point coming from `E(K_{S''})` with `w ∉ S''` is fixed by the inertia at `w`** (PROVED;
for the text: the division points of the Heegner point over `H_{dq}` generate an extension
unramified at the places above the unused primes, `DivisionPointsF.exists_supportPoint_of_field`).
-/
theorem inertiaFixes_of_support (w : Places K S) (hw : w.1 ∉ S'') (q : ambU₀ S'' W Δ) :
    InertiaFixesDivisionPoint (ambRhoU h1 W Δ) (inertiaImage w)
      (show ambU h1 W Δ from ptMapT h'' W Δ q) :=
  inertiaFixes_of_inflated (h''.trans h1) w hw _ fun g hg => by
    change (inflMap K h1 g • ptMapT h'' W Δ q : ambU₀ S₁ W Δ) = ptMapT h'' W Δ q
    rw [ptMapT_smul, ← inflMap_trans h'' h1 g, hg, one_smul]

end Inertia

section Unramified

variable {K : Type} [Field K] [NumberField K] {S S₀ S₁ : Set (HeightOneSpectrum (𝓞 K))}
  (hS : S₀ ⊆ S) (h01 : S₀ ⊆ S₁) (h1 : S₁ ⊆ S) (W : WeierstrassCurve K) [W.IsElliptic] (i : ℕ)
  [NeZero i] (s : KS K S₀) {h : K} (hs : s ^ 2 = algebraMap K (KS K S₀) h) (hs0 : s ≠ 0)
  [TopologicalSpace (Acoef i)] [DiscreteTopology (Acoef i)]
  {Δ : Type} [CommGroup Δ] [Finite Δ] (π : GKS K S₀ →* Δ)
  (H : Subgroup (GKS K S)) [H.Normal] (hH : H ≤ (alphaInfl hS s hs hs0 π).ker)
  (w : Places K S) (hw : w.1 ∉ S₀)

include hw in
/-- **`hPw` for the ambient module over `S₁`** (PROVED; tex 3471–3487): for any transfer subgroup
`H ≤ ker(χ_h [π] ∘ infl)` containing the inertia image at `w` (`hunr`; for the text `H = G_{H_R}`,
`G_{H_P}`, the ring class fields being unramified at `w`) and a division point `Q` fixed by the
conjugates of that inertia (`hQin`; `inertiaFixes_of_support`). No `hker`. -/
theorem hPw_actualS [IsOpenKer (alphaShap s hs hs0 π)] [Fintype (GKS K S ⧸ H)]
    (r : GKS K S ⧸ H → GKS K S) (hr : ∀ δ, ((r δ : GKS K S) : GKS K S ⧸ H) = δ)
    [ContinuousSMul (GUr K w.1)
      (urRep (MonoidAlgebra ℤ Δ) (shapMod₀ W i s hs hs0 π) (newPlace w hw)).V]
    (kk : ℤ) {Q y : ambU h1 W Δ} (hQ : kk • Q = y)
    (a : (globalCx (MonoidAlgebra ℤ Δ) (GKS K S) (shapMod hS W i s hs hs0 π)).X 1)
    (hz : ∀ g : Fin 1 → GKS K S,
      ambIotaS hS h01 h1 W i s hs hs0 π
          (gval (A := MonoidAlgebra ℤ Δ) (M := shapMod hS W i s hs hs0 π) a g) =
        T H r hr (ambRhoU h1 W Δ) (thetaH hS s hs hs0 π H hH) 1
          (kummerCochain (ambRhoU h1 W Δ) H Q) g)
    (hunr : inertiaImage w ⊆ (H : Set (GKS K S)))
    (hQin : InertiaFixesDivisionPoint (ambRhoU h1 W Δ) (inertiaImage w) Q) :
    ∃ y : (genuineUq K S (MonoidAlgebra ℤ Δ) w
        (urRep (MonoidAlgebra ℤ Δ) (shapMod₀ W i s hs hs0 π) (newPlace w hw))).X 1,
      (genuineιq K S (MonoidAlgebra ℤ Δ) (shapMod hS W i s hs hs0 π) w
        (urRep (MonoidAlgebra ℤ Δ) (shapMod₀ W i s hs hs0 π) (newPlace w hw))
        (urId hS (MonoidAlgebra ℤ Δ) (shapMod₀ W i s hs hs0 π) (newPlace w hw))
        (urId_compat hS (MonoidAlgebra ℤ Δ) (shapMod₀ W i s hs hs0 π) w hw)).f 1 1 rfl y =
      (stageRes K S (MonoidAlgebra ℤ Δ) (shapMod hS W i s hs hs0 π) w).f 1 1 rfl a :=
  hPw_of_transfer hS (MonoidAlgebra ℤ Δ) (shapMod₀ W i s hs hs0 π) (ambRhoU h1 W Δ)
    H r hr (thetaH hS s hs hs0 π H hH) (ambIotaS hS h01 h1 W i s hs hs0 π)
    (ambIotaS_injective hS h01 h1 W i s hs hs0 π)
    (ambIotaS_equivariantH hS h01 h1 W i s hs hs0 π H hH) w hw kk hQ a hz hunr hQin

end Unramified

section UnramifiedLifts

variable {K : Type} [Field K] [NumberField K] {S S₀ S₁ : Set (HeightOneSpectrum (𝓞 K))}
  (hS : S₀ ⊆ S) (h01 : S₀ ⊆ S₁) (h1 : S₁ ⊆ S) (W : WeierstrassCurve K) [W.IsElliptic] (i : ℕ)
  [NeZero i] (s : KS K S₀) {h : K} (hs : s ^ 2 = algebraMap K (KS K S₀) h) (hs0 : s ≠ 0)
  [TopologicalSpace (Acoef i)] [DiscreteTopology (Acoef i)]
  {Δ : Type} [CommGroup Δ] [Finite Δ] (π : GKS K S₀ →* Δ) [IsOpenKer (alphaShap s hs hs0 π)]
  (H : Subgroup (GKS K S)) [H.Normal] (hH : H ≤ (alphaInfl hS s hs hs0 π).ker)
  {ι : Type} (place : ι × Bool → Places K S) (hw : ∀ j, (place j).1 ∉ S₀)
  [∀ j, ContinuousSMul (GUr K (place j).1)
    (urRep (MonoidAlgebra ℤ Δ) (shapMod₀ W i s hs hs0 π) (newPlace (place j) (hw j))).V]

/-- **The unramified lifts `hurR`/`hurP` for the ambient module over `S₁`** (PROVED;
`hPw_actualS`), with the inertia hypotheses at each place. -/
theorem hur_actualS [Fintype (GKS K S ⧸ H)]
    (r : GKS K S ⧸ H → GKS K S) (hr : ∀ δ, ((r δ : GKS K S) : GKS K S ⧸ H) = δ)
    (kk : ℤ) {Q y : ambU h1 W Δ} (hQ : kk • Q = y)
    (a : (globalCx (MonoidAlgebra ℤ Δ) (GKS K S) (shapMod hS W i s hs hs0 π)).X 1)
    (hz : ∀ g : Fin 1 → GKS K S,
      ambIotaS hS h01 h1 W i s hs hs0 π
          (gval (A := MonoidAlgebra ℤ Δ) (M := shapMod hS W i s hs hs0 π) a g) =
        T H r hr (ambRhoU h1 W Δ) (thetaH hS s hs hs0 π H hH) 1
          (kummerCochain (ambRhoU h1 W Δ) H Q) g)
    (hunr : ∀ j, inertiaImage (place j) ⊆ (H : Set (GKS K S)))
    (hQin : ∀ j, InertiaFixesDivisionPoint (ambRhoU h1 W Δ) (inertiaImage (place j)) Q)
    (j : ι × Bool) :
    ∃ u, (genuineιq K S (MonoidAlgebra ℤ Δ) (shapMod hS W i s hs hs0 π) (place j)
        (urRep (MonoidAlgebra ℤ Δ) (shapMod₀ W i s hs hs0 π) (newPlace (place j) (hw j)))
        (urId hS (MonoidAlgebra ℤ Δ) (shapMod₀ W i s hs hs0 π) (newPlace (place j) (hw j)))
        (urId_compat hS (MonoidAlgebra ℤ Δ) (shapMod₀ W i s hs hs0 π) (place j) (hw j))).f 1 1 rfl
          u =
      (natHom (resCochains (k := MonoidAlgebra ℤ Δ) (M := shapMod hS W i s hs hs0 π)
        (locMap K S (place j).1))).f 1 1 rfl a :=
  hPw_actualS hS h01 h1 W i s hs hs0 π H hH (place j) (hw j) r hr kk hQ a hz (hunr j) (hQin j)

end UnramifiedLifts

end ZInQ.Contrib.CloudB3E2.NormCochain
