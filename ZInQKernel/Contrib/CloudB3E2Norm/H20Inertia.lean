import ZInQKernel.Contrib.CloudB3E2Norm.H20Twist
import ZInQKernel.Contrib.CloudB3E2Norm.H20Primitive

/-!
# `InertiaFixesDivisionPoint` and the transfer field unramified at `w`, for the actual data

Manuscript `diophantine_zq.tex`, tex 3471–3487 (the unramified condition at a new place `w ∉ S₀`).

`H20Primitive.hPw_of_transfer` takes two inputs at the new place `w`: the image of the inertia
group at `w` lies in `H` (the transfer field unramified at `w`; for the actual data `H = G_L`, `L`
the field cut out by `Ψ_i`), and `InertiaFixesDivisionPoint` (every conjugate
of the inertia image fixes the division point `Q`). For a new place `w ∉ S₀`:

* **`infl_inertiaImage`** (PROVED): the inertia image at `w` maps trivially to `G_{K,S₀}` (lane
  RC26's factorization of the localization through `Gal(K_w^{ur}/K_w)` for `w ∉ S₀`,
  `urFactor_spec`, with `locMap_compat`).
* **`inertiaFixes_of_inflated`** (PROVED): if `ρ` factors through `G_{K,S} → G_{K,S₀}` on `Q`, then
  `InertiaFixesDivisionPoint` holds; **`inertiaImage_le_of_ker`** (PROVED): if
  `ker(G_{K,S} → G_{K,S₀}) ≤ H`, the inertia image lies in `H`.
* **`inertiaFixes_actual`**, **`inertiaImage_le_actual`** (PROVED): both hold for the actual data
  of `H20Twist.lean` (the ambient module of points `ambD` is inflated from `G_{K,S₀}`, and
  `H = ker(π ∘ infl)` contains the kernel of inflation) — with no further input.
* `ambIota_injective` (PROVED); **`hPw_actual`** (PROVED): `hPw` for the actual data at `w ∉ S₀`,
  for every genuine cochain carried to `𝒯_θ(κ(Q))` with `Q` in the ambient module of points.
* Non-vacuity: the hypotheses are those of `H20Twist.lean`/`H20Actual.lean` and `w ∉ S₀`.

So the arithmetic content of Néron–Ogg–Shafarevich in `hPw` is now the existence of the division
point `Q ∈ ℤ[Δ] ⊗ E(K_{S₀})` of the weighted sum (the hypothesis `hQ` of the norm identity), i.e. that
the `2^i`-division points of the Heegner points lie in `E(K_{S₀})`; for points over `K` this is the
tree's `DivisionPoints.globalDivisionPointsInSupport_of_goodReduction` (Silverman AEC VIII.1.5(b),
proved), for points over the ring class fields the same argument over `H_f` (named, not formalized).

Kinds: PROVED.
-/

noncomputable section

namespace ZInQ.Contrib.CloudB3E2.NormCochain

open ZInQ.Contrib.CloudB3RC53.HeegnerCohomology.TwistedTransfer
open ZInQ.Contrib.CloudB3RC53.UnramifiedComplex ZInQ.Contrib.CloudB3RC53.RankCounts
open ZInQ.Manuscript.RC.Wiring ZInQ.Manuscript.RC.SelmerComplex ZInQ.Manuscript.RC.CoefModules
open ZInQ.Manuscript.RC.HeegnerAlgebra (Acoef)
open NumberField IsDedekindDomain

attribute [local instance] groupRingTop ptSAction TopRep.distribMulAction TopRep.smulCommClass

set_option linter.unusedSectionVars false

section Generic

variable {K : Type} [Field K] [NumberField K] {S S₀ : Set (HeightOneSpectrum (𝓞 K))}
  (hS : S₀ ⊆ S) (w : Places K S) (hw : w.1 ∉ S₀)

include hw in
/-- **The inertia image at `w ∉ S₀` maps trivially to `G_{K,S₀}`** (PROVED). -/
theorem infl_inertiaImage {t : GKS K S} (ht : t ∈ inertiaImage w) : inflMap K hS t = 1 := by
  obtain ⟨τ, hτ, rfl⟩ := ht
  rw [locMap_compat K hS w.1 τ, urFactor_spec K (newPlace w hw) τ]
  change urFactor K (newPlace w hw) (resUr K w.1 τ) = 1
  rw [hτ, map_one]

include hw in
/-- **`InertiaFixesDivisionPoint` from inflation** (PROVED): if `ρ` factors through
`G_{K,S} → G_{K,S₀}` on `Q`, every conjugate of the inertia image at `w ∉ S₀` fixes `Q`. -/
theorem inertiaFixes_of_inflated {k D : Type*} [CommRing k] [AddCommGroup D] [Module k D]
    (ρ : GKS K S →* Module.End k D) {Q : D}
    (hQ : ∀ g : GKS K S, inflMap K hS g = 1 → ρ g Q = Q) :
    InertiaFixesDivisionPoint ρ (inertiaImage w) Q := by
  intro g t ht
  apply hQ
  rw [map_mul, map_mul, infl_inertiaImage hS w hw ht, mul_one, map_inv, mul_inv_cancel]

include hw in
/-- **The inertia image lies in `H` when `H` contains the kernel of inflation** (PROVED). -/
theorem inertiaImage_le_of_ker (H : Subgroup (GKS K S))
    (hH : ∀ g : GKS K S, inflMap K hS g = 1 → g ∈ H) :
    inertiaImage w ⊆ (H : Set (GKS K S)) :=
  fun _ ht => hH _ (infl_inertiaImage hS w hw ht)

end Generic

section Actual

variable {K : Type} [Field K] [NumberField K] {S S₀ : Set (HeightOneSpectrum (𝓞 K))}
  (hS : S₀ ⊆ S) (W : WeierstrassCurve K) [W.IsElliptic] (i : ℕ) [NeZero i] (s : KS K S₀) {h : K}
  (hs : s ^ 2 = algebraMap K (KS K S₀) h) (hs0 : s ≠ 0)
  {Δ : Type} [CommGroup Δ] [Finite Δ] (π : GKS K S₀ →* Δ) (w : Places K S) (hw : w.1 ∉ S₀)

include hw in
/-- **`InertiaFixesDivisionPoint` for the actual ambient module** (PROVED): every element of
`ambD` (inflated from `G_{K,S₀}`) is fixed by the conjugates of the inertia image at `w ∉ S₀`.
**Superseded for the wiring** (see `H20Untwisted.lean`): the statement is valid, but with the
`χ_h`-twisted ambient module the norm relation needed by `h1_shapiro` holds only when `χ_h(σ_q) =
1`, and the point factor loses the text's sign `z = χ_h(σ_q) Ψ(σ_q)` (tex 3915, 4158–4172); wire the
untwisted instance instead (`inertiaFixesU`). -/
theorem inertiaFixes_actual (Q : ambD hS W s hs hs0 (Δ := Δ)) :
    InertiaFixesDivisionPoint (ambRho hS W s hs hs0 (Δ := Δ)) (inertiaImage w) Q :=
  inertiaFixes_of_inflated hS w hw _ fun g hg => by
    change (inflMap K hS g • (show ambD₀ W s hs hs0 (Δ := Δ) from Q) : ambD₀ W s hs hs0) = Q
    rw [hg, one_smul]

include hw in
/-- **`L` unramified at `w` for the actual data** (PROVED): the inertia image at `w ∉ S₀` lies
in `ker(π ∘ infl) = G_L`. -/
theorem inertiaImage_le_actual : inertiaImage w ⊆ ((piInfl hS π).ker : Set (GKS K S)) :=
  inertiaImage_le_of_ker hS w hw _ fun g hg => by
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply]
    change π (inflMap K hS g) = 1
    rw [hg, map_one]

/-- `ι = 1 ⊗ incl` is injective (`ℤ[Δ]` flat). Kind: PROVED. -/
theorem ambIota_injective [TopologicalSpace (Acoef i)] [DiscreteTopology (Acoef i)] :
    Function.Injective (ambIota hS W i s hs hs0 π) := by
  have h := Module.Flat.lTensor_preserves_injective_linearMap (M := MonoidAlgebra ℤ Δ)
    (torsIncl K S₀ W i) Subtype.val_injective
  intro x y hxy
  apply h
  have := hxy
  change LinearMap.baseChange _ _ x = LinearMap.baseChange _ _ y at this
  rwa [LinearMap.baseChange_eq_lTensor] at this

include hw in
/-- **`hPw` for the actual data** (PROVED; tex 3471–3487): at a new place `w ∉ S₀`, for every
genuine global cochain `a` over `ℤ[Δ]` carried by `ι` to `𝒯_{[π]}(κ(Q))` with `Q` in the ambient
module of points (`k Q = y`), the localization at `w` lies in the image of RC30's unramified
condition (RC26's `urRep`, `urId`).
**Superseded for the wiring** (see `H20Untwisted.lean`): the statement is valid, but with the
`χ_h`-twisted ambient module the norm relation needed by `h1_shapiro` holds only when `χ_h(σ_q) =
1`, and the point factor loses the text's sign `z = χ_h(σ_q) Ψ(σ_q)` (tex 3915, 4158–4172); wire the
untwisted instance instead (`hPw_actualU`). -/
theorem hPw_actual [TopologicalSpace (Acoef i)] [DiscreteTopology (Acoef i)]
    [IsOpenKer (alphaShap s hs hs0 π)]
    [Fintype (GKS K S ⧸ (piInfl hS π).ker)] (r : GKS K S ⧸ (piInfl hS π).ker → GKS K S)
    (hr : ∀ δ, ((r δ : GKS K S) : GKS K S ⧸ (piInfl hS π).ker) = δ)
    [ContinuousSMul (GUr K w.1)
      (urRep (MonoidAlgebra ℤ Δ) (shapMod₀ W i s hs hs0 π) (newPlace w hw)).V]
    (kk : ℤ) {Q y : ambD hS W s hs hs0 (Δ := Δ)} (hQ : kk • Q = y)
    (a : (globalCx (MonoidAlgebra ℤ Δ) (GKS K S) (shapMod hS W i s hs hs0 π)).X 1)
    (hz : ∀ g : Fin 1 → GKS K S,
      ambIota hS W i s hs hs0 π (gval (A := MonoidAlgebra ℤ Δ) (M := shapMod hS W i s hs hs0 π) a g) =
        T (piInfl hS π).ker r hr (ambRho hS W s hs hs0 (Δ := Δ)) (thetaPi hS π) 1
          (kummerCochain (ambRho hS W s hs hs0 (Δ := Δ)) (piInfl hS π).ker Q) g) :
    ∃ y : (genuineUq K S (MonoidAlgebra ℤ Δ) w
        (urRep (MonoidAlgebra ℤ Δ) (shapMod₀ W i s hs hs0 π) (newPlace w hw))).X 1,
      (genuineιq K S (MonoidAlgebra ℤ Δ) (shapMod hS W i s hs hs0 π) w
        (urRep (MonoidAlgebra ℤ Δ) (shapMod₀ W i s hs hs0 π) (newPlace w hw))
        (urId hS (MonoidAlgebra ℤ Δ) (shapMod₀ W i s hs hs0 π) (newPlace w hw))
        (urId_compat hS (MonoidAlgebra ℤ Δ) (shapMod₀ W i s hs hs0 π) w hw)).f 1 1 rfl y =
      (stageRes K S (MonoidAlgebra ℤ Δ) (shapMod hS W i s hs hs0 π) w).f 1 1 rfl a :=
  hPw_of_transfer hS (MonoidAlgebra ℤ Δ) (shapMod₀ W i s hs hs0 π) (ambRho hS W s hs hs0 (Δ := Δ))
    (piInfl hS π).ker r hr (thetaPi hS π) (ambIota hS W i s hs hs0 π)
    (ambIota_injective hS W i s hs hs0 π) (ambIota_equivariant hS W i s hs hs0 π) w hw kk hQ a hz
    (inertiaImage_le_actual hS π w hw) (inertiaFixes_actual hS W s hs hs0 w hw Q)

end Actual

end ZInQ.Contrib.CloudB3E2.NormCochain
