import ZInQKernel.Contrib.CloudB3E2Norm.H20Shapiro
import ZInQKernel.Contrib.CloudB3E2Norm.H20Assembly

/-!
# The primitive class at the new place lies in the unramified condition (`hPw`)

Manuscript `diophantine_zq.tex`, tex 3471–3487 (the unramified condition `[W --(Φ_w − 1)--> W]` at a
new place `w`, mapped to the local cochains by inflation of the `ℤ̂`-cocycles) and tex 4157–4170
(the primitive class is the transferred Kummer class of the primitive support).

At a new place `w ∉ S₀` the coefficient module `M = M₀` (inflated) is unramified. For a genuine
global cochain `a` with `ι(a(g)) = R(g) P̃ − P̃` (the transferred Kummer class, `kummer_weighted_sum`),
if inertia at `w` fixes `P̃` under `R`, the localization `σ ↦ a(p_w σ)` is inflated from the
unramified quotient `Gal(K_w^{ur}/K_w) ≃ ℤ̂`, hence equals the image under `ι_w = genuineιq` of the
unramified cochain `c_x`, `x = a(p_w(Frob))` — exactly (the `d⁰`-term is `d⁰ 0`).

* `localization_factors` (PROVED): the localization depends only on the image in
  `Gal(K_w^{ur}/K_w)`.
* **`hPw_of_inertia`** (PROVED): `∃ y, ι_w(y) = res_w a` in RC30's format (`genuineιq` for RC26's
  `urRep`/`urId`).
* **`inertia_fixes_wsum`** (PROVED): `P̃ = ∑_δ R(r_δ) Q` is fixed by inertia at `w` when `H_f` is
  unramified at `w` (inertia maps into `H`) and the division point `Q` is fixed by every inertia group
  above `w` (`InertiaFixesDivisionPoint`).
* **`InertiaFixesDivisionPoint`** (Prop; kind GLUE, standard): every conjugate of the image of the
  inertia group at `w` fixes `Q`. For `Q` a `2^i`-division point of a point of `E` over the ring class
  field `H_f`, `w ∤ 2f` a place of good reduction, this is the finite étaleness of `[2^i]` on the
  Néron model of `E` over each completion of `H_f` above `w` (residue characteristic prime to `2`):
  the torsion is unramified by Néron–Ogg–Shafarevich (Serre–Tate, *Good reduction of abelian
  varieties*, Ann. Math. 88 (1968), Thm. 1) and the Kummer fibres (division points of a local point)
  are unramified (Silverman, *AEC*, VIII.1.5(b)). (Algebraically the proof only uses conjugation by
  the chosen representatives `r_δ`; the statement for all conjugates is the natural arithmetic
  form.)
* **`hPw_of_transfer`** (PROVED): `hPw` for the transferred Kummer class from `H_f` unramified at `w`
  and `InertiaFixesDivisionPoint`.
* Non-vacuity: `nonVacuity_inertia`.

Kinds: PROVED from the named GLUE input.
-/

noncomputable section

namespace ZInQ.Contrib.CloudB3E2.NormCochain

open ZInQ.Contrib.CloudB3RC53.PairedFunctional ZInQ.Contrib.CloudB3RC53.SelmerDuality
open ZInQ.Contrib.CloudB3RC53.UnramifiedComplex ZInQ.Contrib.CloudB3RC53.RankCounts
open ZInQ.Contrib.CloudB3RC53.HeegnerCohomology.TwistedTransfer
open ZInQ.Manuscript.RC.Wiring ZInQ.Manuscript.RC.SelmerComplex ZInQ.Manuscript.RC.CoefModules
open NumberField IsDedekindDomain

attribute [local instance] TopRep.distribMulAction TopRep.smulCommClass

set_option linter.unusedSectionVars false

section Primitive

variable {K : Type} [Field K] [NumberField K] {S S₀ : Set (HeightOneSpectrum (𝓞 K))}
  (hS : S₀ ⊆ S) (k : Type) [CommRing k] [TopologicalSpace k] [DiscreteTopology k]
  (M₀ : Type) [AddCommGroup M₀] [Module k M₀] [DistribMulAction (GKS K S₀) M₀]
  [SMulCommClass (GKS K S₀) k M₀] [TopologicalSpace M₀] [DiscreteTopology M₀]
  [ContinuousSMul (GKS K S₀) M₀] [Finite M₀]
  {D : Type} [AddCommGroup D] [Module k D] (Rf : GKS K S → Module.End k D)
  (hRmul : ∀ g h, Rf (g * h) = Rf g * Rf h)
  (ι : InflMod hS M₀ →ₗ[k] D) (hι : Function.Injective ι)
  (hιeq : ∀ (g : GKS K S) (m : InflMod hS M₀), ι (g • m) = Rf g (ι m))
  (w : Places K S) (hw : w.1 ∉ S₀)

/-- The localization at `w` of a genuine global `1`-cochain, as a function on `G_{K_w}`. -/
abbrev locz (a : (globalCx k (GKS K S) (InflMod hS M₀)).X 1) (σ : Gloc K w.1) : InflMod hS M₀ :=
  gval (A := k) (M := InflMod hS M₀) a (fun _ => locMap K S w.1 σ)

include hRmul hι hιeq in
/-- The localization is a cocycle. Kind: PROVED. -/
theorem locz_cocycle (a : (globalCx k (GKS K S) (InflMod hS M₀)).X 1) {Pt : D}
    (hz : ∀ g, ι (gval (A := k) (M := InflMod hS M₀) a g) = Rf (g 0) Pt - Pt) (σ τ : Gloc K w.1) :
    locz hS k M₀ w a (σ * τ) = locMap K S w.1 σ • locz hS k M₀ w a τ + locz hS k M₀ w a σ := by
  apply hι
  rw [map_add, hιeq, hz, hz, hz, map_mul, hRmul, Module.End.mul_apply, map_sub]
  abel

include hRmul hι in
/-- **The localization depends only on the image in `Gal(K_w^{ur}/K_w)`** (PROVED), when inertia
fixes `P̃`. -/
theorem localization_factors (a : (globalCx k (GKS K S) (InflMod hS M₀)).X 1) {Pt : D}
    (hz : ∀ g, ι (gval (A := k) (M := InflMod hS M₀) a g) = Rf (g 0) Pt - Pt)
    (hinert : ∀ τ : Gloc K w.1, resUr K w.1 τ = 1 → Rf (locMap K S w.1 τ) Pt = Pt)
    {σ σ' : Gloc K w.1} (h : resUr K w.1 σ = resUr K w.1 σ') :
    locz hS k M₀ w a σ = locz hS k M₀ w a σ' := by
  apply hι
  have hτ : resUr K w.1 (σ⁻¹ * σ') = 1 := by rw [map_mul, map_inv, h, inv_mul_cancel]
  have e : σ' = σ * (σ⁻¹ * σ') := by group
  rw [hz, hz]
  change Rf (locMap K S w.1 σ) Pt - Pt = Rf (locMap K S w.1 σ') Pt - Pt
  rw [e, map_mul, hRmul, Module.End.mul_apply, hinert _ hτ]

include hRmul hι hιeq in
/-- **`hPw` from inertia-invariance** (PROVED; tex 3471–3487): the localization at `w` of `a` lies in
the image of RC30's unramified condition `genuineιq` (RC26's `urRep`, `urId`): it is `ι_w(c_x)` for
`x = a(p_w(Frob))`. -/
theorem hPw_of_inertia [ContinuousSMul (GUr K w.1) (urRep k M₀ (newPlace w hw)).V]
    (a : (globalCx k (GKS K S) (InflMod hS M₀)).X 1) {Pt : D}
    (hz : ∀ g, ι (gval (A := k) (M := InflMod hS M₀) a g) = Rf (g 0) Pt - Pt)
    (hinert : ∀ τ : Gloc K w.1, resUr K w.1 τ = 1 → Rf (locMap K S w.1 τ) Pt = Pt) :
    ∃ y : (genuineUq K S k w (urRep k M₀ (newPlace w hw))).X 1,
      (genuineιq K S k (InflMod hS M₀) w (urRep k M₀ (newPlace w hw)) (urId hS k M₀ (newPlace w hw))
        (urId_compat hS k M₀ w hw)).f 1 1 rfl y =
      (stageRes K S k (InflMod hS M₀) w).f 1 1 rfl a := by
  classical
  -- the function on `Gal(K_w^ur/K_w)`
  set z := locz hS k M₀ w a with hzdef
  let pre : GUr K w.1 → Gloc K w.1 := fun γ => (resUr_surjective K w.1 γ).choose
  have hpre : ∀ γ, resUr K w.1 (pre γ) = γ := fun γ => (resUr_surjective K w.1 γ).choose_spec
  let c' : GUr K w.1 → (urRep k M₀ (newPlace w hw)).V := fun γ => z (pre γ)
  have hc'z : ∀ σ, c' (resUr K w.1 σ) = z σ := fun σ =>
    localization_factors hS k M₀ Rf hRmul ι hι w a hz hinert (hpre _)
  -- continuity
  have hzc : Continuous z := by
    have h1 : Continuous fun g : Fin 1 → GKS K S => gval (A := k) (M := InflMod hS M₀) a g :=
      ((contSubCx k (GKS K S) (InflMod hS M₀)).el a).2
    exact h1.comp (continuous_pi fun _ => (locMap K S w.1).continuous)
  have hq : Topology.IsQuotientMap (resUr K w.1) :=
    IsClosedMap.isQuotientMap ((resUr K w.1).continuous.isClosedMap) (resUr K w.1).continuous
      (resUr_surjective K w.1)
  have hc'c : Continuous c' := by
    rw [hq.continuous_iff]
    have : c' ∘ resUr K w.1 = z := funext hc'z
    rw [this]
    exact hzc
  -- cocycle
  have hc'coc : ∀ α β : GUr K w.1, c' (α * β) = α • c' β + c' α := by
    intro α β
    obtain ⟨σ, rfl⟩ := resUr_surjective K w.1 α
    obtain ⟨τ, rfl⟩ := resUr_surjective K w.1 β
    rw [← map_mul, hc'z, hc'z, hc'z]
    change locz hS k M₀ w a (σ * τ) = _
    rw [locz_cocycle hS k M₀ Rf hRmul ι hι hιeq w a hz]
    exact congrArg (· + z σ) (urId_compat hS k M₀ w hw σ (z τ)).symm
  -- uniqueness
  have huniq := cocycle_unique (eUr K w.1) hc'c (urCocycle_continuous (eUr K w.1) _ (c' (frobElt (eUr K w.1))))
    hc'coc (urCocycle_cocycle (eUr K w.1) _ _) (urCocycle_frob (eUr K w.1) _ _).symm
  refine ⟨(urG1 (S := S) w (urRep k M₀ (newPlace w hw))).inv.hom (c' (frobElt (eUr K w.1))), ?_⟩
  rw [genuineιq_f1, iso_inv_hom_apply']
  refine Subtype.ext (funext fun σ => ?_)
  change (urId hS k M₀ (newPlace w hw))
      (urCocycle (eUr K w.1) (urRep k M₀ (newPlace w hw)) (c' (frobElt (eUr K w.1)))
        (resUr K w.1 (σ 0))) =
    gval (A := k) (M := InflMod hS M₀) a (fun i => locMap K S w.1 (σ i))
  rw [← huniq]
  have hσ : (fun i => locMap K S w.1 (σ i)) = fun _ => locMap K S w.1 (σ 0) := by
    funext i
    rw [Fin.fin_one_eq_zero i]
  rw [hσ]
  exact hc'z (σ 0)

end Primitive

/-! ### Inertia fixes the weighted division point -/

section Inertia

variable {G : Type*} [Group G] {k : Type*} [CommRing k] {D : Type*} [AddCommGroup D] [Module k D]
  (ρ : G →* Module.End k D) (H : Subgroup G) [H.Normal] [Fintype (G ⧸ H)]
  (r : G ⧸ H → G) (hr : ∀ δ, ((r δ : G) : G ⧸ H) = δ) (θ : G ⧸ H →* kˣ)

/-- **Inertia fixes the division point** (Prop; GLUE): every conjugate of an element of the inertia
image `I` fixes `Q`. Kind: definition (Prop). -/
def InertiaFixesDivisionPoint (I : Set G) (Q : D) : Prop :=
  ∀ (g t : G), t ∈ I → ρ (g * t * g⁻¹) Q = Q

/-- **The weighted division point is fixed by inertia** (PROVED): if `I ⊆ H` (`H_f` unramified at
`w`) and every conjugate of `I` fixes `Q`, then `R(t) (∑_δ R(r_δ) Q) = ∑_δ R(r_δ) Q` for `t ∈ I`. -/
theorem inertia_fixes_wsum (I : Set G) (hIH : I ⊆ H) {Q : D}
    (hQ : InertiaFixesDivisionPoint ρ I Q) {t : G} (ht : t ∈ I) :
    R H ρ θ t (wsum ρ H r θ Q) = wsum ρ H r θ Q := by
  simp only [wsum, map_sum]
  refine Finset.sum_congr rfl fun δ _ => ?_
  have hc : (r δ)⁻¹ * t * r δ ∈ H := by
    have := (inferInstance : H.Normal).conj_mem t (hIH ht) (r δ)⁻¹
    simpa using this
  have e : t * r δ = r δ * ((r δ)⁻¹ * t * r δ) := by group
  rw [← Module.End.mul_apply, ← ZInQ.Contrib.CloudB3RC53.HeegnerCohomology.TwistedTransfer.R_mul, e, ZInQ.Contrib.CloudB3RC53.HeegnerCohomology.TwistedTransfer.R_mul, Module.End.mul_apply,
    R_of_mem H ρ θ hc]
  congr 1
  have := hQ (r δ)⁻¹ t ht
  simpa [mul_assoc] using this

end Inertia

/-! ### `hPw` for the transferred Kummer class -/

section Transfer

variable {K : Type} [Field K] [NumberField K] {S S₀ : Set (HeightOneSpectrum (𝓞 K))}
  (hS : S₀ ⊆ S) (k : Type) [CommRing k] [TopologicalSpace k] [DiscreteTopology k]
  (M₀ : Type) [AddCommGroup M₀] [Module k M₀] [DistribMulAction (GKS K S₀) M₀]
  [SMulCommClass (GKS K S₀) k M₀] [TopologicalSpace M₀] [DiscreteTopology M₀]
  [ContinuousSMul (GKS K S₀) M₀] [Finite M₀]
  {D : Type} [AddCommGroup D] [Module k D] (ρ : GKS K S →* Module.End k D)
  (H : Subgroup (GKS K S)) [H.Normal] [Fintype (GKS K S ⧸ H)]
  (r : GKS K S ⧸ H → GKS K S) (hr : ∀ δ, ((r δ : GKS K S) : GKS K S ⧸ H) = δ)
  (θ : GKS K S ⧸ H →* kˣ)
  (ι : InflMod hS M₀ →ₗ[k] D) (hι : Function.Injective ι)
  (hιeq : ∀ (g : GKS K S) (m : InflMod hS M₀), ι (g • m) = R H ρ θ g (ι m))
  (w : Places K S) (hw : w.1 ∉ S₀)

/-- The image of the inertia group at `w` in `G_{K,S}`. -/
def inertiaImage : Set (GKS K S) :=
  {t | ∃ τ : Gloc K w.1, resUr K w.1 τ = 1 ∧ locMap K S w.1 τ = t}

include hr hι hιeq in
/-- **`hPw` for the transferred Kummer class** (PROVED; tex 3471–3487, 4157–4170): for a genuine
global cochain `a` carried to `𝒯_θ(κ(Q))` (`k Q = y`), if `H_f` is unramified at
`w` (`inertiaImage w ⊆ H`) and `InertiaFixesDivisionPoint` holds for `Q`, the localization at `w`
lies in the image of RC30's unramified condition. -/
theorem hPw_of_transfer [ContinuousSMul (GUr K w.1) (urRep k M₀ (newPlace w hw)).V]
    (kk : ℤ) {Q y : D} (hQ : kk • Q = y)
    (a : (globalCx k (GKS K S) (InflMod hS M₀)).X 1)
    (hz : ∀ g : Fin 1 → GKS K S,
      ι (gval (A := k) (M := InflMod hS M₀) a g) = T H r hr ρ θ 1 (kummerCochain ρ H Q) g)
    (hunr : inertiaImage w ⊆ (H : Set (GKS K S)))
    (hQin : InertiaFixesDivisionPoint ρ (inertiaImage w) Q) :
    ∃ y : (genuineUq K S k w (urRep k M₀ (newPlace w hw))).X 1,
      (genuineιq K S k (InflMod hS M₀) w (urRep k M₀ (newPlace w hw)) (urId hS k M₀ (newPlace w hw))
        (urId_compat hS k M₀ w hw)).f 1 1 rfl y =
      (stageRes K S k (InflMod hS M₀) w).f 1 1 rfl a := by
  obtain ⟨_, hT⟩ := kummer_weighted_sum H r hr ρ θ kk y Q hQ
  refine hPw_of_inertia hS k M₀ (R H ρ θ) (ZInQ.Contrib.CloudB3RC53.HeegnerCohomology.TwistedTransfer.R_mul H ρ θ) ι hι hιeq w hw a
    (Pt := wsum ρ H r θ Q) (fun g => ?_) (fun τ hτ => ?_)
  · rw [hz]
    exact hT g
  · exact inertia_fixes_wsum ρ H r θ (inertiaImage w) hunr hQin ⟨τ, hτ, rfl⟩

end Transfer

/-! ### Non-vacuity -/

/-- **Non-vacuity of `InertiaFixesDivisionPoint`** (logical consistency only): the trivial
representation fixes everything; the intended elliptic instance is the cited arithmetic fact.
Kind: PROVED. -/
theorem nonVacuity_inertia {G : Type*} [Group G] {k : Type*} [CommRing k] {D : Type*}
    [AddCommGroup D] [Module k D] (I : Set G) (Q : D) :
    InertiaFixesDivisionPoint (1 : G →* Module.End k D) I Q :=
  fun _ _ _ => rfl

end ZInQ.Contrib.CloudB3E2.NormCochain
