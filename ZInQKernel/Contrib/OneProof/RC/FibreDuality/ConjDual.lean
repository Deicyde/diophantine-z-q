import ZInQKernel.Contrib.OneProof.RC.FibreDuality.Continuity
import ZInQKernel.Contrib.OneProof.RC.CoefModules.Conjugate
import ZInQKernel.Contrib.OneProof.RC.LambdaCoef.Topology

/-!
# Lane RC31, part 8: the conjugation transport `τ^*V_𝔭(α) ≃ V_𝔭(α⁻¹)` at the fibres

Manuscript `diophantine_zq.tex` (11/5), Lemma `ex:arith-conjugate-duality`, tex 2778–2805:

> Fix an actual complex conjugation `τ ∈ G_ℚ`, so that `τ² = 1`. … Then `α_i^τ = α_i^{-1}`. …
> The Weil pairing gives the following `R_i`-linear perfect pairing:
> `M_i ⊗_{R_i} τ^*M_i → R_i(1)`, `(v,w) ↦ e_2(v, ρ_T(τ)w)`. … Thus `τ^*M_i ≃ M_i^*(1)`.

and (H12), tex 3093: `J = ρ_T(τ)`, `J² = I`; tex 5011: the action `c^τ(g) = J c(τ⁻¹ g τ)`.
Here the transport is carried out at the characteristic-zero fibres `V_𝔭 = k(𝔭) ⊗_{ℤ₂} T_2E`
of lane RC28 (tex 4976–5200).

* `conjTate`: **`J = ρ_T(τ)` on `T_2E`**, coordinatewise `ρ_T(τ)` on the levels `E(K_S)[2^n]`;
  `ℤ₂`-linear, `conjTate_smul`: `J(σx) = c(σ) J x`, `conjTate_conjTate`: `J² = 1`,
  `continuous_conjTate`.
* `conjVP`: **`τ^*V_𝔭(α) → V_𝔭(α⁻¹)`, `id ⊗ J`**, `k(𝔭)`-linear; `conjVP_smul`: equivariant when
  `α ∘ c = α⁻¹`; `conjVP_bijective`; `conjVP_latt` (lattice to lattice); `continuous_conjVP`.
* The instances on `τ^*V_𝔭(α)` used by the duality interface, and `isLatticeTop_pullVP`: the
  pullback carries the same lattice topology.
* `one_conj`: non-vacuity of the hypothesis `α ∘ c = α⁻¹` (the trivial character);
  `isContChar_inv`: `α⁻¹` is continuous with `α`.

Kinds: definitions and PROVED.
-/

noncomputable section

namespace ZInQ.Manuscript.RC.FibreDuality

open NumberField IsDedekindDomain Filter Topology TensorProduct
open ZInQ.Manuscript.RC.Uniform (Lambda)
open ZInQ.Manuscript.RC.Wiring (ResAt)
open ZInQ.Manuscript.RC.SelmerComplex (GKS)
open ZInQ.Manuscript.RC.CoefModules (PullMod ActualConj conjTors conjTors_smul conjTors_conjTors
  conjPt coe_conjTors)
open ZInQ.Manuscript.RC.LambdaCoef
open scoped Pointwise PowerSeries.WithPiTopology

/-! ### Generic instances on the pullback -/

section PullInst

variable {G : Type} [Group G] [TopologicalSpace G] (c : G →ₜ* G) (M : Type) [AddCommGroup M]

/-- The pullback `τ^*M` is a topological group (same group, same topology) (tex 4976–5200).
Kind: PROVED. -/
instance pullMod_isTopologicalAddGroup [TopologicalSpace M] [IsTopologicalAddGroup M] :
    IsTopologicalAddGroup (PullMod c M) :=
  inferInstanceAs (IsTopologicalAddGroup M)

/-- The scalars of `τ^*M` act continuously (same module) (tex 4976–5200). Kind: PROVED. -/
instance pullMod_continuousConstSMul {A : Type} [CommRing A] [Module A M] [TopologicalSpace M]
    [ContinuousConstSMul A M] : ContinuousConstSMul A (PullMod c M) :=
  inferInstanceAs (ContinuousConstSMul A M)

/-- Scalar towers pass to `τ^*M` (same module) (tex 4976–5200). Kind: PROVED. -/
instance pullMod_isScalarTower {A B : Type} [CommRing A] [CommRing B] [SMul A B] [Module A M]
    [Module B M] [IsScalarTower A B M] : IsScalarTower A B (PullMod c M) :=
  inferInstanceAs (IsScalarTower A B M)

/-- **`τ^*M` carries the lattice topology of `M`**: the same lattice, stable under the pulled-back
action since it is stable under every `c(σ)` (tex 2778–2805). Kind: PROVED. -/
theorem isLatticeTop_pullMod [DistribMulAction G M] [Module Lambda M] [TopologicalSpace M]
    (h : IsLatticeTop G M) : IsLatticeTop G (PullMod c M) := by
  obtain ⟨Y, hfg, hst, hex, hb⟩ := h.exists_lattice
  exact ⟨⟨Y, hfg, fun g y hy => hst (c g) y hy, hex, hb⟩⟩

end PullInst

/-! ### `J = ρ_T(τ)` on `T_2E` -/

variable {K : Type} [Field K] [NumberField K] {S : Set (HeightOneSpectrum (𝓞 K))}
  (C : ActualConj K S) (W : WeierstrassCurve K) (hW : W.map (C.κ : K →+* K) = W)

/-- `ρ_T(τ)` commutes with `P ↦ 2P` (it is additive) (tex 3093). Kind: PROVED. -/
theorem conjTors_mem_tateSub (x : TateS K S W) :
    (fun n => conjTors C W hW _ ((x : ∀ n, Lev K S W n) n)) ∈ tateSub K S W := by
  intro n
  apply Subtype.ext
  rw [coe_transLev, coe_conjTors, coe_conjTors, ← map_nsmul]
  exact congrArg _ (x.two_smul_pt n)

/-- **`J = ρ_T(τ)` on the Tate module `T_2E`** (tex 2778–2805, tex 3093): coordinatewise
`ρ_T(τ)` on the levels `E(K_S)[2^n]`; `ℤ₂`-linear. Kind: definition (linearity PROVED). -/
def conjTate : TateS K S W →ₗ[ℤ_[2]] TateS K S W where
  toFun x := ⟨fun n => conjTors C W hW _ ((x : ∀ n, Lev K S W n) n), conjTors_mem_tateSub C W hW x⟩
  map_add' x y := TateS.ext' fun n => map_add (conjPt C W hW) (x.pt n) (y.pt n)
  map_smul' a x := TateS.ext' fun n => map_nsmul (conjPt C W hW) (resN n a) (x.pt n)

/-- The coordinates of `J x` (tex 3093). Kind: PROVED (definitional). -/
theorem conjTate_pt (x : TateS K S W) (n : ℕ) :
    (conjTate C W hW x).pt n = conjPt C W hW (x.pt n) := rfl

/-- **`J(σ x) = c(σ) J x`** (tex 5011: `ρ_T(τστ⁻¹) J = J ρ_T(σ)`). Kind: PROVED. -/
theorem conjTate_smul (σ : GKS K S) (x : TateS K S W) :
    conjTate C W hW (σ • x) = C.conj σ • conjTate C W hW x :=
  Subtype.ext (funext fun n => conjTors_smul C W hW _ σ ((x : ∀ n, Lev K S W n) n))

/-- **`J² = 1`** (tex 2778 "`τ² = 1`", tex 3093 "`J² = I`"). Kind: PROVED. -/
theorem conjTate_conjTate (x : TateS K S W) : conjTate C W hW (conjTate C W hW x) = x :=
  Subtype.ext (funext fun n => conjTors_conjTors C W hW _ ((x : ∀ n, Lev K S W n) n))

attribute [local instance] levTop in
/-- **`J` is continuous** for the inverse-limit topology of `T_2E` (tex 4976–5200). Kind: PROVED. -/
theorem continuous_conjTate : Continuous (conjTate C W hW) := by
  refine continuous_induced_rng.mpr (continuous_pi fun n => ?_)
  exact (continuous_of_discreteTopology (f := conjTors C W hW ((2 ^ n : ℕ) : ℤ))).comp
    (continuous_projLev n)

/-! ### `τ^*V_𝔭(α) ≃ V_𝔭(α⁻¹)` -/

section Fibre

variable (P : Ideal Lambda) [P.IsPrime] (α : GKS K S →* Lambdaˣ)

/-- `id ⊗ J` on `k(𝔭) ⊗_{ℤ₂} T_2E`. (tex 2798–2805). Kind: definition. -/
def conjBase : ResAt P ⊗[ℤ_[2]] TateS K S W →ₗ[ResAt P] ResAt P ⊗[ℤ_[2]] TateS K S W :=
  (conjTate C W hW).baseChange (ResAt P)

/-- `(id ⊗ J)(c ⊗ Q) = c ⊗ J Q` (tex 2798–2805). Kind: PROVED (definitional). -/
theorem conjBase_tmul (c : ResAt P) (Q : TateS K S W) :
    conjBase C W hW P (c ⊗ₜ Q) = c ⊗ₜ conjTate C W hW Q := rfl

/-- `(id ⊗ J)² = 1` (tex 2778–2805). Kind: PROVED. -/
theorem conjBase_conjBase (x : ResAt P ⊗[ℤ_[2]] TateS K S W) :
    conjBase C W hW P (conjBase C W hW P x) = x := by
  induction x using TensorProduct.inductionOn with
  | tmul c Q => rw [conjBase_tmul, conjBase_tmul, conjTate_conjTate]
  | add x y hx hy => rw [map_add, map_add, hx, hy]

/-- `id ⊗ J` read as a map `V_𝔭(α) → V_𝔭(α⁻¹)` (the underlying map of `conjVP`;
tex 2798–2805). Kind: definition. -/
def conjVPv : VP K S W P α →ₗ[ResAt P] VP K S W P α⁻¹ :=
  conjBase C W hW P

/-- `(id ⊗ J)(c ⊗ Q) = c ⊗ J Q` on `V_𝔭(α)` (tex 2798–2805). Kind: PROVED (definitional). -/
theorem conjVPv_tmul (c : ResAt P) (Q : TateS K S W) :
    conjVPv C W hW P α (show VP K S W P α from c ⊗ₜ Q) =
      show VP K S W P α⁻¹ from c ⊗ₜ conjTate C W hW Q := rfl

/-- `id ⊗ J` intertwines `c(σ)` on `V_𝔭(α)` with `σ` on `V_𝔭(α⁻¹)` when `α ∘ c = α⁻¹`
(tex 2786–2795, tex 5011). Kind: PROVED. -/
theorem conjVPv_act (hα : ∀ σ, α (C.conj σ) = (α σ)⁻¹) (σ : GKS K S) (x : VP K S W P α) :
    conjVPv C W hW P α (VP.act P (C.conj σ) x) = VP.act P σ (conjVPv C W hW P α x) := by
  induction x using VP.induction with
  | zero => rw [map_zero, map_zero, map_zero]
  | tmul c Q =>
    rw [VP.act_tmul, conjVPv_tmul, conjVPv_tmul, VP.act_tmul, conjTate_smul, C.conj_conj,
      coe_resChar, coe_resChar, hα σ, MonoidHom.inv_apply]
  | add x y hx hy => rw [map_add, map_add, hx, hy, map_add, map_add]

/-- `id ⊗ J` commutes with `Λ` (acting through `k(𝔭)`) (tex 4976–5200). Kind: PROVED. -/
theorem conjVPv_lambda_smul (l : Lambda) (x : VP K S W P α) :
    conjVPv C W hW P α (l • x) = l • conjVPv C W hW P α x := by
  rw [← algebraMap_smul (ResAt P) l x, map_smul, algebraMap_smul]

/-- **`τ^*V_𝔭(α) → V_𝔭(α⁻¹)`, `w ↦ (id ⊗ ρ_T(τ)) w`** (tex 2798–2805: `(v, w) ↦ e_2(v, ρ_T(τ)w)`
pairs `M` with `τ^*M`; tex 3093: `J = ρ_T(τ)`), `k(𝔭)`-linear (it fixes the coefficients).
Kind: definition. -/
def conjVP : PullMod C.conj (VP K S W P α) →ₗ[ResAt P] VP K S W P α⁻¹ :=
  conjVPv C W hW P α

/-- `conjVP (c ⊗ Q) = c ⊗ J Q` (tex 2798–2805). Kind: PROVED (definitional). -/
theorem conjVP_tmul (c : ResAt P) (Q : TateS K S W) :
    conjVP C W hW P α (show VP K S W P α from c ⊗ₜ Q) =
      show VP K S W P α⁻¹ from c ⊗ₜ conjTate C W hW Q := rfl

/-- **`τ^*V_𝔭(α) → V_𝔭(α⁻¹)` is `G_{K,S}`-equivariant when `α ∘ c = α⁻¹`** (tex 2786–2795:
"`α_i^τ = α_i^{-1}`", "the two scalar characters multiply to one"; tex 5011:
`c^τ(g) = J c(τ⁻¹ g τ)`). The action on the source is the pulled-back one, `σ ⋆ w = c(σ) • w`.
Kind: PROVED. -/
theorem conjVP_smul (hα : ∀ σ, α (C.conj σ) = (α σ)⁻¹) (σ : GKS K S)
    (w : PullMod C.conj (VP K S W P α)) :
    conjVP C W hW P α (σ • w) = σ • conjVP C W hW P α w :=
  conjVPv_act C W hW P α hα σ w

/-- **`ρ_T(τ)² = 1`: `τ^*V_𝔭(α) → V_𝔭(α⁻¹)` is bijective** (tex 2795 "`ρ_T(τ)² = 1`").
Kind: PROVED. -/
theorem conjVP_bijective : Function.Bijective (conjVP C W hW P α) :=
  Function.bijective_iff_has_inverse.mpr
    ⟨conjBase C W hW P, conjBase_conjBase C W hW P, conjBase_conjBase C W hW P⟩

/-- **`τ^*V_𝔭(α) ≃ V_𝔭(α⁻¹)`** as `k(𝔭)`-vector spaces (tex 2798–2805). Kind: definition. -/
def conjVPEquiv : PullMod C.conj (VP K S W P α) ≃ₗ[ResAt P] VP K S W P α⁻¹ :=
  LinearEquiv.ofBijective (conjVP C W hW P α) (conjVP_bijective C W hW P α)

/-- The underlying map of `conjVPEquiv` is `conjVP` (tex 2778–2805). Kind: PROVED (definitional). -/
theorem conjVPEquiv_apply (w : PullMod C.conj (VP K S W P α)) :
    conjVPEquiv C W hW P α w = conjVP C W hW P α w := rfl

/-- **`id ⊗ J` maps the lattice `Λ · (1 ⊗ T_2E)` into the lattice.** (tex 2778–2805).
Kind: PROVED. -/
theorem conjVPv_latt {x : VP K S W P α} (hx : x ∈ latt K S W P α) :
    conjVPv C W hW P α x ∈ latt K S W P α⁻¹ := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨Q, rfl⟩ := hx
    rw [conjVPv_tmul]
    exact one_tmul_mem_latt P _
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add x y _ _ hx hy => rw [map_add]; exact Submodule.add_mem _ hx hy
  | smul l x _ hx => rw [conjVPv_lambda_smul]; exact Submodule.smul_mem _ _ hx

/-- **`conjVP` maps the lattice `Λ · (1 ⊗ T_2E)` of `τ^*V_𝔭(α)` (the lattice of `V_𝔭(α)`) into
the lattice of `V_𝔭(α⁻¹)`.** (tex 2778–2805). Kind: PROVED. -/
theorem conjVP_latt {x : VP K S W P α} (hx : x ∈ latt K S W P α) :
    conjVP C W hW P α x ∈ latt K S W P α⁻¹ :=
  conjVPv_latt C W hW P α hx

/-- `conjVP` maps `2^n latt` into `2^n latt` (tex 4976–5200). Kind: PROVED. -/
theorem conjVP_fibNbhd (n : ℕ) {x : VP K S W P α} (hx : x ∈ fibNbhd K S W P α n) :
    conjVP C W hW P α x ∈ fibNbhd K S W P α⁻¹ n := by
  obtain ⟨y, hy, rfl⟩ := (mem_fibNbhd P).mp hx
  change conjVPv C W hW P α (((2 : Lambda) ^ n) • y) ∈ fibNbhd K S W P α⁻¹ n
  rw [conjVPv_lambda_smul]
  exact two_pow_smul_mem_fibNbhd P (conjVPv_latt C W hW P α hy)

/-- **`conjVP` is continuous** for the lattice topologies (tex 4976–5200). Kind: PROVED. -/
theorem continuous_conjVP : Continuous (conjVP C W hW P α) :=
  continuous_of_hasBasis (M := VP K S W P α) (fun n => (fibNbhd K S W P α n).toAddSubgroup)
    (fun n => (fibNbhd K S W P α⁻¹ n).toAddSubgroup) (fib_hasBasis_nhds_zero P)
    (fib_hasBasis_nhds_zero P) (conjVP C W hW P α).toAddMonoidHom
    (fun n => ⟨n, fun _ hx => conjVP_fibNbhd C W hW P α n hx⟩)

/-! ### The pullback `τ^*V_𝔭(α)` as a coefficient module of the duality interface -/

/-- `Λ → k(𝔭)` is a scalar tower on `τ^*V_𝔭(α)` (tex 4976–5200). Kind: PROVED. -/
instance pullVP_isScalarTower : IsScalarTower Lambda (ResAt P) (PullMod C.conj (VP K S W P α)) :=
  inferInstanceAs (IsScalarTower Lambda (ResAt P) (VP K S W P α))

/-- `τ^*V_𝔭(α)` is a topological group (tex 4976–5200). Kind: PROVED. -/
instance pullVP_isTopologicalAddGroup : IsTopologicalAddGroup (PullMod C.conj (VP K S W P α)) :=
  inferInstanceAs (IsTopologicalAddGroup (VP K S W P α))

/-- The pulled-back Galois action is `k(𝔭)`-linear (tex 2778–2805). Kind: PROVED. -/
instance pullVP_smulCommClass : SMulCommClass (GKS K S) (ResAt P) (PullMod C.conj (VP K S W P α)) :=
  inferInstance

/-- **`τ^*V_𝔭(α)` carries the lattice topology of `V_𝔭(α)`** (the same lattice, stable under
every `c(σ)`; tex 2778–2805). Kind: PROVED. -/
theorem isLatticeTop_pullVP (h : IsLatticeTop (GKS K S) (VP K S W P α)) :
    IsLatticeTop (GKS K S) (PullMod C.conj (VP K S W P α)) :=
  isLatticeTop_pullMod C.conj (VP K S W P α) h

/-- **The hypothesis `α ∘ c = α⁻¹` passes to `α⁻¹`** (tex 2786–2795). Kind: PROVED. -/
theorem inv_conj (hα : ∀ σ, α (C.conj σ) = (α σ)⁻¹) (σ : GKS K S) :
    α⁻¹ (C.conj σ) = (α⁻¹ σ)⁻¹ := by
  rw [MonoidHom.inv_apply, MonoidHom.inv_apply, hα σ]

variable [hPo : IsHeightOneOdd P]

/-- `τ^*V_𝔭(α)` is a topological `k(𝔭)`-vector space (tex 4976–5200). Kind: PROVED. -/
instance pullVP_continuousConstSMul :
    ContinuousConstSMul (ResAt P) (PullMod C.conj (VP K S W P α)) :=
  inferInstanceAs (ContinuousConstSMul (ResAt P) (VP K S W P α))

/-- **The pulled-back Galois action on `τ^*V_𝔭(α)` is continuous** (`c` is continuous;
tex 4976–5200). Kind: PROVED. -/
instance pullVP_continuousSMul [IsContChar α] :
    ContinuousSMul (GKS K S) (PullMod C.conj (VP K S W P α)) :=
  inferInstance

end Fibre

/-! ### The characters -/

section Chars

variable {K : Type} [Field K] [NumberField K] {S : Set (HeightOneSpectrum (𝓞 K))}

/-- **Non-vacuity of `α ∘ c = α⁻¹`** (tex 2786–2795, `α_i^τ = α_i^{-1}`) for `Λ`-characters: the
trivial character satisfies it. (At the finite levels the relation is PROVED for the genuine
`α_i = χ_h Ψ_i` by lane RC28's `alphaChar_conj`.) Kind: PROVED. -/
theorem one_conj (C : ActualConj K S) (σ : GKS K S) :
    (1 : GKS K S →* Lambdaˣ) (C.conj σ) = ((1 : GKS K S →* Lambdaˣ) σ)⁻¹ := by
  rw [MonoidHom.one_apply, MonoidHom.one_apply, inv_one]

/-- **`α⁻¹` is continuous with `α`** (`α⁻¹(σ) = α(σ⁻¹)`), so `V_𝔭(α⁻¹)` carries a continuous
action (tex 4976–5200). Kind: PROVED. -/
instance isContChar_inv (α : GKS K S →* Lambdaˣ) [hα : IsContChar α] : IsContChar α⁻¹ := by
  refine ⟨?_⟩
  have h : (fun σ => ((α⁻¹ σ : Lambdaˣ) : Lambda)) = fun σ => ((α σ⁻¹ : Lambdaˣ) : Lambda) :=
    funext fun σ => by rw [MonoidHom.inv_apply, map_inv]
  rw [h]
  exact hα.continuous_coe.comp continuous_inv

end Chars

end ZInQ.Manuscript.RC.FibreDuality
