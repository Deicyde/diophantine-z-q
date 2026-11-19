import ZInQKernel.Contrib.OneProof.RC.Wiring.CommonCoordinate15Genuine
import ZInQKernel.Contrib.OneProof.RC.CoefModules.Conjugate

/-!
# The stage Frobenius bases and identifications, from the actual coefficient module

Manuscript `diophantine_zq.tex`, Lemma `ex:arith-common-coordinate` (tex 4142–4194): at an unused
split prime `q` with places `w`, `w̄`, the two quotient blocks carry the Frobenius `z Fr_q` and
`z⁻¹ Fr_q` (`δ_q = det(z Fr_q − q) det(z⁻¹ Fr_q − q)`, tex 4176–4184; `z` the scalar Frobenius
value, tex 4144–4145; "Conjugation sends `z` to `z⁻¹`", tex 4171), on the support complexes in
which the old local conditions are retained and the unramified condition `[Φ − 1]` is put at the
new places, the coefficients being unramified there (tex 3470–3498), at a coefficient stage of
the inner limit (tex 4385–4451).

Lane RC32's genuine stage chain (`GenuineStageSteps`) needs, at every stage and every step, the
identifications `f` of the unramified representations with the global coefficient module
(equivariant and bijective) and bases `b₁`, `b₂` of the two places in which the Frobenius is
`z F` and `z⁻¹ F`; lane RC31's `exists_retract_twoPlaces_place_stage` consumes them. This file
produces them from the actual coefficient module.

## (a) The actual coefficient module at a stage, in the tree

* Lane RC28's `CoefMod A α T = (A ⊗_ℤ T)(α)`: `g` acts by `α(g) · (id ⊗ g)` (`CoefMod.smul_def`,
  `CoefMod.act_apply`, `baseChangeAct A T g = id ⊗ g`); `Mcoef K S₀ W i α =
  CoefMod (Acoef i) α (TorsS K S₀ W (2 ^ i))`, i.e. `M_i = (E(K_{S₀})[2^i] ⊗ A_i)(α)`
  (tex 2724–2727); `InflMod hS M₀` (inflation from `G_{K,S₀}` to `G_{K,S}`) and
  `MinS hS W i α = InflMod hS (Mcoef K S₀ W i α)`.
* Lane E2's stage character `alphaStage i s hs hs0 π ψ = χ_h · ψ ∘ π` (into `A_i^×`).
* At a new place `w ∉ S₀` (`newPlace w hw`): `urRep k M₀ w`, the module `M₀` as a representation
  of `Gal(K_w^{ur}/K_w)` through the factorization `urFactor` of the localization, and
  `urId hS k M₀ w = id : urRep k M₀ w → InflMod hS M₀` with `urId_compat` (lanes RC26/RC28, used
  by lane E2's `h20ConditionsPush_actual`). These are exactly the `X` and `f` of the chain: the
  inflation of `M` restricted to the decomposition group.
* The chain's stage ring is `StageRing s = Λ ⧸ stageIdeal s ≃ A_s` (`stageEquiv`); here
  `stageRingChar` carries a character into `A_s^×` to `StageRing s`, and `stageActualMod` is the
  actual module `(StageRing s ⊗ E(K_{S₀})[2^s])(α)` over the stage ring of the chain.

## (b) The inputs (GLUE)

* `urFrobElt K w`: the arithmetic Frobenius at `w`, in `G_{K,S₀}`.
* `FrobMatrixAt eT w F`: in the basis `eT` of `E[2^s] ⊗ A_s` over the stage (free of rank two),
  `id ⊗ Frob_w` has the matrix `F`; `CharValueAt α w z`: `α(Frob_w) = z` (the character line
  `A_s(α)` is free of rank one with basis `1`); `StageFrobInput`: both.
* `AnticyclotomicAt α w₁ w₂`: `α(Frob_{w₂}) = α(Frob_{w₁})⁻¹`.
* `FrobConjugatePlaces S C`: the Frobenius at the conjugate place `κ(w)` is `g c(Frob_w) g⁻¹`,
  with `c` the conjugation by an actual complex conjugation `C`.

Non-vacuity: `stageFrobInput_canonical` (every stage basis satisfies the input for the matrix of
`id ⊗ Frob_w` in it and the value `α(Frob_w)`; the content of the input is that these are the
leaf's `Fr_q` and `z` at the stage).

## (c), (d) What is proved

* `frob_urRep`: the Frobenius of `urRep` is the action of `urFrobElt`; `coefMod_smul_toLin'`: on
  `(k ⊗ T)(α)`, `g` acts by `α(g) F` when `id ⊗ g` has matrix `F`; **`urCoefBasis_frob`**: under
  `StageFrobInput`, the Frobenius of the unramified module is `z F` in the stage basis
  `urCoefBasis` (the identity basis of `(k ⊗ T)(α)`); `urId_bijective`.
* `charValueAt_of_anticyclotomic`: the value `zi = z⁻¹` at `w₂` from `AnticyclotomicAt`;
  `anticyclotomicAt_of_conj`: `AnticyclotomicAt` from `FrobConjugatePlaces` and `α ∘ c = α⁻¹`
  (lane RC28's `alphaChar_conj` for the actual character); `conjStageBasis`,
  **`frobMatrixAt_conj`**: the stage basis at `w₂` with the same matrix `F`, transported from the
  one at `w₁` along `t ↦ ρ_T(τ)(g⁻¹ t)` (lane RC28's `conjTors`).
* **`StageStepFrob`**, **`StageChainFrob`**: exactly the fields `f`, `hf`, `hbij`, `b₁`, `hb₁`,
  `b₂`, `hb₂` of `GenuineStageSteps` (for one step, resp. all steps of a chain), and
  **`GenuineStageSteps.ofFrob`**: the chain's data from them and the other fields.
* **`stageStepFrob_of_inputs`**, `stageStepFrob_of_anticyclotomic`, **`stageStepFrob_of_conj`**,
  `nonempty_stageStepFrob_of_conj`, and the chain versions `stageChainFrob_of_inputs`,
  `stageChainFrob_of_conj`, `nonempty_stageChainFrob_of_conj`: the fields from the inputs, with
  `X j = urRep` and `f j = urId` at the places of the chain.
* `nonempty_stageChainFrob_E2` (lane E2's `Mcoef`, `MinS` over `A_i`) and
  `nonempty_stageChainFrob_stage` (`stageActualMod` over `StageRing s`): the actual instances;
  `urChainRep_continuousSMul`, `inflMod_coefMod_free`, `inflMod_finite`,
  `exists_two_pow_smul_inflMod`: the instance inputs and the field `hexp` of the chain.

Not done here: the GLUE inputs themselves (the comparison of the leaf's `Fr_q` and `z` at the
stage with the Galois action on the actual `E(K_{S₀})[2^s]` and with the character, and
`FrobConjugatePlaces`).

Kinds: definitions, PROVED, and GLUE (the input statements).
-/

noncomputable section

namespace ZInQ.Manuscript.RC.Wiring

open NumberField IsDedekindDomain TensorProduct
open ZInQ.Manuscript.RC.SelmerComplex ZInQ.Manuscript.RC.CoefModules
open ZInQ.Contrib.CloudB3RC53.UnramifiedComplex
open ZInQ.Contrib.CloudB3RC53.RankCounts (GUr)
open ZInQ.Contrib.CloudB3RC53.Duality (baseChangeAct baseChangeAct_tmul)
open ZInQ.Manuscript.RC.HeegnerAlgebra (Acoef)

attribute [local instance] TopRep.distribMulAction

/-! ### The action on `(k ⊗ T)(α)` in a basis, and transport along an intertwiner -/

section CoefBasis

variable {G : Type} [Group G] {k : Type} [CommRing k] {T : Type} [AddCommGroup T]
  [DistribMulAction G T]

/-- **The action on `(k ⊗ T)(α)` in a basis** (tex 2724–2727, 4176–4184): if `id ⊗ g` has the
matrix `F` in a basis `e` of `k ⊗ T`, then `g` acts on `(k ⊗ T)(α)` by `α(g) F`.
Kind: PROVED. -/
theorem coefMod_smul_toLin' (α : G →* kˣ) (e : k ⊗[ℤ] T ≃ₗ[k] (Fin 2 → k)) (g : G)
    (F : Matrix (Fin 2) (Fin 2) k)
    (hF : ∀ x, e (baseChangeAct k T g x) = Matrix.toLin' F (e x)) (x : CoefMod k α T) :
    e (g • x) = Matrix.toLin' (((α g : kˣ) : k) • F) (e x) := by
  rw [CoefMod.smul_def, CoefMod.act_apply, map_smul, map_smul, LinearMap.smul_apply]
  exact congrArg (((α g : kˣ) : k) • ·) (hF x)

/-- **`id ⊗ ψ` intertwines `id ⊗ σ₂` with `id ⊗ σ₁`** when `ψ (σ₂ t) = σ₁ (ψ t)` (tex 2778,
4176–4184). Kind: PROVED. -/
theorem baseChangeAct_transport (σ₁ σ₂ : G) (ψ : T ≃+ T) (hψ : ∀ t, ψ (σ₂ • t) = σ₁ • ψ t)
    (x : k ⊗[ℤ] T) :
    LinearEquiv.baseChange ℤ k T T ψ.toIntLinearEquiv (baseChangeAct k T σ₂ x) =
      baseChangeAct k T σ₁ (LinearEquiv.baseChange ℤ k T T ψ.toIntLinearEquiv x) := by
  induction x using TensorProduct.inductionOn with
  | tmul a t =>
    rw [baseChangeAct_tmul, LinearEquiv.baseChange_tmul, LinearEquiv.baseChange_tmul,
      baseChangeAct_tmul]
    exact congrArg (a ⊗ₜ[ℤ] ·) (hψ t)
  | add x y hx hy => rw [map_add, map_add, hx, hy, map_add, map_add]

/-- **Transport of a Frobenius basis along an intertwiner** (tex 2778, 4176–4184): if `id ⊗ σ₁`
has the matrix `F` in the basis `e` and `ψ (σ₂ t) = σ₁ (ψ t)`, then `id ⊗ σ₂` has the matrix `F`
in the basis `e ∘ (id ⊗ ψ)`. Kind: PROVED. -/
theorem toLin'_transport (e : k ⊗[ℤ] T ≃ₗ[k] (Fin 2 → k)) (σ₁ σ₂ : G) (ψ : T ≃+ T)
    (hψ : ∀ t, ψ (σ₂ • t) = σ₁ • ψ t) (F : Matrix (Fin 2) (Fin 2) k)
    (hF : ∀ x, e (baseChangeAct k T σ₁ x) = Matrix.toLin' F (e x)) (x : k ⊗[ℤ] T) :
    ((LinearEquiv.baseChange ℤ k T T ψ.toIntLinearEquiv).trans e) (baseChangeAct k T σ₂ x) =
      Matrix.toLin' F (((LinearEquiv.baseChange ℤ k T T ψ.toIntLinearEquiv).trans e) x) := by
  rw [LinearEquiv.trans_apply, LinearEquiv.trans_apply, baseChangeAct_transport σ₁ σ₂ ψ hψ, hF]

end CoefBasis

/-! ### (a) The arithmetic Frobenius at a new place and the unramified module -/

section Frob

variable (K : Type) [Field K] [NumberField K] {S₀ S : Set (HeightOneSpectrum (𝓞 K))}

/-- **The arithmetic Frobenius at a new place `w ∉ S₀`, in `G_{K,S₀}`** (tex 3478–3487, 4145):
the image of the arithmetic Frobenius `frobElt (eUr K w)` of `Gal(K_w^{ur}/K_w)` under the
factorization `urFactor` of the localization `G_{K_w} → G_{K,S₀}` through the unramified quotient.
Kind: definition. -/
abbrev urFrobElt (w : NewPlaces K S₀ S) : GKS K S₀ := urFactor K w (frobElt (eUr K w.1))

variable {K} (k : Type) [CommRing k] [TopologicalSpace k] [DiscreteTopology k]
  (M₀ : Type) [AddCommGroup M₀] [Module k M₀] [DistribMulAction (GKS K S₀) M₀]
  [SMulCommClass (GKS K S₀) k M₀] [TopologicalSpace M₀] [DiscreteTopology M₀]

/-- **The Frobenius of the unramified module `urRep` is the action of `urFrobElt`**
(tex 3478–3487): `Φ_w x = Frob_w • x` on `M₀`. Kind: PROVED. -/
theorem frob_urRep (w : NewPlaces K S₀ S) (x : (urRep k M₀ w).V) :
    frob (eUr K w.1) (urRep k M₀ w) x = (show M₀ from urFrobElt K w • (show M₀ from x)) := rfl

/-- **The identification `urId` is bijective** (tex 3470–3498: it is the identity of `M₀`).
Kind: PROVED. -/
theorem urId_bijective (hS : S₀ ⊆ S) (w : NewPlaces K S₀ S) :
    Function.Bijective (urId hS k M₀ w) :=
  ⟨fun _ _ h => h, fun y => ⟨y, rfl⟩⟩

end Frob

/-! ### (b) The arithmetic inputs -/

section Input

variable {K : Type} [Field K] [NumberField K] {S₀ S : Set (HeightOneSpectrum (𝓞 K))}
  {k : Type} [CommRing k] {T : Type} [AddCommGroup T] [DistribMulAction (GKS K S₀) T]

/-- **GLUE input: the Frobenius matrix of `E[2^s]` at `w` in a stage basis** (tex 4144–4145,
4176–4184, 4209–4213): in the basis `eT` of `E[2^s] ⊗ A_s` over the stage `A_s` (free of rank
two; `T = E(K_{S₀})[2^s]` for the actual module), `id ⊗ Frob_w` has the matrix `F`. For the leaf,
`F` is the image at the stage of the Frobenius matrix `frobMat C q` of `E` at `q`
(`leafFrobΛ`, `StageFrobAt`), so the content is the comparison of `ρ_T(Fr_q)` on `T₂E` with the
Galois action on the actual torsion `E(K_{S₀})[2^s]`. Kind: GLUE. -/
def FrobMatrixAt (eT : k ⊗[ℤ] T ≃ₗ[k] (Fin 2 → k)) (w : NewPlaces K S₀ S)
    (F : Matrix (Fin 2) (Fin 2) k) : Prop :=
  ∀ x, eT (baseChangeAct k T (urFrobElt K w) x) = Matrix.toLin' F (eT x)

/-- **GLUE input: the character value at the Frobenius of `w`** (tex 4144–4145, 2724–2727):
`α(Frob_w) = z` in the stage ring. The character line `A_s(α)` is free of rank one with basis
`1`, on which `Frob_w` acts by `α(Frob_w)`. For the leaf, `z` is the image at the stage of the
scalar Frobenius value `zAt` (`leafFrobΛ`, `StageFrobAt`). Kind: GLUE. -/
def CharValueAt (α : GKS K S₀ →* kˣ) (w : NewPlaces K S₀ S) (z : k) : Prop :=
  ((α (urFrobElt K w) : kˣ) : k) = z

/-- **The arithmetic input at one place** (tex 4144–4145, 4176–4184): the Frobenius of `E[2^s]`
at `w` has the matrix `F` in the stage basis `eT`, and the character takes the value `z` at it;
so the Frobenius of `M = (A_s ⊗ E[2^s])(α)` at `w` is `z F` (`urCoefBasis_frob`).
Kind: GLUE. -/
structure StageFrobInput (eT : k ⊗[ℤ] T ≃ₗ[k] (Fin 2 → k)) (α : GKS K S₀ →* kˣ)
    (w : NewPlaces K S₀ S) (F : Matrix (Fin 2) (Fin 2) k) (z : k) : Prop where
  /-- the Frobenius matrix of `E[2^s]` at `w` in the stage basis -/
  frobMatrix : FrobMatrixAt eT w F
  /-- the value of the character at the Frobenius of `w` -/
  charValue : CharValueAt α w z

/-- **Non-vacuity of `FrobMatrixAt`** (tex 4176–4184): every stage basis satisfies it for the
matrix of `id ⊗ Frob_w` in that basis. Kind: PROVED. -/
theorem frobMatrixAt_canonical (eT : k ⊗[ℤ] T ≃ₗ[k] (Fin 2 → k)) (w : NewPlaces K S₀ S) :
    FrobMatrixAt eT w (LinearMap.toMatrix' (eT.toLinearMap ∘ₗ
      baseChangeAct k T (urFrobElt K w) ∘ₗ eT.symm.toLinearMap)) := fun x => by
  rw [Matrix.toLin'_toMatrix', LinearMap.comp_apply, LinearMap.comp_apply,
    LinearEquiv.coe_coe, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply]

/-- **Non-vacuity of `StageFrobInput`** (tex 4144–4145, 4176–4184): every stage basis satisfies
it for the matrix of `id ⊗ Frob_w` in that basis and the value `α(Frob_w)`; the content of the
input for the leaf is that these are the leaf's `Fr_q` and `z` at the stage. Kind: PROVED. -/
theorem stageFrobInput_canonical (eT : k ⊗[ℤ] T ≃ₗ[k] (Fin 2 → k)) (α : GKS K S₀ →* kˣ)
    (w : NewPlaces K S₀ S) :
    StageFrobInput eT α w (LinearMap.toMatrix' (eT.toLinearMap ∘ₗ
      baseChangeAct k T (urFrobElt K w) ∘ₗ eT.symm.toLinearMap)) (α (urFrobElt K w) : k) :=
  ⟨frobMatrixAt_canonical eT w, rfl⟩

/-- **GLUE input: the character is anticyclotomic at a split prime** (tex 2778–2796, 4171,
4176–4184): at the Frobenius elements of the two places `w₁`, `w₂ = w̄₁` above an unused split
prime the character takes inverse values, `α(Frob_{w₂}) = α(Frob_{w₁})⁻¹` (`α^τ = α⁻¹`, so
"conjugation sends `z` to `z⁻¹`"). Derived from `FrobConjugatePlaces` in
`anticyclotomicAt_of_conj`. Kind: GLUE. -/
def AnticyclotomicAt (α : GKS K S₀ →* kˣ) (w₁ w₂ : NewPlaces K S₀ S) : Prop :=
  α (urFrobElt K w₂) = (α (urFrobElt K w₁))⁻¹

/-- **The value at the second place is the inverse point** (tex 4171, 4176–4184): from
`α(Frob_{w₁}) = z`, `z zi = 1` and `AnticyclotomicAt`, `α(Frob_{w₂}) = zi`. Kind: PROVED. -/
theorem charValueAt_of_anticyclotomic {α : GKS K S₀ →* kˣ} {w₁ w₂ : NewPlaces K S₀ S}
    {z zi : k} (h₁ : CharValueAt α w₁ z) (hzi : z * zi = 1) (hanti : AnticyclotomicAt α w₁ w₂) :
    CharValueAt α w₂ zi := by
  unfold CharValueAt at *
  rw [hanti]
  exact Units.inv_eq_of_mul_eq_one_right (by rw [h₁]; exact hzi)

variable (S) in
/-- **GLUE input: the Frobenius at the conjugate place** (tex 2778, 4171, 4176–4184): for new
places `w`, `w'` with `w' = κ(w)` (`conjPlace`, `κ = τ|_K` for the actual complex conjugation
`C`), `Frob_{w'} = g c(Frob_w) g⁻¹` for some `g ∈ G_{K,S₀}`, `c = C.conj`. Standard: `τ` carries
the Frobenius at a prime `𝔓` of `K_{S₀}` above `w` to the Frobenius at `τ𝔓`, a prime above
`κ(w)`, and `G_{K,S₀}` permutes the primes above `κ(w) ∉ S₀` transitively. Kind: GLUE. -/
def FrobConjugatePlaces (C : ActualConj K S₀) : Prop :=
  ∀ w w' : NewPlaces K S₀ S, w'.1 = conjPlace C.κ w.1 →
    ∃ g : GKS K S₀, urFrobElt K w' = g * C.conj (urFrobElt K w) * g⁻¹

/-- **Anticyclotomy at a split prime from the conjugate Frobenius** (tex 2778–2796, 4171): if
`Frob_{w₂} = g c(Frob_{w₁}) g⁻¹` and `α ∘ c = α⁻¹` (lane RC28's `alphaChar_conj` for the actual
character), then `α(Frob_{w₂}) = α(Frob_{w₁})⁻¹`. Kind: PROVED. -/
theorem anticyclotomicAt_of_conj (C : ActualConj K S₀) {α : GKS K S₀ →* kˣ}
    (hα : ∀ σ, α (C.conj σ) = (α σ)⁻¹) {w₁ w₂ : NewPlaces K S₀ S} {g : GKS K S₀}
    (hg : urFrobElt K w₂ = g * C.conj (urFrobElt K w₁) * g⁻¹) : AnticyclotomicAt α w₁ w₂ := by
  unfold AnticyclotomicAt
  rw [hg, map_mul, map_mul, map_inv, hα, mul_inv_cancel_comm]

end Input

/-! ### (c) The stage basis at the conjugate place -/

section Conj

variable {K : Type} [Field K] [NumberField K] {S₀ : Set (HeightOneSpectrum (𝓞 K))}
  (C : ActualConj K S₀) (W : WeierstrassCurve K) (hW : W.map (C.κ : K →+* K) = W) (N : ℤ)

/-- **The intertwiner `t ↦ ρ_T(τ)(g⁻¹ t)` of `E(K_{S₀})[N]`** (tex 2778–2796), with inverse
`t ↦ g ρ_T(τ) t` (lane RC28's `conjTors`, an involution). Kind: definition. -/
def conjFrobEquiv (g : GKS K S₀) : TorsS K S₀ W N ≃+ TorsS K S₀ W N where
  toFun t := conjTors C W hW N (g⁻¹ • t)
  invFun t := g • conjTors C W hW N t
  left_inv t := by
    change g • conjTors C W hW N (conjTors C W hW N (g⁻¹ • t)) = t
    rw [conjTors_conjTors, smul_inv_smul]
  right_inv t := by
    change conjTors C W hW N (g⁻¹ • g • conjTors C W hW N t) = t
    rw [inv_smul_smul, conjTors_conjTors]
  map_add' s t := by
    rw [smul_add, map_add]

/-- **The intertwining identity** (tex 2778–2796): `ψ_g((g c(σ) g⁻¹) t) = σ ψ_g(t)`, by
`ρ_T(τ)(σ P) = c(σ) ρ_T(τ) P` (`conjTors_smul`) and `c² = 1`. Kind: PROVED. -/
theorem conjFrobEquiv_smul (g σ : GKS K S₀) (t : TorsS K S₀ W N) :
    conjFrobEquiv C W hW N g ((g * C.conj σ * g⁻¹) • t) = σ • conjFrobEquiv C W hW N g t := by
  change conjTors C W hW N (g⁻¹ • (g * C.conj σ * g⁻¹) • t) = σ • conjTors C W hW N (g⁻¹ • t)
  rw [smul_smul, ← mul_assoc, ← mul_assoc, inv_mul_cancel, one_mul, mul_smul, conjTors_smul,
    C.conj_conj]

variable {k : Type} [CommRing k]

/-- **The stage basis at the conjugate place** (tex 2778–2796, 4176–4184): `eT ∘ (id ⊗ ψ_g)`.
Kind: definition. -/
def conjStageBasis (g : GKS K S₀) (eT : k ⊗[ℤ] TorsS K S₀ W N ≃ₗ[k] (Fin 2 → k)) :
    k ⊗[ℤ] TorsS K S₀ W N ≃ₗ[k] (Fin 2 → k) :=
  (LinearEquiv.baseChange ℤ k _ _ (conjFrobEquiv C W hW N g).toIntLinearEquiv).trans eT

/-- **The same Frobenius matrix at the conjugate place** (tex 4176–4184: the blocks at `w` and
`w̄` share `Fr_q`): if `Frob_{w₂} = g c(Frob_{w₁}) g⁻¹` and `id ⊗ Frob_{w₁}` has the matrix `F`
in `eT`, then `id ⊗ Frob_{w₂}` has the matrix `F` in `conjStageBasis C W hW N g eT`.
Kind: PROVED. -/
theorem frobMatrixAt_conj {S : Set (HeightOneSpectrum (𝓞 K))}
    {eT : k ⊗[ℤ] TorsS K S₀ W N ≃ₗ[k] (Fin 2 → k)} {w₁ w₂ : NewPlaces K S₀ S}
    {F : Matrix (Fin 2) (Fin 2) k} {g : GKS K S₀}
    (hg : urFrobElt K w₂ = g * C.conj (urFrobElt K w₁) * g⁻¹) (h₁ : FrobMatrixAt eT w₁ F) :
    FrobMatrixAt (conjStageBasis C W hW N g eT) w₂ F := fun x => by
  have h := toLin'_transport eT (urFrobElt K w₁) _ (conjFrobEquiv C W hW N g)
    (conjFrobEquiv_smul C W hW N g (urFrobElt K w₁)) F h₁ x
  rw [← hg] at h
  exact h

end Conj

/-! ### (c) The stage basis of the unramified module -/

section UrBasis

variable {K : Type} [Field K] [NumberField K] {S₀ S : Set (HeightOneSpectrum (𝓞 K))}
  {k : Type} [CommRing k] [TopologicalSpace k] [DiscreteTopology k] {T : Type} [AddCommGroup T]
  [DistribMulAction (GKS K S₀) T] (α : GKS K S₀ →* kˣ)

/-- **The stage basis of the unramified module** (tex 4176–4184): the stage basis `eT` of
`k ⊗ T`, read on `(urRep k (CoefMod k α T) w).V`, which is `(k ⊗ T)(α)` itself.
Kind: definition. -/
def urCoefBasis (eT : k ⊗[ℤ] T ≃ₗ[k] (Fin 2 → k)) (w : NewPlaces K S₀ S) :
    (urRep k (CoefMod k α T) w).V ≃ₗ[k] (Fin 2 → k) :=
  eT

/-- **The Frobenius of the unramified module is `z F` in the stage basis** (tex 4176–4184,
3478–3487): under `StageFrobInput eT α w F z`. Kind: PROVED. -/
theorem urCoefBasis_frob {eT : k ⊗[ℤ] T ≃ₗ[k] (Fin 2 → k)} {w : NewPlaces K S₀ S}
    {F : Matrix (Fin 2) (Fin 2) k} {z : k} (h : StageFrobInput eT α w F z)
    (v : (urRep k (CoefMod k α T) w).V) :
    urCoefBasis α eT w (frob (eUr K w.1) (urRep k (CoefMod k α T) w) v) =
      Matrix.toLin' (z • F) (urCoefBasis α eT w v) := by
  rw [← h.charValue]
  exact coefMod_smul_toLin' α eT (urFrobElt K w) F h.frobMatrix v

end UrBasis

/-! ### (d) The Frobenius fields of the genuine stage chain -/

section Fields

variable (k : Type) [CommRing k] [TopologicalSpace k] {K : Type} [Field K] [NumberField K]
  {S : Set (HeightOneSpectrum (𝓞 K))} (M : Type) [AddCommGroup M] [Module k M]
  [DistribMulAction (GKS K S) M] {ι : Type} (place : ι × Bool → Places K S)
  (X : (j : ι × Bool) → TopRep.{0} k (GUr K (place j).1))

/-- **The Frobenius fields of the genuine stage chain at one step** (tex 4176–4184,
3470–3498): exactly the fields `f`, `hf`, `hbij`, `b₁`, `hb₁`, `b₂`, `hb₂` of
`GenuineStageSteps`, at one stage `k` and one step: the places `place (p, false)`,
`place (p, true)` of the unused split prime `p`, the Frobenius matrix `F`, the point `z` and
the inverse point `zi` (data). Kind: definition. -/
structure StageStepFrob (p : ι) (F : Matrix (Fin 2) (Fin 2) k) (z zi : k) : Type where
  /-- the identifications of the unramified representations with `M` -/
  f : ∀ j, (X j).V →ₗ[k] M
  /-- their equivariance -/
  hf : ∀ j (g : Gloc K (place j).1) (v : (X j).V),
    f j (resUr K (place j).1 g • v) = locMap K S (place j).1 g • f j v
  /-- they are bijective -/
  hbij : ∀ j, Function.Bijective (f j)
  /-- the basis at the first place -/
  b₁ : (X (p, false)).V ≃ₗ[k] (Fin 2 → k)
  /-- the Frobenius is `z F` at the first place -/
  hb₁ : ∀ v, b₁ (frob (eUr K (place (p, false)).1) (X (p, false)) v) =
    Matrix.toLin' (z • F) (b₁ v)
  /-- the basis at the second place -/
  b₂ : (X (p, true)).V ≃ₗ[k] (Fin 2 → k)
  /-- the Frobenius is `z⁻¹ F` at the second place -/
  hb₂ : ∀ v, b₂ (frob (eUr K (place (p, true)).1) (X (p, true)) v) =
    Matrix.toLin' (zi • F) (b₂ v)

/-- **The Frobenius fields of the genuine stage chain at all steps** (tex 4176–4184,
3470–3498): exactly the fields `f`, `hf`, `hbij`, `b₁`, `hb₁`, `b₂`, `hb₂` of
`GenuineStageSteps` at one stage `k`, for the steps `i < n` relaxing `pidx i` with Frobenius
matrices `Fr i`, points `z i` and inverse points `zi i` (data). Kind: definition. -/
structure StageChainFrob (pidx : ℕ → ι) (n : ℕ) (Fr : ℕ → Matrix (Fin 2) (Fin 2) k)
    (z zi : ℕ → k) : Type where
  /-- the identifications of the unramified representations with `M` -/
  f : ∀ j, (X j).V →ₗ[k] M
  /-- their equivariance -/
  hf : ∀ j (g : Gloc K (place j).1) (v : (X j).V),
    f j (resUr K (place j).1 g • v) = locMap K S (place j).1 g • f j v
  /-- they are bijective -/
  hbij : ∀ j, Function.Bijective (f j)
  /-- the bases at the first places -/
  b₁ : ∀ i, (X (pidx i, false)).V ≃ₗ[k] (Fin 2 → k)
  /-- the Frobenius is `z F` at the first places -/
  hb₁ : ∀ i < n, ∀ v, b₁ i (frob (eUr K (place (pidx i, false)).1) (X (pidx i, false)) v) =
    Matrix.toLin' (z i • Fr i) (b₁ i v)
  /-- the bases at the second places -/
  b₂ : ∀ i, (X (pidx i, true)).V ≃ₗ[k] (Fin 2 → k)
  /-- the Frobenius is `z⁻¹ F` at the second places -/
  hb₂ : ∀ i < n, ∀ v, b₂ i (frob (eUr K (place (pidx i, true)).1) (X (pidx i, true)) v) =
    Matrix.toLin' (zi i • Fr i) (b₂ i v)

end Fields

/-! ### The actual module is free over the stage -/

section Free

variable {K : Type} [Field K] [NumberField K] {S₀ S : Set (HeightOneSpectrum (𝓞 K))}
  (hS : S₀ ⊆ S) {k : Type} [CommRing k] {T : Type} [AddCommGroup T]

/-- **The actual module is free over the stage** (tex 2724–2727): a stage basis of `k ⊗ T`
makes `InflMod hS (CoefMod k α T)` free, the instance input `Module.Free` of the chain.
Kind: PROVED. -/
theorem inflMod_coefMod_free {G : Type} [Group G] (α : G →* kˣ)
    (eT : k ⊗[ℤ] T ≃ₗ[k] (Fin 2 → k)) : Module.Free k (InflMod hS (CoefMod k α T)) :=
  Module.Free.of_equiv (show (Fin 2 → k) ≃ₗ[k] InflMod hS (CoefMod k α T) from eT.symm)

/-- **The inflated module is finite** (tex 2724–2727): the instance input `Finite` of the chain.
Kind: PROVED. -/
theorem inflMod_finite (M₀ : Type) [Finite M₀] : Finite (InflMod hS M₀) :=
  inferInstanceAs (Finite M₀)

/-- **The actual module has `2`-power exponent** (tex 2724–2727): `2^s` kills
`InflMod hS (CoefMod k α E(K_{S₀})[2^s])`, the field `hexp` of `GenuineStageSteps`.
Kind: PROVED. -/
theorem exists_two_pow_smul_inflMod (W : WeierstrassCurve K) (s : ℕ) {G : Type} [Group G]
    (α : G →* kˣ) :
    ∃ e : ℕ, ∀ m : InflMod hS (CoefMod k α (TorsS K S₀ W ((2 ^ s : ℕ) : ℤ))),
      (2 ^ e) • m = 0 := by
  have hT : ∀ t : TorsS K S₀ W ((2 ^ s : ℕ) : ℤ), (2 ^ s : ℕ) • t = 0 := fun t =>
    Subtype.ext (AddSubgroup.torsionBy.nsmul_iff.1 t.2)
  have hkill : ∀ x : k ⊗[ℤ] TorsS K S₀ W ((2 ^ s : ℕ) : ℤ), (2 ^ s : ℕ) • x = 0 := by
    intro x
    induction x using TensorProduct.inductionOn with
    | tmul a t => rw [← TensorProduct.tmul_smul, hT, TensorProduct.tmul_zero]
    | add x y hx hy => rw [smul_add, hx, hy, add_zero]
  exact ⟨s, fun m => hkill m⟩

end Free

/-! ### (d) The fields from the inputs -/

section Build

variable {K : Type} [Field K] [NumberField K] {S₀ S : Set (HeightOneSpectrum (𝓞 K))}
  (hS : S₀ ⊆ S) {k : Type} [CommRing k] [TopologicalSpace k] [DiscreteTopology k]
  {ι : Type} (place : ι × Bool → Places K S) (hw : ∀ j, (place j).1 ∉ S₀)

/-- **The unramified modules of the chain** (tex 3470–3498): at every place `place j ∉ S₀` of
the chain, the module `M₀` as a representation of `Gal(K_w^{ur}/K_w)` (lane RC28's `urRep`).
Kind: definition. -/
abbrev urChainRep (M₀ : Type) [AddCommGroup M₀] [Module k M₀] [DistribMulAction (GKS K S₀) M₀]
    [SMulCommClass (GKS K S₀) k M₀] [TopologicalSpace M₀] [DiscreteTopology M₀]
    (j : ι × Bool) : TopRep.{0} k (GUr K (place j).1) :=
  urRep k M₀ (newPlace (place j) (hw j))

/-- **The unramified modules of the chain are discrete `Gal(K_w^{ur}/K_w)`-modules**
(tex 3470–3498; lane RC28's `urRep_continuousSMul`): the instance input of the chain.
Kind: PROVED. -/
theorem urChainRep_continuousSMul (M₀ : Type) [AddCommGroup M₀] [Module k M₀]
    [DistribMulAction (GKS K S₀) M₀] [SMulCommClass (GKS K S₀) k M₀] [TopologicalSpace M₀]
    [DiscreteTopology M₀] [ContinuousSMul (GKS K S₀) M₀] [Finite M₀] (j : ι × Bool) :
    ContinuousSMul (GUr K (place j).1) (urChainRep (k := k) place hw M₀ j).V :=
  urRep_continuousSMul k M₀ (newPlace (place j) (hw j))

variable {T : Type} [AddCommGroup T] [DistribMulAction (GKS K S₀) T] (α : GKS K S₀ →* kˣ)

variable [ContinuousSMul (GKS K S₀) (CoefMod k α T)] [Finite (CoefMod k α T)]

/-- **The Frobenius fields at one step from the inputs** (tex 4176–4184, 3470–3498): for the
actual module `M = InflMod hS (CoefMod k α T)` and the unramified modules `urChainRep` at the
places of the chain (all outside `S₀`), the identifications `f j = urId` (equivariant by
`urId_compat`, bijective), and the stage bases `urCoefBasis` at the two places, in which the
Frobenius is `z F` and `zi F` by `StageFrobInput` at each place. Kind: definition. -/
def stageStepFrob_of_inputs (p : ι) (F : Matrix (Fin 2) (Fin 2) k) (z zi : k)
    (e₁ e₂ : k ⊗[ℤ] T ≃ₗ[k] (Fin 2 → k))
    (h₁ : StageFrobInput e₁ α (newPlace (place (p, false)) (hw (p, false))) F z)
    (h₂ : StageFrobInput e₂ α (newPlace (place (p, true)) (hw (p, true))) F zi) :
    StageStepFrob k (InflMod hS (CoefMod k α T)) place
      (urChainRep place hw (CoefMod k α T)) p F z zi where
  f j := urId hS k (CoefMod k α T) (newPlace (place j) (hw j))
  hf j := urId_compat hS k (CoefMod k α T) (place j) (hw j)
  hbij j := urId_bijective k (CoefMod k α T) hS (newPlace (place j) (hw j))
  b₁ := urCoefBasis α e₁ (newPlace (place (p, false)) (hw (p, false)))
  hb₁ := urCoefBasis_frob α h₁
  b₂ := urCoefBasis α e₂ (newPlace (place (p, true)) (hw (p, true)))
  hb₂ := urCoefBasis_frob α h₂

/-- **The Frobenius fields at one step from the anticyclotomic input** (tex 4171, 4176–4184):
as `stageStepFrob_of_inputs`, with the value `zi` at the second place derived from `z zi = 1`
and `AnticyclotomicAt` (`charValueAt_of_anticyclotomic`). Kind: definition. -/
def stageStepFrob_of_anticyclotomic (p : ι) (F : Matrix (Fin 2) (Fin 2) k) (z zi : k)
    (e₁ e₂ : k ⊗[ℤ] T ≃ₗ[k] (Fin 2 → k))
    (h₁ : StageFrobInput e₁ α (newPlace (place (p, false)) (hw (p, false))) F z)
    (h₂ : FrobMatrixAt e₂ (newPlace (place (p, true)) (hw (p, true))) F) (hzi : z * zi = 1)
    (hanti : AnticyclotomicAt α (newPlace (place (p, false)) (hw (p, false)))
      (newPlace (place (p, true)) (hw (p, true)))) :
    StageStepFrob k (InflMod hS (CoefMod k α T)) place
      (urChainRep place hw (CoefMod k α T)) p F z zi :=
  stageStepFrob_of_inputs hS place hw α p F z zi e₁ e₂ h₁
    ⟨h₂, charValueAt_of_anticyclotomic h₁.charValue hzi hanti⟩

/-- **The Frobenius fields of a chain from the inputs** (tex 4176–4184, 3470–3498): the chain
version of `stageStepFrob_of_inputs`, with stage bases `e₁ i`, `e₂ i` at the places of the step
`i < n`. Kind: definition. -/
def stageChainFrob_of_inputs (pidx : ℕ → ι) (n : ℕ) (Fr : ℕ → Matrix (Fin 2) (Fin 2) k)
    (z zi : ℕ → k) (e₁ e₂ : ℕ → k ⊗[ℤ] T ≃ₗ[k] (Fin 2 → k))
    (h₁ : ∀ i < n, StageFrobInput (e₁ i) α (newPlace (place (pidx i, false))
      (hw (pidx i, false))) (Fr i) (z i))
    (h₂ : ∀ i < n, StageFrobInput (e₂ i) α (newPlace (place (pidx i, true))
      (hw (pidx i, true))) (Fr i) (zi i)) :
    StageChainFrob k (InflMod hS (CoefMod k α T)) place
      (urChainRep place hw (CoefMod k α T)) pidx n Fr z zi where
  f j := urId hS k (CoefMod k α T) (newPlace (place j) (hw j))
  hf j := urId_compat hS k (CoefMod k α T) (place j) (hw j)
  hbij j := urId_bijective k (CoefMod k α T) hS (newPlace (place j) (hw j))
  b₁ i := urCoefBasis α (e₁ i) (newPlace (place (pidx i, false)) (hw (pidx i, false)))
  hb₁ i hi := urCoefBasis_frob α (h₁ i hi)
  b₂ i := urCoefBasis α (e₂ i) (newPlace (place (pidx i, true)) (hw (pidx i, true)))
  hb₂ i hi := urCoefBasis_frob α (h₂ i hi)

end Build

/-! ### (d) The fields from the conjugate Frobenius -/

section BuildConj

variable {K : Type} [Field K] [NumberField K] {S₀ S : Set (HeightOneSpectrum (𝓞 K))}
  (hS : S₀ ⊆ S) {k : Type} [CommRing k] [TopologicalSpace k] [DiscreteTopology k]
  {ι : Type} (place : ι × Bool → Places K S) (hw : ∀ j, (place j).1 ∉ S₀)
  (C : ActualConj K S₀) (W : WeierstrassCurve K) (hW : W.map (C.κ : K →+* K) = W) (N : ℤ)
  (α : GKS K S₀ →* kˣ) [ContinuousSMul (GKS K S₀) (CoefMod k α (TorsS K S₀ W N))]
  [Finite (CoefMod k α (TorsS K S₀ W N))] (hα : ∀ σ, α (C.conj σ) = (α σ)⁻¹)

include hα in
/-- **The Frobenius fields at one step from the conjugate Frobenius** (tex 2778–2796, 4171,
4176–4184): for `T = E(K_{S₀})[N]` with `E` defined over the fixed field of `κ` (`hW`) and an
anticyclotomic character (`hα`), the input at the first place and `Frob_{w₂} = g c(Frob_{w₁})
g⁻¹` give the fields: the basis at the second place is `conjStageBasis` (`frobMatrixAt_conj`),
the value there is `zi` (`anticyclotomicAt_of_conj`). Kind: definition. -/
def stageStepFrob_of_conj (p : ι) (F : Matrix (Fin 2) (Fin 2) k) (z zi : k)
    (eT : k ⊗[ℤ] TorsS K S₀ W N ≃ₗ[k] (Fin 2 → k))
    (h₁ : StageFrobInput eT α (newPlace (place (p, false)) (hw (p, false))) F z)
    (hzi : z * zi = 1) (g : GKS K S₀)
    (hg : urFrobElt K (newPlace (place (p, true)) (hw (p, true))) =
      g * C.conj (urFrobElt K (newPlace (place (p, false)) (hw (p, false)))) * g⁻¹) :
    StageStepFrob k (InflMod hS (CoefMod k α (TorsS K S₀ W N))) place
      (urChainRep place hw (CoefMod k α (TorsS K S₀ W N))) p F z zi :=
  stageStepFrob_of_anticyclotomic hS place hw α p F z zi eT (conjStageBasis C W hW N g eT) h₁
    (frobMatrixAt_conj C W hW N hg h₁.frobMatrix) hzi (anticyclotomicAt_of_conj C hα hg)

include hW hα in
/-- **The Frobenius fields at one step exist from the GLUE inputs** (tex 2778–2796, 4171,
4176–4184): `FrobConjugatePlaces` at the two places of `p` (`place (p, true) = κ(place (p,
false))`), `StageFrobInput` at the first place and `z zi = 1`. Kind: PROVED. -/
theorem nonempty_stageStepFrob_of_conj (hC : FrobConjugatePlaces S C) (p : ι)
    (hp : (place (p, true)).1 = conjPlace C.κ (place (p, false)).1)
    (F : Matrix (Fin 2) (Fin 2) k) (z zi : k) (eT : k ⊗[ℤ] TorsS K S₀ W N ≃ₗ[k] (Fin 2 → k))
    (h₁ : StageFrobInput eT α (newPlace (place (p, false)) (hw (p, false))) F z)
    (hzi : z * zi = 1) :
    Nonempty (StageStepFrob k (InflMod hS (CoefMod k α (TorsS K S₀ W N))) place
      (urChainRep place hw (CoefMod k α (TorsS K S₀ W N))) p F z zi) := by
  obtain ⟨g, hg⟩ := hC (newPlace (place (p, false)) (hw (p, false)))
    (newPlace (place (p, true)) (hw (p, true))) hp
  exact ⟨stageStepFrob_of_conj hS place hw C W hW N α hα p F z zi eT h₁ hzi g hg⟩

include hα in
/-- **The Frobenius fields of a chain from the conjugate Frobenius** (tex 2778–2796, 4171,
4176–4184): the chain version of `stageStepFrob_of_conj`, with conjugating elements `g i`.
Kind: definition. -/
def stageChainFrob_of_conj (pidx : ℕ → ι) (n : ℕ) (Fr : ℕ → Matrix (Fin 2) (Fin 2) k)
    (z zi : ℕ → k) (eT : ℕ → k ⊗[ℤ] TorsS K S₀ W N ≃ₗ[k] (Fin 2 → k))
    (h₁ : ∀ i < n, StageFrobInput (eT i) α (newPlace (place (pidx i, false))
      (hw (pidx i, false))) (Fr i) (z i))
    (hzi : ∀ i < n, z i * zi i = 1) (g : ℕ → GKS K S₀)
    (hg : ∀ i < n, urFrobElt K (newPlace (place (pidx i, true)) (hw (pidx i, true))) =
      g i * C.conj (urFrobElt K (newPlace (place (pidx i, false)) (hw (pidx i, false)))) *
        (g i)⁻¹) :
    StageChainFrob k (InflMod hS (CoefMod k α (TorsS K S₀ W N))) place
      (urChainRep place hw (CoefMod k α (TorsS K S₀ W N))) pidx n Fr z zi :=
  stageChainFrob_of_inputs hS place hw α pidx n Fr z zi eT
    (fun i => conjStageBasis C W hW N (g i) (eT i)) h₁
    (fun i hi => ⟨frobMatrixAt_conj C W hW N (hg i hi) (h₁ i hi).frobMatrix,
      charValueAt_of_anticyclotomic (h₁ i hi).charValue (hzi i hi)
        (anticyclotomicAt_of_conj C hα (hg i hi))⟩)

include hW hα in
/-- **The Frobenius fields of a chain exist from the GLUE inputs** (tex 2778–2796, 4171,
4176–4184): `FrobConjugatePlaces` at the two places of every step `i < n`, `StageFrobInput` at
the first places and `z i zi i = 1`. Kind: PROVED. -/
theorem nonempty_stageChainFrob_of_conj (hC : FrobConjugatePlaces S C) (pidx : ℕ → ι) (n : ℕ)
    (hp : ∀ i < n, (place (pidx i, true)).1 = conjPlace C.κ (place (pidx i, false)).1)
    (Fr : ℕ → Matrix (Fin 2) (Fin 2) k) (z zi : ℕ → k)
    (eT : ℕ → k ⊗[ℤ] TorsS K S₀ W N ≃ₗ[k] (Fin 2 → k))
    (h₁ : ∀ i < n, StageFrobInput (eT i) α (newPlace (place (pidx i, false))
      (hw (pidx i, false))) (Fr i) (z i))
    (hzi : ∀ i < n, z i * zi i = 1) :
    Nonempty (StageChainFrob k (InflMod hS (CoefMod k α (TorsS K S₀ W N))) place
      (urChainRep place hw (CoefMod k α (TorsS K S₀ W N))) pidx n Fr z zi) := by
  have hex : ∀ i, ∃ g : GKS K S₀, i < n →
      urFrobElt K (newPlace (place (pidx i, true)) (hw (pidx i, true))) =
        g * C.conj (urFrobElt K (newPlace (place (pidx i, false)) (hw (pidx i, false)))) *
          g⁻¹ := by
    intro i
    by_cases hi : i < n
    · obtain ⟨g, hg⟩ := hC (newPlace (place (pidx i, false)) (hw (pidx i, false)))
        (newPlace (place (pidx i, true)) (hw (pidx i, true))) (hp i hi)
      exact ⟨g, fun _ => hg⟩
    · exact ⟨1, fun h => absurd h hi⟩
  choose g hg using hex
  exact ⟨stageChainFrob_of_conj hS place hw C W hW N α hα pidx n Fr z zi eT h₁ hzi g
    fun i hi => hg i hi⟩

end BuildConj

/-! ### (d) The genuine stage chain from the Frobenius fields -/

section Genuine

open Matrix Filter ZInQ.Manuscript ZInQ.Manuscript.RC ZInQ.Manuscript.RC.Central
  ZInQ.Manuscript.RC.Uniform ZInQ.Contrib.CloudB3RC53 ZInQ.Contrib.CloudB3RC53.CommonCoordinate
open ZInQ.Manuscript.RC.Limits (stageIdeal SplitInclusion)
open ZInQ.Contrib.CloudB3RC53.PairedFunctional
open ZInQ.Contrib.CloudB3RC53.RankCounts

attribute [local instance] TopRep.smulCommClass

variable {K : Type} [Field K] [NumberField K] {S₀ S : Set (HeightOneSpectrum (𝓞 K))}
  [DecidableEq (Places K S₀)] [∀ s, TopologicalSpace (StageRing s)]
  {M : ℕ → Type} [∀ s, AddCommGroup (M s)] [∀ s, Module (StageRing s) (M s)]
  [∀ s, DistribMulAction (GKS K S) (M s)] [∀ s, SMulCommClass (GKS K S) (StageRing s) (M s)]
  [∀ s, TopologicalSpace (M s)] [∀ s, DiscreteTopology (M s)]
  [∀ s, ContinuousSMul (GKS K S) (M s)]
  {Δ : ∀ s, LocalConditions (StageRing s) (GKS K S) (fun v : Places K S₀ => Gloc K v.1)
    (fun v => locMap K S v.1) (M s)}
  {ι : Type} [DecidableEq ι] {place : ι × Bool → Places K S}
  {X : ∀ s, (j : ι × Bool) → TopRep.{0} (StageRing s) (GUr K (place j).1)}
  {EU : ∀ s j, SplitInclusion (genuineUq K S (StageRing s) (place j) (X s j))
    (genuineLq K S (StageRing s) (M s) (place j))}
  [∀ s, Module.Free (StageRing s) (M s)] [∀ s, Finite (M s)]
  [∀ s j, ContinuousSMul (GUr K (place j).1) (X s j).V] [∀ s j, DiscreteTopology (X s j).V]
  [∀ s j, Finite (X s j).V]

/-- **The genuine data of one chain at one stage from the Frobenius fields** (tex 4142–4194,
4176–4184, 4385–4451): `GenuineStageSteps` with the fields `f`, `hf`, `hbij`, `b₁`, `hb₁`, `b₂`,
`hb₂` taken from a `StageChainFrob` and the other fields given. Kind: definition. -/
def GenuineStageSteps.ofFrob {s m0 m1 m2 : ℕ} {pidx : ℕ → ι} {n : ℕ}
    {Fr : ℕ → Matrix (Fin 2) (Fin 2) (StageRing s)} {z zi : ℕ → StageRing s}
    (D : StageChainFrob (StageRing s) (M s) place (X s) pidx n Fr z zi)
    (hnew : ∀ i < n, pidx i ∉ chainT pidx i)
    (st0 : CMState m0 m1 m2 (genCx K S₀ S M Δ place X EU s ∅) 0) (q : ℕ → ℕ)
    (zR : ∀ i, (genCx K S₀ S M Δ place X EU s (insert (pidx i) (chainT pidx i))).X 1)
    (hzR : ∀ i, (genCx K S₀ S M Δ place X EU s (insert (pidx i) (chainT pidx i))).d 1 2 rfl
      (zR i) = 0)
    (lamR : ∀ i, (genCx K S₀ S M Δ place X EU s (insert (pidx i) (chainT pidx i))).X 2
      →ₗ[StageRing s] StageRing s)
    (hlamR : ∀ i, lamR i ∘ₗ
      (genCx K S₀ S M Δ place X EU s (insert (pidx i) (chainT pidx i))).d 1 2 rfl = 0)
    (hE : ∀ j, (EU s j).i = ofCCHom (urToLocal_galois K S (place j) (X s j) (D.f j) (D.hf j)))
    (hexp : ∃ e : ℕ, ∀ m : M s, (2 ^ e) • m = 0) (hqodd : ∀ i < n, Odd (q i))
    (hqc : ∀ i < n, ∀ c : Bool, q i = Nat.card (𝓞 K ⧸ (place (pidx i, c)).1.asIdeal)) :
    GenuineStageSteps K S₀ S M Δ place X EU s m0 m1 m2 pidx n where
  hnew := hnew
  st0 := st0
  Fr := Fr
  q := q
  z := z
  zi := zi
  zR := zR
  hzR := hzR
  lamR := lamR
  hlamR := hlamR
  f := D.f
  hf := D.hf
  hbij := D.hbij
  hE := hE
  hexp := hexp
  hqodd := hqodd
  hqc := hqc
  b₁ := D.b₁
  hb₁ := D.hb₁
  b₂ := D.b₂
  hb₂ := D.hb₂

end Genuine

/-! ### (a) The actual module over the stage ring of the chain -/

section StageRingActual

variable {K : Type} [Field K] {S₀ : Set (HeightOneSpectrum (𝓞 K))}

/-- **The stage character over the stage ring of the chain** (tex 2724–2727, 4385–4451): a
character `α : G_{K,S₀} → A_s^×` (e.g. lane E2's `alphaStage`) carried to
`(Λ ⧸ stageIdeal s)^×` along `stageEquiv s : Λ ⧸ stageIdeal s ≃ A_s`. Kind: definition. -/
def stageRingChar (s : ℕ) (α : GKS K S₀ →* (Acoef s)ˣ) : GKS K S₀ →* (StageRing s)ˣ :=
  (Units.map (ZInQ.Manuscript.RC.Limits.stageEquiv s).symm.toRingHom.toMonoidHom).comp α

/-- **The stage character has open kernel** when `α` has (tex 2724–2727): the instance input
for the continuity of the actual module over the stage ring. Kind: PROVED. -/
theorem isOpenKer_stageRingChar (s : ℕ) (α : GKS K S₀ →* (Acoef s)ˣ) [hα : IsOpenKer α] :
    IsOpenKer (stageRingChar s α) :=
  ⟨Subgroup.isOpen_mono (fun g hg => by
    rw [MonoidHom.mem_ker, stageRingChar, MonoidHom.comp_apply, MonoidHom.mem_ker.1 hg,
      map_one]) hα.isOpen_ker⟩

/-- **The actual coefficient module at the stage `s`, over the stage ring of the chain**
(tex 2724–2727, 4385–4451): `(StageRing s ⊗ E(K_{S₀})[2^s])(α)`, i.e. lane E2's
`Mcoef K S₀ W s α` with `A_s` replaced by `Λ ⧸ stageIdeal s`. Kind: definition. -/
abbrev stageActualMod (s : ℕ) (W : WeierstrassCurve K) (α : GKS K S₀ →* (Acoef s)ˣ) : Type :=
  CoefMod (StageRing s) (stageRingChar s α) (TorsS K S₀ W ((2 ^ s : ℕ) : ℤ))

end StageRingActual

/-! ### (d) The actual instances -/

section Actual

variable {K : Type} [Field K] [NumberField K] {S₀ S : Set (HeightOneSpectrum (𝓞 K))}
  (hS : S₀ ⊆ S) {ι : Type} (place : ι × Bool → Places K S) (hw : ∀ j, (place j).1 ∉ S₀)
  (W : WeierstrassCurve K) [W.IsElliptic]

/-- **The Frobenius fields of a chain for lane E2's actual module** (tex 2724–2727,
4176–4184, 3470–3498): over `A_i` with lane E2's `Mcoef K S₀ W i α` (e.g.
`α = alphaStage i s hs hs0 π ψ`), `M = MinS hS W i α`, `X j = urRep (Acoef i) (Mcoef K S₀ W i α)
(newPlace (place j) _)` and `f j = urId`: the objects of lane E2's `h20ConditionsPush_actual`.
Kind: PROVED. -/
theorem nonempty_stageChainFrob_E2 (i : ℕ) [TopologicalSpace (Acoef i)]
    [DiscreteTopology (Acoef i)] (α : GKS K S₀ →* (Acoef i)ˣ) [IsOpenKer α] (pidx : ℕ → ι)
    (n : ℕ) (Fr : ℕ → Matrix (Fin 2) (Fin 2) (Acoef i)) (z zi : ℕ → Acoef i)
    (e₁ e₂ : ℕ → Acoef i ⊗[ℤ] TorsS K S₀ W ((2 ^ i : ℕ) : ℤ) ≃ₗ[Acoef i] (Fin 2 → Acoef i))
    (h₁ : ∀ j < n, StageFrobInput (e₁ j) α (newPlace (place (pidx j, false))
      (hw (pidx j, false))) (Fr j) (z j))
    (h₂ : ∀ j < n, StageFrobInput (e₂ j) α (newPlace (place (pidx j, true))
      (hw (pidx j, true))) (Fr j) (zi j)) :
    Nonempty (StageChainFrob (Acoef i) (MinS hS W i α) place
      (urChainRep place hw (Mcoef K S₀ W i α)) pidx n Fr z zi) :=
  ⟨stageChainFrob_of_inputs hS place hw α pidx n Fr z zi e₁ e₂ h₁ h₂⟩

/-- **The Frobenius fields of a chain for the actual module over the stage ring of the chain**
(tex 2724–2727, 4176–4184, 3470–3498, 4385–4451): over `StageRing s = Λ ⧸ stageIdeal s`, the
coefficient ring of `GenuineStageSteps`, with `M = InflMod hS (stageActualMod s W α)`.
Kind: PROVED. -/
theorem nonempty_stageChainFrob_stage (s : ℕ) [TopologicalSpace (StageRing s)]
    [DiscreteTopology (StageRing s)] (α : GKS K S₀ →* (Acoef s)ˣ) [IsOpenKer α] (pidx : ℕ → ι)
    (n : ℕ) (Fr : ℕ → Matrix (Fin 2) (Fin 2) (StageRing s)) (z zi : ℕ → StageRing s)
    (e₁ e₂ : ℕ → StageRing s ⊗[ℤ] TorsS K S₀ W ((2 ^ s : ℕ) : ℤ) ≃ₗ[StageRing s]
      (Fin 2 → StageRing s))
    (h₁ : ∀ j < n, StageFrobInput (e₁ j) (stageRingChar s α)
      (newPlace (place (pidx j, false)) (hw (pidx j, false))) (Fr j) (z j))
    (h₂ : ∀ j < n, StageFrobInput (e₂ j) (stageRingChar s α)
      (newPlace (place (pidx j, true)) (hw (pidx j, true))) (Fr j) (zi j)) :
    Nonempty (StageChainFrob (StageRing s) (InflMod hS (stageActualMod s W α)) place
      (urChainRep place hw (stageActualMod s W α)) pidx n Fr z zi) := by
  have := isOpenKer_stageRingChar s α
  have : Finite (TorsS K S₀ W ((2 ^ s : ℕ) : ℤ)) :=
    finite_torsS (by exact_mod_cast (pow_ne_zero s two_ne_zero : (2 : ℕ) ^ s ≠ 0))
  exact ⟨stageChainFrob_of_inputs hS place hw (stageRingChar s α) pidx n Fr z zi e₁ e₂ h₁ h₂⟩

end Actual

end ZInQ.Manuscript.RC.Wiring
