import ZInQKernel.Contrib.CloudB3E2Norm.GlobalChar
import ZInQKernel.Contrib.OneProof.RC.Wiring.CommonCoordinate11Genuine

/-!
# The global component of the norm identity in the genuine continuous cochains

Manuscript `diophantine_zq.tex`, tex 4157–4170 ("The actual norm identity is `z_R = e_q i(z_P)`,
with its retained boundary"). The consumer is lane RC32's `hzR_of_components`
(`RC/Wiring/CommonCoordinate11Genuine.lean`), whose global component is
`hG : zR.1 = e • primG D f 1 zP + D.G.d 0 1 rfl bG` at `D = genuineRelaxed …`, with global complex
`D.G = globalCx k (GKS K S) M` (`C^•_cont(G_{K,S}, M)`, `RC/SelmerComplex/Selmer.lean`); the global
component of `i` is the identity (`changeMap_global`).

The identity of `TransferNorm.lean` is between cochains `(Fin 1 → G) → D` with values in the
ambient module `D` (for the text, `D ⊇ E(K̄)`-type divisible coefficients), valued in `D[k]`. This file
transports it to the genuine complex `globalCx A G M` of continuous cochains with values in a
discrete `G`-module `M` (the finite coefficient module) through an injective equivariant map
`ι : M → D` whose image contains `D[k]`:

* `gval z` (definition): the function `Gⁿ → M` of a genuine cochain `z ∈ (globalCx A G M).X 1`;
  `gval_injective`, `gval_add`, `gval_smul` (PROVED).
* `const0 m` (definition): the constant `0`-cochain; `gval_d_const0` (PROVED):
  `d(const0 m)(g) = g₀ m − m`.
* **`hG_of_transfer`** (PROVED): if `zR`, `zP ∈ (globalCx A G M).X 1` are the genuine cochains
  whose images under `ι` are the twisted transfers `𝒯_θ(κ(Q_R))`, `𝒯_θ(κ(Q_P))` of the Kummer
  cocycles (`hzR`, `hzP`: the identification of the actual classes), then under the hypotheses of
  `transfer_kummer_norm_of_transversal` there is a genuine `0`-cochain `b_G` (the `ι`-preimage of
  the retained boundary, a constant cochain) with `zR = e_q • zP + d b_G` in `globalCx A G M`.
  This is exactly the shape of `hG` (with `primG D f 1 zP` the global component of `zP`).
* **`exists_gval_eq_transfer`** (PROVED): such genuine cochains exist (continuity): if the
  twisted-action stabilizer of the weighted sum `P̃ = ∑_δ R(r_δ) Q` is open (for the text: `P̃` is a
  point defined over a finite extension inside `K_S`, and `H` is open) and the values of
  `𝒯_θ(κ(Q))` lie in `ι(M)`, then there is a continuous genuine `z` with `ι ∘ z = 𝒯_θ(κ(Q))`.
* **`hG_genuine_of_transfer`** (PROVED): the same at lane RC32's genuine relaxed Selmer data
  `genuineRelaxed K S₀ S k M Δ w`, for the global components `zR.1` and `primG D f 1 zP`; after
  destructuring its existential, it supplies exactly the arguments `bG` and `hG` of
  `hzR_of_components`.
* Non-vacuity: `nonVacuity_genuine`.

**What remains**: (1) the character compatibility `hθ` of `transfer_kummer_norm_of_transversal`
(removed for descents of one global character in `GlobalChar.lean`); (2) witnesses for the
actual-class identifications `hzR`, `hzP`: by `exists_gval_eq_transfer` they exist once the
stabilizers are open, but the open-stabilizer witnesses for the actual points (their fields of
definition inside `K_S`) and the ring class fields `H_T` as intermediate fields of `K_S/K` are not
in the tree; (3) the identification of the genuine coefficient module `M` with `D[k]` through `ι`
and of the genuine action with the twisted action `R = θ ρ` (`hιeq`, `htors`); (4) the
identification of the division points `Q_T` with those of the actual Heegner points
(the anchor of `CCLThm2_15AppliedWithUnits`); (5) the local components `hU`, `hL` (item 3 of the
common-coordinate step).

Kinds: definitions and PROVED.
-/

noncomputable section

namespace ZInQ.Contrib.CloudB3E2.NormCochain

open ZInQ.Contrib.CloudB3RC53.HeegnerCohomology.TwistedTransfer
open ZInQ.Manuscript.RC.SelmerComplex
open ZInQ.Manuscript.RC.Central (pointFactor)
open scoped Pointwise

section Genuine

variable {A : Type} [CommRing A] {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {M : Type} [AddCommGroup M] [Module A M] [DistribMulAction G M] [SMulCommClass G A M]
  [TopologicalSpace M] [DiscreteTopology M] [ContinuousSMul G M]

/-- **The function of a genuine `1`-cochain** `z ∈ C¹_cont(G, M)`. Kind: definition. -/
def gval (z : (globalCx A G M).X 1) : (Fin 1 → G) → M :=
  asFun A G M ((contSubCx A G M).el z : contCochain A G M 1)

theorem gval_injective : Function.Injective (gval (A := A) (G := G) (M := M)) := by
  intro z₁ z₂ h
  exact Subtype.ext h

theorem gval_add (z₁ z₂ : (globalCx A G M).X 1) : gval (z₁ + z₂) = gval z₁ + gval z₂ := rfl

theorem gval_smul (c : A) (z : (globalCx A G M).X 1) : gval (c • z) = c • gval z := rfl

/-- **The constant `0`-cochain** with value `m`. Kind: definition. -/
def const0 (m : M) : (globalCx A G M).X 0 :=
  (contSubCx A G M).ofSub ⟨(fun _ => m : (Fin 0 → G) → M), continuous_const⟩

/-- **The coboundary of a constant `0`-cochain** (PROVED): `d(const0 m)(g) = g₀ m − m`. -/
theorem gval_d_const0 (m : M) (g : Fin 1 → G) :
    gval ((globalCx A G M).d 0 1 rfl (const0 m)) g = g 0 • m - m := by
  have h := contCochains_d_apply (k := A) (G := G) (M := M) 0 (const0 m) g
  change asFun A G M (((contSubCx A G M).el (((contCochains A G M).d 0 (0 + 1)).hom
    (const0 m)) : contCochain A G M (0 + 1)) : _) g = _
  have hc : ∀ x, asFun A G M (((contSubCx A G M).el (const0 m) : contCochain A G M 0) :
      (groupCohomology.inhomogeneousCochains (rep A G M)).X 0) x = m := fun _ => rfl
  rw [h, hc, Fin.sum_univ_one, hc]
  simp [sub_eq_add_neg]

variable {D : Type} [AddCommGroup D] [Module A D] (ρ : G →* Module.End A D)
  (HP HR : Subgroup G) [HP.Normal] [HR.Normal] [Fintype (G ⧸ HP)] [Fintype (G ⧸ HR)]
  (rP : G ⧸ HP → G) (hrP : ∀ δ, ((rP δ : G) : G ⧸ HP) = δ)
  (rR : G ⧸ HR → G) (hrR : ∀ δ, ((rR δ : G) : G ⧸ HR) = δ)
  (θP : G ⧸ HP →* Aˣ) (θR : G ⧸ HR →* Aˣ)
  (U : Subgroup HP) (hU : ∀ h : HP, h ∈ U ↔ (h : G) ∈ HR) [Fintype (HP ⧸ U)]
  (t : HP ⧸ U → HP) (ht : ∀ τ : HP ⧸ U, (QuotientGroup.mk (t τ) : HP ⧸ U) = τ)

set_option linter.unusedSectionVars false

include hrP hrR hU ht in
/-- **The global component `hG` of the norm identity in the genuine continuous cochains**
(PROVED; tex 4157–4170 at a finite coefficient stage). Let `ι : M → D` be an injective `A`-linear
map from the genuine coefficient module to the ambient module, equivariant for the genuine action
and the twisted action `R = θ ρ` (`hιeq`), with image containing `D[k]` (`htors`). If the genuine
cochains `zR`, `zP` are carried by `ι` to the twisted transfers of the Kummer cocycles of `Q_R`,
`Q_P` (`hzR`, `hzP`), then under the hypotheses of `transfer_kummer_norm_of_transversal`,
`zR = e_q • zP + d b_G` for a genuine `0`-cochain `b_G` (the `ι`-preimage of the retained
boundary). -/
theorem hG_of_transfer (hle : HR ≤ HP)
    (hθ : ∀ x : G, ((θR (x : G ⧸ HR) : Aˣ) : A) = θP (x : G ⧸ HP))
    (k a : ℤ) (σ : G) {yR yP QR QP : D}
    (hQR : k • QR = yR) (hQP : k • QP = yP) (hfixR : ∀ h ∈ HR, ρ h yR = yR)
    (hfixP : ∀ h ∈ HP, ρ h yP = yP)
    (hnorm : ∑ τ : HP ⧸ U, ρ (t τ : G) yR = a • yP - ρ σ yP - ρ σ⁻¹ yP)
    (ι : M →ₗ[A] D) (hι : Function.Injective ι)
    (hιeq : ∀ (g : G) (m : M), ι (g • m) = R HR ρ θR g (ι m))
    (htors : ∀ x : D, k • x = 0 → ∃ m : M, ι m = x)
    (zR zP : (globalCx A G M).X 1)
    (hzR : ∀ g : Fin 1 → G, ι (gval zR g) = T HR rR hrR ρ θR 1 (kummerCochain ρ HR QR) g)
    (hzP : ∀ g : Fin 1 → G, ι (gval zP g) = T HP rP hrP ρ θP 1 (kummerCochain ρ HP QP) g) :
    ∃ bG : (globalCx A G M).X 0,
      zR = eq_ HP θP a σ • zP + (globalCx A G M).d 0 1 rfl bG := by
  obtain ⟨h1, h2, -, -⟩ := transfer_kummer_norm_of_transversal ρ HP HR rP hrP rR hrR θP θR U hU
    t ht hle hθ k a σ hQR hQP hfixR hfixP hnorm
  obtain ⟨m₀, hm₀⟩ := htors _ h2
  refine ⟨const0 m₀, gval_injective (funext fun g => hι ?_)⟩
  rw [gval_add, gval_smul, Pi.add_apply, Pi.smul_apply, gval_d_const0, map_add, map_smul,
    map_sub, hιeq, hzR, hzP, hm₀, h1 g]

/-- **Genuine cochains carrying the transferred Kummer cocycles exist** (PROVED; continuity): for
an element `P ∈ D` (the weighted sum `∑_δ R(r_δ) Q`) whose stabilizer `V` under an action
`act : G → D → D` is open, if every value `act g P − P` lies in `ι(M)`, then there is a
continuous genuine `1`-cochain `z` with `ι (z g) = act g₀ P − P`. Applied with
`act = R HR ρ θR` and `kummer_weighted_sum`, `act g₀ P − P` is `𝒯_θ(κ(Q))(g)`. -/
theorem exists_gval_eq_transfer (ι : M →ₗ[A] D) (hι : Function.Injective ι) (act : G → D → D)
    (hact : ∀ g h : G, act (g * h) = act g ∘ act h) (P : D) (V : Subgroup G)
    (hV : IsOpen (V : Set G)) (hVP : ∀ v ∈ V, act v P = P)
    (himg : ∀ g : G, ∃ m : M, ι m = act g P - P) :
    ∃ z : (globalCx A G M).X 1, ∀ g : Fin 1 → G, ι (gval z g) = act (g 0) P - P := by
  classical
  choose c hc using himg
  -- `c` is constant on the left cosets of the open subgroup `V`, hence locally constant
  have hconst : ∀ g : G, ∀ v ∈ V, c (g * v) = c g := by
    intro g v hv
    apply hι
    rw [hc, hc, hact, Function.comp_apply, hVP v hv]
  have hcont : Continuous c := by
    refine continuous_def.mpr fun s _ => ?_
    have : c ⁻¹' s = ⋃ g ∈ c ⁻¹' s, g • (V : Set G) := by
      ext x
      simp only [Set.mem_preimage, Set.mem_iUnion]
      constructor
      · intro hx
        exact ⟨x, hx, ⟨1, V.one_mem, by simp⟩⟩
      · rintro ⟨g, hg, v, hv, rfl⟩
        simpa [hconst g v hv] using hg
    rw [this]
    exact isOpen_biUnion fun g _ => hV.smul g
  refine ⟨(contSubCx A G M).ofSub ⟨(fun x => c (x 0) : (Fin 1 → G) → M),
    hcont.comp (continuous_apply 0)⟩, fun g => ?_⟩
  exact hc (g 0)

end Genuine

/-! ### At the genuine relaxed Selmer data of lane RC32 -/

section GenuineTriangle

open NumberField IsDedekindDomain ZInQ.Manuscript.RC.Wiring
open ZInQ.Contrib.CloudB3RC53.PairedFunctional

variable (K : Type) [Field K] [NumberField K] (S₀ S : Set (HeightOneSpectrum (𝓞 K)))
  (k : Type) [Field k] [TopologicalSpace k]
  (M : Type) [AddCommGroup M] [Module k M] [DistribMulAction (GKS K S) M]
  [SMulCommClass (GKS K S) k M] [TopologicalSpace M] [DiscreteTopology M]
  [ContinuousSMul (GKS K S) M]
  {D : Type} [AddCommGroup D] [Module k D] (ρ : GKS K S →* Module.End k D)
  (HP HR : Subgroup (GKS K S)) [HP.Normal] [HR.Normal] [Fintype (GKS K S ⧸ HP)]
  [Fintype (GKS K S ⧸ HR)]
  (rP : GKS K S ⧸ HP → GKS K S) (hrP : ∀ δ, ((rP δ : GKS K S) : GKS K S ⧸ HP) = δ)
  (rR : GKS K S ⧸ HR → GKS K S) (hrR : ∀ δ, ((rR δ : GKS K S) : GKS K S ⧸ HR) = δ)
  (θP : GKS K S ⧸ HP →* kˣ) (θR : GKS K S ⧸ HR →* kˣ)
  (U : Subgroup HP) (hU : ∀ h : HP, h ∈ U ↔ (h : GKS K S) ∈ HR) [Fintype (HP ⧸ U)]
  (t : HP ⧸ U → HP) (ht : ∀ τ : HP ⧸ U, (QuotientGroup.mk (t τ) : HP ⧸ U) = τ)

set_option linter.unusedSectionVars false

include hrP hrR hU ht in
/-- **`hG` of lane RC32's `hzR_of_components` at the genuine relaxed Selmer data**
`genuineRelaxed K S₀ S k M Δ w` (PROVED): its global complex is `globalCx k (GKS K S) M`, so
`hG_of_transfer` applies to the global components `zR.1` and `primG D f 1 zP` (the global
component of `i` is the identity, `changeMap_global`). After destructuring the existential, the
conclusion supplies exactly the arguments `bG` and `hG` of `hzR_of_components`. -/
theorem hG_genuine_of_transfer
    (Δ : LocalConditions k (GKS K S) (fun v : Places K S₀ => Gloc K v.1)
      (fun v => locMap K S v.1) M) (w : Places K S) {U' : GCx k}
    (f : GHom U' (genuineRelaxed K S₀ S k M Δ w).U)
    (zR : (selCx (genuineRelaxed K S₀ S k M Δ w)).X 1)
    (zP : (selCx (selRestrict (genuineRelaxed K S₀ S k M Δ w) f)).X 1)
    (hle : HR ≤ HP)
    (hθ : ∀ x : GKS K S, ((θR (x : GKS K S ⧸ HR) : kˣ) : k) = θP (x : GKS K S ⧸ HP))
    (kk a : ℤ) (σ : GKS K S) {yR yP QR QP : D}
    (hQR : kk • QR = yR) (hQP : kk • QP = yP) (hfixR : ∀ h ∈ HR, ρ h yR = yR)
    (hfixP : ∀ h ∈ HP, ρ h yP = yP)
    (hnorm : ∑ τ : HP ⧸ U, ρ (t τ : GKS K S) yR = a • yP - ρ σ yP - ρ σ⁻¹ yP)
    (ι : M →ₗ[k] D) (hι : Function.Injective ι)
    (hιeq : ∀ (g : GKS K S) (m : M), ι (g • m) = R HR ρ θR g (ι m))
    (htors : ∀ x : D, kk • x = 0 → ∃ m : M, ι m = x)
    (hzR : ∀ g : Fin 1 → GKS K S,
      ι (gval (A := k) (M := M) zR.1 g) = T HR rR hrR ρ θR 1 (kummerCochain ρ HR QR) g)
    (hzP : ∀ g : Fin 1 → GKS K S,
      ι (gval (A := k) (M := M) (primG (genuineRelaxed K S₀ S k M Δ w) f 1 zP) g) =
        T HP rP hrP ρ θP 1 (kummerCochain ρ HP QP) g) :
    ∃ bG : (genuineRelaxed K S₀ S k M Δ w).G.X 0,
      zR.1 = eq_ HP θP a σ • primG (genuineRelaxed K S₀ S k M Δ w) f 1 zP +
        (genuineRelaxed K S₀ S k M Δ w).G.d 0 1 rfl bG :=
  hG_of_transfer ρ HP HR rP hrP rR hrR θP θR U hU t ht hle hθ kk a σ hQR hQP hfixR hfixP hnorm
    ι hι hιeq htors zR.1 (primG (genuineRelaxed K S₀ S k M Δ w) f 1 zP) hzR hzP

end GenuineTriangle

/-! ### Non-vacuity -/

/-- **Non-vacuity of the coefficient hypotheses of `hG_of_transfer`**: the identity map of `ℤ`
(as a module over itself, trivial action of the trivial group, discrete topology) is injective,
equivariant for the trivial twisted action, and its image contains `ℤ[2]`; the remaining
hypotheses are those of `transfer_kummer_norm_of_transversal` (`nonVacuity_transversal`). -/
theorem nonVacuity_genuine :
    ∃ (ι : ℤ →ₗ[ℤ] ℤ), Function.Injective ι ∧ (∀ (g : Unit) (m : ℤ), ι (g • m) = ι m) ∧
      ∀ x : ℤ, (2 : ℤ) • x = 0 → ∃ m : ℤ, ι m = x :=
  ⟨LinearMap.id, fun _ _ h => h, fun _ _ => rfl, fun x _ => ⟨x, rfl⟩⟩

end ZInQ.Contrib.CloudB3E2.NormCochain
