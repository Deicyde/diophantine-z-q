import ZInQKernel.Contrib.CloudB3E2Norm.H20Assembly

/-!
# `LocalTwistIdentification` for the actual data: the quadratic-twist comparison

Manuscript `diophantine_zq.tex`, tex 3251–3270 ("Under the fixed quadratic-twist identification,
the local map is the ordinary integral norm on Kummer classes") and tex 3413–3438 (the local twist
`B = E^{(h)}` over `K_v`, `T_2B ≅ T_2E(χ_h)`).

`LocalIdentity.lean` states the coefficient/twist identification at an old place as the Prop
`LocalTwistIdentification ρ H θ ι B m φ ι_v ψ j_B` (five clauses). This file constructs the objects
and proves the Prop for the actual data of `H20Actual.lean` (the Shapiro-level module
`shapMod = (ℤ[Δ] ⊗ E(K_{S₀})[2^i])(χ_h[π])` and lane RC29's Kummer maps), with the comparisons
already in the tree (lane RC29's `compPt`, `compTors`, `twistPt`; lane RC28's `CoefMod`):

* `PtS` (with `ptSAction`): the points `E(K_{S₀})` with their `G_{K,S₀}`-action (coordinatewise).
* `ambD₀ = (ℤ[Δ] ⊗ E(K_{S₀}))(χ_h)` and its inflation `ambD` to `G_{K,S}` — the ambient module of
  points (`ρ = ambRho`); `ambIota : shapMod → ambD` (`1 ⊗` the inclusion `E[2^i] ⊆ E(K_{S₀})`).
* `locL v = (ℤ[Δ] ⊗ E(K̄_v))(χ_h ∘ p_v)` over `G_{K_v}`; `locPsi v = 1 ⊗ compPt` (along the
  embedding `K_{S₀} → K̄_v`); `locJB v = 1 ⊗ twistPt` (the twist identification `B(K̄_v) ≅ E(K̄_v)`).
* **`localTwistIdentification_actual`** (PROVED): for `v ∈ P` (where `Ψ_i` is trivial, the ELLIOT
  input), any normal `H` and character `θ` trivial on `p_v(G_{K_v})`, and `FullTorsion`, the Prop
  holds with `m = 2^i` and `ι_v` the Shapiro-level Kummer map `shapIota`:
  1. `ψ ∘ ι` injective (`ℤ[Δ]` flat, `compPt` injective);
  2. `2^i`-torsion of `L` comes from `M` (`ℤ[Δ]` flat, so `(ℤ[Δ] ⊗ X)[2^i] = ℤ[Δ] ⊗ X[2^i]`, and
     `compTors` is bijective by `FullTorsion`);
  3. `ψ` equivariant (`compPt_smul`, `locMap_compat`);
  4. `j_B` equivariant (`twistPt_smul`, `twistSign_localSqrt`);
  5. `ψ(ι(ι_v t)) = j_B(t)` (unfolding RC29's `genIotaBase`).
* **`oldPlaceInput_actual`** (PROVED): `OldPlaceInput` (the hypothesis `hinR`/`hinP` of
  `h1_shapiro`) at `v ∈ P` from the realization `hreal` alone.
* `thetaPi` (the character `[π]` of `G_{K,S}/ker(π ∘ infl)`; so the transfer subgroup is
  `H = ker(π ∘ infl) = G_L`, `L` the field cut out by `Ψ_i` for `Δ = im Ψ_i` — the `im Ψ_i` level of
  `H20Bridge.lean`, not the manuscript's `G_{H_f}`, which is reached through `bridge_class`), `thetaPi_trivial` (PROVED from the
  ELLIOT input: the hypothesis `hθ` above at `v ∈ P`), **`ambIota_equivariant`** (PROVED: `ι`
  intertwines the Shapiro-level action with `R = [π]ρ`, the hypothesis `hιeq` of `h1_shapiro`).
* Non-vacuity: the hypotheses are those of `H20Actual.lean` (witnessed there), `FullTorsion`
  (discharged by `DivisionPoints.fullTorsion_of_goodReduction`) and the realization `hreal`.

Kinds: definitions and PROVED (GLUE `FullTorsion`, discharged in the tree by
`DivisionPoints.fullTorsion_of_goodReduction`; ELLIOT `PsiTrivialAt2N`).
-/

noncomputable section

namespace ZInQ.Contrib.CloudB3E2.NormCochain

open ZInQ.Contrib.CloudB3RC53.HeegnerCohomology.TwistedTransfer
open ZInQ.Manuscript.RC.Wiring ZInQ.Manuscript.RC.SelmerComplex ZInQ.Manuscript.RC.CoefModules
open ZInQ.Manuscript.RC.KummerMaps
open ZInQ.Manuscript.RC.HeegnerAlgebra (Acoef)
open NumberField IsDedekindDomain TensorProduct WeierstrassCurve

attribute [local instance] groupRingTop

set_option linter.unusedSectionVars false

/-! ### The points `E(K_{S₀})` with their Galois action -/

section Points

variable (K : Type) [Field K] [NumberField K] (S₀ : Set (HeightOneSpectrum (𝓞 K)))
  (W : WeierstrassCurve K)

/-- The points `E(K_{S₀})`. -/
abbrev PtS : Type := (W.baseChange (KS K S₀)).toAffine.Point

/-- **The Galois action of `G_{K,S₀}` on `E(K_{S₀})`** (coordinatewise). Kind: definition. -/
@[reducible] def ptSAction : DistribMulAction (GKS K S₀) (PtS K S₀ W) where
  smul σ P := Affine.Point.map (galS K S₀ σ).toAlgHom P
  one_smul P := pointMap_one P
  mul_smul σ τ P := (Affine.Point.map_map (galS K S₀ τ).toAlgHom (galS K S₀ σ).toAlgHom P).symm
  smul_zero _ := map_zero _
  smul_add _ _ _ := map_add _ _ _

attribute [local instance] ptSAction

theorem ptS_smul_def (σ : GKS K S₀) (P : PtS K S₀ W) :
    σ • P = Affine.Point.map (galS K S₀ σ).toAlgHom P := rfl

/-- The inclusion `E(K_{S₀})[2^i] ⊆ E(K_{S₀})`, as a `ℤ`-linear map. -/
def torsIncl (i : ℕ) : TorsT S₀ W i →ₗ[ℤ] PtS K S₀ W :=
  (AddSubgroup.subtype _).toIntLinearMap

end Points

attribute [local instance] ptSAction

/-! ### The ambient module of points and the local modules -/

section Objects

variable {K : Type} [Field K] [NumberField K] {S S₀ : Set (HeightOneSpectrum (𝓞 K))}
  (hS : S₀ ⊆ S) (W : WeierstrassCurve K) [W.IsElliptic] (i : ℕ) [NeZero i] (s : KS K S₀) {h : K}
  (hs : s ^ 2 = algebraMap K (KS K S₀) h) (hs0 : s ≠ 0)
  {Δ : Type} [CommGroup Δ] [Finite Δ] (π : GKS K S₀ →* Δ)

/-- The character `χ_h` with values in `ℤ[Δ]^×`. -/
abbrev chiZ : GKS K S₀ →* (MonoidAlgebra ℤ Δ)ˣ :=
  (intUnitsTo (MonoidAlgebra ℤ Δ)).comp (quadChar s hs hs0)

/-- **The ambient module of points over `G_{K,S₀}`**: `(ℤ[Δ] ⊗ E(K_{S₀}))(χ_h)`. -/
abbrev ambD₀ : Type := CoefMod (MonoidAlgebra ℤ Δ) (chiZ s hs hs0 (Δ := Δ)) (PtS K S₀ W)

/-- **The ambient module of points over `G_{K,S}`** (inflated). -/
abbrev ambD : Type := ResMod (inflMap K hS) (ambD₀ W s hs hs0 (Δ := Δ))

/-- `ρ` on the ambient module. -/
abbrev ambRho : GKS K S →* Module.End (MonoidAlgebra ℤ Δ) (ambD hS W s hs hs0 (Δ := Δ)) :=
  DistribMulAction.toModuleEnd (MonoidAlgebra ℤ Δ) (ambD hS W s hs hs0 (Δ := Δ))

/-- **`ι : shapMod → ambD`**, `1 ⊗` the inclusion of the `2^i`-torsion. Kind: definition. -/
def ambIota : shapMod hS W i s hs hs0 π →ₗ[MonoidAlgebra ℤ Δ] ambD hS W s hs hs0 (Δ := Δ) :=
  LinearMap.baseChange (MonoidAlgebra ℤ Δ) (torsIncl K S₀ W i)

variable (v : HeightOneSpectrum (𝓞 K))

/-- `E(K̄_v)`. -/
abbrev PtV : Type := PtAlg (v.adicCompletion K) (W.baseChange (v.adicCompletion K))

/-- **The local module at `v`**: `(ℤ[Δ] ⊗ E(K̄_v))(χ_h ∘ p_v)` over `G_{K_v}`. -/
abbrev locL (Δ : Type) [CommGroup Δ] : Type :=
  CoefMod (MonoidAlgebra ℤ Δ) ((chiZ s hs hs0 (Δ := Δ)).comp (locMap K S₀ v : Gloc K v →* GKS K S₀))
    (PtV W v)

/-- `1 ⊗ compPt` on the uninflated ambient module. Kind: definition. -/
def psi₀ : ambD₀ W s hs hs0 (Δ := Δ) →ₗ[MonoidAlgebra ℤ Δ] locL W s hs hs0 v Δ :=
  LinearMap.baseChange (MonoidAlgebra ℤ Δ) (compPt (S := S₀) W v).toIntLinearMap

theorem psi₀_tmul (a : MonoidAlgebra ℤ Δ) (P : PtS K S₀ W) :
    psi₀ W s hs hs0 v (CoefMod.equiv _ _ _ (a ⊗ₜ P)) =
      CoefMod.equiv _ _ _ (a ⊗ₜ compPt (S := S₀) W v P) := rfl

/-- **`ψ = 1 ⊗ compPt`** along the embedding `K_{S₀} → K̄_v`. Kind: definition. -/
def locPsi : ambD hS W s hs hs0 (Δ := Δ) →ₗ[MonoidAlgebra ℤ Δ] locL W s hs hs0 v Δ :=
  psi₀ W s hs hs0 v

/-- **`j_B = 1 ⊗ twistPt`**, the twist identification `B(K̄_v) ≅ E(K̄_v)` at `q = j(s)`.
Kind: definition. -/
def locJB : PtAlg (v.adicCompletion K) (localTwist W h v) →+ locL W s hs hs0 v Δ :=
  (TensorProduct.mk ℤ (MonoidAlgebra ℤ Δ) (PtV W v) 1).toAddMonoidHom.comp
    (twistPt (W.baseChange (v.adicCompletion K)) (algebraMap K (v.adicCompletion K) h)
      two_ne_zero (localSqrt_ne_zero s hs0 v) (localSqrt_sq s hs v)).toAddMonoidHom

end Objects

/-! ### The five clauses -/

section Clauses

variable {K : Type} [Field K] [NumberField K] {S S₀ : Set (HeightOneSpectrum (𝓞 K))}
  (hS : S₀ ⊆ S) (W : WeierstrassCurve K) [W.IsElliptic] (i : ℕ) [NeZero i] (s : KS K S₀) {h : K}
  (hs : s ^ 2 = algebraMap K (KS K S₀) h) (hs0 : s ≠ 0) (hFull : FullTorsion K S₀ W (2 ^ i))
  {Δ : Type} [CommGroup Δ] [Finite Δ] (π : GKS K S₀ →* Δ)
  (v : HeightOneSpectrum (𝓞 K))

/-- `ψ ∘ ι` composed: the map `E(K_{S₀})[2^i] → E(K̄_v)`. -/
abbrev psiIotaBase (S₀ : Set (HeightOneSpectrum (𝓞 K))) : TorsT S₀ W i →ₗ[ℤ] PtV W v :=
  (compPt (S := S₀) W v).toIntLinearMap ∘ₗ torsIncl K S₀ W i

/-- **`ψ ∘ ι = 1 ⊗ (compPt ∘ incl)`** (PROVED). -/
theorem psi_iota_apply [TopologicalSpace (Acoef i)] [DiscreteTopology (Acoef i)]
    (x : shapMod hS W i s hs hs0 π) :
    locPsi hS W s hs hs0 v (ambIota hS W i s hs hs0 π x) =
      LinearMap.lTensor (MonoidAlgebra ℤ Δ) (psiIotaBase W i v S₀)
        (show MonoidAlgebra ℤ Δ ⊗[ℤ] TorsT S₀ W i from x) := by
  change LinearMap.baseChange _ _ (LinearMap.baseChange _ _ x) = _
  rw [LinearMap.baseChange_eq_lTensor, LinearMap.baseChange_eq_lTensor]
  exact (LinearMap.lTensor_comp_apply (MonoidAlgebra ℤ Δ) _ _ _).symm

/-- `compPt ∘ incl` is injective. Kind: PROVED. -/
theorem psiIotaBase_injective : Function.Injective (psiIotaBase W i v S₀) :=
  (compPt_injective (S := S₀) W v).comp Subtype.val_injective

/-- The inclusion `E(K̄_v)[2^i] ⊆ E(K̄_v)`. -/
abbrev torsVIncl :
    TorsAlg (v.adicCompletion K) (W.baseChange (v.adicCompletion K)) (2 ^ i) →ₗ[ℤ] PtV W v :=
  (AddSubgroup.subtype _).toIntLinearMap

/-- `compPt ∘ incl = incl ∘ compTors`. Kind: PROVED. -/
theorem psiIotaBase_eq :
    psiIotaBase W i v S₀ = torsVIncl W i v ∘ₗ (compTors (S := S₀) W (2 ^ i) v).toIntLinearMap := by
  ext t
  rfl

include hFull in
/-- **Clause 2**: every `2^i`-torsion element of `L` comes from `M` (PROVED; `ℤ[Δ]` flat and
`compTors` bijective under `FullTorsion`). -/
theorem clause2 [TopologicalSpace (Acoef i)] [DiscreteTopology (Acoef i)]
    (x : locL W s hs hs0 v Δ) (hx : (2 ^ i : ℕ) • x = 0) :
    ∃ m₀ : shapMod hS W i s hs hs0 π, locPsi hS W s hs hs0 v (ambIota hS W i s hs hs0 π m₀) = x := by
  set A := MonoidAlgebra ℤ Δ
  let mul : PtV W v →ₗ[ℤ] PtV W v := ((2 ^ i : ℕ) : ℤ) • (LinearMap.id : PtV W v →ₗ[ℤ] PtV W v)
  have hmul : ∀ y, mul y = (2 ^ i : ℕ) • y := fun y => by
    simp only [mul, LinearMap.smul_apply, LinearMap.id_apply, natCast_zsmul]
  have hex : Function.Exact (torsVIncl W i v) mul := by
    intro y
    rw [hmul]
    constructor
    · intro hy
      exact ⟨⟨y, (AddSubgroup.torsionBy.nsmul_iff).2 hy⟩, rfl⟩
    · rintro ⟨t, rfl⟩
      exact (AddSubgroup.torsionBy.nsmul_iff).1 t.2
  have hex' := Module.Flat.lTensor_exact A hex
  have hlt : ∀ z : A ⊗[ℤ] PtV W v, LinearMap.lTensor A mul z = (2 ^ i : ℕ) • z := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul a y => rw [LinearMap.lTensor_tmul, hmul, TensorProduct.tmul_smul]
    | add z₁ z₂ h₁ h₂ => rw [map_add, h₁, h₂, smul_add]
  have hmx : LinearMap.lTensor A mul (show A ⊗[ℤ] PtV W v from x) = 0 := by
    rw [hlt]
    exact hx
  obtain ⟨y, hy⟩ := (hex' _).1 hmx
  have hsurj : Function.Surjective (LinearMap.lTensor A
      (compTors (S := S₀) W (2 ^ i) v).toIntLinearMap) :=
    LinearMap.lTensor_surjective A (compTors_bijective W (2 ^ i) hFull v).2
  obtain ⟨z, rfl⟩ := hsurj y
  refine ⟨z, (psi_iota_apply hS W i s hs hs0 π v z).trans ?_⟩
  rw [psiIotaBase_eq, LinearMap.lTensor_comp, LinearMap.comp_apply]
  exact hy

/-- `ψ₀` is equivariant for `p_v` (PROVED; `compPt_smul`). -/
theorem psi₀_smul (σ : Gloc K v) (x : ambD₀ W s hs hs0 (Δ := Δ)) :
    psi₀ W s hs hs0 v (locMap K S₀ v σ • x) = σ • psi₀ W s hs hs0 v x := by
  refine TensorProduct.induction_on (R := ℤ) (M := MonoidAlgebra ℤ Δ) (N := PtS K S₀ W)
    (motive := fun z => psi₀ W s hs hs0 v (locMap K S₀ v σ • (show ambD₀ W s hs hs0 (Δ := Δ) from z))
      = σ • psi₀ W s hs hs0 v (show ambD₀ W s hs hs0 (Δ := Δ) from z)) x ?_ ?_ ?_
  · change psi₀ W s hs hs0 v (locMap K S₀ v σ • (0 : ambD₀ W s hs hs0 (Δ := Δ))) =
      σ • psi₀ W s hs hs0 v 0
    rw [smul_zero, map_zero, smul_zero]
  · intro a P
    have h1 := CoefMod.smul_tmul (MonoidAlgebra ℤ Δ) (chiZ s hs hs0 (Δ := Δ)) (PtS K S₀ W)
      (locMap K S₀ v σ) a P
    have h2 := CoefMod.smul_tmul (MonoidAlgebra ℤ Δ)
      ((chiZ s hs hs0 (Δ := Δ)).comp (locMap K S₀ v : Gloc K v →* GKS K S₀)) (PtV W v) σ a
      (compPt (S := S₀) W v P)
    change psi₀ W s hs hs0 v (locMap K S₀ v σ • CoefMod.equiv _ _ _ (a ⊗ₜ P)) =
      σ • psi₀ W s hs hs0 v (CoefMod.equiv _ _ _ (a ⊗ₜ P))
    rw [h1, psi₀_tmul, psi₀_tmul, h2, ptS_smul_def, compPt_smul]
    rfl
  · intro x y hx hy
    change psi₀ W s hs hs0 v (locMap K S₀ v σ • ((show ambD₀ W s hs hs0 (Δ := Δ) from x) +
        (show ambD₀ W s hs hs0 (Δ := Δ) from y))) =
      σ • psi₀ W s hs hs0 v ((show ambD₀ W s hs hs0 (Δ := Δ) from x) +
        (show ambD₀ W s hs hs0 (Δ := Δ) from y))
    rw [smul_add, map_add, hx, hy, map_add, smul_add]

/-- **Clause 3 (untwisted)**: `ψ` is equivariant for `ρ ∘ p_v` (PROVED; `locMap_compat`). -/
theorem clause3_rho (σ : Gloc K v) (x : ambD hS W s hs hs0 (Δ := Δ)) :
    locPsi hS W s hs hs0 v (locMap K S v σ • x) = σ • locPsi hS W s hs hs0 v x := by
  change psi₀ W s hs hs0 v (inflMap K hS (locMap K S v σ) • (show ambD₀ W s hs hs0 from x)) =
    σ • psi₀ W s hs hs0 v (show ambD₀ W s hs hs0 from x)
  rw [locMap_compat K hS v σ]
  exact psi₀_smul W s hs hs0 v σ x

/-- **Clause 4**: `j_B` is Galois-equivariant (PROVED; `twistPt_smul`, `twistSign_localSqrt`). -/
theorem clause4 (σ : Gloc K v) (p : PtAlg (v.adicCompletion K) (localTwist W h v)) :
    locJB W s hs hs0 v (Δ := Δ) (σ • p) = σ • locJB W s hs hs0 v (Δ := Δ) p := by
  have h2 := CoefMod.smul_tmul (MonoidAlgebra ℤ Δ)
    ((chiZ s hs hs0 (Δ := Δ)).comp (locMap K S₀ v : Gloc K v →* GKS K S₀)) (PtV W v) σ 1
    (twistPt (W.baseChange (v.adicCompletion K)) (algebraMap K (v.adicCompletion K) h)
      two_ne_zero (localSqrt_ne_zero s hs0 v) (localSqrt_sq s hs v) p)
  change (CoefMod.equiv _ ((chiZ s hs hs0 (Δ := Δ)).comp (locMap K S₀ v : Gloc K v →* GKS K S₀))
      (PtV W v) ((1 : MonoidAlgebra ℤ Δ) ⊗ₜ twistPt _ _ _ _ _ (σ • p)) : locL W s hs hs0 v Δ) =
    σ • CoefMod.equiv _ _ _ ((1 : MonoidAlgebra ℤ Δ) ⊗ₜ twistPt _ _ _ _ _ p)
  rw [h2, twistPt_smul, twistSign_localSqrt (S := S₀) s hs hs0 v σ, mul_one]
  congr 1
  rw [TensorProduct.tmul_smul]
  change _ = ((((intUnitsTo (MonoidAlgebra ℤ Δ)) (quadChar s hs hs0 (locMap K S₀ v σ)) :
    (MonoidAlgebra ℤ Δ)ˣ) : MonoidAlgebra ℤ Δ) ⊗ₜ[ℤ] _ : MonoidAlgebra ℤ Δ ⊗[ℤ] PtV W v)
  rw [show (((intUnitsTo (MonoidAlgebra ℤ Δ)) (quadChar s hs hs0 (locMap K S₀ v σ)) :
      (MonoidAlgebra ℤ Δ)ˣ) : MonoidAlgebra ℤ Δ) =
      ((quadChar s hs hs0 (locMap K S₀ v σ) : ℤˣ) : ℤ) • (1 : MonoidAlgebra ℤ Δ) by
    simp [intUnitsTo], ← TensorProduct.smul_tmul']

end Clauses

/-! ### The identification -/

section Main

variable {K : Type} [Field K] [NumberField K] {S S₀ : Set (HeightOneSpectrum (𝓞 K))}
  (hS : S₀ ⊆ S) (W : WeierstrassCurve K) [W.IsElliptic] (i : ℕ) [NeZero i] (s : KS K S₀) {h : K}
  (hs : s ^ 2 = algebraMap K (KS K S₀) h) (hs0 : s ≠ 0) (hFull : FullTorsion K S₀ W (2 ^ i))
  [TopologicalSpace (Acoef i)] [DiscreteTopology (Acoef i)]
  {Δ : Type} [CommGroup Δ] [Finite Δ] (π : GKS K S₀ →* Δ)

/-- **Clause 5**: `ψ(ι(ι_v t)) = j_B(t)` (PROVED; unfolding RC29's `genIotaBase`). -/
theorem clause5 (v : Places K S) (t : TorsAlg (v.1.adicCompletion K) (localTwist W h v.1) (2 ^ i)) :
    locPsi hS W s hs hs0 v.1 (ambIota hS W i s hs hs0 π
      (ofResModAdd (locMap K S v.1) (shapMod hS W i s hs hs0 π)
        (shapIota hS W i s hs hs0 hFull π v t))) =
      locJB W s hs hs0 v.1 (Δ := Δ) (t : PtAlg (v.1.adicCompletion K) (localTwist W h v.1)) := by
  change (1 : MonoidAlgebra ℤ Δ) ⊗ₜ compPt (S := S₀) W v.1
      (((compTorsEquiv W (2 ^ i) hFull v.1).symm
        (twistTors (W.baseChange (v.1.adicCompletion K)) (algebraMap K (v.1.adicCompletion K) h)
          two_ne_zero (localSqrt_ne_zero s hs0 v.1) (localSqrt_sq s hs v.1) (2 ^ i) t) :
          TorsT S₀ W i) : PtS K S₀ W) =
    (1 : MonoidAlgebra ℤ Δ) ⊗ₜ twistPt _ _ _ _ _ (t : PtAlg (v.1.adicCompletion K) (localTwist W h v.1))
  congr 1
  rw [← coe_compTors, ← compTorsEquiv_apply W (2 ^ i) hFull, AddEquiv.apply_symm_apply,
    coe_twistTors]

open scoped Classical in
/-- **`LocalTwistIdentification` for the actual data** (PROVED; tex 3251–3270, 3413–3438): at an
old place `v ∈ P` (where the Shapiro-level character is `χ_h`), for any normal `H` and character `θ`
trivial on `p_v(G_{K_v})`, with `ι` = `ambIota`, `ψ` = `locPsi`, `j_B` = `locJB` and `ι_v` the
Shapiro-level Kummer map.
**Superseded for the wiring** (see `H20Untwisted.lean`): the statement is valid, but with the
`χ_h`-twisted ambient module the norm relation needed by `h1_shapiro` holds only when `χ_h(σ_q) =
1`, and the point factor loses the text's sign `z = χ_h(σ_q) Ψ(σ_q)` (tex 3915, 4158–4172); wire the
untwisted instance instead (`localTwistIdentificationU`). -/
theorem localTwistIdentification_actual (v : Places K S) (H : Subgroup (GKS K S)) [H.Normal]
    (θ : GKS K S ⧸ H →* (MonoidAlgebra ℤ Δ)ˣ)
    (hθ : ∀ σ : Gloc K v.1, θ ((locMap K S v.1 σ : GKS K S) : GKS K S ⧸ H) = 1)
    [(localTwist W h v.1).IsElliptic] :
    LocalTwistIdentification (ambRho hS W s hs hs0 (Δ := Δ)) H θ (ambIota hS W i s hs hs0 π)
      (localTwist W h v.1) (2 ^ i) (locMap K S v.1 : Gloc K v.1 →* GKS K S)
      ((ofResModAdd (locMap K S v.1) (shapMod hS W i s hs hs0 π)).comp
        (shapIota hS W i s hs hs0 hFull π v))
      (locPsi hS W s hs hs0 v.1) (locJB W s hs hs0 v.1 (Δ := Δ)) := by
  refine ⟨fun x y hxy => ?_, fun x hx => ?_, fun σ x => ?_, fun σ p => ?_, fun t => ?_⟩
  · have hx := psi_iota_apply hS W i s hs hs0 π v.1 x
    have hy := psi_iota_apply hS W i s hs hs0 π v.1 y
    have hinj := Module.Flat.lTensor_preserves_injective_linearMap (M := MonoidAlgebra ℤ Δ)
      (psiIotaBase W i v.1 S₀) (psiIotaBase_injective W i v.1 (S₀ := S₀))
    exact hinj (hx.symm.trans (hxy.trans hy))
  · exact clause2 hS W i s hs hs0 hFull π v.1 x hx
  · have h1 : ((θ ((locMap K S v.1 σ : GKS K S) : GKS K S ⧸ H) : (MonoidAlgebra ℤ Δ)ˣ) :
        MonoidAlgebra ℤ Δ) = 1 := by rw [hθ σ, Units.val_one]
    change locPsi hS W s hs hs0 v.1 ((((θ ((locMap K S v.1 σ : GKS K S) : GKS K S ⧸ H) :
      (MonoidAlgebra ℤ Δ)ˣ) : MonoidAlgebra ℤ Δ) • ambRho hS W s hs hs0 (locMap K S v.1 σ)) x) = _
    rw [h1, one_smul]
    exact clause3_rho hS W s hs hs0 v.1 σ x
  · exact clause4 W s hs hs0 v.1 σ p
  · exact clause5 hS W i s hs hs0 hFull π v t

open scoped Classical in
/-- **`OldPlaceInput` for the actual data from the realization alone** (PROVED): at `v ∈ P`, the
input of `LocalIdentity.lean` / `H20Assembly.lean` reduces to the realization `hreal` of the
weighted sum by local points of the twist (the coefficient/twist identification is
`localTwistIdentification_actual`).
**Superseded for the wiring** (see `H20Untwisted.lean`): the statement is valid, but with the
`χ_h`-twisted ambient module the norm relation needed by `h1_shapiro` holds only when `χ_h(σ_q) =
1`, and the point factor loses the text's sign `z = χ_h(σ_q) Ψ(σ_q)` (tex 3915, 4158–4172); wire the
untwisted instance instead (`oldPlaceInputU`). -/
theorem oldPlaceInput_actual (v : Places K S) (H : Subgroup (GKS K S)) [H.Normal]
    [Fintype (GKS K S ⧸ H)] (r : GKS K S ⧸ H → GKS K S)
    (θ : GKS K S ⧸ H →* (MonoidAlgebra ℤ Δ)ˣ)
    (hθ : ∀ σ : Gloc K v.1, θ ((locMap K S v.1 σ : GKS K S) : GKS K S ⧸ H) = 1)
    [(localTwist W h v.1).IsElliptic] (y : ambD hS W s hs hs0 (Δ := Δ))
    {J : Type} (sJ : Finset J) (a : J → MonoidAlgebra ℤ Δ)
    (P : J → (localTwist W h v.1).toAffine.Point)
    (hreal : locPsi hS W s hs hs0 v.1 (wsum (ambRho hS W s hs hs0) H r θ y) =
      ∑ j ∈ sJ, a j • locJB W s hs hs0 v.1 (Δ := Δ)
        (basePt (v.1.adicCompletion K) (localTwist W h v.1) (P j))) :
    OldPlaceInput (ambRho hS W s hs hs0 (Δ := Δ)) H r θ v.1 (localTwist W h v.1) (2 ^ i)
      (shapIota hS W i s hs hs0 hFull π v) (ambIota hS W i s hs hs0 π) y :=
  ⟨locL W s hs hs0 v.1 Δ, inferInstance, inferInstance, inferInstance, inferInstance,
    locPsi hS W s hs hs0 v.1, locJB W s hs hs0 v.1 (Δ := Δ),
    localTwistIdentification_actual hS W i s hs hs0 hFull π v H θ hθ, J, sJ, a, P, hreal⟩

end Main

/-! ### The character `[π]` and the equivariance of `ι` -/

section Theta

variable {K : Type} [Field K] [NumberField K] {S S₀ : Set (HeightOneSpectrum (𝓞 K))}
  (hS : S₀ ⊆ S) (W : WeierstrassCurve K) [W.IsElliptic] (i : ℕ) [NeZero i] (s : KS K S₀) {h : K}
  (hs : s ^ 2 = algebraMap K (KS K S₀) h) (hs0 : s ≠ 0)
  [TopologicalSpace (Acoef i)] [DiscreteTopology (Acoef i)]
  {Δ : Type} [CommGroup Δ] [Finite Δ] (π : GKS K S₀ →* Δ)

/-- `π ∘ infl : G_{K,S} → Δ`. -/
abbrev piInfl : GKS K S →* Δ := π.comp (inflMap K hS : GKS K S →* GKS K S₀)

/-- **The character `[π]` of `G_{K,S}/ker(π ∘ infl)`** with values in `ℤ[Δ]^×`. Kind: definition.
**Superseded for the wiring** (see `H20Untwisted.lean`): the statement is valid, but with the
`χ_h`-twisted ambient module the norm relation needed by `h1_shapiro` holds only when `χ_h(σ_q) =
1`, and the point factor loses the text's sign `z = χ_h(σ_q) Ψ(σ_q)` (tex 3915, 4158–4172); wire the
untwisted instance instead (`thetaU`). -/
def thetaPi : GKS K S ⧸ (piInfl hS π).ker →* (MonoidAlgebra ℤ Δ)ˣ :=
  QuotientGroup.lift _ ((univChar Δ).comp (piInfl hS π)) (fun g hg => by
    rw [MonoidHom.mem_ker] at hg ⊢
    rw [MonoidHom.comp_apply, hg, map_one])

theorem thetaPi_mk (g : GKS K S) :
    thetaPi hS π (g : GKS K S ⧸ (piInfl hS π).ker) = univChar Δ (π (inflMap K hS g)) := rfl

/-- **`[π]` is trivial on the decomposition groups at `P`** (PROVED from the ELLIOT input). -/
theorem thetaPi_trivial {P : Set (HeightOneSpectrum (𝓞 K))} (ψ : Δ →* (Acoef i)ˣ)
    (hψ : Function.Injective ψ) (hΨ : PsiTrivialAt2N i π ψ P) {v : HeightOneSpectrum (𝓞 K)}
    (hv : v ∈ P) (σ : Gloc K v) :
    thetaPi hS π ((locMap K S v σ : GKS K S) : GKS K S ⧸ (piInfl hS π).ker) = 1 := by
  rw [thetaPi_mk, locMap_compat K hS v σ, pi_trivial_of_psi i π ψ hψ hΨ hv σ, map_one]

/-- `ι` on the uninflated modules. -/
def iota₀ : shapMod₀ W i s hs hs0 π →ₗ[MonoidAlgebra ℤ Δ] ambD₀ W s hs hs0 (Δ := Δ) :=
  LinearMap.baseChange (MonoidAlgebra ℤ Δ) (torsIncl K S₀ W i)

theorem iota₀_tmul (a : MonoidAlgebra ℤ Δ) (t : TorsT S₀ W i) :
    iota₀ W i s hs hs0 π (CoefMod.equiv _ _ _ (a ⊗ₜ t)) =
      CoefMod.equiv _ _ _ (a ⊗ₜ (t : PtS K S₀ W)) := rfl

/-- `ι₀` intertwines the actions up to `[π]`. Kind: PROVED. -/
theorem iota₀_smul (g₀ : GKS K S₀) (m : shapMod₀ W i s hs hs0 π) :
    iota₀ W i s hs hs0 π (g₀ • m) =
      ((univChar Δ (π g₀) : (MonoidAlgebra ℤ Δ)ˣ) : MonoidAlgebra ℤ Δ) •
        (g₀ • iota₀ W i s hs hs0 π m) := by
  refine TensorProduct.induction_on (R := ℤ) (M := MonoidAlgebra ℤ Δ) (N := TorsT S₀ W i)
    (motive := fun z => iota₀ W i s hs hs0 π (g₀ • (show shapMod₀ W i s hs hs0 π from z)) =
      ((univChar Δ (π g₀) : (MonoidAlgebra ℤ Δ)ˣ) : MonoidAlgebra ℤ Δ) •
        (g₀ • iota₀ W i s hs hs0 π (show shapMod₀ W i s hs hs0 π from z))) m ?_ ?_ ?_
  · change iota₀ W i s hs hs0 π (g₀ • (0 : shapMod₀ W i s hs hs0 π)) =
      _ • (g₀ • iota₀ W i s hs hs0 π 0)
    rw [smul_zero, map_zero, smul_zero, smul_zero]
  · intro a t
    have h1 := CoefMod.smul_tmul (MonoidAlgebra ℤ Δ) (alphaShap s hs hs0 π) (TorsT S₀ W i) g₀ a t
    have h2 := CoefMod.smul_tmul (MonoidAlgebra ℤ Δ) (chiZ s hs hs0 (Δ := Δ)) (PtS K S₀ W) g₀ a
      (t : PtS K S₀ W)
    change iota₀ W i s hs hs0 π (g₀ • CoefMod.equiv _ _ _ (a ⊗ₜ t)) =
      _ • (g₀ • iota₀ W i s hs hs0 π (CoefMod.equiv _ _ _ (a ⊗ₜ t)))
    rw [h1, iota₀_tmul, iota₀_tmul, h2]
    change (_ ⊗ₜ ((g₀ • t : TorsT S₀ W i) : PtS K S₀ W) : MonoidAlgebra ℤ Δ ⊗[ℤ] PtS K S₀ W) =
      ((univChar Δ (π g₀) : (MonoidAlgebra ℤ Δ)ˣ) : MonoidAlgebra ℤ Δ) •
        (_ ⊗ₜ (g₀ • (t : PtS K S₀ W)) : MonoidAlgebra ℤ Δ ⊗[ℤ] PtS K S₀ W)
    rw [TensorProduct.smul_tmul', smul_eq_mul]
    congr 1
    simp only [alphaShap, charMul_apply, Units.val_mul, MonoidHom.comp_apply, chiZ]
    ring
  · intro x y hx hy
    change iota₀ W i s hs hs0 π (g₀ • ((show shapMod₀ W i s hs hs0 π from x) +
        (show shapMod₀ W i s hs hs0 π from y))) =
      _ • (g₀ • iota₀ W i s hs hs0 π ((show shapMod₀ W i s hs hs0 π from x) +
        (show shapMod₀ W i s hs hs0 π from y)))
    rw [smul_add, map_add, hx, hy, map_add, smul_add, smul_add]

/-- **`ι` intertwines the Shapiro-level action with `R = [π] ρ`** (PROVED): the hypothesis `hιeq`
of `h1_shapiro` for `ι = ambIota`, `ρ = ambRho`, `θ = thetaPi`.
**Superseded for the wiring** (see `H20Untwisted.lean`): the statement is valid, but with the
`χ_h`-twisted ambient module the norm relation needed by `h1_shapiro` holds only when `χ_h(σ_q) =
1`, and the point factor loses the text's sign `z = χ_h(σ_q) Ψ(σ_q)` (tex 3915, 4158–4172); wire the
untwisted instance instead (`ambIotaU_equivariant`). -/
theorem ambIota_equivariant (g : GKS K S) (m : shapMod hS W i s hs hs0 π) :
    ambIota hS W i s hs hs0 π (g • m) =
      R (piInfl hS π).ker (ambRho hS W s hs hs0 (Δ := Δ)) (thetaPi hS π) g
        (ambIota hS W i s hs hs0 π m) :=
  iota₀_smul W i s hs hs0 π (inflMap K hS g) m

end Theta

end ZInQ.Contrib.CloudB3E2.NormCochain
