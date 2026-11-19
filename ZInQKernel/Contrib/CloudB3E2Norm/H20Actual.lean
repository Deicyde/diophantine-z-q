import ZInQKernel.Contrib.CloudB3E2Norm.H20Unramified
import ZInQKernel.Contrib.OneProof.RC.KummerMaps.ActualComplements
import ZInQKernel.Contrib.OneProof.RC.KummerMaps.IotaGen

/-!
# The coefficient push (H20) for the actual data: `H20CoefficientCompat` for RC29's conditions

Manuscript `diophantine_zq.tex`, tex 2724–2730 (`M_i = (T_2E ⊗ A_i)(χ_hΨ_i)`), 3203–3215 ("Under
Shapiro, followed by the equivariant coefficient map `E[2^m] ⊗ A[Δ_f] → (E[2^m] ⊗ A)(θ)`,
`v ⊗ [δ] ↦ θ(δ) v` (H20)"), 3257–3270 (the old Kummer conditions survive (H20)), 3471–3487 (the
unramified condition at the new place).

Setting. `Δ` is a finite abelian group with a homomorphism `π : G_{K,S₀} → Δ` with open kernel and
an injective character `ψ : Δ → A_i^×`; the reading of `shapMod₀` as the induced module needs `π`
surjective, which holds for the instance `Δ = im Ψ_i` of the section `Moving` (`movingPi`,
`movingPsi`, `moving_spec`, `h20ConditionsPush_moving`); the moving character is `Ψ_i = ψ ∘ π` and the actual
character is `α = χ_h · Ψ_i` (`alphaStage`). For the text, `Δ` is the image of `Ψ_i` (a quotient of
the ring class group `Δ_f`), so the Shapiro-level module below is the module induced from the field
`L` cut out by `Ψ_i` (a subfield of `H_f`), twisted by `χ_h`. Using `Δ_f` itself (with `ψ` not
injective) would need the Frobenius at the places above `2N` to be trivial in `Δ_f`, which the
ELLIOT input does not give; then the Kummer maps below are not equivariant, and the local Mackey
decomposition (`LocalIdentity.lean`, the orbit sums) replaces this file's direct comparison.

* **The Shapiro-level module** `shapMod = (ℤ[Δ] ⊗ E(K_{S₀})[2^i])(χ_h · [π])` (`CoefMod` over the group
  ring with the character `alphaShap = χ_h · (δ ↦ [δ]) ∘ π`): `g` acts by `χ_h(g)[π g] ⊗ g`, i.e.
  `E[2^i] ⊗ ℤ[Δ]` with the diagonal action (Galois on `E[2^i]`, left regular through `π` on the
  basis), twisted by `χ_h` — the induced module of Shapiro's lemma. `shapMod_finite` (PROVED).
* **The push** `shapPush`: `φ ⊗ id : ℤ[Δ] ⊗ T → A_i ⊗ T` with `φ = h20RingHom ψ`, `[δ] ↦ ψ(δ)`;
  `φ`-semilinear and `G_{K,S}`-equivariant into lane RC29's stage module `MinS hS W i α`
  (`shapPush_smul`, PROVED from `φ ∘ alphaShap = α`, `h20RingHom_alphaShap`).
* **ELLIOT input** `PsiTrivialAt2N` (tex 2729, 3431, 3500–3506: the moving character is trivial on
  the decomposition groups at `2N`, the places of `P`): `Ψ_i = ψ ∘ π` is trivial on `G_{K_v}` for
  `v ∈ P`. With `ψ` injective it makes the universal character trivial there
  (`isLocallyQuadAtGen_shap`), so the Shapiro-level Kummer map `shapIota` (lane RC29's `genIota`
  over `ℤ[Δ]`, inflated) is `G_{K_v}`-equivariant, and gives RC29's `hα` for the stage
  (`isLocallyQuadAt_stage`).
* **The Kummer maps match**: `shapIota_push` (PROVED): RC29's `kummerIotaS = push ∘ shapIota`
  (`1 ⊗ x ↦ φ(1) ⊗ x = 1 ⊗ x`).
* **The conditions**: `shapConditions` (Kummer at `P`, full at `S₀ − P`, for the Shapiro-level
  module) and `stageConditions` (lane RC29's `actLCondA` at the places of `S₀`: Kummer at `P`, full
  at `S₀ − P`).
* **`h20ConditionsPush_actual`** (PROVED): `H20ConditionsPush` for these conditions and the
  unramified conditions `urRep`/`urId` at a new place `w ∉ S₀` — the actual conditions survive
  (H20). **`hzR_stage_actual`** (PROVED): the Shapiro-level norm identity for the actual Selmer data
  gives the stage-level one with point factor `φ(e₁)`.
* **`Δ = im Ψ_i`** (section `Moving`): `movingPi` (surjective), `movingPsi` (injective),
  `moving_spec`, `psiTrivialAt2N_moving_iff`, **`h20ConditionsPush_moving`** (PROVED).
* Non-vacuity: `nonVacuity_psiTrivial` (the trivial `Δ`), `urRep_hyps_actual`.

What this does not do (named): (1) **the `Δ_f`-to-`im Ψ_i` bridge**: the manuscript's Shapiro-level
classes live over `A[Δ_f]` (induced from `H_f`); passing to `ℤ[im Ψ_i]` (induced from the field cut
out by `Ψ_i`) is a further coefficient push `[δ] ↦ [Ψ_i(δ)]` whose local conditions at `P` are the
orbit (local norm) conditions of `LocalIdentity.lean`, not the plain Kummer conditions used here;
(2) the Shapiro-level norm identity itself (the hypothesis `h₁` of `hzR_stage_actual`); that is the content of `TransferNorm.lean` … `LocalIdentity.lean` at the
coefficient ring `ℤ[Δ]` (conditional there on `LocalTwistIdentification` and the realization of the
actual points). Nor does it identify the cohomology of the Shapiro-level module with that of
`E[2^i]` over `G_L` (Shapiro's lemma itself, Tau Ceti's `ContCohomology/Shapiro`).

Kinds: definitions and PROVED; ELLIOT `PsiTrivialAt2N`; GLUE `FullTorsion` (lane RC28).
-/

noncomputable section

namespace ZInQ.Contrib.CloudB3E2.NormCochain

open ZInQ.Contrib.CloudB3RC53.PairedFunctional ZInQ.Contrib.CloudB3RC53.SelmerDuality
open ZInQ.Contrib.CloudB3RC53.UnramifiedComplex ZInQ.Contrib.CloudB3RC53.RankCounts
open ZInQ.Manuscript.RC.Wiring ZInQ.Manuscript.RC.SelmerComplex ZInQ.Manuscript.RC.CoefModules
open ZInQ.Manuscript.RC.KummerMaps
open ZInQ.Manuscript.RC.HeegnerAlgebra (Acoef)
open NumberField IsDedekindDomain TensorProduct

attribute [local instance] TopRep.distribMulAction TopRep.smulCommClass

set_option linter.unusedSectionVars false

/-! ### The group ring as a discrete coefficient ring -/

/-- The discrete topology on the group ring (the coefficient rings are discrete). -/
@[reducible] def groupRingTop (Δ : Type) [CommGroup Δ] : TopologicalSpace (MonoidAlgebra ℤ Δ) := ⊥

attribute [local instance] groupRingTop

instance (Δ : Type) [CommGroup Δ] : DiscreteTopology (MonoidAlgebra ℤ Δ) := ⟨rfl⟩

section Setting

variable {K : Type} [Field K] [NumberField K] {S S₀ : Set (HeightOneSpectrum (𝓞 K))}
  (hS : S₀ ⊆ S) (W : WeierstrassCurve K) [W.IsElliptic] (i : ℕ) [NeZero i] (s : KS K S₀) {h : K}
  (hs : s ^ 2 = algebraMap K (KS K S₀) h) (hs0 : s ≠ 0) (hFull : FullTorsion K S₀ W (2 ^ i))
  [TopologicalSpace (Acoef i)] [DiscreteTopology (Acoef i)]
  {Δ : Type} [CommGroup Δ] [Finite Δ] (π : GKS K S₀ →* Δ) (ψ : Δ →* (Acoef i)ˣ)

/-- **The Shapiro-level character** `χ_h · [π]` with values in `ℤ[Δ]^×`. Kind: definition. -/
def alphaShap : GKS K S₀ →* (MonoidAlgebra ℤ Δ)ˣ :=
  charMul ((intUnitsTo (MonoidAlgebra ℤ Δ)).comp (quadChar s hs hs0)) ((univChar Δ).comp π)

/-- **The stage character** `χ_h · ψ ∘ π` with values in `A_i^×`. Kind: definition. -/
def alphaStage : GKS K S₀ →* (Acoef i)ˣ :=
  charMul ((intUnitsTo (Acoef i)).comp (quadChar s hs hs0)) (ψ.comp π)

/-- **`φ ∘ alphaShap = alphaStage`** (PROVED). -/
theorem h20RingHom_alphaShap (g : GKS K S₀) :
    h20RingHom ψ ((alphaShap s hs hs0 π g : (MonoidAlgebra ℤ Δ)ˣ) : MonoidAlgebra ℤ Δ) =
      (alphaStage i s hs hs0 π ψ g : Acoef i) := by
  simp only [alphaShap, alphaStage, charMul_apply, MonoidHom.comp_apply, Units.val_mul,
    map_mul, h20RingHom_univChar]
  congr 1
  exact congrArg Units.val (units_map_intUnitsTo (h20RingHom ψ) _)

/-- The torsion module `E(K_{S₀})[2^i]`. -/
abbrev TorsT (S₀ : Set (HeightOneSpectrum (𝓞 K))) (W : WeierstrassCurve K) (i : ℕ) : Type :=
  TorsS K S₀ W ((2 ^ i : ℕ) : ℤ)

/-- **The Shapiro-level module** `(ℤ[Δ] ⊗ E[2^i])(χ_h · [π])` over `G_{K,S₀}`. Kind: definition. -/
abbrev shapMod₀ : Type := CoefMod (MonoidAlgebra ℤ Δ) (alphaShap s hs hs0 π) (TorsT S₀ W i)

/-- **The Shapiro-level module over `G_{K,S}`** (inflated, as RC29's `MinS`). Kind: definition. -/
abbrev shapMod : Type := InflMod hS (shapMod₀ W i s hs hs0 π)

/-- **The Shapiro-level module is finite** (PROVED): `ℤ[Δ] ⊗ T` is a finitely generated abelian
group killed by `2^i`. -/
instance shapMod₀_finite : Finite (shapMod₀ W i s hs hs0 π) := by
  have hT : ∀ t : TorsT S₀ W i, (2 ^ i : ℕ) • t = 0 := fun t =>
    Subtype.ext (AddSubgroup.torsionBy.nsmul_iff.1 t.2)
  have : Finite (TorsT S₀ W i) :=
    finite_torsS (by exact_mod_cast (pow_ne_zero i two_ne_zero : (2 : ℕ) ^ i ≠ 0))
  have : Module.Finite ℤ (TorsT S₀ W i) := Module.Finite.of_finite
  have hA : AddGroup.FG (MonoidAlgebra ℤ Δ) :=
    Module.Finite.iff_addGroup_fg.1 (MonoidAlgebra.moduleFinite (R := ℤ) (S := ℤ))
  have : Module.Finite ℤ (MonoidAlgebra ℤ Δ) := Module.Finite.iff_addGroup_fg.2 hA
  have : Module.Finite ℤ (MonoidAlgebra ℤ Δ ⊗[ℤ] TorsT S₀ W i) :=
    Module.Finite.tensorProduct ℤ _ _
  have : AddGroup.FG (MonoidAlgebra ℤ Δ ⊗[ℤ] TorsT S₀ W i) :=
    Module.Finite.iff_addGroup_fg.1 inferInstance
  have hkill : ∀ x : MonoidAlgebra ℤ Δ ⊗[ℤ] TorsT S₀ W i, (2 ^ i : ℕ) • x = 0 := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => exact smul_zero _
    | tmul a t => rw [← TensorProduct.tmul_smul, hT, TensorProduct.tmul_zero]
    | add x y hx hy => rw [smul_add, hx, hy, add_zero]
  show Finite (MonoidAlgebra ℤ Δ ⊗[ℤ] TorsT S₀ W i)
  exact AddCommGroup.finite_of_fg_isAddTorsion _ fun x =>
    isOfFinAddOrder_iff_nsmul_eq_zero.2 ⟨2 ^ i, pow_pos two_pos i, hkill x⟩

/-- **The push** `φ ⊗ id : (ℤ[Δ] ⊗ T)(χ_h[π]) → (A_i ⊗ T)(χ_hψπ)`, `φ = h20RingHom ψ` (tex 3207,
(H20)). Kind: definition. -/
def shapPush₀ :
    shapMod₀ W i s hs hs0 π →ₛₗ[h20RingHom ψ] Mcoef K S₀ W i (alphaStage i s hs hs0 π ψ) where
  toFun x := TensorProduct.map (h20RingHom ψ).toAddMonoidHom.toIntLinearMap LinearMap.id
    (show MonoidAlgebra ℤ Δ ⊗[ℤ] TorsT S₀ W i from x)
  map_add' x y := map_add _ _ _
  map_smul' a x := by
    change TensorProduct.map (h20RingHom ψ).toAddMonoidHom.toIntLinearMap LinearMap.id
        (a • (show MonoidAlgebra ℤ Δ ⊗[ℤ] TorsT S₀ W i from x)) =
      h20RingHom ψ a • TensorProduct.map (h20RingHom ψ).toAddMonoidHom.toIntLinearMap LinearMap.id
        (show MonoidAlgebra ℤ Δ ⊗[ℤ] TorsT S₀ W i from x)
    induction (show MonoidAlgebra ℤ Δ ⊗[ℤ] TorsT S₀ W i from x) using TensorProduct.induction_on with
    | zero => simp only [smul_zero, map_zero]
    | tmul b t =>
      rw [TensorProduct.smul_tmul', TensorProduct.map_tmul, TensorProduct.map_tmul,
        TensorProduct.smul_tmul']
      simp
    | add x y hx hy => rw [smul_add, map_add, hx, hy, map_add, smul_add]

theorem shapPush₀_tmul (a : MonoidAlgebra ℤ Δ) (t : TorsT S₀ W i) :
    shapPush₀ W i s hs hs0 π ψ (show shapMod₀ W i s hs hs0 π from a ⊗ₜ t) =
      (show Mcoef K S₀ W i (alphaStage i s hs hs0 π ψ) from h20RingHom ψ a ⊗ₜ t) :=
  TensorProduct.map_tmul _ _ _ _

/-- **The push is `G_{K,S₀}`-equivariant** (PROVED), from `φ ∘ alphaShap = alphaStage`. -/
theorem shapPush₀_smul (g : GKS K S₀) (x : shapMod₀ W i s hs hs0 π) :
    shapPush₀ W i s hs hs0 π ψ (g • x) = g • shapPush₀ W i s hs hs0 π ψ x := by
  induction (show MonoidAlgebra ℤ Δ ⊗[ℤ] TorsT S₀ W i from x) using TensorProduct.induction_on with
  | zero =>
    change shapPush₀ W i s hs hs0 π ψ (g • (0 : shapMod₀ W i s hs hs0 π)) =
      g • shapPush₀ W i s hs hs0 π ψ 0
    rw [smul_zero, map_zero, smul_zero]
  | tmul a t =>
    have h1 := CoefMod.smul_tmul (MonoidAlgebra ℤ Δ) (alphaShap s hs hs0 π) (TorsT S₀ W i) g a t
    have h2 := CoefMod.smul_tmul (Acoef i) (alphaStage i s hs hs0 π ψ) (TorsT S₀ W i) g
      (h20RingHom ψ a) t
    change shapPush₀ W i s hs hs0 π ψ (g • (CoefMod.equiv _ _ _ (a ⊗ₜ t))) =
      g • shapPush₀ W i s hs hs0 π ψ (CoefMod.equiv _ _ _ (a ⊗ₜ t))
    rw [h1]
    change shapPush₀ W i s hs hs0 π ψ (show shapMod₀ W i s hs hs0 π from _ ⊗ₜ _) =
      g • shapPush₀ W i s hs hs0 π ψ (show shapMod₀ W i s hs hs0 π from a ⊗ₜ t)
    rw [shapPush₀_tmul, shapPush₀_tmul]
    change _ = g • (CoefMod.equiv _ _ _ (h20RingHom ψ a ⊗ₜ t))
    rw [h2, map_mul, h20RingHom_alphaShap]
    rfl
  | add x y hx hy =>
    change shapPush₀ W i s hs hs0 π ψ (g • ((show shapMod₀ W i s hs hs0 π from x) +
        (show shapMod₀ W i s hs hs0 π from y))) = g • shapPush₀ W i s hs hs0 π ψ
        ((show shapMod₀ W i s hs hs0 π from x) + (show shapMod₀ W i s hs hs0 π from y))
    rw [smul_add, map_add, hx, hy, map_add, smul_add]

/-! #### The ELLIOT input and the local characters -/

/-- **ELLIOT input** (tex 2729, 3431, Proposition `ex:arith-moving-character`, tex 3500–3506: "the
moving character is trivial on the decomposition groups at `2N`"): the moving character
`Ψ_i = ψ ∘ π` is trivial on `G_{K_v}` for every `v ∈ P` (the places above `2N`).
Kind: ELLIOT (definition of the Prop). -/
def PsiTrivialAt2N (P : Set (HeightOneSpectrum (𝓞 K))) : Prop :=
  ∀ v ∈ P, ∀ σ : Gloc K v, ψ (π (locMap K S₀ v σ)) = 1

/-- With `ψ` injective, `Ψ_i` trivial at `v` makes `π` trivial on `G_{K_v}`. Kind: PROVED. -/
theorem pi_trivial_of_psi {P : Set (HeightOneSpectrum (𝓞 K))} (hψ : Function.Injective ψ)
    (hΨ : PsiTrivialAt2N i π ψ P) {v : HeightOneSpectrum (𝓞 K)} (hv : v ∈ P) (σ : Gloc K v) :
    π (locMap K S₀ v σ) = 1 :=
  hψ ((hΨ v hv σ).trans (map_one ψ).symm)

/-- **The Shapiro-level character is `χ_h` on the decomposition groups at `P`** (PROVED from the
ELLIOT input): RC29's `IsLocallyQuadAtGen` over `ℤ[Δ]`. -/
theorem isLocallyQuadAtGen_shap {P : Set (HeightOneSpectrum (𝓞 K))} (hψ : Function.Injective ψ)
    (hΨ : PsiTrivialAt2N i π ψ P) {v : HeightOneSpectrum (𝓞 K)} (hv : v ∈ P) :
    IsLocallyQuadAtGen (MonoidAlgebra ℤ Δ) (alphaShap s hs hs0 π) (quadChar s hs hs0) v := by
  intro σ
  rw [alphaShap, charMul_apply, MonoidHom.comp_apply, MonoidHom.comp_apply,
    pi_trivial_of_psi i π ψ hψ hΨ hv σ, map_one, mul_one]

/-- **The stage character is `χ_h` on the decomposition groups at `P`** (PROVED from the ELLIOT
input): RC29's hypothesis `hα` for `actLCondA`. -/
theorem isLocallyQuadAt_stage {P : Set (HeightOneSpectrum (𝓞 K))} (hΨ : PsiTrivialAt2N i π ψ P) :
    ∀ v ∈ P, IsLocallyQuadAt (S := S₀) i (alphaStage i s hs hs0 π ψ) (quadChar s hs hs0) v := by
  intro v hv σ
  rw [alphaStage, charMul_apply, MonoidHom.comp_apply, MonoidHom.comp_apply, hΨ v hv σ, mul_one]

/-- The characters `[π]` and `ψ ∘ π` have open kernels when `π` does. Kind: PROVED. -/
theorem isOpenKer_comp_pi {A : Type} [Monoid A] (hπ : IsOpen (π.ker : Set (GKS K S₀)))
    (u : Δ →* Aˣ) : IsOpenKer (u.comp π) :=
  ⟨Subgroup.isOpen_mono (fun g hg => by simp [MonoidHom.mem_ker.1 hg]) hπ⟩

theorem isOpenKer_alphaShap (hπ : IsOpen (π.ker : Set (GKS K S₀))) :
    IsOpenKer (alphaShap s hs hs0 π) := by
  have := isOpenKer_comp_pi π hπ (univChar Δ)
  have : IsOpenKer ((intUnitsTo (MonoidAlgebra ℤ Δ)).comp (quadChar s hs hs0)) :=
    ⟨Subgroup.isOpen_mono (fun g hg => by
      simp [MonoidHom.mem_ker.1 hg]) (quadChar_isOpenKer s hs hs0).isOpen_ker⟩
  exact isOpenKer_charMul _ _

theorem isOpenKer_alphaStage (hπ : IsOpen (π.ker : Set (GKS K S₀))) :
    IsOpenKer (alphaStage i s hs hs0 π ψ) := by
  have := isOpenKer_comp_pi π hπ ψ
  have : IsOpenKer ((intUnitsTo (Acoef i)).comp (quadChar s hs hs0)) :=
    ⟨Subgroup.isOpen_mono (fun g hg => by
      simp [MonoidHom.mem_ker.1 hg]) (quadChar_isOpenKer s hs hs0).isOpen_ker⟩
  exact isOpenKer_charMul _ _

/-! #### The push on the inflated modules and the Kummer maps -/

theorem shapPush₀_oneTmul (y : TorsT S₀ W i) :
    shapPush₀ W i s hs hs0 π ψ (oneTmul (MonoidAlgebra ℤ Δ) (alphaShap s hs hs0 π) (TorsT S₀ W i) y) =
      oneTmul (Acoef i) (alphaStage i s hs hs0 π ψ) (TorsT S₀ W i) y := by
  change shapPush₀ W i s hs hs0 π ψ (show shapMod₀ W i s hs hs0 π from (1 : MonoidAlgebra ℤ Δ) ⊗ₜ y) =
    (show Mcoef K S₀ W i (alphaStage i s hs hs0 π ψ) from (1 : Acoef i) ⊗ₜ y)
  rw [shapPush₀_tmul, map_one]

/-- **The push on the inflated modules** `shapMod → MinS` (the same map). Kind: definition. -/
def shapPush : shapMod hS W i s hs hs0 π →ₛₗ[h20RingHom ψ] MinS hS W i (alphaStage i s hs hs0 π ψ) :=
  shapPush₀ W i s hs hs0 π ψ

/-- **The push is `G_{K,S}`-equivariant** (PROVED). -/
theorem shapPush_smul (g : GKS K S) (m : shapMod hS W i s hs hs0 π) :
    shapPush hS W i s hs hs0 π ψ (g • m) = g • shapPush hS W i s hs hs0 π ψ m :=
  shapPush₀_smul W i s hs hs0 π ψ (inflMap K hS g) m

/-- **The Shapiro-level Kummer map** at `v ∈ S`: lane RC29's `genIota` over `ℤ[Δ]`, inflated to
`G_{K,S}` as RC29's `kummerIotaS` (`t ↦ 1 ⊗ j⁻¹(φ_q t)`). Kind: definition. -/
def shapIota (v : Places K S) :
    TorsAlg (v.1.adicCompletion K) (localTwist W h v.1) (2 ^ i) →+
      ResMod (locMap K S v.1) (shapMod hS W i s hs hs0 π) :=
  (toResModAdd (locMap K S v.1) (shapMod hS W i s hs hs0 π)).comp
    ((toResModAdd (inflMap K hS) (shapMod₀ W i s hs hs0 π)).comp
      (genIotaBase (MonoidAlgebra ℤ Δ) W (2 ^ i) s hs hs0 (alphaShap s hs hs0 π) hFull v.1))

/-- **The Shapiro-level Kummer map is `G_{K_v}`-equivariant** at the places where the
Shapiro-level character is `χ_h` (PROVED; RC29's proof of `kummerIotaS_smul`). -/
theorem shapIota_smul (v : Places K S)
    (hα : IsLocallyQuadAtGen (MonoidAlgebra ℤ Δ) (alphaShap s hs hs0 π) (quadChar s hs hs0) v.1)
    (σ : Gloc K v.1) (t : TorsAlg (v.1.adicCompletion K) (localTwist W h v.1) (2 ^ i)) :
    shapIota hS W i s hs hs0 hFull π v (σ • t) = σ • shapIota hS W i s hs hs0 hFull π v t := by
  change toResModAdd (locMap K S v.1) (shapMod hS W i s hs hs0 π)
      (toResModAdd (inflMap K hS) (shapMod₀ W i s hs hs0 π)
        (genIotaBase (MonoidAlgebra ℤ Δ) W (2 ^ i) s hs hs0 (alphaShap s hs hs0 π) hFull v.1
          (σ • t))) =
    σ • toResModAdd (locMap K S v.1) (shapMod hS W i s hs hs0 π)
      (toResModAdd (inflMap K hS) (shapMod₀ W i s hs hs0 π)
        (genIotaBase (MonoidAlgebra ℤ Δ) W (2 ^ i) s hs hs0 (alphaShap s hs hs0 π) hFull v.1 t))
  rw [smul_toResModAdd, smul_toResModAdd, locMap_compat K hS v.1 σ,
    genIotaBase_smul (MonoidAlgebra ℤ Δ) W (2 ^ i) s hs hs0 (alphaShap s hs hs0 π) hFull v.1 hα σ t]

/-- **RC29's Kummer map is the push of the Shapiro-level one** (PROVED; tex 3203–3215):
`kummerIotaS = push ∘ shapIota`, since `1 ⊗ x ↦ φ(1) ⊗ x = 1 ⊗ x`. -/
theorem shapIota_push (v : Places K S)
    (t : TorsAlg (v.1.adicCompletion K) (localTwist W h v.1) (2 ^ i)) :
    kummerIotaS hS W i s hs hs0 (alphaStage i s hs hs0 π ψ) hFull v t =
      resPush (h20RingHom ψ) (shapPush hS W i s hs hs0 π ψ) v.1
        (shapIota hS W i s hs hs0 hFull π v t) :=
  (shapPush₀_oneTmul W i s hs hs0 π ψ _).symm

end Setting

/-! ### The actual local conditions survive (H20) -/

section Conditions

variable {K : Type} [Field K] [NumberField K] {S S₀ : Set (HeightOneSpectrum (𝓞 K))}
  (hS : S₀ ⊆ S) (W : WeierstrassCurve K) [W.IsElliptic] (i : ℕ) [NeZero i] (s : KS K S₀) {h : K}
  (hs : s ^ 2 = algebraMap K (KS K S₀) h) (hs0 : s ≠ 0) (hFull : FullTorsion K S₀ W (2 ^ i))
  [TopologicalSpace (Acoef i)] [DiscreteTopology (Acoef i)]
  {Δ : Type} [CommGroup Δ] [Finite Δ] (π : GKS K S₀ →* Δ) (ψ : Δ →* (Acoef i)ˣ)
  [IsOpenKer (alphaShap s hs hs0 π)] [IsOpenKer (alphaStage i s hs hs0 π ψ)]
  (P : Set (HeightOneSpectrum (𝓞 K))) (hψ : Function.Injective ψ) (hΨ : PsiTrivialAt2N i π ψ P)

open scoped Classical in
/-- **The Shapiro-level local condition at an old place** `v ∈ S₀`: the Kummer condition with
`shapIota` at the places of `P`, the full condition at `S₀ − P` (as RC29's `actLCondA`).
Kind: definition. -/
def shapCond (v : Places K S₀) :
    CondAt K S (MonoidAlgebra ℤ Δ) (shapMod hS W i s hs hs0 π) ⟨v.1, hS v.2⟩ :=
  if hP : v.1 ∈ P then
    haveI := isElliptic_localTwist W (ne_zero_of_sqrt s hs hs0) v.1
    kummerAt ⟨v.1, hS v.2⟩ (localTwist W h v.1) (2 ^ i) (shapIota hS W i s hs hs0 hFull π _)
      (shapIota_smul hS W i s hs hs0 hFull π _
        (isLocallyQuadAtGen_shap i s hs hs0 π ψ hψ hΨ hP))
  else fullAt K S (MonoidAlgebra ℤ Δ) (shapMod hS W i s hs hs0 π) ⟨v.1, hS v.2⟩

/-- **The Shapiro-level old local conditions** (Kummer at `P`, full at `S₀ − P`).
Kind: definition. -/
def shapConditions : LocalConditions (MonoidAlgebra ℤ Δ) (GKS K S)
    (fun v : Places K S₀ => Gloc K v.1) (fun v => locMap K S v.1) (shapMod hS W i s hs hs0 π) where
  U v := (shapCond hS W i s hs hs0 hFull π ψ P hψ hΨ v).U
  i v := (shapCond hS W i s hs hs0 hFull π ψ P hψ hΨ v).i

/-- **Lane RC29's actual local conditions at the old places** `v ∈ S₀` (`actLCondA`: Kummer at `P`,
full at `S₀ − P`), in the format of the genuine old data. Kind: definition. -/
def stageConditions : LocalConditions (Acoef i) (GKS K S) (fun v : Places K S₀ => Gloc K v.1)
    (fun v => locMap K S v.1) (MinS hS W i (alphaStage i s hs hs0 π ψ)) where
  U v := (actLCondA hS W i s hs hs0 hFull P (alphaStage i s hs hs0 π ψ)
    (isLocallyQuadAt_stage i s hs hs0 π ψ hΨ) ⟨v.1, hS v.2⟩).U
  i v := (actLCondA hS W i s hs hs0 hFull P (alphaStage i s hs hs0 π ψ)
    (isLocallyQuadAt_stage i s hs hs0 π ψ hΨ) ⟨v.1, hS v.2⟩).i

open scoped Classical in
/-- **The old conditions are pushed** (PROVED; tex 3257–3270): at `v ∈ P` the Shapiro-level
Kummer condition is pushed into RC29's actual Kummer condition (`CondPushAt.kummer` with
`shapIota_push`), at `v ∈ S₀ − P` the full condition into the full condition. -/
theorem condPush_actual (v : Places K S₀) :
    Nonempty (CondPushAt (h20RingHom ψ) (shapPush hS W i s hs hs0 π ψ)
      (shapPush_smul hS W i s hs hs0 π ψ) v.1
      ((shapConditions hS W i s hs hs0 hFull π ψ P hψ hΨ).i v)
      ((stageConditions hS W i s hs hs0 hFull π ψ P hΨ).i v)) := by
  change Nonempty (CondPushAt (h20RingHom ψ) (shapPush hS W i s hs hs0 π ψ)
      (shapPush_smul hS W i s hs hs0 π ψ) v.1
      (shapCond hS W i s hs hs0 hFull π ψ P hψ hΨ v).i
      (actLCondA hS W i s hs hs0 hFull P (alphaStage i s hs hs0 π ψ)
        (isLocallyQuadAt_stage i s hs hs0 π ψ hΨ) ⟨v.1, hS v.2⟩).i)
  by_cases hP : v.1 ∈ P
  · rw [actLCondA_of_P hS W i s hs hs0 hFull P (alphaStage i s hs hs0 π ψ)
      (isLocallyQuadAt_stage i s hs hs0 π ψ hΨ) (v := ⟨v.1, hS v.2⟩) v.2 hP]
    unfold shapCond
    rw [dif_pos hP]
    haveI := isElliptic_localTwist W (ne_zero_of_sqrt s hs hs0) v.1
    exact ⟨CondPushAt.kummer (h20RingHom ψ) (shapPush hS W i s hs hs0 π ψ)
      (shapPush_smul hS W i s hs hs0 π ψ) v.1 _
      (shapIota_smul hS W i s hs hs0 hFull π ⟨v.1, hS v.2⟩
        (isLocallyQuadAtGen_shap i s hs hs0 π ψ hψ hΨ hP)) _
      (kummerIotaS_smul hS W i s hs hs0 (alphaStage i s hs hs0 π ψ) hFull ⟨v.1, hS v.2⟩
        (isLocallyQuadAt_stage i s hs hs0 π ψ hΨ v.1 hP))
      (shapIota_push hS W i s hs hs0 hFull π ψ ⟨v.1, hS v.2⟩)⟩
  · rw [actLCondA_of_notP hS W i s hs hs0 hFull P (alphaStage i s hs hs0 π ψ)
      (isLocallyQuadAt_stage i s hs hs0 π ψ hΨ) (v := ⟨v.1, hS v.2⟩) v.2 hP]
    unfold shapCond
    rw [dite_cond_eq_false (eq_false hP)]
    exact ⟨CondPushAt.full (h20RingHom ψ) (shapPush hS W i s hs hs0 π ψ)
      (shapPush_smul hS W i s hs hs0 π ψ) v.1⟩

/-- **The push of the unramified modules at a new place** `w ∉ S₀`: the push `shapPush₀` between
the `Gal(K_w^{ur}/K_w)`-representations `urRep` (lane RC26). Kind: definition. -/
def urPush (w : Places K S) (hw : w.1 ∉ S₀) :
    (urRep (MonoidAlgebra ℤ Δ) (shapMod₀ W i s hs hs0 π) (newPlace w hw)).V →ₛₗ[h20RingHom ψ]
      (urRep (Acoef i) (Mcoef K S₀ W i (alphaStage i s hs hs0 π ψ)) (newPlace w hw)).V :=
  shapPush₀ W i s hs hs0 π ψ

/-- The push of the unramified modules is equivariant. Kind: PROVED. -/
theorem urPush_smul (w : Places K S) (hw : w.1 ∉ S₀) (γ : GUr K w.1)
    (x : (urRep (MonoidAlgebra ℤ Δ) (shapMod₀ W i s hs hs0 π) (newPlace w hw)).V) :
    urPush W i s hs hs0 π ψ w hw (γ • x) = γ • urPush W i s hs hs0 π ψ w hw x :=
  shapPush₀_smul W i s hs hs0 π ψ (urFactor K (newPlace w hw) γ) x

/-- **`H20CoefficientCompat` for the actual data** (PROVED; tex 3203–3215, 3257–3270, 3471–3487):
at the old places, RC29's actual Kummer maps `kummerIotaS` are the push of the Shapiro-level
`shapIota`; at the new place `w ∉ S₀`, the push of the unramified modules commutes with RC26's
maps `urId`. -/
theorem h20CoefficientCompat_actual [∀ v : Places K S₀, (localTwist W h v.1).IsElliptic]
    (w : Places K S) (hw : w.1 ∉ S₀) :
    H20CoefficientCompat (h20RingHom ψ) (shapPush hS W i s hs hs0 π ψ) (2 ^ i)
      (fun v : Places K S₀ => localTwist W h v.1)
      (fun v => shapIota hS W i s hs hs0 hFull π ⟨v.1, hS v.2⟩)
      (fun v => kummerIotaS hS W i s hs hs0 (alphaStage i s hs hs0 π ψ) hFull ⟨v.1, hS v.2⟩) w
      (urRep (MonoidAlgebra ℤ Δ) (shapMod₀ W i s hs hs0 π) (newPlace w hw))
      (urRep (Acoef i) (Mcoef K S₀ W i (alphaStage i s hs hs0 π ψ)) (newPlace w hw))
      (urId hS (MonoidAlgebra ℤ Δ) (shapMod₀ W i s hs hs0 π) (newPlace w hw))
      (urId hS (Acoef i) (Mcoef K S₀ W i (alphaStage i s hs hs0 π ψ)) (newPlace w hw)) :=
  ⟨fun v t => shapIota_push hS W i s hs hs0 hFull π ψ ⟨v.1, hS v.2⟩ t,
    urPush W i s hs hs0 π ψ w hw, urPush_smul W i s hs hs0 π ψ w hw, fun _ => rfl⟩

/-- **The actual local conditions survive (H20)** (PROVED; tex 3203–3215, 3257–3270,
3471–3487): `H20ConditionsPush` from the Shapiro-level conditions (Kummer at `P`, full at
`S₀ − P`, unramified at `w`) to lane RC29's actual conditions `actLCondA` at the old places and
RC30's unramified condition `genuineιq` (`urRep`, `urId`) at a new place `w ∉ S₀`. Inputs: the
ELLIOT input `PsiTrivialAt2N` and `ψ` injective. -/
theorem h20ConditionsPush_actual (w : Places K S) (hw : w.1 ∉ S₀)
    [ContinuousSMul (GUr K w.1)
      (urRep (MonoidAlgebra ℤ Δ) (shapMod₀ W i s hs hs0 π) (newPlace w hw)).V]
    [ContinuousSMul (GUr K w.1)
      (urRep (Acoef i) (Mcoef K S₀ W i (alphaStage i s hs hs0 π ψ)) (newPlace w hw)).V] :
    H20ConditionsPush (h20RingHom ψ) (shapPush hS W i s hs hs0 π ψ)
      (shapPush_smul hS W i s hs hs0 π ψ) (shapConditions hS W i s hs hs0 hFull π ψ P hψ hΨ)
      (stageConditions hS W i s hs hs0 hFull π ψ P hΨ) w
      (genuineιq K S (MonoidAlgebra ℤ Δ) (shapMod hS W i s hs hs0 π) w
        (urRep (MonoidAlgebra ℤ Δ) (shapMod₀ W i s hs hs0 π) (newPlace w hw))
        (urId hS (MonoidAlgebra ℤ Δ) (shapMod₀ W i s hs hs0 π) (newPlace w hw))
        (urId_compat hS (MonoidAlgebra ℤ Δ) (shapMod₀ W i s hs hs0 π) w hw))
      (genuineιq K S (Acoef i) (MinS hS W i (alphaStage i s hs hs0 π ψ)) w
        (urRep (Acoef i) (Mcoef K S₀ W i (alphaStage i s hs hs0 π ψ)) (newPlace w hw))
        (urId hS (Acoef i) (Mcoef K S₀ W i (alphaStage i s hs hs0 π ψ)) (newPlace w hw))
        (urId_compat hS (Acoef i) (Mcoef K S₀ W i (alphaStage i s hs hs0 π ψ)) w hw)) := by
  exact ⟨⟨fun v => Classical.choice (condPush_actual hS W i s hs hs0 hFull π ψ P hψ hΨ v)⟩,
    ⟨wPushUr (h20RingHom ψ) (shapPush hS W i s hs hs0 π ψ) (shapPush_smul hS W i s hs hs0 π ψ) w
      (urRep (MonoidAlgebra ℤ Δ) (shapMod₀ W i s hs hs0 π) (newPlace w hw))
      (urRep (Acoef i) (Mcoef K S₀ W i (alphaStage i s hs hs0 π ψ)) (newPlace w hw))
      (urId hS (MonoidAlgebra ℤ Δ) (shapMod₀ W i s hs hs0 π) (newPlace w hw))
      (urId_compat hS (MonoidAlgebra ℤ Δ) (shapMod₀ W i s hs hs0 π) w hw)
      (urId hS (Acoef i) (Mcoef K S₀ W i (alphaStage i s hs hs0 π ψ)) (newPlace w hw))
      (urId_compat hS (Acoef i) (Mcoef K S₀ W i (alphaStage i s hs hs0 π ψ)) w hw)
      (urPush W i s hs hs0 π ψ w hw) (urPush_smul W i s hs hs0 π ψ w hw) (fun _ => rfl)⟩⟩

/-- **The stage norm identity for the actual data from the Shapiro-level one** (PROVED; tex
3203–3215, 3257–3290): for genuine relaxed and primitive classes over `ℤ[Δ]` with the Shapiro-level
conditions satisfying the norm identity with retained boundary and point factor `e₁` (for the text
`a_q − z − z⁻¹`, `z = χ_h(σ_q)[π σ_q]`), there are classes for lane RC29's actual conditions over
`A_i` satisfying it with point factor `φ(e₁)` (`a_q − z − z⁻¹`, `z = χ_h(σ_q) ψ(π σ_q)`,
`eq_transport`). -/
theorem hzR_stage_actual (w : Places K S) (hw : w.1 ∉ S₀)
    [ContinuousSMul (GUr K w.1)
      (urRep (MonoidAlgebra ℤ Δ) (shapMod₀ W i s hs hs0 π) (newPlace w hw)).V]
    [ContinuousSMul (GUr K w.1)
      (urRep (Acoef i) (Mcoef K S₀ W i (alphaStage i s hs hs0 π ψ)) (newPlace w hw)).V]
    (zR₁ : (selCx (stageRelaxed K S₀ S (MonoidAlgebra ℤ Δ) (shapMod hS W i s hs hs0 π)
      (shapConditions hS W i s hs hs0 hFull π ψ P hψ hΨ) w)).X 1)
    (zP₁ : (selCx (selRestrict (stageRelaxed K S₀ S (MonoidAlgebra ℤ Δ)
      (shapMod hS W i s hs hs0 π) (shapConditions hS W i s hs hs0 hFull π ψ P hψ hΨ) w)
      (primToRel (stageOld K S₀ S (MonoidAlgebra ℤ Δ) (shapMod hS W i s hs hs0 π)
        (shapConditions hS W i s hs hs0 hFull π ψ P hψ hΨ))
        (stageRes K S (MonoidAlgebra ℤ Δ) (shapMod hS W i s hs hs0 π) w)
        (genuineιq K S (MonoidAlgebra ℤ Δ) (shapMod hS W i s hs hs0 π) w
          (urRep (MonoidAlgebra ℤ Δ) (shapMod₀ W i s hs hs0 π) (newPlace w hw))
          (urId hS (MonoidAlgebra ℤ Δ) (shapMod₀ W i s hs hs0 π) (newPlace w hw))
          (urId_compat hS (MonoidAlgebra ℤ Δ) (shapMod₀ W i s hs hs0 π) w hw))))).X 1)
    (e₁ : MonoidAlgebra ℤ Δ)
    (h₁ : ∃ b, zR₁ = e₁ • (changeMap _ _).f 1 1 rfl zP₁ + (selCx _).d 0 1 rfl b) :
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
      ∃ b, zR₂ = h20RingHom ψ e₁ • (changeMap _ _).f 1 1 rfl zP₂ + (selCx _).d 0 1 rfl b :=
  hzR_stage_of_shapiro (h20RingHom ψ) (shapPush hS W i s hs hs0 π ψ)
    (shapPush_smul hS W i s hs hs0 π ψ) _ _ w _ _
    (h20ConditionsPush_actual hS W i s hs hs0 hFull π ψ P hψ hΨ w hw) zR₁ zP₁ e₁ h₁

end Conditions

/-! ### The moving character: `Δ = im Ψ_i` -/

section Moving

variable {K : Type} [Field K] [NumberField K] {S S₀ : Set (HeightOneSpectrum (𝓞 K))}
  (hS : S₀ ⊆ S) (W : WeierstrassCurve K) [W.IsElliptic] (i : ℕ) [NeZero i] (s : KS K S₀) {h : K}
  (hs : s ^ 2 = algebraMap K (KS K S₀) h) (hs0 : s ≠ 0) (hFull : FullTorsion K S₀ W (2 ^ i))
  [TopologicalSpace (Acoef i)] [DiscreteTopology (Acoef i)]
  (Ψ : GKS K S₀ →* (Acoef i)ˣ)

/-- The image `im Ψ_i` with its commutative group structure. -/
abbrev MovingΔ : Type := Ψ.range

/-- **`π = Ψ_i` onto its image** `Δ = im Ψ_i` (surjective). Kind: definition. -/
def movingPi : @MonoidHom (GKS K S₀) (MovingΔ i Ψ) _
    (@MulOneClass.toMulOne _ (@CommGroup.toGroup (MovingΔ i Ψ) inferInstance).toMulOneClass) :=
  { toFun := fun g => ⟨Ψ g, g, rfl⟩
    map_one' := Subtype.ext (map_one Ψ)
    map_mul' := fun a b => Subtype.ext (map_mul Ψ a b) }

/-- **`ψ` = the inclusion of the image** (injective). Kind: definition. -/
def movingPsi : @MonoidHom (MovingΔ i Ψ) (Acoef i)ˣ
    (@MulOneClass.toMulOne _ (@CommGroup.toGroup (MovingΔ i Ψ) inferInstance).toMulOneClass) _ :=
  { toFun := fun x => x.1
    map_one' := rfl
    map_mul' := fun _ _ => rfl }

/-- With `Δ = im Ψ_i`, `π` is surjective (so `shapMod₀` is the module induced from `ker Ψ_i`, the
absolute Galois group of the field cut out by `Ψ_i`, twisted by `χ_h`), `ψ` is injective, and
`ψ ∘ π = Ψ_i`. Kind: PROVED. -/
theorem moving_spec :
    Function.Surjective (movingPi i Ψ) ∧ Function.Injective (movingPsi i Ψ) ∧
      ∀ g, movingPsi i Ψ (movingPi i Ψ g) = Ψ g :=
  ⟨fun ⟨_, g, hg⟩ => ⟨g, Subtype.ext hg⟩, Subtype.val_injective, fun _ => rfl⟩

/-- **The ELLIOT input for `Δ = im Ψ_i`** is exactly "`Ψ_i` is trivial on the decomposition
groups at the places of `P`" (tex 2729, 3431, 3500–3506). Kind: PROVED. -/
theorem psiTrivialAt2N_moving_iff (P : Set (HeightOneSpectrum (𝓞 K))) :
    PsiTrivialAt2N i (movingPi i Ψ) (movingPsi i Ψ) P ↔
      ∀ v ∈ P, ∀ σ : Gloc K v, Ψ (locMap K S₀ v σ) = 1 :=
  Iff.rfl

/-- **The actual local conditions survive (H20), for the moving character** (PROVED):
`h20ConditionsPush_actual` with `Δ = im Ψ_i`, `π` its corestriction (surjective) and `ψ` the
inclusion (injective). The only inputs are the ELLIOT statement that `Ψ_i` is trivial on the
decomposition groups at `P`, `FullTorsion`, and the open kernels. -/
theorem h20ConditionsPush_moving
    [IsOpenKer (alphaShap s hs hs0 (movingPi i Ψ))]
    [IsOpenKer (alphaStage i s hs hs0 (movingPi i Ψ) (movingPsi i Ψ))]
    (P : Set (HeightOneSpectrum (𝓞 K)))
    (hΨ : ∀ v ∈ P, ∀ σ : Gloc K v, Ψ (locMap K S₀ v σ) = 1) (w : Places K S) (hw : w.1 ∉ S₀)
    [ContinuousSMul (GUr K w.1)
      (urRep (MonoidAlgebra ℤ (MovingΔ i Ψ)) (shapMod₀ W i s hs hs0 (movingPi i Ψ)) (newPlace w hw)).V]
    [ContinuousSMul (GUr K w.1) (urRep (Acoef i)
      (Mcoef K S₀ W i (alphaStage i s hs hs0 (movingPi i Ψ) (movingPsi i Ψ))) (newPlace w hw)).V] :
    H20ConditionsPush (h20RingHom (movingPsi i Ψ))
      (shapPush hS W i s hs hs0 (movingPi i Ψ) (movingPsi i Ψ))
      (shapPush_smul hS W i s hs hs0 (movingPi i Ψ) (movingPsi i Ψ))
      (shapConditions hS W i s hs hs0 hFull (movingPi i Ψ) (movingPsi i Ψ) P
        (moving_spec i Ψ).2.1 hΨ)
      (stageConditions hS W i s hs hs0 hFull (movingPi i Ψ) (movingPsi i Ψ) P hΨ) w
      (genuineιq K S (MonoidAlgebra ℤ (MovingΔ i Ψ)) (shapMod hS W i s hs hs0 (movingPi i Ψ)) w
        (urRep (MonoidAlgebra ℤ (MovingΔ i Ψ)) (shapMod₀ W i s hs hs0 (movingPi i Ψ)) (newPlace w hw))
        (urId hS (MonoidAlgebra ℤ (MovingΔ i Ψ)) (shapMod₀ W i s hs hs0 (movingPi i Ψ)) (newPlace w hw))
        (urId_compat hS (MonoidAlgebra ℤ (MovingΔ i Ψ)) (shapMod₀ W i s hs hs0 (movingPi i Ψ)) w hw))
      (genuineιq K S (Acoef i) (MinS hS W i (alphaStage i s hs hs0 (movingPi i Ψ) (movingPsi i Ψ)))
        w (urRep (Acoef i) (Mcoef K S₀ W i (alphaStage i s hs hs0 (movingPi i Ψ) (movingPsi i Ψ)))
          (newPlace w hw))
        (urId hS (Acoef i) (Mcoef K S₀ W i (alphaStage i s hs hs0 (movingPi i Ψ) (movingPsi i Ψ)))
          (newPlace w hw))
        (urId_compat hS (Acoef i)
          (Mcoef K S₀ W i (alphaStage i s hs hs0 (movingPi i Ψ) (movingPsi i Ψ))) w hw)) :=
  h20ConditionsPush_actual hS W i s hs hs0 hFull (movingPi i Ψ) (movingPsi i Ψ) P
    (moving_spec i Ψ).2.1 hΨ w hw

end Moving

/-! ### Non-vacuity -/

/-- **Non-vacuity of the ELLIOT input and of the injectivity hypothesis**: for the trivial group
`Δ = PUnit`, `π = 1`, `ψ = 1`, `ψ` is injective and `PsiTrivialAt2N` holds at every set of places.
Kind: PROVED. -/
theorem nonVacuity_psiTrivial {K : Type} [Field K] [NumberField K]
    {S₀ : Set (HeightOneSpectrum (𝓞 K))} (i : ℕ) (P : Set (HeightOneSpectrum (𝓞 K))) :
    Function.Injective (1 : PUnit →* (Acoef i)ˣ) ∧
      PsiTrivialAt2N i (1 : GKS K S₀ →* PUnit) (1 : PUnit →* (Acoef i)ˣ) P :=
  ⟨fun _ _ _ => Subsingleton.elim _ _, fun _ _ _ => rfl⟩

/-- **The unramified-module hypotheses of `h20ConditionsPush_actual` hold** (lane RC26's
`urRep_continuousSMul`). Kind: PROVED. -/
theorem urRep_hyps_actual {K : Type} [Field K] [NumberField K]
    {S S₀ : Set (HeightOneSpectrum (𝓞 K))} (W : WeierstrassCurve K) [W.IsElliptic] (i : ℕ)
    [NeZero i] (s : KS K S₀) {h : K} (hs : s ^ 2 = algebraMap K (KS K S₀) h) (hs0 : s ≠ 0)
    [TopologicalSpace (Acoef i)] [DiscreteTopology (Acoef i)]
    {Δ : Type} [CommGroup Δ] [Finite Δ] (π : GKS K S₀ →* Δ) (ψ : Δ →* (Acoef i)ˣ)
    [IsOpenKer (alphaShap s hs hs0 π)] [IsOpenKer (alphaStage i s hs hs0 π ψ)]
    (w : Places K S) (hw : w.1 ∉ S₀) :
    ContinuousSMul (GUr K w.1)
        (urRep (MonoidAlgebra ℤ Δ) (shapMod₀ W i s hs hs0 π) (newPlace w hw)).V ∧
      ContinuousSMul (GUr K w.1)
        (urRep (Acoef i) (Mcoef K S₀ W i (alphaStage i s hs hs0 π ψ)) (newPlace w hw)).V :=
  ⟨urRep_continuousSMul (MonoidAlgebra ℤ Δ) (shapMod₀ W i s hs hs0 π) (newPlace w hw),
    urRep_continuousSMul (Acoef i) (Mcoef K S₀ W i (alphaStage i s hs hs0 π ψ)) (newPlace w hw)⟩

end ZInQ.Contrib.CloudB3E2.NormCochain
