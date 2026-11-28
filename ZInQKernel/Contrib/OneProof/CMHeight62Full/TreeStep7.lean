import ZInQKernel.Contrib.OneProof.CMHeight62Full.TreeH2
import ZInQKernel.Contrib.OneProof.CMHeight62.Final
import ZInQKernel.Contrib.RC53Assist.HodgeLatticeIdeal.Fractional

/-!
# cmHeight62 (finite place), tree wiring: `localComparison`, `step7` and `CMHeight62` (H5)

The finite-place step `Step7` from the tree inputs already proved (H1, the N5-bridge chart at the
unit section, H2) and two inputs that are still open, stated as explicit hypotheses:

* `LocalAssemblyCore` (node L6 of the blueprint, edition 4): the per-place algebraic assembly.
  Given the N5-bridge chart at `e(s)`, a fraction field `Ω` of `𝒪_{𝒢,ξ}` with an isomorphism
  `Ψ : Ω ≅ F` of `L`-algebras onto a function field with a place `P` (degree one, the pole-space
  ladder, valuation ring the image of `𝒪_{𝒢,ξ}`, a uniformizer of `𝒪_{𝒢,ξ}` of order one, `Ψ`
  compatible with the structure maps), a Weierstrass equation `W(X', Y')` with poles of orders
  two and three at `P` only, and a germ `t_G ∈ 𝔪_ξ` with `Ψ t_G = −X'/Y'`, it produces the local
  comparison at `v` with `η = 𝒢.wedge ![t_G]`. Every input is local: the statement mentions only
  the group model, Mathlib and Tau Ceti places. It takes the generic data in the form H2 gives it
  (any fraction field of `𝒪_{𝒢,ξ}`); the passage to `FractionRing A` for the chart `A` is local
  (`valuation_omegaEquiv_le_one_iff_of_isLocalization`, the localization of node L2).
* `ShortComparisonInput` (the content of nodes H3 and H4): for the identity place `P` of `E_L`,
  the images `X', Y'` of the short coordinates satisfy the base-changed equation, have exact pole
  orders two and three at `P` and no other pole, and `t_L = −X'/Y'` in `K(E_L)`.

`localComparison` builds the data of `abs_norm_le_of_comparisons` at every finite place from
these, `step7` is `Step7`, and `cmHeight62_full` is `CMHeight62` through
`cmHeight62_of_step7'`.
-/

set_option autoImplicit false

noncomputable section

namespace ZInQ.Contrib.CMHeight62Full

open NumberField IsDedekindDomain AlgebraicGeometry CategoryTheory IsLocalRing
open ZInQ.DefFaltings
open HDec.CMBranch.CMjBridges (AbVarFunctionField abVarIdentity)
open ZInQ.Contrib.RC53Assist.HodgeLatticeIdeal
  (coefficientFractionalIdeal_ne_zero coefficientFractionalIdeal_coe)

attribute [local instance] HDec.CMBranch.CMjBridges.abVar_isIntegral
  HDec.CMBranch.CMjBridges.abVarFunctionFieldAlgebra

/-- **L6, the per-place algebraic assembly (edition 4), as a hypothesis.** -/
def LocalAssemblyCore : Prop :=
  ∀ {K : Type} [Field K] {E : PkgI3.AbVar K} {L : Type} [Field L] [NumberField L]
    [Algebra K L] (𝒢 : GroupModel E L) [IsDomain 𝒢.genStalk]
    [IsDiscreteValuationRing 𝒢.genStalk], IsProper 𝒢.G.hom →
    ∀ (v : HeightOneSpectrum (𝓞 L)) (s : Spec (CommRingCat.of (𝓞 L))),
      s.asIdeal = v.asIdeal →
    ∀ [IsDiscreteValuationRing (Localization.AtPrime s.asIdeal)] (A₀ : Type) [CommRing A₀]
      [Algebra (Localization.AtPrime s.asIdeal) A₀],
      Algebra.IsStandardSmoothOfRelativeDimension 1 (Localization.AtPrime s.asIdeal) A₀ →
    ∀ (σ : A₀ →ₐ[Localization.AtPrime s.asIdeal] Localization.AtPrime s.asIdeal)
      (φ : Localization.AtPrime (sectionPrime σ) ≃+*
        𝒢.G.left.presheaf.stalk (𝒢.unitSection s))
      (φη : Localization.AtPrime (RingHom.ker σ) ≃+* 𝒢.genStalk),
      (∀ a, (𝒢.unitSection.stalkMap s).hom (φ a) = specStalkEquiv s (localSection σ a)) →
      (∀ x : A₀, 𝒢.G.left.presheaf.stalkSpecializes (𝒢.specializes_genericUnit s)
        (φ (algebraMap A₀ _ x)) = φη (algebraMap A₀ _ x)) →
    ∀ (F : Type) [Field F] [Algebra L F] (Ω : Type) [Field Ω] [Algebra 𝒢.genStalk Ω]
      [IsFractionRing 𝒢.genStalk Ω] [Algebra L Ω] (Ψ : Ω ≃ₐ[L] F) (P : TauCeti.Place L F),
      P.degree = 1 →
      (∀ n : ℕ, 1 ≤ n →
        TauCeti.Divisor.dim (Finsupp.single P (n : ℤ) : TauCeti.Divisor L F) = n) →
      (∀ n : ℕ, FiniteDimensional L (poleSpace P n)) →
      (∀ g : Ω, P.valuation (Ψ g) ≤ 1 ↔ g ∈ (algebraMap 𝒢.genStalk Ω).range) →
      (∀ τ : 𝒢.genStalk, maximalIdeal 𝒢.genStalk = Ideal.span {τ} →
        P.valuation (Ψ (algebraMap 𝒢.genStalk Ω τ)) = WithZero.exp (-1 : ℤ)) →
      (∀ c : 𝓞 L, algebraMap 𝒢.genStalk Ω (𝒢.structMap c) =
        algebraMap L Ω (algebraMap (𝓞 L) L c)) →
    ∀ (W : WeierstrassCurve L) (X' Y' : F), (W.baseChange F).toAffine.Equation X' Y' →
      P.valuation X' = WithZero.exp (1 : ℤ) ^ 2 → P.valuation Y' = WithZero.exp (1 : ℤ) ^ 3 →
      X' ∈ regularAway P → Y' ∈ regularAway P →
    ∀ tG : maximalIdeal 𝒢.genStalk, Ψ (algebraMap 𝒢.genStalk Ω tG) = -X' / Y' →
      ∃ (W₀ : WeierstrassCurve L) (C : WeierstrassCurve.VariableChange L)
        (θ : 𝒢.hodgeSpace 1) (b : L),
        v.valuation L W₀.Δ = 1 ∧ C⁻¹ • W = W₀ ∧ θ ≠ 0 ∧
        (∀ m ∈ 𝒢.detLattice 1, ∃ r : L, v.valuation L r ≤ 1 ∧ m = r • θ) ∧
        𝒢.wedge ![tG] = b • θ ∧ v.valuation L (C.u : L) = v.valuation L b

/-- **H3 and H4, as a hypothesis.** For the identity place `P` of `E_L` (any place whose valuation
ring is the image of the stalk at the identity), the images `X', Y'` of the short coordinates of
`D` in `K(E_L)` satisfy the equation of `W_L`, have exact pole orders two and three at `P` and no
pole elsewhere, and `t_L = −X'/Y'`. -/
def ShortComparisonInput : Prop :=
  ∀ {K : Type} [Field K] [NumberField K] {L : Type} [Field L] [NumberField L] [Algebra K L]
    {E : PkgI3.AbVar K} (_ : E.dim = 1) (D : ZInQ.Contrib.CMHeight62.ShortData E)
    (𝒢 : GroupModel E L), D.etaW 𝒢 ≠ 0 →
    ∀ P : TauCeti.Place L (AbVarFunctionField (E.baseChange L)),
      (algebraMap ((E.baseChange L).X.left.presheaf.stalk (abVarIdentity (E.baseChange L)))
        (AbVarFunctionField (E.baseChange L))).range = P.integers.toSubring →
      ∃ X' Y' : AbVarFunctionField (E.baseChange L),
        ((D.W.map (algebraMap K L)).baseChange
          (AbVarFunctionField (E.baseChange L))).toAffine.Equation X' Y' ∧
        P.valuation X' = WithZero.exp (1 : ℤ) ^ 2 ∧
        P.valuation Y' = WithZero.exp (1 : ℤ) ^ 3 ∧
        X' ∈ regularAway P ∧ Y' ∈ regularAway P ∧
        algebraMap ((E.baseChange L).X.left.presheaf.stalk (abVarIdentity (E.baseChange L)))
          (AbVarFunctionField (E.baseChange L)) (D.tL (L := L)) = -X' / Y'

section Wiring

variable {K : Type} [Field K] [NumberField K] {L : Type} [Field L] [NumberField L]
  [Algebra K L] {E : PkgI3.AbVar K}

/-- **The local comparison at a finite place `v`** (the `hcmp v` input of
`abs_norm_le_of_comparisons`), from H1, the N5-bridge chart at the unit section, H2 and the two
open inputs. -/
theorem localComparison (hL6 : LocalAssemblyCore) (hshort : ShortComparisonInput)
    (hdim : E.dim = 1) (D : ZInQ.Contrib.CMHeight62.ShortData E) (𝒢 : GroupModel E L)
    (hprop : IsProper 𝒢.G.hom) (hη : D.etaW 𝒢 ≠ 0) (v : HeightOneSpectrum (𝓞 L)) :
    ∃ (W₀ : WeierstrassCurve L) (C : WeierstrassCurve.VariableChange L)
      (θ : 𝒢.hodgeSpace 1) (b : L),
      v.valuation L W₀.Δ = 1 ∧ C⁻¹ • D.W.map (algebraMap K L) = W₀ ∧ θ ≠ 0 ∧
      (∀ m ∈ 𝒢.detLattice 1, ∃ r : L, v.valuation L r ≤ 1 ∧ m = r • θ) ∧
      D.etaW 𝒢 = b • θ ∧ v.valuation L (C.u : L) = v.valuation L b := by
  obtain ⟨_, _⟩ := genStalk_isDiscreteValuationRing 𝒢 hdim
  let s : Spec (CommRingCat.of (𝓞 L)) := (⟨v.asIdeal, v.isPrime⟩ : PrimeSpectrum (𝓞 L))
  have hs : s.asIdeal = v.asIdeal := rfl
  have : IsDiscreteValuationRing (Localization.AtPrime s.asIdeal) :=
    IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain (𝓞 L) v.ne_bot _
  obtain ⟨A₀, _, _, hstd, σ, φ, φη, hφ, hsp⟩ := exists_localModel_genericUnit 𝒢 s
  letI := omegaAlgebra 𝒢 (FractionRing 𝒢.genStalk)
  obtain ⟨X', Y', heq, hX, hY, hXS, hYS, htL⟩ :=
    hshort hdim D 𝒢 hη (identityPlace L hdim) (identityPlace_spec hdim).2.1
  exact hL6 𝒢 hprop v s hs A₀ hstd σ φ φη hφ hsp _ (FractionRing 𝒢.genStalk)
    (omegaAlgEquiv 𝒢 (FractionRing 𝒢.genStalk)) (identityPlace L hdim)
    (identityPlace_spec hdim).1 (identityPlace_spec hdim).2.2
    (finiteDimensional_poleSpace_identityPlace hdim)
    (valuation_omegaEquiv_le_one_iff hdim 𝒢 (FractionRing 𝒢.genStalk))
    (fun _ hτ => valuation_omegaEquiv_eq_of_span_eq hdim 𝒢 (FractionRing 𝒢.genStalk) hτ)
    (algebraMap_structMap_omega 𝒢 (FractionRing 𝒢.genStalk))
    (D.W.map (algebraMap K L)) X' Y' heq hX hY hXS hYS (D.tG 𝒢)
    ((omegaEquiv_tG D 𝒢 (FractionRing 𝒢.genStalk)).trans htL)

end Wiring

/-- **`Step7`**, from the two open inputs: `abs_norm_le_of_comparisons` with
`J = coefficientFractionalIdeal 𝒢 hdim η_W hη` and the local comparison at every finite place. -/
theorem step7 (hL6 : LocalAssemblyCore) (hshort : ShortComparisonInput) :
    ZInQ.Contrib.CMHeight62.Step7 := by
  intro K _ _ L _ _ _ E hdim D 𝒢 hprop hη
  exact abs_norm_le_of_comparisons 𝒢 D.W D.W_Δ_ne_zero (D.etaW 𝒢)
    (coefficientFractionalIdeal_ne_zero 𝒢 hdim (D.etaW 𝒢) hη)
    (coefficientFractionalIdeal_coe 𝒢 hdim (D.etaW 𝒢) hη)
    (localComparison hL6 hshort hdim D 𝒢 hprop hη)

/-- **`CMHeight62`**, from the two open inputs, through `cmHeight62_of_step7'`. -/
theorem cmHeight62_full (hL6 : LocalAssemblyCore) (hshort : ShortComparisonInput) :
    HDec.CMBranch.CMHeight62 :=
  ZInQ.Contrib.CMHeight62.cmHeight62_of_step7' (step7 hL6 hshort)

end ZInQ.Contrib.CMHeight62Full
