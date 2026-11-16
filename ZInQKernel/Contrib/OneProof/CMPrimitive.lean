import ZInQKernel.Contrib.OneProof.MainCMPolar

/-!
# cm-primitive: the main theorem of CM for primitive CM types suffices

Task cm-primitive (2026-11-16). Report: `docs/research/cm-primitive.md`; log: `scratch/cm-primitive/log.md`.

mtcm-polar's leaves `MainCMPolar.MainTheoremCMPol` / `MainTheoremCMPolMax` state Shimura's main theorem of complex
multiplication (1971 Thm 5.15, 1998 Thm 18.6) for an arbitrary CM type `(E, Φ)`. The consumers use it on
`E = K(√2)` with the type `Φ = {φ₁, φ₂}` induced from `(K, κ)` (qmrec-printed's `qmReciprocityL3_of_printed`) and on
imaginary quadratic `K` (hcm-printed's `shimuraMainCM_of_printed`). If the print is read for primitive types only,
the first use is not covered. This file states the leaves for primitive types only (`IsPrimitiveType`,
`MainTheoremCMPolPrim`, `MainTheoremCMPolMaxPrim`), which are printed under every reading and are implied by
mtcm-polar's leaves, and proves the consumers from them:

* every CM type of an imaginary quadratic field is primitive (`isPrimitiveType_of_finrank_two`), and the induced
  type of `K(√2)` is not (`not_isPrimitiveType_PhiE`);
* both consumers need the main theorem only for imaginary quadratic fields, so an even weaker leaf suffices: the
  main theorem for CM elliptic curves (`MainTheoremCMPolQuad`, `MainTheoremCMPolMaxQuad`; Shimura 1971 Thm 5.4),
  implied by the primitive leaves (`polQuad_of_polPrim`, `polMaxQuad_of_polMaxPrim`);
* mtcm-polar's isogeny step on any class of CM types (`mainTheoremCMSignOn_of_polar`, a copy of
  `MainCMPolar.mainTheoremCMSign_of_polar` with the hypothesis `P E g Φ` threaded through);
* an abelian variety of the induced type is isogenous to `B²`, `B` of type `(K, κ)` (`exists_isogeny_EK`);
* the reduction from the induced type of `E = K(√2)` to `(K, κ)` (`mainTheoremCMEK_of_quad`): `B = ℂ/κ(N𝓞_K)`,
  the two homomorphisms `B → A`, `w ↦ θ(wΦ(1))`, `w ↦ θ(wΦ(√2))` (an isogeny `B² → A`), their conjugates, and
  `θ'(w₁Φ(1) + w₂Φ(√2)) = f₁^σ(θ'_B(w₁)) · f₂^σ(θ'_B(w₂))`; the reflex field of `(E, Φ)` is `κ(K)`
  (`QMRecPrinted.reflex_eq`) and its reflex norm is `𝔸_{K,f} → 𝔸_f ⊗ E` (`QMRecPrinted.reflexNorm_rhoK`),
  the reflex norm of `(K, κ)` followed by the inclusion;
* the consumers `qmReciprocityL3`, `rayClassCMAb` and `hCM = T5Glue.ShimuraMainCM`.

No statement of the kernel is changed. No `sorry`; axioms `propext`, `Classical.choice`, `Quot.sound`.
-/

noncomputable section

set_option linter.all false

namespace CMPrimitive

open ZInQ.HomLattice (IsAnalyticHom isAnalyticHom_of_unif analyticHomLiftC_of_leaf isAnalyticHom_comp
  isUniformization_iff map_nsmul_of_hom)
open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory
open NumberField IsDedekindDomain QMRecPrinted ShimuraCFT RayClassCFT
open TauCeti.ClassFieldTheory TauCeti.GlobalNumberFields
open ZInQ.LeafPush2 (CPts IsUniformization cptObj)
open MainCMPolar
open scoped TensorProduct ComplexConjugate

/-! ## §1 Primitive CM types -/

section Primitive

variable {E : Type} [Field E]

/-- **`(E, Φ)` is primitive** (Shimura–Taniyama §8.2, Shimura 1998 §8.2, Milne *Complex multiplication* §1; numbers
UNVERIFIED): `Φ` is not induced from a CM type of a proper subfield, i.e. the only subfield `F ⊆ E` such that every
embedding `ψ : E → ℂ` agreeing on `F` with some `φᵢ` is some `φⱼ` (`Φ = {ψ : ψ|_F ∈ Φ|_F}`) is `F = E`. (Such an `F`
is automatically a CM field when `Φ ∩ Φ̄ = ∅`: if `F` were totally real, `φ̄ᵢ|_F = φᵢ|_F` would put `φ̄ᵢ` in `Φ`.) -/
def IsPrimitiveType {g : ℕ} (Φ : Fin g → E →+* ℂ) : Prop :=
  ∀ F : Subfield E, (∀ (i : Fin g) (ψ : E →+* ℂ), (∀ x ∈ F, ψ x = Φ i x) → ∃ j, ψ = Φ j) → F = ⊤

variable [NumberField E]

/-- **Every CM type of an imaginary quadratic field is primitive** (`[E : ℚ] = 2`: the only proper subfield is `ℚ`,
on which `φ` and `φ̄` agree). -/
theorem isPrimitiveType_of_finrank_two (Φ : Fin 1 → E →+* ℂ) (h2 : Module.finrank ℚ E = 2)
    (hinj : Function.Injective (Sum.elim Φ fun i => (starRingEnd ℂ).comp (Φ i))) : IsPrimitiveType Φ := by
  intro F hF
  let F' : IntermediateField ℚ E := F.toIntermediateField (fun q => by
    rw [eq_ratCast]; exact SubfieldClass.ratCast_mem F q)
  haveI : IsSimpleOrder (IntermediateField ℚ E) :=
    IntermediateField.isSimpleOrder_of_finrank_prime ℚ E (by rw [h2]; exact Nat.prime_two)
  rcases IsSimpleOrder.eq_bot_or_eq_top F' with hb | ht
  · exfalso
    obtain ⟨j, hj⟩ := hF 0 ((starRingEnd ℂ).comp (Φ 0)) (fun x hx => by
      have hx' : x ∈ (⊥ : IntermediateField ℚ E) := by rw [← hb]; exact hx
      obtain ⟨q, rfl⟩ := IntermediateField.mem_bot.1 hx'
      simp [eq_ratCast])
    have := hinj (a₁ := Sum.inr 0) (a₂ := Sum.inl j) (by simpa using hj)
    exact Sum.inr_ne_inl this
  · ext x
    simp only [Subfield.mem_top, iff_true]
    have hx : x ∈ (⊤ : IntermediateField ℚ E) := trivial
    rw [← ht] at hx
    exact hx

end Primitive

/-! ## §2 The leaves for primitive types and the glue target -/

section Leaves

open MonObj

/-- **LEAF `MainTheoremCMPolMaxPrim` (the main theorem of complex multiplication for polarized CM abelian varieties
of primitive type `(E, Φ; 𝔞, ζ)`, `𝔞` a fractional `𝓞_E`-ideal, in Shimura's normalization; printed form).**
mtcm-polar's `MainCMPolar.MainTheoremCMPolMax` with the one added hypothesis `IsPrimitiveType Φ`.

*Published statement*: G. Shimura, *Introduction to the arithmetic theory of automorphic functions* (1971), §5.5,
Thm 5.15; G. Shimura, *Abelian varieties with complex multiplication and modular functions* (1998), §18,
Thm 18.6; Shimura–Taniyama (1961), §§13–14 (numbers UNVERIFIED; this host has no network). Under the strictest reading
these are stated for primitive types (the setting of Shimura–Taniyama's and Shimura's chapters on the reflex
field); this leaf assumes exactly that.

*Form*: as `MainTheoremCMPolMax` (polarized structures, `𝓞_E`-ideal lattices, `ε = 1`, the clauses on `C^σ`, on
the type of `(A^σ, θ')` and the uniqueness of `θ'` dropped), plus primitivity. Implied by `MainTheoremCMPolMax`
(`polMaxPrim_of_polMax`). -/
def MainTheoremCMPolMaxPrim : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (g : ℕ) (Φ : Fin g → E →+* ℂ),
    Module.finrank ℚ E = 2 * g →
    Function.Injective (Sum.elim Φ fun i => (starRingEnd ℂ).comp (Φ i)) →
    IsPrimitiveType Φ →
  ∀ (Er : Type) [Field Er] [NumberField Er] (κr : Er →+* ℂ),
    κr.fieldRange = Subfield.closure (Set.range fun e : E => ∑ i, Φ i e) →
  ∀ (n : ℕ) (ρ : Er →ₐ[ℚ] Matrix (Fin n) (Fin n) E) (j : (Fin n → E) →+ (Fin g → ℂ)),
    IsReflexModel Φ κr ρ j →
  ∀ (σ : ℂ ≃+* ℂ) (s : IdeleGroup (𝓞 Er) Er), ArtinCondC κr σ s →
  ∀ (A : PkgI3.AbVar ℂ), A.dim = (g : WithBot ℕ∞) →
  ∀ (𝔞 : AddSubgroup E) (θ : (Fin g → ℂ) → CPts A (RingHom.id ℂ)),
    IsUniformization (RingHom.id ℂ) (cmLat Φ 𝔞) θ → IsOfType Φ 𝔞 θ →
    IsOLattice 𝔞 → (∃ ζ : E, IsRiemannDatum Φ 𝔞 ζ) →
  ∀ (A' : PkgI3.AbVar ℂ) (h : A'.X.left ⟶ A.X.left),
    IsPullback h A'.X.hom A.X.hom (Spec.map (CommRingCat.ofHom (σ : ℂ →+* ℂ))) →
    (1 : CPts A' (RingHom.id ℂ)).left ≫ h =
      Spec.map (CommRingCat.ofHom (σ : ℂ →+* ℂ)) ≫ (1 : CPts A (RingHom.id ℂ)).left →
  ∃ θ' : (Fin g → ℂ) → CPts A' (RingHom.id ℂ),
    IsUniformization (RingHom.id ℂ)
      (cmLat Φ (latAct ((reflexNorm ρ (IdeleGroup.toFiniteIdele (𝓞 Er) Er s) : (AQ ⊗[ℚ] E)ˣ) : AQ ⊗[ℚ] E) 𝔞))
      θ' ∧
    ∀ x y : E,
      ((reflexNorm ρ (IdeleGroup.toFiniteIdele (𝓞 Er) Er s) : (AQ ⊗[ℚ] E)ˣ) : AQ ⊗[ℚ] E) * (1 ⊗ₜ y) - 1 ⊗ₜ x ∈
          latHat 𝔞 →
        (θ' (cmVec Φ y)).left ≫ h = Spec.map (CommRingCat.ofHom (σ : ℂ →+* ℂ)) ≫ (θ (cmVec Φ x)).left

/-- `MainTheoremCMPolMaxPrim` at a sign `ε`: mtcm-polar's `MainCMPolar.MainTheoremCMPolSign ε` with the one added
hypothesis `IsPrimitiveType Φ`. -/
def MainTheoremCMPolPrimSign (ε : ℤˣ) : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (g : ℕ) (Φ : Fin g → E →+* ℂ),
    Module.finrank ℚ E = 2 * g →
    Function.Injective (Sum.elim Φ fun i => (starRingEnd ℂ).comp (Φ i)) →
    IsPrimitiveType Φ →
  ∀ (Er : Type) [Field Er] [NumberField Er] (κr : Er →+* ℂ),
    κr.fieldRange = Subfield.closure (Set.range fun e : E => ∑ i, Φ i e) →
  ∀ (n : ℕ) (ρ : Er →ₐ[ℚ] Matrix (Fin n) (Fin n) E) (j : (Fin n → E) →+ (Fin g → ℂ)),
    IsReflexModel Φ κr ρ j →
  ∀ (σ : ℂ ≃+* ℂ) (s : IdeleGroup (𝓞 Er) Er), ArtinCondC κr σ s →
  ∀ (A : PkgI3.AbVar ℂ), A.dim = (g : WithBot ℕ∞) →
  ∀ (𝔞 : AddSubgroup E) (θ : (Fin g → ℂ) → CPts A (RingHom.id ℂ)),
    IsUniformization (RingHom.id ℂ) (cmLat Φ 𝔞) θ → IsOfType Φ 𝔞 θ →
    IsOLattice 𝔞 → (∃ ζ : E, IsRiemannDatum Φ 𝔞 ζ) →
  ∀ (A' : PkgI3.AbVar ℂ) (h : A'.X.left ⟶ A.X.left),
    IsPullback h A'.X.hom A.X.hom (Spec.map (CommRingCat.ofHom (σ : ℂ →+* ℂ))) →
    (1 : CPts A' (RingHom.id ℂ)).left ≫ h =
      Spec.map (CommRingCat.ofHom (σ : ℂ →+* ℂ)) ≫ (1 : CPts A (RingHom.id ℂ)).left →
  ∃ θ' : (Fin g → ℂ) → CPts A' (RingHom.id ℂ),
    IsUniformization (RingHom.id ℂ)
      (cmLat Φ (latAct ((reflexNorm ρ (IdeleGroup.toFiniteIdele (𝓞 Er) Er s) ^ (ε : ℤ) :
        (AQ ⊗[ℚ] E)ˣ) : AQ ⊗[ℚ] E) 𝔞)) θ' ∧
    ∀ x y : E,
      ((reflexNorm ρ (IdeleGroup.toFiniteIdele (𝓞 Er) Er s) ^ (ε : ℤ) : (AQ ⊗[ℚ] E)ˣ) : AQ ⊗[ℚ] E) *
          (1 ⊗ₜ y) - 1 ⊗ₜ x ∈ latHat 𝔞 →
        (θ' (cmVec Φ y)).left ≫ h = Spec.map (CommRingCat.ofHom (σ : ℂ →+* ℂ)) ≫ (θ (cmVec Φ x)).left

/-- **LEAF `MainTheoremCMPolPrim` (the polarized, maximal-order print for primitive types with the sign of the Artin
map left open; printed form).** `∃ ε, MainTheoremCMPolPrimSign ε`: mtcm-polar's `MainCMPolar.MainTheoremCMPol`
with the one added hypothesis `IsPrimitiveType Φ`. Same published statements as `MainTheoremCMPolMaxPrim`; implied
by it (`polPrim_of_polMaxPrim`) and by `MainCMPolar.MainTheoremCMPol` (`polPrim_of_pol`). -/
def MainTheoremCMPolPrim : Prop := ∃ ε : ℤˣ, MainTheoremCMPolPrimSign ε

/-- **Glue target** `MainTheoremCMSignPrim ε`: hcm-printed's `HcmPrinted.MainTheoremCMSign ε` (every lattice, no
polarization) with the one added hypothesis `IsPrimitiveType Φ`. -/
def MainTheoremCMSignPrim (ε : ℤˣ) : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (g : ℕ) (Φ : Fin g → E →+* ℂ),
    Module.finrank ℚ E = 2 * g →
    Function.Injective (Sum.elim Φ fun i => (starRingEnd ℂ).comp (Φ i)) →
    IsPrimitiveType Φ →
  ∀ (Er : Type) [Field Er] [NumberField Er] (κr : Er →+* ℂ),
    κr.fieldRange = Subfield.closure (Set.range fun e : E => ∑ i, Φ i e) →
  ∀ (n : ℕ) (ρ : Er →ₐ[ℚ] Matrix (Fin n) (Fin n) E) (j : (Fin n → E) →+ (Fin g → ℂ)),
    IsReflexModel Φ κr ρ j →
  ∀ (σ : ℂ ≃+* ℂ) (s : IdeleGroup (𝓞 Er) Er), ArtinCondC κr σ s →
  ∀ (A : PkgI3.AbVar ℂ), A.dim = (g : WithBot ℕ∞) →
  ∀ (𝔞 : AddSubgroup E) (θ : (Fin g → ℂ) → CPts A (RingHom.id ℂ)),
    IsUniformization (RingHom.id ℂ) (cmLat Φ 𝔞) θ → IsOfType Φ 𝔞 θ →
  ∀ (A' : PkgI3.AbVar ℂ) (h : A'.X.left ⟶ A.X.left),
    IsPullback h A'.X.hom A.X.hom (Spec.map (CommRingCat.ofHom (σ : ℂ →+* ℂ))) →
    (1 : CPts A' (RingHom.id ℂ)).left ≫ h =
      Spec.map (CommRingCat.ofHom (σ : ℂ →+* ℂ)) ≫ (1 : CPts A (RingHom.id ℂ)).left →
  ∃ θ' : (Fin g → ℂ) → CPts A' (RingHom.id ℂ),
    IsUniformization (RingHom.id ℂ)
      (cmLat Φ (latAct ((reflexNorm ρ (IdeleGroup.toFiniteIdele (𝓞 Er) Er s) ^ (ε : ℤ) :
        (AQ ⊗[ℚ] E)ˣ) : AQ ⊗[ℚ] E) 𝔞)) θ' ∧
    ∀ x y : E,
      ((reflexNorm ρ (IdeleGroup.toFiniteIdele (𝓞 Er) Er s) ^ (ε : ℤ) : (AQ ⊗[ℚ] E)ˣ) : AQ ⊗[ℚ] E) *
          (1 ⊗ₜ y) - 1 ⊗ₜ x ∈ latHat 𝔞 →
        (θ' (cmVec Φ y)).left ≫ h = Spec.map (CommRingCat.ofHom (σ : ℂ →+* ℂ)) ≫ (θ (cmVec Φ x)).left

theorem polPrimSign_one_of_polMaxPrim (h : MainTheoremCMPolMaxPrim) : MainTheoremCMPolPrimSign 1 := by
  intro E _ _ _ g Φ hdeg hinj hprim Er _ _ κr hκ n ρ j hρ σ s hs A hA 𝔞 θ hθ htype hO hζ A' hh hpb hone
  simp only [Units.val_one, zpow_one]
  exact h E g Φ hdeg hinj hprim Er κr hκ n ρ j hρ σ s hs A hA 𝔞 θ hθ htype hO hζ A' hh hpb hone

theorem polPrim_of_polMaxPrim (h : MainTheoremCMPolMaxPrim) : MainTheoremCMPolPrim :=
  ⟨1, polPrimSign_one_of_polMaxPrim h⟩

/-- The primitive leaf is implied by mtcm-polar's leaf (it only adds a hypothesis). -/
theorem polMaxPrim_of_polMax (h : MainTheoremCMPolMax) : MainTheoremCMPolMaxPrim :=
  fun E _ _ _ g Φ hdeg hinj _ Er _ _ κr hκ n ρ j hρ σ s hs A hA 𝔞 θ hθ htype hO hζ A' hh hpb hone =>
    h E g Φ hdeg hinj Er κr hκ n ρ j hρ σ s hs A hA 𝔞 θ hθ htype hO hζ A' hh hpb hone

theorem polPrimSign_of_polSign {ε : ℤˣ} (h : MainTheoremCMPolSign ε) : MainTheoremCMPolPrimSign ε :=
  fun E _ _ _ g Φ hdeg hinj _ Er _ _ κr hκ n ρ j hρ σ s hs A hA 𝔞 θ hθ htype hO hζ A' hh hpb hone =>
    h E g Φ hdeg hinj Er κr hκ n ρ j hρ σ s hs A hA 𝔞 θ hθ htype hO hζ A' hh hpb hone

/-- The primitive leaf is implied by mtcm-polar's leaf (it only adds a hypothesis). -/
theorem polPrim_of_pol (h : MainTheoremCMPol) : MainTheoremCMPolPrim := by
  obtain ⟨ε, h⟩ := h
  exact ⟨ε, polPrimSign_of_polSign h⟩

/-- The glue target is implied by hcm-printed's statement (it only adds a hypothesis). -/
theorem signPrim_of_sign {ε : ℤˣ} (h : HcmPrinted.MainTheoremCMSign ε) : MainTheoremCMSignPrim ε :=
  fun E _ _ _ g Φ hdeg hinj _ Er _ _ κr hκ n ρ j hρ σ s hs A hA 𝔞 θ hθ htype A' hh hpb hone =>
    h E g Φ hdeg hinj Er κr hκ n ρ j hρ σ s hs A hA 𝔞 θ hθ htype A' hh hpb hone

/-! ### The imaginary quadratic case (`g = 1`, CM elliptic curves)

Both consumers use the main theorem only for imaginary quadratic fields: hcm-printed's at `(QNeg m, κ)`, and the
reduction `mainTheoremCMEK_of_quad` below at `(K, κ)`. So an even weaker form of the leaf suffices: the main theorem
for `[E : ℚ] = 2` (every such type is primitive, `isPrimitiveType_of_finrank_two`). -/

/-- **LEAF `MainTheoremCMPolMaxQuad` (the main theorem of complex multiplication for CM elliptic curves with
`𝓞_E`-ideal lattices, in Shimura's normalization; printed form).** mtcm-polar's `MainCMPolar.MainTheoremCMPolMax`
with the one added hypothesis `Module.finrank ℚ E = 2` (so `g = 1`: `E` imaginary quadratic, `A` an elliptic curve
with CM by `𝓞_E`).

*Published statement*: G. Shimura, *Introduction to the arithmetic theory of automorphic functions* (1971), Thm 5.4
(elliptic curves: `ξ(u)^σ = ξ'(s⁻¹u)` for `σ = [s, K]`, `ξ' : ℂ/s⁻¹𝔞 ≅ E^σ`); S. Lang, *Elliptic functions*, Ch. 10,
Thm 3; J. Silverman, *Advanced topics in the arithmetic of elliptic curves*, Thm II.8.2 (numbers UNVERIFIED). In
dimension `1` the reflex field of `(E, {κ})` is `κ(E)`, the reflex norm is the identity (`reflexNorm_rho1`), every
lattice of the leaf is an `𝓞_E`-ideal and every elliptic curve is polarized, so the leaf is the printed statement
for `𝓞_E`-ideal lattices with the clauses on the type of `(E^σ, θ')` and the uniqueness of `θ'` dropped. Implied by
`MainTheoremCMPolMaxPrim` (`polMaxQuad_of_polMaxPrim`). -/
def MainTheoremCMPolMaxQuad : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (g : ℕ) (Φ : Fin g → E →+* ℂ),
    Module.finrank ℚ E = 2 * g →
    Function.Injective (Sum.elim Φ fun i => (starRingEnd ℂ).comp (Φ i)) →
    Module.finrank ℚ E = 2 →
  ∀ (Er : Type) [Field Er] [NumberField Er] (κr : Er →+* ℂ),
    κr.fieldRange = Subfield.closure (Set.range fun e : E => ∑ i, Φ i e) →
  ∀ (n : ℕ) (ρ : Er →ₐ[ℚ] Matrix (Fin n) (Fin n) E) (j : (Fin n → E) →+ (Fin g → ℂ)),
    IsReflexModel Φ κr ρ j →
  ∀ (σ : ℂ ≃+* ℂ) (s : IdeleGroup (𝓞 Er) Er), ArtinCondC κr σ s →
  ∀ (A : PkgI3.AbVar ℂ), A.dim = (g : WithBot ℕ∞) →
  ∀ (𝔞 : AddSubgroup E) (θ : (Fin g → ℂ) → CPts A (RingHom.id ℂ)),
    IsUniformization (RingHom.id ℂ) (cmLat Φ 𝔞) θ → IsOfType Φ 𝔞 θ →
    IsOLattice 𝔞 → (∃ ζ : E, IsRiemannDatum Φ 𝔞 ζ) →
  ∀ (A' : PkgI3.AbVar ℂ) (h : A'.X.left ⟶ A.X.left),
    IsPullback h A'.X.hom A.X.hom (Spec.map (CommRingCat.ofHom (σ : ℂ →+* ℂ))) →
    (1 : CPts A' (RingHom.id ℂ)).left ≫ h =
      Spec.map (CommRingCat.ofHom (σ : ℂ →+* ℂ)) ≫ (1 : CPts A (RingHom.id ℂ)).left →
  ∃ θ' : (Fin g → ℂ) → CPts A' (RingHom.id ℂ),
    IsUniformization (RingHom.id ℂ)
      (cmLat Φ (latAct ((reflexNorm ρ (IdeleGroup.toFiniteIdele (𝓞 Er) Er s) : (AQ ⊗[ℚ] E)ˣ) : AQ ⊗[ℚ] E) 𝔞))
      θ' ∧
    ∀ x y : E,
      ((reflexNorm ρ (IdeleGroup.toFiniteIdele (𝓞 Er) Er s) : (AQ ⊗[ℚ] E)ˣ) : AQ ⊗[ℚ] E) * (1 ⊗ₜ y) - 1 ⊗ₜ x ∈
          latHat 𝔞 →
        (θ' (cmVec Φ y)).left ≫ h = Spec.map (CommRingCat.ofHom (σ : ℂ →+* ℂ)) ≫ (θ (cmVec Φ x)).left

/-- `MainTheoremCMPolMaxQuad` at a sign `ε`. -/
def MainTheoremCMPolQuadSign (ε : ℤˣ) : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (g : ℕ) (Φ : Fin g → E →+* ℂ),
    Module.finrank ℚ E = 2 * g →
    Function.Injective (Sum.elim Φ fun i => (starRingEnd ℂ).comp (Φ i)) →
    Module.finrank ℚ E = 2 →
  ∀ (Er : Type) [Field Er] [NumberField Er] (κr : Er →+* ℂ),
    κr.fieldRange = Subfield.closure (Set.range fun e : E => ∑ i, Φ i e) →
  ∀ (n : ℕ) (ρ : Er →ₐ[ℚ] Matrix (Fin n) (Fin n) E) (j : (Fin n → E) →+ (Fin g → ℂ)),
    IsReflexModel Φ κr ρ j →
  ∀ (σ : ℂ ≃+* ℂ) (s : IdeleGroup (𝓞 Er) Er), ArtinCondC κr σ s →
  ∀ (A : PkgI3.AbVar ℂ), A.dim = (g : WithBot ℕ∞) →
  ∀ (𝔞 : AddSubgroup E) (θ : (Fin g → ℂ) → CPts A (RingHom.id ℂ)),
    IsUniformization (RingHom.id ℂ) (cmLat Φ 𝔞) θ → IsOfType Φ 𝔞 θ →
    IsOLattice 𝔞 → (∃ ζ : E, IsRiemannDatum Φ 𝔞 ζ) →
  ∀ (A' : PkgI3.AbVar ℂ) (h : A'.X.left ⟶ A.X.left),
    IsPullback h A'.X.hom A.X.hom (Spec.map (CommRingCat.ofHom (σ : ℂ →+* ℂ))) →
    (1 : CPts A' (RingHom.id ℂ)).left ≫ h =
      Spec.map (CommRingCat.ofHom (σ : ℂ →+* ℂ)) ≫ (1 : CPts A (RingHom.id ℂ)).left →
  ∃ θ' : (Fin g → ℂ) → CPts A' (RingHom.id ℂ),
    IsUniformization (RingHom.id ℂ)
      (cmLat Φ (latAct ((reflexNorm ρ (IdeleGroup.toFiniteIdele (𝓞 Er) Er s) ^ (ε : ℤ) :
        (AQ ⊗[ℚ] E)ˣ) : AQ ⊗[ℚ] E) 𝔞)) θ' ∧
    ∀ x y : E,
      ((reflexNorm ρ (IdeleGroup.toFiniteIdele (𝓞 Er) Er s) ^ (ε : ℤ) : (AQ ⊗[ℚ] E)ˣ) : AQ ⊗[ℚ] E) *
          (1 ⊗ₜ y) - 1 ⊗ₜ x ∈ latHat 𝔞 →
        (θ' (cmVec Φ y)).left ≫ h = Spec.map (CommRingCat.ofHom (σ : ℂ →+* ℂ)) ≫ (θ (cmVec Φ x)).left

/-- **LEAF `MainTheoremCMPolQuad` (the main theorem of CM for CM elliptic curves with `𝓞_E`-ideal lattices, sign of
the Artin map left open; printed form).** `∃ ε, MainTheoremCMPolQuadSign ε`. Same sources as
`MainTheoremCMPolMaxQuad`; implied by it and by `MainTheoremCMPolPrim` (`polQuad_of_polPrim`). -/
def MainTheoremCMPolQuad : Prop := ∃ ε : ℤˣ, MainTheoremCMPolQuadSign ε

/-- **Glue target** `MainTheoremCMSignQuad ε`: `HcmPrinted.MainTheoremCMSign ε` for imaginary quadratic `E`. -/
def MainTheoremCMSignQuad (ε : ℤˣ) : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (g : ℕ) (Φ : Fin g → E →+* ℂ),
    Module.finrank ℚ E = 2 * g →
    Function.Injective (Sum.elim Φ fun i => (starRingEnd ℂ).comp (Φ i)) →
    Module.finrank ℚ E = 2 →
  ∀ (Er : Type) [Field Er] [NumberField Er] (κr : Er →+* ℂ),
    κr.fieldRange = Subfield.closure (Set.range fun e : E => ∑ i, Φ i e) →
  ∀ (n : ℕ) (ρ : Er →ₐ[ℚ] Matrix (Fin n) (Fin n) E) (j : (Fin n → E) →+ (Fin g → ℂ)),
    IsReflexModel Φ κr ρ j →
  ∀ (σ : ℂ ≃+* ℂ) (s : IdeleGroup (𝓞 Er) Er), ArtinCondC κr σ s →
  ∀ (A : PkgI3.AbVar ℂ), A.dim = (g : WithBot ℕ∞) →
  ∀ (𝔞 : AddSubgroup E) (θ : (Fin g → ℂ) → CPts A (RingHom.id ℂ)),
    IsUniformization (RingHom.id ℂ) (cmLat Φ 𝔞) θ → IsOfType Φ 𝔞 θ →
  ∀ (A' : PkgI3.AbVar ℂ) (h : A'.X.left ⟶ A.X.left),
    IsPullback h A'.X.hom A.X.hom (Spec.map (CommRingCat.ofHom (σ : ℂ →+* ℂ))) →
    (1 : CPts A' (RingHom.id ℂ)).left ≫ h =
      Spec.map (CommRingCat.ofHom (σ : ℂ →+* ℂ)) ≫ (1 : CPts A (RingHom.id ℂ)).left →
  ∃ θ' : (Fin g → ℂ) → CPts A' (RingHom.id ℂ),
    IsUniformization (RingHom.id ℂ)
      (cmLat Φ (latAct ((reflexNorm ρ (IdeleGroup.toFiniteIdele (𝓞 Er) Er s) ^ (ε : ℤ) :
        (AQ ⊗[ℚ] E)ˣ) : AQ ⊗[ℚ] E) 𝔞)) θ' ∧
    ∀ x y : E,
      ((reflexNorm ρ (IdeleGroup.toFiniteIdele (𝓞 Er) Er s) ^ (ε : ℤ) : (AQ ⊗[ℚ] E)ˣ) : AQ ⊗[ℚ] E) *
          (1 ⊗ₜ y) - 1 ⊗ₜ x ∈ latHat 𝔞 →
        (θ' (cmVec Φ y)).left ≫ h = Spec.map (CommRingCat.ofHom (σ : ℂ →+* ℂ)) ≫ (θ (cmVec Φ x)).left

theorem polQuadSign_of_polPrimSign {ε : ℤˣ} (h : MainTheoremCMPolPrimSign ε) : MainTheoremCMPolQuadSign ε := by
  intro E _ _ _ g Φ hdeg hinj h2 Er _ _ κr hκ n ρ j hρ σ s hs A hA 𝔞 θ hθ htype hO hζ A' hh hpb hone
  obtain rfl : g = 1 := by omega
  exact h E 1 Φ hdeg hinj (isPrimitiveType_of_finrank_two Φ h2 hinj) Er κr hκ n ρ j hρ σ s hs A hA 𝔞 θ hθ htype
    hO hζ A' hh hpb hone

/-- The quadratic leaf is implied by the primitive leaf. -/
theorem polMaxQuad_of_polMaxPrim (h : MainTheoremCMPolMaxPrim) : MainTheoremCMPolMaxQuad := by
  intro E _ _ _ g Φ hdeg hinj h2 Er _ _ κr hκ n ρ j hρ σ s hs A hA 𝔞 θ hθ htype hO hζ A' hh hpb hone
  obtain rfl : g = 1 := by omega
  exact h E 1 Φ hdeg hinj (isPrimitiveType_of_finrank_two Φ h2 hinj) Er κr hκ n ρ j hρ σ s hs A hA 𝔞 θ hθ htype
    hO hζ A' hh hpb hone

/-- The quadratic leaf is implied by the primitive leaf. -/
theorem polQuad_of_polPrim (h : MainTheoremCMPolPrim) : MainTheoremCMPolQuad := by
  obtain ⟨ε, h⟩ := h
  exact ⟨ε, polQuadSign_of_polPrimSign h⟩

theorem polQuadSign_one_of_polMaxQuad (h : MainTheoremCMPolMaxQuad) : MainTheoremCMPolQuadSign 1 := by
  intro E _ _ _ g Φ hdeg hinj h2 Er _ _ κr hκ n ρ j hρ σ s hs A hA 𝔞 θ hθ htype hO hζ A' hh hpb hone
  simp only [Units.val_one, zpow_one]
  exact h E g Φ hdeg hinj h2 Er κr hκ n ρ j hρ σ s hs A hA 𝔞 θ hθ htype hO hζ A' hh hpb hone

theorem polQuad_of_polMaxQuad (h : MainTheoremCMPolMaxQuad) : MainTheoremCMPolQuad :=
  ⟨1, polQuadSign_one_of_polMaxQuad h⟩

theorem signQuad_of_signPrim {ε : ℤˣ} (h : MainTheoremCMSignPrim ε) : MainTheoremCMSignQuad ε := by
  intro E _ _ _ g Φ hdeg hinj h2 Er _ _ κr hκ n ρ j hρ σ s hs A hA 𝔞 θ hθ htype A' hh hpb hone
  obtain rfl : g = 1 := by omega
  exact h E 1 Φ hdeg hinj (isPrimitiveType_of_finrank_two Φ h2 hinj) Er κr hκ n ρ j hρ σ s hs A hA 𝔞 θ hθ htype
    A' hh hpb hone

/-! ### Generic forms (a class of CM types), for the copied proof -/

/-- A class of CM types `(E, Φ)`. -/
abbrev CMTypeClass : Type 1 :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (g : ℕ), (Fin g → E →+* ℂ) → Prop

/-- `MainCMPolar.MainTheoremCMPolSign ε` restricted to a class `P` of CM types. -/
def MainTheoremCMPolOn (P : CMTypeClass) (ε : ℤˣ) : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (g : ℕ) (Φ : Fin g → E →+* ℂ),
    Module.finrank ℚ E = 2 * g →
    Function.Injective (Sum.elim Φ fun i => (starRingEnd ℂ).comp (Φ i)) →
    P E g Φ →
  ∀ (Er : Type) [Field Er] [NumberField Er] (κr : Er →+* ℂ),
    κr.fieldRange = Subfield.closure (Set.range fun e : E => ∑ i, Φ i e) →
  ∀ (n : ℕ) (ρ : Er →ₐ[ℚ] Matrix (Fin n) (Fin n) E) (j : (Fin n → E) →+ (Fin g → ℂ)),
    IsReflexModel Φ κr ρ j →
  ∀ (σ : ℂ ≃+* ℂ) (s : IdeleGroup (𝓞 Er) Er), ArtinCondC κr σ s →
  ∀ (A : PkgI3.AbVar ℂ), A.dim = (g : WithBot ℕ∞) →
  ∀ (𝔞 : AddSubgroup E) (θ : (Fin g → ℂ) → CPts A (RingHom.id ℂ)),
    IsUniformization (RingHom.id ℂ) (cmLat Φ 𝔞) θ → IsOfType Φ 𝔞 θ →
    IsOLattice 𝔞 → (∃ ζ : E, IsRiemannDatum Φ 𝔞 ζ) →
  ∀ (A' : PkgI3.AbVar ℂ) (h : A'.X.left ⟶ A.X.left),
    IsPullback h A'.X.hom A.X.hom (Spec.map (CommRingCat.ofHom (σ : ℂ →+* ℂ))) →
    (1 : CPts A' (RingHom.id ℂ)).left ≫ h =
      Spec.map (CommRingCat.ofHom (σ : ℂ →+* ℂ)) ≫ (1 : CPts A (RingHom.id ℂ)).left →
  ∃ θ' : (Fin g → ℂ) → CPts A' (RingHom.id ℂ),
    IsUniformization (RingHom.id ℂ)
      (cmLat Φ (latAct ((reflexNorm ρ (IdeleGroup.toFiniteIdele (𝓞 Er) Er s) ^ (ε : ℤ) :
        (AQ ⊗[ℚ] E)ˣ) : AQ ⊗[ℚ] E) 𝔞)) θ' ∧
    ∀ x y : E,
      ((reflexNorm ρ (IdeleGroup.toFiniteIdele (𝓞 Er) Er s) ^ (ε : ℤ) : (AQ ⊗[ℚ] E)ˣ) : AQ ⊗[ℚ] E) *
          (1 ⊗ₜ y) - 1 ⊗ₜ x ∈ latHat 𝔞 →
        (θ' (cmVec Φ y)).left ≫ h = Spec.map (CommRingCat.ofHom (σ : ℂ →+* ℂ)) ≫ (θ (cmVec Φ x)).left

/-- `HcmPrinted.MainTheoremCMSign ε` restricted to a class `P` of CM types. -/
def MainTheoremCMSignOn (P : CMTypeClass) (ε : ℤˣ) : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (g : ℕ) (Φ : Fin g → E →+* ℂ),
    Module.finrank ℚ E = 2 * g →
    Function.Injective (Sum.elim Φ fun i => (starRingEnd ℂ).comp (Φ i)) →
    P E g Φ →
  ∀ (Er : Type) [Field Er] [NumberField Er] (κr : Er →+* ℂ),
    κr.fieldRange = Subfield.closure (Set.range fun e : E => ∑ i, Φ i e) →
  ∀ (n : ℕ) (ρ : Er →ₐ[ℚ] Matrix (Fin n) (Fin n) E) (j : (Fin n → E) →+ (Fin g → ℂ)),
    IsReflexModel Φ κr ρ j →
  ∀ (σ : ℂ ≃+* ℂ) (s : IdeleGroup (𝓞 Er) Er), ArtinCondC κr σ s →
  ∀ (A : PkgI3.AbVar ℂ), A.dim = (g : WithBot ℕ∞) →
  ∀ (𝔞 : AddSubgroup E) (θ : (Fin g → ℂ) → CPts A (RingHom.id ℂ)),
    IsUniformization (RingHom.id ℂ) (cmLat Φ 𝔞) θ → IsOfType Φ 𝔞 θ →
  ∀ (A' : PkgI3.AbVar ℂ) (h : A'.X.left ⟶ A.X.left),
    IsPullback h A'.X.hom A.X.hom (Spec.map (CommRingCat.ofHom (σ : ℂ →+* ℂ))) →
    (1 : CPts A' (RingHom.id ℂ)).left ≫ h =
      Spec.map (CommRingCat.ofHom (σ : ℂ →+* ℂ)) ≫ (1 : CPts A (RingHom.id ℂ)).left →
  ∃ θ' : (Fin g → ℂ) → CPts A' (RingHom.id ℂ),
    IsUniformization (RingHom.id ℂ)
      (cmLat Φ (latAct ((reflexNorm ρ (IdeleGroup.toFiniteIdele (𝓞 Er) Er s) ^ (ε : ℤ) :
        (AQ ⊗[ℚ] E)ˣ) : AQ ⊗[ℚ] E) 𝔞)) θ' ∧
    ∀ x y : E,
      ((reflexNorm ρ (IdeleGroup.toFiniteIdele (𝓞 Er) Er s) ^ (ε : ℤ) : (AQ ⊗[ℚ] E)ˣ) : AQ ⊗[ℚ] E) *
          (1 ⊗ₜ y) - 1 ⊗ₜ x ∈ latHat 𝔞 →
        (θ' (cmVec Φ y)).left ≫ h = Spec.map (CommRingCat.ofHom (σ : ℂ →+* ℂ)) ≫ (θ (cmVec Φ x)).left

end Leaves

/-! ## §3 mtcm-polar's isogeny step for primitive types

Copy of `MainCMPolar.mainTheoremCMSign_of_polar` (`ZInQKernel/Contrib/OneProof/MainCMPolar.lean`, wip/mtcm-polar
50dcdc48, lines 637-846), for a class `P` of CM types: the hypothesis `hprim : P E g Φ` is introduced and passed to
the leaf; no other change. -/

section Proof

open MonObj HcmPrinted
open AvSplit.HomLatticeAN3 (bcC projC ptE ptE_left)

/-- **The main theorem of CM for arbitrary lattices from the polarized, maximal-order print, on any class `P` of CM
types, at any sign `ε`.** -/
theorem mainTheoremCMSignOn_of_polar (P : CMTypeClass) (ε : ℤˣ) (hP : MainTheoremCMPolOn P ε) (hX : CMAbVarExists)
    (hUL : BPAnalytic.Uniformization.UniformizationLeafAll) (hG : ZInQ.HomLattice.GAGAMorphism) :
    MainTheoremCMSignOn P ε := by
  have hH : ZInQ.HomUnify.HomLatticeCorr := AvSplit.Final.h69 hUL hG
  intro E _ _ _ g Φ hdeg hinj hprim Er _ _ κr hκ n ρ j hρ σ s hs A hdimA 𝔞 θ hθ htype A' h hpb hone
  set t : AQ ⊗[ℚ] E := ((reflexNorm ρ (IdeleGroup.toFiniteIdele (𝓞 Er) Er s) ^ (ε : ℤ) : (AQ ⊗[ℚ] E)ˣ) :
    AQ ⊗[ℚ] E) with ht
  have hg : 0 < g := by
    have := Module.finrank_pos (R := ℚ) (M := E); omega
  obtain ⟨⟨N, hN, hNa⟩, ⟨d, hd, hda⟩⟩ := lattice_of_unif hUL Φ hg hdeg hθ
  -- the `𝓞_E`-lattice `𝔟 = N 𝓞_E ⊆ 𝔞`
  let 𝔟 : AddSubgroup E := nO N
  have hb_le : 𝔟 ≤ 𝔞 := fun x hx => by obtain ⟨o, rfl⟩ := mem_nO.1 hx; exact hNa o
  have hm : ∀ x ∈ 𝔞, ((N * d : ℕ) : E) * x ∈ 𝔟 := by
    intro x hx
    refine mem_nO.2 ⟨⟨(d : E) * x, hda x hx⟩, ?_⟩
    show (N : E) * ((d : E) * x) = _
    push_cast; ring
  have hmpos : 0 < N * d := Nat.mul_pos hN hd
  have hbdense : ∀ e : E, ∃ k : ℕ, 0 < k ∧ (k : E) * e ∈ 𝔟 := by
    intro e
    obtain ⟨y, hy0, hy⟩ := exists_integral_multiples ℤ ℚ (L := E) {e}
    have hye := natAbs_mul_integral (hy e (Finset.mem_singleton_self e))
    refine ⟨N * y.natAbs, Nat.mul_pos hN (Int.natAbs_pos.2 hy0), mem_nO.2 ⟨⟨_, hye⟩, ?_⟩⟩
    show (N : E) * ((y.natAbs : E) * e) = _
    push_cast; ring
  have hOL : IsOLattice 𝔟 := by
    refine ⟨fun o x hx => ?_, ⟨N, hN, fun o => mem_nO.2 ⟨o, rfl⟩⟩, ⟨1, one_pos, fun x hx => ?_⟩⟩
    · obtain ⟨o', rfl⟩ := mem_nO.1 hx
      exact mem_nO.2 ⟨o * o', by push_cast; ring⟩
    · obtain ⟨o, rfl⟩ := mem_nO.1 hx
      have := coe_integral ((N : 𝓞 E) * o)
      push_cast at this
      rw [Nat.cast_one, _root_.one_mul]; exact this
  -- step (2): the Riemann-form datum
  obtain ⟨ζ0, hζc, hζi⟩ := exists_zeta Φ hinj
  obtain ⟨y, hy0, hy⟩ := exists_integral_multiples ℤ ℚ (L := E) {ζ0}
  have hyζ := hy ζ0 (Finset.mem_singleton_self ζ0)
  have hζint : IsIntegral ℤ ((y * y) • ζ0) := by
    rw [mul_smul, zsmul_eq_mul]
    exact (by simpa using (isIntegral_algebraMap (R := ℤ) (A := E) (x := y)) : IsIntegral ℤ (y : E)).mul hyζ
  have hζ : IsRiemannDatum Φ 𝔟 ((y * y) • ζ0) := by
    refine ⟨by rw [map_zsmul, hζc, smul_neg], fun i => ?_, fun x hx x' hx' => ?_⟩
    · rw [map_zsmul, zsmul_eq_mul, Complex.mul_im, Complex.intCast_re, Complex.intCast_im, zero_mul,
        add_zero]
      exact mul_pos (by exact_mod_cast mul_self_pos.2 hy0) (hζi i)
    · obtain ⟨o, rfl⟩ := mem_nO.1 hx
      obtain ⟨o', rfl⟩ := mem_nO.1 hx'
      apply trace_int
      have h1 : IsIntegral ℤ ((N : E) * (o : E)) := by
        have := coe_integral ((N : 𝓞 E) * o); push_cast at this; exact this
      have h2 : IsIntegral ℤ ((N : E) * (o' : E)) := by
        have := coe_integral ((N : 𝓞 E) * o'); push_cast at this; exact this
      exact (hζint.mul h1).mul (h2.map (IsCMField.complexConj E))
  -- the abelian variety `B₀ = ℂ^g/Φ(N𝓞_E)` and the isogeny `μ : B₀ → A`
  obtain ⟨B, θB, hdimB, hθB⟩ := hX E g Φ hdeg hinj 𝔟 hOL ⟨_, hζ⟩
  have htypeB : IsOfType Φ 𝔟 θB := by
    intro e he
    let Me : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ) :=
      { toFun := fun w i => Φ i e * w i
        map_add' := fun w w' => by funext i; simp [mul_add]
        map_smul' := fun c w => by funext i; simp; ring }
    obtain ⟨f, hf, -⟩ := hH.2 B B g g (cmLat Φ 𝔟) (cmLat Φ 𝔟) θB θB hdimB hdimB hθB hθB Me
      (fun z hz => by
        obtain ⟨x, hx, rfl⟩ := mem_cmLat.1 hz
        exact mem_cmLat.2 ⟨e * x, he x hx, by funext i; simp [Me, cmVec]⟩)
    exact ⟨f, fun w => hf w⟩
  obtain ⟨mu, hμ, -⟩ := hH.2 B A g g (cmLat Φ 𝔟) (cmLat Φ 𝔞) θB θ hdimB hdimA hθB hθ LinearMap.id
    (fun z hz => by
      obtain ⟨x, hx, rfl⟩ := mem_cmLat.1 hz; exact mem_cmLat.2 ⟨x, hb_le hx, rfl⟩)
  have hμ' : ∀ z, θB z ≫ mu.hom = θ z := fun z => (hμ z).symm
  -- the main theorem for `B₀`
  obtain ⟨θB', hθB', hrelB⟩ := hP E g Φ hdeg hinj hprim Er κr hκ n ρ j hρ σ s hs B hdimB 𝔟 θB hθB htypeB hOL
    ⟨_, hζ⟩ (bcC B (σ : ℂ →+* ℂ)) (projC B (σ : ℂ →+* ℂ)) (isPullback_bc σ B) (one_left_bc σ B)
  -- the conjugate isogeny `μ^σ : B₀^σ → A'`
  have hsq : (projC B (σ : ℂ →+* ℂ) ≫ mu.hom.left) ≫ A.X.hom =
      (bcC B (σ : ℂ →+* ℂ)).X.hom ≫ Spec.map (CommRingCat.ofHom (σ : ℂ →+* ℂ)) := by
    rw [Category.assoc, Over.w mu.hom]; exact (isPullback_bc σ B).w
  let muL := hpb.lift (projC B (σ : ℂ →+* ℂ) ≫ mu.hom.left) (bcC B (σ : ℂ →+* ℂ)).X.hom hsq
  have hmuL : muL ≫ h = projC B (σ : ℂ →+* ℂ) ≫ mu.hom.left := hpb.lift_fst _ _ _
  let muO : (bcC B (σ : ℂ →+* ℂ)).X ⟶ A'.X := Over.homMk muL (hpb.lift_snd _ _ _)
  have hηB : η[(bcC B (σ : ℂ →+* ℂ)).X].left ≫ projC B (σ : ℂ →+* ℂ) =
      Spec.map (CommRingCat.ofHom (σ : ℂ →+* ℂ)) ≫ η[B.X].left := by
    have := one_left_bc σ B
    simp only [pl, one_left] at this
    exact this
  have hηA : η[A'.X].left ≫ h = Spec.map (CommRingCat.ofHom (σ : ℂ →+* ℂ)) ≫ η[A.X].left := by
    have := hone
    simp only [one_left] at this
    exact this
  have hμη : η[B.X].left ≫ mu.hom.left = η[A.X].left := by
    rw [← Over.comp_left, IsMonHom.one_hom]
  have hη : η[(bcC B (σ : ℂ →+* ℂ)).X] ≫ muO = η[A'.X] := by
    apply Over.OverMorphism.ext
    apply hpb.hom_ext
    · calc (η[(bcC B (σ : ℂ →+* ℂ)).X] ≫ muO).left ≫ h
            = η[(bcC B (σ : ℂ →+* ℂ)).X].left ≫ muL ≫ h := by
              rw [Over.comp_left, Category.assoc]; rfl
          _ = η[(bcC B (σ : ℂ →+* ℂ)).X].left ≫ projC B (σ : ℂ →+* ℂ) ≫ mu.hom.left := by rw [hmuL]
          _ = Spec.map (CommRingCat.ofHom (σ : ℂ →+* ℂ)) ≫ η[A.X].left := by
              rw [← Category.assoc, hηB, Category.assoc, hμη]
          _ = η[A'.X].left ≫ h := hηA.symm
    · rw [Over.w, Over.w]
  haveI : IsMonHom muO := MulRigidity.isMonHom_of_geometricallyIntegral _ _ muO hη
  have key : ∀ P : CPts (bcC B (σ : ℂ →+* ℂ)) (RingHom.id ℂ),
      pl (P ≫ muO) ≫ h = sp (σ : ℂ →+* ℂ) ≫ pl (dd σ B P ≫ mu.hom) := by
    intro P
    calc pl (P ≫ muO) ≫ h = (pl P ≫ muL) ≫ h := rfl
      _ = pl P ≫ (muL ≫ h) := Category.assoc _ _ _
      _ = pl P ≫ (projC B (σ : ℂ →+* ℂ) ≫ mu.hom.left) := by rw [hmuL]
      _ = (pl P ≫ projC B (σ : ℂ →+* ℂ)) ≫ mu.hom.left := (Category.assoc _ _ _).symm
      _ = (sp (σ : ℂ →+* ℂ) ≫ pl (dd σ B P)) ≫ mu.hom.left := by rw [dd_key σ B P]
      _ = sp (σ : ℂ →+* ℂ) ≫ (pl (dd σ B P) ≫ mu.hom.left) := Category.assoc _ _ _
  have hone' : pl (1 : CPts A' (RingHom.id ℂ)) ≫ h = sp (σ : ℂ →+* ℂ) ≫ pl (1 : CPts A (RingHom.id ℂ)) :=
    hone
  have hddrel : ∀ x y : E, t * (1 ⊗ₜ y) - 1 ⊗ₜ x ∈ latHat 𝔟 →
      dd σ B (θB' (cmVec Φ y)) = θB (cmVec Φ x) := by
    intro x y hxy
    apply dd_unique σ B
    exact hrelB x y hxy
  have hsp : ∀ {P Q : CPts A (RingHom.id ℂ)},
      sp (σ : ℂ →+* ℂ) ≫ pl P = sp (σ : ℂ →+* ℂ) ≫ pl Q → P = Q := by
    intro P Q hPQ
    apply pl_ext
    have := congrArg (fun r => sp (σ.symm : ℂ →+* ℂ) ≫ r) hPQ
    rwa [← Category.assoc, ← Category.assoc, sp_symm_comp, Category.id_comp, Category.id_comp] at this
  let θ' : (Fin g → ℂ) → CPts A' (RingHom.id ℂ) := fun z => θB' z ≫ muO
  -- the kernel
  have hker : ∀ z, θ' z = 1 ↔ z ∈ cmLat Φ (latAct t 𝔞) := by
    intro z
    constructor
    · intro hz
      have e2 : dd σ B (θB' z) ≫ mu.hom = 1 := by
        apply hsp
        rw [← key]
        show pl (θ' z) ≫ h = _
        rw [hz]; exact hone'
      obtain ⟨v, hv⟩ := hθB.2.2.1 (dd σ B (θB' z))
      have hv1 : θ v = 1 := by rw [← hμ', hv, e2]
      obtain ⟨x0, hx0, rfl⟩ := mem_cmLat.1 ((hθ.2.1 v).1 hv1)
      have hcm : ∀ (k : ℕ) (x : E), cmVec Φ ((k : E) * x) = k • cmVec Φ x := by
        intro k x; rw [← nsmul_eq_mul, map_nsmul]
      have hpow : θB' ((N * d) • z) = 1 := by
        rw [map_nsmul_of_hom hθB'.1]
        apply dd_injective σ B
        change ddHom σ B _ = ddHom σ B 1
        rw [map_pow, map_one]
        change (dd σ B (θB' z)) ^ (N * d) = 1
        rw [← hv, ← map_nsmul_of_hom hθB.1, ← hcm]
        exact (hθB.2.1 _).2 ((cmVec_mem_cmLat hg).2 (hm x0 hx0))
      obtain ⟨y1, hy1, hcy1⟩ := mem_cmLat.1 ((hθB'.2.1 _).1 hpow)
      let y : E := ((N * d : ℕ) : ℚ)⁻¹ • y1
      have hk0 : ((N * d : ℕ) : ℝ) ≠ 0 := by exact_mod_cast hmpos.ne'
      have hcy : cmVec Φ y = z := by
        show cmVec Φ (((N * d : ℕ) : ℚ)⁻¹ • y1) = z
        rw [cmVec_ratSmul, hcy1, ← Nat.cast_smul_eq_nsmul ℝ, smul_smul]
        push_cast
        rw [inv_mul_cancel₀ (by exact_mod_cast hk0), one_smul]
      obtain ⟨x, hx⟩ := exists_approx_latHat hbdense (t * (1 ⊗ₜ y))
      have h1 := hddrel x y hx
      rw [hcy] at h1
      have h2 : θB (cmVec Φ x) = θB (cmVec Φ x0) := by rw [← h1, hv]
      have hxx0 : x - x0 ∈ 𝔟 := by
        have := (hom_eq_iff hθB.1 _ _).1 h2
        rw [← map_sub] at this
        exact (cmVec_mem_cmLat hg).1 ((hθB.2.1 _).1 this)
      refine mem_cmLat.2 ⟨y, ?_, hcy⟩
      show t * (1 ⊗ₜ y) ∈ latHat 𝔞
      have e : t * (1 ⊗ₜ[ℚ] y) = (t * (1 ⊗ₜ y) - 1 ⊗ₜ x) + (1 : AQ) ⊗ₜ[ℚ] (x - x0) + (1 : AQ) ⊗ₜ[ℚ] x0 := by
        rw [TensorProduct.tmul_sub]; abel
      rw [e]
      exact add_mem (add_mem (latHat_mono hb_le hx) (latHat_mono hb_le (one_tmul_mem_latHat hxx0)))
        (one_tmul_mem_latHat hx0)
    · intro hz
      obtain ⟨y, hy, rfl⟩ := mem_cmLat.1 hz
      have hy' : t * (1 ⊗ₜ y) ∈ latHat 𝔞 := hy
      obtain ⟨x0, hx0, hrem⟩ := latHat_decomp hmpos hm hy'
      apply pt_ext hpb
      show pl (θB' (cmVec Φ y) ≫ muO) ≫ h = pl (1 : CPts A' (RingHom.id ℂ)) ≫ h
      rw [key, hddrel x0 y hrem, hμ', (hθ.2.1 _).2 (mem_cmLat.2 ⟨x0, hx0, rfl⟩), hone']
  -- surjectivity
  have hsurj : Function.Surjective θ' := by
    intro P
    have hQ : (sp (σ.symm : ℂ →+* ℂ) ≫ pl P ≫ h) ≫ A.X.hom = sp (RingHom.id ℂ) := by
      have hw : pl P ≫ A'.X.hom = sp (RingHom.id ℂ) := Over.w P
      rw [Category.assoc, Category.assoc, hpb.w, ← Category.assoc (pl P), hw, sp_id, Category.id_comp,
        sp_symm_comp]
    let Q : CPts A (RingHom.id ℂ) := Over.homMk (sp (σ.symm : ℂ →+* ℂ) ≫ pl P ≫ h) hQ
    obtain ⟨u, hu⟩ := hθ.2.2.1 Q
    obtain ⟨R, hR⟩ := dd_surjective σ B (θB u)
    obtain ⟨v, hv⟩ := hθB'.2.2.1 R
    refine ⟨v, pt_ext hpb ?_⟩
    show pl (θB' v ≫ muO) ≫ h = pl P ≫ h
    rw [key, hv, hR, hμ', hu]
    show sp (σ : ℂ →+* ℂ) ≫ (sp (σ.symm : ℂ →+* ℂ) ≫ pl P ≫ h) = pl P ≫ h
    rw [← Category.assoc, sp_comp_symm, Category.id_comp]
  -- the torsion relation
  have htors : ∀ x y : E, t * (1 ⊗ₜ y) - 1 ⊗ₜ x ∈ latHat 𝔞 →
      (θ' (cmVec Φ y)).left ≫ h = Spec.map (CommRingCat.ofHom (σ : ℂ →+* ℂ)) ≫ (θ (cmVec Φ x)).left := by
    intro x y hxy
    obtain ⟨a, ha, hrem⟩ := latHat_decomp hmpos hm hxy
    have hrem' : t * (1 ⊗ₜ y) - 1 ⊗ₜ (x + a) ∈ latHat 𝔟 := by
      have e : t * (1 ⊗ₜ[ℚ] y) - (1 : AQ) ⊗ₜ[ℚ] (x + a) = t * (1 ⊗ₜ y) - 1 ⊗ₜ x - 1 ⊗ₜ a := by
        rw [TensorProduct.tmul_add]; abel
      rw [e]; exact hrem
    show pl (θB' (cmVec Φ y) ≫ muO) ≫ h = sp (σ : ℂ →+* ℂ) ≫ pl (θ (cmVec Φ x))
    rw [key, hddrel _ _ hrem', hμ', map_add, hθ.1, (hθ.2.1 _).2 (mem_cmLat.2 ⟨a, ha, rfl⟩), _root_.mul_one]
  exact ⟨θ', (isUniformization_iff _ _ _).2
    ⟨isAnalyticHom_comp (isAnalyticHom_of_unif hθB') muO, hker, hsurj⟩, htors⟩

/-- **The main theorem of CM for arbitrary lattices and primitive types** from the primitive print. -/
theorem mainTheoremCMSignPrim_of_polar (ε : ℤˣ) (hP : MainTheoremCMPolPrimSign ε) (hX : CMAbVarExists)
    (hUL : BPAnalytic.Uniformization.UniformizationLeafAll) (hG : ZInQ.HomLattice.GAGAMorphism) :
    MainTheoremCMSignPrim ε :=
  mainTheoremCMSignOn_of_polar (fun _ _ _ _ _ Φ => IsPrimitiveType Φ) ε hP hX hUL hG

/-- **The main theorem of CM for arbitrary lattices on CM elliptic curves** from the quadratic print. -/
theorem mainTheoremCMSignQuad_of_polar (ε : ℤˣ) (hP : MainTheoremCMPolQuadSign ε) (hX : CMAbVarExists)
    (hUL : BPAnalytic.Uniformization.UniformizationLeafAll) (hG : ZInQ.HomLattice.GAGAMorphism) :
    MainTheoremCMSignQuad ε :=
  mainTheoremCMSignOn_of_polar (fun E _ _ _ _ _ => Module.finrank ℚ E = 2) ε hP hX hUL hG

end Proof

/-! ## §4 Conjugating homomorphisms; reduction to `A^σ = A ×_{ℂ,σ} ℂ` -/

section Conj

open MonObj HcmPrinted
open AvSplit.HomLatticeAN3 (bcC projC ptE ptE_left)

/-- **The conjugate `f^σ : B^σ → A'` of a homomorphism `f : B → A`**, for any `A'` presented as a pullback of `A`
along `Spec σ` preserving the identity (mtcm-polar's `μ^σ`, for any `f`): a homomorphism (rigidity) with
`f^σ(P) = σ(f(σ⁻¹P))`. -/
theorem exists_liftHom (σ : ℂ ≃+* ℂ) {A A' B : PkgI3.AbVar ℂ} (h : A'.X.left ⟶ A.X.left)
    (hpb : IsPullback h A'.X.hom A.X.hom (Spec.map (CommRingCat.ofHom (σ : ℂ →+* ℂ))))
    (hone : (1 : CPts A' (RingHom.id ℂ)).left ≫ h =
      Spec.map (CommRingCat.ofHom (σ : ℂ →+* ℂ)) ≫ (1 : CPts A (RingHom.id ℂ)).left)
    (f : B.X ⟶ A.X) [IsMonHom f] :
    ∃ F : (bcC B (σ : ℂ →+* ℂ)).X ⟶ A'.X, IsMonHom F ∧
      ∀ P : CPts (bcC B (σ : ℂ →+* ℂ)) (RingHom.id ℂ),
        pl (P ≫ F) ≫ h = sp (σ : ℂ →+* ℂ) ≫ pl (dd σ B P ≫ f) := by
  have hsq : (projC B (σ : ℂ →+* ℂ) ≫ f.left) ≫ A.X.hom =
      (bcC B (σ : ℂ →+* ℂ)).X.hom ≫ Spec.map (CommRingCat.ofHom (σ : ℂ →+* ℂ)) := by
    rw [Category.assoc, Over.w f]; exact (isPullback_bc σ B).w
  let muL := hpb.lift (projC B (σ : ℂ →+* ℂ) ≫ f.left) (bcC B (σ : ℂ →+* ℂ)).X.hom hsq
  have hmuL : muL ≫ h = projC B (σ : ℂ →+* ℂ) ≫ f.left := hpb.lift_fst _ _ _
  let muO : (bcC B (σ : ℂ →+* ℂ)).X ⟶ A'.X := Over.homMk muL (hpb.lift_snd _ _ _)
  have hηB : η[(bcC B (σ : ℂ →+* ℂ)).X].left ≫ projC B (σ : ℂ →+* ℂ) =
      Spec.map (CommRingCat.ofHom (σ : ℂ →+* ℂ)) ≫ η[B.X].left := by
    have := one_left_bc σ B
    simp only [pl, one_left] at this
    exact this
  have hηA : η[A'.X].left ≫ h = Spec.map (CommRingCat.ofHom (σ : ℂ →+* ℂ)) ≫ η[A.X].left := by
    have := hone
    simp only [one_left] at this
    exact this
  have hμη : η[B.X].left ≫ f.left = η[A.X].left := by
    rw [← Over.comp_left, IsMonHom.one_hom]
  have hη : η[(bcC B (σ : ℂ →+* ℂ)).X] ≫ muO = η[A'.X] := by
    apply Over.OverMorphism.ext
    apply hpb.hom_ext
    · calc (η[(bcC B (σ : ℂ →+* ℂ)).X] ≫ muO).left ≫ h
            = η[(bcC B (σ : ℂ →+* ℂ)).X].left ≫ muL ≫ h := by
              rw [Over.comp_left, Category.assoc]; rfl
          _ = η[(bcC B (σ : ℂ →+* ℂ)).X].left ≫ projC B (σ : ℂ →+* ℂ) ≫ f.left := by rw [hmuL]
          _ = Spec.map (CommRingCat.ofHom (σ : ℂ →+* ℂ)) ≫ η[A.X].left := by
              rw [← Category.assoc, hηB, Category.assoc, hμη]
          _ = η[A'.X].left ≫ h := hηA.symm
    · rw [Over.w, Over.w]
  haveI : IsMonHom muO := MulRigidity.isMonHom_of_geometricallyIntegral _ _ muO hη
  refine ⟨muO, inferInstance, fun P => ?_⟩
  calc pl (P ≫ muO) ≫ h = (pl P ≫ muL) ≫ h := rfl
    _ = pl P ≫ (muL ≫ h) := Category.assoc _ _ _
    _ = pl P ≫ (projC B (σ : ℂ →+* ℂ) ≫ f.left) := by rw [hmuL]
    _ = (pl P ≫ projC B (σ : ℂ →+* ℂ)) ≫ f.left := (Category.assoc _ _ _).symm
    _ = (sp (σ : ℂ →+* ℂ) ≫ pl (dd σ B P)) ≫ f.left := by rw [dd_key σ B P]
    _ = sp (σ : ℂ →+* ℂ) ≫ (pl (dd σ B P) ≫ f.left) := Category.assoc _ _ _

/-- **Base change of a homomorphism**: `f^σ : B^σ → A^σ` with `σ⁻¹(f^σ(P)) = f(σ⁻¹(P))`. -/
theorem exists_bcHom (σ : ℂ ≃+* ℂ) {A B : PkgI3.AbVar ℂ} (f : B.X ⟶ A.X) [IsMonHom f] :
    ∃ F : (bcC B (σ : ℂ →+* ℂ)).X ⟶ (bcC A (σ : ℂ →+* ℂ)).X, IsMonHom F ∧
      ∀ P : CPts (bcC B (σ : ℂ →+* ℂ)) (RingHom.id ℂ), dd σ A (P ≫ F) = dd σ B P ≫ f := by
  obtain ⟨F, hF, hkey⟩ := exists_liftHom σ (projC A (σ : ℂ →+* ℂ)) (isPullback_bc σ A) (one_left_bc σ A) f
  exact ⟨F, hF, fun P => dd_unique σ A (hkey P)⟩

theorem sp_cancel (σ : ℂ ≃+* ℂ) {A : PkgI3.AbVar ℂ} {P Q : CPts A (RingHom.id ℂ)}
    (hPQ : sp (σ : ℂ →+* ℂ) ≫ pl P = sp (σ : ℂ →+* ℂ) ≫ pl Q) : P = Q := by
  apply pl_ext
  have := congrArg (fun r => sp (σ.symm : ℂ →+* ℂ) ≫ r) hPQ
  rwa [← Category.assoc, ← Category.assoc, sp_symm_comp, Category.id_comp, Category.id_comp] at this

/-- **Reduction to `A^σ = bcC A σ`**: a uniformization `θ₀` of `A^σ` gives one of any `A'` presented as a pullback
of `A` along `Spec σ` preserving the identity, with the same lattice, compatible with de-conjugation. -/
theorem exists_unif_of_bc (σ : ℂ ≃+* ℂ) {A A' : PkgI3.AbVar ℂ} (h : A'.X.left ⟶ A.X.left)
    (hpb : IsPullback h A'.X.hom A.X.hom (Spec.map (CommRingCat.ofHom (σ : ℂ →+* ℂ))))
    (hone : (1 : CPts A' (RingHom.id ℂ)).left ≫ h =
      Spec.map (CommRingCat.ofHom (σ : ℂ →+* ℂ)) ≫ (1 : CPts A (RingHom.id ℂ)).left)
    {g : ℕ} {L : Submodule ℤ (Fin g → ℂ)}
    {θ0 : (Fin g → ℂ) → CPts (bcC A (σ : ℂ →+* ℂ)) (RingHom.id ℂ)}
    (hθ0 : IsUniformization (RingHom.id ℂ) L θ0) :
    ∃ θ' : (Fin g → ℂ) → CPts A' (RingHom.id ℂ), IsUniformization (RingHom.id ℂ) L θ' ∧
      ∀ z, pl (θ' z) ≫ h = sp (σ : ℂ →+* ℂ) ≫ pl (dd σ A (θ0 z)) := by
  obtain ⟨F, hF, hkey⟩ := exists_liftHom σ h hpb hone (𝟙 A.X)
  have hkey' : ∀ P, pl (P ≫ F) ≫ h = sp (σ : ℂ →+* ℂ) ≫ pl (dd σ A P) := fun P => by
    rw [hkey, Category.comp_id]
  have hone' : pl (1 : CPts A' (RingHom.id ℂ)) ≫ h = sp (σ : ℂ →+* ℂ) ≫ pl (1 : CPts A (RingHom.id ℂ)) :=
    hone
  refine ⟨fun z => θ0 z ≫ F, (isUniformization_iff _ _ _).2
    ⟨isAnalyticHom_comp (isAnalyticHom_of_unif hθ0) F, fun z => ?_, ?_⟩, fun z => hkey' _⟩
  · rw [← hθ0.2.1 z]
    constructor
    · intro hz
      apply dd_injective σ A
      rw [dd_one]
      apply sp_cancel σ
      rw [← hkey']
      show pl (θ0 z ≫ F) ≫ h = _
      rw [hz]; exact hone'
    · intro hz
      show θ0 z ≫ F = 1
      rw [hz]; exact MonObj.one_comp F
  · intro P
    have hQ : (sp (σ.symm : ℂ →+* ℂ) ≫ pl P ≫ h) ≫ A.X.hom = sp (RingHom.id ℂ) := by
      have hw : pl P ≫ A'.X.hom = sp (RingHom.id ℂ) := Over.w P
      rw [Category.assoc, Category.assoc, hpb.w, ← Category.assoc (pl P), hw, sp_id, Category.id_comp,
        sp_symm_comp]
    let Q : CPts A (RingHom.id ℂ) := Over.homMk (sp (σ.symm : ℂ →+* ℂ) ≫ pl P ≫ h) hQ
    obtain ⟨R, hR⟩ := dd_surjective σ A Q
    obtain ⟨v, hv⟩ := hθ0.2.2.1 R
    refine ⟨v, pt_ext hpb ?_⟩
    show pl (θ0 v ≫ F) ≫ h = pl P ≫ h
    rw [hkey', hv, hR]
    show sp (σ : ℂ →+* ℂ) ≫ (sp (σ.symm : ℂ →+* ℂ) ≫ pl P ≫ h) = pl P ≫ h
    rw [← Category.assoc, sp_comp_symm, Category.id_comp]

end Conj

/-! ## §5 The CM type `(K, κ)` of an imaginary quadratic field, its reflex field and reflex norm -/

section ModelK

open scoped FiniteAdeleExtension

variable {K : Type} [Field K] [NumberField K]

/-- An imaginary quadratic field is a CM field. -/
theorem isCMField_K [IsTotallyComplex K] (hK : Module.finrank ℚ K = 2) : IsCMField K := by
  haveI : Algebra.IsQuadraticExtension ℚ K := ⟨hK⟩
  exact IsCMField.ofCMExtension ℚ K

/-- `{κ}` is a CM type of `K`. -/
theorem type_inj1 [IsTotallyComplex K] (κ : K →+* ℂ) :
    Function.Injective (Sum.elim (fun _ : Fin 1 => κ) fun i => (starRingEnd ℂ).comp ((fun _ : Fin 1 => κ) i)) := by
  obtain ⟨x0, hx0⟩ := exists_not_real κ
  intro a b hab
  rcases a with a | a <;> rcases b with b | b
  · rw [Subsingleton.elim a b]
  · exfalso
    have := RingHom.congr_fun hab x0
    simp only [Sum.elim_inl, Sum.elim_inr, RingHom.coe_comp, Function.comp_apply] at this
    exact hx0 this.symm
  · exfalso
    have := RingHom.congr_fun hab x0
    simp only [Sum.elim_inl, Sum.elim_inr, RingHom.coe_comp, Function.comp_apply] at this
    exact hx0 this
  · rw [Subsingleton.elim a b]

/-- The reflex field of `(K, {κ})` is `κ(K)`. -/
theorem reflex1 (κ : K →+* ℂ) :
    κ.fieldRange = Subfield.closure (Set.range fun e : K => ∑ i : Fin 1, (fun _ : Fin 1 => κ) i e) := by
  simp only [Finset.univ_unique, Fin.default_eq_zero, Finset.sum_singleton]
  rw [← RingHom.coe_fieldRange, Subfield.closure_eq]

/-- `ρ(a)` = multiplication by `a` on `V = K`. -/
def rho1 : K →ₐ[ℚ] Matrix (Fin 1) (Fin 1) K :=
  (Algebra.ofId K (Matrix (Fin 1) (Fin 1) K)).restrictScalars ℚ

/-- `j(v) = κ(v₀)`. -/
def j1 (κ : K →+* ℂ) : (Fin 1 → K) →+ (Fin 1 → ℂ) :=
  (cmVec (fun _ : Fin 1 => κ)).comp (Pi.evalAddMonoidHom (fun _ => K) 0)

theorem j1_apply (κ : K →+* ℂ) (v : Fin 1 → K) (i : Fin 1) : j1 κ v i = κ (v 0) := rfl

theorem rho1_mulVec (a : K) (v : Fin 1 → K) : (rho1 a).mulVec v = fun i => a * v i := by
  funext i
  simp [rho1, Matrix.algebraMap_eq_diagonal, Matrix.mulVec_diagonal]

/-- `V = K` is a model of `ℂ^{κ}` over the reflex field `K`. -/
theorem model1 (κ : K →+* ℂ) : IsReflexModel (fun _ : Fin 1 => κ) κ rho1 (j1 κ) := by
  refine ⟨fun e v => ?_, fun a v => ?_, ?_, rfl⟩
  · funext i; simp [j1_apply, map_mul]
  · funext i; simp [j1_apply, rho1_mulVec, map_mul]
  · rw [eq_top_iff]
    intro w _
    have hw : w = (w 0) • j1 κ (fun _ => (1 : K)) := by
      funext i; rw [Subsingleton.elim i 0]; simp [j1_apply]
    rw [hw]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, rfl⟩)

theorem rhoA_rho1 (w : AQ ⊗[ℚ] K) : rhoA rho1 w 0 0 = w := by
  induction w using TensorProduct.induction_on with
  | zero => simp
  | tmul a k =>
    rw [rhoA, AlgHom.liftEquiv_tmul]
    simp [rho1, Matrix.algebraMap_eq_diagonal, Algebra.TensorProduct.includeRight_apply,
      TensorProduct.smul_tmul']
  | add x y hx hy => rw [map_add, Matrix.add_apply, hx, hy]

/-- **The reflex norm of `(K, {κ})` is `𝔸_{K,f} ≅ 𝔸_f ⊗ K`.** -/
theorem reflexNorm_rho1 (u : (FiniteAdeleRing (𝓞 K) K)ˣ) :
    (reflexNorm rho1 u : AQ ⊗[ℚ] K) = (finiteAdeleBaseChangeAlgEquiv ℚ K).symm u := by
  simp only [reflexNorm, Units.coe_map, MonoidHom.coe_comp, Function.comp_apply,
    Matrix.coe_detMonoidHom, Matrix.det_unique]
  exact rhoA_rho1 _

end ModelK

/-! ## §6 `E = K(√2)` over `K`: coordinates, the two maps `ℂ → ℂ²`, and `𝔸_f ⊗ E = (𝔸_f ⊗ K)²` -/

section Coord

open Polynomial

variable {K : Type} [Field K] [NumberField K] [Fact (Irreducible (X ^ 2 - C (2 : K)))]

/-- Denominators of a `ℚ`-linear map between number fields on integers. -/
theorem exists_den_lin {F L : Type} [Field F] [NumberField F] [Field L] [NumberField L] (ℓ : F →ₗ[ℚ] L) :
    ∃ D : ℕ, 0 < D ∧ ∀ o : 𝓞 F, IsIntegral ℤ ((D : L) * ℓ (o : F)) := by
  classical
  let b := RingOfIntegers.basis F
  obtain ⟨y, hy0, hy⟩ := exists_integral_multiples ℤ ℚ (L := L) (Finset.univ.image fun i => ℓ (b i : F))
  refine ⟨y.natAbs, Int.natAbs_pos.2 hy0, fun o => ?_⟩
  have ho : (o : F) = ∑ i, (b.repr o i) • (b i : F) := by
    conv_lhs => rw [← b.sum_repr o]
    push_cast
    rfl
  rw [ho, map_sum, Finset.mul_sum]
  refine IsIntegral.sum _ fun i _ => ?_
  rw [map_zsmul, mul_smul_comm, zsmul_eq_mul]
  exact (by simpa using (isIntegral_algebraMap (R := ℤ) (A := L) (x := b.repr o i)) :
    IsIntegral ℤ ((b.repr o i : ℤ) : L)).mul
    (natAbs_mul_integral (hy _ (Finset.mem_image_of_mem _ (Finset.mem_univ i))))

theorem crd_algebraMap_mul (i : Fin 2) (k : K) (e : EK K) :
    crd i (algebraMap K (EK K) k * e) = k * crd i e := by
  rw [crd_apply, crd_apply, ← Algebra.smul_def, map_smul]; rfl

theorem crd_natCast_mul (i : Fin 2) (m : ℕ) (e : EK K) : crd i ((m : EK K) * e) = (m : K) * crd i e := by
  rw [← map_natCast (algebraMap K (EK K)) m, crd_algebraMap_mul]

theorem crd_mk0 (a b : K) : crd 0 (algebraMap K (EK K) a + algebraMap K (EK K) b * AdjoinRoot.root _) = a := by
  rw [crd_apply, ← Algebra.smul_def, Algebra.algebraMap_eq_smul_one]
  have h1 : (1 : EK K) = bK 0 := by rw [bK_apply]; simp
  have h2 : AdjoinRoot.root (X ^ 2 - C (2 : K)) = bK 1 := by rw [bK_apply]; simp
  rw [h1, h2, map_add, map_smul, map_smul, bK.repr_self, bK.repr_self]
  simp

theorem crd_mk1 (a b : K) : crd 1 (algebraMap K (EK K) a + algebraMap K (EK K) b * AdjoinRoot.root _) = b := by
  rw [crd_apply, ← Algebra.smul_def, Algebra.algebraMap_eq_smul_one]
  have h1 : (1 : EK K) = bK 0 := by rw [bK_apply]; simp
  have h2 : AdjoinRoot.root (X ^ 2 - C (2 : K)) = bK 1 := by rw [bK_apply]; simp
  rw [h1, h2, map_add, map_smul, map_smul, bK.repr_self, bK.repr_self]
  simp

theorem root_sq : (AdjoinRoot.root (X ^ 2 - C (2 : K))) ^ 2 = 2 := by
  have h := AdjoinRoot.eval₂_root (X ^ 2 - C (2 : K))
  simp only [eval₂_sub, eval₂_X_pow, eval₂_C] at h
  rw [sub_eq_zero] at h
  exact h.trans (map_ofNat _ 2)

theorem isIntegral_root : IsIntegral ℤ (AdjoinRoot.root (X ^ 2 - C (2 : K))) := by
  refine IsIntegral.of_pow two_pos ?_
  rw [root_sq]
  simpa using (isIntegral_algebraMap (R := ℤ) (A := EK K) (x := 2))

variable (κ : K →+* ℂ)

/-- `w ↦ w Φ(α)`, `ℂ → ℂ²`. -/
def Mv (α : EK K) : (Fin 1 → ℂ) →ₗ[ℂ] (Fin 2 → ℂ) :=
  (LinearMap.proj (R := ℂ) (φ := fun _ : Fin 1 => ℂ) 0).smulRight (cmVec (PhiE κ) α)

theorem Mv_apply (α : EK K) (w : Fin 1 → ℂ) : Mv κ α w = w 0 • cmVec (PhiE κ) α := rfl

/-- The first coordinate in the basis `Φ(1), Φ(√2)` of `ℂ²`. -/
def ell0 : (Fin 2 → ℂ) →ₗ[ℂ] (Fin 1 → ℂ) where
  toFun w _ := (w 0 + w 1) / 2
  map_add' w w' := by funext; simp only [Pi.add_apply]; ring
  map_smul' c w := by funext; simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]; ring

/-- The second coordinate in the basis `Φ(1), Φ(√2)` of `ℂ²`. -/
def ell1 : (Fin 2 → ℂ) →ₗ[ℂ] (Fin 1 → ℂ) where
  toFun w _ := (w 0 - w 1) / (2 * ((√2 : ℝ) : ℂ))
  map_add' w w' := by funext; simp only [Pi.add_apply]; ring
  map_smul' c w := by funext; simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]; ring

theorem cmVec_one : cmVec (PhiE κ) (1 : EK K) = ![1, 1] := by
  funext i; fin_cases i <;> simp [cmVec]

theorem cmVec_root : cmVec (PhiE κ) (AdjoinRoot.root _) = ![((√2 : ℝ) : ℂ), -((√2 : ℝ) : ℂ)] := by
  funext i; fin_cases i <;> simp [cmVec, phiE0_root, phiE1_root]

theorem span_Mv (w : Fin 2 → ℂ) : Mv κ 1 (ell0 w) + Mv κ (AdjoinRoot.root _) (ell1 w) = w := by
  rw [Mv_apply, Mv_apply]
  exact (span_two κ w).symm

theorem ell0_Mv1 (v : Fin 1 → ℂ) : ell0 (Mv κ 1 v) = v := by
  funext i; rw [Subsingleton.elim i 0]
  simp [ell0, Mv_apply, cmVec_one]

theorem ell1_Mv1 (v : Fin 1 → ℂ) : ell1 (Mv κ 1 v) = 0 := by
  funext i
  simp [ell1, Mv_apply, cmVec_one]

theorem ell0_Mvr (v : Fin 1 → ℂ) : ell0 (Mv κ (AdjoinRoot.root _) v) = 0 := by
  funext i
  simp [ell0, Mv_apply, cmVec_root]

theorem ell1_Mvr (v : Fin 1 → ℂ) : ell1 (Mv κ (AdjoinRoot.root _) v) = v := by
  funext i; rw [Subsingleton.elim i 0]
  simp [ell1, Mv_apply, cmVec_root]
  field_simp [sqrt2_ne_zero]
  ring

theorem ell0_cmVec (e : EK K) : ell0 (cmVec (PhiE κ) e) = cmVec (fun _ : Fin 1 => κ) (crd 0 e) := by
  funext i
  show (PhiE κ 0 e + PhiE κ 1 e) / 2 = κ (crd 0 e)
  rw [phi0_apply, phi1_apply, crd_apply]; ring

theorem ell1_cmVec (e : EK K) : ell1 (cmVec (PhiE κ) e) = cmVec (fun _ : Fin 1 => κ) (crd 1 e) := by
  funext i
  show (PhiE κ 0 e - PhiE κ 1 e) / (2 * ((√2 : ℝ) : ℂ)) = κ (crd 1 e)
  rw [phi0_apply, phi1_apply, crd_apply]
  field_simp [sqrt2_ne_zero]
  ring

theorem cmVec_decomp (e : EK K) :
    Mv κ 1 (cmVec (fun _ : Fin 1 => κ) (crd 0 e)) +
      Mv κ (AdjoinRoot.root _) (cmVec (fun _ : Fin 1 => κ) (crd 1 e)) = cmVec (PhiE κ) e := by
  rw [← ell0_cmVec, ← ell1_cmVec, span_Mv]

theorem Mv_cmVec (α : EK K) (b : K) :
    Mv κ α (cmVec (fun _ : Fin 1 => κ) b) = cmVec (PhiE κ) (algebraMap K (EK K) b * α) := by
  funext i
  simp [Mv_apply, cmVec, map_mul, phiE_of]

/-- `𝔸_f ⊗ E → 𝔸_f ⊗ K`, the base change of a coordinate. -/
def crdHat (i : Fin 2) : AQ ⊗[ℚ] EK K →ₗ[AQ] AQ ⊗[ℚ] K := (crd i).baseChange AQ

theorem crdHat_tmul (i : Fin 2) (a : AQ) (e : EK K) : crdHat i (a ⊗ₜ e) = a ⊗ₜ crd i e :=
  LinearMap.baseChange_tmul _ _ _

theorem crdHat_inclA_mul (i : Fin 2) (w : AQ ⊗[ℚ] K) (v : AQ ⊗[ℚ] EK K) :
    crdHat i (inclA w * v) = w * crdHat i v := by
  induction w using TensorProduct.induction_on with
  | zero => simp
  | add w w' hw hw' => rw [map_add, add_mul, map_add, hw, hw', add_mul]
  | tmul a k =>
    induction v using TensorProduct.induction_on with
    | zero => simp
    | add v v' hv hv' => rw [mul_add, map_add, hv, hv', map_add, mul_add]
    | tmul b e =>
      rw [inclA_tmul, Algebra.TensorProduct.tmul_mul_tmul, crdHat_tmul, crdHat_tmul,
        Algebra.TensorProduct.tmul_mul_tmul, crd_algebraMap_mul]

theorem crdHat_latHat (i : Fin 2) {𝔠 : AddSubgroup (EK K)} {𝔟 : AddSubgroup K}
    (h : ∀ e ∈ 𝔠, crd i e ∈ 𝔟) {w : AQ ⊗[ℚ] EK K} (hw : w ∈ latHat 𝔠) : crdHat i w ∈ latHat 𝔟 := by
  induction hw using AddSubgroup.closure_induction with
  | mem w hw =>
    obtain ⟨c, hc, x, hx, rfl⟩ := hw
    rw [crdHat_tmul]
    exact AddSubgroup.subset_closure ⟨c, hc, _, h x hx, rfl⟩
  | zero => rw [map_zero]; exact zero_mem _
  | add u v _ _ hu hv => rw [map_add]; exact add_mem hu hv
  | neg u _ hu => rw [map_neg]; exact neg_mem hu

end Coord

/-! ## §7 The induced type of `E = K(√2)` from the primitive type `(K, κ)` -/

section EK

open Polynomial MonObj HcmPrinted
open AvSplit.HomLatticeAN3 (bcC projC ptE ptE_left)
open ZInQ.HomLattice (isAnalyticHom_lin map_zero_of_hom)

/-- **Glue target `MainTheoremCMEK ε`**: `HcmPrinted.MainTheoremCMSign ε` at the CM type `Φ = PhiE κ` of
`E = K(√2)` induced from `(K, κ)` (`K` imaginary quadratic), its reflex field `(K, κ)` and the model `rhoK`: the only
instance of `QMRecPrinted.MainTheoremCM` used by `QMRecPrinted.qmReciprocityL3_of_printed`. Implied by
`MainTheoremCMSign ε` (`ek_of_sign`). -/
def MainTheoremCMEK (ε : ℤˣ) : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [IsTotallyComplex K], Module.finrank ℚ K = 2 →
  ∀ [Fact (Irreducible (X ^ 2 - C (2 : K)))] (κ : K →+* ℂ) (σ : ℂ ≃+* ℂ) (s : IdeleGroup (𝓞 K) K),
    ArtinCondC κ σ s →
  ∀ (A : PkgI3.AbVar ℂ), A.dim = ((2 : ℕ) : WithBot ℕ∞) →
  ∀ (𝔞 : AddSubgroup (EK K)) (θ : (Fin 2 → ℂ) → CPts A (RingHom.id ℂ)),
    IsUniformization (RingHom.id ℂ) (cmLat (PhiE κ) 𝔞) θ → IsOfType (PhiE κ) 𝔞 θ →
  ∀ (A' : PkgI3.AbVar ℂ) (h : A'.X.left ⟶ A.X.left),
    IsPullback h A'.X.hom A.X.hom (Spec.map (CommRingCat.ofHom (σ : ℂ →+* ℂ))) →
    (1 : CPts A' (RingHom.id ℂ)).left ≫ h =
      Spec.map (CommRingCat.ofHom (σ : ℂ →+* ℂ)) ≫ (1 : CPts A (RingHom.id ℂ)).left →
  ∃ θ' : (Fin 2 → ℂ) → CPts A' (RingHom.id ℂ),
    IsUniformization (RingHom.id ℂ)
      (cmLat (PhiE κ) (latAct ((reflexNorm rhoK (IdeleGroup.toFiniteIdele (𝓞 K) K s) ^ (ε : ℤ) :
        (AQ ⊗[ℚ] EK K)ˣ) : AQ ⊗[ℚ] EK K) 𝔞)) θ' ∧
    ∀ x y : EK K,
      ((reflexNorm rhoK (IdeleGroup.toFiniteIdele (𝓞 K) K s) ^ (ε : ℤ) : (AQ ⊗[ℚ] EK K)ˣ) :
          AQ ⊗[ℚ] EK K) * (1 ⊗ₜ y) - 1 ⊗ₜ x ∈ latHat 𝔞 →
        (θ' (cmVec (PhiE κ) y)).left ≫ h =
          Spec.map (CommRingCat.ofHom (σ : ℂ →+* ℂ)) ≫ (θ (cmVec (PhiE κ) x)).left

/-- `MainTheoremCMEK ε` is an instance of `MainTheoremCMSign ε`. -/
theorem ek_of_sign {ε : ℤˣ} (h : HcmPrinted.MainTheoremCMSign ε) : MainTheoremCMEK ε := by
  intro K _ _ _ hK _ κ σ s hs A hA 𝔞 θ hθ ht A' h' hpb hone
  haveI := isCMField_EK hK
  exact h (EK K) 2 (PhiE κ) (by rw [finrank_EK hK]) (type_inj κ) K κ (reflex_eq κ) 1 rhoK (jK κ) (model hK κ)
    σ s hs A hA 𝔞 θ hθ ht A' h' hpb hone

/-- **The reduction from the induced type of `E = K(√2)` to the primitive type `(K, κ)`.** The main theorem of CM
for imaginary quadratic fields (every lattice), Shimura's existence theorem and the textbook leaves give the main
theorem for `(E, PhiE κ)`. -/
theorem mainTheoremCMEK_of_quad (ε : ℤˣ) (hP : MainTheoremCMSignQuad ε) (hX : CMAbVarExists)
    (hUL : BPAnalytic.Uniformization.UniformizationLeafAll) (hG : ZInQ.HomLattice.GAGAMorphism) :
    MainTheoremCMEK ε := by
  intro K _ _ _ hK _ κ σ s hs A hdimA 𝔞 θ hθ htype A' h hpb hone
  have hH : ZInQ.HomUnify.HomLatticeCorr := AvSplit.Final.h69 hUL hG
  haveI : IsCMField K := isCMField_K hK
  haveI : IsCMField (EK K) := isCMField_EK hK
  set Φ := PhiE κ with hΦ
  set Φ0 : Fin 1 → K →+* ℂ := fun _ => κ with hΦ0
  set r : EK K := AdjoinRoot.root (X ^ 2 - C (2 : K)) with hr
  set s' := IdeleGroup.toFiniteIdele (𝓞 K) K s with hs'
  set t : AQ ⊗[ℚ] EK K := ((reflexNorm rhoK s' ^ (ε : ℤ) : (AQ ⊗[ℚ] EK K)ˣ) : AQ ⊗[ℚ] EK K) with ht
  set tK : AQ ⊗[ℚ] K := ((reflexNorm rho1 s' ^ (ε : ℤ) : (AQ ⊗[ℚ] K)ˣ) : AQ ⊗[ℚ] K) with htK
  have htt : t = inclA tK := by
    rw [ht, htK, ← map_zpow (reflexNorm rhoK) s' (ε : ℤ), ← map_zpow (reflexNorm rho1) s' (ε : ℤ),
      reflexNorm_rhoK, reflexNorm_rho1]
  have hdeg : Module.finrank ℚ (EK K) = 2 * 2 := by rw [finrank_EK hK]
  have hinj1 := type_inj1 κ
  obtain ⟨⟨N, hN, hNa⟩, ⟨d, hd, hda⟩⟩ := lattice_of_unif hUL Φ two_pos hdeg hθ
  -- the elliptic curve `B = ℂ/κ(N𝓞_K)`
  let 𝔟 : AddSubgroup K := nO N
  have hOL : IsOLattice 𝔟 := by
    refine ⟨fun o x hx => ?_, ⟨N, hN, fun o => mem_nO.2 ⟨o, rfl⟩⟩, ⟨1, one_pos, fun x hx => ?_⟩⟩
    · obtain ⟨o', rfl⟩ := mem_nO.1 hx
      exact mem_nO.2 ⟨o * o', by push_cast; ring⟩
    · obtain ⟨o, rfl⟩ := mem_nO.1 hx
      have := coe_integral ((N : 𝓞 K) * o)
      push_cast at this
      rw [Nat.cast_one, _root_.one_mul]; exact this
  obtain ⟨ζ0, hζc, hζi⟩ := exists_zeta Φ0 hinj1
  obtain ⟨y, hy0, hy⟩ := exists_integral_multiples ℤ ℚ (L := K) {ζ0}
  have hyζ := hy ζ0 (Finset.mem_singleton_self ζ0)
  have hζint : IsIntegral ℤ ((y * y) • ζ0) := by
    rw [mul_smul, zsmul_eq_mul]
    exact (by simpa using (isIntegral_algebraMap (R := ℤ) (A := K) (x := y)) : IsIntegral ℤ (y : K)).mul hyζ
  have hζ : IsRiemannDatum Φ0 𝔟 ((y * y) • ζ0) := by
    refine ⟨by rw [map_zsmul, hζc, smul_neg], fun i => ?_, fun x hx x' hx' => ?_⟩
    · rw [map_zsmul, zsmul_eq_mul, Complex.mul_im, Complex.intCast_re, Complex.intCast_im, zero_mul,
        add_zero]
      exact mul_pos (by exact_mod_cast mul_self_pos.2 hy0) (hζi i)
    · obtain ⟨o, rfl⟩ := mem_nO.1 hx
      obtain ⟨o', rfl⟩ := mem_nO.1 hx'
      apply trace_int
      have h1 : IsIntegral ℤ ((N : K) * (o : K)) := by
        have := coe_integral ((N : 𝓞 K) * o); push_cast at this; exact this
      have h2 : IsIntegral ℤ ((N : K) * (o' : K)) := by
        have := coe_integral ((N : 𝓞 K) * o'); push_cast at this; exact this
      exact (hζint.mul h1).mul (h2.map (IsCMField.complexConj K))
  obtain ⟨B, θB, hdimB, hθB⟩ := hX K 1 Φ0 (by rw [hK]) hinj1 𝔟 hOL ⟨_, hζ⟩
  have htypeB : IsOfType Φ0 𝔟 θB := by
    intro e he
    let Me : (Fin 1 → ℂ) →ₗ[ℂ] (Fin 1 → ℂ) :=
      { toFun := fun w i => Φ0 i e * w i
        map_add' := fun w w' => by funext i; simp [mul_add]
        map_smul' := fun c w => by funext i; simp; ring }
    obtain ⟨f, hf, -⟩ := hH.2 B B 1 1 (cmLat Φ0 𝔟) (cmLat Φ0 𝔟) θB θB hdimB hdimB hθB hθB Me
      (fun z hz => by
        obtain ⟨x, hx, rfl⟩ := mem_cmLat.1 hz
        exact mem_cmLat.2 ⟨e * x, he x hx, by funext i; simp [Me, cmVec]⟩)
    exact ⟨f, fun w => hf w⟩
  -- the main theorem for the primitive type `(K, κ)`, applied to `B`
  obtain ⟨θB', hθB', hrelB⟩ := hP K 1 Φ0 (by rw [hK]) hinj1 hK
    K κ (reflex1 κ) 1 rho1 (j1 κ) (model1 κ) σ s hs B hdimB 𝔟 θB hθB htypeB
    (bcC B (σ : ℂ →+* ℂ)) (projC B (σ : ℂ →+* ℂ)) (isPullback_bc σ B) (one_left_bc σ B)
  have hddB : ∀ x y : K, tK * (1 ⊗ₜ y) - 1 ⊗ₜ x ∈ latHat 𝔟 →
      dd σ B (θB' (cmVec Φ0 y)) = θB (cmVec Φ0 x) := fun x y hxy => dd_unique σ B (hrelB x y hxy)
  -- the homomorphisms `f₁, f₂ : B → A`, `θ(wΦ(α)) = f_α(θ_B(w))`
  have hMlat : ∀ α : EK K, IsIntegral ℤ α → ∀ z ∈ cmLat Φ0 𝔟, Mv κ α z ∈ cmLat Φ 𝔞 := by
    intro α hα z hz
    obtain ⟨b, hb, rfl⟩ := mem_cmLat.1 hz
    obtain ⟨o, rfl⟩ := mem_nO.1 hb
    refine mem_cmLat.2 ⟨_, hNa ⟨algebraMap K (EK K) (o : K) * α,
      ((coe_integral o).map (IsScalarTower.toAlgHom ℤ K (EK K))).mul hα⟩, ?_⟩
    rw [Mv_cmVec]
    congr 1
    show (N : EK K) * (algebraMap K (EK K) (o : K) * α) = algebraMap K (EK K) ((N : K) * (o : K)) * α
    rw [map_mul, map_natCast, _root_.mul_assoc]
  obtain ⟨f1, hf1, -⟩ := hH.2 B A 1 2 (cmLat Φ0 𝔟) (cmLat Φ 𝔞) θB θ hdimB hdimA hθB hθ (Mv κ 1)
    (hMlat 1 isIntegral_one)
  obtain ⟨fr, hfr, -⟩ := hH.2 B A 1 2 (cmLat Φ0 𝔟) (cmLat Φ 𝔞) θB θ hdimB hdimA hθB hθ (Mv κ r)
    (hMlat r isIntegral_root)
  obtain ⟨F1, hF1, hF1dd⟩ := exists_bcHom σ f1.hom
  obtain ⟨Fr, hFr, hFrdd⟩ := exists_bcHom σ fr.hom
  -- `θ₀(z) = f₁^σ(θ'_B(ℓ₁ z)) · f₂^σ(θ'_B(ℓ₂ z))` on `A^σ = bcC A σ`
  let θ0 : (Fin 2 → ℂ) → CPts (bcC A (σ : ℂ →+* ℂ)) (RingHom.id ℂ) :=
    fun z => (θB' (ell0 z) ≫ F1) * (θB' (ell1 z) ≫ Fr)
  have hdd0 : ∀ z, dd σ A (θ0 z) = dd σ B (θB' (ell0 z)) ≫ f1.hom * dd σ B (θB' (ell1 z)) ≫ fr.hom := by
    intro z
    show dd σ A ((θB' (ell0 z) ≫ F1) * (θB' (ell1 z) ≫ Fr)) = _
    rw [dd_mul, hF1dd, hFrdd]
  -- analyticity: `θ₀ = ψ ∘ (M₁ + M₂)` for a uniformization `ψ` of `A^σ`
  obtain ⟨g', Λ', ψ, -, -, hψ⟩ := ZInQ.LeafPush2.exists_isUniformization_of_leaf hUL (bcC A (σ : ℂ →+* ℂ))
  obtain ⟨M1, hM1⟩ := analyticHomLiftC_of_leaf hUL _ _ _ _ _ hψ _
    (isAnalyticHom_comp (isAnalyticHom_lin (isAnalyticHom_of_unif hθB') ell0) F1)
  obtain ⟨M2, hM2⟩ := analyticHomLiftC_of_leaf hUL _ _ _ _ _ hψ _
    (isAnalyticHom_comp (isAnalyticHom_lin (isAnalyticHom_of_unif hθB') ell1) Fr)
  have hθ0ψ : θ0 = fun z => ψ ((M1 + M2) z) := by
    funext z
    rw [LinearMap.add_apply, hψ.1, hM1, hM2]
  have hθ0an : IsAnalyticHom (RingHom.id ℂ) θ0 := by
    rw [hθ0ψ]; exact isAnalyticHom_lin (isAnalyticHom_of_unif hψ) (M1 + M2)
  -- `m 𝔞 ⊆ 𝔠 = 𝔟 + 𝔟√2`
  let 𝔠 : AddSubgroup (EK K) := 𝔟.comap (crd 0).toAddMonoidHom ⊓ 𝔟.comap (crd 1).toAddMonoidHom
  have h𝔠 : ∀ i, ∀ e ∈ 𝔠, crd i e ∈ 𝔟 := by
    intro i e he
    fin_cases i
    · exact he.1
    · exact he.2
  obtain ⟨D0, hD0, hD0'⟩ := exists_den_lin (crd 0 : EK K →ₗ[ℚ] K)
  obtain ⟨D1, hD1, hD1'⟩ := exists_den_lin (crd 1 : EK K →ₗ[ℚ] K)
  have hDint : ∀ i, ∀ o : 𝓞 (EK K), IsIntegral ℤ (((D0 * D1 : ℕ) : K) * crd i (o : EK K)) := by
    intro i o
    fin_cases i
    · have := (hD0' o).mul (isIntegral_algebraMap (R := ℤ) (A := K) (x := (D1 : ℤ)))
      convert this using 1; push_cast; ring
    · have := (hD1' o).mul (isIntegral_algebraMap (R := ℤ) (A := K) (x := (D0 : ℤ)))
      convert this using 1; push_cast; ring
  set m : ℕ := N * (D0 * D1) * d with hmdef
  have hmpos : 0 < m := Nat.mul_pos (Nat.mul_pos hN (Nat.mul_pos hD0 hD1)) hd
  have hmcrd : ∀ i, ∀ x ∈ 𝔞, (m : K) * crd i x ∈ 𝔟 := by
    intro i x hx
    refine mem_nO.2 ⟨⟨_, hDint i ⟨(d : EK K) * x, hda x hx⟩⟩, ?_⟩
    show (N : K) * (((D0 * D1 : ℕ) : K) * crd i ((d : EK K) * x)) = (m : K) * crd i x
    rw [crd_natCast_mul, hmdef]; push_cast; ring
  have hm : ∀ x ∈ 𝔞, (m : EK K) * x ∈ 𝔠 := by
    intro x hx
    refine ⟨?_, ?_⟩
    · show crd 0 ((m : EK K) * x) ∈ 𝔟
      rw [crd_natCast_mul]; exact hmcrd 0 x hx
    · show crd 1 ((m : EK K) * x) ∈ 𝔟
      rw [crd_natCast_mul]; exact hmcrd 1 x hx
  -- the torsion relation for `θ₀`
  have hrelA : ∀ x y : EK K, t * (1 ⊗ₜ y) - 1 ⊗ₜ x ∈ latHat 𝔞 →
      dd σ A (θ0 (cmVec Φ y)) = θ (cmVec Φ x) := by
    intro x y hxy
    obtain ⟨a, ha, hrem⟩ := latHat_decomp hmpos hm hxy
    have hrem' : t * (1 ⊗ₜ y) - 1 ⊗ₜ (x + a) ∈ latHat 𝔠 := by
      have e : t * (1 ⊗ₜ[ℚ] y) - (1 : AQ) ⊗ₜ[ℚ] (x + a) = t * (1 ⊗ₜ y) - 1 ⊗ₜ x - 1 ⊗ₜ a := by
        rw [TensorProduct.tmul_add]; abel
      rw [e]; exact hrem
    have hcomp : ∀ i, tK * (1 ⊗ₜ crd i y) - 1 ⊗ₜ crd i (x + a) ∈ latHat 𝔟 := by
      intro i
      have := crdHat_latHat i (h𝔠 i) hrem'
      rwa [map_sub, htt, crdHat_inclA_mul, crdHat_tmul, crdHat_tmul] at this
    rw [hdd0, ell0_cmVec, ell1_cmVec, hddB _ _ (hcomp 0), hddB _ _ (hcomp 1), ← hf1, ← hfr, ← hθ.1,
      cmVec_decomp, map_add, hθ.1, (hθ.2.1 _).2 (mem_cmLat.2 ⟨a, ha, rfl⟩), _root_.mul_one]
  -- every element of `E` has a multiple in `𝔞`
  have hbdense : ∀ e : EK K, ∃ k : ℕ, 0 < k ∧ (k : EK K) * e ∈ 𝔞 := by
    intro e
    obtain ⟨y, hy0, hy⟩ := exists_integral_multiples ℤ ℚ (L := EK K) {e}
    have hye := natAbs_mul_integral (hy e (Finset.mem_singleton_self e))
    refine ⟨N * y.natAbs, Nat.mul_pos hN (Int.natAbs_pos.2 hy0), ?_⟩
    have := hNa ⟨_, hye⟩
    rw [show ((N * y.natAbs : ℕ) : EK K) * e = (N : EK K) * ((y.natAbs : EK K) * e) by push_cast; ring]
    exact this
  -- the kernel
  have hlift : ∀ (u : Fin 1 → ℂ) (c : K), dd σ B (θB' u) = θB (cmVec Φ0 c) → (m : K) * c ∈ 𝔟 →
      ∃ y : K, u = cmVec Φ0 y := by
    intro u c huc hc
    have hpow : θB' (m • u) = 1 := by
      rw [map_nsmul_of_hom hθB'.1]
      apply dd_injective σ B
      change ddHom σ B _ = ddHom σ B 1
      rw [map_pow, map_one]
      change (dd σ B (θB' u)) ^ m = 1
      rw [huc, ← map_nsmul_of_hom hθB.1, ← map_nsmul, nsmul_eq_mul]
      exact (hθB.2.1 _).2 ((cmVec_mem_cmLat one_pos).2 hc)
    obtain ⟨y1, -, hcy1⟩ := mem_cmLat.1 ((hθB'.2.1 _).1 hpow)
    refine ⟨((m : ℕ) : ℚ)⁻¹ • y1, ?_⟩
    have hk0 : ((m : ℕ) : ℝ) ≠ 0 := by exact_mod_cast hmpos.ne'
    rw [cmVec_ratSmul, hcy1, ← Nat.cast_smul_eq_nsmul ℝ, smul_smul]
    push_cast
    rw [inv_mul_cancel₀ (by exact_mod_cast hk0), one_smul]
  have hker : ∀ z, θ0 z = 1 ↔ z ∈ cmLat Φ (latAct t 𝔞) := by
    intro z
    constructor
    · intro hz
      have h1 : dd σ A (θ0 z) = 1 := by rw [hz, dd_one]
      have h1' := h1
      rw [hdd0] at h1
      obtain ⟨v0, hv0⟩ := hθB.2.2.1 (dd σ B (θB' (ell0 z)))
      obtain ⟨v1, hv1⟩ := hθB.2.2.1 (dd σ B (θB' (ell1 z)))
      rw [← hv0, ← hv1, ← hf1, ← hfr, ← hθ.1] at h1
      obtain ⟨e, he, hee⟩ := mem_cmLat.1 ((hθ.2.1 _).1 h1)
      have hv0e : v0 = cmVec Φ0 (crd 0 e) := by
        rw [← ell0_cmVec, hee, map_add, ell0_Mv1, ell0_Mvr, add_zero]
      have hv1e : v1 = cmVec Φ0 (crd 1 e) := by
        rw [← ell1_cmVec, hee, map_add, ell1_Mv1, ell1_Mvr, zero_add]
      obtain ⟨y0, hy0⟩ := hlift (ell0 z) (crd 0 e) (by rw [← hv0, hv0e]) (hmcrd 0 e he)
      obtain ⟨y1, hy1⟩ := hlift (ell1 z) (crd 1 e) (by rw [← hv1, hv1e]) (hmcrd 1 e he)
      set yE : EK K := algebraMap K (EK K) y0 + algebraMap K (EK K) y1 * r with hyE
      have hzy : cmVec Φ yE = z := by
        rw [← cmVec_decomp, hyE, crd_mk0, crd_mk1, ← hy0, ← hy1, span_Mv]
      obtain ⟨x, hx⟩ := exists_approx_latHat hbdense (t * (1 ⊗ₜ yE))
      have h2 := hrelA x yE hx
      rw [hzy, h1'] at h2
      have hx𝔞 : x ∈ 𝔞 := (cmVec_mem_cmLat two_pos).1 ((hθ.2.1 _).1 h2.symm)
      refine mem_cmLat.2 ⟨yE, ?_, hzy⟩
      show t * (1 ⊗ₜ yE) ∈ latHat 𝔞
      have e : t * (1 ⊗ₜ[ℚ] yE) = (t * (1 ⊗ₜ yE) - 1 ⊗ₜ x) + (1 : AQ) ⊗ₜ[ℚ] x := by abel
      rw [e]
      exact add_mem hx (one_tmul_mem_latHat hx𝔞)
    · intro hz
      obtain ⟨y, hy, rfl⟩ := mem_cmLat.1 hz
      have hy' : t * (1 ⊗ₜ y) - 1 ⊗ₜ (0 : EK K) ∈ latHat 𝔞 := by
        rw [TensorProduct.tmul_zero, sub_zero]; exact hy
      apply dd_injective σ A
      rw [dd_one, hrelA 0 y hy', map_zero]
      exact map_zero_of_hom hθ.1
  -- surjectivity
  have hsurjB : ∀ Q : CPts B (RingHom.id ℂ), ∃ v, dd σ B (θB' v) = Q := by
    intro Q
    obtain ⟨R, hR⟩ := dd_surjective σ B Q
    obtain ⟨v, hv⟩ := hθB'.2.2.1 R
    exact ⟨v, by rw [hv, hR]⟩
  have hsurj : Function.Surjective θ0 := by
    intro P
    obtain ⟨u, hu⟩ := hθ.2.2.1 (dd σ A P)
    obtain ⟨v0, hv0⟩ := hsurjB (θB (ell0 u))
    obtain ⟨v1, hv1⟩ := hsurjB (θB (ell1 u))
    refine ⟨Mv κ 1 v0 + Mv κ r v1, dd_injective σ A ?_⟩
    rw [hdd0, map_add, map_add, ell0_Mv1, ell0_Mvr, ell1_Mv1, ell1_Mvr, add_zero, zero_add, hv0, hv1,
      ← hf1, ← hfr, ← hθ.1, span_Mv, hu]
  have hθ0U : IsUniformization (RingHom.id ℂ) (cmLat Φ (latAct t 𝔞)) θ0 :=
    (isUniformization_iff _ _ _).2 ⟨hθ0an, hker, hsurj⟩
  -- transport to the given `A'`
  obtain ⟨θ', hθ', hθ'rel⟩ := exists_unif_of_bc σ h hpb hone hθ0U
  refine ⟨θ', hθ', fun x y hxy => ?_⟩
  have := hθ'rel (cmVec Φ y)
  rw [hrelA x y hxy] at this
  exact this

/-- **The reduction from the induced type of `E = K(√2)`**, from the main theorem for primitive types. -/
theorem mainTheoremCMEK_of_prim (ε : ℤˣ) (hP : MainTheoremCMSignPrim ε) (hX : CMAbVarExists)
    (hUL : BPAnalytic.Uniformization.UniformizationLeafAll) (hG : ZInQ.HomLattice.GAGAMorphism) :
    MainTheoremCMEK ε :=
  mainTheoremCMEK_of_quad ε (signQuad_of_signPrim hP) hX hUL hG

/-- **The reflex norm of the induced type is the reflex norm of `(K, κ)` followed by `𝔸_f ⊗ K → 𝔸_f ⊗ E`**
(with the reflex field `κ(K)` of both, `QMRecPrinted.reflex_eq` and `reflex1`). -/
theorem reflexNorm_rhoK_eq (K : Type) [Field K] [NumberField K] [Fact (Irreducible (X ^ 2 - C (2 : K)))]
    (u : (FiniteAdeleRing (𝓞 K) K)ˣ) :
    (reflexNorm rhoK u : AQ ⊗[ℚ] EK K) = inclA (reflexNorm rho1 u : AQ ⊗[ℚ] K) := by
  rw [reflexNorm_rhoK, reflexNorm_rho1]

/-- **An abelian variety of the induced type `(K(√2), PhiE κ)` is isogenous to the square of an elliptic curve of
type `(K, κ)`**: for `θ : ℂ²/Φ(𝔞) ≅ A(ℂ)` there are `B` with `θ_B : ℂ/κ(𝔟) ≅ B(ℂ)` (`𝔟` an `𝓞_K`-ideal) and
homomorphisms `f₁, f₂ : B → A` with `θ(w₁Φ(1) + w₂Φ(√2)) = f₁(θ_B(w₁)) · f₂(θ_B(w₂))`, so that
`B × B → A`, `(P, Q) ↦ f₁(P) f₂(Q)`, is surjective with kernel killed by some `m > 0`. -/
theorem exists_isogeny_EK (hX : CMAbVarExists) (hUL : BPAnalytic.Uniformization.UniformizationLeafAll)
    (hG : ZInQ.HomLattice.GAGAMorphism) (K : Type) [Field K] [NumberField K] [IsTotallyComplex K]
    (hK : Module.finrank ℚ K = 2) [Fact (Irreducible (X ^ 2 - C (2 : K)))] (κ : K →+* ℂ)
    (A : PkgI3.AbVar ℂ) (hdimA : A.dim = ((2 : ℕ) : WithBot ℕ∞)) (𝔞 : AddSubgroup (EK K))
    (θ : (Fin 2 → ℂ) → CPts A (RingHom.id ℂ)) (hθ : IsUniformization (RingHom.id ℂ) (cmLat (PhiE κ) 𝔞) θ) :
    ∃ (B : PkgI3.AbVar ℂ) (θB : (Fin 1 → ℂ) → CPts B (RingHom.id ℂ)) (𝔟 : AddSubgroup K)
      (f₁ f₂ : PkgI3.AbVar.Hom B A) (m : ℕ),
      B.dim = ((1 : ℕ) : WithBot ℕ∞) ∧ IsOLattice 𝔟 ∧
      IsUniformization (RingHom.id ℂ) (cmLat (fun _ : Fin 1 => κ) 𝔟) θB ∧ 0 < m ∧
      (∀ w₁ w₂ : Fin 1 → ℂ, θ (w₁ 0 • cmVec (PhiE κ) 1 + w₂ 0 • cmVec (PhiE κ) (AdjoinRoot.root _)) =
        θB w₁ ≫ f₁.hom * θB w₂ ≫ f₂.hom) ∧
      (∀ P : CPts A (RingHom.id ℂ), ∃ Q₁ Q₂ : CPts B (RingHom.id ℂ), P = Q₁ ≫ f₁.hom * Q₂ ≫ f₂.hom) ∧
      (∀ Q₁ Q₂ : CPts B (RingHom.id ℂ), Q₁ ≫ f₁.hom * Q₂ ≫ f₂.hom = 1 → Q₁ ^ m = 1 ∧ Q₂ ^ m = 1) := by
  have hH : ZInQ.HomUnify.HomLatticeCorr := AvSplit.Final.h69 hUL hG
  haveI : IsCMField K := isCMField_K hK
  haveI : IsCMField (EK K) := isCMField_EK hK
  set Φ := PhiE κ with hΦ
  set Φ0 : Fin 1 → K →+* ℂ := fun _ => κ with hΦ0
  set r : EK K := AdjoinRoot.root (X ^ 2 - C (2 : K)) with hr
  have hdeg : Module.finrank ℚ (EK K) = 2 * 2 := by rw [finrank_EK hK]
  have hinj1 := type_inj1 κ
  obtain ⟨⟨N, hN, hNa⟩, ⟨d, hd, hda⟩⟩ := lattice_of_unif hUL Φ two_pos hdeg hθ
  let 𝔟 : AddSubgroup K := nO N
  have hOL : IsOLattice 𝔟 := by
    refine ⟨fun o x hx => ?_, ⟨N, hN, fun o => mem_nO.2 ⟨o, rfl⟩⟩, ⟨1, one_pos, fun x hx => ?_⟩⟩
    · obtain ⟨o', rfl⟩ := mem_nO.1 hx
      exact mem_nO.2 ⟨o * o', by push_cast; ring⟩
    · obtain ⟨o, rfl⟩ := mem_nO.1 hx
      have := coe_integral ((N : 𝓞 K) * o)
      push_cast at this
      rw [Nat.cast_one, _root_.one_mul]; exact this
  obtain ⟨ζ0, hζc, hζi⟩ := exists_zeta Φ0 hinj1
  obtain ⟨y, hy0, hy⟩ := exists_integral_multiples ℤ ℚ (L := K) {ζ0}
  have hyζ := hy ζ0 (Finset.mem_singleton_self ζ0)
  have hζint : IsIntegral ℤ ((y * y) • ζ0) := by
    rw [mul_smul, zsmul_eq_mul]
    exact (by simpa using (isIntegral_algebraMap (R := ℤ) (A := K) (x := y)) : IsIntegral ℤ (y : K)).mul hyζ
  have hζ : IsRiemannDatum Φ0 𝔟 ((y * y) • ζ0) := by
    refine ⟨by rw [map_zsmul, hζc, smul_neg], fun i => ?_, fun x hx x' hx' => ?_⟩
    · rw [map_zsmul, zsmul_eq_mul, Complex.mul_im, Complex.intCast_re, Complex.intCast_im, zero_mul,
        add_zero]
      exact mul_pos (by exact_mod_cast mul_self_pos.2 hy0) (hζi i)
    · obtain ⟨o, rfl⟩ := mem_nO.1 hx
      obtain ⟨o', rfl⟩ := mem_nO.1 hx'
      apply trace_int
      have h1 : IsIntegral ℤ ((N : K) * (o : K)) := by
        have := coe_integral ((N : 𝓞 K) * o); push_cast at this; exact this
      have h2 : IsIntegral ℤ ((N : K) * (o' : K)) := by
        have := coe_integral ((N : 𝓞 K) * o'); push_cast at this; exact this
      exact (hζint.mul h1).mul (h2.map (IsCMField.complexConj K))
  obtain ⟨B, θB, hdimB, hθB⟩ := hX K 1 Φ0 (by rw [hK]) hinj1 𝔟 hOL ⟨_, hζ⟩
  have hMlat : ∀ α : EK K, IsIntegral ℤ α → ∀ z ∈ cmLat Φ0 𝔟, Mv κ α z ∈ cmLat Φ 𝔞 := by
    intro α hα z hz
    obtain ⟨b, hb, rfl⟩ := mem_cmLat.1 hz
    obtain ⟨o, rfl⟩ := mem_nO.1 hb
    refine mem_cmLat.2 ⟨_, hNa ⟨algebraMap K (EK K) (o : K) * α,
      ((coe_integral o).map (IsScalarTower.toAlgHom ℤ K (EK K))).mul hα⟩, ?_⟩
    rw [Mv_cmVec]
    congr 1
    show (N : EK K) * (algebraMap K (EK K) (o : K) * α) = algebraMap K (EK K) ((N : K) * (o : K)) * α
    rw [map_mul, map_natCast, _root_.mul_assoc]
  obtain ⟨f1, hf1, -⟩ := hH.2 B A 1 2 (cmLat Φ0 𝔟) (cmLat Φ 𝔞) θB θ hdimB hdimA hθB hθ (Mv κ 1)
    (hMlat 1 isIntegral_one)
  obtain ⟨fr, hfr, -⟩ := hH.2 B A 1 2 (cmLat Φ0 𝔟) (cmLat Φ 𝔞) θB θ hdimB hdimA hθB hθ (Mv κ r)
    (hMlat r isIntegral_root)
  obtain ⟨D0, hD0, hD0'⟩ := exists_den_lin (crd 0 : EK K →ₗ[ℚ] K)
  obtain ⟨D1, hD1, hD1'⟩ := exists_den_lin (crd 1 : EK K →ₗ[ℚ] K)
  have hDint : ∀ i, ∀ o : 𝓞 (EK K), IsIntegral ℤ (((D0 * D1 : ℕ) : K) * crd i (o : EK K)) := by
    intro i o
    fin_cases i
    · have := (hD0' o).mul (isIntegral_algebraMap (R := ℤ) (A := K) (x := (D1 : ℤ)))
      convert this using 1; push_cast; ring
    · have := (hD1' o).mul (isIntegral_algebraMap (R := ℤ) (A := K) (x := (D0 : ℤ)))
      convert this using 1; push_cast; ring
  set m : ℕ := N * (D0 * D1) * d with hmdef
  have hmpos : 0 < m := Nat.mul_pos (Nat.mul_pos hN (Nat.mul_pos hD0 hD1)) hd
  have hmcrd : ∀ i, ∀ x ∈ 𝔞, (m : K) * crd i x ∈ 𝔟 := by
    intro i x hx
    refine mem_nO.2 ⟨⟨_, hDint i ⟨(d : EK K) * x, hda x hx⟩⟩, ?_⟩
    show (N : K) * (((D0 * D1 : ℕ) : K) * crd i ((d : EK K) * x)) = (m : K) * crd i x
    rw [crd_natCast_mul, hmdef]; push_cast; ring
  have hfor : ∀ w₁ w₂ : Fin 1 → ℂ, θ (w₁ 0 • cmVec Φ 1 + w₂ 0 • cmVec Φ r) = θB w₁ ≫ f1.hom * θB w₂ ≫ fr.hom := by
    intro w₁ w₂
    rw [← Mv_apply, ← Mv_apply, hθ.1, hf1, hfr]
  refine ⟨B, θB, 𝔟, f1, fr, m, hdimB, hOL, hθB, hmpos, hfor, fun P => ?_, fun Q₁ Q₂ hQ => ?_⟩
  · obtain ⟨u, rfl⟩ := hθ.2.2.1 P
    refine ⟨θB (ell0 u), θB (ell1 u), ?_⟩
    rw [← hfor, ← Mv_apply, ← Mv_apply, span_Mv]
  · obtain ⟨v0, rfl⟩ := hθB.2.2.1 Q₁
    obtain ⟨v1, rfl⟩ := hθB.2.2.1 Q₂
    rw [← hfor, ← Mv_apply, ← Mv_apply] at hQ
    obtain ⟨e, he, hee⟩ := mem_cmLat.1 ((hθ.2.1 _).1 hQ)
    have hv0e : v0 = cmVec Φ0 (crd 0 e) := by
      rw [← ell0_cmVec, hee, map_add, ell0_Mv1, ell0_Mvr, add_zero]
    have hv1e : v1 = cmVec Φ0 (crd 1 e) := by
      rw [← ell1_cmVec, hee, map_add, ell1_Mv1, ell1_Mvr, zero_add]
    have key : ∀ (v : Fin 1 → ℂ) (c : K), v = cmVec Φ0 c → (m : K) * c ∈ 𝔟 → θB v ^ m = 1 := by
      intro v c hv hc
      rw [← map_nsmul_of_hom hθB.1, hv, ← map_nsmul, nsmul_eq_mul]
      exact (hθB.2.1 _).2 ((cmVec_mem_cmLat one_pos).2 hc)
    exact ⟨key v0 _ hv0e (hmcrd 0 e he), key v1 _ hv1e (hmcrd 1 e he)⟩

/-- **Sanity check: the induced type of `K(√2)` is not primitive** (it is induced from `K`), so the primitive leaf
does not apply to it directly and the reduction `mainTheoremCMEK_of_prim` is needed. -/
theorem not_isPrimitiveType_PhiE {K : Type} [Field K] [NumberField K] [Fact (Irreducible (X ^ 2 - C (2 : K)))]
    (κ : K →+* ℂ) : ¬ IsPrimitiveType (PhiE κ) := by
  intro hprim
  have hF := hprim (algebraMap K (EK K)).fieldRange (fun i ψ hψ => by
    have hψK : ∀ k : K, ψ (algebraMap K (EK K) k) = κ k := fun k => by
      rw [hψ _ ⟨k, rfl⟩, phiE_of]
    have hr : ψ (AdjoinRoot.root _) ^ 2 = ((√2 : ℝ) : ℂ) ^ 2 := by
      rw [← map_pow, root_sq, map_ofNat, QMRecPrinted.sqrt2_sq]
    have hval : ∀ c : ℂ, ψ (AdjoinRoot.root _) = c → ∀ e : EK K,
        ψ e = κ (bK.repr e 0) + κ (bK.repr e 1) * c := fun c hc e => by
      conv_lhs => rw [decomp e]
      rw [map_add, map_mul, hψK, hψK, hc]
    rcases sq_eq_sq_iff_eq_or_eq_neg.1 hr with h0 | h1
    · exact ⟨0, RingHom.ext fun e => by rw [hval _ h0 e, phi0_apply]⟩
    · exact ⟨1, RingHom.ext fun e => by rw [hval _ h1 e, phi1_apply]⟩)
  have hr : AdjoinRoot.root (X ^ 2 - C (2 : K)) ∈ (algebraMap K (EK K)).fieldRange := by
    rw [hF]; trivial
  obtain ⟨k, hk⟩ := hr
  have h1 := crd_mk1 (K := K) k 0
  have h2 := crd_mk1 (K := K) 0 1
  rw [map_zero, zero_mul, add_zero, hk] at h1
  rw [map_zero, map_one, _root_.one_mul, zero_add] at h2
  exact one_ne_zero (h2.symm.trans h1)

/-- **The main theorem of CM for primitive types** (every lattice, existential sign) from the primitive print. -/
theorem mainTheoremCMPrim_of_polPrim (hP : MainTheoremCMPolPrim) (hX : CMAbVarExists)
    (hUL : BPAnalytic.Uniformization.UniformizationLeafAll) (hG : ZInQ.HomLattice.GAGAMorphism) :
    ∃ ε : ℤˣ, MainTheoremCMSignPrim ε := by
  obtain ⟨ε, h⟩ := hP
  exact ⟨ε, mainTheoremCMSignPrim_of_polar ε h hX hUL hG⟩

/-- **The main theorem of CM at the induced type of `K(√2)`** (existential sign) from the primitive print. -/
theorem mainTheoremCMEK_of_polPrim (hP : MainTheoremCMPolPrim) (hX : CMAbVarExists)
    (hUL : BPAnalytic.Uniformization.UniformizationLeafAll) (hG : ZInQ.HomLattice.GAGAMorphism) :
    ∃ ε : ℤˣ, MainTheoremCMEK ε := by
  obtain ⟨ε, h⟩ := hP
  exact ⟨ε, mainTheoremCMEK_of_prim ε (mainTheoremCMSignPrim_of_polar ε h hX hUL hG) hX hUL hG⟩

/-- **The main theorem of CM at the induced type of `K(√2)`** (existential sign) from the quadratic print. -/
theorem mainTheoremCMEK_of_polQuad (hP : MainTheoremCMPolQuad) (hX : CMAbVarExists)
    (hUL : BPAnalytic.Uniformization.UniformizationLeafAll) (hG : ZInQ.HomLattice.GAGAMorphism) :
    ∃ ε : ℤˣ, MainTheoremCMEK ε := by
  obtain ⟨ε, h⟩ := hP
  exact ⟨ε, mainTheoremCMEK_of_quad ε (mainTheoremCMSignQuad_of_polar ε h hX hUL hG) hX hUL hG⟩

end EK

/-! ## §8 The consumers

`qmReciprocityL3_of_ek` is a copy of `QMRecPrinted.qmReciprocityL3_of_printed`
(`ZInQKernel/Contrib/OneProof/QMRecPrinted.lean`, wip/mtcm-polar 50dcdc48, lines 880-1073) whose only change is the
hypothesis `∃ ε, MainTheoremCMEK ε` in place of `MainTheoremCM`, applied at the same instance (line 934 there).
`shimuraMainCM_of_arithQuad` is a copy of `HcmPrinted.shimuraMainCM_of_printed`
(`ZInQKernel/Contrib/OneProof/ShimuraMainCMPrinted.lean`, lines 1189-1256) whose only change is the hypothesis
`MainTheoremCMSignQuad 1` in place of `MainTheoremCMArith`, applied at the same instance (line 1237 there) with the
extra argument `finrank_QNeg`. -/

section QMRec

open LeafQM LeafQM.AV
open scoped FiniteAdeleExtension MonObj
open Polynomial ShimuraSplit2

/-- **`QMReciprocityL3` from the main theorem of CM at the induced type of `K(√2)`** (and `HomLatticeCorr`). -/
theorem qmReciprocityL3_of_ek (hM : ∃ ε : ℤˣ, MainTheoremCMEK ε) (hC : ZInQ.HomUnify.HomLatticeCorr) :
    QMReciprocityL3 := by
  obtain ⟨ε, hMain⟩ := hM
  refine ⟨ε, true, ?_⟩
  intro K _ _ _ hK κ q z hz σ s hs g P P' hbc hP
  simp only [if_true] at hz
  haveI : Fact (Irreducible (X ^ 2 - C (2 : K))) := ⟨irr_fE hK⟩
  haveI : IsCMField (EK K) := isCMField_EK hK
  obtain ⟨Φu, hU, hI, hL⟩ := hP
  obtain ⟨g0, hpb, hιbc, hηbc⟩ := hbc
  set Φ := PhiE κ with hΦ
  set 𝔞 : AddSubgroup (EK K) := (latB g).comap (beta q).toAddMonoidHom with h𝔞
  set u : BAQˣ := qHatU q s ^ (ε : ℤ) with hu
  set t : AQ ⊗[ℚ] EK K := ((reflexNorm rhoK (IdeleGroup.toFiniteIdele (𝓞 K) K s) ^ (ε : ℤ) :
      (AQ ⊗[ℚ] EK K)ˣ) : AQ ⊗[ℚ] EK K) with ht
  have hβ : ∀ x : LeafQM.B, beta q ((betaE hK hz).symm x) = x := fun x => by
    rw [← betaE_apply hK hz, LinearEquiv.apply_symm_apply]
  -- `θ = Φ_u ∘ D_z`, uniformizing `A` by `Φ(𝔞)`
  let θ : (Fin 2 → ℂ) → CPts P.A (RingHom.id ℂ) := fun w => Φu (Dz z w)
  have hθ : ∀ e, θ (cmVec Φ e) = Φu ((iotaC (beta q e)).mulVec ![(z : ℂ), 1]) := fun e => by
    rw [vec_beta' hz]
  have hlat : cmLat Φ 𝔞 = (vecLat (z : ℂ) g).map ((Dz z).symm.toLinearMap.restrictScalars ℤ) := by
    rw [← cmLat_map_Dz hK hz 𝔞 g (fun e => Iff.rfl), map_symm_map]
  have hθU : IsUniformization (RingHom.id ℂ) (cmLat Φ 𝔞) θ := by
    rw [hlat]
    convert HDec.HSyn.G0Split.FibreQM.isUniformization_comp hU (Dz z).symm using 2
    simp [θ]
  -- `(A, θ)` is of type `(E, Φ)`
  have hType : IsOfType Φ 𝔞 θ := by
    intro e he
    let M : (Fin 2 → ℂ) →ₗ[ℂ] (Fin 2 → ℂ) := Matrix.mulVecLin (Matrix.diagonal fun i => Φ i e)
    have hMv : ∀ v, M v = fun i => Φ i e * v i := fun v => by
      funext i; simp [M, Matrix.mulVec_diagonal]
    have hMD : ∀ e', M (Dz z (cmVec Φ e')) = Dz z (cmVec Φ (e * e')) := fun e' => by
      rw [hMv]; funext i; fin_cases i <;> simp [Dz_apply, cmVec] <;> ring
    have hMΛ : ∀ v ∈ vecLat (z : ℂ) g, M v ∈ vecLat (z : ℂ) g := by
      intro v hv
      obtain ⟨x, hx, rfl⟩ := mem_vecLat.1 hv
      obtain ⟨e', rfl⟩ := (betaE hK hz).surjective x
      rw [betaE_apply, vec_beta' hz, hMD, ← vec_beta' hz]
      exact mem_vecLat.2 ⟨_, he _ hx, rfl⟩
    obtain ⟨f, hf, -⟩ := hC.2 P.A P.A 2 2 _ _ Φu Φu (dim_two P) (dim_two P) hU hU M hMΛ
    refine ⟨f, fun w => ?_⟩
    show Φu (Dz z (fun i => Φ i e * w i)) = Φu (Dz z w) ≫ f.hom
    rw [← hf]
    congr 1
    rw [hMv]; funext i; fin_cases i <;> simp [Dz_apply] <;> ring
  -- the identity sections correspond
  have h1pt : (1 : CPts P'.A (RingHom.id ℂ)).left ≫ g0 =
      Spec.map (CommRingCat.ofHom (σ : ℂ →+* ℂ)) ≫ (1 : CPts P.A (RingHom.id ℂ)).left := by
    have e := hηbc 0
    simp only [map_zero, toMul_zero] at e
    exact e
  -- apply the main theorem of CM
  obtain ⟨θ', hθ'U, hrel⟩ := hMain K hK κ σ s hs P.A (dim_two P) 𝔞 θ hθU hType P'.A g0 hpb h1pt
  rw [← ht] at hθ'U hrel
  -- dictionary
  have hbt : ∀ w, betaHat q (t * w) = betaHat q w * u := betaHat_t q s ε
  have hact : ∀ e, e ∈ latAct t 𝔞 ↔ beta q e ∈ latB (u * g) := by
    intro e
    show t * (1 ⊗ₜ e) ∈ latHat 𝔞 ↔ bEmb (beta q e) * ((u * g : BAQˣ) : BAQ) ∈ OhatQ
    rw [mem_latHat_iff hK hz g, hbt, betaHat_one_tmul, Units.val_mul, mul_assoc]
  have hrelB : ∀ x y : EK K, (bEmb (beta q y) * u - bEmb (beta q x)) * g ∈ OhatQ →
      (θ' (cmVec Φ y)).left ≫ g0 = Spec.map (CommRingCat.ofHom (σ : ℂ →+* ℂ)) ≫
        (Φu ((iotaC (beta q x)).mulVec ![(z : ℂ), 1])).left := by
    intro x y hxy
    rw [← hθ x]
    apply hrel x y
    rw [mem_latHat_iff hK hz g, map_sub, hbt, betaHat_one_tmul, betaHat_one_tmul]
    exact hxy
  -- `Φ_u' = θ' ∘ D_z⁻¹`
  let Φu' : (Fin 2 → ℂ) → CPts P'.A (RingHom.id ℂ) := fun v => θ' ((Dz z).symm v)
  have hθ' : ∀ e, Φu' ((iotaC (beta q e)).mulVec ![(z : ℂ), 1]) = θ' (cmVec Φ e) := fun e => by
    show θ' ((Dz z).symm _) = _
    rw [vec_beta' hz, LinearEquiv.symm_apply_apply]
  have hU' : IsUniformization (RingHom.id ℂ) (vecLat (z : ℂ) (u * g)) Φu' := by
    rw [← cmLat_map_Dz hK hz (latAct t 𝔞) (u * g) hact]
    exact HDec.HSyn.G0Split.FibreQM.isUniformization_comp hθ'U (Dz z)
  -- the conjugate of `Φ_u(v_x)` is `Φ_u'(v_y)`
  have hconj : ∀ x y : EK K, (bEmb (beta q y) * u - bEmb (beta q x)) * g ∈ OhatQ →
      (Φu' ((iotaC (beta q y)).mulVec ![(z : ℂ), 1])).left ≫ g0 =
        Spec.map (CommRingCat.ofHom (σ : ℂ →+* ℂ)) ≫
          (Φu ((iotaC (beta q x)).mulVec ![(z : ℂ), 1])).left := by
    intro x y hxy
    rw [hθ']
    exact hrelB x y hxy
  have hexists : ∀ y : EK K, ∃ x : EK K, (bEmb (beta q y) * u - bEmb (beta q x)) * g ∈ OhatQ := by
    intro y
    obtain ⟨x0, hx0⟩ := exists_approx (bEmb (beta q y) * u) g
    refine ⟨(betaE hK hz).symm x0, ?_⟩
    rw [hβ]
    have e : (bEmb (beta q y) * u - bEmb x0) * g = -((bEmb x0 - bEmb (beta q y) * u) * g) := by noncomm_ring
    rw [e]; exact OhatQ_neg hx0
  refine ⟨Φu', hU', ?_, ?_⟩
  · -- `ι`-compatibility
    intro a v
    obtain ⟨T, hT⟩ := hC.1 ℂ P'.A P'.A (RingHom.id ℂ) 2 2 _ _ Φu' Φu' (dim_two P') (dim_two P') hU' hU'
      (P'.q.iota a)
    let Dl : (Fin 2 → ℂ) →ₗ[ℂ] (Fin 2 → ℂ) := T - Matrix.mulVecLin (iotaC (a : LeafQM.B))
    have h1 : ∀ y : EK K, Dl ((iotaC (beta q y)).mulVec ![(z : ℂ), 1]) ∈ vecLat (z : ℂ) (u * g) := by
      intro y
      obtain ⟨x, hxy⟩ := hexists y
      have hya : (iotaC (a : LeafQM.B)).mulVec ((iotaC (beta q y)).mulVec ![(z : ℂ), 1]) =
          (iotaC (beta q ((betaE hK hz).symm ((a : LeafQM.B) * beta q y)))).mulVec ![(z : ℂ), 1] := by
        rw [hβ, map_mul, ← Matrix.mulVec_mulVec]
      have hxa : (iotaC (a : LeafQM.B)).mulVec ((iotaC (beta q x)).mulVec ![(z : ℂ), 1]) =
          (iotaC (beta q ((betaE hK hz).symm ((a : LeafQM.B) * beta q x)))).mulVec ![(z : ℂ), 1] := by
        rw [hβ, map_mul, ← Matrix.mulVec_mulVec]
      have hxya : (bEmb (beta q ((betaE hK hz).symm ((a : LeafQM.B) * beta q y))) * u -
          bEmb (beta q ((betaE hK hz).symm ((a : LeafQM.B) * beta q x)))) * g ∈ OhatQ := by
        rw [hβ, hβ, map_mul, map_mul, mul_assoc, ← mul_sub, mul_assoc]
        exact OhatQ_mul (bEmb_mem_of_inO a.2) hxy
      have heq : Φu' (T ((iotaC (beta q y)).mulVec ![(z : ℂ), 1])) =
          Φu' ((iotaC (a : LeafQM.B)).mulVec ((iotaC (beta q y)).mulVec ![(z : ℂ), 1])) := by
        apply pt_ext hpb
        have hI' := hI a ((iotaC (beta q x)).mulVec ![(z : ℂ), 1])
        rw [qmMat_eq, hxa] at hI'
        rw [hT, Over.comp_left, Category.assoc, hιbc a, ← Category.assoc, hconj x y hxy, hya,
          hconj _ _ hxya, hI', Over.comp_left]
        exact Category.assoc _ _ _
      have hone : Φu' (Dl ((iotaC (beta q y)).mulVec ![(z : ℂ), 1])) = 1 := by
        have e := hU'.1 (Dl ((iotaC (beta q y)).mulVec ![(z : ℂ), 1]))
          ((iotaC (a : LeafQM.B)).mulVec ((iotaC (beta q y)).mulVec ![(z : ℂ), 1]))
        have e2 : Dl ((iotaC (beta q y)).mulVec ![(z : ℂ), 1]) +
            (iotaC (a : LeafQM.B)).mulVec ((iotaC (beta q y)).mulVec ![(z : ℂ), 1]) =
            T ((iotaC (beta q y)).mulVec ![(z : ℂ), 1]) := by
          rw [LinearMap.sub_apply, Matrix.mulVecLin_apply, sub_add_cancel]
        rw [e2, heq] at e
        exact (mul_eq_right.1 e.symm)
      exact (hU'.2.1 _).1 hone
    have h2 : ∀ y : EK K, Dl ((iotaC (beta q y)).mulVec ![(z : ℂ), 1]) = 0 := by
      intro y
      obtain ⟨x0, -, hx0e⟩ := mem_vecLat.1 (h1 y)
      have hx0z : x0 = 0 := by
        apply eq_zero_of_forall_dvd (u * g) x0
        intro N hN
        obtain ⟨xN, hxN, hxNe⟩ := mem_vecLat.1 (h1 ((N : ℚ)⁻¹ • y))
        refine ⟨xN, hxN, vec_inj hK hz ?_⟩
        have hN0 : (N : ℂ) ≠ 0 := by exact_mod_cast hN.ne'
        rw [iotaC_smul_mulVec, hxNe, hx0e, map_smul, iotaC_smul_mulVec, map_smul, smul_smul]
        push_cast
        rw [mul_inv_cancel₀ hN0, one_smul]
      rw [← hx0e, hx0z, map_zero, Matrix.zero_mulVec]
    have hDl : Dl = 0 := by
      apply LinearMap.ext
      intro w
      have e1 := h2 1
      have e2 := h2 (AdjoinRoot.root _)
      rw [vec_beta' hz] at e1 e2
      have hw := span_two κ ((Dz z).symm w)
      rw [LinearMap.zero_apply, ← LinearEquiv.apply_symm_apply (Dz z) w, hw, map_add, map_smul, map_smul,
        map_add, map_smul, map_smul, e1, e2, smul_zero, smul_zero, add_zero]
    have hTv : T v = (iotaC (a : LeafQM.B)).mulVec v := by
      have := LinearMap.congr_fun hDl v
      simp only [Dl, LinearMap.sub_apply, LinearMap.zero_apply, Matrix.mulVecLin_apply] at this
      exact sub_eq_zero.1 this
    rw [← hT v, hTv, qmMat_eq]
  · -- the level structure
    intro a
    obtain ⟨x0, ⟨y0, hy0, hx0⟩, hΦx0⟩ := hL a
    have hxE : beta q ((betaE hK hz).symm ((1 / 3 : ℚ) • x0)) = (1 / 3 : ℚ) • x0 := hβ _
    obtain ⟨y1, hy1⟩ := exists_approx (bEmb (beta q ((betaE hK hz).symm ((1 / 3 : ℚ) • x0))) *
      ((u⁻¹ : BAQˣ) : BAQ)) ((u * g : BAQˣ) : BAQ)
    have hyE : beta q ((betaE hK hz).symm y1) = y1 := hβ _
    set xE := (betaE hK hz).symm ((1 / 3 : ℚ) • x0) with hxEdef
    have hc : (bEmb (beta q ((betaE hK hz).symm y1)) * u - bEmb (beta q xE)) * g ∈ OhatQ := by
      have e : (bEmb (beta q ((betaE hK hz).symm y1)) * u - bEmb (beta q xE)) * g =
          (bEmb y1 - bEmb (beta q xE) * ((u⁻¹ : BAQˣ) : BAQ)) * ((u * g : BAQˣ) : BAQ) := by
        rw [hyE, Units.val_mul, sub_mul, sub_mul, mul_assoc, mul_assoc (bEmb (beta q xE)),
          ← mul_assoc ((u⁻¹ : BAQˣ) : BAQ), Units.inv_mul, one_mul, ← mul_assoc]
      rw [e]; exact hy1
    have hpt : Φu' ((iotaC y1).mulVec ![(z : ℂ), 1]) = Additive.toMul (P'.e.eta a) := by
      apply pt_ext hpb
      have h3 : (((1 / 3 : ℚ)) : ℂ) = (3 : ℂ)⁻¹ := by push_cast; ring
      rw [← hyE]
      refine (hconj xE _ hc).trans (Eq.trans ?_ (hηbc a).symm)
      rw [hxE, iotaC_smul_mulVec, h3, hΦx0]
    refine ⟨(3 : ℚ) • y1, ⟨(bEmb (beta q ((betaE hK hz).symm y1)) * u - bEmb (beta q xE)) * g + y0,
      OhatQ_add hc hy0, ?_⟩, ?_⟩
    · have h3 : (3 : BAQ) * (bEmb (beta q xE) * g) = bEmb (a : LeafQM.B) + 3 * y0 := by
        rw [hxE, map_smul, smul_mul_assoc, three_mul_eq_smul, smul_smul]
        norm_num
        exact hx0
      have e : bEmb (a : LeafQM.B) + 3 * ((bEmb (beta q ((betaE hK hz).symm y1)) * u - bEmb (beta q xE)) * g + y0) =
          bEmb (a : LeafQM.B) + 3 * (bEmb y1 * u * g) - (3 : BAQ) * (bEmb (beta q xE) * g) + 3 * y0 := by
        rw [hyE]; noncomm_ring
      rw [e, h3, map_smul, ← three_mul_eq_smul, Units.val_mul]
      noncomm_ring
    · rw [iotaC_smul_mulVec, smul_smul]
      push_cast
      rw [inv_mul_cancel₀ (by norm_num : (3 : ℂ) ≠ 0), one_smul]
      exact hpt


/-- **`QMReciprocityL3` from the polarized, maximal-order print for primitive types** (existential sign), Shimura's
existence theorem and the textbook leaves. -/
theorem qmReciprocityL3_of_polPrim (hP : MainTheoremCMPolPrim) (hX : CMAbVarExists)
    (hUL : BPAnalytic.Uniformization.UniformizationLeafAll) (hG : ZInQ.HomLattice.GAGAMorphism) :
    ShimuraSplit2.QMReciprocityL3 :=
  qmReciprocityL3_of_ek (mainTheoremCMEK_of_polPrim hP hX hUL hG) (AvSplit.Final.h69 hUL hG)

/-- **`QMReciprocityL3` from the main theorem of CM for CM elliptic curves** (`𝓞_E`-ideal lattices, existential
sign), Shimura's existence theorem and the textbook leaves. -/
theorem qmReciprocityL3_of_polQuad (hP : MainTheoremCMPolQuad) (hX : CMAbVarExists)
    (hUL : BPAnalytic.Uniformization.UniformizationLeafAll) (hG : ZInQ.HomLattice.GAGAMorphism) :
    ShimuraSplit2.QMReciprocityL3 :=
  qmReciprocityL3_of_ek (mainTheoremCMEK_of_polQuad hP hX hUL hG) (AvSplit.Final.h69 hUL hG)

/-- **The former field `rayClassCMAb`** (shimura-split2's `rayClassCMAb_of_leaves2`) from the primitive print. -/
theorem rayClassCMAb_of_polPrim (hR : ShimuraGlue.DeligneComponentsX6PrintedAb) (hP : MainTheoremCMPolPrim)
    (hX : CMAbVarExists) (hUL : BPAnalytic.Uniformization.UniformizationLeafAll)
    (hG : ZInQ.HomLattice.GAGAMorphism) (hMum : AvSplit.MumfordTorsionAlgClosed) :
    ShimuraGlue.Ray.RayClassCMAb :=
  rayClassCMAb_of_leaves2 hR (qmReciprocityL3_of_polPrim hP hX hUL hG) hUL hG hMum

/-- **The former field `rayClassCMAb`** from the quadratic print. -/
theorem rayClassCMAb_of_polQuad (hR : ShimuraGlue.DeligneComponentsX6PrintedAb) (hP : MainTheoremCMPolQuad)
    (hX : CMAbVarExists) (hUL : BPAnalytic.Uniformization.UniformizationLeafAll)
    (hG : ZInQ.HomLattice.GAGAMorphism) (hMum : AvSplit.MumfordTorsionAlgClosed) :
    ShimuraGlue.Ray.RayClassCMAb :=
  rayClassCMAb_of_leaves2 hR (qmReciprocityL3_of_polQuad hP hX hUL hG) hUL hG hMum

end QMRec

section Hcm

open NumberField IsDedekindDomain QMRecPrinted ShimuraCFT RayClassCFT
open TauCeti.ClassFieldTheory TauCeti.GlobalNumberFields
open ZInQ.RouteK.Rank5b ZInQ.Contrib.TYZGenus.Shimura ZInQ.Contrib.TYZGenus.CM
open scoped TensorProduct FiniteAdeleExtension
open Complex MonObj HcmPrinted
open ZInQ.LeafPush2 (cEvalAt cDom)
open AvSplit.HomLatticeAN3 (bcC projC ptE ptE_left)

/-- **`T5Glue.ShimuraMainCM` from the main theorem of CM for imaginary quadratic fields** (`ε = 1`), the
Weierstrass leaves and `HomLatticeCorr`. -/
theorem shimuraMainCM_of_arithQuad (hM : MainTheoremCMSignQuad 1) (hWU : WeierstrassUniformization)
    (hWP : WeierstrassParam) (hWA : WeierstrassAbVar) (hH : ZInQ.HomUnify.HomLatticeCorr) :
    T5Glue.ShimuraMainCM := by
  intro m _ hsq e he σ s hs 𝔞 P P' hP hP'
  obtain ⟨A, θ, U, x, y, hdim, hθ, hθU⟩ := hWA P
  let S : AddSubgroup (QNeg m) := P.lattice.toAddSubgroup.comap (kap m).toAddMonoidHom
  have hS : (S : Set (QNeg m)) = 𝔞 := by
    ext z
    change kap m z ∈ P.lattice ↔ z ∈ 𝔞
    rw [← SetLike.mem_coe, hP]
    constructor
    · rintro ⟨w, hw, hwz⟩
      rw [kap_apply] at hwz
      rwa [T5Glue.kappa_injective hwz] at hw
    · intro hz; exact ⟨z, hz, (kap_apply z).symm⟩
  obtain ⟨b₁, hb₁, hb₁'⟩ : ∃ b ∈ 𝔞, kappa m b = P.ω₁ := by
    have := P.ω₁_mem_lattice; rw [← SetLike.mem_coe, hP] at this; exact this
  obtain ⟨b₂, hb₂, hb₂'⟩ : ∃ b ∈ 𝔞, kappa m b = P.ω₂ := by
    have := P.ω₂_mem_lattice; rw [← SetLike.mem_coe, hP] at this; exact this
  have hb : ∀ z, z ∈ 𝔞 ↔ ∃ n₁ n₂ : ℤ, z = n₁ * b₁ + n₂ * b₂ := by
    intro z
    constructor
    · intro hz
      have hk : kappa m z ∈ P.lattice := by rw [← SetLike.mem_coe, hP]; exact ⟨z, hz, rfl⟩
      obtain ⟨n₁, n₂, hn⟩ := PeriodPair.mem_lattice.1 hk
      refine ⟨n₁, n₂, T5Glue.kappa_injective ?_⟩
      rw [T5Glue.kappa_add, T5Glue.kappa_intCast_mul, T5Glue.kappa_intCast_mul, hb₁', hb₂', hn]
    · rintro ⟨n₁, n₂, rfl⟩
      rw [← hS]
      have h1 : b₁ ∈ S := by rw [← SetLike.mem_coe, hS]; exact hb₁
      have h2 : b₂ ∈ S := by rw [← SetLike.mem_coe, hS]; exact hb₂
      rw [← zsmul_eq_mul, ← zsmul_eq_mul]
      exact add_mem (zsmul_mem h1 n₁) (zsmul_mem h2 n₂)
  -- `t = N(s)` and the lattice of `A^σ`
  set t : AQ ⊗[ℚ] QNeg m := ((reflexNorm rhoQ (IdeleGroup.toFiniteIdele (𝓞 (QNeg m)) (QNeg m) s) ^
    ((1 : ℤˣ) : ℤ) : (AQ ⊗[ℚ] QNeg m)ˣ) : AQ ⊗[ℚ] QNeg m) with ht_def
  have ht : t = (eK m).symm (T5Glue.finPart s) := by
    rw [ht_def, Units.val_one, zpow_one, reflexNorm_rhoQ]; rfl
  have htmul : ∀ z : QNeg m, t * (1 ⊗ₜ z) =
      (eK m).symm (T5Glue.finPart s * algebraMap (QNeg m) (T5Glue.AfK m) z) := by
    intro z; rw [ht, map_mul, finiteAdeleBaseChangeAlgEquiv_symm_algebraMap]
  have hadel := adelic 𝔞 S hS b₁ b₂ hb
  have hlat : (latAct t S : Set (QNeg m)) = T5Glue.sInvLat m s 𝔞 := by
    ext z
    change t * Algebra.TensorProduct.includeRight z ∈ QMRecPrinted.latHat S ↔ _
    rw [Algebra.TensorProduct.includeRight_apply, htmul, hadel, AlgEquiv.apply_symm_apply]
    rfl
  -- the main theorem of CM
  obtain ⟨θ', hθ', hrel⟩ := hM (QNeg m) 1 (fun _ => kap m) (by rw [finrank_QNeg]) type_inj finrank_QNeg
    (QNeg m) (kap m)
    reflex_range 1 rhoQ jQ model σ s (artinCondC_of_artinCond e he σ s hs) A hdim S θ
    (by rw [cmLat_eq S P (by rw [hP, hS])]; exact hθ)
    (isOfType_of_corr hH A hdim θ P hθ S (by rw [hP, hS]))
    (bcC A (σ : ℂ →+* ℂ)) (projC A (σ : ℂ →+* ℂ)) (isPullback_bc σ A) (one_left_bc σ A)
  have hθ'' : IsUniformization (RingHom.id ℂ) (lat1 P') θ' := by
    rw [cmLat_eq _ P' (by rw [hP', hlat])] at hθ'
    exact hθ'
  obtain ⟨ν, hν, hcoord⟩ := core hWP hWU σ P P' A θ U x y hθ hθU θ' hθ''
  refine ⟨ν, hν, fun u v hu huv => ?_⟩
  have hmem : t * (1 ⊗ₜ v) - 1 ⊗ₜ u ∈ QMRecPrinted.latHat S := by
    rw [htmul, ← finiteAdeleBaseChangeAlgEquiv_symm_algebraMap, ← map_sub, hadel,
      AlgEquiv.apply_symm_apply]
    exact huv
  have hr := hrel u v hmem
  have hcv : ∀ z : QNeg m, cmVec (fun _ : Fin 1 => kap m) z = fun _ => kappa m z :=
    fun z => funext fun _ => kap_apply z
  rw [hcv, hcv] at hr
  exact hcoord (kappa m u) (kappa m v) hu hr



/-- `T5Glue.ShimuraMainCM` from the main theorem of CM for primitive types. -/
theorem shimuraMainCM_of_arithPrim (hM : MainTheoremCMSignPrim 1) (hWU : WeierstrassUniformization)
    (hWP : WeierstrassParam) (hWA : WeierstrassAbVar) (hH : ZInQ.HomUnify.HomLatticeCorr) :
    T5Glue.ShimuraMainCM :=
  shimuraMainCM_of_arithQuad (signQuad_of_signPrim hM) hWU hWP hWA hH

/-- **`hCM = T5Glue.ShimuraMainCM` from the polarized, maximal-order print for primitive types** (`ε = 1`),
Shimura's existence theorem, hcm-printed's Weierstrass leaves and the textbook leaves. -/
theorem shimuraMainCM_of_polMaxPrim (hP : MainTheoremCMPolMaxPrim) (hX : CMAbVarExists)
    (hWU : HcmPrinted.WeierstrassUniformization) (hWP : HcmPrinted.WeierstrassParam)
    (hWA : HcmPrinted.WeierstrassAbVar) (hUL : BPAnalytic.Uniformization.UniformizationLeafAll)
    (hG : ZInQ.HomLattice.GAGAMorphism) : T5Glue.ShimuraMainCM :=
  shimuraMainCM_of_arithPrim (mainTheoremCMSignPrim_of_polar 1 (polPrimSign_one_of_polMaxPrim hP) hX hUL hG)
    hWU hWP hWA (AvSplit.Final.h69 hUL hG)

/-- **`hCM = T5Glue.ShimuraMainCM` from the main theorem of CM for CM elliptic curves** (`𝓞_E`-ideal lattices,
`ε = 1`), Shimura's existence theorem, hcm-printed's Weierstrass leaves and the textbook leaves. -/
theorem shimuraMainCM_of_polMaxQuad (hP : MainTheoremCMPolMaxQuad) (hX : CMAbVarExists)
    (hWU : HcmPrinted.WeierstrassUniformization) (hWP : HcmPrinted.WeierstrassParam)
    (hWA : HcmPrinted.WeierstrassAbVar) (hUL : BPAnalytic.Uniformization.UniformizationLeafAll)
    (hG : ZInQ.HomLattice.GAGAMorphism) : T5Glue.ShimuraMainCM :=
  shimuraMainCM_of_arithQuad (mainTheoremCMSignQuad_of_polar 1 (polQuadSign_one_of_polMaxQuad hP) hX hUL hG)
    hWU hWP hWA (AvSplit.Final.h69 hUL hG)

end Hcm

end CMPrimitive
