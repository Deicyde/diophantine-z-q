import ZInQKernel.HDecomp.QM.Pairs
import ZInQKernel.HDecomp.Descent.B2Glue

/-!
# inner-twist: `G0ModField.UnramifiedConjugates` (from `scratch/fibre-cover/FibreCover.lean`), proved

Task inner-twist (2026-11-13). The Prop `UnramifiedConjugates` is copied verbatim (docstring and
body) from `scratch/fibre-cover/FibreCover.lean`, in the same namespace `G0ModField`; `Qbar` is
`LeafQM.AV.Qbar = AlgebraicClosure ℚ` and `UnramifiedAt` is glue-descent's
`GlueDescent.B2Q.UnramifiedAt` (`ZInQKernel/HDecomp/Descent/B2Glue.lean`), as in the source.

Proof (no leaf, no glue Prop). Let `K = ℚ(α)`, `L = ℚ(roots of minpoly α)` (finite Galois), `Q` a
prime of `𝓞 L` containing `p`, `G = Gal(L/ℚ)`, `I = I(Q) ≤ G`.
1. (`inertia_le_fixing`) `I` fixes `𝓞 K`: let `H ≤ G` fix `𝓞 K`; `H` is a Galois group of
   `𝓞 L / 𝓞 K` (Mathlib `IsGaloisGroup.of_isScalarTower`). Then
   `#(I ∩ H) = #I_H(Q) = e(Q | Q ∩ 𝓞 K) = e(Q | p) / e(Q ∩ 𝓞 K | p) = e(Q | p) = #I`
   (Mathlib `card_inertia_eq_ramificationIdxIn` twice, `ramificationIdx_tower`), so `I ≤ H`.
2. (`inertia_fixes_field`) hence `I` fixes `K = Frac(𝓞 K)`, in particular `α`.
3. (`conj_mem_inertia`) for `σ ∈ G`, `σ⁻¹ I(Q) σ ⊆ I(σ⁻¹Q)`, and `σ⁻¹Q ∋ p`; so `I(Q)` fixes
   `σ(α)` for all `σ`, i.e. every root of `minpoly α` (`Normal.minpoly_eq_iff_mem_orbit`).
4. So `I(Q)` fixes `L`, `I(Q) = 1`, and `e(Q | p) = #I(Q) = 1`.
The argument is uniform in `p : ℕ` (no case split).
-/

open NumberField
open LeafQM.AV GlueDescent.B2Q

namespace G0ModField

/-- **Textbook (STANDARD): the Galois closure of an unramified field is unramified.** If
`ℚ(α) ⊆ ℚ̄` is unramified at `p`, so is the splitting field `ℚ(roots of minpoly α)`, which is
the compositum of the conjugates `σℚ(α) ≅ ℚ(α)`; a compositum of number fields unramified at `p`
is unramified at `p` (Neukirch, *Algebraic Number Theory*, Ch. I §9 or Ch. III §2, the
compositum of unramified extensions; UNVERIFIED locator). Not in Mathlib v4.35 for
`UnramifiedAt` (cf. g0-mod-field's `UnramifiedSup`, the Galois case). -/
def UnramifiedConjugates : Prop :=
  ∀ (α : Qbar) (p : ℕ), UnramifiedAt (IntermediateField.adjoin ℚ {α}) p →
    UnramifiedAt (IntermediateField.adjoin ℚ ((minpoly ℚ α).rootSet Qbar)) p

/-! ## The abstract step: inertia fixes an unramified subfield -/

section Abstract

variable {K L : Type} [Field K] [Field L] [NumberField K] [NumberField L] [Algebra K L]
  [IsGalois ℚ L]

/-- **Inertia fixes the integers of an unramified subfield.** For number fields `K → L`, `L/ℚ`
Galois, `K` unramified at `p` (every prime of `𝓞 K` containing `p` has `e = 1` over `ℤ`), a prime
`Q ∋ p` of `𝓞 L` and `g ∈ I(Q) ≤ Gal(L/ℚ)`: `g` fixes the image of `𝓞 K`. -/
theorem inertia_le_fixing (p : ℕ)
    (hK : ∀ P : Ideal (𝓞 K), P.IsPrime → ((p : ℤ) : 𝓞 K) ∈ P → P.ramificationIdx ℤ = 1)
    (Q : Ideal (𝓞 L)) [hQ : Q.IsPrime] (hpQ : ((p : ℤ) : 𝓞 L) ∈ Q) (g : L ≃ₐ[ℚ] L)
    (hg : g ∈ Q.inertia (L ≃ₐ[ℚ] L)) (y : 𝓞 K) :
    g • algebraMap (𝓞 K) (𝓞 L) y = algebraMap (𝓞 K) (𝓞 L) y := by
  let G := L ≃ₐ[ℚ] L
  let H : Subgroup G := fixingSubgroup G (Set.range (algebraMap (𝓞 K) (𝓞 L)))
  have : IsGaloisGroup H (𝓞 K) (𝓞 L) := IsGaloisGroup.of_isScalarTower G ℤ (𝓞 L) (𝓞 K)
  let QK : Ideal (𝓞 K) := Q.under (𝓞 K)
  have : QK.IsPrime := Ideal.IsPrime.under (𝓞 K) Q
  have : Algebra.HasSeparableResidueFieldsAt (𝓞 K) (𝓞 L) QK :=
    Algebra.HasSeparableResidueFieldsAt.tower_top (Q.under ℤ) QK
  have hpQK : ((p : ℤ) : 𝓞 K) ∈ QK := by
    show algebraMap (𝓞 K) (𝓞 L) ((p : ℤ) : 𝓞 K) ∈ Q
    rw [map_intCast]; exact hpQ
  have he1 : QK.ramificationIdx ℤ = 1 := hK QK inferInstance hpQK
  have htower : Q.ramificationIdx ℤ = QK.ramificationIdx ℤ * Q.ramificationIdx (𝓞 K) :=
    Ideal.ramificationIdx_tower (R := ℤ) QK Q
  have hcardH : Nat.card (Q.inertia H) = Q.ramificationIdx (𝓞 K) := by
    rw [Ideal.card_inertia_eq_ramificationIdxIn (G := H) QK Q,
      Ideal.ramificationIdxIn_eq_ramificationIdx QK Q H]
  have hcardG : Nat.card (Q.inertia G) = Q.ramificationIdx ℤ := by
    rw [Ideal.card_inertia_eq_ramificationIdxIn (G := G) (Q.under ℤ) Q,
      Ideal.ramificationIdxIn_eq_ramificationIdx (Q.under ℤ) Q G]
  have hcard : Nat.card ((Q.inertia G).subgroupOf H) = Nat.card (Q.inertia G) := by
    rw [hcardG, htower, he1, _root_.one_mul, ← hcardH]; rfl
  have hle : Q.inertia G ≤ H := by
    have h1 : Nat.card ((Q.inertia G) ⊓ H : Subgroup G) = Nat.card (Q.inertia G) := by
      rw [← hcard, ← Subgroup.subgroupOf_map_subtype]
      exact Subgroup.card_map_of_injective H.subtype_injective
    have h2 : (Q.inertia G) ⊓ H = Q.inertia G :=
      Subgroup.eq_of_le_of_card_ge inf_le_left h1.ge
    exact inf_eq_left.mp h2
  exact (mem_fixingSubgroup_iff G).mp (hle hg) _ ⟨y, rfl⟩


/-- **Inertia fixes an unramified subfield** (`K = Frac(𝓞 K)`). -/
theorem inertia_fixes_field (p : ℕ)
    (hK : ∀ P : Ideal (𝓞 K), P.IsPrime → ((p : ℤ) : 𝓞 K) ∈ P → P.ramificationIdx ℤ = 1)
    (Q : Ideal (𝓞 L)) [hQ : Q.IsPrime] (hpQ : ((p : ℤ) : 𝓞 L) ∈ Q) (g : L ≃ₐ[ℚ] L)
    (hg : g ∈ Q.inertia (L ≃ₐ[ℚ] L)) (x : K) : g (algebraMap K L x) = algebraMap K L x := by
  obtain ⟨a, b, -, rfl⟩ := IsFractionRing.div_surjective (A := 𝓞 K) x
  have h : ∀ y : 𝓞 K, g (algebraMap K L (algebraMap (𝓞 K) K y)) =
      algebraMap K L (algebraMap (𝓞 K) K y) := fun y =>
    congrArg (fun z : 𝓞 L => (z : L)) (inertia_le_fixing p hK Q hpQ g hg y)
  rw [map_div₀, map_div₀, h a, h b]

omit [IsGalois ℚ L] in
/-- **Conjugation of inertia**: `σ⁻¹ I(Q) σ ⊆ I(σ⁻¹ Q)`, where `σ⁻¹ Q = {x | σ x ∈ Q}`. -/
theorem conj_mem_inertia (Q : Ideal (𝓞 L)) (g σ : L ≃ₐ[ℚ] L)
    (hg : g ∈ Q.inertia (L ≃ₐ[ℚ] L)) :
    σ⁻¹ * g * σ ∈ (Q.comap (MulSemiringAction.toRingHom (L ≃ₐ[ℚ] L) (𝓞 L) σ)).inertia
      (L ≃ₐ[ℚ] L) := by
  rw [Ideal.mem_inertia] at hg ⊢
  intro x
  show MulSemiringAction.toRingHom (L ≃ₐ[ℚ] L) (𝓞 L) σ ((σ⁻¹ * g * σ) • x - x) ∈ Q
  rw [map_sub]
  simp only [MulSemiringAction.toRingHom_apply, mul_smul, smul_inv_smul]
  exact hg (σ • x)

end Abstract

/-- A finite intermediate field of `ℚ̄/ℚ` is a number field. -/
theorem numberField_of_fd (F : IntermediateField ℚ Qbar) [FiniteDimensional ℚ F] :
    NumberField F :=
  { to_charZero := inferInstance, to_finiteDimensional := inferInstance }

/-- **`UnramifiedConjugates`, proved** (no leaf, no glue Prop). -/
theorem unramifiedConjugates : UnramifiedConjugates := by
  classical
  intro α p hK
  have hαint : IsIntegral ℚ α := Algebra.IsIntegral.isIntegral α
  have hf0 : minpoly ℚ α ≠ 0 := minpoly.ne_zero hαint
  set K : IntermediateField ℚ Qbar := IntermediateField.adjoin ℚ {α} with hKdef
  set L : IntermediateField ℚ Qbar :=
    IntermediateField.adjoin ℚ ((minpoly ℚ α).rootSet Qbar) with hLdef
  have hroot : ∀ β ∈ (minpoly ℚ α).rootSet Qbar, β ∈ L :=
    fun β hβ => IntermediateField.subset_adjoin _ _ hβ
  have hαroot : α ∈ (minpoly ℚ α).rootSet Qbar :=
    (Polynomial.mem_rootSet).2 ⟨hf0, minpoly.aeval ℚ α⟩
  have hαL : α ∈ L := hroot α hαroot
  have hKL : K ≤ L := IntermediateField.adjoin_simple_le_iff.2 hαL
  have : Polynomial.IsSplittingField ℚ L (minpoly ℚ α) :=
    IntermediateField.adjoin_rootSet_isSplittingField (IsAlgClosed.splits _)
  have : FiniteDimensional ℚ L := Polynomial.IsSplittingField.finiteDimensional L (minpoly ℚ α)
  have : IsGalois ℚ L :=
    IsGalois.of_separable_splitting_field (minpoly.irreducible hαint).separable
  have : FiniteDimensional ℚ K := IntermediateField.adjoin.finiteDimensional hαint
  have : NumberField K := numberField_of_fd K
  have : NumberField L := numberField_of_fd L
  let : Algebra K L := (IntermediateField.inclusion hKL).toRingHom.toAlgebra
  intro Q hQ hpQ
  -- every element of the inertia group fixes every root of `minpoly α`
  have hfix : ∀ g ∈ Q.inertia (L ≃ₐ[ℚ] L), ∀ β (hβ : β ∈ (minpoly ℚ α).rootSet Qbar),
      g ⟨β, hroot β hβ⟩ = ⟨β, hroot β hβ⟩ := by
    intro g hg β hβ
    have hβ0 : Polynomial.aeval β (minpoly ℚ α) = 0 := ((Polynomial.mem_rootSet).1 hβ).2
    have hmin : minpoly ℚ (⟨β, hroot β hβ⟩ : L) = minpoly ℚ (⟨α, hαL⟩ : L) := by
      rw [← minpoly.algHom_eq L.val Subtype.val_injective (⟨β, hroot β hβ⟩ : L),
        ← minpoly.algHom_eq L.val Subtype.val_injective (⟨α, hαL⟩ : L)]
      exact (minpoly.eq_of_irreducible_of_monic (minpoly.irreducible hαint) hβ0
        (minpoly.monic hαint)).symm
    obtain ⟨σ, hσ⟩ := (Normal.minpoly_eq_iff_mem_orbit (F := ℚ) (E := L)).mp hmin
    -- `σ⁻¹ g σ` lies in the inertia group of `σ⁻¹ Q`, which contains `p`
    let Q' : Ideal (𝓞 L) := Q.comap (MulSemiringAction.toRingHom (L ≃ₐ[ℚ] L) (𝓞 L) σ)
    have : Q'.IsPrime := Ideal.comap_isPrime _ _
    have hpQ' : ((p : ℤ) : 𝓞 L) ∈ Q' := by
      show MulSemiringAction.toRingHom (L ≃ₐ[ℚ] L) (𝓞 L) σ ((p : ℤ) : 𝓞 L) ∈ Q
      rw [map_intCast]; exact hpQ
    have h1 := inertia_fixes_field (K := K) (L := L) p hK Q' hpQ' (σ⁻¹ * g * σ)
      (conj_mem_inertia Q g σ hg) ⟨α, IntermediateField.mem_adjoin_simple_self ℚ α⟩
    have h2 : algebraMap K L ⟨α, IntermediateField.mem_adjoin_simple_self ℚ α⟩ =
        (⟨α, hαL⟩ : L) := rfl
    rw [h2] at h1
    have h3 : (⟨β, hroot β hβ⟩ : L) = σ ⟨α, hαL⟩ := hσ.symm
    rw [h3]
    have h4 := congrArg σ h1
    simpa [AlgEquiv.mul_apply] using h4
  -- hence the inertia group is trivial
  have htriv : ∀ g ∈ Q.inertia (L ≃ₐ[ℚ] L), g = 1 := by
    intro g hg
    let s : Qbar ≃ₐ[ℚ] Qbar := g.liftNormal Qbar
    have hs : ∀ y : L, s (y : Qbar) = ((g y : L) : Qbar) :=
      fun y => AlgEquiv.liftNormal_commutes g Qbar y
    have hsroot : ∀ β ∈ (minpoly ℚ α).rootSet Qbar, s β = β := by
      intro β hβ
      have := hs ⟨β, hroot β hβ⟩
      rw [hfix g hg β hβ] at this
      exact this
    have hL' : L ≤ IntermediateField.fixedField (Subgroup.zpowers s) := by
      rw [hLdef, IntermediateField.adjoin_le_iff]
      intro β hβ
      rw [SetLike.mem_coe, IntermediateField.mem_fixedField_iff]
      intro f hf
      have hsβ : s ∈ MulAction.stabilizer (Qbar ≃ₐ[ℚ] Qbar) β :=
        MulAction.mem_stabilizer_iff.mpr (hsroot β hβ)
      exact MulAction.mem_stabilizer_iff.mp ((Subgroup.zpowers_le.mpr hsβ) hf)
    apply AlgEquiv.ext
    intro y
    apply Subtype.ext
    have hy := hL' y.2 ⟨s, Subgroup.mem_zpowers s⟩
    rw [← hs]
    exact hy
  have hcard : Nat.card (Q.inertia (L ≃ₐ[ℚ] L)) = 1 := by
    rw [Nat.card_eq_one_iff_unique]
    refine ⟨⟨fun a b => Subtype.ext ((htriv a a.2).trans (htriv b b.2).symm)⟩, ⟨1⟩⟩
  rw [← Ideal.ramificationIdxIn_eq_ramificationIdx (Q.under ℤ) Q (L ≃ₐ[ℚ] L),
    ← Ideal.card_inertia_eq_ramificationIdxIn (G := L ≃ₐ[ℚ] L) (Q.under ℤ) Q, hcard]

end G0ModField

#print axioms G0ModField.inertia_le_fixing
#print axioms G0ModField.unramifiedConjugates
#check @G0ModField.UnramifiedConjugates
example : G0ModField.UnramifiedConjugates = ∀ (α : AlgebraicClosure ℚ) (p : ℕ),
    GlueDescent.B2Q.UnramifiedAt (IntermediateField.adjoin ℚ {α}) p →
    GlueDescent.B2Q.UnramifiedAt
      (IntermediateField.adjoin ℚ ((minpoly ℚ α).rootSet (AlgebraicClosure ℚ))) p := rfl
