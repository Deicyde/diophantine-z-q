import ActualDivisionFieldV004
import WildFiniteGroupV002

/-!
# Strict wild displacement under actual finite Galois restriction

The restricted valuation ring is the literal inverse image of the given
valuation ring. Its canonical valuation is equivalent to the restricted
original valuation. Thus the actual finite image inherits the strict
inequality required by the finite residue-characteristic group theorem.
-/

noncomputable section
set_option autoImplicit false

namespace ActualFiniteRamification
variable {K Ω : Type} [Field K] [Field Ω] [Algebra K Ω]

lemma valuation_comap_equiv (w : ValuationSubring Ω) (L : IntermediateField K Ω) :
    (w.valuation.comap L.val.toRingHom).IsEquiv
      (w.comap L.val.toRingHom).valuation := by
  apply Valuation.isEquiv_of_val_le_one
  intro x
  simp only [Valuation.comap_apply, ValuationSubring.valuation_le_one_iff,
    ValuationSubring.mem_comap]

lemma restriction_strict (w : ValuationSubring Ω) (L : FiniteGaloisIntermediateField K Ω)
    (σ : Ω ≃ₐ[K] Ω)
    (hσ : ∀ x : Ω, x ≠ 0 → w.valuation (σ x - x) < w.valuation x) :
    AlgEquiv.restrictNormalHom L σ ∈
      WildFiniteGroup.strictDisplacementGroup (K := K) (w.comap L.toIntermediateField.val.toRingHom) := by
  intro x hx
  apply (valuation_comap_equiv w L.toIntermediateField).lt_iff_lt.mp
  have hxΩ : (x : Ω) ≠ 0 := fun h => hx (Subtype.ext h)
  have he : ((AlgEquiv.restrictNormalHom L σ x : L) : Ω) = σ (x : Ω) :=
    AlgEquiv.restrictNormal_commutes σ L x
  change w.valuation (((AlgEquiv.restrictNormalHom L σ x : L) : Ω) - (x : Ω)) <
    w.valuation (x : Ω)
  rw [he]
  exact hσ x hxΩ

def wildImage (w : ValuationSubring Ω) (L : FiniteGaloisIntermediateField K Ω) :
    Subgroup (L ≃ₐ[K] L) :=
  (WildFiniteGroup.strictDisplacementGroup (K := K) w).map (AlgEquiv.restrictNormalHom L)

lemma wildImage_le (w : ValuationSubring Ω) (L : FiniteGaloisIntermediateField K Ω) :
    wildImage w L ≤ WildFiniteGroup.strictDisplacementGroup
      (K := K) (w.comap L.toIntermediateField.val.toRingHom) := by
  rintro τ ⟨σ, hσ, rfl⟩
  exact restriction_strict w L σ hσ

lemma wildImage_isPGroup (w : ValuationSubring Ω) (L : FiniteGaloisIntermediateField K Ω)
    (p : ℕ) [Fact p.Prime]
    [CharP (IsLocalRing.ResidueField (w.comap L.toIntermediateField.val.toRingHom)) p] :
    IsPGroup p (wildImage w L) := by
  let P := WildFiniteGroup.strictDisplacementGroup (K := K) (w.comap L.toIntermediateField.val.toRingHom)
  have hP : IsPGroup p P := WildFiniteGroup.strictDisplacementGroup_isPGroup _ p
  let f : wildImage w L →* P := Subgroup.inclusion (wildImage_le w L)
  exact hP.of_injective f (Subgroup.inclusion_injective (wildImage_le w L))

lemma restricted_order_coprime (O : ValuationSubring K) (w : ValuationSubring Ω)
    (hw : w.comap (algebraMap K Ω) = O) (ℓ : ℕ) (hℓ : ℓ.Prime) (hu : IsUnit (ℓ : O))
    (L : FiniteGaloisIntermediateField K Ω) (σ : Ω ≃ₐ[K] Ω)
    (hσ : ∀ x : Ω, x ≠ 0 → w.valuation (σ x - x) < w.valuation x) :
    Nat.Coprime (orderOf (AlgEquiv.restrictNormalHom L σ)) ℓ :=
  WildFiniteRestriction.restriction_order_coprime O w hw ℓ hℓ hu σ hσ L

end ActualFiniteRamification
