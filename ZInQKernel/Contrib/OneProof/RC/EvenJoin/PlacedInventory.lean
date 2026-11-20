import ZInQKernel.Contrib.OneProof.RC.EvenJoin.ExactInventory

/-! The independent inventory over one finite extension of the fixed
place. The place contains even the character of a block with empty list. -/

noncomputable section

set_option maxHeartbeats 1200000

namespace ZInQ.Manuscript.RC.EvenJoin

open AddressGenuine AuxInputs BlocksPerU EvenBudget EvenExpansion
open IsDedekindDomain NumberField ThetaCoeff Wiring
open ZInQ.Contrib.CloudB3RC53
open ZInQ.Contrib.CloudB3RC53.CoefficientDictionary
open scoped AdicCompletionExtension

variable {D : Type} [Fintype D] {N : ℕ} [NeZero N]
variable {m : D → ℕ} {a : D → ℕ → ℂ}
variable (A : ∀ b, CuspBlockExpansion (m b) (a b)) (hm : ∀ b, m b ∣ N)

def liftedBlockChar (b : D) : (ZMod N)ˣ →* ℂˣ :=
  (A b).χ.toUnitHom.comp (ZMod.unitsMap (hm b))

variable {F : IntermediateField ℚ ℂ} [NumberField F]

/-- Algebraic field of definition and a place for the actual finite lists
and their block characters. No Galois or Fourier spanning law is a field. -/
structure PlacedCuspLists (v : HeightOneSpectrum (𝓞 F)) where
  E : IntermediateField ℚ ℂ
  [numberField : NumberField E]
  includes : F ≤ E
  w : HeightOneSpectrum (𝓞 E)
  liesOver : letI : Algebra F E := (IntermediateField.inclusion includes).toAlgebra
    w.asIdeal.LiesOver v.asIdeal
  source_mem : ∀ x : ↥(distinctCuspColumns A hm), x.val.source.field ≤ E
  block_char_mem : ∀ b u, (liftedBlockChar A hm b u : ℂ) ∈ E

attribute [instance] PlacedCuspLists.numberField

/-- The compositum includes all genuine newform fields and the values of
the finitely many lifted characters. The latter are roots of unity. -/
theorem exists_placedCuspLists (v : HeightOneSpectrum (𝓞 F)) :
    Nonempty (PlacedCuspLists A hm v) := by
  classical
  let I := Σ _b : D, (ZMod N)ˣ
  let c : I → ℂ := fun u => liftedBlockChar A hm u.1 u.2
  let H := IntermediateField.adjoin ℚ (Set.range c)
  have hint (u : I) : IsIntegral ℚ (c u) := by
    apply IsIntegral.of_pow (Fintype.card_pos (α := (ZMod N)ˣ))
    have he : c u ^ Fintype.card (ZMod N)ˣ = 1 := by
      change (↑(liftedBlockChar A hm u.1 u.2) : ℂ) ^ _ = _
      rw [← Units.val_pow_eq_pow_val, ← map_pow, pow_card_eq_one, map_one, Units.val_one]
    rw [he]
    exact isIntegral_one
  letI : FiniteDimensional ℚ H := IntermediateField.finiteDimensional_adjoin
    (fun _ ⟨u, hu⟩ => hu ▸ hint u)
  letI : NumberField H := {}
  letI fields : ∀ x : ↥(distinctCuspColumns A hm), NumberField x.val.source.field := by
    intro x
    obtain ⟨b, y, he⟩ := (mem_distinctCuspColumns A hm x.val).mp x.property
    rw [← he]
    exact (A b).col_numberField y
  letI : FiniteDimensional ℚ (F ⊔ H : IntermediateField ℚ ℂ) :=
    IntermediateField.finiteDimensional_sup F H
  letI : NumberField (F ⊔ H : IntermediateField ℚ ℂ) := {}
  obtain ⟨E, hE, hFH, hfields⟩ := finite_constituent_compositum (F ⊔ H)
    (fun (x : ↥(distinctCuspColumns A hm)) => x.val.source.field)
  let hFE : F ≤ E := le_sup_left.trans hFH
  letI : Algebra F E := (IntermediateField.inclusion hFE).toAlgebra
  obtain ⟨w, hw⟩ := exists_constituent_place (E := E) v
  exact ⟨{ E := E
           numberField := hE
           includes := hFE
           w := w
           liesOver := hw
           source_mem := hfields
           block_char_mem := fun b u =>
             (le_sup_right.trans hFH) (IntermediateField.subset_adjoin ℚ _ ⟨⟨b, u⟩, rfl⟩) }⟩

namespace PlacedCuspLists

variable {A hm} {v : HeightOneSpectrum (𝓞 F)} (P : PlacedCuspLists A hm v)

abbrev κ : FixedField P.w →+* ℂ := constituentComplexEmbedding P.w

theorem in_image {z : ℂ} (hz : z ∈ P.E) : ∃ y : FixedField P.w, P.κ y = z :=
  ⟨FinitePlace.embedding P.w ⟨z, hz⟩, constituentComplexEmbedding_constituent P.w ⟨z, hz⟩⟩

def inventory {L : Type} [AddCommGroup L] {ε : L →+ ZMod 2} (T : TypeData L ε)
    (hLi : OldNewIndependenceWeightTwo) :
    Inventory ↥(distinctCuspColumns A hm) ↥(cuspSources (distinctCuspColumns A hm))
      (FixedField P.w) T N :=
  cuspInventory _ P.κ
    (fun x n => P.in_image (P.source_mem x (x.val.source.coeff_mem_field n)))
    (fun x u => P.in_image (P.source_mem x (x.val.source.char_mem_field u))) hLi

def blockChar (b : D) : (ZMod N)ˣ →* (FixedField P.w)ˣ :=
  charAt P.κ (liftedBlockChar A hm b) fun u => P.in_image (P.block_char_mem b u)

@[simp] theorem blockChar_complex (b : D) (u : (ZMod N)ˣ) :
    P.κ (P.blockChar b u : FixedField P.w) = (liftedBlockChar A hm b u : ℂ) :=
  charAt_apply _ _ _ _

/-- Every block still lies in the span with its own intrinsic level and
pulled back character. The occurrence map retains the exact columns,
even when several blocks use the same one. -/
theorem block_span {L : Type} [AddCommGroup L] {ε : L →+ ZMod 2} (T : TypeData L ε)
    (hLi : OldNewIndependenceWeightTwo) (b : D) :
    a b ∈ Submodule.span ℂ (blockColumns (P.inventory T hLi) P.κ (m b) (P.blockChar b)) := by
  apply block_span_of_inventory_labels (A b) (P.inventory T hLi) P.κ (P.blockChar b)
    (distinctCuspIndex A hm b)
  · intro c
    change ((A b).liftColumn (hm b) c).source.level * ((A b).liftColumn (hm b) c).degree ∣ m b
    rw [Nat.mul_comm]
    exact (A b).liftColumn_level (hm b) c
  · intro c
    apply MonoidHom.ext
    intro u
    apply Units.ext
    apply P.κ.injective
    rw [P.blockChar_complex]
    change P.κ ((P.inventory T hLi).χ (cuspOrigin _ (distinctCuspIndex A hm b c)) u :
        FixedField P.w) = _
    rw [inventory, cuspInventory_char]
    exact congrArg (fun χ : (ZMod N)ˣ →* ℂˣ => (χ u : ℂ)) ((A b).liftColumn_char (hm b) c)
  · intro c n
    rw [inventory, cuspInventory_coeff]
    rfl

end PlacedCuspLists

end ZInQ.Manuscript.RC.EvenJoin
