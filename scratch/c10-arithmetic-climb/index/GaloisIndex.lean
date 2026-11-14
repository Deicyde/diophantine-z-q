/-
climb/galois-index — the finite-index identification primitive for the checked S1/S2 C10 helper.

SCOPE, stated up front so the strength is not overclaimed:

  * The GENERIC Galois finite-index equality is **already in the pinned Mathlib** and is reused,
    not reproved: `IntermediateField.finrank_eq_fixingSubgroup_index`
    (Mathlib/FieldTheory/Galois/Basic.lean:705, pinned 56a005855ea1):
        `Module.finrank F ↥L = L.fixingSubgroup.index`  for `[IsGalois F E']`.
    No coset construction, no orbit–stabilizer, no transitivity, no embedding count and no finite
    Galois theory is developed here.
  * What this file adds is the **actual-object plumbing** the C10 helper needs: for a GIVEN number
    field `L` and a GIVEN `ι : L →ₐ[ℚ] ℚ̄`, the literal subgroup of `G_ℚ` fixing `ι(L)` pointwise,
    the identification of that literal fixing condition with the intermediate-field fixing
    subgroup, transport of the rank along the actual `AlgEquiv` onto `ι.fieldRange`, and the
    nonzero cast that fills the caller's `hidx` slot.
  * `θ`/`H`/`j` Krull continuity, geometric Tate transport, the chosen topology, B1/B2 isogenies
    and every Frobenius/halting lane are NOT touched. No finite-image hypothesis on the real Tate
    representation is used or needed: openness of fixing subgroups (KrullTopology:170) is never
    invoked.
  * The `range jj = ·` identification is kept as an EXPLICIT hypothesis. It is not derivable for
    an arbitrary group hom and must come from 120c's actual map.
  * `L`, `A`, `Ψ`, `χ` remain the open global residual; nothing here constructs them.

Pinned environment: Lean 4.35.0, Mathlib 56a005855ea1 (read-only, prebuilt). No other dependency.
-/

import Mathlib.FieldTheory.Galois.Basic
import Mathlib.FieldTheory.AbsoluteGaloisGroup
import Mathlib.NumberTheory.NumberField.Basic

namespace ClimbGaloisIndex

/-- `ℚ̄` — the same carrier as the original `GlueC10.Qbar`. -/
abbrev Qbar : Type := AlgebraicClosure ℚ

/-- `G_ℚ` — definitionally the original `GlueC10.GQ` (an `abbrev` for `Qbar ≃ₐ[ℚ] Qbar`) and
Mathlib's `Field.absoluteGaloisGroup ℚ`. -/
abbrev GQ : Type := Qbar ≃ₐ[ℚ] Qbar

example : GQ = Field.absoluteGaloisGroup ℚ := rfl

variable {L : Type} [Field L] [CharZero L] (ι : L →ₐ[ℚ] Qbar)

/-! ## 1. The actual subgroup and the literal fixing condition -/

/-- **The subgroup of `G_ℚ` fixing `ι(L)` pointwise**, as the fixing subgroup of the actual
intermediate field `ι.fieldRange`. -/
noncomputable def fixSub : Subgroup GQ := (ι.fieldRange).fixingSubgroup

/-- The literal condition: `σ` fixes every value of `ι`. -/
theorem mem_fixSub_iff (σ : GQ) : σ ∈ fixSub ι ↔ ∀ a : L, σ (ι a) = ι a := by
  rw [fixSub, IntermediateField.mem_fixingSubgroup_iff]
  constructor
  · intro h a
    exact h (ι a) (AlgHom.mem_fieldRange.mpr ⟨a, rfl⟩)
  · rintro h x hx
    obtain ⟨a, rfl⟩ := AlgHom.mem_fieldRange.mp hx
    exact h a

/-- The same condition as an equation of `ℚ`-algebra maps `L → ℚ̄`. -/
theorem mem_fixSub_iff_comp (σ : GQ) :
    σ ∈ fixSub ι ↔ (σ : Qbar →ₐ[ℚ] Qbar).comp ι = ι := by
  rw [mem_fixSub_iff]
  constructor
  · intro h
    exact AlgHom.ext fun a => h a
  · intro h a
    exact DFunLike.congr_fun h a

/-! ## 2. The index, from the pinned library equality -/

/-- The actual `AlgEquiv` `L ≃ₐ[ℚ] ι(L)` transports the rank. -/
theorem finrank_fieldRange :
    Module.finrank ℚ (ι.fieldRange : IntermediateField ℚ Qbar) = Module.finrank ℚ L :=
  ((AlgEquiv.ofInjectiveField ι).toLinearEquiv.finrank_eq).symm

/-- **The index of the actual fixing subgroup is `[L : ℚ]`.**
The content is the pinned library lemma `IntermediateField.finrank_eq_fixingSubgroup_index`
(for the Galois extension `ℚ̄/ℚ`); this statement only carries it onto the actual `ι`. -/
theorem index_fixSub : (fixSub ι).index = Module.finrank ℚ L := by
  rw [fixSub, ← IntermediateField.finrank_eq_fixingSubgroup_index, finrank_fieldRange]

/-- For a number field the index is nonzero (and equals `[L:ℚ]`). -/
theorem index_fixSub_ne_zero [NumberField L] : (fixSub ι).index ≠ 0 := by
  rw [index_fixSub]
  exact Module.finrank_pos.ne'

theorem finiteIndex_fixSub [NumberField L] : (fixSub ι).FiniteIndex :=
  ⟨index_fixSub_ne_zero ι⟩

/-- **The caller's scalar fact**: in a characteristic-zero coefficient field the index casts to a
nonzero scalar. This is the shape consumed as `hidx`. -/
theorem cast_index_fixSub_ne_zero [NumberField L] (k : Type*) [Field k] [CharZero k] :
    (((fixSub ι).index : ℕ) : k) ≠ 0 :=
  Nat.cast_ne_zero.mpr (index_fixSub_ne_zero ι)

/-- Non-vacuity of the primitive itself: every number field admits such an `ι`, so the bundle
`(L, ι, fixSub ι)` exists for every number field. (This says nothing about the separate global
`A`/`Ψ`/`χ` bundle, which remains open.) -/
theorem exists_embedding (M : Type) [Field M] [NumberField M] : Nonempty (M →ₐ[ℚ] Qbar) :=
  ⟨IsAlgClosed.lift⟩

/-! ## 3. The caller interface: `hidx` from a VERIFIED range identification

`MonoidHom.range jj = fixSub ι` is an explicit hypothesis. It does **not** follow from `jj` being
some group hom into `G_ℚ`, and nothing here claims it; it must be discharged by 120c's actual
`H`/`j` output. -/

/-- **`hidx` for the helper**, given a genuinely verified range identification. -/
theorem cast_index_range_ne_zero_of_range_eq [NumberField L] (k : Type*) [Field k] [CharZero k]
    {Γ : Type*} [Group Γ] (jj : Γ →* GQ) (hjj : MonoidHom.range jj = fixSub ι) :
    (((MonoidHom.range jj).index : ℕ) : k) ≠ 0 := by
  rw [hjj]
  exact cast_index_fixSub_ne_zero ι k

/-- The same, with the index also identified as `[L:ℚ]`. -/
theorem index_range_eq_of_range_eq [NumberField L] {Γ : Type*} [Group Γ] (jj : Γ →* GQ)
    (hjj : MonoidHom.range jj = fixSub ι) :
    (MonoidHom.range jj).index = Module.finrank ℚ L := by
  rw [hjj, index_fixSub]

/-! ## 4. Negative controls -/

/-- **Finite-dimensionality is necessary.** For an intermediate field that is not finite over `ℚ`
the library equality forces index `0`: the subgroup has infinite index and no `hidx` can be had.
(`Module.finrank` is `0` by convention in the infinite-dimensional case, and the library lemma
covers that case, so this is an equality, not an artefact.) -/
theorem index_eq_zero_of_not_finiteDimensional (E : IntermediateField ℚ Qbar)
    (h : ¬ FiniteDimensional ℚ E) : E.fixingSubgroup.index = 0 := by
  rw [← IntermediateField.finrank_eq_fixingSubgroup_index, Module.finrank_of_infinite_dimensional h]

theorem cast_index_eq_zero_of_not_finiteDimensional (k : Type*) [Field k]
    (E : IntermediateField ℚ Qbar) (h : ¬ FiniteDimensional ℚ E) :
    ((E.fixingSubgroup.index : ℕ) : k) = 0 := by
  rw [index_eq_zero_of_not_finiteDimensional E h, Nat.cast_zero]

/-- **Characteristic zero is necessary for the cast.** If `char k = p` divides `[L:ℚ]` then the
index casts to `0`, even though it is finite — so `hidx` fails in positive characteristic. -/
theorem cast_index_eq_zero_of_charP_dvd [NumberField L] (k : Type*) [Field k] (p : ℕ)
    [CharP k p] (hp : p ∣ Module.finrank ℚ L) : (((fixSub ι).index : ℕ) : k) = 0 := by
  rw [index_fixSub]
  exact (CharP.cast_eq_zero_iff k p _).mpr hp

/-- The quadratic instance of the characteristic control, over any field of characteristic 2. -/
theorem cast_index_eq_zero_of_char_two [NumberField L] (k : Type*) [Field k] [CharP k 2]
    (h2 : Module.finrank ℚ L = 2) : (((fixSub ι).index : ℕ) : k) = 0 :=
  cast_index_eq_zero_of_charP_dvd ι k 2 (by rw [h2])

/-! ## 5. Checks -/

#check @fixSub
#check @mem_fixSub_iff
#check @mem_fixSub_iff_comp
#check @index_fixSub
#check @cast_index_fixSub_ne_zero
#check @cast_index_range_ne_zero_of_range_eq

#print axioms mem_fixSub_iff
#print axioms mem_fixSub_iff_comp
#print axioms finrank_fieldRange
#print axioms index_fixSub
#print axioms index_fixSub_ne_zero
#print axioms cast_index_fixSub_ne_zero
#print axioms exists_embedding
#print axioms cast_index_range_ne_zero_of_range_eq
#print axioms index_range_eq_of_range_eq
#print axioms index_eq_zero_of_not_finiteDimensional
#print axioms cast_index_eq_zero_of_charP_dvd
#print axioms cast_index_eq_zero_of_char_two

end ClimbGaloisIndex
