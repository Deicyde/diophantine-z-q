/-
climb/galois-index — bridge and checks.

Three jobs, nothing more:

 1. **Comparison with the independent specification.** `ClimbIndexExpected.fixingEmbedding`
    (independent pre-candidate module `GaloisIndexExpected.lean`,
    sha256 641c1965384cd475077c6463bee6435dcea0e9cbeda4b1f953d9171941ddb2f9, compiled by the
    spec author) defines the literal embedding-fixing subgroup by its carrier. This file proves
    that the object constructed in `GaloisIndex.lean` — the fixing subgroup of the actual
    intermediate field `ι.fieldRange` — is **equal** to it, and then discharges all three of the
    spec's targets `IndexEquality`, `IndexCastNonzero`, `RangeIndexCastNonzero`.
    The spec's own compile proved no theorem; these are the proofs.

 2. **The literal `algebraMap` form.** 120c's `CoefficientFixingNative.lean` states `H` as the
    literal coefficient fix `∀ l, σ (algebraMap L ℚ̄ l) = algebraMap L ℚ̄ l`. That source is
    currently UNCOMPILED and is deliberately **not imported here as a provider**. Instead the
    same condition is characterised independently (`mem_fixSub_algebraMap_iff`), so the alias to
    their artifact is a one-line consequence once it is validated.

 3. **Caller bind.** `hidx` of the checked S1/S2 helper is produced from a verified range
    identification, which stays an OPEN explicit hypothesis: the reverse map `k γ = θ γ θ⁻¹` and
    `range k = H` are assigned to 120c/40a and are **not** constructed, duplicated or assumed
    discharged here.
-/

import GaloisIndex
import GaloisIndexExpected
import S2Fill

namespace ClimbGaloisIndexBridge

open ClimbGaloisIndex

/-! ## 1. Equality with the independent specification's object -/

variable {L : Type} [Field L] [NumberField L] (ι : L →ₐ[ℚ] GlueC10.Qbar)

/-- **The constructed object is the specified object.** -/
theorem fixSub_eq_fixingEmbedding : fixSub ι = ClimbIndexExpected.fixingEmbedding ι := by
  ext σ
  rw [mem_fixSub_iff]
  rfl

/-- **Spec target 1, proved**: the exact index equality (library 705 strength, not a bound). -/
theorem indexEquality : ClimbIndexExpected.IndexEquality := by
  intro L _ _ ι
  rw [← fixSub_eq_fixingEmbedding ι, index_fixSub]

/-- **Spec target 2, proved**: the characteristic-zero cast is nonzero. -/
theorem indexCastNonzero : ClimbIndexExpected.IndexCastNonzero := by
  intro L _ _ ι k _ _
  rw [← fixSub_eq_fixingEmbedding ι]
  exact cast_index_fixSub_ne_zero ι k

/-- **Spec target 3, proved**: with an EXPLICIT range identification (never fabricated). -/
theorem rangeIndexCastNonzero : ClimbIndexExpected.RangeIndexCastNonzero := by
  intro L _ _ ι k _ _ jj hjj
  refine cast_index_range_ne_zero_of_range_eq ι k jj ?_
  rw [hjj, fixSub_eq_fixingEmbedding ι]

/-! ## 2. The literal `algebraMap` (coefficient-fixing) form, stated independently -/

section AlgebraMap

variable (L : Type) [Field L] [CharZero L] [Algebra L GlueC10.Qbar]
  [IsScalarTower ℚ L GlueC10.Qbar]

/-- The constructed subgroup, for the canonical embedding of an `L`-algebra structure on `ℚ̄`,
is exactly the literal coefficient-fixing condition used by 120c's `CoefficientFixingNative`.
Their source is not imported; this is the independent characterisation. -/
theorem mem_fixSub_algebraMap_iff (σ : GlueC10.GQ) :
    σ ∈ fixSub (IsScalarTower.toAlgHom ℚ L GlueC10.Qbar) ↔
      ∀ l : L, σ (algebraMap L GlueC10.Qbar l) = algebraMap L GlueC10.Qbar l := by
  rw [mem_fixSub_iff]
  rfl

/-- …and its index is `[L:ℚ]` whenever `L` is a number field. -/
theorem index_fixSub_algebraMap [NumberField L] :
    (fixSub (IsScalarTower.toAlgHom ℚ L GlueC10.Qbar)).index = Module.finrank ℚ L :=
  index_fixSub _

end AlgebraMap

/-! ## 3. Caller bind into the checked S1/S2 helper

The range identification `MonoidHom.range jj = fixSub ι` remains an open hypothesis of this
statement. It is 120c/40a's reverse-map artifact to supply; nothing here closes it. -/

open GlueDescent GlueC10 GlueC10Link PkgI3
open scoped TensorProduct

theorem hr_of_globalTateComparison_with_galois_index
    (hS : PkgI3.FaltingsSemisimple) (hTF : PkgI3.TateModuleFree)
    {C : Type} [Field C] [CharZero C]
    (c ε : GlueC10.GQ → GlueC10.GQ → C) (a β : GlueC10.GQ → C)
    (ha : ∀ g h, a g * a h * c g h = ε g h * a (g * h))
    (hβ : ∀ g h, β g * β h = ε g h * β (g * h)) (hβ0 : ∀ g, β g ≠ 0)
    (ha1 : a 1 = 1) (hβ1 : β 1 = 1)
    {k₃ V₃ : Type} [Field k₃] [Algebra ℚ_[3] k₃] [CharZero k₃]
    [AddCommGroup V₃] [Module k₃ V₃]
    (ι₃ : C →+* k₃) (T₃ : GlueC10.GQ → Module.End k₃ V₃)
    (hT₃ : ∀ g h, T₃ g * T₃ h = ι₃ (c g h) • T₃ (g * h)) (hT₃1 : T₃ 1 = 1)
    (u₃ : MatrixUnits2 k₃ V₃) (hu₃ : ∀ g i j, Commute (T₃ g) (u₃.e i j))
    -- the actual number field, its actual embedding, and the OPEN range identification
    {L : Type} [Field L] [NumberField L] (A : PkgI3.AbVar L)
    (ιL : L →ₐ[ℚ] GlueC10.Qbar)
    (jj : Field.absoluteGaloisGroup L →* GlueC10.GQ)
    (hjj : MonoidHom.range jj = fixSub ιL)
    (Ψ : V₃ ≃ₗ[k₃] TensorProduct ℚ_[3] k₃ (A.V 3))
    (χ : Field.absoluteGaloisGroup L → k₃) (hχ : ∀ σ, χ σ ≠ 0)
    (hΨ : ∀ σ, Ψ.toLinearMap ∘ₗ T₃ (jj σ) =
      χ σ • ((GlueI3.repBaseChange k₃ (A.galRep 3) σ) ∘ₗ Ψ.toLinearMap)) :
    IsSemisimpleModule (MonoidAlgebra k₃ GlueC10.GQ)
      (rL c ε a β ha hβ hβ0 ha1 hβ1 ι₃ T₃ hT₃ hT₃1 u₃ hu₃).asModule :=
  ScaledS2Fill.semisimple_rL_of_globalTateComparison_closed hS hTF c ε a β ha hβ hβ0 ha1 hβ1
    ι₃ T₃ hT₃ hT₃1 u₃ hu₃ A jj
    (cast_index_range_ne_zero_of_range_eq ιL k₃ jj hjj) Ψ χ hχ hΨ

/-! ## 4. Checks -/

#check @fixSub_eq_fixingEmbedding
#check @indexEquality
#check @indexCastNonzero
#check @rangeIndexCastNonzero
#check @mem_fixSub_algebraMap_iff
#check @hr_of_globalTateComparison_with_galois_index

#print axioms fixSub_eq_fixingEmbedding
#print axioms indexEquality
#print axioms indexCastNonzero
#print axioms rangeIndexCastNonzero
#print axioms mem_fixSub_algebraMap_iff
#print axioms index_fixSub_algebraMap
#print axioms hr_of_globalTateComparison_with_galois_index

end ClimbGaloisIndexBridge
