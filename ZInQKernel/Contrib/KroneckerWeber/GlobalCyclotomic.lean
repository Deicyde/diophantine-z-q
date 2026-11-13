/-
Exact simultaneous global cyclotomic-field assembly, using the unchanged
Mathlib v4.35.0 pin. New additive helper module; the original partial sources
and note are not modified. No local Kronecker–Weber theorem is assumed or proved.
-/
module

public import ZInQKernel.Contrib.KroneckerWeber.GlobalCyclic
public import Mathlib.NumberTheory.Cyclotomic.Basic
public import Mathlib.FieldTheory.Normal.Basic

/-!
# Simultaneous cyclotomic containment and the cyclic arithmetic reduction

The cyclotomic intermediate field is a genuine field of roots of unity in the
algebraic closure of `ℚ`. Normality identifies arbitrary embeddings of a supplied
subfield with that same intermediate field, so independently chosen embeddings
of a finite family are made simultaneous at a single positive level.

The final arithmetic reduction has an EXPLICIT cyclic-extension embedding input.
That input is not supplied in this module and is not a proof of full T17. The
closed helpers preceding it prove the representation/composition transitions;
no name, typeclass, `Fact` or literature assumption hides the missing arithmetic.
-/

@[expose] public section

set_option autoImplicit false

namespace ZInQ.Contrib.KroneckerWeber

/-- The actual cyclotomic field at positive level `n` inside the algebraic closure. -/
noncomputable def cyclotomicLayer (n : ℕ+) : IntermediateField ℚ (AlgebraicClosure ℚ) :=
  IntermediateField.adjoin ℚ {x : AlgebraicClosure ℚ | x ^ (n : ℕ) = 1}

/-- The root-of-unity intermediate field is a cyclotomic extension in Mathlib's
sense, with no abstract embedding or class-field hypothesis. -/
theorem cyclotomicLayer_isCyclotomic (n : ℕ+) :
    IsCyclotomicExtension {(n : ℕ)} ℚ (cyclotomicLayer n) := by
  have : NeZero (n : ℕ) := ⟨n.pos.ne'⟩
  obtain ⟨ζ, hζ⟩ := IsCyclotomicExtension.exists_isPrimitiveRoot
    (AlgebraicClosure ℚ) (AlgebraicClosure ℚ) (S := {(n : ℕ)})
    (Set.mem_singleton (n : ℕ)) n.pos.ne'
  apply (IntermediateField.isCyclotomicExtension_singleton_iff_eq_adjoin
    (n : ℕ) ℚ (AlgebraicClosure ℚ) (cyclotomicLayer n) hζ).mpr
  unfold cyclotomicLayer
  apply le_antisymm
  · rw [IntermediateField.adjoin_le_iff]
    intro x hx
    obtain ⟨i, _, rfl⟩ := hζ.eq_pow_of_pow_eq_one hx
    exact pow_mem (IntermediateField.mem_adjoin_simple_self ℚ ζ) i
  · exact IntermediateField.adjoin.mono ℚ _ _
      (Set.singleton_subset_iff.mpr hζ.pow_eq_one)

/-- The genuine intermediate field is the same cyclotomic extension as the exact
`CyclotomicField` model consumed by T17. -/
noncomputable def cyclotomicLayerEquiv (n : ℕ+) :
    CyclotomicField (n : ℕ) ℚ ≃ₐ[ℚ] cyclotomicLayer n := by
  have : IsCyclotomicExtension {(n : ℕ)} ℚ (cyclotomicLayer n) :=
    cyclotomicLayer_isCyclotomic n
  have : IsCyclotomicExtension {(n : ℕ)} ℚ (CyclotomicField (n : ℕ) ℚ) :=
    CyclotomicField.isCyclotomicExtension (n : ℕ) ℚ
  exact IsCyclotomicExtension.algEquiv {(n : ℕ)} ℚ _ _

/-- Raising the positive cyclotomic level by divisibility enlarges the actual
root-of-unity field in the same algebraic closure. -/
theorem cyclotomicLayer_le_of_dvd {m n : ℕ+} (h : (m : ℕ) ∣ (n : ℕ)) :
    cyclotomicLayer m ≤ cyclotomicLayer n := by
  have : NeZero (n : ℕ) := ⟨n.pos.ne'⟩
  have : IsCyclotomicExtension {(m : ℕ)} ℚ (cyclotomicLayer m) :=
    cyclotomicLayer_isCyclotomic m
  have : IsCyclotomicExtension {(n : ℕ)} ℚ (cyclotomicLayer n) :=
    cyclotomicLayer_isCyclotomic n
  exact IntermediateField.isCyclotomicExtension_le_of_dvd ℚ (AlgebraicClosure ℚ)
    (m : ℕ) (n : ℕ) _ _ h

/-- If an actual subfield of `ℚ̄` admits an abstract embedding into a cyclotomic
field, it is contained in the corresponding actual cyclotomic subfield. Normality
of the latter proves that an independently chosen embedding gives the SAME field;
this step is not inferred merely from the existence of unrelated maps. -/
theorem le_cyclotomicLayer_of_embedding (E : IntermediateField ℚ (AlgebraicClosure ℚ))
    (n : ℕ+) (f : E →ₐ[ℚ] CyclotomicField (n : ℕ) ℚ) :
    E ≤ cyclotomicLayer n := by
  have : IsCyclotomicExtension {(n : ℕ)} ℚ (cyclotomicLayer n) :=
    cyclotomicLayer_isCyclotomic n
  have : IsGalois ℚ (cyclotomicLayer n) :=
    IsCyclotomicExtension.isGalois {(n : ℕ)} ℚ _
  let g : E →ₐ[ℚ] cyclotomicLayer n := (cyclotomicLayerEquiv n).toAlgHom.comp f
  intro x hx
  have hs := (inferInstance : Normal ℚ (cyclotomicLayer n)).splits (g ⟨x, hx⟩)
  have hp : minpoly ℚ (g ⟨x, hx⟩) = minpoly ℚ x :=
    (minpoly.algHom_eq g g.injective ⟨x, hx⟩).trans
      (minpoly.algHom_eq E.val E.val.injective ⟨x, hx⟩).symm
  rw [hp] at hs
  exact (Algebra.IsIntegral.isIntegral x).mem_intermediateField_of_minpoly_splits hs

/-- A finite family of embedded global fields is simultaneously contained in one
cyclotomic field of positive level. Empty families and level one are included. -/
theorem exists_cyclotomicLayer_containing_family {ι : Type*} [Fintype ι]
    (E : ι → IntermediateField ℚ (AlgebraicClosure ℚ))
    (hE : ∀ i, ∃ n : ℕ+, Nonempty ((E i) →ₐ[ℚ] CyclotomicField (n : ℕ) ℚ)) :
    ∃ n : ℕ+, (⨆ i, E i) ≤ cyclotomicLayer n := by
  classical
  choose n hn using hE
  let N : ℕ := ∏ i, (n i : ℕ)
  have hN : 0 < N := Finset.prod_pos (fun i _ => (n i).pos)
  refine ⟨⟨N, hN⟩, iSup_le fun i => ?_⟩
  exact (le_cyclotomicLayer_of_embedding (E i) (n i) (hn i).some).trans
    (cyclotomicLayer_le_of_dvd (Finset.dvd_prod_of_mem _ (Finset.mem_univ i)))

/-- Assemble actual embeddings of generating intermediate fields of the original
number field into an actual embedding of that same number field. The hypothesis
supplies arithmetic embeddings of the factors only; simultaneous field identity,
positive common level and exact codomain are proved here. -/
theorem exists_positive_embedding_of_generating_subfields
    (L : Type*) [Field L] [NumberField L] {ι : Type*} [Fintype ι]
    (F : ι → IntermediateField ℚ L) (hgen : (⨆ i, F i) = ⊤)
    (hF : ∀ i, ∃ n : ℕ+, Nonempty ((F i) →ₐ[ℚ] CyclotomicField (n : ℕ) ℚ)) :
    ∃ n : ℕ+, Nonempty (L →ₐ[ℚ] CyclotomicField (n : ℕ) ℚ) := by
  classical
  let φ : L →ₐ[ℚ] AlgebraicClosure ℚ := IsAlgClosed.lift
  let E (i : ι) : IntermediateField ℚ (AlgebraicClosure ℚ) := (F i).map φ
  have hE : ∀ i, ∃ n : ℕ+, Nonempty ((E i) →ₐ[ℚ] CyclotomicField (n : ℕ) ℚ) := by
    intro i
    obtain ⟨n, ⟨f⟩⟩ := hF i
    exact ⟨n, ⟨f.comp ((F i).equivMap φ).symm.toAlgHom⟩⟩
  obtain ⟨n, hn⟩ := exists_cyclotomicLayer_containing_family E hE
  have hφ : φ.fieldRange ≤ cyclotomicLayer n := by
    rw [AlgHom.fieldRange_eq_map, ← hgen, IntermediateField.map_iSup]
    exact hn
  exact ⟨n, ⟨(cyclotomicLayerEquiv n).symm.toAlgHom.comp
    ((IntermediateField.inclusion hφ).comp φ.equivFieldRange.toAlgHom)⟩⟩

/-- A conditional arithmetic reduction: if every cyclic Galois subextension of the
input field has a positive cyclotomic embedding, the full abelian input embeds.
No such cyclic arithmetic supplier is assumed as a `Fact`, hidden typeclass or
proved theorem here. This is not an unrestricted T17 provider. -/
theorem exists_positive_embedding_of_cyclic_subfield_input
    (L : Type*) [Field L] [NumberField L] [IsAbelianGalois ℚ L]
    (hcyclic : ∀ F : IntermediateField ℚ L, IsGalois ℚ F →
      IsCyclic (F ≃ₐ[ℚ] F) →
        ∃ n : ℕ+, Nonempty (F →ₐ[ℚ] CyclotomicField (n : ℕ) ℚ)) :
    ∃ n : ℕ+, Nonempty (L →ₐ[ℚ] CyclotomicField (n : ℕ) ℚ) := by
  obtain ⟨ι, _, F, hF, hgen⟩ := exists_cyclic_subextensions L
  exact exists_positive_embedding_of_generating_subfields L F hgen
    (fun i => hcyclic (F i) (hF i).1 (hF i).2)

end ZInQ.Contrib.KroneckerWeber
