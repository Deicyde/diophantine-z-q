/-
Exact global-to-cyclotomic assembly for the Kronecker–Weber route.
The arithmetic conductor/inertia coverage and bounds remain explicit arguments;
this is NOT a closed unrestricted T17 provider and assumes no local KW as a Fact.
-/
module

public import ZInQKernel.Contrib.KroneckerWeber.GlobalInertiaFinite

/-!
# The original number field and its actual cyclotomic compositum

This module constructs the actual compositum in a fixed algebraic closure of `ℚ`.
Its finite-dimensionality and abelian Galois properties are derived. If finite
actual-prime inertia coverage and cardinality bounds with the cyclotomic degree
product are supplied, the proved global inertia generation and degree squeeze
identify this compositum with the exact cyclotomic field. No local completion,
local KW provider or arbitrary abelian conductor witness is proved here.
-/

@[expose] public section

set_option autoImplicit false

namespace ZInQ.Contrib.KroneckerWeber

open NumberField IsDedekindDomain
open scoped NumberField IsMulCommutative

/-- A fixed genuine `ℚ`-algebra embedding of the original number field into `ℚ̄`. -/
noncomputable def rationalClosureEmbedding (L : Type*) [Field L] [NumberField L] :
    L →ₐ[ℚ] AlgebraicClosure ℚ := IsAlgClosed.lift

/-- The actual compositum of the original number-field image and the positive
cyclotomic layer in the SAME algebraic closure. -/
noncomputable def cyclotomicCompositum (L : Type*) [Field L] [NumberField L] (n : ℕ+) :
    IntermediateField ℚ (AlgebraicClosure ℚ) :=
  (rationalClosureEmbedding L).fieldRange ⊔ cyclotomicLayer n

/-- Both parts are finite over `ℚ`, so the actual compositum is a number field. -/
theorem numberField_cyclotomicCompositum (L : Type*) [Field L] [NumberField L] (n : ℕ+) :
    NumberField (cyclotomicCompositum L n) := by
  let φ := rationalClosureEmbedding L
  have : FiniteDimensional ℚ φ.fieldRange := φ.equivFieldRange.toLinearEquiv.finiteDimensional
  have : IsCyclotomicExtension {(n : ℕ)} ℚ (cyclotomicLayer n) :=
    cyclotomicLayer_isCyclotomic n
  have : FiniteDimensional ℚ (cyclotomicLayer n) :=
    IsCyclotomicExtension.finiteDimensional {(n : ℕ)} ℚ _
  change NumberField (φ.fieldRange ⊔ cyclotomicLayer n :
    IntermediateField ℚ (AlgebraicClosure ℚ))
  exact { }

/-- An abelian original number field gives an abelian actual cyclotomic compositum.
The original field's group and the cyclotomic Galois property are transported via
actual maps, not assumed for an unrelated field. -/
theorem isAbelianGalois_cyclotomicCompositum
    (L : Type*) [Field L] [NumberField L] [IsAbelianGalois ℚ L] (n : ℕ+) :
    IsAbelianGalois ℚ (cyclotomicCompositum L n) := by
  let φ := rationalClosureEmbedding L
  have : IsAbelianGalois ℚ φ.fieldRange :=
    IsAbelianGalois.of_algHom φ.equivFieldRange.symm.toAlgHom
  have : IsCyclotomicExtension {(n : ℕ)} ℚ (cyclotomicLayer n) :=
    cyclotomicLayer_isCyclotomic n
  have : IsAbelianGalois ℚ (cyclotomicLayer n) :=
    IsCyclotomicExtension.isAbelianGalois {(n : ℕ)} ℚ _
  change IsAbelianGalois ℚ (φ.fieldRange ⊔ cyclotomicLayer n :
    IntermediateField ℚ (AlgebraicClosure ℚ))
  infer_instance

/-- The actual common-conductor/inertia inputs imply an exact original-field
embedding in `CyclotomicField n ℚ`. ALL arithmetic coverage and bounds are explicit;
they are not a proved arbitrary-abelian conductor theorem in this contribution. -/
theorem nonempty_embedding_of_compositum_inertia_bounds
    (L : Type*) [Field L] [NumberField L] [IsAbelianGalois ℚ L] (n : ℕ+)
    {ι : Type*} [Fintype ι]
    (P : ι → HeightOneSpectrum (𝓞 (cyclotomicCompositum L n)))
    (hcover : ∀ Q : HeightOneSpectrum (𝓞 (cyclotomicCompositum L n)),
      Q.asIdeal.inertia ((cyclotomicCompositum L n) ≃ₐ[ℚ] (cyclotomicCompositum L n)) ≤
        ⨆ i, (P i).asIdeal.inertia
          ((cyclotomicCompositum L n) ≃ₐ[ℚ] (cyclotomicCompositum L n)))
    (b : ι → ℕ)
    (hbound : ∀ i, Nat.card ((P i).asIdeal.inertia
      ((cyclotomicCompositum L n) ≃ₐ[ℚ] (cyclotomicCompositum L n))) ≤ b i)
    (hprod : (∏ i, b i) = (n : ℕ).totient) :
    Nonempty (L →ₐ[ℚ] CyclotomicField (n : ℕ) ℚ) := by
  have : NumberField (cyclotomicCompositum L n) := numberField_cyclotomicCompositum L n
  have : IsAbelianGalois ℚ (cyclotomicCompositum L n) :=
    isAbelianGalois_cyclotomicCompositum L n
  let E := cyclotomicCompositum L n
  let I (i : ι) : Subgroup (E ≃ₐ[ℚ] E) := (P i).asIdeal.inertia (E ≃ₐ[ℚ] E)
  have hI : (⨆ i, I i) = ⊤ := by
    apply top_unique
    rw [← globalInertiaSpan_eq_top E, globalInertiaSpan_def]
    exact iSup_le hcover
  have heq : E = cyclotomicLayer n :=
    eq_cyclotomicLayer_of_subgroup_bounds E I hI b hbound n le_sup_right hprod
  let φ := rationalClosureEmbedding L
  have hφ : φ.fieldRange ≤ cyclotomicLayer n := le_sup_left.trans heq.le
  exact ⟨(cyclotomicLayerEquiv n).symm.toAlgHom.comp
    ((IntermediateField.inclusion hφ).comp φ.equivFieldRange.toAlgHom)⟩

end ZInQ.Contrib.KroneckerWeber
