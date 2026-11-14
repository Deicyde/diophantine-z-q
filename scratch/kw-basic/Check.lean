import ZInQKernel.Contrib.TauCeti.NumberTheory.ClassFieldTheory.ClassFields.KroneckerWeber

/-!
# The Kronecker–Weber theorem in Mathlib terms, from Tau Ceti's `kroneckerWeber`

This module imports only the vendored Tau Ceti module
`ZInQKernel.Contrib.TauCeti.NumberTheory.ClassFieldTheory.ClassFields.KroneckerWeber` (and through
it Mathlib and other vendored Tau Ceti modules); it does not import `ZInQKernel/HDecomp/`.

Tau Ceti proves the Kronecker–Weber theorem as
`TauCeti.ClassFieldTheory.kroneckerWeber (E : Type) [Field E] [NumberField E]
[IsAbelianGalois ℚ E] : ∃ n : ℕ, n ≠ 0 ∧ Nonempty (E →ₐ[ℚ] CyclotomicField n ℚ)`.

Every statement below is over Mathlib's definitions only (`NumberField`, `IsGalois`, `AlgEquiv`,
`CyclotomicField`, `IsCyclic`):

* `HSynKroneckerWeber` (verbatim leaf T17, `HSyn.KroneckerWeber` of
  `scratch/h-decomposition/Leaves.lean`, also the body of `TSkolemKW.KW.KroneckerWeber`), proved
  as `hSynKroneckerWeber`;
* `GlueKroneckerWeber` (verbatim `KroneckerWeber` of `scratch/glue-assembly/Leaves.lean`), proved
  as `glueKroneckerWeber`;
* `KroneckerWeberCyclic` (verbatim body of `TSkolemKW.KW.KroneckerWeberCyclic`, the cyclic case
  that step C8 uses), proved as `kroneckerWeber_cyclic`.

`ZInQKernel.Contrib.KroneckerWeber.Leaves` identifies the last statement and `HSynKroneckerWeber`
with their `HDecomp` copies (`TSkolemKW.KW.KroneckerWeber(Cyclic)`) by `Iff.rfl`.
-/

namespace ZInQ.Contrib.KroneckerWeber

/-- **L17. Kronecker–Weber** (Washington, *Cyclotomic fields*, Thm 14.1; Tau Ceti
`kroneckerWeber`). Verbatim `HSyn.KroneckerWeber`, `scratch/h-decomposition/Leaves.lean`
(line 21206 at fork main c303557d). -/
def HSynKroneckerWeber : Prop :=
  ∀ (L : Type) [Field L] [NumberField L] [IsGalois ℚ L],
    (∀ σ τ : L ≃ₐ[ℚ] L, σ * τ = τ * σ) →
    ∃ n : ℕ+, Nonempty (L →ₐ[ℚ] CyclotomicField (n : ℕ) ℚ)

/-- Verbatim `GlueAssembly.KroneckerWeber`, `scratch/glue-assembly/Leaves.lean` (line 19 at fork
main c303557d). -/
def GlueKroneckerWeber : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [IsGalois ℚ K],
    (∀ a b : K ≃ₐ[ℚ] K, a * b = b * a) →
      ∃ n : ℕ, 0 < n ∧ Nonempty (K →ₐ[ℚ] CyclotomicField n ℚ)

/-- **Kronecker–Weber for cyclic extensions** (the case step C8 uses: the fixed field of the kernel
of a finite-order character with values in a field). Verbatim body of
`TSkolemKW.KW.KroneckerWeberCyclic` (`ZInQKernel/HDecomp/Textbook/KroneckerWeberUse.lean`). A
consequence of `HSynKroneckerWeber` (`kroneckerWeberCyclic_of_kroneckerWeber`), so never stronger
than the published theorem. -/
def KroneckerWeberCyclic : Prop :=
  ∀ (L : Type) [Field L] [NumberField L] [IsGalois ℚ L], IsCyclic (L ≃ₐ[ℚ] L) →
    ∃ n : ℕ+, Nonempty (L →ₐ[ℚ] CyclotomicField (n : ℕ) ℚ)

/-- A Galois extension of `ℚ` with commuting automorphisms is abelian Galois. -/
theorem isAbelianGalois_of_comm (L : Type) [Field L] [Algebra ℚ L] [IsGalois ℚ L]
    (h : ∀ σ τ : L ≃ₐ[ℚ] L, σ * τ = τ * σ) : IsAbelianGalois ℚ L :=
  { toIsGalois := inferInstance
    toIsMulCommutative := ⟨⟨h⟩⟩ }

/-- Tau Ceti's Kronecker–Weber theorem with a positive level. -/
theorem exists_pos_algHom_cyclotomicField (L : Type) [Field L] [NumberField L] [IsGalois ℚ L]
    (h : ∀ σ τ : L ≃ₐ[ℚ] L, σ * τ = τ * σ) :
    ∃ n : ℕ, 0 < n ∧ Nonempty (L →ₐ[ℚ] CyclotomicField n ℚ) := by
  have := isAbelianGalois_of_comm L h
  obtain ⟨n, hn, hL⟩ := TauCeti.ClassFieldTheory.kroneckerWeber L
  exact ⟨n, Nat.pos_of_ne_zero hn, hL⟩

/-- **Leaf T17 (`HSyn.KroneckerWeber`) is proved.** -/
theorem hSynKroneckerWeber : HSynKroneckerWeber := by
  intro L _ _ _ h
  obtain ⟨n, hn, hL⟩ := exists_pos_algHom_cyclotomicField L h
  exact ⟨⟨n, hn⟩, hL⟩

/-- **The glue-assembly form of Kronecker–Weber is proved.** -/
theorem glueKroneckerWeber : GlueKroneckerWeber := by
  intro K _ _ _ h
  exact exists_pos_algHom_cyclotomicField K h

/-- The cyclic case follows from the general one (verbatim proof of
`TSkolemKW.KW.kroneckerWeberCyclic_of_kroneckerWeber`). -/
theorem kroneckerWeberCyclic_of_kroneckerWeber (h : HSynKroneckerWeber) :
    KroneckerWeberCyclic := by
  intro L _ _ _ hc
  let _ : CommGroup (L ≃ₐ[ℚ] L) := IsCyclic.commGroup
  exact h L fun σ τ => mul_comm σ τ

/-- **Kronecker–Weber for cyclic extensions is proved.** -/
theorem kroneckerWeber_cyclic : KroneckerWeberCyclic :=
  kroneckerWeberCyclic_of_kroneckerWeber hSynKroneckerWeber

end ZInQ.Contrib.KroneckerWeber

/-! ## Axiom check (scratch copy of `ZInQKernel/Contrib/KroneckerWeber/Basic.lean`) -/

#print axioms ZInQ.Contrib.KroneckerWeber.isAbelianGalois_of_comm
#print axioms ZInQ.Contrib.KroneckerWeber.exists_pos_algHom_cyclotomicField
#print axioms ZInQ.Contrib.KroneckerWeber.hSynKroneckerWeber
#print axioms ZInQ.Contrib.KroneckerWeber.glueKroneckerWeber
#print axioms ZInQ.Contrib.KroneckerWeber.kroneckerWeberCyclic_of_kroneckerWeber
#print axioms ZInQ.Contrib.KroneckerWeber.kroneckerWeber_cyclic
