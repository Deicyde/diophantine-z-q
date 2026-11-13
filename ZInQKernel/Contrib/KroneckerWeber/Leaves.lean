import ZInQKernel.Contrib.TauCeti.NumberTheory.ClassFieldTheory.ClassFields.KroneckerWeber

/-!
# The Kronecker–Weber leaves, proved from Tau Ceti's `kroneckerWeber`

Tau Ceti (vendored under `ZInQKernel/Contrib/TauCeti/`) proves the Kronecker–Weber theorem as
`TauCeti.ClassFieldTheory.kroneckerWeber (E : Type) [Field E] [NumberField E]
[IsAbelianGalois ℚ E] : ∃ n : ℕ, n ≠ 0 ∧ Nonempty (E →ₐ[ℚ] CyclotomicField n ℚ)`.

The decomposition states the theorem in three forms, in scratch files that cannot be imported.
Each is restated here verbatim as a `def … : Prop` (source in its docstring) and proved outright:

* `HSynKroneckerWeber` (leaf T17, `HSyn.KroneckerWeber`, `scratch/h-decomposition/Leaves.lean`);
* `GlueKroneckerWeber` (`KroneckerWeber`, `scratch/glue-assembly/Leaves.lean`);
* `KroneckerWeberCyclic` (`TSkolemKW.KW.KroneckerWeberCyclic`,
  `scratch/t-skolem-kw/KroneckerWeberUse.lean`).
-/

namespace ZInQ.Contrib.KroneckerWeber

/-- **L17. Kronecker–Weber** (Washington, *Cyclotomic fields*, Thm 14.1; Tau Ceti
`kroneckerWeber`). Verbatim `HSyn.KroneckerWeber`, `scratch/h-decomposition/Leaves.lean`
(line 21206 at fork main 883c4ddf); the same text is `TSkolemKW.KW.KroneckerWeber` in
`scratch/t-skolem-kw/KroneckerWeberUse.lean`. -/
def HSynKroneckerWeber : Prop :=
  ∀ (L : Type) [Field L] [NumberField L] [IsGalois ℚ L],
    (∀ σ τ : L ≃ₐ[ℚ] L, σ * τ = τ * σ) →
    ∃ n : ℕ+, Nonempty (L →ₐ[ℚ] CyclotomicField (n : ℕ) ℚ)

/-- Verbatim `KroneckerWeber`, `scratch/glue-assembly/Leaves.lean` (line 19 at fork main
883c4ddf). -/
def GlueKroneckerWeber : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [IsGalois ℚ K],
    (∀ a b : K ≃ₐ[ℚ] K, a * b = b * a) →
      ∃ n : ℕ, 0 < n ∧ Nonempty (K →ₐ[ℚ] CyclotomicField n ℚ)

/-- **Kronecker–Weber for cyclic extensions.** Verbatim `TSkolemKW.KW.KroneckerWeberCyclic`,
`scratch/t-skolem-kw/KroneckerWeberUse.lean` (line 108 at fork main 883c4ddf). -/
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

/-- **Kronecker–Weber for cyclic extensions is proved.** -/
theorem kroneckerWeberCyclic : KroneckerWeberCyclic := by
  intro L _ _ _ hc
  let _ : CommGroup (L ≃ₐ[ℚ] L) := IsCyclic.commGroup
  exact hSynKroneckerWeber L fun σ τ => mul_comm σ τ

end ZInQ.Contrib.KroneckerWeber
