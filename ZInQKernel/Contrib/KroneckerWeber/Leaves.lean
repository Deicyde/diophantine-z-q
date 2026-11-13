import ZInQKernel.Contrib.TauCeti.NumberTheory.ClassFieldTheory.ClassFields.KroneckerWeber
import ZInQKernel.HDecomp.Textbook.KroneckerWeberUse

/-!
# The Kronecker–Weber leaves, proved from Tau Ceti's `kroneckerWeber`

Tau Ceti (vendored under `ZInQKernel/Contrib/TauCeti/`) proves the Kronecker–Weber theorem as
`TauCeti.ClassFieldTheory.kroneckerWeber (E : Type) [Field E] [NumberField E]
[IsAbelianGalois ℚ E] : ∃ n : ℕ, n ≠ 0 ∧ Nonempty (E →ₐ[ℚ] CyclotomicField n ℚ)`.

The decomposition states the theorem in several forms:

* `TSkolemKW.KW.KroneckerWeber` and `TSkolemKW.KW.KroneckerWeberCyclic`, defined in
  `ZInQKernel.HDecomp.Textbook.KroneckerWeberUse` (imported; proved here as
  `tSkolemKW_kroneckerWeber`, `kroneckerWeberCyclic`);
* leaf T17, `HSyn.KroneckerWeber` (`scratch/h-decomposition/Leaves.lean`) and `KroneckerWeber`
  of `scratch/glue-assembly/Leaves.lean`; these exist only in scratch files, so they are restated
  verbatim here (`HSynKroneckerWeber`, `GlueKroneckerWeber`) and proved.

Step C8's consumer (`TSkolemKW.KW.dirichletCharacter_of_kroneckerWeberCyclic` and its companions)
is then closed outright in the last section.
-/

open PkgI4 (Qbar GQ)

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

/-- **`TSkolemKW.KW.KroneckerWeber` (the Textbook copy of T17) is proved.** -/
theorem tSkolemKW_kroneckerWeber : TSkolemKW.KW.KroneckerWeber := hSynKroneckerWeber

/-- **Kronecker–Weber for cyclic extensions (`TSkolemKW.KW.KroneckerWeberCyclic`) is proved.** -/
theorem kroneckerWeberCyclic : TSkolemKW.KW.KroneckerWeberCyclic :=
  TSkolemKW.KW.kroneckerWeberCyclic_of_kroneckerWeber tSkolemKW_kroneckerWeber

/-! ## Step C8 outright: finite-order characters of `G_ℚ` are Dirichlet characters -/

/-- **C8, outright.** For `ψ : G_ℚ →* Eˣ` (`E` a field) with open kernel there are `m ≥ 1` and a
Dirichlet character `χ` mod `m` with `ψ = χ ∘ cyc_m`
(`TSkolemKW.KW.dirichletCharacter_of_kroneckerWeberCyclic` with its hypothesis discharged). -/
theorem dirichletCharacter_of_openKer {E : Type*} [Field E] (ψ : GQ →* Eˣ)
    (hψ : IsOpen (ψ.ker : Set GQ)) :
    ∃ (m : ℕ+) (χ : DirichletCharacter E (m : ℕ)),
      ∀ σ : GQ, (ψ σ : E) = χ ((TSkolemKW.KW.cycChar m σ : (ZMod m)ˣ) : ZMod m) :=
  TSkolemKW.KW.dirichletCharacter_of_kroneckerWeberCyclic kroneckerWeberCyclic ψ hψ

/-- **C8, outright, continuous form.** A continuous `ψ : G_ℚ →* Eˣ` with finite image, `E` a
topological field with `T1` units, is a Dirichlet character composed with `cyc_m`. -/
theorem dirichletCharacter_of_continuous {E : Type*} [Field E] [TopologicalSpace Eˣ]
    [T1Space Eˣ] (ψ : GQ →* Eˣ) (hc : Continuous ψ) (hfin : (Set.range ψ).Finite) :
    ∃ (m : ℕ+) (χ : DirichletCharacter E (m : ℕ)),
      ∀ σ : GQ, (ψ σ : E) = χ ((TSkolemKW.KW.cycChar m σ : (ZMod m)ˣ) : ZMod m) :=
  dirichletCharacter_of_openKer ψ (TSkolemKW.KW.isOpen_ker_of_continuous ψ hc hfin)

/-- **`ker_ge_of_kroneckerWeber`, outright** (any commutative target group). -/
theorem ker_ge_of_openKer {G : Type*} [CommGroup G] (ψ : GQ →* G)
    (hψ : IsOpen (ψ.ker : Set GQ)) :
    ∃ m : ℕ+, ∀ σ : GQ, (∀ ζ : Qbar, ζ ^ (m : ℕ) = 1 → σ ζ = ζ) → ψ σ = 1 :=
  TSkolemKW.KW.ker_ge_of_kroneckerWeber tSkolemKW_kroneckerWeber ψ hψ

/-- **`eq_of_agree_on_roots`, outright** (any commutative target group). -/
theorem eq_of_agree_on_roots {G : Type*} [CommGroup G] (ψ : GQ →* G)
    (hψ : IsOpen (ψ.ker : Set GQ)) :
    ∃ m : ℕ+, ∀ σ τ : GQ, (∀ ζ : Qbar, ζ ^ (m : ℕ) = 1 → σ ζ = τ ζ) → ψ σ = ψ τ :=
  TSkolemKW.KW.eq_of_agree_on_roots tSkolemKW_kroneckerWeber ψ hψ

end ZInQ.Contrib.KroneckerWeber
