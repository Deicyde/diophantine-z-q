import ZInQKernel.HDecomp.Objects
import ZInQKernel.Contrib.AVB1.AlgClosed

/-!
# faltings-cm: `r9b` (`PkgI3.FaltingsTate`) from the surjectivity half of Faltings' theorem

Copyright: this file is part of the fork Deicyde/diophantine-z-q (task faltings-cm, 2026-11-15).

The bundle field `OpenResearchLeaves22.r9b : PkgI3.FaltingsTate` (Faltings 1983, Satz 4 and Korollar 1) has two
halves: the natural map `ℤ_ℓ ⊗ Hom_K(A, B) → Hom_{ℤ_ℓ}(T_ℓ A, T_ℓ B)` is injective, and its image is the
set of `G_K`-equivariant maps. On the route to `ZInQ.OneProof.frozenTarget`:

* the injectivity half is Mumford's §19, Theorem 3 (Weil, Tate; no Faltings), which is already in the bundles as
  `OpenTextbookLeaves11.homFreeFiniteAlgClosed`, over any field (via the kernel's proved base change
  `ZInQ.Contrib.AVB1.homFreeFinite_of_algClosed`);
* the inclusion `image ⊆ equivariant` is proved outright (`PkgI3.range_tateHomZl_subset`);
* so the only content of Faltings' theorem the route uses is the inclusion `equivariant ⊆ image`:
  `FaltingsTateSurj` below, a consequence of the published statement, strictly weaker as a Prop.

`faltingsTate_of_surj` proves the field from `FaltingsTateSurj` and the bundle field `homFreeFiniteAlgClosed`;
`faltingsTateSurj_of_faltingsTate` proves that the new leaf is implied by the field it replaces.
-/

noncomputable section

namespace ZInQ.Contrib.FaltingsCM

open PkgI3 PkgI3.AbVar

/-- **Faltings 1983, Satz 4 and Korollar 1, surjectivity half (printed form, consequence).** G. Faltings,
*Endlichkeitssätze für abelsche Varietäten über Zahlkörpern*, Invent. Math. 73 (1983), 349-366, §5, Satz 4
(`A = B`) and Korollar 1 (Tate's conjecture: `Hom_K(A, B) ⊗ ℤ_ℓ ≅ Hom_{G_K}(T_ℓ A, T_ℓ B)`) (UNVERIFIED locator;
the same source as the bundle field `r9b`). For abelian varieties `A, B` over a number field `K` and a prime
`ℓ`, every `G_K`-equivariant `ℤ_ℓ`-linear map `T_ℓ A → T_ℓ B` is in the image of
`ℤ_ℓ ⊗ Hom_K(A, B)`. This is the second conjunct of `PkgI3.FaltingsTate` with `=` weakened to `⊇`, and without
the injectivity conjunct. -/
def FaltingsTateSurj : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (A B : AbVar K) (ℓ : ℕ) [Fact ℓ.Prime],
    {φ | IsGalEquivariant φ} ⊆ Set.range (tateHomZl ℓ A B)

/-- **The new leaf is implied by the field it replaces** (`r9b`). -/
theorem faltingsTateSurj_of_faltingsTate (h : PkgI3.FaltingsTate) : FaltingsTateSurj :=
  fun K _ _ A B ℓ _ => (h K A B ℓ).2.symm.subset

/-- **`r9b` from the surjectivity half and Mumford §19 Thm 3** (the bundle field
`OpenTextbookLeaves11.homFreeFiniteAlgClosed`). Injectivity: `homFreeFinite_of_algClosed` at the number field `K`
(characteristic `0`, so `ℓ ≠ 0` in `K`). The inclusion `image ⊆ equivariant`: `range_tateHomZl_subset`. -/
theorem faltingsTate_of_surj (hS : FaltingsTateSurj)
    (hH : ZInQ.Contrib.AVB1.HomFreeFiniteAlgClosed) : PkgI3.FaltingsTate := by
  intro K _ _ A B ℓ _
  have hℓK : (ℓ : K) ≠ 0 := Nat.cast_ne_zero.mpr (Fact.out : ℓ.Prime).ne_zero
  refine ⟨(ZInQ.Contrib.AVB1.homFreeFinite_of_algClosed hH K A B).2.2.2 ℓ hℓK, ?_⟩
  exact Set.Subset.antisymm (range_tateHomZl_subset A B ℓ) (hS K A B ℓ)

end ZInQ.Contrib.FaltingsCM
