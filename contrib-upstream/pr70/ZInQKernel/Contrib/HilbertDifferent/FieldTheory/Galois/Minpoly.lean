/-
Ported with Codex assistance on 2026-11-14 from trureturing@8af78b5bb176c99b2750222c0dd3d00a475d39eb.
Source: D5/S3/Factorization/Dedekind/HilbertDifferent/FieldTheory/Galois/Minpoly.lean
Original SHA-256: fc93fcaf9384fdd196b87a75e8203c13b2df32b10b0e65442fa978cec6c5bcd6
Changes: contribution import paths and namespace; retained proof content.
Full licenses and provenance: ZInQKernel/Contrib/HilbertDifferent/Attribution.lean.
-/

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
/- Adapted to the repository-pinned Mathlib API; only declarations needed by the
Hilbert different consumer are retained. Source: TauCeti@33c2099c678ea391f7ea3e0ddaf945a76a625e5d,
TauCeti/FieldTheory/Galois/Minpoly.lean.
Full license and pertinent inherited attribution: ZInQKernel/Contrib/HilbertDifferent/Attribution.lean.
Replace this port by direct use when this project's pinned Mathlib supplies an equivalent declaration. -/


import Mathlib.FieldTheory.Galois.Basic
import Mathlib.FieldTheory.Minpoly.ConjRootClass
import ZInQKernel.Contrib.HilbertDifferent.Support.TameDifferent

noncomputable section

section

open Polynomial IntermediateField

namespace TauCeti

variable {K L : Type*} [Field K] [Field L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]

/- The image in `L[X]` of the minimal polynomial of a primitive element `x` of a finite Galois
extension `L/K` is `∏ σ : Gal(L/K), (X - C (σ x))`. -/
theorem minpoly_map_eq_prod_X_sub_C_of_adjoin_eq_top {x : L} (hx : K⟮x⟯ = ⊤) :
    (minpoly K x).map (algebraMap K L) = ∏ σ : L ≃ₐ[K] L, (X - C (σ x)) := by
  classical
  -- An automorphism is determined by its value at the generator `x`.
  have hinj : Function.Injective fun σ : L ≃ₐ[K] L ↦ σ x := fun σ τ h ↦
    AlgEquiv.coe_toAlgHom_injective <| AlgHom.ext_of_adjoin_eq_top
      ((adjoin_eq_top_iff_of_isAlgebraic fun y _ ↦ IsAlgebraic.of_finite K y).1 hx)
      (Set.eqOn_singleton.2 h)
  -- The conjugacy class of `x` is its Galois orbit.
  have hcarrier : (ConjRootClass.mk K x).carrier.toFinset =
      Finset.univ.image fun σ : L ≃ₐ[K] L ↦ σ x := by
    ext y
    simp [ConjRootClass.mem_carrier, isConjRoot_iff_exists_algEquiv]
  rw [← ConjRootClass.minpoly_mk, ConjRootClass.minpoly.map_eq_prod, hcarrier,
    Finset.prod_image fun σ _ τ _ h ↦ hinj h]

/- The derivative of the minimal polynomial of a primitive element `x` of a finite Galois
extension, evaluated at `x`, is `∏_{σ ≠ 1} (x - σ x)`. -/
theorem aeval_derivative_minpoly_eq_prod_of_adjoin_eq_top [DecidableEq (L ≃ₐ[K] L)] {x : L}
    (hx : K⟮x⟯ = ⊤) :
    aeval x (derivative (minpoly K x)) =
      ∏ σ ∈ Finset.univ.erase (1 : L ≃ₐ[K] L), (x - σ x) := by
  classical
  -- `x` is the root of the linear factor indexed by the identity automorphism.
  have hmem : x ∈ Multiset.map (fun σ : L ≃ₐ[K] L ↦ σ x) Finset.univ.val :=
    Multiset.mem_map.2 ⟨1, Finset.mem_univ _, AlgEquiv.one_apply x⟩
  -- Erasing that root from the multiset of conjugates erases the identity from the index set.
  have herase : (Multiset.map (fun σ : L ≃ₐ[K] L ↦ σ x) Finset.univ.val).erase x =
      Multiset.map (fun σ : L ≃ₐ[K] L ↦ σ x) (Finset.univ.erase (1 : L ≃ₐ[K] L)).val := by
    rw [Finset.erase_val, Multiset.map_erase_of_mem _ _ (Finset.mem_univ 1), AlgEquiv.one_apply]
  -- The product over the Galois group is the product of `X - C a` over the multiset of conjugates.
  have hprod : ∏ σ : L ≃ₐ[K] L, (X - C (σ x)) =
      (Multiset.map (fun a : L ↦ X - C a)
        (Multiset.map (fun σ : L ≃ₐ[K] L ↦ σ x) Finset.univ.val)).prod := by
    rw [Multiset.map_map]; rfl
  rw [aeval_def, eval₂_eq_eval_map, ← derivative_map,
    minpoly_map_eq_prod_X_sub_C_of_adjoin_eq_top hx, hprod,
    eval_multiset_prod_X_sub_C_derivative hmem, herase, Multiset.map_map]
  rfl

end TauCeti
