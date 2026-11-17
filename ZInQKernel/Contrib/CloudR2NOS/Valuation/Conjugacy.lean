/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the source LICENSE.

Adapted from anthropics/fermats-last-theorem@6e837e75355538c7f80bab5b956861e86c4eacc2:
* P2M/Sol/S_ValuationSubring_exists_algEquiv_forall_mem_iff_of_isGalois.lean.
* P2M/Sol/S_ValuationSubring_exists_algEquiv_forall_mem_iff_of_isGalois_infinite.lean.
MODIFICATION NOTICE (2026-11-14, H5 Round-2 Lane2): isolated namespace,
ordinary Lean proofs instead of P2M export/reactivation, narrow import closure;
the finite proof's integral-closure bound calls its direct proved lemma rather
than importing the unused maximal-center existence half of a larger theorem.
Type* universes and every finite/infinite Galois hypothesis are retained.
The source LICENSE, NOTICE and ATTRIBUTION are preserved in the lane report.
-/
import ZInQKernel.Contrib.CloudR2NOS.Valuation.IntegralClosure
import Mathlib.FieldTheory.Galois.Profinite
import Mathlib.RingTheory.Invariant.Galois
import Mathlib.RingTheory.Ideal.Pointwise
import Mathlib.RingTheory.Localization.Integral

set_option autoImplicit false
noncomputable section

namespace ZInQ.Contrib.CloudR2NOS.Valuation
namespace FiniteConjugacy

open IsLocalRing Pointwise
open scoped Pointwise

variable {E F : Type*} [Field E] [Field F] [Algebra E F]

section galois
variable [FiniteDimensional E F] [IsGalois E F] (O : ValuationSubring E)

scoped instance msaGalB : MulSemiringAction Gal(F/E) (integralClosure O F) :=
  IsIntegralClosure.MulSemiringAction O E F (integralClosure O F)

omit [FiniteDimensional E F] in
theorem smul_coe (σ : Gal(F/E)) (b : integralClosure O F) :
    ((σ • b : integralClosure O F) : F) = σ (b : F) :=
  algebraMap_galRestrict_apply O σ b

scoped instance sccGalOB : SMulCommClass Gal(F/E) O (integralClosure O F) where
  smul_comm g a b := by
    have key : ∀ c : integralClosure O F, ((a • c : integralClosure O F) : F)
        = algebraMap E F (a : E) * (c : F) := fun c => by
      rw [Subalgebra.coe_smul, Algebra.smul_def, IsScalarTower.algebraMap_apply O E F]; rfl
    exact Subtype.ext <| by rw [smul_coe, key, key, smul_coe, map_mul, g.commutes]

scoped instance ifrBF : IsFractionRing (integralClosure O F) F :=
  integralClosure.isFractionRing_of_finite_extension E F

scoped instance invOBGal : Algebra.IsInvariant O (integralClosure O F) Gal(F/E) :=
  Algebra.isInvariant_of_isGalois O E F (integralClosure O F)

end galois

section center
variable (O : ValuationSubring E) (O' : ValuationSubring F)
  (hO : ∀ x : E, algebraMap E F x ∈ O' ↔ x ∈ O)

def inclBtoO' : integralClosure O F →+* O' where
  toFun b := ⟨b.1, (O'.valuation_le_one_iff _).mp (Prufer.val_le_one_of_isIntegral O O' hO b.2)⟩
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl

def centerQ : Ideal (integralClosure O F) :=
  (IsLocalRing.maximalIdeal O').comap (inclBtoO' O O' hO)

theorem mem_centerQ_iff (b : integralClosure O F) :
    b ∈ centerQ O O' hO ↔ O'.valuation (b : F) < 1 :=
  ValuationSubring.valuation_lt_one_iff O' _

scoped instance centerQ_isPrime : (centerQ O O' hO).IsPrime :=
  Ideal.IsPrime.comap (inclBtoO' O O' hO)

include hO in
theorem valO'_lt_one_iff (a : E) :
    O'.valuation (algebraMap E F a) < 1 ↔ O.valuation a < 1 := by
  simp only [← ValuationSubring.mem_nonunits_iff, ValuationSubring.mem_nonunits_iff_or,
    ← map_inv₀, hO, FaithfulSMul.algebraMap_eq_zero_iff]

scoped instance centerQ_liesOver : (centerQ O O' hO).LiesOver (IsLocalRing.maximalIdeal O) := by
  constructor
  ext a
  rw [Ideal.mem_under, mem_centerQ_iff]
  have hcoe : ((algebraMap O (integralClosure O F) a : integralClosure O F) : F)
      = algebraMap E F (a : E) := (IsScalarTower.algebraMap_apply O E F a :)
  rw [hcoe, valO'_lt_one_iff O O' hO]
  exact ValuationSubring.valuation_lt_one_iff O a

section galois
variable [FiniteDimensional E F] [IsGalois E F]

include hO in
omit [FiniteDimensional E F] [IsGalois E F] in
theorem smul_O'_over (σ : Gal(F/E)) : ∀ x : E, algebraMap E F x ∈ σ • O' ↔ x ∈ O := by
  intro x
  rw [ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem,
    show (σ⁻¹ : Gal(F/E)) • algebraMap E F x = algebraMap E F x from (σ⁻¹).commutes x]
  exact hO x

omit [FiniteDimensional E F] in
theorem val_smul_lt_one_iff (σ : Gal(F/E)) (b : integralClosure O F) :
    (σ • O').valuation (b : F) < 1 ↔ σ⁻¹ • b ∈ centerQ O O' hO := by
  rw [mem_centerQ_iff, smul_coe, ← ValuationSubring.mem_nonunits_iff,
    ← ValuationSubring.mem_nonunits_iff, ValuationSubring.mem_nonunits_iff_or,
    ValuationSubring.mem_nonunits_iff_or]
  refine or_congr ?_ (not_congr ?_)
  · exact ⟨fun h => by rw [h, map_zero], fun h => σ⁻¹.injective (by rwa [map_zero])⟩
  · rw [ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem,
      show (σ⁻¹ : Gal(F/E)) • ((↑b : F)⁻¹) = (σ⁻¹ : Gal(F/E)) ((↑b : F)⁻¹) from rfl,
      map_inv₀]

omit [FiniteDimensional E F] in
theorem smul_eq_of_center_eq (O'' : ValuationSubring F)
    (hO'' : ∀ x : E, algebraMap E F x ∈ O'' ↔ x ∈ O) (σ : Gal(F/E))
    (hσ : centerQ O O'' hO'' = σ • centerQ O O' hO) : σ • O' = O'' := by
  refine (mem_iff_exists_integralClosure_valuation_eq_one_mul_eq_of_isAlgebraic O O'' hO'').2
    (σ • O') (smul_O'_over O O' hO σ) ?_
  intro b
  rw [← mem_centerQ_iff O O'' hO'', val_smul_lt_one_iff O O' hO σ b, hσ,
    Ideal.mem_pointwise_smul_iff_inv_smul_mem]

include hO in
/-- Finite Galois prolongation conjugacy from the original source proof. -/
theorem exists_algEquiv
    (O'' : ValuationSubring F) (hO'' : ∀ x : E, algebraMap E F x ∈ O'' ↔ x ∈ O) :
    ∃ σ : F ≃ₐ[E] F, ∀ x : F, σ x ∈ O'' ↔ x ∈ O' := by
  have hunder : (centerQ O O' hO).under O = (centerQ O O'' hO'').under O := by
    rw [← Ideal.over_def _ (IsLocalRing.maximalIdeal O),
      ← Ideal.over_def _ (IsLocalRing.maximalIdeal O)]
  obtain ⟨σ, hσ⟩ := Algebra.IsInvariant.exists_smul_of_under_eq O (integralClosure O F)
    Gal(F/E) (centerQ O O' hO) (centerQ O O'' hO'') hunder
  have hOeq : σ • O' = O'' := smul_eq_of_center_eq O O' hO O'' hO'' σ hσ
  exact ⟨σ, fun x => by
    rw [← hOeq, show σ x = σ • x from rfl, ValuationSubring.smul_mem_pointwise_smul_iff]⟩

end galois
end center
end FiniteConjugacy

/-- Exact finite source conjugacy signature; no DVR or henselian hypothesis. -/
theorem exists_algEquiv_forall_mem_iff_of_isGalois
    {E F : Type*} [Field E] [Field F] [Algebra E F] [FiniteDimensional E F] [IsGalois E F]
    (O : ValuationSubring E) (O' O'' : ValuationSubring F)
    (hO : ∀ x : E, algebraMap E F x ∈ O' ↔ x ∈ O)
    (hO'' : ∀ x : E, algebraMap E F x ∈ O'' ↔ x ∈ O) :
    ∃ σ : F ≃ₐ[E] F, ∀ x : F, σ x ∈ O'' ↔ x ∈ O' :=
  FiniteConjugacy.exists_algEquiv O O' hO O'' hO''

namespace InfiniteConjugacy

open scoped Topology Pointwise

variable {E F : Type*} [Field E] [Field F] [Algebra E F]

theorem isClosed_of_mul_mem_iff (H : Subgroup (F ≃ₐ[E] F)) (hH : IsOpen (H : Set (F ≃ₐ[E] F)))
    (D : Set (F ≃ₐ[E] F)) (hD : ∀ σ : F ≃ₐ[E] F, ∀ h ∈ H, σ * h ∈ D ↔ σ ∈ D) : IsClosed D := by
  rw [← isOpen_compl_iff, isOpen_iff_forall_mem_open]
  intro σ hσ
  refine ⟨(fun h => σ * h) '' (H : Set (F ≃ₐ[E] F)), ?_, isOpenMap_mul_left σ _ hH,
    ⟨1, H.one_mem, mul_one σ⟩⟩
  rintro _ ⟨h, hh, rfl⟩ hmem
  exact hσ ((hD σ h hh).mp hmem)

variable (O' O'' : ValuationSubring F)

def transportAt (x : F) : Set (F ≃ₐ[E] F) := {σ | σ x ∈ O'' ↔ x ∈ O'}

theorem isClosed_transportAt [Algebra.IsAlgebraic E F] (x : F) :
    IsClosed (transportAt (E := E) O' O'' x) := by
  haveI : FiniteDimensional E (IntermediateField.adjoin E {x}) :=
    IntermediateField.adjoin.finiteDimensional (Algebra.IsIntegral.isIntegral x)
  refine isClosed_of_mul_mem_iff (IntermediateField.adjoin E {x}).fixingSubgroup
    (IntermediateField.fixingSubgroup_isOpen _) _ fun σ h hh => ?_
  have hx : h x = x := (IntermediateField.mem_fixingSubgroup_iff _ _).mp hh x
    (IntermediateField.mem_adjoin_simple_self E x)
  simp only [transportAt, Set.mem_setOf_eq, AlgEquiv.mul_apply, hx]

theorem nonempty_iInter_transportAt [IsGalois E F] (O : ValuationSubring E)
    (hO : ∀ x : E, algebraMap E F x ∈ O' ↔ x ∈ O)
    (hO'' : ∀ x : E, algebraMap E F x ∈ O'' ↔ x ∈ O) (s : Finset F) :
    (⋂ x ∈ s, transportAt (E := E) O' O'' x).Nonempty := by
  classical
  let L := (FiniteGaloisIntermediateField.adjoin E (↑s : Set F)).toIntermediateField
  have hsL : (↑s : Set F) ⊆ L := FiniteGaloisIntermediateField.subset_adjoin E (↑s : Set F)
  obtain ⟨τ, hτ⟩ := exists_algEquiv_forall_mem_iff_of_isGalois (E := E) (F := L) O
    (O'.comap (algebraMap L F)) (O''.comap (algebraMap L F))
    (fun x => by rw [ValuationSubring.mem_comap, ← IsScalarTower.algebraMap_apply]; exact hO x)
    (fun x => by rw [ValuationSubring.mem_comap, ← IsScalarTower.algebraMap_apply]; exact hO'' x)
  refine ⟨τ.liftNormal F, Set.mem_iInter₂.mpr fun x hx => ?_⟩
  have hxL : x ∈ L := hsL (Finset.mem_coe.mpr hx)
  have h1 : τ.liftNormal F x = algebraMap L F (τ ⟨x, hxL⟩) := by
    simpa using AlgEquiv.liftNormal_commutes τ F ⟨x, hxL⟩
  show τ.liftNormal F x ∈ O'' ↔ x ∈ O'
  rw [h1]
  simpa [ValuationSubring.mem_comap] using hτ ⟨x, hxL⟩

end InfiniteConjugacy

open InfiniteConjugacy in
/-- Infinite Galois prolongation conjugacy, with the exact unrestricted Type* source type. -/
theorem exists_algEquiv_forall_mem_iff_of_isGalois_infinite
    {E F : Type*} [Field E] [Field F] [Algebra E F] [IsGalois E F]
    (O : ValuationSubring E) (O' O'' : ValuationSubring F)
    (hO : ∀ x : E, algebraMap E F x ∈ O' ↔ x ∈ O)
    (hO'' : ∀ x : E, algebraMap E F x ∈ O'' ↔ x ∈ O) :
    ∃ σ : F ≃ₐ[E] F, ∀ x : F, σ x ∈ O'' ↔ x ∈ O' := by
  classical
  let t : Finset F → Set (F ≃ₐ[E] F) := fun s => ⋂ x ∈ s, transportAt (E := E) O' O'' x
  have hdir : Directed (fun a b => a ⊇ b) t := by
    intro s s'
    refine ⟨s ∪ s', ?_, ?_⟩ <;>
      exact Set.biInter_subset_biInter_left (by intro x hx; simp_all)
  have hne : ∀ s, (t s).Nonempty := nonempty_iInter_transportAt O' O'' O hO hO''
  have hclosed : ∀ s, IsClosed (t s) := fun s =>
    isClosed_biInter fun x _ => isClosed_transportAt O' O'' x
  have hcompact : ∀ s, IsCompact (t s) := fun s => (hclosed s).isCompact
  obtain ⟨σ, hσ⟩ := IsCompact.nonempty_iInter_of_directed_nonempty_isCompact_isClosed t hdir hne
    hcompact hclosed
  refine ⟨σ, fun x => ?_⟩
  have := Set.mem_iInter.mp hσ {x}
  simpa [t, transportAt] using this

end ZInQ.Contrib.CloudR2NOS.Valuation
