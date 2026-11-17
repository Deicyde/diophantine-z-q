/-
Ported with Codex assistance on 2026-11-14 from trureturing@8af78b5bb176c99b2750222c0dd3d00a475d39eb.
Source: D5/S3/Factorization/Dedekind/HilbertDifferent/NumberTheory/NumberField/LocalGlobal/DecompositionGroup.lean
Original SHA-256: daf819ddf18eb4dbe963a74754f96807eb292a7c0bf6830cb6faeb130095f884
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
TauCeti/NumberTheory/NumberField/LocalGlobal/DecompositionGroup.lean.
Full license and pertinent inherited attribution: ZInQKernel/Contrib/HilbertDifferent/Attribution.lean.
Replace this port by direct use when this project's pinned Mathlib supplies an equivalent declaration. -/


import ZInQKernel.Contrib.HilbertDifferent.NumberTheory.NumberField.AutomorphismAction
import ZInQKernel.Contrib.HilbertDifferent.NumberTheory.NumberField.LocalGlobal.Completion
import ZInQKernel.Contrib.HilbertDifferent.NumberTheory.RamificationInertia.SeparableDegree
import ZInQKernel.Contrib.HilbertDifferent.RingTheory.DedekindDomain.AdicValuation.LocalDegree
import ZInQKernel.Contrib.HilbertDifferent.RingTheory.DedekindDomain.AdicValuation.Transport
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.NumberTheory.NumberField.Ideal.Basic
import Mathlib.RingTheory.Frobenius
import ZInQKernel.Contrib.HilbertDifferent.Support.TameDifferent
import Mathlib.NumberTheory.LegendreSymbol.Basic
import Mathlib.RingTheory.Ideal.Int
import Mathlib.RingTheory.Ideal.Over
import Mathlib.RingTheory.Ideal.Span
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.FieldTheory.KummerPolynomial
import Mathlib.Algebra.CharP.Basic
import Mathlib.NumberTheory.RamificationInertia.Galois
import Mathlib.RingTheory.Unramified.Locus
import Mathlib.RingTheory.Localization.Basic

noncomputable section

section
noncomputable section

open IsDedekindDomain Module NumberField
open scoped NumberField Pointwise AdicCompletionExtension

namespace IsDedekindDomain.HeightOneSpectrum

local notation "𝒪" => _root_.NumberField.RingOfIntegers

variable {K L : Type*} [Field K] [Field L] [NumberField L] [Algebra K L]

/- An automorphism `σ` of `L/K` carries the `w`-adic valuation to the `w'`-adic valuation
when `w' = σ • w`. -/
theorem valuation_apply_eq_of_asIdeal_eq_smul (σ : L ≃ₐ[K] L)
    {w w' : HeightOneSpectrum (𝒪 L)} (h : w'.asIdeal = σ • w.asIdeal) (x : L) :
    w'.valuation L (σ x) = w.valuation L x := by
  let e := MulSemiringAction.toRingEquiv (L ≃ₐ[K] L) (𝒪 L) σ
  have hσ : (IsFractionRing.ringEquivOfRingEquiv e : L ≃+* L) = σ.toRingEquiv := by
    apply RingEquiv.toRingHom_injective
    refine IsLocalization.ringHom_ext (nonZeroDivisors (𝒪 L)) (S := L) (RingHom.ext fun r ↦ ?_)
    simp [e]
  have hw : w'.asIdeal = Ideal.map e w.asIdeal := by
    rw [h, Ideal.pointwise_smul_def]
    -- `e` and `MulSemiringAction.toRingHom _ _ σ` bundle the same map, as an equivalence and as
    -- a homomorphism respectively
    rfl
  rw [← valuation_ringEquivOfRingEquiv (K := L) (K' := L) e hw x, hσ, AlgEquiv.coe_toRingEquiv]

variable [NumberField K] (v : HeightOneSpectrum (𝒪 K))

/- The isomorphism of completions `L_w ≃ₐ[K_v] L_{w'}` induced by an automorphism `σ` of `L/K`
carrying `w` to `w'`: the continuous extension of `σ`. -/
def completionCongr (σ : L ≃ₐ[K] L) {w w' : HeightOneSpectrum (𝒪 L)}
    [w.asIdeal.LiesOver v.asIdeal] [w'.asIdeal.LiesOver v.asIdeal]
    (h : w'.asIdeal = σ • w.asIdeal) :
    w.adicCompletion L ≃ₐ[v.adicCompletion K] w'.adicCompletion L :=
  AlgEquiv.ofRingEquiv (f := adicCompletionCongr w w' σ.toRingEquiv
    (valuation_apply_eq_of_asIdeal_eq_smul σ h)) fun a ↦ by
    -- both sides are continuous in `a` and extend `K → L`, so they are the canonical map
    have := eq_completionAlgHom_of_continuous v w'
      ((adicCompletionCongr w w' σ.toRingEquiv
        (valuation_apply_eq_of_asIdeal_eq_smul σ h)).toRingHom.comp
          (completionAlgHom v w).toRingHom)
      ((continuous_adicCompletionCongr (valuation_apply_eq_of_asIdeal_eq_smul σ h)).comp (continuous_completionAlgHom v w)) fun x ↦ by
        simp [IsScalarTower.algebraMap_apply K L (w.adicCompletion L)]
    rw [algebraMap_eq_completionAlgHom, algebraMap_eq_completionAlgHom]
    exact congr($this a)

variable {v}

section completionCongr

variable {w w' : HeightOneSpectrum (𝒪 L)} [w.asIdeal.LiesOver v.asIdeal]
  [w'.asIdeal.LiesOver v.asIdeal]

/- `completionCongr v σ h` extends `σ`. -/
@[simp]
theorem completionCongr_algebraMap (σ : L ≃ₐ[K] L) (h : w'.asIdeal = σ • w.asIdeal) (x : L) :
    completionCongr v σ h (algebraMap L (w.adicCompletion L) x) =
      algebraMap L (w'.adicCompletion L) (σ x) := by
  rw [completionCongr, AlgEquiv.ofRingEquiv_apply, adicCompletionCongr_algebraMap,
    AlgEquiv.coe_toRingEquiv]

@[simp]
theorem valued_completionCongr (σ : L ≃ₐ[K] L) (h : w'.asIdeal = σ • w.asIdeal)
    (x : w.adicCompletion L) :
    Valued.v (completionCongr v σ h x) = Valued.v x :=
  valued_adicCompletionCongr (valuation_apply_eq_of_asIdeal_eq_smul σ h) x

/- `completionCongr` depends only on the automorphism, not on the proof that it carries `w`
to `w'`. -/
@[simp]
theorem completionCongr_one :
    completionCongr (w := w) (w' := w) v (1 : L ≃ₐ[K] L)
      (by simp) = AlgEquiv.refl :=
  AlgEquiv.toRingEquiv_injective adicCompletionCongr_one

/- `completionCongr` is multiplicative: transporting along `σ` and then along `τ` is
transporting along `τ * σ`. -/
@[simp]
theorem completionCongr_trans {w'' : HeightOneSpectrum (𝒪 L)} [w''.asIdeal.LiesOver v.asIdeal]
    (σ τ : L ≃ₐ[K] L) (hσ : w'.asIdeal = σ • w.asIdeal) (hτ : w''.asIdeal = τ • w'.asIdeal) :
    (completionCongr v σ hσ).trans (completionCongr v τ hτ) =
      completionCongr v (τ * σ) (by rw [hτ, hσ, mul_smul]) :=
  AlgEquiv.toRingEquiv_injective (adicCompletionCongr_trans (valuation_apply_eq_of_asIdeal_eq_smul σ hσ) w'' τ.toRingEquiv (valuation_apply_eq_of_asIdeal_eq_smul τ hτ))

/- The inverse of `completionCongr v σ h` is `completionCongr` of `σ⁻¹`. -/
end completionCongr

variable (v) (w : HeightOneSpectrum (𝒪 L)) [w.asIdeal.LiesOver v.asIdeal]

/- The action of the decomposition group of `w` on the completion `L_w`: each element of the
stabilizer of `w` extends by continuity to a `K_v`-algebra automorphism of `L_w`. -/
def decompositionHom :
    MulAction.stabilizer (L ≃ₐ[K] L) w.asIdeal →* (w.adicCompletion L ≃ₐ[v.adicCompletion K]
      w.adicCompletion L) where
  toFun τ := completionCongr v (τ : L ≃ₐ[K] L) (MulAction.mem_stabilizer_iff.mp τ.2).symm
  map_one' := completionCongr_one
  map_mul' σ τ := (completionCongr_trans (τ : L ≃ₐ[K] L) (σ : L ≃ₐ[K] L)
      (MulAction.mem_stabilizer_iff.mp τ.2).symm
      (MulAction.mem_stabilizer_iff.mp σ.2).symm).symm

variable {v w}

/- An element of the decomposition group acts on `L_w` by `completionCongr`. -/
theorem decompositionHom_apply (τ : MulAction.stabilizer (L ≃ₐ[K] L) w.asIdeal) :
    decompositionHom v w τ =
      completionCongr v (τ : L ≃ₐ[K] L) (MulAction.mem_stabilizer_iff.mp τ.2).symm :=
  (rfl)

/- The defining property of `decompositionHom`: on `L` it is the action of the automorphism. -/
@[simp]
theorem decompositionHom_algebraMap (τ : MulAction.stabilizer (L ≃ₐ[K] L) w.asIdeal) (x : L) :
    decompositionHom v w τ (algebraMap L (w.adicCompletion L) x) =
      algebraMap L (w.adicCompletion L) ((τ : L ≃ₐ[K] L) x) := by
  rw [decompositionHom_apply, completionCongr_algebraMap]

/- On the ring of integers of `L`, `decompositionHom` is the action of the automorphism. -/
theorem decompositionHom_algebraMap_ringOfIntegers
    (τ : MulAction.stabilizer (L ≃ₐ[K] L) w.asIdeal) (x : 𝒪 L) :
    decompositionHom v w τ (algebraMap (𝒪 L) (w.adicCompletion L) x) =
      algebraMap (𝒪 L) (w.adicCompletion L) ((τ : L ≃ₐ[K] L) • x) := by
  rw [IsScalarTower.algebraMap_apply (𝒪 L) L (w.adicCompletion L) x,
    IsScalarTower.algebraMap_apply (𝒪 L) L (w.adicCompletion L) (_ • x),
    decompositionHom_algebraMap, NumberField.algebraMap_smul_eq_apply]

/- The action of the decomposition group on `L_w` preserves the valuation of `L_w`. -/
@[simp]
theorem valued_decompositionHom (τ : MulAction.stabilizer (L ≃ₐ[K] L) w.asIdeal)
    (x : w.adicCompletion L) :
    Valued.v (decompositionHom v w τ x) = Valued.v x := by
  rw [decompositionHom_apply, valued_completionCongr]

variable (v w) in
/- The decomposition group of `w` acts faithfully on `L_w`. -/
theorem decompositionHom_injective : Function.Injective (decompositionHom v w) := by
  rw [injective_iff_map_eq_one]
  intro τ hτ
  ext x
  have := congr($hτ (algebraMap L (w.adicCompletion L) x))
  rw [decompositionHom_algebraMap, AlgEquiv.one_apply] at this
  exact (algebraMap L (w.adicCompletion L)).injective this

/- **Compatibility of `decompositionHom` with the action on places.** If `σ` carries `w` to
`w'` and `τ` stabilizes `w`, then the action of `σ τ σ⁻¹` on `L_{w'}` is the action of `τ` on
`L_w` transported along `completionCongr σ`. -/
section IsGalois

variable (v w) [IsGalois K L]

/- **The decomposition group of `w` has order the local degree.** For `L/K` Galois the
decomposition group of `w` has `e(w ∣ v) · f(w ∣ v)` elements, and that product is the degree
of `L_w` over `K_v`. -/
theorem card_stabilizer_eq_finrank_adicCompletion :
    Nat.card (MulAction.stabilizer (L ≃ₐ[K] L) w.asIdeal) =
      finrank (v.adicCompletion K) (w.adicCompletion L) := by
  have : Finite (𝒪 L ⧸ w.asIdeal) := Ring.HasFiniteQuotients.finiteQuotient w.ne_bot
  rw [finrank_adicCompletion v w,
    Ideal.card_stabilizer_eq_ramificationIdx_mul_inertiaDeg
      (R := 𝒪 K) (G := L ≃ₐ[K] L) w.asIdeal]

/- **The decomposition group of `w` exhausts `Aut(L_w/K_v)`.** For `L/K` Galois every
`K_v`-algebra automorphism of `L_w` is the continuous extension of an automorphism of `L/K`
stabilizing `w`. -/
-- The decomposition group has `[L_w : K_v]` elements and a finite extension of fields has at
-- most that many automorphisms, so the injection of the previous lemma is already onto.
theorem decompositionHom_surjective : Function.Surjective (decompositionHom v w) := by
  refine ((Nat.bijective_iff_injective_and_card (decompositionHom v w)).mpr
    ⟨decompositionHom_injective v w, le_antisymm ?_ ?_⟩).surjective
  · exact Nat.card_le_card_of_injective _ (decompositionHom_injective v w)
  · rw [card_stabilizer_eq_finrank_adicCompletion v w]
    exact Nat.card_eq_fintype_card.trans_le AlgEquiv.card_le

/- **The decomposition group of `w` is the Galois group of `L_w/K_v`.** -/
def decompositionEquiv :
    MulAction.stabilizer (L ≃ₐ[K] L) w.asIdeal ≃*
      (w.adicCompletion L ≃ₐ[v.adicCompletion K] w.adicCompletion L) :=
  MulEquiv.ofBijective (decompositionHom v w)
    ⟨decompositionHom_injective v w, decompositionHom_surjective v w⟩

theorem isGalois_adicCompletion : IsGalois (v.adicCompletion K) (w.adicCompletion L) :=
  IsGalois.of_card_aut_eq_finrank _ _
    ((Nat.card_congr (decompositionEquiv v w).toEquiv).symm.trans
      (card_stabilizer_eq_finrank_adicCompletion v w))

scoped[AdicCompletionExtension] attribute [instance]
  IsDedekindDomain.HeightOneSpectrum.isGalois_adicCompletion

end IsGalois

section IsGaloisAdicCompletion

variable (v w) [IsGalois (v.adicCompletion K) (w.adicCompletion L)]

/- **The local Galois group at `w` has order `e(w ∣ v) · f(w ∣ v)`.** -/
end IsGaloisAdicCompletion

/-! ### The local Galois group at an unramified place -/

section IsUnramifiedAt

variable (v w) [IsGalois (v.adicCompletion K) (w.adicCompletion L)]
  [Algebra.IsUnramifiedAt (𝒪 K) w.asIdeal]

/- **The local Galois group at an unramified place has order `f(w ∣ v)`.** -/
end IsUnramifiedAt

section IsGaloisUnramifiedAt

variable (v w) [IsGalois K L] [Algebra.IsUnramifiedAt (𝒪 K) w.asIdeal]

/- **The local Galois group at an unramified place is cyclic.** -/
-- It is the image of the decomposition group of `w`, which an arithmetic Frobenius generates.
end IsGaloisUnramifiedAt

end IsDedekindDomain.HeightOneSpectrum
