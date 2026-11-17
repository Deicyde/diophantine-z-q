/-
Ported with Codex assistance on 2026-11-14 from trureturing@8af78b5bb176c99b2750222c0dd3d00a475d39eb.
Source: D5/S3/Factorization/Dedekind/HilbertDifferent/NumberTheory/NumberField/LocalGlobal/RamificationGroup.lean
Original SHA-256: 78857b0ef73830c901c9cbd511268405b054f975da751a807c5f41f8352016be
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
TauCeti/NumberTheory/NumberField/LocalGlobal/RamificationGroup.lean.
Full license and pertinent inherited attribution: ZInQKernel/Contrib/HilbertDifferent/Attribution.lean.
Replace this port by direct use when this project's pinned Mathlib supplies an equivalent declaration. -/


import ZInQKernel.Contrib.HilbertDifferent.NumberTheory.LocalField.RamificationGroup
import ZInQKernel.Contrib.HilbertDifferent.NumberTheory.NumberField.LocalGlobal.DecompositionGroup
import ZInQKernel.Contrib.HilbertDifferent.RingTheory.Ideal.RamificationGroup
import ZInQKernel.Contrib.HilbertDifferent.Support.TameDifferent

noncomputable section

section
noncomputable section

open IsDedekindDomain NumberField ValuativeRel WithZero
open scoped NumberField Pointwise AdicCompletionExtension

namespace IsDedekindDomain.HeightOneSpectrum

variable {K L : Type*} [Field K] [Field L] [NumberField K] [NumberField L] [Algebra K L]
  (v : HeightOneSpectrum (𝓞 K)) {w : HeightOneSpectrum (𝓞 L)} [w.asIdeal.LiesOver v.asIdeal]

/- **The global and local ramification groups agree.** An element `σ` of the decomposition group
of `w` lies in the `i`-th ramification group of the prime `w` of `𝓞 L` exactly when its continuous
extension to `L_w` lies in the `i`-th lower-numbering ramification group of `L_w/K_v`. -/
theorem mem_ramificationGroup_iff_decompositionHom_mem (i : ℕ)
    (σ : MulAction.stabilizer (L ≃ₐ[K] L) w.asIdeal) :
    (σ : L ≃ₐ[K] L) ∈ w.asIdeal.ramificationGroup (L ≃ₐ[K] L) i ↔
      decompositionHom v w σ ∈ TauCeti.LocalFieldsRamification.lowerRamificationGroup
        (v.adicCompletion K) (w.adicCompletion L) i := by
  rw [Ideal.mem_ramificationGroup_iff,
    TauCeti.LocalFieldsRamification.lowerRamificationGroup_def,
    TauCeti.IsLocalRing.mem_ramificationGroup_natCast_iff]
  simp_rw [mem_maximalIdeal_integer_pow_iff, w.mem_asIdeal_pow_iff_valued_algebraMap_le (K := L),
    map_sub, AddSubgroupClass.coe_sub, AlgEquiv.coe_smul_integerRing]
  refine ⟨fun h y ↦ ?_, fun h x ↦ ?_⟩
  · -- approximate `y` by an element `a` of `𝓞 L` modulo the `(i + 1)`-st power of the maximal
    -- ideal; the action moves `y - a` by no more than that power, and moves `a` by `h`
    obtain ⟨a, ha⟩ := w.exists_valued_sub_le (K := L)
      (w.integerEquivAdicCompletionIntegers (K := L) y) (i + 1)
    rw [coe_integerEquivAdicCompletionIntegers] at ha
    have hσa : Valued.v (decompositionHom v w σ (algebraMap (𝓞 L) (w.adicCompletion L) a) -
        algebraMap (𝓞 L) (w.adicCompletion L) a) ≤ exp (-((i + 1 : ℕ) : ℤ)) := by
      rw [decompositionHom_algebraMap_ringOfIntegers]
      exact h a
    have hσya : Valued.v (decompositionHom v w σ
        ((y : w.adicCompletion L) - algebraMap (𝓞 L) (w.adicCompletion L) a)) ≤
          exp (-((i + 1 : ℕ) : ℤ)) := by
      rwa [valued_decompositionHom]
    rw [map_sub] at hσya
    have hsplit : decompositionHom v w σ (y : w.adicCompletion L) - y =
        (decompositionHom v w σ y - decompositionHom v w σ (algebraMap (𝓞 L) _ a)) +
          (decompositionHom v w σ (algebraMap (𝓞 L) _ a) - algebraMap (𝓞 L) _ a) -
            (y - algebraMap (𝓞 L) (w.adicCompletion L) a) := by
      ring
    rw [hsplit]
    exact Valuation.map_sub_le _ (Valuation.map_add_le _ hσya hσa) ha
  · have hx : Valued.v (decompositionHom v w σ (algebraMap (𝓞 L) (w.adicCompletion L) x) -
        algebraMap (𝓞 L) (w.adicCompletion L) x) ≤ exp (-((i + 1 : ℕ) : ℤ)) :=
      h ⟨_, algebraMap_mem_integer_adicCompletion w x⟩
    rwa [decompositionHom_algebraMap_ringOfIntegers] at hx

/- **The global ramification groups are the local ones, pulled back along `decompositionHom`.**
Inside the decomposition group of `w`, the `i`-th ramification group of `w` is the preimage of the
`i`-th lower-numbering ramification group of `L_w/K_v`. -/
theorem ramificationGroup_stabilizer_eq_comap_decompositionHom (i : ℕ) :
    w.asIdeal.ramificationGroup (MulAction.stabilizer (L ≃ₐ[K] L) w.asIdeal) i =
      (TauCeti.LocalFieldsRamification.lowerRamificationGroup
        (v.adicCompletion K) (w.adicCompletion L) i).comap (decompositionHom v w) := by
  ext σ
  rw [← Ideal.ramificationGroup_subgroupOf, Subgroup.mem_subgroupOf, Subgroup.mem_comap,
    mem_ramificationGroup_iff_decompositionHom_mem v]

variable [IsGalois K L]

variable (w) in
/- **The decomposition group carries the global ramification groups onto the local ones.** For
`L/K` Galois, the image of the `i`-th ramification group of `w` in `Aut(L_w/K_v)` is the `i`-th
lower-numbering ramification group of `L_w/K_v`. -/
theorem map_ramificationGroup_decompositionHom (i : ℕ) :
    (w.asIdeal.ramificationGroup (MulAction.stabilizer (L ≃ₐ[K] L) w.asIdeal) i).map
        (decompositionHom v w) =
      TauCeti.LocalFieldsRamification.lowerRamificationGroup
        (v.adicCompletion K) (w.adicCompletion L) i := by
  rw [ramificationGroup_stabilizer_eq_comap_decompositionHom v]
  exact Subgroup.map_comap_eq_self_of_surjective (decompositionHom_surjective v w) _

variable (w) in
/- **The global and local ramification groups have the same order.** For `L/K` Galois, the
`i`-th ramification group of `w` has as many elements as the `i`-th lower-numbering ramification
group of `L_w/K_v`. -/
theorem card_ramificationGroup_eq_card_lowerRamificationGroup (i : ℕ) :
    Nat.card (w.asIdeal.ramificationGroup (L ≃ₐ[K] L) i) =
      Nat.card (TauCeti.LocalFieldsRamification.lowerRamificationGroup
        (v.adicCompletion K) (w.adicCompletion L) i) := by
  rw [← map_ramificationGroup_decompositionHom v w i, ← Ideal.ramificationGroup_subgroupOf]
  exact Nat.card_congr ((Subgroup.subgroupOfEquivOfLe
    (w.asIdeal.ramificationGroup_le_stabilizer i)).symm.trans
      (Subgroup.equivMapOfInjective _ _ (decompositionHom_injective v w))).toEquiv

end IsDedekindDomain.HeightOneSpectrum
