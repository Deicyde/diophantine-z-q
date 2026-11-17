/-
Copyright (c) 2026 H5 Round-2 Lane2 contributors.
Released under Apache 2.0 license as described in the source LICENSE.

New proofs assembled from the pinned Mathlib separable-closure, normal-lift and
purely-inseparable power lemmas, and the source conjugacy port in Conjugacy.lean.
The ambient extension is never declared Galois. In the target specialization it
remains exactly AlgebraicClosure K; only its separable intermediate field is Galois.
No PerfectField, CharZero, henselianity, valuation discreteness upstairs, or
restriction on the torsion order is introduced.
-/
import ZInQKernel.Contrib.CloudR2NOS.Valuation.Basic
import ZInQKernel.Contrib.CloudR2NOS.Valuation.Conjugacy

set_option autoImplicit false
noncomputable section

namespace ZInQ.Contrib.CloudR2NOS.Valuation

open scoped Pointwise

variable {K L : Type*} [Field K] [Field L] [Algebra K L]

/-- Restriction is injective across a purely inseparable extension, by power saturation. -/
theorem comap_injective_of_isPurelyInseparable [IsPurelyInseparable K L] :
    Function.Injective (fun V : ValuationSubring L => V.comap (algebraMap K L)) := by
  intro V W h
  change V.comap (algebraMap K L) = W.comap (algebraMap K L) at h
  ext x
  obtain ⟨n, y, hy⟩ := IsPurelyInseparable.pow_mem K (ringExpChar K) x
  have hn : 0 < ringExpChar K ^ n := expChar_pow_pos K _ n
  calc
    x ∈ V ↔ x ^ ringExpChar K ^ n ∈ V := (pow_mem_iff V x hn).symm
    _ ↔ algebraMap K L y ∈ V := by rw [hy]
    _ ↔ y ∈ V.comap (algebraMap K L) := Iff.rfl
    _ ↔ y ∈ W.comap (algebraMap K L) := by rw [h]
    _ ↔ algebraMap K L y ∈ W := Iff.rfl
    _ ↔ x ^ ringExpChar K ^ n ∈ W := by rw [hy]
    _ ↔ x ∈ W := pow_mem_iff W x hn

/-- Two prolongations to an arbitrary normal extension are conjugate, even over imperfect K. -/
theorem exists_algEquiv_forall_mem_iff_of_normal [Normal K L]
    (O : ValuationSubring K) (V W : ValuationSubring L)
    (hV : ∀ x : K, algebraMap K L x ∈ V ↔ x ∈ O)
    (hW : ∀ x : K, algebraMap K L x ∈ W ↔ x ∈ O) :
    ∃ g : L ≃ₐ[K] L, ∀ x : L, g x ∈ W ↔ x ∈ V := by
  classical
  let S := separableClosure K L
  haveI : Normal K S := IntermediateField.normal_iff_normalClosure_eq.mpr
    (separableClosure.normalClosure_eq_self K L)
  haveI : IsGalois K S := isGalois_iff.mpr ⟨inferInstance, inferInstance⟩
  haveI : IsPurelyInseparable S L := separableClosure.isPurelyInseparable K L
  obtain ⟨τ, hτ⟩ := exists_algEquiv_forall_mem_iff_of_isGalois_infinite (E := K) (F := S) O
    (V.comap (algebraMap S L)) (W.comap (algebraMap S L))
    (fun x => by rw [ValuationSubring.mem_comap, ← IsScalarTower.algebraMap_apply]; exact hV x)
    (fun x => by rw [ValuationSubring.mem_comap, ← IsScalarTower.algebraMap_apply]; exact hW x)
  refine ⟨τ.liftNormal L, fun x => ?_⟩
  obtain ⟨n, y, hy⟩ := IsPurelyInseparable.pow_mem S (ringExpChar S) x
  have hn : 0 < ringExpChar S ^ n := expChar_pow_pos S _ n
  have hpow : (τ.liftNormal L x) ^ ringExpChar S ^ n = algebraMap S L (τ y) := by
    rw [← map_pow, ← hy, AlgEquiv.liftNormal_commutes]
  calc
    τ.liftNormal L x ∈ W ↔ (τ.liftNormal L x) ^ ringExpChar S ^ n ∈ W :=
      (pow_mem_iff W _ hn).symm
    _ ↔ algebraMap S L (τ y) ∈ W := by rw [hpow]
    _ ↔ τ y ∈ W.comap (algebraMap S L) := Iff.rfl
    _ ↔ y ∈ V.comap (algebraMap S L) := hτ y
    _ ↔ algebraMap S L y ∈ V := Iff.rfl
    _ ↔ x ^ ringExpChar S ^ n ∈ V := by rw [hy]
    _ ↔ x ∈ V := pow_mem_iff V x hn

/-- Convert the source's membership orientation to literal pointwise-scalar equality. -/
theorem smul_eq_of_forall_apply_mem_iff (V W : ValuationSubring L) (g : L ≃ₐ[K] L)
    (h : ∀ x : L, g x ∈ W ↔ x ∈ V) : g • V = W := by
  ext x
  rw [ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem, AlgEquiv.smul_def]
  have hcancel : g (g⁻¹ x) = x := by
    rw [← AlgEquiv.mul_apply, mul_inv_cancel, AlgEquiv.one_apply]
  simpa only [hcancel] using (h (g⁻¹ x)).symm

/-- Normal-extension prolongation conjugacy, phrased directly by equal restrictions. -/
theorem exists_smul_eq_of_comap_eq [Normal K L] (V W : ValuationSubring L)
    (h : V.comap (algebraMap K L) = W.comap (algebraMap K L)) :
    ∃ g : L ≃ₐ[K] L, g • V = W := by
  obtain ⟨g, hg⟩ := exists_algEquiv_forall_mem_iff_of_normal
    (W.comap (algebraMap K L)) V W
    (fun x => by change x ∈ V.comap (algebraMap K L) ↔ _; rw [h])
    (fun _ => Iff.rfl)
  exact ⟨g, smul_eq_of_forall_apply_mem_iff V W g hg⟩

/-- The target's same algebraic closure, with no perfectness or Galois assumption on Kbar/K. -/
theorem exists_smul_eq_on_algebraicClosure (O : ValuationSubring K)
    (V W : ValuationSubring (AlgebraicClosure K))
    (hV : V.comap (algebraMap K (AlgebraicClosure K)) = O)
    (hW : W.comap (algebraMap K (AlgebraicClosure K)) = O) :
    ∃ g : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K, g • V = W :=
  exists_smul_eq_of_comap_eq V W (hV.trans hW.symm)

end ZInQ.Contrib.CloudR2NOS.Valuation
