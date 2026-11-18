import FrobLift.WildInertiaV001
import FrobLift.ResidueGaloisV004

/-!
# Corollaries: Frobenius lifts modulo inertia, powers, and the residue field of `w`

* Two Frobenius lifts differ by an inertia element (`isInertia_mul_inv_of_frobenius`).
* For a Frobenius lift `φ` and `r : ℕ`, `ψ = φ^r` satisfies the tame relation with exponent `q^r`
  and `(ψ τ ψ⁻¹)⁻¹ τ^(q^r)` is a genuine wild inertia element (`tame_relation_pow`).
* The residue field of `w` is algebraically closed (`isAlgClosed_residueField`).
-/

noncomputable section

namespace FrobLift

open Polynomial

variable {K : Type} [Field K] [NumberField K] {O : ValuationSubring K} [IsDiscreteValuationRing O]
  {Ω : Type} [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω] {w : ValuationSubring Ω}

omit [NumberField K] [IsAlgClosure K Ω] in
/-- **Frobenius lifts are unique modulo inertia.** -/
theorem isInertia_mul_inv_of_frobenius {φ₁ φ₂ : Ω ≃ₐ[K] Ω} (h1 : φ₁ ∈ w.decompositionSubgroup K)
    (h2 : φ₂ ∈ w.decompositionSubgroup K) {q : ℕ}
    (c1 : ∀ x ∈ w, w.valuation (φ₁ x - x ^ q) < 1) (c2 : ∀ x ∈ w, w.valuation (φ₂ x - x ^ q) < 1) :
    PkgI2.IsInertia w (φ₁ * φ₂⁻¹) := by
  refine ⟨mul_mem h1 (inv_mem h2), ?_⟩
  show MulSemiringAction.toRingAut _ _ _ = 1
  ext r
  obtain ⟨x, rfl⟩ := IsLocalRing.residue_surjective r
  show (⟨φ₁ * φ₂⁻¹, mul_mem h1 (inv_mem h2)⟩ : w.decompositionSubgroup K) •
    IsLocalRing.residue w x = IsLocalRing.residue w x
  rw [← IsLocalRing.ResidueField.residue_smul, ← sub_eq_zero, ← map_sub,
    IsLocalRing.residue_eq_zero_iff, ValuationSubring.valuation_lt_one_iff]
  show w.valuation ((φ₁ * φ₂⁻¹) (x : Ω) - x) < 1
  set y := φ₂⁻¹ (x : Ω) with hy
  have hyw : y ∈ w := (mem_iff_of_decomp (inv_mem h2) x).2 x.2
  have hφy : φ₂ y = x := by
    rw [hy, ← AlgEquiv.mul_apply, mul_inv_cancel, AlgEquiv.one_apply]
  have e : (φ₁ * φ₂⁻¹) (x : Ω) - x = (φ₁ y - y ^ q) - (φ₂ y - y ^ q) := by
    rw [AlgEquiv.mul_apply, ← hy, hφy]
    ring
  rw [e]
  exact Valuation.map_sub_lt _ (c1 y hyw) (c2 y hyw)

/-- **Powers of a Frobenius lift satisfy the tame relation with exponent `q^r`**, and produce
genuine wild inertia elements. -/
theorem tame_relation_pow {φ : Ω ≃ₐ[K] Ω} (hD : φ ∈ w.decompositionSubgroup K) {q : ℕ}
    (hcong : ∀ x ∈ w, w.valuation (φ x - x ^ q) < 1) (r : ℕ) (τ : Ω ≃ₐ[K] Ω)
    (hτ : PkgI2.IsInertia w τ) :
    PkgI2.IsInertia w ((φ ^ r * τ * (φ ^ r)⁻¹)⁻¹ * τ ^ (q ^ r)) ∧
      ∀ x : Ω, x ≠ 0 →
        w.valuation (((φ ^ r * τ * (φ ^ r)⁻¹)⁻¹ * τ ^ (q ^ r)) x - x) < w.valuation x :=
  ⟨isInertia_frob_conj (pow_mem hD r) hτ _,
    tame_relation_of_frobenius (pow_mem hD r) (pow_congr hD hcong r) τ hτ⟩

/-- **The residue field of a valuation subring of an algebraically closed field is algebraically
closed** (in particular for `w ⊆ Ω = K̄`, via `IsAlgClosure.isAlgClosed K`). -/
theorem isAlgClosed_residueField {L : Type} [Field L] [IsAlgClosed L] (w : ValuationSubring L) :
    IsAlgClosed (IsLocalRing.ResidueField w) := by
  refine IsAlgClosed.of_exists_root _ fun p hmon hirr => ?_
  have hlift : p ∈ Polynomial.lifts (IsLocalRing.residue w) :=
    Polynomial.lifts_iff_coeff_lifts _ |>.mpr fun n => IsLocalRing.residue_surjective _
  obtain ⟨P, hPmap, hPdeg, hPmon⟩ :=
    Polynomial.lifts_and_natDegree_eq_and_monic hlift hmon
  have hinj : Function.Injective (algebraMap w L) := fun a b h => Subtype.ext h
  have hdeg : (P.map (algebraMap w L)).degree ≠ 0 := by
    rw [Polynomial.degree_map_eq_of_injective hinj, Polynomial.degree_eq_natDegree hPmon.ne_zero,
      hPdeg]
    have := Irreducible.natDegree_pos hirr
    exact_mod_cast this.ne'
  obtain ⟨z, hz⟩ := IsAlgClosed.exists_root (P.map (algebraMap w L)) hdeg
  have hzint : IsIntegral w z := ⟨P, hPmon, by rwa [Polynomial.IsRoot, Polynomial.eval_map] at hz⟩
  obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.mp hzint
  refine ⟨IsLocalRing.residue w y, ?_⟩
  rw [← hPmap, Polynomial.eval_map, Polynomial.eval₂_hom]
  have h0 : Polynomial.eval y P = 0 := by
    apply hinj
    have e : algebraMap w L (Polynomial.eval y P) = Polynomial.eval z (P.map (algebraMap w L)) := by
      rw [Polynomial.eval_map, ← hy, Polynomial.eval₂_hom]
    rw [e, map_zero]
    exact hz
  rw [h0, map_zero]

end FrobLift
