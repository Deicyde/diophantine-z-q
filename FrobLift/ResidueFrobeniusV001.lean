import FrobLift.ResidueGaloisV004

/-!
# The residue Frobenius as an automorphism, with its `q^r`-power law

For a Frobenius lift `σ` (an element of the decomposition group of `w` with
`σ x ≡ x^q (mod 𝔪_w)` on `w`) and every `r : ℕ`:

* on the residue field `k_w`, the residue action of `σ^r` (Mathlib's
  `MulSemiringAction.toRingAut` of the decomposition group, whose kernel is `inertiaSubgroup`) is
  `t ↦ t^(q^r)` (`residue_toRingAut_pow_apply`);
* on `B/Q` (`B` the integral closure of `O`, `Q = 𝔪_w ∩ B`), the `O/𝔪_O`-algebra automorphism
  `Ideal.Quotient.stabilizerHom` of `σ^r` is `y ↦ y^(q^r)` (`stabilizerHom_frob_pow_apply`);
* the isomorphism `resB : B/Q ≅ k_w` intertwines the two actions (`resB_stabilizerHom`).
-/

noncomputable section

namespace FrobLift

open scoped Pointwise

attribute [local instance] primeQ_liesOver

section General

variable {K : Type} [Field K] {Ω : Type} [Field Ω] [Algebra K Ω] {w : ValuationSubring Ω}

/-- The residue action of a Frobenius lift is `t ↦ t^q`. -/
theorem residue_toRingAut_apply {σ : Ω ≃ₐ[K] Ω} (hD : σ ∈ w.decompositionSubgroup K) {q : ℕ}
    (hcong : ∀ x ∈ w, w.valuation (σ x - x ^ q) < 1) (t : IsLocalRing.ResidueField w) :
    MulSemiringAction.toRingAut (w.decompositionSubgroup K) (IsLocalRing.ResidueField w)
      ⟨σ, hD⟩ t = t ^ q := by
  obtain ⟨x, rfl⟩ := IsLocalRing.residue_surjective t
  show (⟨σ, hD⟩ : w.decompositionSubgroup K) • IsLocalRing.residue w x = _
  rw [← IsLocalRing.ResidueField.residue_smul]
  exact residue_frobenius hD hcong x

/-- **The residue action of `σ^r` is `t ↦ t^(q^r)`.** -/
theorem residue_toRingAut_pow_apply {σ : Ω ≃ₐ[K] Ω} (hD : σ ∈ w.decompositionSubgroup K)
    {q : ℕ} (hcong : ∀ x ∈ w, w.valuation (σ x - x ^ q) < 1) (r : ℕ)
    (t : IsLocalRing.ResidueField w) :
    MulSemiringAction.toRingAut (w.decompositionSubgroup K) (IsLocalRing.ResidueField w)
      ((⟨σ, hD⟩ : w.decompositionSubgroup K) ^ r) t = t ^ (q ^ r) := by
  have hDr : σ ^ r ∈ w.decompositionSubgroup K := pow_mem hD r
  have e : (⟨σ, hD⟩ : w.decompositionSubgroup K) ^ r = ⟨σ ^ r, hDr⟩ := Subtype.ext (by simp)
  rw [e]
  exact residue_toRingAut_apply hDr (pow_congr hD hcong r) t

end General

section Lift

variable {K : Type} [Field K] [NumberField K] {O : ValuationSubring K} [IsDiscreteValuationRing O]
  {Ω : Type} [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω] {w : ValuationSubring Ω}

theorem mem_stabilizer_of_decomp (hw : w.comap (algebraMap K Ω) = O) {σ : Ω ≃ₐ[K] Ω}
    (hD : σ ∈ w.decompositionSubgroup K) :
    σ ∈ MulAction.stabilizer (Ω ≃ₐ[K] Ω) (primeQ hw) := by
  rw [← decomposition_eq_stabilizer hw]
  exact hD

/-- **The `O/𝔪_O`-algebra automorphism of `B/Q` induced by `σ^r` is `y ↦ y^(q^r)`.** -/
theorem stabilizerHom_frob_pow_apply (hw : w.comap (algebraMap K Ω) = O) {σ : Ω ≃ₐ[K] Ω}
    (hD : σ ∈ w.decompositionSubgroup K) {q : ℕ}
    (hcong : ∀ x ∈ w, w.valuation (σ x - x ^ q) < 1) (r : ℕ)
    (y : integralClosure O Ω ⧸ primeQ hw) :
    Ideal.Quotient.stabilizerHom (primeQ hw) (IsLocalRing.maximalIdeal O) (Ω ≃ₐ[K] Ω)
      ((⟨σ, mem_stabilizer_of_decomp hw hD⟩ : MulAction.stabilizer (Ω ≃ₐ[K] Ω) (primeQ hw)) ^ r) y =
      y ^ (q ^ r) := by
  obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective y
  rw [Ideal.Quotient.stabilizerHom_apply, ← map_pow, Ideal.Quotient.eq, mem_primeQ]
  have e : (((⟨σ, mem_stabilizer_of_decomp hw hD⟩ :
      MulAction.stabilizer (Ω ≃ₐ[K] Ω) (primeQ hw)) ^ r : MulAction.stabilizer _ _) :
        Ω ≃ₐ[K] Ω) = σ ^ r := by simp
  show w.valuation ((((⟨σ, mem_stabilizer_of_decomp hw hD⟩ :
      MulAction.stabilizer (Ω ≃ₐ[K] Ω) (primeQ hw)) ^ r : MulAction.stabilizer _ _) :
        Ω ≃ₐ[K] Ω) (b : Ω) - (b : Ω) ^ (q ^ r)) < 1
  rw [e]
  exact pow_congr hD hcong r b (intClosure_mem hw b)

/-- **`resB : B/Q ≅ k_w` intertwines the two residue actions.** -/
theorem resB_stabilizerHom (hw : w.comap (algebraMap K Ω) = O) {σ : Ω ≃ₐ[K] Ω}
    (hD : σ ∈ w.decompositionSubgroup K) (y : integralClosure O Ω ⧸ primeQ hw) :
    resB hw (Ideal.Quotient.stabilizerHom (primeQ hw) (IsLocalRing.maximalIdeal O) (Ω ≃ₐ[K] Ω)
      ⟨σ, mem_stabilizer_of_decomp hw hD⟩ y) =
      MulSemiringAction.toRingAut (w.decompositionSubgroup K) (IsLocalRing.ResidueField w)
        ⟨σ, hD⟩ (resB hw y) := by
  obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective y
  rw [Ideal.Quotient.stabilizerHom_apply, resB_mk, resB_mk]
  show _ = (⟨σ, hD⟩ : w.decompositionSubgroup K) • IsLocalRing.residue w (incB hw b)
  rw [← IsLocalRing.ResidueField.residue_smul]
  rfl

end Lift

end FrobLift
