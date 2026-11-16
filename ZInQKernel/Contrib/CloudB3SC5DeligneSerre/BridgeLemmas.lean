import ZInQKernel.Contrib.G9.I4Layer
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Definitions.Def_FLTPrelim_Ramification
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Definitions.Def_EllipticCurve_FrobeniusTrace

/-! # Bridge lemmas for Deligne–Serre in weight one (cluster C5)

Supporting lemmas only. This file proves no open hypothesis and assumes no open statement. It
translates between the project's pkg-I4 vocabulary (`PkgI4.CF`, `PkgI4.coeff`,
`PkgI4.IsNormalizedEigenform`, `PkgI4.LiesOver`, `PkgI4.IsArithFrob`, Mathlib's inertia subgroup)
and the vocabulary of the already-vendored Anthropic FLT definitions
(`ValuationSubring.LiesOverPrime`, `ValuationSubring.inertiaSubgroupIn`,
`ValuationSubring.IsFrobeniusAt`). It also proves continuity of a homomorphism out of `G_ℚ` whose
kernel contains the fixing subgroup of a finite intermediate field.

* `coeff_prime_mul_add_of_isNormalizedEigenform` (L1): for a normalized eigenform of weight `1`
  with nebentypus `χ` and every prime `p`, the weight-one Hecke recurrence holds for **every**
  `n : ℕ` (including `n = 0`):
  `a_{pn} + χ(p) · [p ∣ n] · a_{n/p} = a_p · a_n`.
* `continuous_of_fixingSubgroup` and `continuous_of_exists_finiteLevel` (L4): `ρ : G_ℚ →* M` is
  continuous (Krull topology, any topology on `M`) once `ρ` kills `Gal(ℚ̄/L)` for some `L/ℚ` finite.
* `liesOverPrime_iff_liesOver` (L6), `mem_inertiaSubgroupIn_of_mem_inertiaSubgroup` (L7) and
  `isFrobeniusAt_of_isArithFrob` (L8): the place, inertia and Frobenius conversions.

Checked 2026-11-16 with Lean v4.35.0 and Mathlib `56a005855ea17e0b0958f73ec801ae140b0a1679`:
the file compiles without warnings of its own, and every theorem depends only on `propext`,
`Classical.choice` and `Quot.sound`.
-/

noncomputable section

namespace ZInQ.Contrib.CloudB3SC5DeligneSerre

open ZInQ.Contrib.G9

/-! ## L1. The weight-one prime Hecke recurrence for every `n` -/

section HeckeRecurrence

/-- The constant `q`-coefficient of a cusp form on `Γ₁(N)` vanishes. -/
theorem coeff_zero_eq_zero {N : ℕ} {k : ℤ} (g : PkgI4.CF N k) : PkgI4.coeff g 0 = 0 := by
  unfold PkgI4.coeff
  exact CuspFormClass.qExpansion_coeff_zero (Γ := (CongruenceSubgroup.Gamma1 N : Subgroup (GL (Fin 2) ℝ)))
    (k := k) g one_pos (by
      rw [CongruenceSubgroup.strictPeriods_Gamma1]
      exact AddSubgroup.mem_zmultiples 1)

/-- **L1.** For a normalized eigenform `g` of weight `1` with nebentypus `χ` (pkg-I4's
coefficient definition) and a prime `p`, for every `n : ℕ`:
`a_{pn} + χ(p) · (if p ∣ n then a_{n/p} else 0) = a_p a_n`. -/
theorem coeff_prime_mul_add_of_isNormalizedEigenform {N : ℕ} (χ : DirichletCharacter ℂ N)
    (g : PkgI4.CF N 1) (hg : PkgI4.IsNormalizedEigenform g χ) {p : ℕ} (hp : p.Prime) (n : ℕ) :
    PkgI4.coeff g (p * n) + χ (p : ZMod N) * (if p ∣ n then PkgI4.coeff g (n / p) else 0) =
      PkgI4.coeff g p * PkgI4.coeff g n := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [coeff_zero_eq_zero g]
  have hrec := hg.2.2 p n hp.pos hn
  simp only [sub_self, zpow_zero, mul_one] at hrec
  rw [hrec]
  by_cases hdvd : p ∣ n
  · obtain ⟨m, rfl⟩ := hdvd
    have hgcd : Nat.gcd p (p * m) = p := Nat.gcd_eq_left (dvd_mul_right p m)
    have hp1 : (1 : ℕ) ≠ p := hp.one_lt.ne
    rw [hgcd, hp.divisors]
    simp only [Finset.sum_pair hp1, dvd_mul_right p m, ↓reduceIte]
    have e1 : p * (p * m) / 1 ^ 2 = p * (p * m) := by rw [one_pow, Nat.div_one]
    have e2 : p * (p * m) / p ^ 2 = m := by
      rw [← mul_assoc, ← pow_two, Nat.mul_div_cancel_left m (pow_pos hp.pos 2)]
    have e3 : p * m / p = m := Nat.mul_div_cancel_left m hp.pos
    rw [e1, e2, e3, Nat.cast_one, map_one, one_mul]
  · have hcop : Nat.gcd p n = 1 := (Nat.Prime.coprime_iff_not_dvd hp).mpr hdvd
    rw [hcop, Nat.divisors_one]
    simp only [Finset.sum_singleton, hdvd, ↓reduceIte, one_pow, Nat.div_one, Nat.cast_one, map_one,
      one_mul, mul_zero, add_zero]

end HeckeRecurrence

/-! ## L4. A homomorphism that factors through a finite level is continuous -/

section Continuity

open scoped Pointwise

/-- **L4.** If `ρ : Gal(ℚ̄/ℚ) →* M` is trivial on `Gal(ℚ̄/L)` for a finite `L/ℚ`, then `ρ` is
continuous for the Krull topology and any topology on `M` (it is constant on the open cosets of
`Gal(ℚ̄/L)`). -/
theorem continuous_of_fixingSubgroup {M : Type*} [Monoid M] [TopologicalSpace M]
    (ρ : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) →* M)
    (L : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ L]
    (hL : ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, (∀ x ∈ L, σ x = x) → ρ σ = 1) :
    Continuous ρ := by
  have hU : IsOpen (L.fixingSubgroup : Set (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)) :=
    IntermediateField.fixingSubgroup_isOpen L
  have hker : ∀ τ ∈ L.fixingSubgroup, ρ τ = 1 := fun τ hτ =>
    hL τ (by simpa using hτ)
  rw [continuous_def]
  intro s _
  rw [isOpen_iff_forall_mem_open]
  intro σ hσ
  refine ⟨σ • (L.fixingSubgroup : Set (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)), ?_,
    hU.leftCoset σ, Set.mem_smul_set.mpr ⟨1, L.fixingSubgroup.one_mem, by simp⟩⟩
  intro x hx
  obtain ⟨τ, hτ, rfl⟩ := Set.mem_smul_set.mp hx
  show ρ (σ • τ) ∈ s
  rw [smul_eq_mul, map_mul, hker τ hτ, mul_one]
  exact hσ

/-- **L4, finite-level form.** The finite-level condition, written exactly as the body of Anthropic
FLT's `GaloisFactorsThroughFiniteLevel`, implies continuity. -/
theorem continuous_of_exists_finiteLevel {M : Type*} [Monoid M] [TopologicalSpace M]
    (ρ : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) →* M)
    (h : ∃ L : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ L ∧
      ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, (∀ x ∈ L, σ x = x) → ρ σ = 1) :
    Continuous ρ := by
  obtain ⟨L, hL, hker⟩ := h
  have := hL
  exact continuous_of_fixingSubgroup ρ L hker

end Continuity

/-! ## L6–L8. Places, inertia and Frobenius -/

section Places

/-- **L6.** pkg-I4's `LiesOver` is Anthropic FLT's `LiesOverPrime` (same definition). -/
theorem liesOverPrime_iff_liesOver (v : ValuationSubring PkgI4.Qbar) (p : ℕ) :
    v.LiesOverPrime p ↔ PkgI4.LiesOver v p :=
  Iff.rfl

/-- **L7.** An element of Mathlib's inertia subgroup (a subgroup of the decomposition group) lies,
as an element of `G_ℚ`, in Anthropic FLT's `inertiaSubgroupIn`. -/
theorem mem_inertiaSubgroupIn_of_mem_inertiaSubgroup {v : ValuationSubring PkgI4.Qbar}
    {σ : v.decompositionSubgroup ℚ} (hσ : σ ∈ v.inertiaSubgroup ℚ) :
    (σ : PkgI4.GQ) ∈ v.inertiaSubgroupIn ℚ :=
  Subgroup.mem_map_of_mem (v.decompositionSubgroup ℚ).subtype hσ

/-- **L8.** A pkg-I4 arithmetic Frobenius (`σ` in the decomposition group with `σ x ≡ x ^ p` modulo
the maximal ideal for every `x ∈ v`) is a Frobenius in the sense of Anthropic FLT's `IsFrobeniusAt`
(the decomposition action on the residue field is `x ↦ x ^ p`). -/
theorem isFrobeniusAt_of_isArithFrob {σ : PkgI4.GQ} {v : ValuationSubring PkgI4.Qbar} {p : ℕ}
    (h : PkgI4.IsArithFrob σ v p) : v.IsFrobeniusAt σ p := by
  refine ⟨h.1, fun x => ?_⟩
  obtain ⟨a, rfl⟩ := IsLocalRing.residue_surjective x
  rw [← IsLocalRing.ResidueField.residue_smul, ← map_pow, ← sub_eq_zero, ← map_sub,
    IsLocalRing.residue_eq_zero_iff, ← ValuationSubring.coe_mem_nonunits_iff]
  -- the coercions of `•`, `-` and `^` from `v` to `ℚ̄` are definitional
  show σ (a : PkgI4.Qbar) - (a : PkgI4.Qbar) ^ p ∈ v.nonunits
  exact h.2 a a.2

end Places

end ZInQ.Contrib.CloudB3SC5DeligneSerre
