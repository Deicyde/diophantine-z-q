import ZInQKernel.Contrib.CloudB3RC53.WeilIsogeny.Trace
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

/-!
# Hasse's bound

For an elliptic curve `E` over a finite field `𝔽_q`, `| |E(𝔽_q)| − q − 1 | ≤ 2√q`
(`hasseBoundProved_proof`; Silverman, *The Arithmetic of Elliptic Curves*, Theorem V.1.1).

* `degree_psi`: `deg(n π − m) = m² − a m n + q n²` whenever `m ≠ 0` in `\bar{𝔽}_q`: by
  `weilPairing_degree` at a prime `ℓ ≠ p`, where some value of `e_ℓ` is a primitive `ℓ`-th root of
  unity (nondegeneracy; `E[ℓ] ≠ 0`), `ℓ` divides `deg(n π − m) − (m² − amn + qn²)`; `ℓ` can be taken
  larger than this difference.
* `sq_traceFrob_le`: `a² ≤ 4q`. Otherwise, with `n = 3` and `m = ⌊3a/2⌋` or `⌊3a/2⌋ + 1` (one of
  them is nonzero in `\bar{𝔽}_q`), `4(m² − 3am + 9q) = (2m − 3a)² − 9(a² − 4q) ≤ 4 − 9 < 0`, while a
  degree is nonnegative.

This proves `HasseBound` of `Hasse/Convergence.lean` (same statement; cited by the manuscript as
Silverman V.1.1, p. 138, tex 1590–1591, 6323–6324; here PROVED, so not an input), hence
`HasseConvergence`.

Classification: PROVED.
-/

noncomputable section

open WeierstrassCurve WeierstrassCurve.Affine TauCeti TauCeti.Isogeny

namespace ZInQ.Contrib.CloudB3RC53.WeilIsogeny

variable {F : Type*} [Field F] [Fintype F] (W : WeierstrassCurve F) [W.IsElliptic]
  {K : Type*} [Field K] [DecidableEq K] [Algebra F K] [IsSepClosed K] [Algebra.IsAlgebraic F K]

/-- At a prime `ℓ` invertible in `K`, `ℓ` divides `deg ψ − (m² − amn + qn²)`. PROVED. -/
theorem prime_dvd_degree_sub {m : ℤ} (n : ℤ) (hm : (m : K) ≠ 0) {ℓ : ℕ} (hℓ : ℓ.Prime)
    (hℓK : (ℓ : K) ≠ 0) :
    (ℓ : ℤ) ∣ (psi W n hm).degree - (m ^ 2 - traceFrob W * m * n + Fintype.card F * n ^ 2) := by
  have : NeZero ℓ := ⟨hℓ.ne_zero⟩
  have hc : ((ℓ : ℤ) : K) ≠ 0 := by rwa [Int.cast_natCast]
  -- a nonzero `ℓ`-torsion point
  obtain ⟨R, hR, hR0⟩ : ∃ R : (W⁄K).toAffine.Point, (ℓ : ℤ) • R = 0 ∧ R ≠ 0 := by
    by_contra h
    simp only [not_exists, not_and, not_not] at h
    have hcard := (W⁄K).toAffine.natCard_setOf_zsmul_eq_zero hc
    have hsub : {R : (W⁄K).toAffine.Point | (ℓ : ℤ) • R = 0} ⊆ {0} := fun R hR => h R hR
    have := Nat.card_mono (Set.finite_singleton 0) hsub
    rw [hcard, Nat.card_unique, Int.natAbs_natCast] at this
    have h1 := hℓ.one_lt
    nlinarith
  set T : Submodule.torsionBy ℤ (W⁄K).toAffine.Point (ℓ : ℤ) :=
    ⟨R, (Submodule.mem_torsionBy_iff _ _).mpr hR⟩
  have hT0 : T ≠ 0 := fun h => hR0 (congrArg Subtype.val h)
  obtain ⟨S, hS⟩ : ∃ S, weilPairing (W⁄K) ℓ hℓK S T ≠ 0 := by
    by_contra h
    simp only [not_exists, not_not] at h
    exact hT0 (eq_zero_of_forall_weilPairing_eq_zero (W⁄K) ℓ hℓK h)
  set x := weilPairing (W⁄K) ℓ hℓK S T
  have hx : ℓ • x = 0 := by
    apply Additive.toMul.injective
    rw [toMul_nsmul, toMul_zero]
    ext
    simpa using ((mem_rootsOfUnity' ℓ _).mp (Additive.toMul x).2)
  have hord : addOrderOf x = ℓ := by
    rcases (Nat.dvd_prime hℓ).mp (addOrderOf_dvd_of_nsmul_eq_zero hx) with h | h
    · exact absurd (AddMonoid.addOrderOf_eq_one_iff.mp h) hS
    · exact h
  have hdeg := weilPairing_degree W ℓ hℓK n hm S T
  rw [← sub_eq_zero, ← sub_smul] at hdeg
  rw [← hord]
  exact (addOrderOf_dvd_iff_zsmul_eq_zero).mpr hdeg

/-- **`deg(n π − m) = m² − a m n + q n²`.** PROVED. -/
theorem degree_psi {m : ℤ} (n : ℤ) (hm : (m : K) ≠ 0) :
    ((psi W n hm).degree : ℤ) = m ^ 2 - traceFrob W * m * n + Fintype.card F * n ^ 2 := by
  set D := ((psi W n hm).degree : ℤ) - (m ^ 2 - traceFrob W * m * n + Fintype.card F * n ^ 2)
  obtain ⟨ℓ, hle, hℓ⟩ := Nat.exists_infinite_primes (D.natAbs + Fintype.card F + 1)
  have hℓK : (ℓ : K) ≠ 0 := by
    intro h0
    have hF : (ℓ : F) = 0 := by
      apply (algebraMap F K).injective
      rw [map_natCast, map_zero, h0]
    have h1 := (CharP.cast_eq_zero_iff F (ringChar F) ℓ).mp hF
    have h2 := (CharP.cast_eq_zero_iff F (ringChar F) (Fintype.card F)).mp (FiniteField.cast_card_eq_zero F)
    have hr : ringChar F = ℓ := ((Nat.dvd_prime hℓ).mp h1).resolve_left (CharP.ringChar_ne_one)
    rw [hr] at h2
    have := Nat.le_of_dvd Fintype.card_pos h2
    omega
  have hdvd := prime_dvd_degree_sub W n hm hℓ hℓK
  have hlt : (D.natAbs : ℤ) < ℓ := by exact_mod_cast (by omega : D.natAbs < ℓ)
  have : D = 0 := Int.eq_zero_of_abs_lt_dvd hdvd (by rwa [Int.abs_eq_natAbs])
  simp only [D] at this
  linarith

omit [DecidableEq K] [IsSepClosed K] [Algebra.IsAlgebraic F K] in
/-- **`a² ≤ 4q`.** PROVED. -/
theorem sq_traceFrob_le (L : Type*) [Field L] [DecidableEq L] [Algebra F L] [IsSepClosed L]
    [Algebra.IsAlgebraic F L] : traceFrob W ^ 2 ≤ 4 * (Fintype.card F : ℤ) := by
  by_contra hlt
  rw [not_le] at hlt
  have key : ∀ m : ℤ, (m : L) ≠ 0 →
      0 ≤ m ^ 2 - traceFrob W * m * 3 + (Fintype.card F : ℤ) * 3 ^ 2 := fun m hm => by
    rw [← degree_psi W (K := L) 3 hm]; exact Nat.cast_nonneg _
  have hr := Int.emod_two_eq_zero_or_one (3 * traceFrob W)
  have hdiv := Int.mul_ediv_add_emod (3 * traceFrob W) 2
  have hneg : ∀ m : ℤ, (2 * m - 3 * traceFrob W) ^ 2 ≤ 4 →
      m ^ 2 - traceFrob W * m * 3 + (Fintype.card F : ℤ) * 3 ^ 2 < 0 := by
    intro m hm; nlinarith
  by_cases h0 : ((3 * traceFrob W / 2 : ℤ) : L) = 0
  · have h1 : ((3 * traceFrob W / 2 + 1 : ℤ) : L) ≠ 0 := by
      rw [Int.cast_add, h0, zero_add, Int.cast_one]; exact one_ne_zero
    have := key _ h1
    have := hneg (3 * traceFrob W / 2 + 1) (by rcases hr with h | h <;> nlinarith)
    omega
  · have := key _ h0
    have := hneg (3 * traceFrob W / 2) (by rcases hr with h | h <;> nlinarith)
    omega

omit [W.IsElliptic] [DecidableEq K] [IsSepClosed K] [Algebra.IsAlgebraic F K] in
/-- **Hasse's bound** `| |E(𝔽_q)| − q − 1 | ≤ 2√q` (Silverman V.1.1). PROVED. -/
theorem hasse_bound_of_sq (h : traceFrob W ^ 2 ≤ 4 * (Fintype.card F : ℤ)) :
    |(Nat.card W.toAffine.Point : ℝ) - Fintype.card F - 1| ≤ 2 * √(Fintype.card F : ℝ) := by
  have e : (Nat.card W.toAffine.Point : ℝ) - Fintype.card F - 1 = -(traceFrob W : ℝ) := by
    simp only [traceFrob]; push_cast; ring
  rw [e, abs_neg, ← Real.sqrt_sq_eq_abs, show (2 : ℝ) * √(Fintype.card F : ℝ) =
    √(4 * Fintype.card F) by rw [Real.sqrt_mul (by norm_num), show (4 : ℝ) = 2 ^ 2 by norm_num,
      Real.sqrt_sq (by norm_num)]]
  exact Real.sqrt_le_sqrt (by exact_mod_cast h)

/-- **Node `HasseBoundProved`** (Silverman, *The Arithmetic of Elliptic Curves*, 2nd ed., Theorem
V.1.1; the statement `HasseBound` of `Hasse/Convergence.lean`; cited by the manuscript, p. 138): for
an elliptic curve `E` over a finite field `𝔽_q`, `| |E(𝔽_q)| − q − 1 | ≤ 2√q`. PROVED
(`hasseBoundProved_proof`). -/
def HasseBoundProved : Prop :=
  ∀ (F : Type) [Field F] [Fintype F] (W : WeierstrassCurve F) [W.IsElliptic],
    |(Nat.card W.toAffine.Point : ℝ) - Fintype.card F - 1| ≤ 2 * √(Fintype.card F : ℝ)

theorem hasseBoundProved_proof : HasseBoundProved := by
  intro F _ _ W _
  classical
  exact hasse_bound_of_sq W (sq_traceFrob_le W (AlgebraicClosure F))

end ZInQ.Contrib.CloudB3RC53.WeilIsogeny
