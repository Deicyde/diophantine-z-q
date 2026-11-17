/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: P2M.Sol.S_DeligneSerre_exists_residual_galoisRep_charpoly_frobenius_eq_of_weightOne_hecke_eigen (git blob e38085e9f1dd9e489a8f3c9751c820c7e0e67386, sha256 66a60fa3184d7bb94f3a6b27b86f1dea30353b7f54da6a7f06d4f4d074098285).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_GaloisRep_Residual
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_Deformations_MatrixRepresentation
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_CuspForm_PrimitiveFormGamma1
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_CuspForm_exists_gamma1_qCoeff_eq_ite_coprime
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_DeligneSerre_exists_weightTwo_hecke_eigen_reduction_eq_of_weightOne_hecke_eigen
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_DeligneSerre_exists_residual_galoisRep_charpoly_frobenius_eq_of_weightTwo_hecke_eigen

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

namespace P2MW.S_DeligneSerre_exists_residual_galoisRep_charpoly_frobenius_eq_of_weightOne_hecke_eigen

set_option autoImplicit false

open CongruenceSubgroup Polynomial
open scoped MatrixGroups



namespace DeligneSerre67W2

open ModularFormClass

theorem qCoeff_zero_eq_zero {N : ℕ} [NeZero N] {k : ℤ} (f : CuspForm (Gamma1 N) k) :
    qCoeff f 0 = 0 := by
  have h0 : UpperHalfPlane.IsZeroAtImInfty (⇑f) := CuspFormClass.zero_at_infty f
  simp only [qCoeff, UpperHalfPlane.qExpansion_coeff, Nat.factorial_zero, Nat.cast_one, inv_one,
    one_mul, iteratedDeriv_zero]
  exact h0.cuspFunction_apply_zero one_pos

section Coeff

variable {N : ℕ} [NeZero N] (ε : DirichletCharacter ℂ N) (f : CuspForm (Gamma1 N) 1)

theorem qCoeff_mem_of_coprime
    (hf₁ : qCoeff f 1 = 1)
    (hT : ∀ p : ℕ, p.Prime → ¬ p ∣ N → ∀ n : ℕ,
        qCoeff f (p * n) + ε (p : ZMod N) * (if p ∣ n then qCoeff f (n / p) else 0) =
          qCoeff f p * qCoeff f n)
    (R : Subalgebra ℤ ℂ) (hR : ∀ p : ℕ, p.Prime → ¬ p ∣ N → qCoeff f p ∈ R)
    (hε : ∀ x : ZMod N, ε x ∈ R) :
    ∀ n : ℕ, n.Coprime N → qCoeff f n ∈ R := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro hn
    rcases Nat.lt_or_ge n 2 with hlt | hge
    · interval_cases n
      · rw [qCoeff_zero_eq_zero]; exact zero_mem R
      · rw [hf₁]; exact one_mem R
    ·
      have hn1 : n ≠ 1 := by omega
      obtain ⟨p, hp, hpn⟩ : ∃ p : ℕ, p.Prime ∧ p ∣ n :=
        ⟨n.minFac, Nat.minFac_prime hn1, Nat.minFac_dvd n⟩
      have hpN : ¬ p ∣ N := fun h => hp.one_lt.ne' (Nat.eq_one_of_dvd_coprimes hn hpn h)
      obtain ⟨m, rfl⟩ := hpn
      have hm_lt : m < p * m := by
        have hm0 : 0 < m := Nat.pos_of_ne_zero (by rintro rfl; simp at hge)
        exact lt_mul_left hm0 hp.one_lt
      have hmN : m.Coprime N := Nat.Coprime.coprime_dvd_left (Dvd.intro_left p rfl) hn
      have hrel := hT p hp hpN m
      have hkey : qCoeff f (p * m) =
          qCoeff f p * qCoeff f m -
            ε (p : ZMod N) * (if p ∣ m then qCoeff f (m / p) else 0) := by
        rw [← hrel]; ring
      rw [hkey]
      refine sub_mem (mul_mem (hR p hp hpN) (ih m hm_lt hmN)) (mul_mem (hε _) ?_)
      split_ifs with hpm
      · refine ih (m / p) ?_ ?_
        · exact lt_of_le_of_lt (Nat.div_le_self m p) hm_lt
        · exact Nat.Coprime.coprime_dvd_left (Nat.div_dvd_of_dvd hpm) hmN
      · exact zero_mem R

end Coeff

section Level

variable {N : ℕ} (ε : DirichletCharacter ℂ N)

theorem dvd_level : N ∣ N * N ^ 2 := Dvd.intro _ rfl

theorem changeLevel_mem (R : Subalgebra ℤ ℂ) (hε : ∀ x : ZMod N, ε x ∈ R)
    (x : ZMod (N * N ^ 2)) :
    DirichletCharacter.changeLevel (dvd_level (N := N)) ε x ∈ R := by
  by_cases hx : IsUnit x
  · have := DirichletCharacter.changeLevel_eq_cast_of_dvd ε (dvd_level (N := N)) hx.unit
    rw [IsUnit.unit_spec] at this
    rw [this]
    exact hε _
  · rw [MulChar.map_nonunit _ hx]
    exact zero_mem R

theorem changeLevel_natCast_of_not_dvd {p : ℕ} (hp : p.Prime) (hpN : ¬ p ∣ N) :
    DirichletCharacter.changeLevel (dvd_level (N := N)) ε (p : ZMod (N * N ^ 2)) =
      ε (p : ZMod N) := by
  have hcopN : p.Coprime N := (Nat.Prime.coprime_iff_not_dvd hp).2 hpN
  have hcop : p.Coprime (N * N ^ 2) :=
    Nat.Coprime.mul_right hcopN (Nat.Coprime.pow_right 2 hcopN)
  have := DirichletCharacter.changeLevel_eq_cast_of_dvd ε (dvd_level (N := N))
    (ZMod.unitOfCoprime p hcop)
  simp only [ZMod.coe_unitOfCoprime] at this
  rw [this, ZMod.cast_natCast (dvd_level (N := N))]

theorem not_dvd_of_not_dvd_level {p : ℕ} (h : ¬ p ∣ N * N ^ 2) : ¬ p ∣ N :=
  fun h' => h (dvd_mul_of_dvd_left h' _)

theorem not_dvd_level_of_not_dvd {p : ℕ} (hp : p.Prime) (h : ¬ p ∣ N) : ¬ p ∣ N * N ^ 2 := by
  intro h'
  rcases (Nat.Prime.dvd_mul hp).1 h' with h1 | h2
  · exact h h1
  · exact h (hp.dvd_of_dvd_pow h2)

end Level

section Depletion

variable {N : ℕ} (ε : DirichletCharacter ℂ N) (f : CuspForm (Gamma1 N) 1)
  (f₁ : CuspForm (Gamma1 (N * N ^ 2)) 1)
  (hf₁f : ∀ n : ℕ, qCoeff f₁ n = if n.Coprime N then qCoeff f n else 0)

include hf₁f

theorem depleted_qCoeff_one (hf₁ : qCoeff f 1 = 1) : qCoeff f₁ 1 = 1 := by
  rw [hf₁f, if_pos (Nat.coprime_one_left N), hf₁]

theorem depleted_hecke
    (hT : ∀ p : ℕ, p.Prime → ¬ p ∣ N → ∀ n : ℕ,
        qCoeff f (p * n) + ε (p : ZMod N) * (if p ∣ n then qCoeff f (n / p) else 0) =
          qCoeff f p * qCoeff f n) :
    ∀ p : ℕ, p.Prime → ¬ p ∣ N * N ^ 2 → ∀ n : ℕ,
        qCoeff f₁ (p * n) +
            DirichletCharacter.changeLevel (dvd_level (N := N)) ε (p : ZMod (N * N ^ 2)) *
              (if p ∣ n then qCoeff f₁ (n / p) else 0) =
          qCoeff f₁ p * qCoeff f₁ n := by
  intro p hp hpM n
  have hpN : ¬ p ∣ N := not_dvd_of_not_dvd_level hpM
  have hcopN : p.Coprime N := (Nat.Prime.coprime_iff_not_dvd hp).2 hpN
  rw [changeLevel_natCast_of_not_dvd ε hp hpN]
  simp only [hf₁f]
  rw [if_pos hcopN]
  by_cases hn : n.Coprime N
  · have hpn : (p * n).Coprime N := Nat.Coprime.mul_left hcopN hn
    rw [if_pos hpn, if_pos hn]
    by_cases hdiv : p ∣ n
    · have hnp : (n / p).Coprime N :=
        Nat.Coprime.coprime_dvd_left (Nat.div_dvd_of_dvd hdiv) hn
      rw [if_pos hdiv, if_pos hnp]
      have := hT p hp hpN n
      rwa [if_pos hdiv] at this
    · rw [if_neg hdiv]
      have := hT p hp hpN n
      rwa [if_neg hdiv] at this
  · have hpn : ¬ (p * n).Coprime N := fun h => hn (Nat.Coprime.coprime_mul_left h)
    rw [if_neg hpn, if_neg hn]
    by_cases hdiv : p ∣ n
    · have hnp : ¬ (n / p).Coprime N := by
        intro h
        apply hn
        have : n = p * (n / p) := (Nat.mul_div_cancel' hdiv).symm
        rw [this]
        exact Nat.Coprime.mul_left hcopN h
      rw [if_pos hdiv, if_neg hnp]
      ring
    · rw [if_neg hdiv]
      ring

theorem depleted_qCoeff_mem [NeZero N] (hf₁ : qCoeff f 1 = 1)
    (hT : ∀ p : ℕ, p.Prime → ¬ p ∣ N → ∀ n : ℕ,
        qCoeff f (p * n) + ε (p : ZMod N) * (if p ∣ n then qCoeff f (n / p) else 0) =
          qCoeff f p * qCoeff f n)
    (R : Subalgebra ℤ ℂ) (hR : ∀ p : ℕ, p.Prime → ¬ p ∣ N → qCoeff f p ∈ R)
    (hε : ∀ x : ZMod N, ε x ∈ R) (n : ℕ) : qCoeff f₁ n ∈ R := by
  rw [hf₁f]
  split_ifs with hn
  · exact qCoeff_mem_of_coprime ε f hf₁ hT R hR hε n hn
  · exact zero_mem R

end Depletion

end DeligneSerre67W2

open DeligneSerre67W2 ModularFormClass in
theorem solution
    (N : ℕ) [NeZero N] (ε : DirichletCharacter ℂ N) (f : CuspForm (Gamma1 N) 1)
    (hf₁ : ModularFormClass.qCoeff f 1 = 1)
    (hT : ∀ p : ℕ, p.Prime → ¬ p ∣ N → ∀ n : ℕ,
        ModularFormClass.qCoeff f (p * n) +
            ε (p : ZMod N) * (if p ∣ n then ModularFormClass.qCoeff f (n / p) else 0) =
          ModularFormClass.qCoeff f p * ModularFormClass.qCoeff f n)
    (R : Subalgebra ℤ ℂ) (hR : ∀ p : ℕ, p.Prime → ¬ p ∣ N → ModularFormClass.qCoeff f p ∈ R)
    (hε : ∀ x : ZMod N, ε x ∈ R)
    (k : Type) [Field k] [Finite k] (φ : R →+* k) :
    ∃ ρ : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) →* GL (Fin 2) k, GaloisFactorsThroughFiniteLevel ρ ∧
      (Deformation.matrixRepresentation ρ).IsSemisimpleRepresentation ∧
      ∀ (p : ℕ) (hp : p.Prime) (hpN : ¬ p ∣ N), (p : k) ≠ 0 →
        ∀ A : ValuationSubring (AlgebraicClosure ℚ), A.LiesOverPrime p →
          (∀ σ ∈ A.inertiaSubgroupIn ℚ, ρ σ = 1) ∧
          ∀ σ : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ), A.IsFrobeniusAt σ p →
            ((ρ σ : GL (Fin 2) k) : Matrix (Fin 2) (Fin 2) k).charpoly =
              X ^ 2 - C (φ ⟨ModularFormClass.qCoeff f p, hR p hp hpN⟩) * X +
                C (φ ⟨ε (p : ZMod N), hε _⟩) := by
  classical

  set M₀ : ℕ := N * N ^ 2 with hM₀_def
  haveI : NeZero M₀ := ⟨mul_ne_zero (NeZero.ne N) (pow_ne_zero 2 (NeZero.ne N))⟩
  obtain ⟨f₁, hf₁f⟩ :=
    CuspForm.exists_gamma1_qCoeff_eq_ite_coprime N 1 f N (NeZero.ne N) M₀ (dvd_refl _)
  set ε₁ : DirichletCharacter ℂ M₀ := DirichletCharacter.changeLevel (dvd_level (N := N)) ε
    with hε₁_def
  have hf₁one : qCoeff f₁ 1 = 1 := depleted_qCoeff_one f f₁ hf₁f hf₁
  have hT₁ := depleted_hecke ε f f₁ hf₁f hT
  have hRall : ∀ n : ℕ, qCoeff f₁ n ∈ R := depleted_qCoeff_mem ε f f₁ hf₁f hf₁ hT R hR hε
  have hε₁R : ∀ x : ZMod M₀, ε₁ x ∈ R := changeLevel_mem ε R hε

  obtain ⟨M, instM, hMprimes, η, g, b, hg0, hηg, hTg, R', φ', hηR', hbR', hred⟩ :=
    DeligneSerre.exists_weightTwo_hecke_eigen_reduction_eq_of_weightOne_hecke_eigen M₀ ε₁ f₁ hf₁one
      hT₁ R hRall hε₁R k φ
  haveI : NeZero M := instM

  have hRW : ∀ p : ℕ, p.Prime → ¬ p ∣ M → p ∉ (∅ : Finset ℕ) → b p ∈ R' :=
    fun p hp hpM _ => hbR' p hp hpM
  obtain ⟨ρ, hfin, hss, hW⟩ :=
    DeligneSerre.exists_residual_galoisRep_charpoly_frobenius_eq_of_weightTwo_hecke_eigen M η g hg0
      hηg b hTg ∅ R' hRW hηR' k φ'
  refine ⟨ρ, hfin, hss, ?_⟩
  intro p hp hpN hpk A hA

  have hpM₀ : ¬ p ∣ M₀ := not_dvd_level_of_not_dvd hp hpN
  have hpM : ¬ p ∣ M := fun h => by
    rcases (hMprimes p hp).1 h with h1 | h2
    · exact hpM₀ h1
    · exact hpk h2
  obtain ⟨hin, hfrob⟩ := hW p hp hpM hpk A hA
  refine ⟨hin, fun σ hσ => ?_⟩
  rw [hfrob (Finset.notMem_empty p) σ hσ]

  obtain ⟨hb, hηp⟩ := hred p hp hpM
  have hb' : φ' ⟨b p, hRW p hp hpM (Finset.notMem_empty p)⟩ = φ ⟨qCoeff f p, hR p hp hpN⟩ := by
    rw [hb]
    congr 1
    apply Subtype.ext
    change qCoeff f₁ p = qCoeff f p
    rw [hf₁f, if_pos ((Nat.Prime.coprime_iff_not_dvd hp).2 hpN)]
  have hεp : φ' ⟨η (p : ZMod M), hηR' _⟩ * (p : k) = φ ⟨ε (p : ZMod N), hε _⟩ := by
    rw [hηp]
    congr 1
    apply Subtype.ext
    exact changeLevel_natCast_of_not_dvd ε hp hpN
  rw [hb', hεp]
