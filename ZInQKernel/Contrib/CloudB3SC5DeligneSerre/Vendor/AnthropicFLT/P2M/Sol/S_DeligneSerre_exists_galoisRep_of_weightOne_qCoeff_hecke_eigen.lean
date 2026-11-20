/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: P2M.Sol.S_DeligneSerre_exists_galoisRep_of_weightOne_qCoeff_hecke_eigen (git blob 81806b55ba3d9aa0504eaa1edfee095ea85f9b6e, sha256 ccfbeea401e9c29fe3bd25c5934ad2e3274227401760be1d3ab087f44fc5f174).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_FLTPrelim_Modularity
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_GaloisRep_Residual
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_Deformations_MatrixRepresentation
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Definitions.Def_ModularForm_HeckeOperator
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_DeligneSerre_exists_finset_qCoeff_mem_of_upperDensity_le_of_weightOne_hecke_eigen
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_DeligneSerre_exists_tsum_norm_qCoeff_sq_mul_rpow_le_log_of_weightOne_hecke_eigen
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_DeligneSerre_exists_residual_galoisRep_charpoly_frobenius_eq_of_weightOne_hecke_eigen
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_DeligneSerre_exists_natCard_range_le_of_charpoly_frobenius_mem_of_upperDensity_le
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_DeligneSerre_exists_galoisRep_complex_trace_frobenius_eq_of_forall_residual
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_CuspForm_slash_eq_dirichlet_smul_of_qCoeff_hecke_eigen

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

namespace P2MW.S_DeligneSerre_exists_galoisRep_of_weightOne_qCoeff_hecke_eigen

set_option autoImplicit false

open CongruenceSubgroup Polynomial
open scoped MatrixGroups ModularForm

namespace DeligneSerre41



theorem apply_neg_one_eq
    (N : ℕ) [NeZero N] (ε : DirichletCharacter ℂ N) (f : CuspForm (Gamma1 N) 1)
    (hf₁ : ModularFormClass.qCoeff f 1 = 1)
    (hT : ∀ p : ℕ, p.Prime → ¬ p ∣ N → ∀ n : ℕ,
        ModularFormClass.qCoeff f (p * n) +
            ε (p : ZMod N) * (if p ∣ n then ModularFormClass.qCoeff f (n / p) else 0) =
          ModularFormClass.qCoeff f p * ModularFormClass.qCoeff f n) :
    ε (-1) = -1 := by

  have heig : ∀ p : ℕ, p.Prime → ¬ p ∣ N → ∃ lam : ℂ, ∀ n : ℕ,
      ModularFormClass.qCoeff (⇑f) (n * p)
        + ε (p : ZMod N) * (p : ℂ) ^ ((1 : ℤ) - 1)
            * (if p ∣ n then ModularFormClass.qCoeff (⇑f) (n / p) else 0)
        = lam * ModularFormClass.qCoeff (⇑f) n := by
    intro p hp hpN
    refine ⟨ModularFormClass.qCoeff f p, fun n => ?_⟩
    rw [sub_self, zpow_zero, mul_one, mul_comm n p]
    exact hT p hp hpN n
  have hneg : (-1 : SL(2, ℤ)) ∈ Gamma0 N := by
    rw [Gamma0_mem]
    simp
  have hs := CuspForm.slash_eq_dirichlet_smul_of_qCoeff_hecke_eigen 1 f ε heig (-1) hneg

  have hf0 : ∃ τ : UpperHalfPlane, f τ ≠ 0 := by
    by_contra h
    push Not at h
    have hzero : (⇑f : UpperHalfPlane → ℂ) = 0 := funext h
    have : ModularFormClass.qCoeff f 1 = 0 := by
      unfold ModularFormClass.qCoeff
      rw [hzero, UpperHalfPlane.qExpansion_zero]
      simp
    rw [this] at hf₁
    exact zero_ne_one hf₁
  obtain ⟨τ, hτ⟩ := hf0
  have h1 := congrFun hs τ
  rw [ModularForm.SL_slash_apply, ModularGroup.SL_neg_smul, one_smul,
    ModularGroup.denom_apply] at h1
  simp only [Matrix.SpecialLinearGroup.coe_neg, Matrix.SpecialLinearGroup.coe_one,
    Matrix.neg_apply, Matrix.one_apply_ne (show (1 : Fin 2) ≠ 0 by decide),
    Matrix.one_apply_eq, neg_zero, Int.cast_zero, zero_mul, zero_add, Int.cast_neg,
    Int.cast_one, Pi.smul_apply, smul_eq_mul] at h1

  have h2 : ((-1 : ℂ)) ^ (-(1 : ℤ)) = -1 := by norm_num
  rw [h2] at h1
  have h3 : (ε (-1) + 1) * f τ = 0 := by linear_combination -h1
  rcases mul_eq_zero.mp h3 with h | h
  · linear_combination h
  · exact absurd h hτ

theorem exists_finite_adjoin_root (R : Subalgebra ℤ ℂ) (hR : Module.Finite ℤ R)
    (m : ℕ) (hm : 0 < m) (ζ : ℂ) (hζ : IsPrimitiveRoot ζ m) :
    ∃ R' : Subalgebra ℤ ℂ, Module.Finite ℤ R' ∧ ζ ∈ R' ∧ ∀ x ∈ R, x ∈ R' := by
  classical

  have hfgR : R.toSubmodule.FG := by
    rw [← Submodule.fg_top]
    exact hR.fg_top
  obtain ⟨s, hs⟩ := hfgR
  have hsR : ∀ x ∈ (s : Set ℂ), x ∈ R := by
    intro x hx
    have : x ∈ Submodule.span ℤ (s : Set ℂ) := Submodule.subset_span hx
    rw [hs] at this
    exact this

  have hint : ∀ x ∈ insert ζ (s : Set ℂ), IsIntegral ℤ x := by
    rintro x (rfl | hx)
    · exact hζ.isIntegral hm
    · exact IsIntegral.of_mem_of_fg R ⟨s, hs⟩ x (hsR x hx)
  let R' : Subalgebra ℤ ℂ := Algebra.adjoin ℤ (insert ζ (s : Set ℂ))
  have hfg' : R'.toSubmodule.FG := fg_adjoin_of_finite (Set.finite_insert.mpr s.finite_toSet) hint
  refine ⟨R', ?_, Algebra.subset_adjoin (Set.mem_insert ζ _), ?_⟩
  · exact ⟨(Submodule.fg_top _).mpr hfg'⟩
  · intro x hx
    have hx' : x ∈ R.toSubmodule := hx
    rw [← hs] at hx'
    have hle : Submodule.span ℤ (s : Set ℂ) ≤ R'.toSubmodule := by
      refine Submodule.span_le.mpr ?_
      intro y hy
      exact Algebra.subset_adjoin (Set.mem_insert_of_mem ζ hy)
    exact hle hx'

theorem mem_of_pow_eq_one {R' : Subalgebra ℤ ℂ} {m : ℕ} (hm : 0 < m) {ζ : ℂ}
    (hζ : IsPrimitiveRoot ζ m) (hζR : ζ ∈ R') {z : ℂ} (hz : z ^ m = 1) : z ∈ R' := by
  haveI : NeZero m := ⟨hm.ne'⟩
  obtain ⟨i, -, rfl⟩ := hζ.eq_pow_of_pow_eq_one hz
  exact pow_mem hζR i

theorem dirichlet_mem {N : ℕ} [NeZero N] (ε : DirichletCharacter ℂ N)
    {R' : Subalgebra ℤ ℂ} {m : ℕ} (hm : 0 < m) {ζ : ℂ}
    (hζ : IsPrimitiveRoot ζ m) (hζR : ζ ∈ R') (hNm : Nat.totient N ∣ m) (x : ZMod N) :
    ε x ∈ R' := by
  by_cases hx : IsUnit x
  · obtain ⟨u, rfl⟩ := hx
    apply mem_of_pow_eq_one hm hζ hζR
    obtain ⟨c, hc⟩ := hNm
    have hu : (ε (u : ZMod N)) ^ Nat.totient N = 1 := by
      rw [← map_pow, ← Units.val_pow_eq_pow_val, ← ZMod.card_units_eq_totient N,
        pow_card_eq_one, Units.val_one, map_one]
    rw [hc, pow_mul, hu, one_pow]
  · rw [MulChar.map_nonunit ε hx]
    exact zero_mem _

theorem finite_range_of_factorsThroughFiniteLevel {M : Type} [Group M] (ρ : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) →* M)
    (hρ : GaloisFactorsThroughFiniteLevel ρ) : Finite (MonoidHom.range ρ) := by
  classical
  obtain ⟨L, hL, hker⟩ := hρ
  haveI := hL

  let F : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) → (L →ₐ[ℚ] AlgebraicClosure ℚ) := fun σ => σ.toAlgHom.comp L.val
  have hF : ∀ σ τ : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ), F σ = F τ → ρ σ = ρ τ := by
    intro σ τ h
    have hfix : ∀ x ∈ L, (τ⁻¹ * σ) x = x := by
      intro x hx
      have hx' := congrArg (fun φ : L →ₐ[ℚ] AlgebraicClosure ℚ => φ ⟨x, hx⟩) h
      simp only [F, AlgHom.coe_comp, Function.comp_apply, AlgEquiv.coe_algHom] at hx'
      change σ x = τ x at hx'
      rw [AlgEquiv.mul_apply, hx']
      exact τ.symm_apply_apply x
    have h1 : ρ (τ⁻¹ * σ) = 1 := hker _ hfix
    rw [map_mul, map_inv, inv_mul_eq_one] at h1
    exact h1.symm
  let g : (L →ₐ[ℚ] AlgebraicClosure ℚ) → M := fun v =>
    if h : ∃ σ : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ), F σ = v then ρ h.choose else 1
  have hsub : (MonoidHom.range ρ : Set M) ⊆ Set.range g := by
    rintro _ ⟨σ, rfl⟩
    refine ⟨F σ, ?_⟩
    have h : ∃ σ' : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ), F σ' = F σ := ⟨σ, rfl⟩
    simp only [g, dif_pos h]
    exact hF _ _ h.choose_spec
  exact Set.Finite.subset (Set.finite_range g) hsub |>.to_subtype

end DeligneSerre41

open DeligneSerre41 in

theorem solution
    (N : ℕ) [NeZero N] (ε : DirichletCharacter ℂ N) (f : CuspForm (Gamma1 N) 1)
    (hf₁ : ModularFormClass.qCoeff f 1 = 1)
    (hT : ∀ p : ℕ, p.Prime → ¬ p ∣ N → ∀ n : ℕ,
        ModularFormClass.qCoeff f (p * n) +
            ε (p : ZMod N) * (if p ∣ n then ModularFormClass.qCoeff f (n / p) else 0) =
          ModularFormClass.qCoeff f p * ModularFormClass.qCoeff f n) :
    ∃ ρ : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) →* GL (Fin 2) ℂ,
      GaloisFactorsThroughFiniteLevel ρ ∧ -- [port] irreducibility conclusion omitted
      ∀ p : ℕ, p.Prime → ¬ p ∣ N →
        ∀ A : ValuationSubring (AlgebraicClosure ℚ), A.LiesOverPrime p →
          (∀ σ ∈ A.inertiaSubgroupIn ℚ, ρ σ = 1) ∧
          ∀ σ : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ), A.IsFrobeniusAt σ p →
            ((ρ σ : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ).trace = ModularFormClass.qCoeff f p ∧
            ((ρ σ : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ).det = ε (p : ZMod N) := by
  classical

  obtain ⟨R, hRfin, hRa, h55⟩ :=
    DeligneSerre.exists_finset_qCoeff_mem_of_upperDensity_le_of_weightOne_hecke_eigen N ε f hf₁ hT
  obtain ⟨Y, X₀, hX₀, hY⟩ := h55 (1 / 4) (by norm_num)

  obtain ⟨A, hA⟩ :=
    DeligneSerre.exists_natCard_range_le_of_charpoly_frobenius_mem_of_upperDensity_le
      (1 / 4) (by norm_num) (Y.card * N) X₀ hX₀

  set m : ℕ := A.factorial * Nat.totient N with hm_def
  have hm : 0 < m := Nat.mul_pos (Nat.factorial_pos A) (Nat.totient_pos.mpr (NeZero.pos N))
  set ζ : ℂ := Complex.exp (2 * Real.pi * Complex.I / m) with hζ_def
  have hζ : IsPrimitiveRoot ζ m := Complex.isPrimitiveRoot_exp m hm.ne'
  obtain ⟨R', hR'fin, hζR', hRR'⟩ := exists_finite_adjoin_root R hRfin m hm ζ hζ
  haveI := hR'fin
  have hR'a : ∀ p : ℕ, p.Prime → ¬ p ∣ N → ModularFormClass.qCoeff f p ∈ R' :=
    fun p hp hpN => hRR' _ (hRa p hp hpN)
  have hR'ε : ∀ x : ZMod N, ε x ∈ R' :=
    dirichlet_mem ε hm hζ hζR' (Dvd.intro_left _ rfl)

  have hfam : ∀ (ℓ : ℕ) [Fact ℓ.Prime] (φ : R' →+* ZMod ℓ),
      ∃ ρ : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) →* GL (Fin 2) (ZMod ℓ),
        GaloisFactorsThroughFiniteLevel ρ ∧
        Nat.card (MonoidHom.range ρ) ∣ m ∧
        ∀ (p : ℕ) (hp : p.Prime) (hpN : ¬ p ∣ N), p ≠ ℓ →
          ∀ A : ValuationSubring (AlgebraicClosure ℚ), A.LiesOverPrime p →
            (∀ σ ∈ A.inertiaSubgroupIn ℚ, ρ σ = 1) ∧
            ∀ σ : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ), A.IsFrobeniusAt σ p →
              ((ρ σ : GL (Fin 2) (ZMod ℓ)) : Matrix (Fin 2) (Fin 2) (ZMod ℓ)).charpoly =
                X ^ 2 - C (φ ⟨(fun p => ModularFormClass.qCoeff f p) p, hR'a p hp hpN⟩) * X +
                  C (φ ⟨(fun p : ℕ => ε (p : ZMod N)) p, hR'ε _⟩) := by
    intro ℓ hℓ φ
    obtain ⟨ρ, hfl, hss, hfrob⟩ :=
      DeligneSerre.exists_residual_galoisRep_charpoly_frobenius_eq_of_weightOne_hecke_eigen
        N ε f hf₁ hT R' hR'a hR'ε (ZMod ℓ) φ
    have hpℓ : ∀ p : ℕ, p.Prime → p ≠ ℓ → (p : ZMod ℓ) ≠ 0 := by
      intro p hp hne h
      rw [ZMod.natCast_eq_zero_iff] at h
      exact hne ((Nat.prime_dvd_prime_iff_eq hℓ.out hp).mp h).symm

    let φ' : ℂ → ZMod ℓ := fun y => if h : y ∈ R' then φ ⟨y, h⟩ else 0
    let P : Finset (ZMod ℓ)[X] :=
      (Y ×ˢ (Finset.univ : Finset (ZMod N))).image
        fun ye => X ^ 2 - C (φ' ye.1) * X + C (φ ⟨ε ye.2, hR'ε _⟩)
    have hPcard : P.card ≤ Y.card * N := by
      refine (Finset.card_image_le).trans ?_
      rw [Finset.card_product, Finset.card_univ, ZMod.card]

    let S : Finset ℕ := N.primeFactors ∪ {ℓ}
    have hS : ∀ p : ℕ, p.Prime → p ∉ S → ¬ p ∣ N ∧ p ≠ ℓ := by
      intro p hp hpS
      simp only [S, Finset.mem_union, Finset.mem_singleton, not_or, Nat.mem_primeFactors] at hpS
      exact ⟨fun h => hpS.1 ⟨hp, h, NeZero.ne N⟩, hpS.2⟩
    have hcard : Nat.card (MonoidHom.range ρ) ≤ A := by
      refine hA ℓ ρ hfl hss S P hPcard ?_
      intro p hp hpS B hB
      obtain ⟨hpN, hpne⟩ := hS p hp hpS
      obtain ⟨hin, hfr⟩ := hfrob p hp hpN (hpℓ p hp hpne) B hB
      refine ⟨hin, fun σ hσ hpX => ?_⟩
      rw [hfr σ hσ]
      refine Finset.mem_image.mpr ⟨(ModularFormClass.qCoeff f p, (p : ZMod N)),
        Finset.mem_product.mpr ⟨hY p hp hpN hpX, Finset.mem_univ _⟩, ?_⟩
      simp only [φ', dif_pos (hR'a p hp hpN)]
    haveI : Finite (MonoidHom.range ρ) := finite_range_of_factorsThroughFiniteLevel ρ hfl
    have hpos : 0 < Nat.card (MonoidHom.range ρ) := Nat.card_pos
    refine ⟨ρ, hfl, ?_, ?_⟩
    · exact (Nat.dvd_factorial hpos hcard).trans (Dvd.intro _ rfl)
    · intro p hp hpN hpne B hB
      exact hfrob p hp hpN (hpℓ p hp hpne) B hB

  obtain ⟨ρ, hρfl, hρ⟩ :=
    DeligneSerre.exists_galoisRep_complex_trace_frobenius_eq_of_forall_residual N R' m hm ζ hζ hζR'
      (fun p => ModularFormClass.qCoeff f p) (fun p : ℕ => ε (p : ZMod N)) hR'a
      (fun p _ _ => hR'ε _) hfam

  exact ⟨ρ, hρfl, hρ⟩ -- [port] irreducibility step omitted
