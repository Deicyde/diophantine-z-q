/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: P2M.Sol.S_DeligneSerre_exists_residual_galoisRep_charpoly_frobenius_eq_of_weightTwo_hecke_eigen (git blob 10842a454395c8ab3ff6c19f38d646ab4368d34a, sha256 02b3a34a5375ddb4b880c1be4bf23b048cb417d4801970ff22f1a61591aa69c1).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_GaloisRep_Residual
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_GaloisRep_Adic
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_Deformations_MatrixRepresentation
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_CuspForm_PrimitiveFormGamma1
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_CuspForm_IsEigenformWith_exists_galoisRepAdic_charpoly_frobenius_eq_and_isUnramifiedAt
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_CuspForm_exists_isPrimitiveForm_of_hasNebentypus_qCoeff_hecke_eigen
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_CuspForm_IsEigenformWith_fg_adjoin_qCoeff
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_IsDedekindDomain_HeightOneSpectrum_isAdicComplete_adicCompletionIntegers
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_IsDedekindDomain_HeightOneSpectrum_finite_residueField_adicCompletionIntegers
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_GaloisRep_exists_isSemisimpleRepresentation_charpoly_map_eq_of_trace_det_frobenius_mem_range

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

namespace P2MW.S_DeligneSerre_exists_residual_galoisRep_charpoly_frobenius_eq_of_weightTwo_hecke_eigen

set_option autoImplicit false

open CongruenceSubgroup Polynomial NumberField IsDedekindDomain
open scoped MatrixGroups

namespace DSW2



theorem ker_isMaximal_of_finite {A F : Type*} [CommRing A] [Field F] [Finite F] (f : A →+* F) :
    (RingHom.ker f).IsMaximal := by
  haveI : Finite f.range := Subtype.finite
  have hF : IsField f.range := Finite.isField_of_domain f.range
  have hQ : IsField (A ⧸ RingHom.ker f) := MulEquiv.isField hF (RingHom.quotientKerEquivRange f).toMulEquiv
  exact Ideal.Quotient.maximal_of_isField _ hQ

theorem ker_eq_ker_of_le {A F F' : Type*} [CommRing A] [Field F] [Finite F] [Field F'] (f : A →+* F)
    (g : A →+* F') (h : RingHom.ker f ≤ RingHom.ker g) : RingHom.ker f = RingHom.ker g :=
  (ker_isMaximal_of_finite f).eq_of_le (RingHom.ker_ne_top g) h

theorem exists_embedding {A κ k'' : Type} [CommRing A] [Field κ] [Finite κ] [Field k''] [Finite k'']
    (φ₀ : A →+* κ) (r : A →+* k'') (h : ∀ x, φ₀ x = 0 → r x = 0) :
    ∃ e : k'' →+* AlgebraicClosure κ, ∀ x, e (r x) = algebraMap κ (AlgebraicClosure κ) (φ₀ x) := by
  classical
  have hle : RingHom.ker φ₀ ≤ RingHom.ker r := fun x hx => (RingHom.mem_ker).mpr (h x hx)
  have hker : RingHom.ker φ₀ = RingHom.ker r := ker_eq_ker_of_le φ₀ r hle
  let k₀ : Type := φ₀.range
  haveI : Finite k₀ := Subtype.finite
  have hk₀ : IsField k₀ := Finite.isField_of_domain k₀
  letI : Field k₀ := hk₀.toField
  let φ₀' : A →+* k₀ := φ₀.rangeRestrict
  have hsurj : Function.Surjective φ₀' := RingHom.rangeRestrict_surjective φ₀
  have hkerφ₀' : RingHom.ker φ₀' = RingHom.ker φ₀ := RingHom.ker_rangeRestrict φ₀
  let j : k₀ →+* k'' := RingHom.liftOfSurjective φ₀' hsurj ⟨r, by rw [hkerφ₀', hker]⟩
  have hj : ∀ x, j (φ₀' x) = r x := fun x =>
    RingHom.liftOfRightInverse_comp_apply φ₀' _ _ ⟨r, by rw [hkerφ₀', hker]⟩ x
  let i : k₀ →+* AlgebraicClosure κ := (algebraMap κ (AlgebraicClosure κ)).comp φ₀.range.subtype
  letI : Algebra k₀ k'' := j.toAlgebra
  letI : Algebra k₀ (AlgebraicClosure κ) := i.toAlgebra
  haveI : Module.Finite k₀ k'' := Module.Finite.of_finite
  haveI : Algebra.IsAlgebraic k₀ k'' := Algebra.IsAlgebraic.of_finite k₀ k''
  let e : k'' →ₐ[k₀] AlgebraicClosure κ := IsAlgClosed.lift
  refine ⟨e.toRingHom, fun x => ?_⟩
  have h1 : r x = algebraMap k₀ k'' (φ₀' x) := (hj x).symm
  rw [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, h1, AlgHom.commutes]
  rfl

theorem algebraMap_mem_maximalIdeal_adicCompletionIntegers_iff
    {R : Type*} [CommRing R] [IsDedekindDomain R] (K : Type*) [Field K] [Algebra R K]
    [IsFractionRing R K] (v : HeightOneSpectrum R) (r : R) :
    algebraMap R (v.adicCompletionIntegers K) r ∈
        IsLocalRing.maximalIdeal (v.adicCompletionIntegers K) ↔ r ∈ v.asIdeal := by
  rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff,
    HeightOneSpectrum.adicCompletionIntegers.isUnit_iff_valued_eq_one,
    ← HeightOneSpectrum.valuation_lt_one_iff_mem (K := K)]
  change ¬ Valued.v ((algebraMap R K r : K) : v.adicCompletion K) = 1 ↔ _
  rw [HeightOneSpectrum.valuedAdicCompletion_eq_valuation']
  exact ⟨fun h => lt_of_le_of_ne (HeightOneSpectrum.valuation_le_one v r) h, fun h => h.ne⟩

theorem exists_coefficientRing (K : Type) [Field K] [NumberField K] {A : Type} [CommRing A]
    (i : A →+* 𝓞 K) (hi : Function.Injective i) (P : Ideal A) (hP : P.IsMaximal) :
    ∃ (O : Type) (_ : CommRing O) (_ : IsDomain O)
      (_ : IsDiscreteValuationRing O) (_ : IsAdicComplete (IsLocalRing.maximalIdeal O) O)
      (_ : Finite (IsLocalRing.ResidueField O)) (_ : CharZero O)
      (ι : A →+* O), ∀ x, ι x ∈ IsLocalRing.maximalIdeal O ↔ x ∈ P := by
  classical
  haveI := hP
  letI : Algebra A (𝓞 K) := i.toAlgebra
  haveI : IsScalarTower ℤ A (𝓞 K) := IsScalarTower.of_algebraMap_eq (fun n => by simp)
  haveI : Algebra.IsIntegral A (𝓞 K) := ⟨fun y => (RingOfIntegers.isIntegral y).tower_top⟩
  have hker : RingHom.ker (algebraMap A (𝓞 K)) = ⊥ := (RingHom.injective_iff_ker_eq_bot _).mp hi
  obtain ⟨Q, hQmax, hQP⟩ := Ideal.exists_ideal_over_maximal_of_isIntegral P (S := 𝓞 K)
    (by rw [hker]; exact bot_le)
  have hQne : Q ≠ ⊥ := Ring.ne_bot_of_isMaximal_of_not_isField hQmax (RingOfIntegers.not_isField K)
  let v : HeightOneSpectrum (𝓞 K) := ⟨Q, hQmax.isPrime, hQne⟩
  haveI : Finite (𝓞 K ⧸ Q) := Ideal.finiteQuotientOfFreeOfNeBot Q hQne
  let O : Type := v.adicCompletionIntegers K
  haveI : IsAdicComplete (IsLocalRing.maximalIdeal O) O :=
    HeightOneSpectrum.isAdicComplete_adicCompletionIntegers_aflt K v
  haveI : Finite (𝓞 K ⧸ v.asIdeal) := ‹Finite (𝓞 K ⧸ Q)›
  haveI : Finite (IsLocalRing.ResidueField O) :=
    HeightOneSpectrum.finite_residueField_adicCompletionIntegers_aflt K v
  haveI : CharZero (v.adicCompletion K) :=
    charZero_of_injective_algebraMap (algebraMap K (v.adicCompletion K)).injective
  haveI : CharZero O := inferInstance
  let ι : A →+* O := (algebraMap (𝓞 K) O).comp i
  refine ⟨O, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, ι,
    fun x => ?_⟩
  show algebraMap (𝓞 K) O (i x) ∈ _ ↔ _
  rw [algebraMap_mem_maximalIdeal_adicCompletionIntegers_iff K v, ← hQP, Ideal.mem_comap]
  rfl

section MatrixForm

variable {Ω : Type} [Field Ω] (τ : ResidualGaloisRep Ω)

theorem charpoly_fin_two {K : Type*} [CommRing K] (M : Matrix (Fin 2) (Fin 2) K) :
    M.charpoly = X ^ 2 - C M.trace * X + C M.det := by
  nontriviality K
  have hdeg : M.charpoly.natDegree = 2 := by rw [Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin]
  have hmonic := M.charpoly_monic
  have hc0 : M.charpoly.coeff 0 = M.det := by
    rw [Matrix.det_eq_sign_charpoly_coeff, Fintype.card_fin]; ring
  have hc1 : M.charpoly.coeff 1 = -M.trace := by
    rw [Matrix.trace_eq_neg_charpoly_coeff, Fintype.card_fin]; simp
  apply Polynomial.ext
  intro n
  rcases n with _ | _ | _ | n
  · simp [hc0]
  · simp [hc1, coeff_X_pow, coeff_C]
  · have : M.charpoly.coeff 2 = 1 := by
      have := hmonic.leadingCoeff
      rwa [Polynomial.leadingCoeff, hdeg] at this
    simp [this]
  · have hlt : M.charpoly.natDegree < n + 3 := by omega
    rw [Polynomial.coeff_eq_zero_of_natDegree_lt hlt]
    simp [coeff_X_pow]

theorem trace_eq_of_charpoly_eq {K : Type*} [CommRing K] (M : Matrix (Fin 2) (Fin 2) K) (u v : K)
    (h : M.charpoly = X ^ 2 - C u * X + C v) : M.trace = u := by
  rw [Matrix.trace_eq_neg_charpoly_coeff, h, Fintype.card_fin]
  simp [coeff_C, coeff_X_pow]

theorem det_eq_of_charpoly_eq {K : Type*} [CommRing K] (M : Matrix (Fin 2) (Fin 2) K) (u v : K)
    (h : M.charpoly = X ^ 2 - C u * X + C v) : M.det = v := by
  rw [Matrix.det_eq_sign_charpoly_coeff, h, Fintype.card_fin]
  simp [coeff_C, coeff_X_pow]

noncomputable def basisTwo : Module.Basis (Fin 2) Ω τ.V := Module.finBasisOfFinrankEq Ω τ.V τ.finrank_eq

noncomputable def matForm : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) →* GL (Fin 2) Ω :=
  (Units.map (LinearMap.toMatrixAlgEquiv (basisTwo τ)).toMonoidHom).comp (MonoidHom.toHomUnits τ.ρ)

theorem matForm_val (σ : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)) :
    ((matForm τ σ : GL (Fin 2) Ω) : Matrix (Fin 2) (Fin 2) Ω) = LinearMap.toMatrix (basisTwo τ) (basisTwo τ) (τ.ρ σ) := by
  simp only [matForm, MonoidHom.coe_comp, Function.comp_apply, Units.coe_map, MonoidHom.coe_toHomUnits]
  rfl

theorem charpoly_matForm (σ : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)) :
    ((matForm τ σ : GL (Fin 2) Ω) : Matrix (Fin 2) (Fin 2) Ω).charpoly = (τ.ρ σ).charpoly := by
  rw [matForm_val, LinearMap.charpoly_toMatrix]

theorem matForm_eq_one {σ : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)} (h : τ.ρ σ = 1) : matForm τ σ = 1 := by
  apply Units.ext
  rw [matForm_val, h, Units.val_one]
  exact LinearMap.toMatrix_one _

theorem factorsThroughFiniteLevel_matForm : GaloisFactorsThroughFiniteLevel (matForm τ) := by
  obtain ⟨L, hL, hker⟩ := τ.factorsThroughFiniteLevel
  exact ⟨L, hL, fun σ hσ => matForm_eq_one τ (hker σ hσ)⟩

end MatrixForm

theorem exists_matrixRep_of_galoisRepAdic
    {A κ : Type} [CommRing A] [Field κ] [Finite κ] (φ₀ : A →+* κ)
    (O'' : Type) [CommRing O''] [IsLocalRing O''] [Finite (IsLocalRing.ResidueField O'')]
    (ψ : A →+* O'') (hψ : ∀ x, φ₀ x = 0 → ψ x ∈ IsLocalRing.maximalIdeal O'')
    (ρ : GaloisRepAdic O'') :
    ∃ ρΩ : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) →* GL (Fin 2) (AlgebraicClosure κ), GaloisFactorsThroughFiniteLevel ρΩ ∧
      (∀ σ, ρ.ρ σ = 1 → ρΩ σ = 1) ∧
      ∀ (σ : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)) (u v : A), LinearMap.charpoly (ρ.ρ σ) = X ^ 2 - C (ψ u) * X + C (ψ v) →
        (ρΩ σ : Matrix (Fin 2) (Fin 2) (AlgebraicClosure κ)).charpoly =
          X ^ 2 - C (algebraMap κ (AlgebraicClosure κ) (φ₀ u)) * X + C (algebraMap κ (AlgebraicClosure κ) (φ₀ v)) := by
  set k'' := IsLocalRing.ResidueField O''
  let r : A →+* k'' := (IsLocalRing.residue O'').comp ψ
  have hr : ∀ x, φ₀ x = 0 → r x = 0 := fun x hx =>
    (IsLocalRing.residue_eq_zero_iff _).mpr (hψ x hx)
  obtain ⟨e, he⟩ := exists_embedding φ₀ r hr

  let τ : ResidualGaloisRep (AlgebraicClosure κ) := ρ.residual.baseChangeAlong e
  letI : Algebra k'' (AlgebraicClosure κ) := e.toAlgebra
  refine ⟨matForm τ, factorsThroughFiniteLevel_matForm τ, fun σ hσ => matForm_eq_one τ ?_, fun σ u v hcp => ?_⟩
  ·
    have h1 : ρ.residual.ρ σ = 1 := by
      change (ρ.ρ σ).baseChange k'' = 1
      rw [hσ, LinearMap.baseChange_one]
    change (ρ.residual.ρ σ).baseChange (AlgebraicClosure κ) = 1
    rw [h1, LinearMap.baseChange_one]
  · rw [charpoly_matForm]
    change ((ρ.residual.ρ σ).baseChange (AlgebraicClosure κ)).charpoly = _
    rw [LinearMap.charpoly_baseChange]
    change ((ρ.ρ σ).baseChange k'').charpoly.map (algebraMap k'' (AlgebraicClosure κ)) = _
    rw [LinearMap.charpoly_baseChange, hcp]
    simp only [Polynomial.map_add, Polynomial.map_sub, Polynomial.map_mul, Polynomial.map_pow,
      Polynomial.map_X, Polynomial.map_C]
    have hu : algebraMap k'' (AlgebraicClosure κ) (algebraMap O'' k'' (ψ u)) = algebraMap κ _ (φ₀ u) := he u
    have hv : algebraMap k'' (AlgebraicClosure κ) (algebraMap O'' k'' (ψ v)) = algebraMap κ _ (φ₀ v) := he v
    rw [hu, hv]

theorem isIntegral_dirichlet {N : ℕ} [NeZero N] (ε : DirichletCharacter ℂ N) (x : ZMod N) :
    IsIntegral ℤ (ε x) := by
  by_cases hx : IsUnit x
  · obtain ⟨u, rfl⟩ := hx
    have hpow : (ε u) ^ (N.totient) = 1 := by
      rw [← map_pow, ← Units.val_pow_eq_pow_val, ZMod.pow_totient, Units.val_one, map_one]
    have hpos : 0 < N.totient := Nat.totient_pos.mpr (NeZero.pos N)
    exact IsIntegral.of_pow hpos (by rw [hpow]; exact isIntegral_one)
  · rw [MulChar.map_nonunit ε hx]; exact isIntegral_zero

theorem solution' (N : ℕ) [NeZero N] (ε : DirichletCharacter ℂ N)
    (g : CuspForm (Gamma1 N) 2) (hg : g ≠ 0) (hεg : CuspForm.HasNebentypus ε g)
    (b : ℕ → ℂ)
    (hT : ∀ p : ℕ, p.Prime → ¬ p ∣ N → ∀ n : ℕ,
        ModularFormClass.qCoeff g (p * n) +
            ε (p : ZMod N) * (p : ℂ) *
              (if p ∣ n then ModularFormClass.qCoeff g (n / p) else 0) =
          b p * ModularFormClass.qCoeff g n)
    (S : Finset ℕ) (R : Subalgebra ℤ ℂ)
    (hR : ∀ p : ℕ, p.Prime → ¬ p ∣ N → p ∉ S → b p ∈ R) (hε : ∀ x : ZMod N, ε x ∈ R)
    (κ : Type) [Field κ] [Finite κ] (φ : R →+* κ) :
    ∃ ρ : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) →* GL (Fin 2) κ, GaloisFactorsThroughFiniteLevel ρ ∧
      (Deformation.matrixRepresentation ρ).IsSemisimpleRepresentation ∧
      ∀ (p : ℕ) (hp : p.Prime) (hpN : ¬ p ∣ N), (p : κ) ≠ 0 →
        ∀ A : ValuationSubring (AlgebraicClosure ℚ), A.LiesOverPrime p →
          (∀ σ ∈ A.inertiaSubgroupIn ℚ, ρ σ = 1) ∧
          ∀ (hpS : p ∉ S) (σ : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)), A.IsFrobeniusAt σ p →
            ((ρ σ : GL (Fin 2) κ) : Matrix (Fin 2) (Fin 2) κ).charpoly =
              X ^ 2 - C (φ ⟨b p, hR p hp hpN hpS⟩) * X +
                C (φ ⟨ε (p : ZMod N), hε _⟩ * (p : κ)) := by
  classical

  obtain ⟨ℓ, hℓchar⟩ := CharP.exists κ
  haveI := hℓchar
  have hℓ : ℓ.Prime := (CharP.char_is_prime_or_zero κ ℓ).resolve_right (CharP.char_ne_zero_of_finite κ ℓ)
  haveI : Fact ℓ.Prime := ⟨hℓ⟩

  have hT' : ∀ p : ℕ, p.Prime → ¬ p ∣ N → ∀ n : ℕ,
      ModularFormClass.qCoeff g (p * n) +
          ε (p : ZMod N) * (p : ℂ) ^ ((2 : ℤ) - 1) *
            (if p ∣ n then ModularFormClass.qCoeff g (n / p) else 0) =
        b p * ModularFormClass.qCoeff g n := by
    intro p hp hpN n
    have : ((p : ℂ)) ^ ((2 : ℤ) - 1) = p := by norm_num
    rw [this]; exact hT p hp hpN n
  obtain ⟨M, instM, εM, h, hMN, hprim, hpack⟩ :=
    CuspForm.exists_isPrimitiveForm_of_hasNebentypus_qCoeff_hecke_eigen N 2 ε g hg hεg b hT'
  have hh : CuspForm.IsEigenformWith εM h := hprim.isEigenformWith

  let Gen : Set ℂ := {z | ∃ p : ℕ, p.Prime ∧ ¬ p ∣ N ∧ p ∉ S ∧ z = b p} ∪ Set.range (fun x : ZMod N => ε x)
  let R₀ : Subalgebra ℤ ℂ := Algebra.adjoin ℤ Gen
  have hR₀R : R₀ ≤ R := by
    refine Algebra.adjoin_le ?_
    rintro z (⟨p, hp, hpN, hpS, rfl⟩ | ⟨x, rfl⟩)
    · exact hR p hp hpN hpS
    · exact hε x

  let Ah : Subalgebra ℤ ℂ := Algebra.adjoin ℤ
    ((Set.range fun n : ℕ => ModularFormClass.qCoeff h n) ∪ Set.range fun u : (ZMod M)ˣ => εM (u : ZMod M))
  have hAhfg : (Subalgebra.toSubmodule Ah).FG := CuspForm.IsEigenformWith.fg_adjoin_qCoeff hh
  have hbmem : ∀ p : ℕ, p.Prime → ¬ p ∣ N → b p ∈ Ah := by
    intro p hp hpN
    rw [← (hpack p hp hpN).1]
    exact Algebra.subset_adjoin (Or.inl ⟨p, rfl⟩)
  have hGenInt : ∀ z ∈ Gen, IsIntegral ℤ z := by
    rintro z (⟨p, hp, hpN, -, rfl⟩ | ⟨x, rfl⟩)
    · exact IsIntegral.of_mem_of_fg Ah hAhfg _ (hbmem p hp hpN)
    · exact isIntegral_dirichlet ε x
  have hR₀int : ∀ z ∈ R₀, IsIntegral ℤ z := by
    intro z hz
    have : R₀ ≤ integralClosure ℤ ℂ := Algebra.adjoin_le fun z hz => hGenInt z hz
    exact this hz

  obtain ⟨tA, htA⟩ := hAhfg
  let Tset : Set ℂ := (↑tA : Set ℂ) ∪ Set.range (fun x : ZMod N => ε x)
  haveI : Finite Tset := (tA.finite_toSet.union (Set.finite_range _)).to_subtype
  have hTint : ∀ z ∈ Tset, IsIntegral ℚ z := by
    rintro z (hz | ⟨x, rfl⟩)
    · have hz' : z ∈ Ah := by
        have : z ∈ Submodule.span ℤ (↑tA : Set ℂ) := Submodule.subset_span hz
        rw [htA] at this; exact this
      exact (IsIntegral.of_mem_of_fg Ah ⟨tA, htA⟩ _ hz').tower_top
    · exact (isIntegral_dirichlet ε x).tower_top
  let K : IntermediateField ℚ ℂ := IntermediateField.adjoin ℚ Tset
  haveI : FiniteDimensional ℚ K := IntermediateField.finiteDimensional_adjoin hTint
  haveI : NumberField K := { to_charZero := inferInstance, to_finiteDimensional := inferInstance }
  have hGenK : Gen ⊆ (K : Set ℂ) := by
    rintro z (⟨p, hp, hpN, hpS, rfl⟩ | ⟨x, rfl⟩)
    ·
      have h1 : b p ∈ Submodule.span ℤ (↑tA : Set ℂ) := by rw [htA]; exact hbmem p hp hpN
      have h2 : Submodule.span ℤ (↑tA : Set ℂ) ≤ (K.toSubalgebra.toSubmodule).restrictScalars ℤ := by
        rw [Submodule.span_le]
        intro z hz
        exact IntermediateField.subset_adjoin ℚ Tset (Or.inl hz)
      exact h2 h1
    · exact IntermediateField.subset_adjoin ℚ Tset (Or.inr ⟨x, rfl⟩)
  have hR₀K : ∀ z ∈ R₀, z ∈ K := by
    intro z hz
    have : R₀ ≤ K.toSubalgebra.restrictScalars ℤ := Algebra.adjoin_le hGenK
    exact this hz

  let iK : R₀ →+* 𝓞 K :=
    { toFun := fun z => ⟨⟨z.1, hR₀K z.1 z.2⟩, by
        have hz : IsIntegral ℤ (z : ℂ) := hR₀int z.1 z.2
        have : IsIntegral ℤ ((⟨z.1, hR₀K z.1 z.2⟩ : K) : ℂ) := hz
        exact (isIntegral_algHom_iff (K.val.restrictScalars ℤ) Subtype.val_injective).mp this⟩
      map_one' := by ext; rfl
      map_mul' := fun _ _ => by ext; rfl
      map_zero' := by ext; rfl
      map_add' := fun _ _ => by ext; rfl }
  have hiK : Function.Injective iK := by
    intro x y hxy
    have := congrArg (fun z : 𝓞 K => ((z : K) : ℂ)) hxy
    exact Subtype.ext this

  let φ₀ : R₀ →+* κ := φ.comp (Subalgebra.inclusion hR₀R).toRingHom
  have hφ₀ : ∀ z : R₀, φ₀ z = φ (Subalgebra.inclusion hR₀R z) := fun _ => rfl
  let P : Ideal R₀ := RingHom.ker φ₀
  have hP : P.IsMaximal := ker_isMaximal_of_finite φ₀
  have hℓP : ((ℓ : ℕ) : R₀) ∈ P := by
    rw [RingHom.mem_ker, map_natCast]; exact CharP.cast_eq_zero κ ℓ

  obtain ⟨O', _, _, _, _, _, _, ι, hι⟩ := exists_coefficientRing K iK hiK P hP
  have hℓO' : ((ℓ : ℕ) : O') ∈ IsLocalRing.maximalIdeal O' := by
    rw [← map_natCast ι]; exact (hι _).mpr hℓP

  let S₁ : Finset ℕ := S ∪ N.primeFactors ∪ {ℓ}
  have hℓS₁ : ℓ ∈ S₁ := Finset.mem_union_right _ (Finset.mem_singleton_self ℓ)
  have hS₁ : ∀ p : ℕ, p.Prime → p ∉ S₁ → ¬ p ∣ N ∧ p ∉ S ∧ p ≠ ℓ := by
    intro p hp hpS₁
    simp only [S₁, Finset.mem_union, Finset.mem_singleton, not_or, Nat.mem_primeFactors] at hpS₁
    exact ⟨fun h => hpS₁.1.2 ⟨hp, h, NeZero.ne N⟩, hpS₁.1.1, hpS₁.2⟩
  let bR : ℕ → R₀ := fun p =>
    if hp : p.Prime ∧ ¬ p ∣ N ∧ p ∉ S then ⟨b p, Algebra.subset_adjoin (Or.inl ⟨p, hp.1, hp.2.1, hp.2.2, rfl⟩)⟩
    else 0
  let eR : ℕ → R₀ := fun p => ⟨ε (p : ZMod N), Algebra.subset_adjoin (Or.inr ⟨(p : ZMod N), rfl⟩)⟩
  have hbR : ∀ p : ℕ, p.Prime → ¬ p ∣ M → p ∉ S₁ → (R₀.val : R₀ →+* ℂ) (bR p) = ModularFormClass.qCoeff h p := by
    intro p hp _ hpS₁
    obtain ⟨hpN, hpS, -⟩ := hS₁ p hp hpS₁
    simp only [bR, dif_pos (show p.Prime ∧ ¬ p ∣ N ∧ p ∉ S from ⟨hp, hpN, hpS⟩)]
    exact ((hpack p hp hpN).1).symm
  have heR : ∀ p : ℕ, p.Prime → ¬ p ∣ M → p ∉ S₁ → (R₀.val : R₀ →+* ℂ) (eR p) = εM (p : ZMod M) := by
    intro p hp _ hpS₁
    obtain ⟨hpN, -, -⟩ := hS₁ p hp hpS₁
    exact ((hpack p hp hpN).2).symm
  obtain ⟨O'', _, _, _, _, _, _, _, _, hloc, hinj, ρ, hcp, hunr⟩ :=
    hh.exists_galoisRepAdic_charpoly_frobenius_eq_and_isUnramifiedAt ℓ S₁ hℓS₁ O' hℓO' R₀
      (R₀.val : R₀ →+* ℂ) Subtype.val_injective ι bR eR hbR heR

  let ψ : R₀ →+* O'' := (algebraMap O' O'').comp ι
  have hψ : ∀ x, φ₀ x = 0 → ψ x ∈ IsLocalRing.maximalIdeal O'' := by
    intro x hx
    haveI := hloc
    exact map_nonunit (algebraMap O' O'') (ι x) ((hι x).mpr hx)
  obtain ⟨ρΩ, hΩlevel, hΩone, hΩcp⟩ := exists_matrixRep_of_galoisRepAdic φ₀ O'' ψ hψ ρ
  set Ω := AlgebraicClosure κ
  let ιΩ : κ →+* Ω := algebraMap κ Ω

  have hΩfrob : ∀ p : ℕ, p.Prime → p ∉ S₁ →
      ∀ A : ValuationSubring (AlgebraicClosure ℚ), A.LiesOverPrime p →
        ∀ σ : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ), A.IsFrobeniusAt σ p →
          (ρΩ σ : Matrix (Fin 2) (Fin 2) Ω).charpoly =
            X ^ 2 - C (ιΩ (φ₀ (bR p))) * X + C (ιΩ (φ₀ (eR p * p))) := by
    intro p hp hpS₁ A hA σ hσ
    obtain ⟨hpN, -, -⟩ := hS₁ p hp hpS₁
    have hpM : ¬ p ∣ M := fun h => hpN (h.trans hMN)
    apply hΩcp σ (bR p) (eR p * p)
    rw [hcp p hp hpM hpS₁ A hA σ hσ]
    simp [ψ, map_mul, map_natCast]

  have hfrobmem : ∀ p : ℕ, p.Prime → p ∉ S₁ →
      ∀ A : ValuationSubring (AlgebraicClosure ℚ), A.LiesOverPrime p →
        ∀ σ : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ), A.IsFrobeniusAt σ p →
          Matrix.trace (ρΩ σ : Matrix (Fin 2) (Fin 2) Ω) ∈ ιΩ.range ∧
            Matrix.det (ρΩ σ : Matrix (Fin 2) (Fin 2) Ω) ∈ ιΩ.range := by
    intro p hp hpS₁ A hA σ hσ
    have h := hΩfrob p hp hpS₁ A hA σ hσ
    exact ⟨⟨_, (trace_eq_of_charpoly_eq _ _ _ h).symm⟩, ⟨_, (det_eq_of_charpoly_eq _ _ _ h).symm⟩⟩
  obtain ⟨ρ₀, h₀level, h₀ss, h₀one, h₀cp⟩ :=
    GaloisRep.exists_isSemisimpleRepresentation_charpoly_map_eq_of_trace_det_frobenius_mem_range κ Ω ιΩ ρΩ
      hΩlevel S₁ hfrobmem

  refine ⟨ρ₀, h₀level, h₀ss, fun p hp hpN hpκ A hA => ⟨fun σ hσ => ?_, fun hpS σ hσ => ?_⟩⟩
  ·
    have hpℓ : p ≠ ℓ := by rintro rfl; exact hpκ (CharP.cast_eq_zero κ p)
    have hpM : ¬ p ∣ M := fun h => hpN (h.trans hMN)
    exact h₀one σ (hΩone σ (hunr p hp hpM hpℓ A hA σ hσ))
  · have hpℓ : p ≠ ℓ := by rintro rfl; exact hpκ (CharP.cast_eq_zero κ p)
    have hpS₁ : p ∉ S₁ := by
      simp only [S₁, Finset.mem_union, Finset.mem_singleton, not_or, Nat.mem_primeFactors]
      exact ⟨⟨hpS, fun h => hpN h.2.1⟩, hpℓ⟩
    apply Polynomial.map_injective ιΩ ιΩ.injective
    rw [← Matrix.charpoly_map, h₀cp σ, hΩfrob p hp hpS₁ A hA σ hσ]
    simp only [Polynomial.map_add, Polynomial.map_sub, Polynomial.map_mul, Polynomial.map_pow,
      Polynomial.map_X, Polynomial.map_C, map_mul, map_natCast, Polynomial.map_natCast]
    have hb : φ₀ (bR p) = φ ⟨b p, hR p hp hpN hpS⟩ := by
      rw [hφ₀]
      simp only [bR, dif_pos (show p.Prime ∧ ¬ p ∣ N ∧ p ∉ S from ⟨hp, hpN, hpS⟩)]
      rfl
    have he : φ₀ (eR p) = φ ⟨ε (p : ZMod N), hε _⟩ := by rw [hφ₀]; rfl
    rw [hb, he]

end DSW2

open CongruenceSubgroup Polynomial in
open scoped MatrixGroups in
theorem solution
    (N : ℕ) [NeZero N] (ε : DirichletCharacter ℂ N)
    (g : CuspForm (Gamma1 N) 2) (hg : g ≠ 0) (hεg : CuspForm.HasNebentypus ε g)
    (b : ℕ → ℂ)
    (hT : ∀ p : ℕ, p.Prime → ¬ p ∣ N → ∀ n : ℕ,
        ModularFormClass.qCoeff g (p * n) +
            ε (p : ZMod N) * (p : ℂ) *
              (if p ∣ n then ModularFormClass.qCoeff g (n / p) else 0) =
          b p * ModularFormClass.qCoeff g n)
    (S : Finset ℕ) (R : Subalgebra ℤ ℂ)
    (hR : ∀ p : ℕ, p.Prime → ¬ p ∣ N → p ∉ S → b p ∈ R) (hε : ∀ x : ZMod N, ε x ∈ R)
    (κ : Type) [Field κ] [Finite κ] (φ : R →+* κ) :
    ∃ ρ : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) →* GL (Fin 2) κ, GaloisFactorsThroughFiniteLevel ρ ∧
      (Deformation.matrixRepresentation ρ).IsSemisimpleRepresentation ∧
      ∀ (p : ℕ) (hp : p.Prime) (hpN : ¬ p ∣ N), (p : κ) ≠ 0 →
        ∀ A : ValuationSubring (AlgebraicClosure ℚ), A.LiesOverPrime p →
          (∀ σ ∈ A.inertiaSubgroupIn ℚ, ρ σ = 1) ∧
          ∀ (hpS : p ∉ S) (σ : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)), A.IsFrobeniusAt σ p →
            ((ρ σ : GL (Fin 2) κ) : Matrix (Fin 2) (Fin 2) κ).charpoly =
              X ^ 2 - C (φ ⟨b p, hR p hp hpN hpS⟩) * X +
                C (φ ⟨ε (p : ZMod N), hε _⟩ * (p : κ)) :=
  DSW2.solution' N ε g hg hεg b hT S R hR hε κ φ
