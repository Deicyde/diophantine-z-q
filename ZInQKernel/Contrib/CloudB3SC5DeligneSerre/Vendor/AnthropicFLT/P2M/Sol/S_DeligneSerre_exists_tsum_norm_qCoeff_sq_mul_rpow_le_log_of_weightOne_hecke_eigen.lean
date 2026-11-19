/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: P2M.Sol.S_DeligneSerre_exists_tsum_norm_qCoeff_sq_mul_rpow_le_log_of_weightOne_hecke_eigen (git blob c4594ee5e921ed0bee8b616348c58d83e29b6ace, sha256 ff80b2b5caaf959568143114a75548c103d2ec6d61fdb0f9a8cd93117ae05453).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_FLTPrelim_Modularity
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_CuspForm_PrimitiveFormGamma1
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AutomorphicForm_ProductionPinsGeneral
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_AutomorphicForm_exists_tsum_norm_a_sq_mul_rpow_absNorm_le_log_of_isArithGenuineCuspRealizable
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_AutomorphicForm_exists_isGenuineCuspRealizationAt_hasNewvectorConductor_adelicSpan_factorization_of_isPrimitiveForm_weightOne
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_AutomorphicForm_SiegelCovering_coversModCentre_productionPinsGeneral_D_rat
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_CuspForm_exists_isPrimitiveForm_of_qCoeff_hecke_eigen
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_IsDedekindDomain_HeightOneSpectrum_exists_prime_and_asIdeal_eq_span_ringOfIntegers_rat

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

namespace P2MW.S_DeligneSerre_exists_tsum_norm_qCoeff_sq_mul_rpow_le_log_of_weightOne_hecke_eigen

set_option autoImplicit false

open CongruenceSubgroup IsDedekindDomain NumberField AutomorphicForm
open NumberField.AdelicLevel NumberField.AdelicBox AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering

open scoped MatrixGroups

noncomputable section

namespace RankinWeightOneReduction

theorem prime_eq_of_natCast_mem_span {p q : ℕ} (hp : p.Prime) (hq : q.Prime)
    (h : (p : 𝓞 ℚ) ∈ Ideal.span {(q : 𝓞 ℚ)}) : p = q := by
  have hdvd : (q : 𝓞 ℚ) ∣ (p : 𝓞 ℚ) := Ideal.mem_span_singleton.mp h
  have hdvd' : ((q : ℤ)) ∣ (p : ℤ) := by
    have := map_dvd (Rat.ringOfIntegersEquiv : 𝓞 ℚ ≃+* ℤ) hdvd
    simpa [map_natCast] using this
  have : q ∣ p := Int.natCast_dvd_natCast.mp hdvd'
  exact ((Nat.prime_dvd_prime_iff_eq hq hp).mp this).symm

theorem prime_natCast_ringOfIntegers_rat {p : ℕ} (hp : p.Prime) : Prime (p : 𝓞 ℚ) := by
  have h1 : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
  have h2 : (Rat.ringOfIntegersEquiv.symm : ℤ ≃+* 𝓞 ℚ) (p : ℤ) = (p : 𝓞 ℚ) := by
    simp [map_natCast]
  rw [← h2]
  exact (MulEquiv.prime_iff (Rat.ringOfIntegersEquiv.symm : ℤ ≃+* 𝓞 ℚ)).mpr h1

def primePlace (p : ℕ) (hp : p.Prime) : HeightOneSpectrum (𝓞 ℚ) where
  asIdeal := Ideal.span {(p : 𝓞 ℚ)}
  isPrime := (Ideal.span_singleton_prime (prime_natCast_ringOfIntegers_rat hp).ne_zero).mpr
    (prime_natCast_ringOfIntegers_rat hp)
  ne_bot := mt Ideal.span_singleton_eq_bot.mp (prime_natCast_ringOfIntegers_rat hp).ne_zero

theorem primePlace_asIdeal (p : ℕ) (hp : p.Prime) :
    (primePlace p hp).asIdeal = Ideal.span {(p : 𝓞 ℚ)} := rfl

theorem absNorm_span_natCast_ringOfIntegers_rat (p : ℕ) :
    Ideal.absNorm (Ideal.span {(p : 𝓞 ℚ)}) = p := by
  rw [Ideal.absNorm_span_singleton]
  have : (p : 𝓞 ℚ) = algebraMap ℤ (𝓞 ℚ) (p : ℤ) := by simp
  rw [this, Algebra.norm_algebraMap, RingOfIntegers.rank, Module.finrank_self]
  simp

def primeOf (v : HeightOneSpectrum (𝓞 ℚ)) : ℕ :=
  (HeightOneSpectrum.exists_prime_and_asIdeal_eq_span_ringOfIntegers_rat v).choose

theorem primeOf_prime (v : HeightOneSpectrum (𝓞 ℚ)) : (primeOf v).Prime :=
  (HeightOneSpectrum.exists_prime_and_asIdeal_eq_span_ringOfIntegers_rat v).choose_spec.1

theorem asIdeal_eq_span_primeOf (v : HeightOneSpectrum (𝓞 ℚ)) :
    v.asIdeal = Ideal.span {(primeOf v : 𝓞 ℚ)} :=
  (HeightOneSpectrum.exists_prime_and_asIdeal_eq_span_ringOfIntegers_rat v).choose_spec.2

theorem primeOf_eq_of_natCast_mem {v : HeightOneSpectrum (𝓞 ℚ)} {p : ℕ} (hp : p.Prime)
    (h : (p : 𝓞 ℚ) ∈ v.asIdeal) : primeOf v = p := by
  rw [asIdeal_eq_span_primeOf] at h
  exact (prime_eq_of_natCast_mem_span hp (primeOf_prime v) h).symm

theorem primeOf_primePlace {p : ℕ} (hp : p.Prime) : primeOf (primePlace p hp) = p :=
  primeOf_eq_of_natCast_mem hp (Ideal.mem_span_singleton_self _)

theorem primePlace_inj {p q : ℕ} (hp : p.Prime) (hq : q.Prime)
    (h : primePlace p hp = primePlace q hq) : p = q := by
  have hmem : (p : 𝓞 ℚ) ∈ (primePlace q hq).asIdeal := h ▸ Ideal.mem_span_singleton_self _
  exact prime_eq_of_natCast_mem_span hp hq hmem

def placeOf (N : ℕ) (p : {p : ℕ // p.Prime ∧ ¬ p ∣ N}) : HeightOneSpectrum (𝓞 ℚ) :=
  primePlace p.1 p.2.1

theorem placeOf_injective (N : ℕ) : Function.Injective (placeOf N) := fun p q hpq =>
  Subtype.ext (primePlace_inj p.2.1 q.2.1 hpq)

theorem primeOf_placeOf (N : ℕ) (p : {p : ℕ // p.Prime ∧ ¬ p ∣ N}) :
    primeOf (placeOf N p) = (p : ℕ) :=
  primeOf_primePlace p.2.1

theorem absNorm_placeOf (N : ℕ) (p : {p : ℕ // p.Prime ∧ ¬ p ∣ N}) :
    Ideal.absNorm (placeOf N p).asIdeal = (p : ℕ) :=
  absNorm_span_natCast_ringOfIntegers_rat p.1

theorem asIdeal_dvd_span_of_primeOf_dvd {v : HeightOneSpectrum (𝓞 ℚ)} {M : ℕ}
    (h : primeOf v ∣ M) : v.asIdeal ∣ Ideal.span {(M : 𝓞 ℚ)} := by
  rw [Ideal.dvd_span_singleton, asIdeal_eq_span_primeOf, Ideal.mem_span_singleton]
  exact Nat.cast_dvd_cast h

theorem norm_dirichletCharacter_apply_prime_eq_one {M : ℕ} (ψ : DirichletCharacter ℂ M)
    {p : ℕ} (hp : p.Prime) (h : ¬ p ∣ M) : ‖ψ (p : ZMod M)‖ = 1 := by
  have hc : Nat.Coprime p M := (Nat.Prime.coprime_iff_not_dvd hp).mpr h
  have := ψ.unit_norm_eq_one (ZMod.unitOfCoprime p hc)
  simpa [ZMod.coe_unitOfCoprime] using this

def thetaOf {M : ℕ} (ψ : DirichletCharacter ℂ M) (g : CuspForm (Gamma1 M) 1) :
    HeckeEigensystem ℚ ℂ where
  level := ⊤
  level_ne_bot := top_ne_bot
  a := fun v => ModularFormClass.qCoeff g (primeOf v)
  b := fun v => ψ (primeOf v : ZMod M)

@[scoped simp] theorem thetaOf_a {M : ℕ} (ψ : DirichletCharacter ℂ M) (g : CuspForm (Gamma1 M) 1)
    (v : HeightOneSpectrum (𝓞 ℚ)) : (thetaOf ψ g).a v = ModularFormClass.qCoeff g (primeOf v) :=
  rfl

@[scoped simp] theorem thetaOf_b {M : ℕ} (ψ : DirichletCharacter ℂ M) (g : CuspForm (Gamma1 M) 1)
    (v : HeightOneSpectrum (𝓞 ℚ)) : (thetaOf ψ g).b v = ψ (primeOf v : ZMod M) :=
  rfl

theorem exists_agrees_isArithGenuineCuspRealizable_of_isPrimitiveForm
    {M : ℕ} [NeZero M] (ψ : DirichletCharacter ℂ M) (g : CuspForm (Gamma1 M) 1)
    (hg : CuspForm.IsPrimitiveForm ψ g) :
    ∃ Θ' : HeckeEigensystem ℚ ℂ, Θ'.AgreesAwayFromFinite (thetaOf ψ g) ∧
      IsArithGenuineCuspRealizable ℚ (productionPinsGeneral ℚ) Θ' := by
  have hΘ : ∃ S : Finset ℕ, ∀ p : ℕ, p.Prime → p ∉ S → ¬ p ∣ M →
      ∀ v : HeightOneSpectrum (𝓞 ℚ), (p : 𝓞 ℚ) ∈ v.asIdeal →
        ModularFormClass.qCoeff g p = (thetaOf ψ g).a v ∧ ψ (p : ZMod M) = (thetaOf ψ g).b v := by
    refine ⟨∅, fun p hp _ _ v hv => ?_⟩
    have h := primeOf_eq_of_natCast_mem hp hv
    simp [h]
  have hcov : CoversModCentre ℚ
      (⋃ x ∈ classRepTranslates ℚ, (· * x) '' centreCutSiegelSet ℚ (1/2 : ℝ) 1 (1/2) 2) :=
    SiegelCovering.coversModCentre_productionPinsGeneral_D_rat
  obtain ⟨Θ', hagree, R', hgen, -⟩ :=
    AutomorphicForm.exists_isGenuineCuspRealizationAt_hasNewvectorConductor_adelicSpan_factorization_of_isPrimitiveForm_weightOne
      (1/2 : ℝ) 1 (1/2) 2 (classRepTranslates ℚ) (by norm_num) (by norm_num) (by norm_num) hcov
      M ψ g hg (thetaOf ψ g) hΘ
  exact ⟨Θ', hagree, R', hgen⟩

theorem main
    (N : ℕ) [NeZero N] (ε : DirichletCharacter ℂ N) (f : CuspForm (Gamma1 N) 1)
    (hf₁ : ModularFormClass.qCoeff f 1 = 1)
    (hT : ∀ p : ℕ, p.Prime → ¬ p ∣ N → ∀ n : ℕ,
        ModularFormClass.qCoeff f (p * n) +
            ε (p : ZMod N) * (if p ∣ n then ModularFormClass.qCoeff f (n / p) else 0) =
          ModularFormClass.qCoeff f p * ModularFormClass.qCoeff f n) :
    ∃ C : ℝ, ∀ s : ℝ, 1 < s → s < 2 →
      Summable (fun p : {p : ℕ // p.Prime ∧ ¬ p ∣ N} =>
        ‖ModularFormClass.qCoeff f (p : ℕ)‖ ^ 2 * ((p : ℕ) : ℝ) ^ (-s)) ∧
      ∑' p : {p : ℕ // p.Prime ∧ ¬ p ∣ N},
          ‖ModularFormClass.qCoeff f (p : ℕ)‖ ^ 2 * ((p : ℕ) : ℝ) ^ (-s) ≤
        Real.log (1 / (s - 1)) + C := by
  classical

  obtain ⟨M, instM, ψ, g, -, hg, hgf⟩ :=
    CuspForm.exists_isPrimitiveForm_of_qCoeff_hecke_eigen N 1 f hf₁ (fun p => ε (p : ZMod N)) hT

  obtain ⟨Θ', ⟨S₁, hS₁⟩, hreal⟩ :=
    exists_agrees_isArithGenuineCuspRealizable_of_isPrimitiveForm ψ g hg

  have hMne : Ideal.span {(M : 𝓞 ℚ)} ≠ 0 := by
    rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
    exact_mod_cast (NeZero.ne M)
  have hBfin : {v : HeightOneSpectrum (𝓞 ℚ) | v.asIdeal ∣ Ideal.span {(M : 𝓞 ℚ)}}.Finite :=
    Ideal.finite_factors hMne
  have hb : ∀ v : HeightOneSpectrum (𝓞 ℚ), v ∉ S₁ ∪ hBfin.toFinset → ‖Θ'.b v‖ = 1 := by
    intro v hv
    simp only [Finset.mem_union, Set.Finite.mem_toFinset, Set.mem_setOf_eq, not_or] at hv
    rw [(hS₁ v hv.1).2, thetaOf_b]
    refine norm_dirichletCharacter_apply_prime_eq_one ψ (primeOf_prime v) fun hd => ?_
    exact hv.2 (asIdeal_dvd_span_of_primeOf_dvd hd)

  obtain ⟨C₀, hC₀⟩ :=
    AutomorphicForm.exists_tsum_norm_a_sq_mul_rpow_absNorm_le_log_of_isArithGenuineCuspRealizable
      Θ' hreal (S₁ ∪ hBfin.toFinset) hb

  set K : ℝ := ∑ v ∈ S₁, ‖ModularFormClass.qCoeff f (primeOf v)‖ ^ 2 with hK
  refine ⟨C₀ + K, fun s hs₁ hs₂ => ?_⟩
  obtain ⟨hsum, hle⟩ := hC₀ s hs₁ hs₂

  set G : HeightOneSpectrum (𝓞 ℚ) → ℝ :=
    fun v => ‖Θ'.a v‖ ^ 2 * (Ideal.absNorm v.asIdeal : ℝ) ^ (-s)
  set H : HeightOneSpectrum (𝓞 ℚ) → ℝ :=
    fun v => if v ∈ S₁ then ‖ModularFormClass.qCoeff f (primeOf v)‖ ^ 2 else 0
  have hG0 : ∀ v, 0 ≤ G v := fun v =>
    mul_nonneg (sq_nonneg _) (Real.rpow_nonneg (Nat.cast_nonneg _) _)
  have hH_of_mem : ∀ v, v ∈ S₁ → H v = ‖ModularFormClass.qCoeff f (primeOf v)‖ ^ 2 :=
    fun v hv => if_pos hv
  have hH_of_not_mem : ∀ v, v ∉ S₁ → H v = 0 := fun v hv => if_neg hv
  have hH0 : ∀ v, 0 ≤ H v := fun v => by
    by_cases hv : v ∈ S₁
    · rw [hH_of_mem v hv]; exact sq_nonneg _
    · rw [hH_of_not_mem v hv]
  have hHsum : Summable H := summable_of_ne_finset_zero (s := S₁) hH_of_not_mem
  have hHtsum : ∑' v, H v = K := by
    rw [tsum_eq_sum (s := S₁) hH_of_not_mem, hK]
    exact Finset.sum_congr rfl hH_of_mem
  have hGsum : Summable G := hsum
  have hGle : ∑' v, G v ≤ Real.log (1 / (s - 1)) + C₀ := hle
  have hGH : Summable (fun v => G v + H v) := hGsum.add hHsum

  have hF_le : ∀ p : {p : ℕ // p.Prime ∧ ¬ p ∣ N},
      ‖ModularFormClass.qCoeff f (p : ℕ)‖ ^ 2 * ((p : ℕ) : ℝ) ^ (-s) ≤
        G (placeOf N p) + H (placeOf N p) := by
    intro p
    by_cases hp : placeOf N p ∈ S₁
    · have h1 : ‖ModularFormClass.qCoeff f (p : ℕ)‖ ^ 2 * ((p : ℕ) : ℝ) ^ (-s) ≤
          ‖ModularFormClass.qCoeff f (p : ℕ)‖ ^ 2 :=
        mul_le_of_le_one_right (sq_nonneg _)
          (Real.rpow_le_one_of_one_le_of_nonpos (by exact_mod_cast p.2.1.one_lt.le)
            (by linarith))
      have h2 : H (placeOf N p) = ‖ModularFormClass.qCoeff f (p : ℕ)‖ ^ 2 := by
        rw [hH_of_mem _ hp, primeOf_placeOf]
      linarith [hG0 (placeOf N p)]
    · have ha : Θ'.a (placeOf N p) = ModularFormClass.qCoeff f (p : ℕ) := by
        rw [(hS₁ _ hp).1, thetaOf_a, primeOf_placeOf]
        exact (hgf p.1 p.2.1 p.2.2).1
      have hn : (Ideal.absNorm (placeOf N p).asIdeal : ℝ) = ((p : ℕ) : ℝ) := by
        rw [absNorm_placeOf]
      have hG : G (placeOf N p) = ‖ModularFormClass.qCoeff f (p : ℕ)‖ ^ 2 * ((p : ℕ) : ℝ) ^ (-s) := by
        show ‖Θ'.a (placeOf N p)‖ ^ 2 * (Ideal.absNorm (placeOf N p).asIdeal : ℝ) ^ (-s) = _
        rw [ha, hn]
      rw [hH_of_not_mem _ hp, add_zero, hG]
  have hF0 : ∀ p : {p : ℕ // p.Prime ∧ ¬ p ∣ N},
      0 ≤ ‖ModularFormClass.qCoeff f (p : ℕ)‖ ^ 2 * ((p : ℕ) : ℝ) ^ (-s) := fun p =>
    mul_nonneg (sq_nonneg _) (Real.rpow_nonneg (Nat.cast_nonneg _) _)
  have hFsum : Summable (fun p : {p : ℕ // p.Prime ∧ ¬ p ∣ N} =>
      ‖ModularFormClass.qCoeff f (p : ℕ)‖ ^ 2 * ((p : ℕ) : ℝ) ^ (-s)) :=
    Summable.of_nonneg_of_le hF0 hF_le (hGH.comp_injective (placeOf_injective N))
  refine ⟨hFsum, ?_⟩
  calc ∑' p : {p : ℕ // p.Prime ∧ ¬ p ∣ N},
          ‖ModularFormClass.qCoeff f (p : ℕ)‖ ^ 2 * ((p : ℕ) : ℝ) ^ (-s)
        ≤ ∑' v, (G v + H v) :=
          Summable.tsum_le_tsum_of_inj (placeOf N) (placeOf_injective N)
            (fun c _ => add_nonneg (hG0 c) (hH0 c)) hF_le hFsum hGH
    _ = ∑' v, G v + ∑' v, H v := hGsum.tsum_add hHsum
    _ ≤ Real.log (1 / (s - 1)) + C₀ + K := by rw [hHtsum]; linarith
    _ = Real.log (1 / (s - 1)) + (C₀ + K) := by ring

end RankinWeightOneReduction
open scoped _root_.P2MW.S_DeligneSerre_exists_tsum_norm_qCoeff_sq_mul_rpow_le_log_of_weightOne_hecke_eigen.RankinWeightOneReduction

end
open scoped _root_.P2MW.S_DeligneSerre_exists_tsum_norm_qCoeff_sq_mul_rpow_le_log_of_weightOne_hecke_eigen.RankinWeightOneReduction

open CongruenceSubgroup
open scoped MatrixGroups

theorem solution
    (N : ℕ) [NeZero N] (ε : DirichletCharacter ℂ N) (f : CuspForm (Gamma1 N) 1)
    (hf₁ : ModularFormClass.qCoeff f 1 = 1)
    (hT : ∀ p : ℕ, p.Prime → ¬ p ∣ N → ∀ n : ℕ,
        ModularFormClass.qCoeff f (p * n) +
            ε (p : ZMod N) * (if p ∣ n then ModularFormClass.qCoeff f (n / p) else 0) =
          ModularFormClass.qCoeff f p * ModularFormClass.qCoeff f n) :
    ∃ C : ℝ, ∀ s : ℝ, 1 < s → s < 2 →
      Summable (fun p : {p : ℕ // p.Prime ∧ ¬ p ∣ N} =>
        ‖ModularFormClass.qCoeff f (p : ℕ)‖ ^ 2 * ((p : ℕ) : ℝ) ^ (-s)) ∧
      ∑' p : {p : ℕ // p.Prime ∧ ¬ p ∣ N},
          ‖ModularFormClass.qCoeff f (p : ℕ)‖ ^ 2 * ((p : ℕ) : ℝ) ^ (-s) ≤
        Real.log (1 / (s - 1)) + C :=
  RankinWeightOneReduction.main N ε f hf₁ hT
