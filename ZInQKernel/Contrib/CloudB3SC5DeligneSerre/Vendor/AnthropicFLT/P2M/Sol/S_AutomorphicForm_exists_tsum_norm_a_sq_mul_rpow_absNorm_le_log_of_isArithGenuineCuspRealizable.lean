/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: P2M.Sol.S_AutomorphicForm_exists_tsum_norm_a_sq_mul_rpow_absNorm_le_log_of_isArithGenuineCuspRealizable (git blob 70fc7bbd721c36aa455c6b8ae158938833bc9ca2, sha256 94be378e32324138b2fea0b578f28c8a30d0f2aa6caea8dddf58b02bcfbc800e).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AutomorphicForm_ProductionPinsGeneral
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_LanglandsTunnell_RankinSelbergEuler
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_AutomorphicForm_exists_finset_forall_lt_one_meromorphicOn_meromorphicOrderAt_one_eq_neg_one_analyticAt_hasProd_rsEulerPoly_self
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_LanglandsTunnell_RankinSelberg_exists_nonneg_exp_tsum_mul_pow_eq_inv_eval_rsEulerPoly_self_of_norm_eq_one
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_LanglandsTunnell_Converse_exists_finset_sq_eq_real_mul_b_and_norm_sq_lt_of_isArithGenuineCuspRealizable
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_LSeries_exists_nonneg_hasSum_tsum_mul_cpow_eq_lseries_of_le_mul_pow
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_LSeries_abscissaOfAbsConv_le_of_forall_analyticAt_ofReal_of_exp_lseries_eq
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_IsDedekindDomain_HeightOneSpectrum_exists_prime_and_asIdeal_eq_span_ringOfIntegers_rat
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_AutomorphicForm_SiegelCovering_coversModCentre_productionPinsGeneral_D_rat

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

namespace P2MW.S_AutomorphicForm_exists_tsum_norm_a_sq_mul_rpow_absNorm_le_log_of_isArithGenuineCuspRealizable

set_option autoImplicit false

open IsDedekindDomain NumberField AutomorphicForm
open NumberField.AdelicLevel NumberField.AdelicBox AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering

noncomputable section

namespace RS40R

open Complex Filter Topology
open scoped ComplexOrder

theorem absNorm_eq_prime (v : HeightOneSpectrum (𝓞 ℚ)) :
    ∃ p : ℕ, p.Prime ∧ Ideal.absNorm v.asIdeal = p ∧ v.asIdeal = Ideal.span {(p : 𝓞 ℚ)} := by
  obtain ⟨p, hp, hv⟩ := IsDedekindDomain.HeightOneSpectrum.exists_prime_and_asIdeal_eq_span_ringOfIntegers_rat v
  refine ⟨p, hp, ?_, hv⟩
  rw [hv, Ideal.absNorm_span_singleton]
  have : ((p : ℕ) : 𝓞 ℚ) = algebraMap ℤ (𝓞 ℚ) (p : ℤ) := by simp
  rw [this, Algebra.norm_algebraMap, NumberField.RingOfIntegers.rank, Module.finrank_self, pow_one,
    Int.natAbs_natCast]

theorem absNorm_prime (v : HeightOneSpectrum (𝓞 ℚ)) : (Ideal.absNorm v.asIdeal).Prime := by
  obtain ⟨p, hp, h, -⟩ := absNorm_eq_prime v
  rw [h]; exact hp

theorem absNorm_injective : Function.Injective fun v : HeightOneSpectrum (𝓞 ℚ) => Ideal.absNorm v.asIdeal := by
  intro v w h
  obtain ⟨p, hp, hpv, hv⟩ := absNorm_eq_prime v
  obtain ⟨q, hq, hqw, hw⟩ := absNorm_eq_prime w
  have hpq : p = q := by
    have : Ideal.absNorm v.asIdeal = Ideal.absNorm w.asIdeal := h
    rw [hpv, hqw] at this; exact this
  apply IsDedekindDomain.HeightOneSpectrum.ext
  rw [hv, hw, hpq]

theorem one_lt_absNorm (v : HeightOneSpectrum (𝓞 ℚ)) : (1 : ℝ) < (Ideal.absNorm v.asIdeal : ℝ) := by
  exact_mod_cast (absNorm_prime v).one_lt

def rterm (d : ℕ → ℝ) (σ : ℝ) (n : ℕ) : ℝ := if n = 0 then 0 else d n / (n : ℝ) ^ σ

theorem term_eq_rterm (d : ℕ → ℝ) (σ : ℝ) (n : ℕ) :
    LSeries.term (fun n => (d n : ℂ)) (σ : ℂ) n = ((rterm d σ n : ℝ) : ℂ) := by
  rw [LSeries.term_def, rterm]
  split_ifs with h
  · simp
  · push_cast
    rw [Complex.ofReal_cpow (Nat.cast_nonneg n)]
    norm_cast

theorem summable_rterm {d : ℕ → ℝ} {σ : ℝ} (h : LSeriesSummable (fun n => (d n : ℂ)) (σ : ℂ)) :
    Summable (rterm d σ) := by
  have : LSeries.term (fun n => (d n : ℂ)) (σ : ℂ) = fun n => ((rterm d σ n : ℝ) : ℂ) :=
    funext (term_eq_rterm d σ)
  unfold LSeriesSummable at h
  rw [this] at h
  exact Complex.summable_ofReal.1 h

theorem lseries_eq_ofReal_tsum (d : ℕ → ℝ) (σ : ℝ) :
    LSeries (fun n => (d n : ℂ)) (σ : ℂ) = ((∑' n, rterm d σ n : ℝ) : ℂ) := by
  rw [LSeries, Complex.ofReal_tsum]
  exact tsum_congr (term_eq_rterm d σ)

theorem rterm_nonneg {d : ℕ → ℝ} (hd : ∀ n, 0 ≤ d n) (σ : ℝ) (n : ℕ) : 0 ≤ rterm d σ n := by
  unfold rterm; split_ifs
  · exact le_rfl
  · exact div_nonneg (hd n) (Real.rpow_nonneg (Nat.cast_nonneg n) σ)

theorem rterm_anti {d : ℕ → ℝ} (hd : ∀ n, 0 ≤ d n) {σ σ' : ℝ} (hσ : σ' ≤ σ) (n : ℕ) :
    rterm d σ n ≤ rterm d σ' n := by
  unfold rterm; split_ifs with h
  · exact le_rfl
  · have hn : (1 : ℝ) ≤ n := by exact_mod_cast Nat.one_le_iff_ne_zero.2 h
    apply div_le_div_of_nonneg_left (hd n) (Real.rpow_pos_of_pos (by linarith) _)
    exact Real.rpow_le_rpow_of_exponent_le hn hσ

end RS40R

open RS40R in
theorem solution
    (Φ : AutomorphicForm.HeckeEigensystem ℚ ℂ)
    (hΦ : AutomorphicForm.IsArithGenuineCuspRealizable ℚ (AutomorphicForm.productionPinsGeneral ℚ) Φ)
    (SQ₀ : Finset (HeightOneSpectrum (𝓞 ℚ)))
    (hb : ∀ p : HeightOneSpectrum (𝓞 ℚ), p ∉ SQ₀ → ‖Φ.b p‖ = 1) :
    ∃ C : ℝ, ∀ σ : ℝ, 1 < σ → σ < 2 →
      Summable (fun p : HeightOneSpectrum (𝓞 ℚ) => ‖Φ.a p‖ ^ 2 * (Ideal.absNorm p.asIdeal : ℝ) ^ (-σ)) ∧
      ∑' p : HeightOneSpectrum (𝓞 ℚ), ‖Φ.a p‖ ^ 2 * (Ideal.absNorm p.asIdeal : ℝ) ^ (-σ) ≤
        Real.log (1 / (σ - 1)) + C := by
  classical

  have hcov : CoversModCentre ℚ (⋃ x ∈ classRepTranslates ℚ,
      (· * x) '' centreCutSiegelSet ℚ (1 / 2 : ℝ) 1 (1 / 2) 2) :=
    AutomorphicForm.SiegelCovering.coversModCentre_productionPinsGeneral_D_rat
  obtain ⟨S₁, hS₁⟩ :=
    AutomorphicForm.exists_finset_forall_lt_one_meromorphicOn_meromorphicOrderAt_one_eq_neg_one_analyticAt_hasProd_rsEulerPoly_self
      ℚ (1 / 2) 1 (1 / 2) 2 (classRepTranslates ℚ) (by norm_num) (by norm_num) (by norm_num) hcov Φ hΦ

  obtain ⟨S₂, hS₂⟩ :=
    LanglandsTunnell.Converse.exists_finset_sq_eq_real_mul_b_and_norm_sq_lt_of_isArithGenuineCuspRealizable Φ hΦ
  set S : Finset (HeightOneSpectrum (𝓞 ℚ)) := S₁ ∪ S₂ ∪ SQ₀ with hSdef
  obtain ⟨σ₀, Λ, ⟨a, ha, hmero⟩, hord, han, hprod⟩ := hS₁ S (by
    intro v hv; simp only [hSdef, Finset.mem_union]; exact Or.inl (Or.inl hv))

  have hloc : ∀ i : {p : HeightOneSpectrum (𝓞 ℚ) // p ∉ S},
      ∃ c : ℕ → ℝ, c 0 = 0 ∧ c 1 = ‖Φ.a i.1‖ ^ 2 ∧ (∀ m : ℕ, 0 ≤ c m) ∧
        (∀ m : ℕ, c m ≤ 4 * (Ideal.absNorm i.1.asIdeal : ℝ) ^ m) ∧
        ∀ y : ℂ, ‖y‖ < (Ideal.absNorm i.1.asIdeal : ℝ)⁻¹ →
          Summable (fun m : ℕ => (c m : ℂ) * y ^ m) ∧
          Complex.exp (∑' m : ℕ, (c m : ℂ) * y ^ m) =
            ((LanglandsTunnell.RankinSelberg.rsEulerPoly (Φ.a i.1 / Φ.b i.1) (Φ.b i.1)⁻¹ (Φ.a i.1) (Φ.b i.1) 0).eval y)⁻¹ := by
    intro i
    have hi : i.1 ∉ S := i.2
    have hi2 : i.1 ∉ S₂ := fun h => hi (by simp only [hSdef, Finset.mem_union]; exact Or.inl (Or.inr h))
    have hi0 : i.1 ∉ SQ₀ := fun h => hi (by simp only [hSdef, Finset.mem_union]; exact Or.inr h)
    have hb1 : ‖Φ.b i.1‖ = 1 := hb i.1 hi0
    obtain ⟨hsq, hlt⟩ := hS₂ i.1 hi2
    rw [hb1, one_mul] at hlt
    exact LanglandsTunnell.RankinSelberg.exists_nonneg_exp_tsum_mul_pow_eq_inv_eval_rsEulerPoly_self_of_norm_eq_one
      (Φ.a i.1) (Φ.b i.1) _ (one_lt_absNorm i.1) hb1 hsq hlt
  choose c hc0 hc1 hcnn hcB hcser using hloc

  set N : {p : HeightOneSpectrum (𝓞 ℚ) // p ∉ S} → ℕ := fun i => Ideal.absNorm i.1.asIdeal with hNdef
  have hNprime : ∀ i, (N i).Prime := fun i => absNorm_prime i.1
  have hNinj : Function.Injective N := fun i j h => Subtype.ext (absNorm_injective h)
  obtain ⟨d, hd0, hdval, -, habs, hsumd, hlayer⟩ :=
    LSeries.exists_nonneg_hasSum_tsum_mul_cpow_eq_lseries_of_le_mul_pow N hNprime hNinj c hc0 hcnn 4
      (fun i m => by simpa [hNdef] using hcB i m)

  have hexp : ∀ s : ℂ, max σ₀ 2 < s.re →
      LSeriesSummable (fun n => (d n : ℂ)) s ∧ Complex.exp (LSeries (fun n => (d n : ℂ)) s) = Λ s := by
    intro s hs
    have hs2 : 2 < s.re := lt_of_le_of_lt (le_max_right _ _) hs
    have hs0 : σ₀ < s.re := lt_of_le_of_lt (le_max_left _ _) hs
    obtain ⟨-, hD⟩ := hsumd s hs2
    refine ⟨?_, ?_⟩
    · apply LSeriesSummable_of_abscissaOfAbsConv_lt_re
      refine lt_of_le_of_lt habs ?_
      exact_mod_cast hs2
    ·
      have key : ∀ i : {p : HeightOneSpectrum (𝓞 ℚ) // p ∉ S},
          Complex.exp (∑' m : ℕ, (c i m : ℂ) * (((N i : ℕ) : ℂ) ^ (-s)) ^ m) =
            ((LanglandsTunnell.RankinSelberg.rsEulerPoly (Φ.a i.1 / Φ.b i.1) (Φ.b i.1)⁻¹ (Φ.a i.1) (Φ.b i.1) 0).eval
              (((Ideal.absNorm i.1.asIdeal : ℕ) : ℂ) ^ (-s)))⁻¹ := by
        intro i
        have hy : ‖((N i : ℕ) : ℂ) ^ (-s)‖ < (Ideal.absNorm i.1.asIdeal : ℝ)⁻¹ := by
          rw [Complex.norm_natCast_cpow_of_pos (absNorm_prime i.1).pos, Complex.neg_re, Real.rpow_neg (Nat.cast_nonneg _)]
          rw [inv_lt_inv₀ (Real.rpow_pos_of_pos (by linarith [one_lt_absNorm i.1]) _) (by linarith [one_lt_absNorm i.1])]
          conv_lhs => rw [← Real.rpow_one (Ideal.absNorm i.1.asIdeal : ℝ)]
          exact Real.rpow_lt_rpow_of_exponent_lt (one_lt_absNorm i.1) (by linarith)
        exact (hcser i _ hy).2
      have hE := hD.cexp
      have hfun : (Complex.exp ∘ fun i : {p : HeightOneSpectrum (𝓞 ℚ) // p ∉ S} =>
            ∑' m : ℕ, (c i m : ℂ) * (((N i : ℕ) : ℂ) ^ (-s)) ^ m) =
          fun v : {p : HeightOneSpectrum (𝓞 ℚ) // p ∉ S} =>
            ((LanglandsTunnell.RankinSelberg.rsEulerPoly (Φ.a v.1 / Φ.b v.1) (Φ.b v.1)⁻¹ (Φ.a v.1) (Φ.b v.1) 0).eval
              (((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ (-s)))⁻¹ := by
        funext i; exact key i
      rw [hfun] at hE
      exact hE.unique (hprod s hs0)

  obtain ⟨-, hreal⟩ :=
    LSeries.abscissaOfAbsConv_le_of_forall_analyticAt_ofReal_of_exp_lseries_eq d hd0 Λ 1 (max σ₀ 2) han hexp

  have h1 : (1 : ℂ) ∈ {s : ℂ | a < s.re} := by simp only [Set.mem_setOf_eq, Complex.one_re]; exact ha
  have hordZ : meromorphicOrderAt Λ 1 = ((-1 : ℤ) : WithTop ℤ) := by rw [hord]; rfl
  obtain ⟨g, hgan, hg1, hgev⟩ := (meromorphicOrderAt_eq_int_iff (hmero 1 h1)).1 hordZ
  obtain ⟨δ₁, hδ₁, hΛg⟩ : ∃ δ > 0, ∀ z : ℂ, dist z 1 < δ → z ≠ 1 → Λ z = (z - 1)⁻¹ * g z := by
    rw [eventually_nhdsWithin_iff, Metric.eventually_nhds_iff] at hgev
    obtain ⟨δ, hδ, h⟩ := hgev
    refine ⟨δ, hδ, fun z hz hz1 => ?_⟩
    have := h hz hz1
    rw [this, zpow_neg_one, smul_eq_mul]
  obtain ⟨δ₂, hδ₂, hgb⟩ : ∃ δ > 0, ∀ z : ℂ, dist z 1 < δ → ‖g z‖ ≤ ‖g 1‖ + 1 := by
    obtain ⟨δ, hδ, h⟩ := Metric.continuousAt_iff.1 hgan.continuousAt 1 one_pos
    refine ⟨δ, hδ, fun z hz => ?_⟩
    have := h hz
    rw [dist_eq_norm] at this
    calc ‖g z‖ = ‖(g z - g 1) + g 1‖ := by ring_nf
      _ ≤ ‖g z - g 1‖ + ‖g 1‖ := norm_add_le _ _
      _ ≤ ‖g 1‖ + 1 := by linarith
  set δ : ℝ := min (min δ₁ δ₂) (1 / 2) with hδdef
  have hδpos : 0 < δ := lt_min (lt_min hδ₁ hδ₂) (by norm_num)
  have hδ1 : δ ≤ δ₁ := le_trans (min_le_left _ _) (min_le_left _ _)
  have hδ2 : δ ≤ δ₂ := le_trans (min_le_left _ _) (min_le_right _ _)

  have hDsum : ∀ σ : ℝ, 1 < σ → Summable (rterm d σ) := fun σ hσ => summable_rterm (hreal σ hσ).1
  have hΛre : ∀ σ : ℝ, 1 < σ → Λ σ = ((Real.exp (∑' n, rterm d σ n) : ℝ) : ℂ) := by
    intro σ hσ
    rw [← (hreal σ hσ).2, lseries_eq_ofReal_tsum, Complex.ofReal_exp]
  have hDeq : ∀ σ : ℝ, 1 < σ → ∑' n, rterm d σ n = Real.log (Λ σ).re := by
    intro σ hσ
    rw [hΛre σ hσ, Complex.ofReal_re, Real.log_exp]

  set M₁ : ℝ := Real.log (‖g 1‖ + 1) with hM₁
  set M₂ : ℝ := ∑' n, rterm d (1 + δ) n with hM₂
  set CS : ℝ := ∑ p ∈ S, ‖Φ.a p‖ ^ 2 with hCS
  refine ⟨CS + max M₁ M₂, fun σ hσ1 hσ2 => ?_⟩

  obtain ⟨hlsum, hlle⟩ := hlayer σ (hreal σ hσ1).1
  have hlayer' : Summable (fun i : {p : HeightOneSpectrum (𝓞 ℚ) // p ∉ S} =>
        ‖Φ.a i.1‖ ^ 2 * (Ideal.absNorm i.1.asIdeal : ℝ) ^ (-σ)) ∧
      ∑' i : {p : HeightOneSpectrum (𝓞 ℚ) // p ∉ S}, ‖Φ.a i.1‖ ^ 2 * (Ideal.absNorm i.1.asIdeal : ℝ) ^ (-σ) ≤
        ∑' n, rterm d σ n := by
    have hfeq : (fun i : {p : HeightOneSpectrum (𝓞 ℚ) // p ∉ S} => c i 1 * (N i : ℝ) ^ (-σ)) =
        fun i => ‖Φ.a i.1‖ ^ 2 * (Ideal.absNorm i.1.asIdeal : ℝ) ^ (-σ) := by
      funext i; rw [hc1 i]
    rw [hfeq] at hlsum hlle
    refine ⟨hlsum, hlle.trans ?_⟩
    rw [lseries_eq_ofReal_tsum, Complex.ofReal_re]

  have hlogpos : 0 ≤ Real.log (1 / (σ - 1)) := by
    apply Real.log_nonneg
    rw [le_div_iff₀ (by linarith)]; linarith
  have hmain : ∑' n, rterm d σ n ≤ Real.log (1 / (σ - 1)) + max M₁ M₂ := by
    by_cases hσδ : σ < 1 + δ
    ·
      have hdist : dist (σ : ℂ) 1 < δ := by
        rw [dist_eq_norm, show (σ : ℂ) - 1 = ((σ - 1 : ℝ) : ℂ) by push_cast; ring, Complex.norm_real,
          Real.norm_eq_abs, abs_of_pos (by linarith)]
        linarith
      have hne : (σ : ℂ) ≠ 1 := by
        intro h; have := congrArg Complex.re h; simp at this; linarith
      have hΛσ := hΛg σ (lt_of_lt_of_le hdist hδ1) hne

      have hre : (Λ σ).re = (g σ).re / (σ - 1) := by
        rw [hΛσ, show ((σ : ℂ) - 1)⁻¹ = (((σ - 1)⁻¹ : ℝ) : ℂ) by push_cast; ring, Complex.re_ofReal_mul]
        ring
      have hΛpos : 0 < (Λ σ).re := by rw [hΛre σ hσ1, Complex.ofReal_re]; exact Real.exp_pos _
      have hgpos : 0 < (g σ).re := by
        have hσ0 : σ - 1 ≠ 0 := by linarith
        have : (g σ).re = (Λ σ).re * (σ - 1) := by rw [hre, div_mul_cancel₀ _ hσ0]
        rw [this]; exact mul_pos hΛpos (by linarith)
      have hgle : (g σ).re ≤ ‖g 1‖ + 1 :=
        (Complex.re_le_norm _).trans (hgb σ (lt_of_lt_of_le hdist hδ2))
      rw [hDeq σ hσ1, hre, Real.log_div hgpos.ne' (by linarith), show Real.log (σ - 1) = - Real.log (1 / (σ - 1)) by
        rw [one_div, Real.log_inv, neg_neg]]
      have : Real.log (g σ).re ≤ M₁ := Real.log_le_log hgpos hgle
      linarith [le_max_left M₁ M₂]
    ·
      push Not at hσδ
      have hmono : ∑' n, rterm d σ n ≤ M₂ :=
        Summable.tsum_le_tsum (rterm_anti hd0 hσδ) (hDsum σ hσ1) (hDsum (1 + δ) (by linarith))
      linarith [le_max_right M₁ M₂]

  set f : HeightOneSpectrum (𝓞 ℚ) → ℝ := fun p => ‖Φ.a p‖ ^ 2 * (Ideal.absNorm p.asIdeal : ℝ) ^ (-σ) with hfdef
  have hfsum : Summable f := (Finset.summable_compl_iff S).1 hlayer'.1
  refine ⟨hfsum, ?_⟩
  have hsplit := hfsum.sum_add_tsum_compl (s := S)
  have hcompl : ∑' i : ↑((S : Set (HeightOneSpectrum (𝓞 ℚ)))ᶜ), f i =
      ∑' i : {p : HeightOneSpectrum (𝓞 ℚ) // p ∉ S}, f i.1 := by
    rfl
  have hSpart : ∑ p ∈ S, f p ≤ CS := by
    apply Finset.sum_le_sum
    intro p _
    have h1 : (Ideal.absNorm p.asIdeal : ℝ) ^ (-σ) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos (one_lt_absNorm p).le (by linarith)
    calc ‖Φ.a p‖ ^ 2 * (Ideal.absNorm p.asIdeal : ℝ) ^ (-σ) ≤ ‖Φ.a p‖ ^ 2 * 1 := by
          apply mul_le_mul_of_nonneg_left h1 (sq_nonneg _)
      _ = ‖Φ.a p‖ ^ 2 := mul_one _
  rw [← hsplit, hcompl]
  linarith [hlayer'.2]
