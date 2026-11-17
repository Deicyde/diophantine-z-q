/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: P2M.Sol.S_AutomorphicForm_exists_finset_forall_lt_one_meromorphicOn_meromorphicOrderAt_one_eq_neg_one_analyticAt_hasProd_rsEulerPoly_self (git blob f789283724fa9e964589c7a2d4c846dc7151f37b, sha256 f490d30f732e38ab906d4589cd7219f6a7e7b58fe50f1114fcf5eb3f30403368).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AutomorphicForm_ProductionPinsGeneral
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_NarrowRayClassGroup
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_LanglandsTunnell_RankinSelbergEuler
import Mathlib.Analysis.Meromorphic.Order
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_AutomorphicForm_exists_finset_lt_one_meromorphicOn_meromorphicOrderAt_one_eq_neg_one_analyticAt_hasProd_rsEulerPoly_self

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

namespace P2MW.S_AutomorphicForm_exists_finset_forall_lt_one_meromorphicOn_meromorphicOrderAt_one_eq_neg_one_analyticAt_hasProd_rsEulerPoly_self

set_option autoImplicit false

open NumberField NumberField.AdelicLevel NumberField.AdelicBox
open AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering
open IsDedekindDomain
open Deep.NTSupply
open scoped Classical

noncomputable section

namespace RS40M

open Polynomial Filter Topology

variable {K : Type} [Field K] [NumberField K]

abbrev locPoly (Θ : HeckeEigensystem K ℂ) (v : HeightOneSpectrum (𝓞 K)) : ℂ[X] :=
  LanglandsTunnell.RankinSelberg.rsEulerPoly (Θ.a v / Θ.b v) (Θ.b v)⁻¹ (Θ.a v) (Θ.b v) 0

abbrev locEval (Θ : HeckeEigensystem K ℂ) (v : HeightOneSpectrum (𝓞 K)) (s : ℂ) : ℂ :=
  (locPoly Θ v).eval (((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (-s))

theorem absNorm_ne_zero (v : HeightOneSpectrum (𝓞 K)) : Ideal.absNorm v.asIdeal ≠ 0 := by
  rw [Ne, Ideal.absNorm_eq_zero_iff]; exact v.ne_bot

theorem two_le_absNorm (v : HeightOneSpectrum (𝓞 K)) : 2 ≤ Ideal.absNorm v.asIdeal := by
  have h0 := absNorm_ne_zero v
  have h1 : Ideal.absNorm v.asIdeal ≠ 1 := by
    rw [Ne, Ideal.absNorm_eq_one_iff]; exact v.isPrime.ne_top
  omega

theorem rsEulerPoly_coeff_zero {R : Type*} [CommRing R] (a b e₁ e₂ e₃ : R) :
    (LanglandsTunnell.RankinSelberg.rsEulerPoly a b e₁ e₂ e₃).coeff 0 = 1 := by
  simp [LanglandsTunnell.RankinSelberg.rsEulerPoly, coeff_one, coeff_X, coeff_C, coeff_X_pow]

theorem exists_forall_eval_cpow_neg_ne_zero (P : ℂ[X]) (hP : P.coeff 0 = 1) (N : ℕ) (hN : 2 ≤ N) :
    ∃ σ₀ : ℝ, ∀ s : ℂ, σ₀ < s.re → P.eval (((N : ℕ) : ℂ) ^ (-s)) ≠ 0 := by
  have h0 : P.eval 0 = 1 := by rw [← coeff_zero_eq_eval_zero]; exact hP
  have hcont : ContinuousAt (fun x : ℂ => P.eval x) 0 := P.continuous.continuousAt
  obtain ⟨δ, hδ, hδP⟩ := (Metric.continuousAt_iff.mp hcont) (1 / 2) (by norm_num)
  have hNr : (1 : ℝ) < (N : ℝ) := by exact_mod_cast (lt_of_lt_of_le (by norm_num) hN)
  have hNpos : (0 : ℝ) < (N : ℝ) := lt_trans zero_lt_one hNr
  refine ⟨Real.logb N (1 / δ), fun s hs => ?_⟩
  have hsmall : ‖((N : ℕ) : ℂ) ^ (-s)‖ < δ := by
    rw [Complex.norm_natCast_cpow_of_pos (lt_of_lt_of_le (by norm_num) hN), Complex.neg_re]
    calc (N : ℝ) ^ (-s.re) < (N : ℝ) ^ (-Real.logb N (1 / δ)) :=
          Real.rpow_lt_rpow_of_exponent_lt hNr (by linarith)
      _ = δ := by
          rw [Real.rpow_neg hNpos.le, Real.rpow_logb hNpos hNr.ne' (by positivity), one_div, inv_inv]
  intro hzero
  have := hδP (x := ((N : ℕ) : ℂ) ^ (-s)) (by simpa [dist_zero_right] using hsmall)
  rw [hzero, h0, dist_eq_norm] at this
  norm_num at this

theorem differentiable_locEval (Θ : HeckeEigensystem K ℂ) (v : HeightOneSpectrum (𝓞 K)) :
    Differentiable ℂ (locEval Θ v) := by
  have hN : (((Ideal.absNorm v.asIdeal : ℕ) : ℂ)) ≠ 0 := Nat.cast_ne_zero.mpr (absNorm_ne_zero v)
  have h : (fun s : ℂ => (((Ideal.absNorm v.asIdeal : ℕ) : ℂ)) ^ (-s)) =
      fun s => Complex.exp (Complex.log (((Ideal.absNorm v.asIdeal : ℕ) : ℂ)) * (-s)) := by
    funext s; rw [Complex.cpow_def_of_ne_zero hN]
  have hd : Differentiable ℂ (fun s : ℂ => (((Ideal.absNorm v.asIdeal : ℕ) : ℂ)) ^ (-s)) := by
    rw [h]; fun_prop
  exact (locPoly Θ v).differentiable.comp hd

theorem hasProd_subtype_notMem_of_subset {β : Type*} (f : β → ℂ) {S T : Finset β} (hST : S ⊆ T)
    {a : ℂ} (h : HasProd (fun x : {x // x ∉ S} => f x) a) (hf : ∀ b ∈ T \ S, f b ≠ 0) :
    HasProd (fun x : {x // x ∉ T} => f x) (a * ∏ b ∈ T \ S, (f b)⁻¹) := by
  classical

  have h1 : HasProd (({x | x ∉ S} : Set β).mulIndicator f) a :=
    (hasProd_subtype_iff_mulIndicator (s := ({x | x ∉ S} : Set β)) (f := f)).mp h

  have h2 : HasProd (((↑(T \ S) : Set β)).mulIndicator fun x => (f x)⁻¹) (∏ b ∈ T \ S, (f b)⁻¹) :=
    (hasProd_subtype_iff_mulIndicator (s := ((↑(T \ S) : Set β))) (f := fun x => (f x)⁻¹)).mp
      (Finset.hasProd (T \ S) fun x => (f x)⁻¹)
  have h3 := h1.mul h2

  have hpt : (fun x => ({x | x ∉ S} : Set β).mulIndicator f x *
      ((↑(T \ S) : Set β)).mulIndicator (fun x => (f x)⁻¹) x) = ({x | x ∉ T} : Set β).mulIndicator f := by
    funext x
    by_cases hxT : x ∈ T
    · by_cases hxS : x ∈ S
      · have h1' : x ∉ ({x | x ∉ S} : Set β) := fun h => h hxS
        have h2' : x ∉ ((↑(T \ S) : Set β)) := by
          rw [Finset.mem_coe, Finset.mem_sdiff]; exact fun h => h.2 hxS
        have h3' : x ∉ ({x | x ∉ T} : Set β) := fun h => h hxT
        rw [Set.mulIndicator_of_notMem h1', Set.mulIndicator_of_notMem h2', Set.mulIndicator_of_notMem h3',
          one_mul]
      · have h1' : x ∈ ({x | x ∉ S} : Set β) := hxS
        have h2' : x ∈ ((↑(T \ S) : Set β)) := by
          rw [Finset.mem_coe, Finset.mem_sdiff]; exact ⟨hxT, hxS⟩
        have h3' : x ∉ ({x | x ∉ T} : Set β) := fun h => h hxT
        rw [Set.mulIndicator_of_mem h1', Set.mulIndicator_of_mem h2', Set.mulIndicator_of_notMem h3',
          mul_inv_cancel₀ (hf x (Finset.mem_sdiff.mpr ⟨hxT, hxS⟩))]
    · have hxS : x ∉ S := fun h => hxT (hST h)
      have h1' : x ∈ ({x | x ∉ S} : Set β) := hxS
      have h2' : x ∉ ((↑(T \ S) : Set β)) := by
        rw [Finset.mem_coe, Finset.mem_sdiff]; exact fun h => hxT h.1
      have h3' : x ∈ ({x | x ∉ T} : Set β) := hxT
      rw [Set.mulIndicator_of_mem h1', Set.mulIndicator_of_notMem h2', Set.mulIndicator_of_mem h3', mul_one]
  rw [hpt] at h3
  exact (hasProd_subtype_iff_mulIndicator (s := ({x | x ∉ T} : Set β)) (f := f)).mpr h3

theorem pole_of_pole0
    (K : Type) [Field K] [NumberField K]
    (c u d₁ d₂ : ℝ) (T : Finset (AdelicGL2 (𝓞 K) K))
    (hc : 0 < c) (hd₁ : 0 < d₁) (hd : d₁ < d₂)
    (hcov : CoversModCentre K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂))
    (Θ : HeckeEigensystem K ℂ)
    (hΘ : IsArithGenuineCuspRealizable K
      (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
        (adelicBox K)) Θ) :
    ∃ S₁ : Finset (HeightOneSpectrum (𝓞 K)), ∀ S : Finset (HeightOneSpectrum (𝓞 K)), S₁ ⊆ S →
      ∃ σ₀ : ℝ, ∃ Λ : ℂ → ℂ,
      (∃ a : ℝ, a < 1 ∧ MeromorphicOn Λ {s : ℂ | a < s.re}) ∧
      meromorphicOrderAt Λ 1 = -1 ∧
      (∀ σ : ℝ, 1 < σ → AnalyticAt ℂ Λ (σ : ℂ)) ∧
      ∀ s : ℂ, σ₀ < s.re →
        HasProd (fun v : {v : HeightOneSpectrum (𝓞 K) // v ∉ S} => (locEval Θ v.1 s)⁻¹) (Λ s) := by
  obtain ⟨S, σ₀, Λ, ⟨a, ha, hmero⟩, hord, han, hprod, hgen⟩ :=
    AutomorphicForm.exists_finset_lt_one_meromorphicOn_meromorphicOrderAt_one_eq_neg_one_analyticAt_hasProd_rsEulerPoly_self K c u d₁ d₂ T hc hd₁ hd hcov Θ hΘ
  have hprod' : ∀ s : ℂ, σ₀ < s.re →
      HasProd (fun v : {v : HeightOneSpectrum (𝓞 K) // v ∉ S} => (locEval Θ v.1 s)⁻¹) (Λ s) := hprod
  refine ⟨S, fun S' hSS' => ?_⟩

  have hσv : ∀ v : HeightOneSpectrum (𝓞 K), ∃ σv : ℝ, ∀ s : ℂ, σv < s.re → locEval Θ v s ≠ 0 :=
    fun v => exists_forall_eval_cpow_neg_ne_zero (locPoly Θ v) (rsEulerPoly_coeff_zero _ _ _ _ _)
      (Ideal.absNorm v.asIdeal) (two_le_absNorm v)
  choose σv hσv using hσv
  set σ₁ : ℝ := max σ₀ 0 + ∑ v ∈ S' \ S, max (σv v) 0 with hσ₁
  have hσ₁₀ : σ₀ ≤ σ₁ := by
    have : 0 ≤ ∑ v ∈ S' \ S, max (σv v) 0 := Finset.sum_nonneg fun v _ => le_max_right _ _
    rw [hσ₁]; linarith [le_max_left σ₀ 0]
  have hσ₁v : ∀ v ∈ S' \ S, σv v ≤ σ₁ := by
    intro v hv
    have h1 : max (σv v) 0 ≤ ∑ w ∈ S' \ S, max (σv w) 0 :=
      Finset.single_le_sum (f := fun w => max (σv w) 0) (fun w _ => le_max_right _ _) hv
    rw [hσ₁]; linarith [le_max_left (σv v) 0, le_max_right σ₀ 0]

  set Q : ℂ → ℂ := fun s => ∏ v ∈ S' \ S, locEval Θ v s with hQ
  have hQdiff : Differentiable ℂ Q := by
    rw [hQ]; exact Differentiable.fun_finsetProd fun v _ => differentiable_locEval Θ v
  have hQ1 : Q 1 ≠ 0 := by
    rw [hQ]
    refine Finset.prod_ne_zero_iff.mpr fun v hv => ?_
    have hv' : v ∉ S := (Finset.mem_sdiff.mp hv).2
    have := hgen v hv'
    simpa only [locEval, locPoly, Complex.cpow_neg_one] using this
  refine ⟨σ₁, fun s => Λ s * Q s, ?_, ?_, ?_, ?_⟩
  ·
    refine ⟨a, ha, fun x hx => ?_⟩
    exact (hmero x hx).mul (hQdiff.analyticAt x).meromorphicAt
  ·
    have h1U : (1 : ℂ) ∈ {s : ℂ | a < s.re} := by
      simp only [Set.mem_setOf_eq, Complex.one_re]; exact ha
    have hQan : AnalyticAt ℂ Q 1 := hQdiff.analyticAt 1
    have hordQ : meromorphicOrderAt Q 1 = 0 := by
      rw [hQan.meromorphicOrderAt_eq, (hQan.analyticOrderAt_eq_zero).mpr hQ1]; rfl
    show meromorphicOrderAt (Λ * Q) 1 = -1
    rw [meromorphicOrderAt_mul (hmero 1 h1U) hQan.meromorphicAt, hordQ, add_zero]
    exact hord
  ·
    intro σ hσ
    show AnalyticAt ℂ (fun s => Λ s * Q s) (σ : ℂ)
    exact (han σ hσ).mul (hQdiff.analyticAt _)
  ·
    intro s hs
    have hs₀ : σ₀ < s.re := lt_of_le_of_lt hσ₁₀ hs
    have hne : ∀ v ∈ S' \ S, (locEval Θ v s)⁻¹ ≠ 0 := fun v hv =>
      inv_ne_zero (hσv v s (lt_of_le_of_lt (hσ₁v v hv) hs))
    have key := hasProd_subtype_notMem_of_subset (fun v => (locEval Θ v s)⁻¹) hSS' (hprod' s hs₀) hne
    simp only [inv_inv] at key
    exact key

end RS40M

theorem solution
    (K : Type) [Field K] [NumberField K]
    (c u d₁ d₂ : ℝ) (T : Finset (AdelicGL2 (𝓞 K) K))
    (hc : 0 < c) (hd₁ : 0 < d₁) (hd : d₁ < d₂)
    (hcov : CoversModCentre K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂))
    (Θ : HeckeEigensystem K ℂ)
    (hΘ : IsArithGenuineCuspRealizable K
      (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
        (adelicBox K)) Θ) :
    ∃ S₁ : Finset (HeightOneSpectrum (𝓞 K)), ∀ S : Finset (HeightOneSpectrum (𝓞 K)), S₁ ⊆ S →
      ∃ σ₀ : ℝ, ∃ Λ : ℂ → ℂ,
      (∃ a : ℝ, a < 1 ∧ MeromorphicOn Λ {s : ℂ | a < s.re}) ∧
      meromorphicOrderAt Λ 1 = -1 ∧
      (∀ σ : ℝ, 1 < σ → AnalyticAt ℂ Λ (σ : ℂ)) ∧
      ∀ s : ℂ, σ₀ < s.re →
        HasProd (fun v : {v : HeightOneSpectrum (𝓞 K) // v ∉ S} =>
          ((LanglandsTunnell.RankinSelberg.rsEulerPoly (Θ.a v.1 / Θ.b v.1) (Θ.b v.1)⁻¹
              (Θ.a v.1) (Θ.b v.1) 0).eval (((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ (-s)))⁻¹) (Λ s) :=
  RS40M.pole_of_pole0 K c u d₁ d₂ T hc hd₁ hd hcov Θ hΘ
