import Mathlib.NumberTheory.ModularForms.LevelOne.GradedRing
import ZInQKernel.Contrib.TauCeti.NumberTheory.ModularForms.QExpansion.Basic

/-!
# Arithmetic spanning at actual level one

The normalized even Eisenstein series have rational Fourier coefficients.
The discriminant identity gives the same property for the actual cusp
form of weight twelve. Subtracting the constant term and dividing by the
actual discriminant proves rational-coefficient spanning in every weight.
No arithmetic spanning statement at higher level is assumed.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false

open UpperHalfPlane EisensteinSeries ModularForm
open scoped MatrixGroups ModularForm BigOperators

namespace DirectLevelOneArithmetic

/-- Rational period-one coefficients on the actual level-one form. -/
def IsRat {k : ℤ} (f : ModularForm 𝒮ℒ k) : Prop :=
  ∀ n : ℕ, ∃ q : ℚ, (qExpansion 1 f).coeff n = (q : ℂ)

/-- The complex span is defined from the actual coefficient condition. -/
def rationalSpan (k : ℤ) : Submodule ℂ (ModularForm 𝒮ℒ k) :=
  Submodule.span ℂ {f | IsRat f}

/-- Rational series admit actual rational-coefficient lifts. -/
theorem series_lift {p : PowerSeries ℂ}
    (hp : ∀ n, ∃ q : ℚ, p.coeff n = (q : ℂ)) :
    ∃ r : PowerSeries ℚ, PowerSeries.map (Rat.castHom ℂ) r = p := by
  classical
  choose q hq using hp
  refine ⟨PowerSeries.mk q, ?_⟩
  ext n
  simp only [PowerSeries.coeff_map, PowerSeries.coeff_mk]
  exact (hq n).symm

/-- Multiplication preserves rational coefficients at the actual width-one cusp. -/
theorem isRat_mul {a b : ℤ} {f : ModularForm 𝒮ℒ a} {g : ModularForm 𝒮ℒ b}
    (hf : IsRat f) (hg : IsRat g) : IsRat (f.mul g) := by
  obtain ⟨r, hr⟩ := series_lift hf
  obtain ⟨s, hs⟩ := series_lift hg
  intro n
  refine ⟨(r * s).coeff n, ?_⟩
  rw [ModularForm.qExpansion_mul one_pos one_mem_strictPeriods_SL f g, ← hr, ← hs,
    ← map_mul, PowerSeries.coeff_map]
  rfl

/-- Powers preserve rational coefficients. -/
theorem isRat_pow {k : ℤ} {f : ModularForm 𝒮ℒ k} (hf : IsRat f) (m : ℕ) :
    IsRat (f.pow m) := by
  obtain ⟨r, hr⟩ := series_lift hf
  intro n
  refine ⟨(r ^ m).coeff n, ?_⟩
  rw [ModularForm.qExpansion_pow one_pos one_mem_strictPeriods_SL f m, ← hr,
    ← map_pow, PowerSeries.coeff_map]
  rfl

/-- Subtraction preserves rational coefficients. -/
theorem isRat_sub {k : ℤ} {f g : ModularForm 𝒮ℒ k} (hf : IsRat f) (hg : IsRat g) :
    IsRat (f - g) := by
  intro n
  obtain ⟨r, hr⟩ := hf n
  obtain ⟨s, hs⟩ := hg n
  refine ⟨r - s, ?_⟩
  rw [FunLike.coe_sub, ModularForm.qExpansion_sub one_pos one_mem_strictPeriods_SL,
    map_sub, hr, hs]
  push_cast
  rfl

/-- Rational scalar multiplication preserves rational coefficients. -/
theorem isRat_smul {k : ℤ} {f : ModularForm 𝒮ℒ k} (hf : IsRat f) (q : ℚ) :
    IsRat ((q : ℂ) • f) := by
  intro n
  obtain ⟨r, hr⟩ := hf n
  refine ⟨q * r, ?_⟩
  rw [FunLike.coe_smul, ModularForm.qExpansion_smul one_pos one_mem_strictPeriods_SL,
    PowerSeries.coeff_smul, hr, smul_eq_mul]
  push_cast
  rfl

/-- A weight cast changes no actual coefficient. -/
theorem isRat_mcast {a b : ℤ} (hab : a = b) {f : ModularForm 𝒮ℒ a} (hf : IsRat f) :
    IsRat (ModularForm.mcast hab f) := hf

/-- The actual normalized Eisenstein form is rational in every even weight at least four. -/
theorem eisenstein_rational {k : ℕ} (hk : 3 ≤ k) (heven : Even k) : IsRat (E hk) := by
  intro n
  rw [E_qExpansion_coeff hk heven n]
  by_cases hn : n = 0
  · exact ⟨1, by simp [hn]⟩
  · refine ⟨-(2 * (k : ℚ) / bernoulli k) * (ArithmeticFunction.sigma (k - 1) n : ℚ), ?_⟩
    rw [if_neg hn]
    push_cast
    rfl

/-- The actual modular discriminant has rational coefficients, via the proved analytic identity. -/
theorem discriminant_rational :
    IsRat (CuspForm.discriminant : ModularForm 𝒮ℒ 12) := by
  let F4 : ModularForm 𝒮ℒ 12 := ModularForm.mcast (by norm_num) (E₄.pow 3)
  let F6 : ModularForm 𝒮ℒ 12 := ModularForm.mcast (by norm_num) (E₆.pow 2)
  have h4 : IsRat F4 := isRat_mcast _ (isRat_pow (eisenstein_rational (by norm_num) (by norm_num)) 3)
  have h6 : IsRat F6 := isRat_mcast _ (isRat_pow (eisenstein_rational (by norm_num) (by norm_num)) 2)
  have he : (CuspForm.discriminant : ModularForm 𝒮ℒ 12) =
      ((1 / 1728 : ℚ) : ℂ) • (F4 - F6) := by
    ext τ
    simp only [F4, F6, ModularForm.mcast_apply, ModularForm.coe_pow,
      Pi.pow_apply, _root_.smul_apply, _root_.sub_apply, smul_eq_mul]
    change ModularForm.discriminant τ = ((1 / 1728 : ℚ) : ℂ) * (E₄ τ ^ 3 - E₆ τ ^ 2)
    rw [ModularForm.discriminant_eq_E₄_cube_sub_E₆_sq]
    push_cast
    ring
  rw [he]
  exact isRat_smul (isRat_sub h4 h6) (1 / 1728)

/-- The actual discriminant equivalence supplies the complex-linear multiplication map. -/
def deltaMul (k : ℤ) : ModularForm 𝒮ℒ (k - 12) →ₗ[ℂ] ModularForm 𝒮ℒ k :=
  CuspForm.toModularFormₗ.comp (CuspForm.discriminantEquiv (k := k)).symm.toLinearMap

/-- This map is pointwise multiplication by the actual discriminant. -/
theorem deltaMul_apply (k : ℤ) (f : ModularForm 𝒮ℒ (k - 12)) (τ : ℍ) :
    deltaMul k f τ = ModularForm.discriminant τ * f τ := rfl

/-- Actual discriminant multiplication preserves the rational coefficient condition. -/
theorem deltaMul_rational (k : ℤ) {f : ModularForm 𝒮ℒ (k - 12)} (hf : IsRat f) :
    IsRat (deltaMul k f) := by
  have he : deltaMul k f =
      ModularForm.mcast (by ring) ((CuspForm.discriminant : ModularForm 𝒮ℒ 12).mul f) := by
    ext τ
    rw [deltaMul_apply]
    rfl
  rw [he]
  exact isRat_mcast _ (isRat_mul discriminant_rational hf)

/-- Rational-coefficient spans are preserved by this derived multiplication map. -/
theorem deltaMul_span (k : ℤ) {f : ModularForm 𝒮ℒ (k - 12)}
    (hf : f ∈ rationalSpan (k - 12)) : deltaMul k f ∈ rationalSpan k := by
  change f ∈ Submodule.span ℂ {g | IsRat g} at hf
  refine Submodule.span_induction (p := fun g _ => deltaMul k g ∈ rationalSpan k)
    (fun g hg => Submodule.subset_span (deltaMul_rational k hg))
    (by rw [map_zero]; exact Submodule.zero_mem _) ?_ ?_ hf
  · intro a b _ _ ha hb
    rw [map_add]
    exact Submodule.add_mem _ ha hb
  · intro c a _ ha
    rw [map_smul]
    exact Submodule.smul_mem _ c ha

/-- Actual level-one forms are spanned by rational-coefficient forms in every natural weight. -/
theorem rationalSpan_nat (n : ℕ) : rationalSpan (n : ℤ) = ⊤ := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    apply eq_top_iff.mpr
    intro f _
    rcases Nat.even_or_odd n with heven | hodd
    · by_cases hn0 : n = 0
      · subst n
        obtain ⟨c, hc⟩ := ModularFormClass.levelOne_weight_zero_const f
        have he : f = c • (1 : ModularForm 𝒮ℒ 0) := by
          ext τ
          simpa using congrFun hc τ
        rw [he]
        apply Submodule.smul_mem
        apply Submodule.subset_span
        intro m
        let q : ℚ := if m = 0 then 1 else 0
        refine ⟨q, ?_⟩
        change (qExpansion 1 (1 : ℍ → ℂ)).coeff m = (q : ℂ)
        rw [UpperHalfPlane.qExpansion_one]
        by_cases hm : m = 0 <;> simp [q, PowerSeries.coeff_one, hm]
      · by_cases hn2 : n = 2
        · subst n
          rw [(rank_zero_iff_forall_zero.mp ModularForm.levelOne_weight_two_rank_zero) f]
          exact Submodule.zero_mem _
        · have hk : 3 ≤ n := by
            obtain ⟨a, ha⟩ := heven
            omega
          let c : ℂ := (qExpansion 1 f).coeff 0
          let F : ModularForm 𝒮ℒ (n : ℤ) := f - c • E hk
          have hzero : (qExpansion 1 F).coeff 0 = 0 := by
            change (PowerSeries.coeff 0) ((TauCeti.ModularForm.qExpansionLinearMap one_pos
              one_mem_strictPeriods_SL (n : ℤ)) (f - c • E hk)) = 0
            rw [map_sub, map_smul, map_sub, PowerSeries.coeff_smul, smul_eq_mul,
              TauCeti.ModularForm.qExpansionLinearMap_apply,
              TauCeti.ModularForm.qExpansionLinearMap_apply, E_qExpansion_coeff_zero hk heven]
            simp [c]
          let g := ModularForm.toCuspForm F hzero
          have hGF : (g : ModularForm 𝒮ℒ (n : ℤ)) = F := by ext τ; rfl
          have hFmem : F ∈ rationalSpan (n : ℤ) := by
            by_cases hn12 : n < 12
            · have hg0 : g = 0 := (rank_zero_iff_forall_zero.mp
                (CuspForm.rank_eq_zero_of_weight_lt_twelve (by exact_mod_cast hn12))) g
              rw [← hGF, hg0]
              exact Submodule.zero_mem _
            · have hlt : n - 12 < n := by omega
              have he : ((n - 12 : ℕ) : ℤ) = (n : ℤ) - 12 := by omega
              have hlower : rationalSpan ((n : ℤ) - 12) = ⊤ := by
                rw [← he]
                exact ih (n - 12) hlt
              have hbody : CuspForm.discriminantEquiv g ∈ rationalSpan ((n : ℤ) - 12) := by
                rw [hlower]
                exact Submodule.mem_top
              have hmul := deltaMul_span (n : ℤ) hbody
              have hback : deltaMul (n : ℤ) (CuspForm.discriminantEquiv g) = F := by
                change ((CuspForm.discriminantEquiv (k := (n : ℤ))).symm
                  (CuspForm.discriminantEquiv g) : ModularForm 𝒮ℒ (n : ℤ)) = F
                rw [LinearEquiv.symm_apply_apply]
                exact hGF
              exact hback ▸ hmul
          have hE : E hk ∈ rationalSpan (n : ℤ) :=
            Submodule.subset_span (eisenstein_rational hk heven)
          have he : F + c • E hk = f := by simp [F]
          rw [← he]
          exact Submodule.add_mem _ hFmem (Submodule.smul_mem _ c hE)
    · have hoddInt : Odd (n : ℤ) := by exact_mod_cast hodd
      rw [ModularForm.levelOne_odd_weight_eq_zero hoddInt f]
      exact Submodule.zero_mem _

/-- The full actual integer-weight statement, with negative weights proved zero. -/
theorem rationalSpan_all (k : ℤ) : rationalSpan k = ⊤ := by
  by_cases hk : 0 ≤ k
  · have he : (k.toNat : ℤ) = k := Int.toNat_of_nonneg hk
    rw [← he]
    exact rationalSpan_nat k.toNat
  · apply eq_top_iff.mpr
    intro f _
    have hf : f = 0 := by
      apply ModularForm.ext
      intro τ
      exact congrFun (ModularFormClass.levelOne_neg_weight_eq_zero (by omega) f) τ
    rw [hf]
    exact Submodule.zero_mem _

end DirectLevelOneArithmetic
