import ZInQKernel.Contrib.OneProof.EigenformCoeffFieldFinite

/-! # coeff-rational: `K_f` is a number field, from `T_p`-stable rational forms on `Γ₁(N)`

Task coeff-rational (2026-11-16), report `docs/research/coeff-rational.md`, scratch `scratch/coeff-rational/`.

The open field `eigenformCoeffFieldFinite : DSCoeffExt.EigenformCoeffFieldFinite` (for a normalized eigenform
`f ∈ S_k(N, χ)`, `k ≥ 2`, `K_f = ℚ(a_n(f))` is finite over `ℚ`) is read by the chain at the eigenform that
Pan∘Berger attaches to the QM surface's `r₅`, of a priori arbitrary level, character and weight (it is used to
rule out `k ≥ 3`), so it cannot be narrowed to forms with rational coefficients. This file proves it from the
rational structure of `S_k(Γ₁(N))` in a form that needs no diamond-operator leaf:

* `eigenformCoeffFieldFinite_of_heckePrime : Gamma1IntegralSpan → HeckePrimeIntegralToRational →
  DSCoeffExt.EigenformCoeffFieldFinite`: from Shimura's integral basis (coeff-field's `Gamma1IntegralSpan`) and
  the new leaf `HeckePrimeIntegralToRational` (the Hecke operator `T_p` of the double coset
  `Γ₁(N) diag(1, p) Γ₁(N)`, `p ∤ N` prime, maps integral `q`-expansions to rational ones), in place of coeff-field's
  `DiamondIntegralToRational` (which follows: `diamondIntegralToRational_of_heckePrime`);
* `eigenformCoeffFieldFinite_of_rationalHeckeSpan : RationalHeckeSpan → DSCoeffExt.EigenformCoeffFieldFinite`:
  the one-leaf form, `S_k(Γ₁(N))` is spanned by forms `g` with `g` and every `T_p g` (`p ∤ N`) rational; it follows
  from either pair of `Γ₁(N)` leaves (`rationalHeckeSpan_of_heckePrime`, `rationalHeckeSpan_of_diamond`).

Glue proved here: the diamond operators from `T_p` (`isRatForm_diamond`): for `d ∈ (ℤ/N)ˣ` choose a prime
`p ≡ d (mod N)`, `p > N` (Dirichlet's theorem, Mathlib's `Nat.forall_exists_prime_gt_and_eq_mod`), so `⟨d⟩ = ⟨p⟩`,
and Tau Ceti's recurrence `a_m(T_p g) = a_{pm}(g) + p^{k−1} a_{m/p}(⟨p⟩ g)` at `m = pn` gives
`a_n(⟨p⟩ g) = p^{1−k}(a_{pn}(T_p g) − a_{p²n}(g))`; then coeff-field's `χ`-projector and its abstract
eigenvalue lemma (`CoeffFieldFinite.eigenformCoeffFieldFinite_of`).
-/

noncomputable section

set_option linter.unusedSectionVars false

namespace CoeffRational

open UpperHalfPlane CongruenceSubgroup HeckeRing.GL2 Matrix.SpecialLinearGroup
open CoeffFieldFinite

variable {N : ℕ} [NeZero N] {k : ℤ}

/-- `g` has rational `q`-expansion at `∞`. -/
def IsRatForm (g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) : Prop :=
  ∀ n : ℕ, ∃ q : ℚ, (qExpansion 1 g).coeff n = q

/-- **LEAF (one-leaf form: a `T_p`-stable rational spanning set of `S_k(Γ₁(N))`).** For `k ≥ 2`, `S_k(Γ₁(N))`
(Mathlib's `CuspForm` on `Γ₁(N)`) is spanned over `ℂ` by cusp forms `g` such that `g` and `T_p g` have rational
`q`-expansions at `∞` (period `1`) for every prime `p ∤ N`, where `T_p` is Tau Ceti's operator of the double coset
`Γ₁(N) diag(1, p) Γ₁(N)` (`heckeSlashGamma1CuspFormEnd k (diagCosetGamma1 N p)`; Diamond–Shurman's `T_p`,
`a_m(T_p g) = a_{pm}(g) + p^{k−1} a_{m/p}(⟨p⟩ g)`). A consequence of "`S_k(Γ₁(N))` has a basis in
`S_k(Γ₁(N), ℤ)`, and `S_k(Γ₁(N), ℤ)` is stable under the Hecke operators `T_n`" (Shimura 1971 Thm 3.52 with §3.5;
Diamond–Im 1995 §12.3–12.4; Diamond–Shurman §6.5 for `k = 2`; all locators UNVERIFIED): take the integral basis.
In Lean it follows from `Gamma1IntegralSpan` with either `HeckePrimeIntegralToRational` or coeff-field's
`DiamondIntegralToRational`. -/
def RationalHeckeSpan : Prop :=
  ∀ (N : ℕ) [NeZero N] (k : ℤ), 2 ≤ k →
    Submodule.span ℂ {g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k |
      (∀ n : ℕ, ∃ q : ℚ, (qExpansion 1 g).coeff n = q) ∧
      ∀ p : ℕ, p.Prime → ¬ p ∣ N → ∀ n : ℕ, ∃ q : ℚ,
        (qExpansion 1 (heckeSlashGamma1CuspFormEnd k (diagCosetGamma1 N p) g)).coeff n = q} = ⊤

/-- **LEAF (the Hecke operators `T_p` preserve the integral structure, weakest form).** For `k ≥ 2` and a prime
`p ∤ N`, the Hecke operator `T_p` of the double coset `Γ₁(N) diag(1, p) Γ₁(N)` (Tau Ceti's
`heckeSlashGamma1CuspFormEnd k (diagCosetGamma1 N p)`, with Diamond–Shurman's normalization
`a_m(T_p g) = a_{pm}(g) + p^{k−1} a_{m/p}(⟨p⟩ g)`, Tau Ceti `HeckeSlash/Recurrence.lean`) maps a cusp form on `Γ₁(N)`
with integral `q`-expansion to one with rational `q`-expansion. Source: the Hecke operators `T_n` preserve
`S_k(Γ₁(N), ℤ)` (Shimura 1971 §3.5 with Thm 3.52; Diamond–Im 1995 §12.3–12.4; Diamond–Shurman §6.5 for `k = 2`;
all locators UNVERIFIED). Consequence taken: primes `p ∤ N` only, integral input, rational output, so it follows
from the print for `A = ℤ`, `ℤ[1/N]` or `ℚ` and whether or not the print's Hecke algebra contains the diamond
operators (`T_p` belongs to it in every convention). -/
def HeckePrimeIntegralToRational : Prop :=
  ∀ (N : ℕ) [NeZero N] (k : ℤ) (p : ℕ) (g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k), 2 ≤ k →
    p.Prime → ¬ p ∣ N →
    (∀ n : ℕ, ∃ z : ℤ, (qExpansion 1 g).coeff n = z) →
    ∀ n : ℕ, ∃ q : ℚ,
      (qExpansion 1 (heckeSlashGamma1CuspFormEnd k (diagCosetGamma1 N p) g)).coeff n = q

/-- A prime `p > N` in the class `d`; `⟨p⟩ = ⟨d⟩`. -/
theorem exists_prime_diamond (d : (ZMod N)ˣ) :
    ∃ p : ℕ, p.Prime ∧ ¬ p ∣ N ∧ ∃ h : Nat.Coprime p N, ZMod.unitOfCoprime p h = d := by
  obtain ⟨p, hpN, hp, hpd⟩ := Nat.forall_exists_prime_gt_and_eq_mod (q := N) d.isUnit N
  have hndvd : ¬ p ∣ N := fun h => by
    have := Nat.le_of_dvd (Nat.pos_of_ne_zero (NeZero.ne N)) h
    omega
  have hcop : Nat.Coprime p N := (Nat.Prime.coprime_iff_not_dvd hp).2 hndvd
  exact ⟨p, hp, hndvd, hcop, Units.ext (by simpa using hpd)⟩

/-- **The diamond operators from `T_p` (glue).** If `g` and every `T_p g` (`p ∤ N` prime) have rational
`q`-expansions, so does every `⟨d⟩ g`: pick a prime `p ≡ d (mod N)` (Dirichlet) and read
`a_n(⟨p⟩ g) = p^{1−k} (a_{pn}(T_p g) − a_{p²n}(g))` off Tau Ceti's recurrence. -/
theorem isRatForm_diamond (d : (ZMod N)ˣ) {g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k}
    (hg : IsRatForm g)
    (hT : ∀ p : ℕ, p.Prime → ¬ p ∣ N →
      IsRatForm (heckeSlashGamma1CuspFormEnd k (diagCosetGamma1 N p) g)) :
    IsRatForm (diamondOpCusp k d g) := by
  intro n
  obtain ⟨p, hp, hndvd, hcop, hd⟩ := exists_prime_diamond d
  have hrec := qExpansion_coeff_heckeSlashGamma1CuspFormEnd_diagCosetGamma1_of_prime k hp g (p * n)
  simp only [dvd_mul_right, ↓reduceIte] at hrec
  rw [Nat.mul_div_cancel_left n hp.pos, diamondOpCuspNat_of_coprime k hcop, hd] at hrec
  obtain ⟨q1, hq1⟩ := hT p hp hndvd (p * n)
  obtain ⟨q2, hq2⟩ := hg (p * (p * n))
  refine ⟨(q1 - q2) / (p : ℚ) ^ (k - 1), ?_⟩
  have hp0 : (p : ℂ) ^ (k - 1) ≠ 0 := zpow_ne_zero _ (Nat.cast_ne_zero.2 hp.ne_zero)
  rw [hq1, hq2] at hrec
  push_cast
  field_simp
  linear_combination -hrec

/-- **`T_p` from the diamond operators (glue).** -/
theorem isRatForm_hecke {p : ℕ} (hp : p.Prime) {g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k}
    (hg : IsRatForm g) (hD : ∀ d : (ZMod N)ˣ, IsRatForm (diamondOpCusp k d g)) :
    IsRatForm (heckeSlashGamma1CuspFormEnd k (diagCosetGamma1 N p) g) := by
  intro m
  rw [qExpansion_coeff_heckeSlashGamma1CuspFormEnd_diagCosetGamma1_of_prime k hp g m]
  obtain ⟨q1, hq1⟩ := hg (p * m)
  rw [hq1]
  split_ifs with hpm
  · by_cases hcop : Nat.Coprime p N
    · rw [diamondOpCuspNat_of_coprime k hcop]
      obtain ⟨q2, hq2⟩ := hD (ZMod.unitOfCoprime p hcop) (m / p)
      exact ⟨q1 + (p : ℚ) ^ (k - 1) * q2, by rw [hq2]; push_cast; ring⟩
    · rw [diamondOpCuspNat_of_not_coprime k hcop, LinearMap.zero_apply, ← coeffG_apply, map_zero]
      exact ⟨q1, by simp⟩
  · exact ⟨q1, by simp⟩

theorem proj_coeff_mem_of_rat (χ : (ZMod N)ˣ →* ℂˣ) {g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k}
    (hD : ∀ d : (ZMod N)ˣ, IsRatForm (diamondOpCusp k d g)) (n : ℕ) :
    (qExpansion 1 (proj χ g)).coeff n ∈ charField χ := by
  rw [← coeffG_apply, proj_apply, map_sum]
  refine sum_mem fun d _ => ?_
  rw [map_smul, smul_eq_mul]
  refine mul_mem (IntermediateField.subset_adjoin ℚ _ ⟨d⁻¹, rfl⟩) ?_
  obtain ⟨q, hq⟩ := hD d n
  rw [coeffG_apply, hq]
  exact SubfieldClass.ratCast_mem _ q

/-- **`CharSpaceRationalSpan` from the one-leaf form.** -/
theorem charSpaceRationalSpan_of_rationalHeckeSpan (hS : RationalHeckeSpan) :
    CharSpaceRationalSpan := by
  intro N _ k χ hk
  rw [eq_top_iff]
  rintro F -
  set R := {g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k |
      (∀ n : ℕ, ∃ q : ℚ, (qExpansion 1 g).coeff n = q) ∧
      ∀ p : ℕ, p.Prime → ¬ p ∣ N → ∀ n : ℕ, ∃ q : ℚ,
        (qExpansion 1 (heckeSlashGamma1CuspFormEnd k (diagCosetGamma1 N p) g)).coeff n = q}
  set X := {F : cuspFormCharSpace k χ | ∀ n : ℕ,
      (qExpansion 1 (F : CuspForm ((Gamma1 N).map (mapGL ℝ)) k)).coeff n ∈ charField χ}
  let P' : CuspForm ((Gamma1 N).map (mapGL ℝ)) k →ₗ[ℂ] cuspFormCharSpace k χ :=
    (proj χ).codRestrict _ (proj_mem χ)
  have hR : (F : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) ∈ Submodule.span ℂ R := by
    rw [hS N k hk]; exact Submodule.mem_top
  have hPX : P' '' R ⊆ X := by
    rintro _ ⟨g, ⟨hg, hT⟩, rfl⟩ n
    exact proj_coeff_mem_of_rat χ (fun d => isRatForm_diamond d hg hT) n
  have h1 : P' F ∈ Submodule.span ℂ X := by
    have hmap := Submodule.mem_map_of_mem (f := P') hR
    rw [Submodule.map_span] at hmap
    exact Submodule.span_mono hPX hmap
  have h2 : P' F = (Fintype.card (ZMod N)ˣ : ℂ) • F := Subtype.ext (proj_of_mem χ F.2)
  have hc : (Fintype.card (ZMod N)ˣ : ℂ) ≠ 0 := Nat.cast_ne_zero.2 Fintype.card_ne_zero
  have : F = ((Fintype.card (ZMod N)ˣ : ℂ))⁻¹ • P' F := by
    rw [h2, smul_smul, inv_mul_cancel₀ hc, one_smul]
  rw [this]
  exact Submodule.smul_mem _ _ h1

omit [NeZero N] in
theorem isRatForm_of_int {g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k}
    (hg : ∀ n : ℕ, ∃ z : ℤ, (qExpansion 1 g).coeff n = z) : IsRatForm g := fun n => by
  obtain ⟨z, hz⟩ := hg n
  exact ⟨z, by rw [hz]; push_cast; rfl⟩

/-- The one-leaf form from Shimura's integral span and the `T_p`-rationality. -/
theorem rationalHeckeSpan_of_heckePrime (hA : Gamma1IntegralSpan)
    (hT : HeckePrimeIntegralToRational) : RationalHeckeSpan := by
  intro N _ k hk
  rw [eq_top_iff, ← hA N k hk]
  exact Submodule.span_mono fun g hg => ⟨isRatForm_of_int hg, fun p hp hpN => hT N k p g hk hp hpN hg⟩

/-- The one-leaf form from coeff-field's two leaves. -/
theorem rationalHeckeSpan_of_diamond (hA : Gamma1IntegralSpan)
    (hB : DiamondIntegralToRational) : RationalHeckeSpan := by
  intro N _ k hk
  rw [eq_top_iff, ← hA N k hk]
  exact Submodule.span_mono fun g hg => ⟨isRatForm_of_int hg, fun p hp _ =>
    isRatForm_hecke hp (isRatForm_of_int hg) fun d => hB N k d g hk hg⟩

/-- coeff-field's diamond leaf is a consequence of the `T_p` leaf. -/
theorem diamondIntegralToRational_of_heckePrime (hT : HeckePrimeIntegralToRational) :
    DiamondIntegralToRational := fun N _ k d g hk hg =>
  isRatForm_diamond d (isRatForm_of_int hg) fun p hp hpN => hT N k p g hk hp hpN hg

theorem eigenformCoeffFieldFinite_of_rationalHeckeSpan (hS : RationalHeckeSpan) :
    DSCoeffExt.EigenformCoeffFieldFinite :=
  eigenformCoeffFieldFinite_of (charSpaceRationalSpan_of_rationalHeckeSpan hS)

theorem eigenformCoeffFieldFinite_of_heckePrime (hA : Gamma1IntegralSpan)
    (hT : HeckePrimeIntegralToRational) : DSCoeffExt.EigenformCoeffFieldFinite :=
  eigenformCoeffFieldFinite_of_rationalHeckeSpan (rationalHeckeSpan_of_heckePrime hA hT)

theorem dsThm965Weak_of_printed_rationalHeckeSpan (h1 : DSCoeffExt.DSThm965Printed)
    (hS : RationalHeckeSpan) : DS965Weak.DSThm965Weak :=
  DSCoeffExt.dsThm965Weak_of_printed h1 (eigenformCoeffFieldFinite_of_rationalHeckeSpan hS)

theorem dsThm965Weak_of_printed_heckePrime (h1 : DSCoeffExt.DSThm965Printed)
    (hA : Gamma1IntegralSpan) (hT : HeckePrimeIntegralToRational) : DS965Weak.DSThm965Weak :=
  DSCoeffExt.dsThm965Weak_of_printed h1 (eigenformCoeffFieldFinite_of_heckePrime hA hT)

end CoeffRational
