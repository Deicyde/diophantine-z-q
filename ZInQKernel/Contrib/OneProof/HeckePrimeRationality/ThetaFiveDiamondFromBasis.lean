import ZInQKernel.Contrib.OneProof.HeckePrimeRationality.ThetaFivePowerBasis
import ZInQKernel.Contrib.TauCeti.NumberTheory.ModularForms.Parity
import ZInQKernel.Contrib.TauCeti.NumberTheory.ModularForms.HeckeSlash.Recurrence

/-!
# Rational diamond action on `Γ₁(5)` from an explicit weight-one basis

Let `A, B` be weight-one modular forms on `Γ₁(5)` with rational `q`-expansions, normalized by
`a₀(A) = 0`, `a₁(A) = 1`, `a₀(B) = 1`, and suppose the diamond operator `⟨2⟩` acts on them by
`⟨2⟩A = -3A - B` and `⟨2⟩B = 10A + 3B`. Then for every weight `n : ℕ` and every unit `u`
modulo `5`, the diamond operator `⟨u⟩` maps forms with rational `q`-expansion to forms with
rational `q`-expansion.

The proof writes a form in the power basis `A^j B^(n-j)` with rational coordinates, uses that
diamond operators are multiplicative on these products (both are slashes by one matrix of
`Γ₀(5)`), and that the images `⟨u⟩A, ⟨u⟩B` are rational combinations of `A, B` (from the
`⟨2⟩` equations, `⟨-1⟩ = (-1)^k` and the unit enumeration modulo `5`).

The hypotheses on `A` and `B` are explicit; this file does not construct `A` or `B`.
-/

noncomputable section

open UpperHalfPlane CongruenceSubgroup Matrix.SpecialLinearGroup
open scoped MatrixGroups ModularForm

namespace ZInQ.Contrib.HeckePrimeRationality.ThetaFiveDiamondFromBasis

open ThetaFivePowerBasis

set_option quotPrecheck false in
local notation "Γ₅" => (Gamma1 5).map (mapGL ℝ)

/-- Rational `q`-expansion at `∞`. -/
def IsRat {k : ℤ} (f : ModularForm Γ₅ k) : Prop :=
  ∀ m : ℕ, ∃ q : ℚ, PowerSeries.coeff m (qExpansion 1 f) = q

theorem isRat_add {k : ℤ} {f g : ModularForm Γ₅ k} (hf : IsRat f) (hg : IsRat g) :
    IsRat (f + g) := by
  intro m
  obtain ⟨a, ha⟩ := hf m
  obtain ⟨b, hb⟩ := hg m
  refine ⟨a + b, ?_⟩
  rw [show ⇑(f + g) = ⇑f + ⇑g from rfl, ModularForm.qExpansion_add one_pos oneMemG5, map_add,
    ha, hb]
  push_cast; ring

theorem isRat_smul {k : ℤ} {f : ModularForm Γ₅ k} (hf : IsRat f) (q : ℚ) :
    IsRat ((q : ℂ) • f) := by
  intro m
  obtain ⟨a, ha⟩ := hf m
  refine ⟨q * a, ?_⟩
  rw [show ⇑((q : ℂ) • f) = (q : ℂ) • ⇑f from rfl, ModularForm.qExpansion_smul one_pos oneMemG5,
    PowerSeries.coeff_smul, ha, smul_eq_mul]
  push_cast; ring

theorem isRat_sub {k : ℤ} {f g : ModularForm Γ₅ k} (hf : IsRat f) (hg : IsRat g) :
    IsRat (f - g) := by
  have h := isRat_add hf (isRat_smul hg (-1))
  rwa [show f + ((-1 : ℚ) : ℂ) • g = f - g by push_cast; rw [neg_one_smul, ← sub_eq_add_neg]] at h

/-- Diamond operators are multiplicative on the power products: `⟨u⟩(A^j B^(n-j)) =
(⟨u⟩A)^j (⟨u⟩B)^(n-j)`. -/
theorem diamondOp_P (A B : ModularForm Γ₅ 1) (u : (ZMod 5)ˣ) (n : ℕ) (j : Fin (n + 1)) :
    diamondOp (n : ℤ) u (P A B n j) = P (diamondOp 1 u A) (diamondOp 1 u B) n j := by
  obtain ⟨γ, hγ⟩ := Gamma0Map_toHomUnits_surjective (N := 5) u
  refine ModularForm.ext fun τ => ?_
  rw [P_apply, coe_diamondOp (n : ℤ) u γ hγ, coe_diamondOp 1 u γ hγ, coe_diamondOp 1 u γ hγ]
  change (⇑(P A B n j) ∣[(n : ℤ)] (γ : SL(2, ℤ))) τ =
    ((⇑A ∣[(1 : ℤ)] (γ : SL(2, ℤ))) τ) ^ (j : ℕ) * ((⇑B ∣[(1 : ℤ)] (γ : SL(2, ℤ))) τ) ^ (n - (j : ℕ))
  rw [ModularForm.SL_slash_apply, ModularForm.SL_slash_apply, ModularForm.SL_slash_apply, P_apply]
  have hd : UpperHalfPlane.denom (γ : SL(2, ℤ)) τ ^ (-(n : ℤ)) =
      (UpperHalfPlane.denom (γ : SL(2, ℤ)) τ ^ (-1 : ℤ)) ^ (j : ℕ) *
        (UpperHalfPlane.denom (γ : SL(2, ℤ)) τ ^ (-1 : ℤ)) ^ (n - (j : ℕ)) := by
    rw [← pow_add, Nat.add_sub_cancel' (Nat.lt_succ_iff.mp j.isLt), ← zpow_natCast, ← zpow_mul]
    congr 1
    ring
  rw [hd, mul_pow, mul_pow]
  ring

theorem P_isRat (A B : ModularForm Γ₅ 1) (hA : IsRat A) (hB : IsRat B) (n : ℕ)
    (j : Fin (n + 1)) : IsRat (P A B n j) := by
  let φ : ℚ →+* ℂ := Rat.castHom ℂ
  let aQ : PowerSeries ℚ := PowerSeries.mk fun m => (hA m).choose
  let bQ : PowerSeries ℚ := PowerSeries.mk fun m => (hB m).choose
  have ha : qExpansion 1 A = PowerSeries.map φ aQ := by
    ext m
    rw [PowerSeries.coeff_map, PowerSeries.coeff_mk]
    exact (hA m).choose_spec
  have hb : qExpansion 1 B = PowerSeries.map φ bQ := by
    ext m
    rw [PowerSeries.coeff_map, PowerSeries.coeff_mk]
    exact (hB m).choose_spec
  intro m
  refine ⟨PowerSeries.coeff m (aQ ^ (j : ℕ) * bQ ^ (n - (j : ℕ))), ?_⟩
  rw [qExpansion_P, ha, hb, ← map_pow, ← map_pow, ← map_mul, PowerSeries.coeff_map]
  rfl

theorem S_isRat (A B : ModularForm Γ₅ 1) (hA : IsRat A) (hB : IsRat B) (n : ℕ)
    (c : Fin (n + 1) → ℂ) (hc : ∀ j, ∃ q : ℚ, c j = q) : IsRat (S A B n c) := by
  intro m
  rw [coeff_S]
  choose cq hcq using hc
  choose pq hpq using fun j => P_isRat A B hA hB n j m
  refine ⟨∑ j, cq j * pq j, ?_⟩
  push_cast
  exact Finset.sum_congr rfl fun j _ => by rw [hcq, hpq]

theorem diamondOp_S (A B : ModularForm Γ₅ 1) (u : (ZMod 5)ˣ) (n : ℕ) (c : Fin (n + 1) → ℂ) :
    diamondOp (n : ℤ) u (S A B n c) = S (diamondOp 1 u A) (diamondOp 1 u B) n c := by
  rw [S, S, map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_smul, diamondOp_P]

/-- **Generic transfer.** If the images of `A` and `B` under `⟨u⟩` have rational `q`-expansions,
then `⟨u⟩` preserves rational `q`-expansions in every weight `n : ℕ`. -/
theorem isRat_diamondOp_of_images {A B : ModularForm Γ₅ 1}
    (hA0 : PowerSeries.coeff 0 (qExpansion 1 A) = 0)
    (hA1 : PowerSeries.coeff 1 (qExpansion 1 A) = 1)
    (hB0 : PowerSeries.coeff 0 (qExpansion 1 B) = 1)
    (hA : IsRat A) (hB : IsRat B) (u : (ZMod 5)ˣ)
    (hAu : IsRat (diamondOp 1 u A)) (hBu : IsRat (diamondOp 1 u B))
    (n : ℕ) (g : ModularForm Γ₅ (n : ℤ)) (hg : IsRat g) :
    IsRat (diamondOp (n : ℤ) u g) := by
  obtain ⟨c, hc, -⟩ := existsUnique_coords hA0 hA1 hB0 n g
  have hcq := coords_rat hA0 hA1 hB0 hA hB g hg c hc
  have hgS : g = S A B n c := ModularForm.ext fun τ => by rw [hc, S_apply]
  rw [hgS, diamondOp_S]
  exact S_isRat _ _ hAu hBu n c hcq

section Explicit

open CoeffRational.SharpLevelFiveBound

variable {A B : ModularForm Γ₅ 1}
  (hA : IsRat A) (hB : IsRat B)
  (hDA : diamondOp 1 two A = (-3 : ℂ) • A - B)
  (hDB : diamondOp 1 two B = (10 : ℂ) • A + (3 : ℂ) • B)
include hA hB hDA hDB

omit hA hB hDA hDB in
theorem isRat_neg_one_smul' {f : ModularForm Γ₅ 1} (hf : IsRat f) :
    IsRat (((-1 : ℂ) ^ (1 : ℤ)) • f) := by
  have h := isRat_smul hf (-1)
  rwa [show ((-1 : ℚ) : ℂ) = (-1 : ℂ) ^ (1 : ℤ) by norm_num] at h

omit hDB in
theorem isRat_two_A : IsRat (diamondOp 1 two A) := by
  rw [hDA]
  have h := isRat_sub (isRat_smul hA (-3)) hB
  rwa [show ((-3 : ℚ) : ℂ) = (-3 : ℂ) by norm_num] at h

omit hDA in
theorem isRat_two_B : IsRat (diamondOp 1 two B) := by
  rw [hDB]
  have h := isRat_add (isRat_smul hA 10) (isRat_smul hB 3)
  rwa [show ((10 : ℚ) : ℂ) = (10 : ℂ) by norm_num, show ((3 : ℚ) : ℂ) = (3 : ℂ) by norm_num] at h

/-- Every `⟨u⟩A` and `⟨u⟩B` has rational `q`-expansion. -/
theorem isRat_images (u : (ZMod 5)ˣ) :
    IsRat (diamondOp 1 u A) ∧ IsRat (diamondOp 1 u B) := by
  have h2A := isRat_two_A hA hB hDA
  have h2B := isRat_two_B hA hB hDB
  rcases unit_cases u with rfl | rfl | rfl | rfl
  · simpa using And.intro hA hB
  · exact ⟨h2A, h2B⟩
  · rw [TauCeti.diamondOp_neg_one, TauCeti.diamondOp_neg_one]
    exact ⟨isRat_neg_one_smul' hA, isRat_neg_one_smul' hB⟩
  · rw [diamondOp_mul, LinearMap.comp_apply, LinearMap.comp_apply, TauCeti.diamondOp_neg_one,
      TauCeti.diamondOp_neg_one]
    exact ⟨isRat_neg_one_smul' h2A, isRat_neg_one_smul' h2B⟩

/-- **Rational diamond action at level `5`, from the explicit basis data.** Under the stated
normalization, rationality and `⟨2⟩` equations for `A` and `B`, every diamond operator preserves
rational `q`-expansions of weight-`n` modular forms on `Γ₁(5)`, for every `n : ℕ`. -/
theorem isRat_diamondOp
    (hA0 : PowerSeries.coeff 0 (qExpansion 1 A) = 0)
    (hA1 : PowerSeries.coeff 1 (qExpansion 1 A) = 1)
    (hB0 : PowerSeries.coeff 0 (qExpansion 1 B) = 1)
    (n : ℕ) (g : ModularForm Γ₅ (n : ℤ)) (hg : IsRat g) (u : (ZMod 5)ˣ) :
    IsRat (diamondOp (n : ℤ) u g) :=
  isRat_diamondOp_of_images hA0 hA1 hB0 hA hB u (isRat_images hA hB hDA hDB u).1
    (isRat_images hA hB hDA hDB u).2 n g hg

/-- The same statement for cusp forms (through the cusp/modular coercion). -/
theorem isRat_diamondOpCusp
    (hA0 : PowerSeries.coeff 0 (qExpansion 1 A) = 0)
    (hA1 : PowerSeries.coeff 1 (qExpansion 1 A) = 1)
    (hB0 : PowerSeries.coeff 0 (qExpansion 1 B) = 1)
    (n : ℕ) (g : CuspForm Γ₅ (n : ℤ))
    (hg : ∀ m : ℕ, ∃ q : ℚ, (qExpansion 1 g).coeff m = q) (u : (ZMod 5)ˣ) :
    ∀ m : ℕ, ∃ q : ℚ, (qExpansion 1 (diamondOpCusp (n : ℤ) u g)).coeff m = q := by
  have h := isRat_diamondOp hA hB hDA hDB hA0 hA1 hB0 n (g : ModularForm Γ₅ (n : ℤ)) hg u
  rw [diamondOp_coe_cuspForm] at h
  exact h

open HeckeRing.GL2 in
/-- **Prime Hecke rationality at level `5`, from the explicit basis data.** For every weight
`k ≥ 0`, every prime `p` and every cusp form on `Γ₁(5)` with rational `q`-expansion, the Hecke
operator of the double coset `Γ₁(5) diag(1, p) Γ₁(5)` gives a rational `q`-expansion. -/
theorem isRat_hecke
    (hA0 : PowerSeries.coeff 0 (qExpansion 1 A) = 0)
    (hA1 : PowerSeries.coeff 1 (qExpansion 1 A) = 1)
    (hB0 : PowerSeries.coeff 0 (qExpansion 1 B) = 1)
    (k : ℤ) (hk : 0 ≤ k) {p : ℕ} (hp : p.Prime) (g : CuspForm Γ₅ k)
    (hg : ∀ m : ℕ, ∃ q : ℚ, (qExpansion 1 g).coeff m = q) :
    ∀ m : ℕ, ∃ q : ℚ,
      (qExpansion 1 (heckeSlashGamma1CuspFormEnd k (diagCosetGamma1 5 p) g)).coeff m = q := by
  obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le hk
  intro m
  rw [qExpansion_coeff_heckeSlashGamma1CuspFormEnd_diagCosetGamma1_of_prime (k := (n : ℤ)) hp g m]
  obtain ⟨q1, hq1⟩ := hg (p * m)
  rw [hq1]
  split_ifs with hpm
  · by_cases hcop : Nat.Coprime p 5
    · rw [diamondOpCuspNat_of_coprime _ hcop]
      obtain ⟨q2, hq2⟩ := isRat_diamondOpCusp hA hB hDA hDB hA0 hA1 hB0 n g hg
        (ZMod.unitOfCoprime p hcop) (m / p)
      exact ⟨q1 + (p : ℚ) ^ ((n : ℤ) - 1) * q2, by rw [hq2]; push_cast; ring⟩
    · rw [diamondOpCuspNat_of_not_coprime _ hcop, LinearMap.zero_apply]
      exact ⟨q1, by simp [qExpansion_zero]⟩
  · exact ⟨q1, by simp⟩

end Explicit

end ZInQ.Contrib.HeckePrimeRationality.ThetaFiveDiamondFromBasis
