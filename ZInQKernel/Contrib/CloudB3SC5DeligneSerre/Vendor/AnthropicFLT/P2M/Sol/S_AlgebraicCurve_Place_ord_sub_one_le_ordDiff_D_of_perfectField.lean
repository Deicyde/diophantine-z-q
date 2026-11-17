/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: P2M.Sol.S_AlgebraicCurve_Place_ord_sub_one_le_ordDiff_D_of_perfectField (git blob b5df252e0bc4c90d17cc992202e1758598421aa2, sha256 3b7aae1d6a62d8fa270ecedc88bc257853b9e2237582f867ef2915953b7058aa).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AlgebraicCurve_Differentials
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicCurve_Place_diffCoeff_smul_D_of_ord_eq_one
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicCurve_Place_diffCoeff_smul_D_eq_of_ord_eq_one
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicCurve_Place_ord_diffCoeff_D_nonneg_of_perfectField
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicCurve_Place_exists_ord_eq_one
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicCurve_Place_min_ord_le_ord_add
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicCurve_Place_ord_algebraMap
import Batteries.Tactic.Alias

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

namespace AlgebraicCurve.Place
end AlgebraicCurve.Place
namespace AlgebraicCurve
end AlgebraicCurve

namespace P2MW.S_AlgebraicCurve_Place_ord_sub_one_le_ordDiff_D_of_perfectField

namespace AlgebraicCurve
export _root_.AlgebraicCurve (Place)
namespace Place
export _root_.AlgebraicCurve.Place (diffCoeff ordDiff ordDiff_def ord_uniformizer_alt uniformizer_alt ord ord_zero ord_mul ord_inv ord_zpow diffCoeff_smul_D_of_ord_eq_one diffCoeff_smul_D_eq_of_ord_eq_one ord_diffCoeff_D_nonneg_of_perfectField exists_ord_eq_one min_ord_le_ord_add ord_algebraMap)
open _root_.AlgebraicCurve.Place
open _root_.AlgebraicCurve

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

private theorem _root_.AlgebraicCurve.Place.ordDiff_smul_impl [PerfectField K] (x : F)
    [Algebra.IsAlgebraic (IntermediateField.adjoin K ({x} : Set F)) F] (v : AlgebraicCurve.Place K F)
    {g : F} (hg : g ≠ 0) {ω : Ω[F⁄K]} (hω : ω ≠ 0) :
    v.ordDiff (g • ω) = v.ord g + v.ordDiff ω := by
  have ht : v.ord v.uniformizer_alt = 1 := v.ord_uniformizer_alt v.exists_ord_eq_one
  have hrep : diffCoeff v.uniformizer_alt ω • KaehlerDifferential.D K F v.uniformizer_alt = ω :=
    v.diffCoeff_smul_D_of_ord_eq_one x ht ω
  have hgo : g • ω = (g * diffCoeff v.uniformizer_alt ω) • KaehlerDifferential.D K F v.uniformizer_alt := by
    conv_lhs => rw [← hrep]
    rw [smul_smul]
  have hco : diffCoeff v.uniformizer_alt (g • ω) = g * diffCoeff v.uniformizer_alt ω := by
    rw [hgo]
    exact v.diffCoeff_smul_D_eq_of_ord_eq_one x ht _
  have hc0 : diffCoeff v.uniformizer_alt ω ≠ 0 := by
    intro h0
    apply hω
    rw [← hrep, h0, zero_smul]
  rw [ordDiff_def, ordDiff_def, hco, v.ord_mul hg hc0]

alias ordDiff_smul_impl := _root_.AlgebraicCurve.Place.ordDiff_smul_impl
private theorem ord_pow_nat (v : AlgebraicCurve.Place K F) (t : F) (m : ℕ) :
    v.ord (t ^ m) = (m : ℤ) * v.ord t := by
  rw [← zpow_natCast t m, v.ord_zpow]

private theorem _root_.AlgebraicCurve.Place.H2_pos [PerfectField K] (x : F)
    [FiniteDimensional (IntermediateField.adjoin K ({x} : Set F)) F] (v : AlgebraicCurve.Place K F)
    {f : F} (hD : KaehlerDifferential.D K F f ≠ 0) (hn : 0 ≤ v.ord f) :
    v.ord f - 1 ≤ v.ordDiff (KaehlerDifferential.D K F f) := by
  have ht : v.ord v.uniformizer_alt = 1 := v.ord_uniformizer_alt v.exists_ord_eq_one
  set t := v.uniformizer_alt with htdef
  have ht0 : t ≠ 0 := by
    intro h0
    rw [h0, v.ord_zero] at ht
    omega
  have hf0 : f ≠ 0 := by
    rintro rfl
    rw [map_zero] at hD
    exact hD rfl
  set m : ℕ := (v.ord f).toNat with hmdef
  have hm : (m : ℤ) = v.ord f := Int.toNat_of_nonneg hn
  have htm0 : t ^ m ≠ 0 := pow_ne_zero m ht0
  set u : F := f * (t ^ m)⁻¹ with hudef
  have hu0 : u ≠ 0 := mul_ne_zero hf0 (inv_ne_zero htm0)
  have hordu : v.ord u = 0 := by
    rw [hudef, v.ord_mul hf0 (inv_ne_zero htm0), v.ord_inv, ord_pow_nat, ht, hm]
    ring
  have hfeq : f = u * t ^ m := by
    rw [hudef, mul_assoc, inv_mul_cancel₀ htm0, mul_one]

  set cu : F := diffCoeff t (KaehlerDifferential.D K F u) with hcudef
  have hcu_nonneg : 0 ≤ v.ord cu :=
    v.ord_diffCoeff_D_nonneg_of_perfectField x ht (le_of_eq hordu.symm)
  have hrepu : cu • KaehlerDifferential.D K F t = KaehlerDifferential.D K F u :=
    v.diffCoeff_smul_D_of_ord_eq_one x ht _
  have hDtm : KaehlerDifferential.D K F (t ^ m) =
      ((m : F) * t ^ (m - 1)) • KaehlerDifferential.D K F t := by
    rw [Derivation.leibniz_pow, ← Nat.cast_smul_eq_nsmul F m, smul_smul]
  have hdecomp : KaehlerDifferential.D K F f =
      (u * ((m : F) * t ^ (m - 1)) + t ^ m * cu) • KaehlerDifferential.D K F t := by
    conv_lhs => rw [hfeq]
    rw [Derivation.leibniz, hDtm, ← hrepu, smul_smul, smul_smul, add_smul]
  have hcoeff : diffCoeff t (KaehlerDifferential.D K F f) =
      u * ((m : F) * t ^ (m - 1)) + t ^ m * cu := by
    rw [hdecomp]
    exact v.diffCoeff_smul_D_eq_of_ord_eq_one x ht _
  have hsum0 : u * ((m : F) * t ^ (m - 1)) + t ^ m * cu ≠ 0 := by
    intro h0
    apply hD
    rw [hdecomp, h0, zero_smul]
  rw [ordDiff_def, ← htdef, hcoeff]
  rcases eq_or_ne (u * ((m : F) * t ^ (m - 1))) 0 with ha | ha
  ·
    rw [ha, zero_add] at hsum0 ⊢
    have hcu0 : cu ≠ 0 := fun h => hsum0 (by rw [h, mul_zero])
    rw [v.ord_mul htm0 hcu0, ord_pow_nat, ht]
    omega
  · have hmF : (m : F) ≠ 0 := by
      intro h
      exact ha (by rw [h, zero_mul, mul_zero])
    have hm1 : 1 ≤ m := by
      rcases Nat.eq_zero_or_pos m with h | h
      · exact absurd (by rw [h, Nat.cast_zero] : (m : F) = 0) hmF
      · exact h
    have hordm : v.ord ((m : F)) = 0 := by
      have hcast : ((m : F)) = algebraMap K F ((m : K)) := by
        rw [map_natCast]
      rw [hcast, v.ord_algebraMap]
    have horda : v.ord (u * ((m : F) * t ^ (m - 1))) = (m : ℤ) - 1 := by
      have h1 : (m : F) * t ^ (m - 1) ≠ 0 := mul_ne_zero hmF (pow_ne_zero _ ht0)
      rw [v.ord_mul hu0 h1, v.ord_mul hmF (pow_ne_zero _ ht0), ord_pow_nat, ht, hordu, hordm]
      have : ((m - 1 : ℕ) : ℤ) = (m : ℤ) - 1 := by
        omega
      rw [this]
      ring
    rcases eq_or_ne cu 0 with hcu0 | hcu0
    ·
      rw [hcu0, mul_zero, add_zero, horda]
      omega
    · have hordb : v.ord (t ^ m * cu) = (m : ℤ) + v.ord cu := by
        rw [v.ord_mul htm0 hcu0, ord_pow_nat, ht]
        ring
      have hmin := v.min_ord_le_ord_add ha (by exact mul_ne_zero htm0 hcu0) hsum0
      rw [horda, hordb] at hmin
      have : min ((m : ℤ) - 1) ((m : ℤ) + v.ord cu) = (m : ℤ) - 1 := by
        omega
      rw [this] at hmin
      omega

alias H2_pos := _root_.AlgebraicCurve.Place.H2_pos
private theorem H2_impl [PerfectField K] (x : F)
    [FiniteDimensional (IntermediateField.adjoin K ({x} : Set F)) F] (v : AlgebraicCurve.Place K F)
    {f : F} (hD : KaehlerDifferential.D K F f ≠ 0) :
    v.ord f - 1 ≤ v.ordDiff (KaehlerDifferential.D K F f) := by
  rcases le_or_gt 0 (v.ord f) with hn | hn
  · exact v.H2_pos x hD hn
  ·
    have hf0 : f ≠ 0 := by
      rintro rfl
      rw [map_zero] at hD
      exact hD rfl
    have hDinv : KaehlerDifferential.D K F f⁻¹ ≠ 0 := by
      intro h0
      apply hD
      have hleib := Derivation.leibniz_inv (KaehlerDifferential.D K F) f
      rw [h0] at hleib
      have hne : (-f⁻¹ ^ 2 : F) ≠ 0 := by
        simpa using hf0
      rcases smul_eq_zero.mp hleib.symm with h | h
      · exact absurd h hne
      · exact h
    have hpos := v.H2_pos x hDinv (by rw [v.ord_inv]; omega)
    have hleib := Derivation.leibniz_inv (KaehlerDifferential.D K F) f
    have hsmul : v.ordDiff (KaehlerDifferential.D K F f⁻¹) =
        v.ord (-f⁻¹ ^ 2) + v.ordDiff (KaehlerDifferential.D K F f) := by
      rw [hleib]
      exact v.ordDiff_smul_impl x (by simpa using hf0) hD
    have hordneg : v.ord (-f⁻¹ ^ 2 : F) = -2 * v.ord f := by
      have hneg1 : (-f⁻¹ ^ 2 : F) = algebraMap K F (-1) * f⁻¹ ^ 2 := by
        rw [map_neg, map_one]
        ring
      have h2 : (f⁻¹ ^ 2 : F) ≠ 0 := by
        simpa using hf0
      have hneg1ne : algebraMap K F (-1) ≠ 0 := by
        rw [map_neg, map_one]
        exact neg_ne_zero.mpr one_ne_zero
      rw [hneg1, v.ord_mul hneg1ne h2,
        v.ord_algebraMap, ← zpow_natCast (f⁻¹) 2, v.ord_zpow, v.ord_inv]
      ring
    rw [v.ord_inv] at hpos
    rw [hsmul, hordneg] at hpos
    omega

end AlgebraicCurve.Place

theorem solution {K F : Type*} [Field K] [Field F] [Algebra K F] [PerfectField K] (x : F)
    [FiniteDimensional (IntermediateField.adjoin K ({x} : Set F)) F] (v : AlgebraicCurve.Place K F) {f : F}
    (hD : KaehlerDifferential.D K F f ≠ 0) :
    v.ord f - 1 ≤ v.ordDiff (KaehlerDifferential.D K F f) :=
  AlgebraicCurve.Place.H2_impl x v hD
