/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: P2M.Sol.S_PadicAlgCl_isIntegral_padicInt_iff_norm_le_one
Modified for the Z-in-Q kernel (2026-11-16, p-divisible Hodge-Tate port): local import paths
are relocated, the P2M.Util elaborators are replaced by standard Lean commands or explicit terms,
local notations are expanded in place, and the upstream lakefile options are set as `set_option`
lines after the imports; see ZInQKernel/Contrib/CloudB3SC3PDivHodge/PORTING.md. Any other change is marked `-- [port]`.
Original copyright/attribution notices: NOTICE.upstream and ATTRIBUTION.upstream.md in
ZInQKernel/Contrib/CloudB3SC3PDivHodge/Vendor/AnthropicFLT/; license: LICENSE in that directory.
-/
import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

namespace P2MW.S_PadicAlgCl_isIntegral_padicInt_iff_norm_le_one

set_option autoImplicit false

noncomputable section

namespace TP9P1

open Polynomial

variable (p : ℕ) [Fact p.Prime]

-- [port T8] local notation "Ω" expanded in place

theorem norm_le_one_of_isIntegral {x : (PadicAlgCl p)} (hx : IsIntegral ℤ_[p] x) : ‖x‖ ≤ 1 := by
  have h1 : minpoly ℚ_[p] x = (minpoly ℤ_[p] x).map (algebraMap ℤ_[p] ℚ_[p]) :=
    minpoly.isIntegrallyClosed_eq_field_fractions' ℚ_[p] hx
  rw [← PadicAlgCl.spectralNorm_eq, spectralNorm,
    spectralValue_le_one_iff (minpoly.monic (Algebra.IsIntegral.isIntegral x))]
  intro n
  rw [h1, coeff_map]
  exact PadicInt.norm_le_one _

theorem isIntegral_of_norm_le_one {x : (PadicAlgCl p)} (hx : ‖x‖ ≤ 1) : IsIntegral ℤ_[p] x := by
  have hint : IsIntegral ℚ_[p] x := Algebra.IsIntegral.isIntegral x
  have hmonic : (minpoly ℚ_[p] x).Monic := minpoly.monic hint
  have hcoeff : ∀ n, ‖(minpoly ℚ_[p] x).coeff n‖ ≤ 1 := by
    rw [← spectralValue_le_one_iff hmonic]
    change spectralNorm ℚ_[p] (PadicAlgCl p) x ≤ 1
    rwa [PadicAlgCl.spectralNorm_eq]

  have hlifts : minpoly ℚ_[p] x ∈ Polynomial.lifts (algebraMap ℤ_[p] ℚ_[p]) := by
    rw [Polynomial.lifts_iff_coeff_lifts]
    intro n
    exact ⟨⟨(minpoly ℚ_[p] x).coeff n, hcoeff n⟩, rfl⟩
  obtain ⟨g, hgmap, -, hgmonic⟩ := Polynomial.lifts_and_natDegree_eq_and_monic hlifts hmonic
  refine ⟨g, hgmonic, ?_⟩
  rw [← aeval_def, ← minpoly.aeval ℚ_[p] x, aeval_def, aeval_def,
    IsScalarTower.algebraMap_eq ℤ_[p] ℚ_[p] (PadicAlgCl p), ← eval₂_map, hgmap]

theorem main (x : (PadicAlgCl p)) : IsIntegral ℤ_[p] x ↔ ‖x‖ ≤ 1 :=
  ⟨norm_le_one_of_isIntegral p, isIntegral_of_norm_le_one p⟩

end TP9P1

end

theorem solution (p : ℕ) [Fact p.Prime] (x : PadicAlgCl p) : IsIntegral ℤ_[p] x ↔ ‖x‖ ≤ 1 :=
  TP9P1.main p x
