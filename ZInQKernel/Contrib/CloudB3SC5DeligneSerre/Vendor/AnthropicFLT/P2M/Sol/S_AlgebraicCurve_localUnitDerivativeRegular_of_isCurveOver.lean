/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: P2M.Sol.S_AlgebraicCurve_localUnitDerivativeRegular_of_isCurveOver (git blob ef68604aa3087c2641bbd4a6ca4678575bd05629, sha256 15ed41404443cd25d5d473fdef45f3681314e83323fdf32696a7f33fb58212fa).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Definitions.Def_AlgebraicCurve_DivisorClassGroup
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Definitions.Def_AlgebraicCurve_IsCurveOver
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_ModularCurve_CanonicalDivisor
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_ModularCurve_CanonicalDivisorUniformizer
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicCurve_exists_mem_D_eq_smul_D_of_isCurveOver
import Batteries.Tactic.Alias

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

namespace AlgebraicCurve
end AlgebraicCurve
namespace AlgebraicCurve.Place
end AlgebraicCurve.Place

namespace P2MW.S_AlgebraicCurve_localUnitDerivativeRegular_of_isCurveOver

set_option autoImplicit false

namespace AlgebraicCurve
export _root_.AlgebraicCurve (Place IsCurveOver IsCurveOver.kaehler_free_rank_one exists_mem_D_eq_smul_D_of_isCurveOver)
open _root_.AlgebraicCurve
namespace Place
export _root_.AlgebraicCurve.Place (ord ord_unit_smul_zpow exists_unit_mul_zpow toValuationSubring DCoordGenerates differentialCoeff differentialCoeff_unique uniformizer ord_uniformizer)
open _root_.AlgebraicCurve.Place
variable {K F : Type*} [Field K] [Field F] [Algebra K F] (v : Place K F)
private theorem _root_.AlgebraicCurve.Place.ord_nonneg_of_mem {f : F} (hf : f ∈ v.toValuationSubring) : 0 ≤ v.ord f := by
  rcases eq_or_ne f 0 with rfl | hf0
  · simp
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible v.toValuationSubring
  obtain ⟨n, u, hu⟩ :=
    IsDiscreteValuationRing.eq_unit_mul_pow_irreducible
      (x := (⟨f, hf⟩ : v.toValuationSubring)) (by simpa [Subtype.ext_iff] using hf0) hπ
  have hcoe : f = ((u : v.toValuationSubring) : F) * ((π : F) ^ (n : ℤ)) := by
    have h := congrArg (Subtype.val) hu
    push_cast at h
    rw [zpow_natCast]
    exact h
  rw [hcoe, v.ord_unit_smul_zpow u hπ (n : ℤ)]
  exact Int.natCast_nonneg n
alias ord_nonneg_of_mem := _root_.AlgebraicCurve.Place.ord_nonneg_of_mem
private theorem _root_.AlgebraicCurve.Place.mem_of_ord_nonneg {f : F} (hf : f ≠ 0) (h : 0 ≤ v.ord f) :
    f ∈ v.toValuationSubring := by
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible v.toValuationSubring
  obtain ⟨u, hu⟩ := v.exists_unit_mul_zpow hf hπ
  rw [hu, show v.ord f = (((v.ord f).toNat : ℕ) : ℤ) from (Int.toNat_of_nonneg h).symm,
    zpow_natCast]
  exact mul_mem (u : v.toValuationSubring).2 (pow_mem (π : v.toValuationSubring).2 _)
alias mem_of_ord_nonneg := _root_.AlgebraicCurve.Place.mem_of_ord_nonneg
theorem mem_iff_ord_nonneg {f : F} (hf : f ≠ 0) :
    f ∈ v.toValuationSubring ↔ 0 ≤ v.ord f :=
  ⟨v.ord_nonneg_of_mem, v.mem_of_ord_nonneg hf⟩
end Place
end AlgebraicCurve

namespace AlgebraicCurve
export _root_.AlgebraicCurve (Place IsCurveOver IsCurveOver.kaehler_free_rank_one exists_mem_D_eq_smul_D_of_isCurveOver)
open _root_.AlgebraicCurve

theorem localUnitDerivativeRegular_of_isCurveOver_port {K : Type*} {F' : Type*} [Field K] [Field F'] [Algebra K F']
    [PerfectField K] [Algebra.EssFiniteType K F'] [IsCurveOver K F'] [∀ w : Place K F', w.DCoordGenerates] :
    ∀ (w : Place K F') (u : F'), u ≠ 0 → w.ord u = 0 →
      w.differentialCoeff (KaehlerDifferential.D K F' u) = 0
        ∨ 0 ≤ w.ord (w.differentialCoeff (KaehlerDifferential.D K F' u)) := by
  intro w u hu h0
  haveI : Nontrivial Ω[F'⁄K] :=
    Module.nontrivial_of_finrank_eq_succ (IsCurveOver.kaehler_free_rank_one (K := K) (F := F')).2
  have hu_mem : u ∈ w.toValuationSubring := w.mem_of_ord_nonneg hu (by rw [h0])
  obtain ⟨c, hc, hcu⟩ :=
    exists_mem_D_eq_smul_D_of_isCurveOver (K := K) w (π := w.uniformizer) w.ord_uniformizer hu_mem
  have hcoeff : w.differentialCoeff (KaehlerDifferential.D K F' u) = c :=
    w.differentialCoeff_unique (by rw [hcu]; rfl)
  rw [hcoeff]
  rcases eq_or_ne c 0 with rfl | hc0
  · exact Or.inl rfl
  · exact Or.inr (w.ord_nonneg_of_mem hc)
end AlgebraicCurve

open _root_.AlgebraicCurve _root_.P2MW.S_AlgebraicCurve_localUnitDerivativeRegular_of_isCurveOver.AlgebraicCurve in
theorem solution {K : Type*} {F' : Type*} [Field K] [Field F'] [Algebra K F']
    [PerfectField K] [Algebra.EssFiniteType K F'] [IsCurveOver K F'] [∀ w : Place K F', w.DCoordGenerates] :
    ∀ (w : Place K F') (u : F'), u ≠ 0 → w.ord u = 0 →
      w.differentialCoeff (KaehlerDifferential.D K F' u) = 0
        ∨ 0 ≤ w.ord (w.differentialCoeff (KaehlerDifferential.D K F' u)) :=
  AlgebraicCurve.localUnitDerivativeRegular_of_isCurveOver_port
