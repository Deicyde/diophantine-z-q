/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
-- Backported from Tau Ceti (https://github.com/TauCetiProject/TauCeti, commit 4d91513e4d30, module
-- TauCeti.NumberTheory.ModularForms.Newforms.Descent.CharacterSpace), Apache-2.0: a declaration added to that module
-- after commit 5a01f5fe, whose version is vendored as
-- `ZInQKernel.Contrib.TauCeti.NumberTheory.ModularForms.Newforms.Descent.CharacterSpace`.
module

public import ZInQKernel.Contrib.TauCeti.NumberTheory.ModularForms.Newforms.Descent.CharacterSpace
import ZInQKernel.Contrib.TauCeti.NumberTheory.ModularForms.Cusps.Basic

/-!
# Descent of forms supported on the multiples of `q`, at any level (backport)

* `TauCeti.exists_mem_cuspFormCharSpace_qExpansion_coeff_eq_ite_dvd`: a form of level `M`
  supported on the multiples of any `q` is `V_q` of a form of the same level and nebentypus, on
  coefficients.
-/

public section

open Matrix.SpecialLinearGroup UpperHalfPlane CongruenceSubgroup

open scoped MatrixGroups ModularForm

namespace TauCeti

variable {k : ℤ}

/-- **A form supported on the multiples of `q` is `V_q` of a form of the same level.** If
`F ∈ S_k(Γ₁(M), χ)` has its `q`-expansion supported on the multiples of `q`, then there is
`G ∈ S_k(Γ₁(M), χ)` with `a_n(F) = a_{n/q}(G)` for `q ∣ n` and `a_n(F) = 0` otherwise. Nothing
relates `q` to `M`. For `q ≠ 0` the descent is carried out at level `q M`, where `q` divides the
level, and lands back at level `q M / q = M`. For `q = 0` the hypotheses force every coefficient of
`F` to vanish (the constant term of a cusp form is zero), so `G = 0` works. -/
theorem exists_mem_cuspFormCharSpace_qExpansion_coeff_eq_ite_dvd {M q : ℕ} [NeZero M]
    {χ : (ZMod M)ˣ →* ℂˣ} {F : CuspForm ((Gamma1 M).map (mapGL ℝ)) k}
    (hFχ : F ∈ cuspFormCharSpace k χ) (hF : QExpansionSupportedOnDvd q F) :
    ∃ G ∈ cuspFormCharSpace k χ,
      ∀ n, (qExpansion 1 F).coeff n = if q ∣ n then (qExpansion 1 G).coeff (n / q) else 0 := by
  rcases eq_or_ne q 0 with rfl | hq
  · -- at `q = 0` the support condition kills every coefficient of `F`, as the constant term of a
    -- cusp form vanishes, so `G = 0` works
    refine ⟨0, Submodule.zero_mem _, fun n ↦ ?_⟩
    rcases eq_or_ne n 0 with rfl | hn
    · simp [CuspFormClass.qExpansion_coeff_zero F one_pos (one_mem_strictPeriods_Gamma1_map M),
        qExpansion_zero]
    · simp [PowerSeries.isSupportedOnDvd_iff.mp (qExpansionSupportedOnDvd_iff.mp hF) n
        (by simpa using hn), qExpansion_zero]
  have : NeZero q := ⟨hq⟩
  have hMq : M ∣ q * M / q := by rw [Nat.mul_div_cancel_left M (NeZero.pos q)]
  have hqM : q * M / q ∣ M := by rw [Nat.mul_div_cancel_left M (NeZero.pos q)]
  -- read `F` at level `q M` and descend there, to the level `q M / q`
  obtain ⟨G, hGχ, hG⟩ :=
    exists_mem_cuspFormCharSpace_qExpansion_coeff_eq_ite_dvd_of_qExpansionSupportedOnDvd
      (dvd_mul_right q M) (χ.comp (ZMod.unitsMap hMq))
      (G := CuspForm.restrict (Gamma1_map_le_Gamma1_map_of_dvd (dvd_mul_left M q)) F)
      (by
        have := CuspForm.restrict_mem_cuspFormCharSpace χ (dvd_mul_left M q) hFχ
        rwa [MonoidHom.comp_assoc, ZMod.unitsMap_comp])
      (by
        rw [qExpansionSupportedOnDvd_iff, CuspForm.coe_restrict]
        exact qExpansionSupportedOnDvd_iff.mp hF)
  -- and read the descended form back at level `M`
  refine ⟨CuspForm.restrict (Gamma1_map_le_Gamma1_map_of_dvd hqM) G, ?_, fun n ↦ ?_⟩
  · have := CuspForm.restrict_mem_cuspFormCharSpace _ hqM hGχ
    rwa [MonoidHom.comp_assoc, ZMod.unitsMap_comp, ZMod.unitsMap_self, MonoidHom.comp_id] at this
  · rw [CuspForm.coe_restrict, ← hG n, CuspForm.coe_restrict]

end TauCeti
