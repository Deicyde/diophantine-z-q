/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: P2M.Sol.S_Algebra_IsSeparable_of_coprime_finrank_expChar
Modified for the Z-in-Q kernel (2026-11-15, task flt-cqj2): local import paths are relocated
(`P2M.Util` is the copy published by Cloud Worker 2) and the upstream lakefile options are set
as `set_option` lines after the imports; any other change is marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib.FieldTheory.PurelyInseparable.Basic
import Mathlib.FieldTheory.SeparableClosure
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.P2M.Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

namespace P2MW.S_Algebra_IsSeparable_of_coprime_finrank_expChar

set_option autoImplicit false

theorem solution (F E : Type*) [Field F] [Field E] [Algebra F E]
    [FiniteDimensional F E] (q : ℕ) [ExpChar F q] (h : Nat.Coprime (Module.finrank F E) q) :
    Algebra.IsSeparable F E := by
  rw [← Field.finSepDegree_eq_finrank_iff]

  haveI : ExpChar (separableClosure F E) q :=
    expChar_of_injective_algebraMap (algebraMap F (separableClosure F E)).injective q
  haveI : IsPurelyInseparable (separableClosure F E) E := separableClosure.isPurelyInseparable F E
  obtain ⟨n, hn⟩ := IsPurelyInseparable.finrank_eq_pow (separableClosure F E) E q
  have hins : Field.finInsepDegree F E = q ^ n := hn
  have hmul := Field.finSepDegree_mul_finInsepDegree F E
  rw [hins] at hmul

  have hdvd : q ^ n ∣ Module.finrank F E := ⟨Field.finSepDegree F E, by rw [mul_comm]; exact hmul.symm⟩
  have hone : q ^ n = 1 := Nat.Coprime.eq_one_of_dvd (Nat.Coprime.pow_left n h.symm) hdvd
  rw [hone, mul_one] at hmul
  exact hmul
