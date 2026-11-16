/-
Vendored from anthropics/fermats-last-theorem @ 6e837e75355538c7f80bab5b956861e86c4eacc2.
Apache License 2.0; see LICENSE, NOTICE.upstream and ATTRIBUTION.upstream.md.
W28 compatibility changes: relocated imports; removed imported-only global attribute
suppressions and unused P2M.Util; direct exact solution wrappers; upstream Lake options
made explicit below. Exact bridge cuts, when present, are recorded in SOURCE_MANIFEST.json.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB4W28FineModuli.Vendor.AnthropicFLT.P2M.Sol.S_Rat_exists_ternary_isotropic_adicCompletion_of_intCast_notMem

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false


set_option autoImplicit false

open IsDedekindDomain NumberField

theorem Rat.exists_ternary_isotropic_adicCompletion_of_intCast_notMem
    (m n : ℤ) (v : HeightOneSpectrum (𝓞 ℚ))
    (h2 : (2 : 𝓞 ℚ) ∉ v.asIdeal) (hm : ((m : ℤ) : 𝓞 ℚ) ∉ v.asIdeal) (hn : ((n : ℤ) : 𝓞 ℚ) ∉ v.asIdeal) :
    ∃ z x y : v.adicCompletion ℚ, ¬ (z = 0 ∧ x = 0 ∧ y = 0) ∧
      z ^ 2 - (algebraMap ℚ (v.adicCompletion ℚ) (m : ℚ)) * x ^ 2
        - (algebraMap ℚ (v.adicCompletion ℚ) (n : ℚ)) * y ^ 2 = 0 := by apply @_root_.P2MW.S_Rat_exists_ternary_isotropic_adicCompletion_of_intCast_notMem.solution <;> assumption
