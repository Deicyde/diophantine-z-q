/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: P2M.Sol.S_LanglandsTunnell_TateLocal_psiLocal_ne_one (git blob bbca077fb4cce786956e2913634c84f342fee1d6, sha256 3b9c763d5311403c5e8ed3377ea29a3d1396c40c46ba120f03c5935a214c6d87).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_LanglandsTunnell_StandardLocalConstantsAt
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_NumberField_StandardAddChar_psiLocal_eq_psiLocal_trace
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_NumberField_StandardAddChar_psiLocal_rat_eq_psiV

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

namespace P2MW.S_LanglandsTunnell_TateLocal_psiLocal_ne_one

set_option autoImplicit false

noncomputable section

namespace LanglandsTunnell
namespace TateLocal
namespace SolED33
open _root_.LanglandsTunnell.TateLocal
open _root_.LanglandsTunnell

open NumberField IsDedekindDomain NumberField.StandardAddChar

private theorem trace_surjective (p : HeightOneSpectrum (𝓞 ℚ)) {K : Type} [Field K] [NumberField K]
    (w : p.Extension (𝓞 K)) :
    Function.Surjective
      (Algebra.trace (p.adicCompletion ℚ) (w.1.adicCompletion K)) := by
  intro c
  haveI : CharZero (p.adicCompletion ℚ) :=
    charZero_of_injective_algebraMap (algebraMap ℚ (p.adicCompletion ℚ)).injective
  have hn : (Module.finrank (p.adicCompletion ℚ) (w.1.adicCompletion K) :
      p.adicCompletion ℚ) ≠ 0 :=
    Nat.cast_ne_zero.mpr Module.finrank_pos.ne'
  refine ⟨algebraMap (p.adicCompletion ℚ) (w.1.adicCompletion K)
    (c / (Module.finrank (p.adicCompletion ℚ) (w.1.adicCompletion K) :
      p.adicCompletion ℚ)), ?_⟩
  rw [Algebra.trace_algebraMap, nsmul_eq_mul, mul_comm, div_mul_cancel₀ _ hn]

private theorem main_of_dock_of_base {K : Type} [Field K] [NumberField K]
    (v : HeightOneSpectrum (𝓞 K))
    (p : HeightOneSpectrum (𝓞 ℚ)) (w : p.Extension (𝓞 K)) (hw : w.1 = v)
    (hdock : ∀ x : w.1.adicCompletion K,
      psiLocal K w.1 x
        = psiLocal ℚ p (Algebra.trace (p.adicCompletion ℚ) (w.1.adicCompletion K) x))
    (hbase : psiLocal ℚ p ≠ 1) :
    psiLocal K v ≠ 1 := by
  subst hw
  intro htriv
  apply hbase
  ext y
  obtain ⟨x, hx⟩ := trace_surjective p w y
  have := hdock x
  rw [htriv] at this
  simp only [AddChar.one_apply] at this
  rw [AddChar.one_apply, ← hx, ← this]

private theorem main_of_docks {K : Type} [Field K] [NumberField K]
    (v : HeightOneSpectrum (𝓞 K))
    (p : HeightOneSpectrum (𝓞 ℚ)) (w : p.Extension (𝓞 K)) (hw : w.1 = v)
    (hdock : ∀ x : w.1.adicCompletion K,
      psiLocal K w.1 x
        = psiLocal ℚ p (Algebra.trace (p.adicCompletion ℚ) (w.1.adicCompletion K) x))
    (hR2 : psiLocal ℚ p = psiV p) :
    psiLocal K v ≠ 1 :=
  main_of_dock_of_base v p w hw hdock
    (fun h => psiV_algebraMap_inv_ne_one p (by rw [← hR2, h]; rfl))

end LanglandsTunnell.TateLocal.SolED33

end

theorem solution (K : Type) [Field K] [NumberField K]
    (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)) :
    NumberField.StandardAddChar.psiLocal K v ≠ 1 :=
  LanglandsTunnell.TateLocal.SolED33.main_of_docks v
    (v.under (NumberField.RingOfIntegers ℚ)) ⟨v, rfl⟩ rfl
    (NumberField.StandardAddChar.psiLocal_eq_psiLocal_trace ℚ K
      (v.under (NumberField.RingOfIntegers ℚ)) ⟨v, rfl⟩)
    (NumberField.StandardAddChar.psiLocal_rat_eq_psiV
      (v.under (NumberField.RingOfIntegers ℚ)))
