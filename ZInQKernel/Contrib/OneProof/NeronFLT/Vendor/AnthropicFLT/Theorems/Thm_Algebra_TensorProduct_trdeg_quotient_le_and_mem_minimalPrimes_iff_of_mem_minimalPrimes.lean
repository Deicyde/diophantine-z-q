/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_Algebra_TensorProduct_trdeg_quotient_le_and_mem_minimalPrimes_iff_of_mem_minimalPrimes
Modified for the Z-in-Q kernel (2026-11-16, task neron-flt): local import paths are relocated
(`P2M.Util` is the copy published by Cloud Worker 2) and the upstream lakefile options are set
as `set_option` lines after the imports; any other change is marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.P2M.Util
import ZInQKernel.Contrib.OneProof.NeronFLT.Vendor.AnthropicFLT.P2M.Sol.S_Algebra_TensorProduct_trdeg_quotient_le_and_mem_minimalPrimes_iff_of_mem_minimalPrimes

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

set_option autoImplicit false

open TensorProduct

universe u

theorem Algebra.TensorProduct.trdeg_quotient_le_and_mem_minimalPrimes_iff_of_mem_minimalPrimes
    {R A A' : Type u} [CommRing R] [CommRing A] [CommRing A'] [Algebra R A] [Algebra R A']
    [Algebra.FiniteType R A']
    (𝔓 : Ideal (A ⊗[R] A')) [𝔓.IsPrime]
    (h : 𝔓.comap (Algebra.TensorProduct.includeRight (R := R) (A := A) (B := A')).toRingHom ∈
      ((𝔓.under R).map (algebraMap R A')).minimalPrimes) :
    Algebra.trdeg (A ⧸ 𝔓.under A) ((A ⊗[R] A') ⧸ 𝔓) ≤
        Algebra.trdeg
          (R ⧸ (𝔓.comap (Algebra.TensorProduct.includeRight (R := R) (A := A) (B := A')).toRingHom).under R)
          (A' ⧸ 𝔓.comap (Algebra.TensorProduct.includeRight (R := R) (A := A) (B := A')).toRingHom) ∧
      (𝔓 ∈ ((𝔓.under A).map (algebraMap A (A ⊗[R] A'))).minimalPrimes ↔
        Algebra.trdeg (A ⧸ 𝔓.under A) ((A ⊗[R] A') ⧸ 𝔓) =
          Algebra.trdeg
            (R ⧸ (𝔓.comap (Algebra.TensorProduct.includeRight (R := R) (A := A) (B := A')).toRingHom).under R)
            (A' ⧸ 𝔓.comap (Algebra.TensorProduct.includeRight (R := R) (A := A) (B := A')).toRingHom)) := by p2m_exact_reverting @_root_.P2MW.S_Algebra_TensorProduct_trdeg_quotient_le_and_mem_minimalPrimes_iff_of_mem_minimalPrimes.solution
