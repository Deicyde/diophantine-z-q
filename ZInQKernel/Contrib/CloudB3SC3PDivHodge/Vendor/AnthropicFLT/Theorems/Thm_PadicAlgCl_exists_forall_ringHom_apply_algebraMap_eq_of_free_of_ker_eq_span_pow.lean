/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_PadicAlgCl_exists_forall_ringHom_apply_algebraMap_eq_of_free_of_ker_eq_span_pow
Modified for the Z-in-Q kernel (2026-11-16, p-divisible Hodge-Tate port): local import paths
are relocated, the P2M.Util elaborators are replaced by standard Lean commands or explicit terms,
local notations are expanded in place, and the upstream lakefile options are set as `set_option`
lines after the imports; see ZInQKernel/Contrib/CloudB3SC3PDivHodge/PORTING.md. Any other change is marked `-- [port]`.
Original copyright/attribution notices: NOTICE.upstream and ATTRIBUTION.upstream.md in
ZInQKernel/Contrib/CloudB3SC3PDivHodge/Vendor/AnthropicFLT/; license: LICENSE in that directory.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3SC3PDivHodge.Vendor.AnthropicFLT.P2M.Sol.S_PadicAlgCl_exists_forall_ringHom_apply_algebraMap_eq_of_free_of_ker_eq_span_pow

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

set_option autoImplicit false

theorem PadicAlgCl.exists_forall_ringHom_apply_algebraMap_eq_of_free_of_ker_eq_span_pow
    (p : ℕ) [inst_t1 : Fact p.Prime]
    (B : ℕ → Type) [inst_t2 : ∀ i, CommRing (B i)]
    [inst_t3 : ∀ i, Algebra (integralClosure ℤ_[p] (PadicAlgCl p) ⧸ Ideal.span {(p : integralClosure ℤ_[p] (PadicAlgCl p)) ^ i}) (B i)]
    [inst_t4 : ∀ i, Module.Finite (integralClosure ℤ_[p] (PadicAlgCl p) ⧸ Ideal.span {(p : integralClosure ℤ_[p] (PadicAlgCl p)) ^ i}) (B i)]
    [inst_t5 : ∀ i, Module.Free (integralClosure ℤ_[p] (PadicAlgCl p) ⧸ Ideal.span {(p : integralClosure ℤ_[p] (PadicAlgCl p)) ^ i}) (B i)]
    (ρ : ∀ i, B (i + 1) →+* B i)
    (hρ : ∀ (i : ℕ) (x : integralClosure ℤ_[p] (PadicAlgCl p)),
      ρ i (algebraMap (integralClosure ℤ_[p] (PadicAlgCl p) ⧸ Ideal.span {(p : integralClosure ℤ_[p] (PadicAlgCl p)) ^ (i + 1)}) (B (i + 1))
        (Ideal.Quotient.mk _ x)) =
        algebraMap (integralClosure ℤ_[p] (PadicAlgCl p) ⧸ Ideal.span {(p : integralClosure ℤ_[p] (PadicAlgCl p)) ^ i}) (B i) (Ideal.Quotient.mk _ x))
    (hρs : ∀ i, Function.Surjective (ρ i))
    (hker : ∀ i, RingHom.ker (ρ i) =
      Ideal.span {(algebraMap (integralClosure ℤ_[p] (PadicAlgCl p) ⧸ Ideal.span {(p : integralClosure ℤ_[p] (PadicAlgCl p)) ^ (i + 1)}) (B (i + 1))
        (Ideal.Quotient.mk _ ((p : integralClosure ℤ_[p] (PadicAlgCl p)) ^ i)))})  -- [port] multi-line singleton parenthesized (parser change)
    (ψ : B 1 →+* integralClosure ℤ_[p] (PadicAlgCl p) ⧸ (Ideal.span {(p : integralClosure ℤ_[p] (PadicAlgCl p))}).radical)
    (hψ : ∀ x : integralClosure ℤ_[p] (PadicAlgCl p),
      ψ (algebraMap (integralClosure ℤ_[p] (PadicAlgCl p) ⧸ Ideal.span {(p : integralClosure ℤ_[p] (PadicAlgCl p)) ^ 1}) (B 1) (Ideal.Quotient.mk _ x)) =
        Ideal.Quotient.mk _ x) :
    ∃ σ : ∀ i, B i →+* integralClosure ℤ_[p] (PadicAlgCl p) ⧸ Ideal.span {(p : integralClosure ℤ_[p] (PadicAlgCl p)) ^ i},
      (∀ (i : ℕ) (x : integralClosure ℤ_[p] (PadicAlgCl p) ⧸ Ideal.span {(p : integralClosure ℤ_[p] (PadicAlgCl p)) ^ i}),
        σ i (algebraMap (integralClosure ℤ_[p] (PadicAlgCl p) ⧸ Ideal.span {(p : integralClosure ℤ_[p] (PadicAlgCl p)) ^ i}) (B i) x) = x) ∧
      (∀ (i : ℕ) (b : B (i + 1)) (x : integralClosure ℤ_[p] (PadicAlgCl p)),
        σ (i + 1) b = Ideal.Quotient.mk _ x → σ i (ρ i b) = Ideal.Quotient.mk _ x) ∧
      ∀ b : B 1, ψ b = 0 → IsNilpotent (σ 1 b) :=
  @_root_.P2MW.S_PadicAlgCl_exists_forall_ringHom_apply_algebraMap_eq_of_free_of_ker_eq_span_pow.solution p inst_t1 B inst_t2 inst_t3 inst_t4 inst_t5 ρ hρ hρs hker ψ hψ
