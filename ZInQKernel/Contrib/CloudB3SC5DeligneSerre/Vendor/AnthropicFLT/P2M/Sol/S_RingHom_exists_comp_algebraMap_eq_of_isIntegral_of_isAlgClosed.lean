/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: P2M.Sol.S_RingHom_exists_comp_algebraMap_eq_of_isIntegral_of_isAlgClosed (git blob f89fcabd8da288aa85a3ac94c896c5293aa576c3, sha256 d384bf428f3cc49f6b55ee45ab7072a86b8fad7eb2c772e7ac1f784f7502f4c7).
Modified for the Z-in-Q kernel (2026-11-16, cluster C5): import paths relocated (modules already
vendored elsewhere in the kernel are imported from there), the upstream lakefile options set as
`set_option` lines, and: dropped import P2M.Util (wrapper commands replaced by ordinary Lean); [port] Mathlib 4.35: rewrite `comap` back to `Ideal.under` before using the `under` equation.
Any other change is marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib.RingTheory.Ideal.GoingUp
import Mathlib.FieldTheory.IsAlgClosed.Basic

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

namespace P2MW.S_RingHom_exists_comp_algebraMap_eq_of_isIntegral_of_isAlgClosed

theorem solution {A B K : Type*} [CommRing A] [CommRing B] [Algebra A B] [Algebra.IsIntegral A B] [Field K] [IsAlgClosed K] (χ : A →+* K) (hker : RingHom.ker (algebraMap A B) ≤ RingHom.ker χ) : ∃ ψ : B →+* K, ψ.comp (algebraMap A B) = χ := by
  haveI : (RingHom.ker χ).IsPrime := RingHom.ker_isPrime χ
  obtain ⟨Q, -, hQ, hQP⟩ :=
    Ideal.exists_ideal_over_prime_of_isIntegral (RingHom.ker χ) (⊥ : Ideal B) hker
  haveI := hQ
  have hPker : ∀ a : A, a ∈ Q.comap (algebraMap A B) → χ a = 0 := fun a ha => by
    rw [← Ideal.under_def, hQP] at ha -- [port]
    exact RingHom.mem_ker.mp ha
  let χbar : A ⧸ Q.comap (algebraMap A B) →+* K := Ideal.Quotient.lift _ χ hPker
  have hχbar_inj : Function.Injective χbar :=
    RingHom.lift_injective_of_ker_le_ideal _ hPker (le_of_eq hQP.symm)
  letI : Algebra (A ⧸ Q.comap (algebraMap A B)) K := χbar.toAlgebra
  haveI : IsDomain (B ⧸ Q) := Ideal.Quotient.isDomain Q
  haveI : IsDomain (A ⧸ Q.comap (algebraMap A B)) := Ideal.Quotient.isDomain _
  haveI : Module.IsTorsionFree (A ⧸ Q.comap (algebraMap A B)) (B ⧸ Q) :=
    Module.isTorsionFree_iff_algebraMap_injective.mpr Ideal.algebraMap_quotient_injective
  haveI : Module.IsTorsionFree (A ⧸ Q.comap (algebraMap A B)) K :=
    Module.isTorsionFree_iff_algebraMap_injective.mpr hχbar_inj
  let ψbar : (B ⧸ Q) →ₐ[A ⧸ Q.comap (algebraMap A B)] K := IsAlgClosed.lift
  refine ⟨ψbar.toRingHom.comp (Ideal.Quotient.mk Q), RingHom.ext fun a => ?_⟩
  have h1 : Ideal.Quotient.mk Q (algebraMap A B a) =
      algebraMap (A ⧸ Q.comap (algebraMap A B)) (B ⧸ Q) (Ideal.Quotient.mk _ a) := rfl
  show ψbar (Ideal.Quotient.mk Q (algebraMap A B a)) = χ a
  rw [h1, ψbar.commutes]
  rfl
