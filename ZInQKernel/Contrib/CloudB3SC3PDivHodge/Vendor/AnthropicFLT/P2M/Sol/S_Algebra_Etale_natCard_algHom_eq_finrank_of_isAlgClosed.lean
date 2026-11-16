/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: P2M.Sol.S_Algebra_Etale_natCard_algHom_eq_finrank_of_isAlgClosed
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

namespace P2MW.S_Algebra_Etale_natCard_algHom_eq_finrank_of_isAlgClosed

set_option autoImplicit false

theorem solution
    (k : Type*) [Field k] [IsAlgClosed k] (R : Type*) [CommRing R] [Algebra k R] [Algebra.Etale k R] :
    Nat.card (R →ₐ[k] k) = Module.finrank k R := by
  classical
  obtain ⟨ι, _, L, _, _, e, hL⟩ := (Algebra.Etale.iff_exists_algEquiv_prod k R).mp ‹_›
  haveI : Fintype ι := Fintype.ofFinite ι

  have hLk : ∀ i, Nonempty (L i ≃ₐ[k] k) := fun i => by
    haveI := (hL i).1
    haveI : Algebra.IsIntegral k (L i) := Algebra.IsIntegral.of_finite k (L i)
    exact ⟨(AlgEquiv.ofBijective (Algebra.ofId k (L i))
      IsAlgClosed.algebraMap_bijective_of_isIntegral).symm⟩

  let f : R ≃ₐ[k] (ι → k) := e.trans (AlgEquiv.piCongrRight fun i => (hLk i).some)
  have hrk : Module.finrank k R = Fintype.card ι := by
    rw [LinearEquiv.finrank_eq f.toLinearEquiv, Module.finrank_pi]

  have heval : Function.Bijective (fun i : ι => Pi.evalAlgHom k (fun _ => k) i) := by
    refine ⟨fun i j hij => ?_, fun φ => (AlgHom.eq_piEvalAlgHom φ).imp fun _ h => h.symm⟩
    have := DFunLike.congr_fun hij (Pi.single i 1)
    simp only [Pi.evalAlgHom_apply, Pi.single_apply] at this
    by_contra hne; simp [if_neg (Ne.symm hne)] at this
  have hcard : Nat.card (R →ₐ[k] k) = Fintype.card ι := by
    rw [Nat.card_congr (AlgEquiv.arrowCongr f AlgEquiv.refl),
      ← Nat.card_eq_fintype_card (α := ι),
      Nat.card_eq_of_bijective _ heval]
  rw [hrk, hcard]
