/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: P2M.Sol.S_Subalgebra_isIntegrallyClosed_adjoin_singleton_of_transcendental (git blob 672b94db19d949aafcbf9d4b8941ce261eb3b3a3, sha256 cebfc71a0fd395bb4f98ee94b4d1a4a9c6261f5c89fb81e750c46eefbe6bc75b).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

namespace P2MW.S_Subalgebra_isIntegrallyClosed_adjoin_singleton_of_transcendental

set_option autoImplicit false
set_option maxHeartbeats 8000000

open Polynomial

theorem solution
    {L : Type*} [Field L] {F : Type*} [CommRing F] [IsDomain F] [Algebra L F]
    (x : F) (hxL : Transcendental L x) :
    IsIntegrallyClosed (Algebra.adjoin L ({x} : Set F)) := by
  classical

  have hinj : Function.Injective (Polynomial.aeval (R := L) x) :=
    transcendental_iff_injective.mp hxL
  have hrange : (Polynomial.aeval (R := L) x).range = Algebra.adjoin L ({x} : Set F) :=
    (Algebra.adjoin_singleton_eq_range_aeval L x).symm
  let e : Polynomial L ≃ₐ[L] Algebra.adjoin L ({x} : Set F) :=
    (AlgEquiv.ofInjective (Polynomial.aeval (R := L) x) hinj).trans
      (Subalgebra.equivOfEq _ _ hrange)

  haveI : IsPrincipalIdealRing (Algebra.adjoin L ({x} : Set F)) := by
    constructor
    intro I

    obtain ⟨a, ha⟩ := IsPrincipalIdealRing.principal (I.comap e.toRingHom)
    refine ⟨e a, ?_⟩
    show I = Ideal.span {e a}
    rw [← Ideal.map_comap_of_surjective e.toRingHom e.surjective I,
      show Ideal.comap e.toRingHom I = Ideal.span {a} from ha,
      Ideal.map_span, Set.image_singleton]
    rfl

  infer_instance
