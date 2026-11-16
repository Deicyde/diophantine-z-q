/-
Vendored from anthropics/fermats-last-theorem @ 6e837e75355538c7f80bab5b956861e86c4eacc2.
Original module: P2M.Sol.S_CoherentBaseChange_TwoTermComplex_natCast_finrank_ker_baseChange_sub_natCast_finrank_quotient_range_eq_chi. Apache-2.0.
Modification notice (CloudB3 Worker16, 2026-11-16): relocated imports; removed
nonessential negative-attribute and reactivation scaffolding; expanded namespace/open/export
helpers to ordinary commands and resolved metadata aliases directly. Mathematical proof
bodies retained, subject to documented Lean 4.35 API adaptations.
Full original notices/credits: NOTICE.upstream, ATTRIBUTION.upstream.md, LICENSE in this vendor root.
-/
import Mathlib
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_CoherentBaseChange
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.P2M.Util

set_option backward.isDefEq.respectTransparency false

namespace P2MW.S_CoherentBaseChange_TwoTermComplex_natCast_finrank_ker_baseChange_sub_natCast_finrank_quotient_range_eq_chi

set_option autoImplicit false

universe u v w

open scoped TensorProduct
open CoherentBaseChange
open P2MW.S_CoherentBaseChange_TwoTermComplex_natCast_finrank_ker_baseChange_sub_natCast_finrank_quotient_range_eq_chi.CoherentBaseChange

namespace CoherentBaseChange
export CoherentBaseChange (TwoTermComplex)
namespace TwoTermComplex
export CoherentBaseChange.TwoTermComplex (chi C0 d C1)
namespace ChiFieldAux
open CoherentBaseChange.TwoTermComplex
open CoherentBaseChange

variable {R : Type u} [CommRing R] (G : CoherentBaseChange.TwoTermComplex.{u, v} R)
  (K : Type w) [Field K] [Algebra R K]

noncomputable def rk : ℕ := Module.finrank K (LinearMap.range (G.d.baseChange K))

theorem h0_add_rk :
    Module.finrank K (LinearMap.ker (G.d.baseChange K)) + rk G K =
      Module.finrank K (K ⊗[R] G.C0) := by
  have h := LinearMap.finrank_range_add_finrank_ker (G.d.baseChange K)
  unfold rk; omega

theorem rk_add_h1 :
    rk G K + Module.finrank K ((K ⊗[R] G.C1) ⧸ LinearMap.range (G.d.baseChange K)) =
      Module.finrank K (K ⊗[R] G.C1) := by
  have h := Submodule.finrank_quotient_add_finrank (LinearMap.range (G.d.baseChange K))
  unfold rk; omega

theorem main :
    (Module.finrank K (LinearMap.ker (G.d.baseChange K)) : ℤ) -
      Module.finrank K ((K ⊗[R] G.C1) ⧸ LinearMap.range (G.d.baseChange K)) = G.chi := by
  haveI : Nontrivial R := (algebraMap R K).domain_nontrivial
  have h0 := h0_add_rk G K
  have h1 := rk_add_h1 G K
  rw [Module.finrank_baseChange] at h0 h1
  show _ = (Module.finrank R G.C0 : ℤ) - (Module.finrank R G.C1 : ℤ)
  have h0' : (Module.finrank K (LinearMap.ker (G.d.baseChange K)) : ℤ) + (rk G K : ℤ) =
      (Module.finrank R G.C0 : ℤ) := by exact_mod_cast h0
  have h1' : (rk G K : ℤ) + (Module.finrank K ((K ⊗[R] G.C1) ⧸
      LinearMap.range (G.d.baseChange K)) : ℤ) = (Module.finrank R G.C1 : ℤ) := by exact_mod_cast h1
  omega

end CoherentBaseChange.TwoTermComplex.ChiFieldAux

theorem solution
    {R : Type u} [CommRing R] (G : CoherentBaseChange.TwoTermComplex.{u, v} R)
    (K : Type w) [Field K] [Algebra R K] :
    (Module.finrank K (LinearMap.ker (G.d.baseChange K)) : ℤ) -
      Module.finrank K ((K ⊗[R] G.C1) ⧸ LinearMap.range (G.d.baseChange K)) = G.chi := by
  exact CoherentBaseChange.TwoTermComplex.ChiFieldAux.main G K
