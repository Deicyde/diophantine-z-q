/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Definitions.Def_ModularCurve_FibrePoly
Modified for the Z-in-Q kernel (2026-11-15, task flt-cqj2): local import paths are relocated
(`P2M.Util` is the copy published by Cloud Worker 2) and the upstream lakefile options are set
as `set_option` lines after the imports; any other change is marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Definitions.Def_ModularCurve_KroneckerTransport

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

noncomputable section

open Polynomial

namespace ModularCurve

section FibrePoly

variable {k : Type*} [Field k]

def fibrePoly (Φ : Polynomial (Polynomial ℤ)) (a : k) : Polynomial k :=
  Φ.map (Polynomial.eval₂RingHom (Int.castRingHom k) a)

variable {ℓ : ℕ} [Fact ℓ.Prime] [CharP k ℓ]

theorem eval₂RingHom_intCast_eq_comp (a : k) :
    Polynomial.eval₂RingHom (Int.castRingHom k) a =
      (Polynomial.eval₂RingHom (ZMod.castHom (dvd_refl ℓ) k) a).comp
        (Polynomial.mapRingHom (Int.castRingHom (ZMod ℓ))) := by
  refine Polynomial.ringHom_ext' (Subsingleton.elim _ _) ?_
  rw [Polynomial.coe_eval₂RingHom, Polynomial.eval₂_X, RingHom.comp_apply,
    Polynomial.coe_mapRingHom, Polynomial.map_X, Polynomial.coe_eval₂RingHom,
    Polynomial.eval₂_X]

theorem fibrePoly_eq_map_reduceModBivar (Φ : Polynomial (Polynomial ℤ)) (a : k) :
    fibrePoly Φ a =
      (reduceModBivar ℓ Φ).map
        (Polynomial.eval₂RingHom (ZMod.castHom (dvd_refl ℓ) k) a) := by
  rw [fibrePoly, eval₂RingHom_intCast_eq_comp (ℓ := ℓ),
    show reduceModBivar ℓ Φ
      = Φ.map (Polynomial.mapRingHom (Int.castRingHom (ZMod ℓ))) from rfl,
    Polynomial.map_map]

end FibrePoly

section Factorization

variable {k : Type*} [Field k] {ℓ : ℕ} [Fact ℓ.Prime] [CharP k ℓ] [PerfectRing k ℓ]

theorem C_sub_X_pow_eq_neg_pow (a : k) :
    Polynomial.C a - Polynomial.X ^ ℓ =
      -((Polynomial.X - Polynomial.C ((frobeniusEquiv k ℓ).symm a)) ^ ℓ) := by
  have hpoly : (Polynomial.X - Polynomial.C ((frobeniusEquiv k ℓ).symm a)) ^ ℓ =
      Polynomial.X ^ ℓ - Polynomial.C ((frobeniusEquiv k ℓ).symm a) ^ ℓ :=
    sub_pow_expChar _ _
  rw [hpoly, ← Polynomial.C_pow, frobeniusEquiv_symm_pow_p, neg_sub]

end Factorization

end ModularCurve
