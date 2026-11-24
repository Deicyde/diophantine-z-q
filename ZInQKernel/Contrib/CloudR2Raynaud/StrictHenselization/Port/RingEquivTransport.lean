/-
Copyright (c) 2026 Contributors. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.

Uses the HenselianLocalRing definition and polynomial-map API from Mathlib,
distributed under Apache 2.0 at revision
56a005855ea17e0b0958f73ec801ae140b0a1679.
-/

import Mathlib

/-!
# Transport of the henselian property along a ring equivalence

Both commutative-ring structures remain fixed. Locality is transported by the
ring equivalence, and a simple polynomial root is lifted after transporting
its coefficients to the source ring.
-/

universe u

namespace ZInQ.Contrib.CloudR2Raynaud.StrictHenselization.Port

/-- A ring equivalent to a henselian local ring is henselian for its original
commutative-ring structure. -/
theorem HenselianLocalRing.of_ringEquiv
    {Rh P : Type u} [CommRing Rh] [CommRing P] [HenselianLocalRing Rh]
    (eR : Rh ≃+* P) : HenselianLocalRing P := by
  haveI : IsLocalRing P := eR.isLocalRing
  constructor
  intro f hf a ha hder
  let g : Polynomial Rh := f.map eR.symm.toRingHom
  have heval (x : P) : g.eval (eR.symm x) = eR.symm (f.eval x) := by
    simpa only [g, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom] using
      (Polynomial.eval_map_apply (p := f) (f := eR.symm.toRingHom) x)
  have hgmonic : g.Monic := Polynomial.Monic.map eR.symm.toRingHom hf
  have hgeval : g.eval (eR.symm a) ∈ IsLocalRing.maximalIdeal Rh := by
    change ¬ IsUnit (g.eval (eR.symm a))
    intro hu
    apply (show ¬ IsUnit (f.eval a) from ha)
    simpa only [RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom,
      heval a, RingEquiv.apply_symm_apply] using hu.map eR.toRingHom
  have hgder : IsUnit (g.derivative.eval (eR.symm a)) := by
    have hdval : g.derivative.eval (eR.symm a) = eR.symm (f.derivative.eval a) := by
      simpa only [g, Polynomial.derivative_map, RingEquiv.toRingHom_eq_coe,
        RingEquiv.coe_toRingHom] using
        (Polynomial.eval_map_apply (p := f.derivative) (f := eR.symm.toRingHom) a)
    rw [hdval]
    simpa only [RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom] using
      hder.map eR.symm.toRingHom
  obtain ⟨r, hr, hra⟩ := _root_.HenselianLocalRing.is_henselian
    g hgmonic (eR.symm a) hgeval hgder
  refine ⟨eR r, ?_, ?_⟩
  · change f.eval (eR r) = 0
    apply eR.symm.injective
    have hh := heval (eR r)
    rw [RingEquiv.symm_apply_apply, hr.eq_zero] at hh
    simpa only [map_zero] using hh.symm
  · change ¬ IsUnit (eR r - a)
    intro hu
    apply (show ¬ IsUnit (r - eR.symm a) from hra)
    simpa only [RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom,
      map_sub, RingEquiv.symm_apply_apply] using hu.map eR.symm.toRingHom

end ZInQ.Contrib.CloudR2Raynaud.StrictHenselization.Port
