/-
Ported with Codex assistance on 2026-11-14 from trureturing@8af78b5bb176c99b2750222c0dd3d00a475d39eb.
Source: D5/S3/Factorization/Dedekind/HilbertDifferent/NumberTheory/RamificationInertia/SeparableDegree.lean
Original SHA-256: af3e43c3bcc48e0a28300f052bfad512a6a6779b43f6a235f075ca00ee1637ec
Changes: contribution import paths and namespace; retained proof content.
Full licenses and provenance: ZInQKernel/Contrib/HilbertDifferent/Attribution.lean.
-/

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
/- Adapted to the repository-pinned Mathlib API; only declarations needed by the
Hilbert different consumer are retained. Source: TauCeti@33c2099c678ea391f7ea3e0ddaf945a76a625e5d,
TauCeti/NumberTheory/RamificationInertia/SeparableDegree.lean.
Full license and pertinent inherited attribution: ZInQKernel/Contrib/HilbertDifferent/Attribution.lean.
Replace this port by direct use when this project's pinned Mathlib supplies an equivalent declaration. -/


import Mathlib.FieldTheory.PurelyInseparable.Basic
import Mathlib.NumberTheory.RamificationInertia.Galois
import ZInQKernel.Contrib.HilbertDifferent.Support.TameDifferent

noncomputable section

section

open Algebra MulAction
open scoped Pointwise

namespace Ideal

attribute [local instance] Ideal.Quotient.field

variable {R S G : Type*} [CommRing R] [CommRing S] [Algebra R S] [Group G]
  [MulSemiringAction G S] [IsGaloisGroup G R S] [Finite G]

include G

/- The automorphism group of a residue extension in a finite invariant extension has order its
separable degree.  The residue extension is normal, but it need not be separable. -/
variable [IsDomain R] [IsDomain S] [Module.Finite R S] [Module.Flat R S]

/- The order of the decomposition group is `e * f`, without a separability hypothesis on the
residue extension. -/
theorem card_stabilizer_eq_ramificationIdxIn_mul_inertiaDegIn (p : Ideal R) [p.IsMaximal]
    (P : Ideal S) [P.LiesOver p] [P.IsMaximal] :
    Nat.card (stabilizer G P) = p.ramificationIdxIn S * p.inertiaDegIn S := by
  have horbit : (p.primesOver S).ncard * Nat.card (stabilizer G P) = Nat.card G := by
    rw [← IsInvariant.orbit_eq_primesOver R S G p P, ← Nat.card_coe_set_eq]
    simpa only [Nat.card_prod] using
      Nat.card_congr (MulAction.orbitProdStabilizerEquivGroup G P)
  have hfund := ncard_primesOver_mul_ramificationIdxIn_mul_inertiaDegIn p S G
  exact mul_right_injective₀ (left_ne_zero_of_mul (horbit.trans_ne Nat.card_pos.ne'))
    (by simpa only [mul_comm] using horbit.trans hfund.symm)

/- The order of the decomposition group is the product of the ramification index and inertia
degree of the upstairs ideal. -/
theorem card_stabilizer_eq_ramificationIdx_mul_inertiaDeg (P : Ideal S) [P.IsMaximal] :
    Nat.card (stabilizer G P) = P.ramificationIdx R * P.inertiaDeg R := by
  rw [← ramificationIdxIn_eq_ramificationIdx (P.under R) P G,
    ← inertiaDegIn_eq_inertiaDeg (P.under R) P G]
  exact card_stabilizer_eq_ramificationIdxIn_mul_inertiaDegIn (G := G) (P.under R) P

/- Over an imperfect residue field, the inertia group has order `e * fᵢ`, where `fᵢ` is the
inseparable residue degree. -/
end Ideal
