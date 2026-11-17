/-
Ported with Codex assistance on 2026-11-14 from trureturing@8af78b5bb176c99b2750222c0dd3d00a475d39eb.
Source: D5/S3/Factorization/Dedekind/HilbertDifferent/RingTheory/Ideal/PrimesOver.lean
Original SHA-256: 1eb32fb5421a39b74c64b0fdf6b8d0f719cc1c7115db24808950dc9376a71fdc
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
TauCeti/RingTheory/Ideal/PrimesOver.lean.
Full license and pertinent inherited attribution: ZInQKernel/Contrib/HilbertDifferent/Attribution.lean.
Replace this port by direct use when this project's pinned Mathlib supplies an equivalent declaration. -/


import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
import ZInQKernel.Contrib.HilbertDifferent.Support.TameDifferent

noncomputable section

section

namespace IsDedekindDomain.HeightOneSpectrum

variable {R B : Type*} [CommRing R] [CommRing B] [Algebra R B]

/- A height one prime of `B` taken from the subtype of those lying over `v` lies over `v`. -/
instance liesOver_val {v : HeightOneSpectrum R}
    (w : {w : HeightOneSpectrum B // w.asIdeal.LiesOver v.asIdeal}) :
    w.1.asIdeal.LiesOver v.asIdeal :=
  w.2

variable (B) [FaithfulSMul R B]

/- The nonzero prime ideals of `B` lying over a nonzero prime `v` of `R` are precisely
`Ideal.primesOver v.asIdeal B`. Injectivity of the algebra map ensures that an ideal lying
above `v` is nonzero; neither ring needs to be a Dedekind domain. -/
def liesOverEquivPrimesOver (v : HeightOneSpectrum R) :
    {w : HeightOneSpectrum B // w.asIdeal.LiesOver v.asIdeal} ≃ v.asIdeal.primesOver B where
  toFun w := ⟨w.1.asIdeal, w.1.isPrime, w.2⟩
  invFun Q := ⟨⟨Q.1, Q.2.1, Ideal.ne_bot_of_liesOver_of_ne_bot v.ne_bot Q.1⟩, Q.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

@[simp]
theorem liesOverEquivPrimesOver_apply (v : HeightOneSpectrum R)
    (w : {w : HeightOneSpectrum B // w.asIdeal.LiesOver v.asIdeal}) :
    (liesOverEquivPrimesOver B v w : Ideal B) = w.1.asIdeal :=
  (rfl)

end IsDedekindDomain.HeightOneSpectrum

end
