/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Definitions.Def_ModularForm_EisensteinChiNegThree (git blob e44e6787a575c1476e242cc2ba78bdc0978b32c6, sha256 29acdc74c36e8a948f2468cf9de2b0fe60ac2dc94f0bcdaf70cb4d0ff7f5aa1b).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

set_option autoImplicit false

namespace EisensteinWeightOne

def chiNegThree (n : ℕ) : ℤ :=
  if n % 3 = 1 then 1 else if n % 3 = 2 then -1 else 0

def sigmaChi (n : ℕ) : ℤ :=
  ∑ d ∈ n.divisors, chiNegThree d

def e1Chi3 : PowerSeries ℤ :=
  PowerSeries.mk fun n => if n = 0 then 1 else 6 * sigmaChi n

noncomputable def e1Chi3In (R : Type*) [CommRing R] : PowerSeries R :=
  PowerSeries.map (Int.castRingHom R) e1Chi3

open CongruenceSubgroup in

def E1Chi3IsModular : Prop :=
  ∃ f : ModularForm (Gamma1 3) 1, ∀ z : UpperHalfPlane,
    f z = ∑' n : ℕ,
      ((PowerSeries.coeff n e1Chi3 : ℤ) : ℂ) *
        Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (n : ℂ) * (z : ℂ))

end EisensteinWeightOne
