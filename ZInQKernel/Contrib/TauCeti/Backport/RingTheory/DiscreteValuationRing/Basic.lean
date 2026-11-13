/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
-- Backported from Tau Ceti (https://github.com/TauCetiProject/TauCeti, commit 97a5b23586f9, module
-- TauCeti.RingTheory.DiscreteValuationRing.Basic), Apache-2.0: declarations added to that module after commit 5a01f5fe, whose
-- version is vendored as `ZInQKernel.Contrib.TauCeti.RingTheory.DiscreteValuationRing.Basic`.
module

public import ZInQKernel.Contrib.TauCeti.RingTheory.DiscreteValuationRing.Basic

public section

namespace TauCeti.IsDiscreteValuationRing

open IsLocalRing
variable {S : Type*} [CommRing S] [IsDomain S] [_root_.IsDiscreteValuationRing S]

/-- A discrete valuation ring is infinite: the powers of a uniformizer are pairwise distinct. -/
instance infinite : Infinite S := by
  obtain ⟨ϖ, hϖ⟩ := _root_.IsDiscreteValuationRing.exists_irreducible S
  exact .of_injective _ (pow_injective_of_not_isUnit hϖ.not_isUnit hϖ.ne_zero)

end TauCeti.IsDiscreteValuationRing

end
