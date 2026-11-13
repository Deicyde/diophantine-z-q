/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
-- Backported from Tau Ceti (https://github.com/TauCetiProject/TauCeti, commit 97a5b23586f9, module
-- TauCeti.NumberTheory.NumberField.Global.Ideles.Basic), Apache-2.0: declarations added to that module after commit 5a01f5fe, whose
-- version is vendored as `ZInQKernel.Contrib.TauCeti.NumberTheory.NumberField.Global.Ideles.Basic` (task ring-class).
module

public import ZInQKernel.Contrib.TauCeti.NumberTheory.NumberField.Global.Ideles.Basic

public section


namespace NumberField.IdeleClassGroup

variable (R : Type*) [CommRing R] [IsDedekindDomain R]
variable (K : Type*) [Field K] [Algebra R K] [IsFractionRing R K]

/-- The idele class group is commutative. This instance makes commutativity available to
instance search without unfolding the quotient abbreviation. -/
instance instIsMulCommutative : IsMulCommutative (IdeleClassGroup R K) :=
  ⟨⟨fun a b ↦ mul_comm a b⟩⟩


end NumberField.IdeleClassGroup
