/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
-- Vendored from Tau Ceti (https://github.com/TauCetiProject/TauCeti, commit 5a01f5fe3621, module TauCeti.GroupTheory.GroupAction.Stabilizer), Apache-2.0.
-- Modified for the Z-in-Q kernel: every declaration removed and the commit-97a5b235 module ZInQKernel.Contrib.TauCeti.GroupTheory.GroupAction.Stabilizer.Basic (vendored), which states all of them verbatim, publicly imported instead (task stab-clash: the two modules declared the same names, e.g. Subgroup.stabilizerInclusion, so no file could import both).
module

public import ZInQKernel.Contrib.TauCeti.GroupTheory.GroupAction.Stabilizer.Basic

/-!
# Point stabilisers: their cardinality, and when they are normal

Between the vendored commits 5a01f5fe and 97a5b235 Tau Ceti moved this module to
`TauCeti.GroupTheory.GroupAction.Stabilizer.Basic` and extended it. Both versions are vendored
here; this file re-exports the later one, which contains every declaration of the earlier one
with the same statement (`Subgroup.stabilizerInclusion`, `TauCeti.cardStabilizerOnOrbit`,
`TauCeti.card_stabilizer_eq_card_ker_mul_card_stabilizer`, ...).
-/
