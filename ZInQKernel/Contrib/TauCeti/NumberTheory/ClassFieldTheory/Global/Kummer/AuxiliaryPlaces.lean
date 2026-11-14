/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
-- Vendored from Tau Ceti (https://github.com/TauCetiProject/TauCeti, commit 5a01f5fe3621, module TauCeti.NumberTheory.ClassFieldTheory.Global.Kummer.AuxiliaryPlaces), Apache-2.0.
-- Modified for the Z-in-Q kernel: every declaration removed and the module ZInQKernel.Contrib.TauCeti.Backport.NumberTheory.ClassFieldTheory.Global.Kummer.AuxiliaryPlaces (vendored), the whole commit-97a5b235 module, which declares all of them, some with changed hypotheses or conclusions, publicly imported instead (task stab-clash: the two modules declared the same names, so no file could import both; no Lean file imported this commit-5a01f5fe module, and its versions of the changed statements are dropped).
module

public import ZInQKernel.Contrib.TauCeti.Backport.NumberTheory.ClassFieldTheory.Global.Kummer.AuxiliaryPlaces

/-!
This commit-5a01f5fe module is superseded by `ZInQKernel.Contrib.TauCeti.Backport.NumberTheory.ClassFieldTheory.Global.Kummer.AuxiliaryPlaces`, which declares every one of its names
(the whole commit-97a5b235 module, which declares all of them, some with changed hypotheses or
conclusions). No Lean file imported this module; its versions of the changed statements are
dropped. It is kept as a re-export so that every module of `ZInQKernel/Contrib/` can be imported
in one Lean environment (task stab-clash).
-/
