/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
-- Vendored from Tau Ceti (https://github.com/TauCetiProject/TauCeti, commit 5a01f5fe3621, module TauCeti.NumberTheory.LocalField.UnitFiltration.Pow), Apache-2.0.
-- Modified for the Z-in-Q kernel: every declaration removed and the module ZInQKernel.Contrib.TauCeti.NumberTheory.LocalField.UnitFiltration.Pow.Basic (vendored), its commit-97a5b235 version, which states all of them verbatim, publicly imported instead (task stab-clash: the two modules declared the same names, so no file could import both).
module

public import ZInQKernel.Contrib.TauCeti.NumberTheory.LocalField.UnitFiltration.Pow.Basic

/-!
This commit-5a01f5fe module is superseded by `ZInQKernel.Contrib.TauCeti.NumberTheory.LocalField.UnitFiltration.Pow.Basic`, which declares every one of its names
(its commit-97a5b235 version, which states all of them verbatim). It is kept as a re-export so that every module of `ZInQKernel/Contrib/` can be imported
in one Lean environment (task stab-clash).
-/
