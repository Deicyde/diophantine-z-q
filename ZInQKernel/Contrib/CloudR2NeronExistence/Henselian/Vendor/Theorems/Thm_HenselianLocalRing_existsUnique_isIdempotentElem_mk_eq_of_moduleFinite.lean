import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.Lemmas01
import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.MvPolynomialCoeff
import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.TensorProductInduction
import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.PresheafOfModulesMonoidal
import ZInQKernel.Contrib.CloudR2NOS.Source.PortUtilExt
/-
Copyright 2026 Anthropic, PBC.
Released under the Apache License, Version 2.0; see LICENSE, NOTICE, ATTRIBUTION.md.
Source: anthropics/fermats-last-theorem@6e837e75355538c7f80bab5b956861e86c4eacc2
Original file: Theorems/Thm_HenselianLocalRing_existsUnique_isIdempotentElem_mk_eq_of_moduleFinite.lean
Original Git blob: 98efca9968320f11d297ba8eaf2a2cdae385ebd1
NOTICE OF MODIFICATION (2026-11-14): isolated namespace/import port to Lean 4.35.0,
Mathlib 56a005855ea17e0b0958f73ec801ae140b0a1679; shared H76 declarations are imported,
not redeclared. No constructor hypothesis or conclusion has been weakened.
-/
import Mathlib
import ZInQKernel.Contrib.CloudR2NeronExistence.Henselian.PortUtil
import ZInQKernel.Contrib.CloudR2NeronExistence.Henselian.Vendor.P2M.Sol.S_HenselianLocalRing_existsUnique_isIdempotentElem_mk_eq_of_moduleFinite

namespace ZInQ.Contrib.CloudR2NeronExistence.Henselian
h77_bridge_namespace

h77_import_shared
h77_open "AlgebraicGeometry NeronModelInfra GoodReductionJacobian"
open ZInQ.Contrib.CloudW03NeronSurj.FLT

universe u v

theorem HenselianLocalRing.existsUnique_isIdempotentElem_mk_eq_of_moduleFinite
    {R : Type u} [CommRing R] [HenselianLocalRing R]
    {S : Type v} [CommRing S] [Algebra R S] [Module.Finite R S]
    (ē : S ⧸ (IsLocalRing.maximalIdeal R).map (algebraMap R S)) (hē : IsIdempotentElem ē) :
    ∃! e : S, IsIdempotentElem e ∧
      Ideal.Quotient.mk ((IsLocalRing.maximalIdeal R).map (algebraMap R S)) e = ē := by h77_exact_reverting @_root_.ZInQ.Contrib.CloudR2NeronExistence.Henselian.P2MW.S_HenselianLocalRing_existsUnique_isIdempotentElem_mk_eq_of_moduleFinite.solution


end ZInQ.Contrib.CloudR2NeronExistence.Henselian
