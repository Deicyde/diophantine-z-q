import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.Lemmas01
import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.MvPolynomialCoeff
import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.TensorProductInduction
import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.PresheafOfModulesMonoidal
import ZInQKernel.Contrib.CloudR2NOS.Source.PortUtilExt
/-
Copyright 2026 Anthropic, PBC.
Released under the Apache License, Version 2.0; see LICENSE, NOTICE, ATTRIBUTION.md.
Source: anthropics/fermats-last-theorem@6e837e75355538c7f80bab5b956861e86c4eacc2
Original file: Theorems/Thm_IsDiscreteValuationRing_length_torsion_quotient_add_finrank_le_of_sq_smul_le_prod.lean
Original Git blob: e50c2511e438c363225c57cfac53fc58ba13eb40
NOTICE OF MODIFICATION (2026-11-14): isolated namespace/import port to Lean 4.35.0,
Mathlib 56a005855ea17e0b0958f73ec801ae140b0a1679; shared H76 declarations are imported,
not redeclared. No constructor hypothesis or conclusion has been weakened.
-/
import Mathlib
import ZInQKernel.Contrib.CloudR2NeronExistence.Henselian.PortUtil
import ZInQKernel.Contrib.CloudR2NeronExistence.Henselian.Vendor.P2M.Sol.S_IsDiscreteValuationRing_length_torsion_quotient_add_finrank_le_of_sq_smul_le_prod

namespace ZInQ.Contrib.CloudR2NeronExistence.Henselian
h77_bridge_namespace

h77_import_shared
h77_open "AlgebraicGeometry NeronModelInfra GoodReductionJacobian"
open ZInQ.Contrib.CloudW03NeronSurj.FLT

set_option autoImplicit false


set_option backward.isDefEq.respectTransparency.instanceSearchTypes false

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open Module

universe u

theorem IsDiscreteValuationRing.length_torsion_quotient_add_finrank_le_of_sq_smul_le_prod
    {R' : Type u} [CommRing R'] [IsDomain R'] [IsDiscreteValuationRing R']
    (π : R') (hπ : Irreducible π) (r n : ℕ)
    (N'' : Submodule R' ((Fin r → R') × (Fin n → R')))
    (hN : (Ideal.span {π ^ 2} : Ideal R') • N'' ≤ (⊤ : Submodule R' (Fin r → R')).prod ((Ideal.span {π} : Ideal R') • (⊤ : Submodule R' (Fin n → R')))) :
    Module.length R' (Submodule.torsion R' (((Fin r → R') × (Fin n → R')) ⧸ N'')) + Module.finrank R' N'' ≤
      Module.length R' (Submodule.torsion R'
        (↥((⊤ : Submodule R' (Fin r → R')).prod ((Ideal.span {π} : Ideal R') • (⊤ : Submodule R' (Fin n → R')))) ⧸
          ((Ideal.span {π ^ 2} : Ideal R') • N'').comap ((⊤ : Submodule R' (Fin r → R')).prod
            ((Ideal.span {π} : Ideal R') • (⊤ : Submodule R' (Fin n → R')))).subtype)) := by h77_exact_reverting @_root_.ZInQ.Contrib.CloudR2NeronExistence.Henselian.P2MW.S_IsDiscreteValuationRing_length_torsion_quotient_add_finrank_le_of_sq_smul_le_prod.solution


end ZInQ.Contrib.CloudR2NeronExistence.Henselian
