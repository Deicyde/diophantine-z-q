import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.Lemmas01
import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.MvPolynomialCoeff
import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.TensorProductInduction
import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.PresheafOfModulesMonoidal
import ZInQKernel.Contrib.CloudR2NOS.Source.PortUtilExt
/-
Copyright 2026 Anthropic, PBC.
Released under the Apache License, Version 2.0; see LICENSE, NOTICE, ATTRIBUTION.md.
Source: anthropics/fermats-last-theorem@6e837e75355538c7f80bab5b956861e86c4eacc2
Original file: Theorems/Thm_Algebra_exists_notMem_map_ker_eq_bot_of_surjective_of_isSmoothAt_of_finrank_le.lean
Original Git blob: ade870d4e5eee1d6e0b5d8833f299bcc00a88f42
NOTICE OF MODIFICATION (2026-11-14): isolated namespace/import port to Lean 4.35.0,
Mathlib 56a005855ea17e0b0958f73ec801ae140b0a1679; shared H76 declarations are imported,
not redeclared. No constructor hypothesis or conclusion has been weakened.
-/
import Mathlib
import ZInQKernel.Contrib.CloudR2NeronExistence.Henselian.PortUtil
import ZInQKernel.Contrib.CloudR2NeronExistence.Henselian.Vendor.P2M.Sol.S_Algebra_exists_notMem_map_ker_eq_bot_of_surjective_of_isSmoothAt_of_finrank_le

namespace ZInQ.Contrib.CloudR2NeronExistence.Henselian
h77_bridge_namespace

h77_import_shared
h77_open "KaehlerDifferential TensorProduct"
h77_open "TensorProduct"
open scoped _root_.TensorProduct
h77_open "AlgebraicGeometry NeronModelInfra GoodReductionJacobian"
open ZInQ.Contrib.CloudW03NeronSurj.FLT

set_option autoImplicit false


set_option backward.isDefEq.respectTransparency.instanceSearchTypes false

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open TensorProduct KaehlerDifferential

universe u

theorem Algebra.exists_notMem_map_ker_eq_bot_of_surjective_of_isSmoothAt_of_finrank_le
    {k : Type u} [Field k] {B : Type u} [CommRing B] [Algebra k B] [Algebra.FiniteType k B] [Algebra.Smooth k B]
    {B' : Type u} [CommRing B'] [Algebra k B'] (ψ : B →ₐ[k] B') (hψ : Function.Surjective ψ)
    (v' : Ideal B') [v'.IsPrime] (v : Ideal B) [v.IsPrime] (hv' : v'.comap ψ.toRingHom = v)
    (hsm : Algebra.IsSmoothAt k v')
    (hrank : Module.finrank v.ResidueField (v.ResidueField ⊗[B] Ω[B⁄k]) ≤
      Module.finrank v'.ResidueField (v'.ResidueField ⊗[B'] Ω[B'⁄k])) :
    ∃ t : B, t ∉ v ∧ (RingHom.ker ψ.toRingHom).map (algebraMap B (Localization.Away t)) = ⊥ := by h77_exact_reverting @_root_.ZInQ.Contrib.CloudR2NeronExistence.Henselian.P2MW.S_Algebra_exists_notMem_map_ker_eq_bot_of_surjective_of_isSmoothAt_of_finrank_le.solution


end ZInQ.Contrib.CloudR2NeronExistence.Henselian
