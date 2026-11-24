import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.Lemmas01
import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.MvPolynomialCoeff
import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.TensorProductInduction
import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.PresheafOfModulesMonoidal
import ZInQKernel.Contrib.CloudR2NOS.Source.PortUtilExt
/-
Copyright 2026 Anthropic, PBC.
Released under the Apache License, Version 2.0; see LICENSE, NOTICE, ATTRIBUTION.md.
Source: anthropics/fermats-last-theorem@6e837e75355538c7f80bab5b956861e86c4eacc2
Original file: Theorems/Thm_Algebra_linearIndepOn_pow_localization_atPrime_of_mem_minimalPrimes_of_dense.lean
Original Git blob: b976758496be4533544e7a71d49fcdca9d8bd8a0
NOTICE OF MODIFICATION (2026-11-14): isolated namespace/import port to Lean 4.35.0,
Mathlib 56a005855ea17e0b0958f73ec801ae140b0a1679; shared H76 declarations are imported,
not redeclared. No constructor hypothesis or conclusion has been weakened.
-/
import Mathlib
import ZInQKernel.Contrib.CloudR2NeronExistence.Henselian.PortUtil
import ZInQKernel.Contrib.CloudR2NeronExistence.Henselian.Vendor.P2M.Sol.S_Algebra_linearIndepOn_pow_localization_atPrime_of_mem_minimalPrimes_of_dense

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

universe u

theorem Algebra.linearIndepOn_pow_localization_atPrime_of_mem_minimalPrimes_of_dense
    {k : Type u} [Field k] {B : Type u} [CommRing B] [Algebra k B] [Algebra.FiniteType k B] [IsReduced B]
    (p : ℕ) (hp : p.Prime) [ExpChar k p]
    (S : Set (PrimeSpectrum B))
    (hdense : ∀ g : B, (∀ 𝔰 ∈ S, g ∈ 𝔰.asIdeal) → g = 0)
    (hsep : ∀ 𝔰 ∈ S, ∃ (K : Type u) (_ : Field K) (_ : Algebra k K),
      (∀ t : Finset K, LinearIndepOn k _root_.id (t : Set K) → LinearIndepOn k (· ^ p) (t : Set K)) ∧
      Nonempty (𝔰.asIdeal.ResidueField →ₐ[k] K))
    (𝔮 : Ideal B) [𝔮.IsPrime] (h𝔮 : 𝔮 ∈ minimalPrimes B)
    (s : Finset (Localization.AtPrime 𝔮)) (hs : LinearIndepOn k _root_.id (s : Set (Localization.AtPrime 𝔮))) :
    LinearIndepOn k (· ^ p) (s : Set (Localization.AtPrime 𝔮)) := by h77_exact_reverting @_root_.ZInQ.Contrib.CloudR2NeronExistence.Henselian.P2MW.S_Algebra_linearIndepOn_pow_localization_atPrime_of_mem_minimalPrimes_of_dense.solution


end ZInQ.Contrib.CloudR2NeronExistence.Henselian
