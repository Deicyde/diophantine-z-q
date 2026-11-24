import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.Lemmas01
import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.MvPolynomialCoeff
import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.TensorProductInduction
import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.PresheafOfModulesMonoidal
import ZInQKernel.Contrib.CloudR2NOS.Source.PortUtilExt
/-
Copyright 2026 Anthropic, PBC.
Released under the Apache License, Version 2.0; see LICENSE, NOTICE, ATTRIBUTION.md.
Source: anthropics/fermats-last-theorem@6e837e75355538c7f80bab5b956861e86c4eacc2
Original file: P2M/Sol/S_Algebra_isSmoothAt_of_mem_minimalPrimes_of_dense_of_formallySmooth_residueField.lean
Original Git blob: 9bc18a37575df1f30cb6e4a2025dd1b4e45114a6
NOTICE OF MODIFICATION (2026-11-14): isolated namespace/import port to Lean 4.35.0,
Mathlib 56a005855ea17e0b0958f73ec801ae140b0a1679; shared H76 declarations are imported,
not redeclared. No constructor hypothesis or conclusion has been weakened.
* Explicitly closed 1 scopes originally left open at EOF.
-/
import Mathlib
import ZInQKernel.Contrib.CloudR2NeronExistence.Henselian.Vendor.Theorems.Thm_Algebra_FormallySmooth_linearIndepOn_pow_of_linearIndepOn_id
import ZInQKernel.Contrib.CloudR2NeronExistence.Henselian.Vendor.Theorems.Thm_Algebra_linearIndepOn_pow_localization_atPrime_of_mem_minimalPrimes_of_dense
import ZInQKernel.Contrib.CloudR2NeronExistence.Henselian.PortUtil

namespace ZInQ.Contrib.CloudR2NeronExistence.Henselian
h77_bridge_namespace

h77_import_shared
h77_open "AlgebraicGeometry NeronModelInfra GoodReductionJacobian"
open ZInQ.Contrib.CloudW03NeronSurj.FLT

namespace P2MW.S_Algebra_isSmoothAt_of_mem_minimalPrimes_of_dense_of_formallySmooth_residueField
h77_bridge_namespace

set_option autoImplicit false


set_option backward.isDefEq.respectTransparency.instanceSearchTypes false

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

namespace B14CGS
h77_bridge_namespace

theorem isSmoothAt_of_forall_linearIndepOn_pow
    {k : Type u} [Field k] {B : Type u} [CommRing B] [Algebra k B] [Algebra.FiniteType k B] [IsReduced B]
    (p : ℕ) [ExpChar k p]
    (𝔮 : Ideal B) [𝔮.IsPrime] (h𝔮 : 𝔮 ∈ minimalPrimes B)
    (H : ∀ s : Finset (Localization.AtPrime 𝔮), LinearIndepOn k _root_.id (s : Set (Localization.AtPrime 𝔮)) →
      LinearIndepOn k (· ^ p) (s : Set (Localization.AtPrime 𝔮))) :
    Algebra.IsSmoothAt k 𝔮 := by
  classical

  have hrad : ((⊥ : Ideal B).map (algebraMap B (Localization.AtPrime 𝔮))).radical =
      𝔮.map (algebraMap B (Localization.AtPrime 𝔮)) :=
    IsLocalization.AtPrime.radical_map_of_mem_minimalPrimes (A := Localization.AtPrime 𝔮) 𝔮 ⊥ h𝔮
  have hmax : IsLocalRing.maximalIdeal (Localization.AtPrime 𝔮) = ⊥ := by
    rw [← Localization.AtPrime.map_eq_maximalIdeal, ← hrad, Ideal.map_bot]
    exact nilradical_eq_zero (Localization.AtPrime 𝔮)
  have hfield : IsField (Localization.AtPrime 𝔮) := IsLocalRing.isField_iff_maximalIdeal_eq.mpr hmax
  letI : Field (Localization.AtPrime 𝔮) := hfield.toField
  haveI : Algebra.EssFiniteType k (Localization.AtPrime 𝔮) := inferInstance
  show Algebra.FormallySmooth k (Localization.AtPrime 𝔮)
  rcases expChar_is_prime_or_one k p with hprime | hp1
  swap
  · subst hp1
    haveI : CharZero k := charZero_of_expChar_one' k
    haveI : PerfectField k := PerfectField.ofCharZero
    exact Algebra.FormallySmooth.of_perfectField
  · obtain ⟨s, hs, hsep⟩ :=
      exists_isTranscendenceBasis_and_isSeparable_of_linearIndepOn_pow_of_essFiniteType p hprime H
    have : Algebra.IsSeparable
        ↥(IntermediateField.adjoin k (Set.range ((↑) : s → Localization.AtPrime 𝔮))) (Localization.AtPrime 𝔮) := by
      convert! hsep <;> simp
    exact Algebra.FormallySmooth.of_algebraicIndependent_of_isSeparable hs.1

end B14CGS

theorem solution
    {k : Type u} [Field k] {B : Type u} [CommRing B] [Algebra k B] [Algebra.FiniteType k B] [IsReduced B]
    (S : Set (PrimeSpectrum B))
    (hdense : ∀ g : B, (∀ 𝔰 ∈ S, g ∈ 𝔰.asIdeal) → g = 0)
    (hsep : ∀ 𝔰 ∈ S, ∃ (K : Type u) (_ : Field K) (_ : Algebra k K),
      Algebra.FormallySmooth k K ∧ Nonempty (𝔰.asIdeal.ResidueField →ₐ[k] K))
    (𝔮 : Ideal B) [𝔮.IsPrime] (h𝔮 : 𝔮 ∈ minimalPrimes B) :
    Algebra.IsSmoothAt k 𝔮 := by
  classical
  obtain ⟨p, hp⟩ := ExpChar.exists k
  rcases hp with ⟨hp0⟩ | ⟨hpp, hpc⟩
  · haveI : ExpChar k 1 := ExpChar.zero
    exact B14CGS.isSmoothAt_of_forall_linearIndepOn_pow 1 𝔮 h𝔮 (fun s hs => by simp only [pow_one] at hs ⊢; exact hs)
  · haveI : ExpChar k p := ExpChar.prime hpp
    refine B14CGS.isSmoothAt_of_forall_linearIndepOn_pow p 𝔮 h𝔮 (fun s hs => ?_)
    refine Algebra.linearIndepOn_pow_localization_atPrime_of_mem_minimalPrimes_of_dense p hpp S hdense
      (fun 𝔰 h𝔰 => ?_) 𝔮 h𝔮 s hs
    obtain ⟨K, iF, iA, hK, hne⟩ := hsep 𝔰 h𝔰
    exact ⟨K, iF, iA, fun t ht => @Algebra.FormallySmooth.linearIndepOn_pow_of_linearIndepOn_id k K _ iF iA hK p hpp _ t ht, hne⟩


end P2MW.S_Algebra_isSmoothAt_of_mem_minimalPrimes_of_dense_of_formallySmooth_residueField
end ZInQ.Contrib.CloudR2NeronExistence.Henselian
