/-
Vendored from anthropics/fermats-last-theorem @ 6e837e75355538c7f80bab5b956861e86c4eacc2.
Original module: P2M.Sol.S_TwoChartCech_isLocallyConstant_fibreEulerChar. Apache-2.0.
Modification notice (CloudB3 Worker16, 2026-11-16): relocated imports; removed
nonessential negative-attribute and reactivation scaffolding; expanded namespace/open/export
helpers to ordinary commands and resolved metadata aliases directly. Mathematical proof
bodies retained, subject to documented Lean 4.35 API adaptations.
Full original notices/credits: NOTICE.upstream, ATTRIBUTION.upstream.md, LICENSE in this vendor root.
-/
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_MumfordTruncation
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_TwoChartCech
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Theorems.Thm_TwoChartCech_Mumford_finite_K0
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Theorems.Thm_TwoChartCech_Mumford_flat_K0
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Theorems.Thm_TwoChartCech_Mumford_bijective_kerMapBaseChange
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Theorems.Thm_TwoChartCech_Mumford_bijective_cokerMapBaseChange
import Mathlib.RingTheory.Spectrum.Prime.FreeLocus
import Mathlib.RingTheory.Flat.Basic
import Mathlib.RingTheory.Noetherian.Basic
import Mathlib.Algebra.Module.FinitePresentation
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.RingTheory.TensorProduct.Finite
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.P2M.Util

set_option backward.isDefEq.respectTransparency false

namespace P2MW.S_TwoChartCech_isLocallyConstant_fibreEulerChar

set_option autoImplicit false

noncomputable section

open scoped TensorProduct

universe u

namespace TwoChartCech
export TwoChartCech (Mumford.rank Mumford.K0 kerMapBaseChange cokerMapBaseChange Mumford.finite_K0 Mumford.flat_K0 Mumford.bijective_kerMapBaseChange Mumford.bijective_cokerMapBaseChange)
namespace Mumford
export TwoChartCech.Mumford (rank K0 dK ι0 ι1 comm finite_K0 flat_K0 bijective_kerMapBaseChange bijective_cokerMapBaseChange)
open TwoChartCech.Mumford
open TwoChartCech

variable {R : Type u} [CommRing R]
variable {C0 C1 : Type u} [AddCommGroup C0] [Module R C0] [AddCommGroup C1] [Module R C1]
variable (d : C0 →ₗ[R] C1) [Module.Finite R (C1 ⧸ LinearMap.range d)]

theorem finrank_ker_sub_finrank_coker {K : Type u} [Field K] {V W : Type u} [AddCommGroup V] [Module K V]
    [AddCommGroup W] [Module K W] [Module.Finite K V] [Module.Finite K W] (f : V →ₗ[K] W) :
    (Module.finrank K (LinearMap.ker f) : ℤ) - Module.finrank K (W ⧸ LinearMap.range f)
      = (Module.finrank K V : ℤ) - Module.finrank K W := by
  have h1 := f.finrank_range_add_finrank_ker
  have h2 := (LinearMap.range f).finrank_quotient_add_finrank
  omega

theorem fibreEulerChar_eq_of_bijective [Module.Flat R C0] [Module.Flat R C1] [IsNoetherianRing R]
    [Module.Finite R (LinearMap.ker d)] (𝔭 : PrimeSpectrum R)
    (hker : Function.Bijective
      (kerMapBaseChange (dK d) d (ι0 d) (ι1 d) (comm d) 𝔭.asIdeal.ResidueField))
    (hcoker : Function.Bijective
      (cokerMapBaseChange (dK d) d (ι0 d) (ι1 d) (comm d) 𝔭.asIdeal.ResidueField)) :
    (Module.finrank 𝔭.asIdeal.ResidueField
        (LinearMap.ker (d.baseChange 𝔭.asIdeal.ResidueField)) : ℤ)
      - Module.finrank 𝔭.asIdeal.ResidueField
          ((𝔭.asIdeal.ResidueField ⊗[R] C1) ⧸ LinearMap.range (d.baseChange 𝔭.asIdeal.ResidueField))
    = (Module.rankAtStalk (K0 d) 𝔭 : ℤ) - Module.rankAtStalk (Fin (rank d) → R) 𝔭 := by
  haveI := finite_K0 d; haveI := flat_K0 d
  rw [← (LinearEquiv.ofBijective _ hker).finrank_eq, ← (LinearEquiv.ofBijective _ hcoker).finrank_eq,
    finrank_ker_sub_finrank_coker, Module.rankAtStalk_eq, Module.rankAtStalk_eq]

end TwoChartCech.Mumford

open _root_.TwoChartCech _root_.P2MW.S_TwoChartCech_isLocallyConstant_fibreEulerChar.TwoChartCech _root_.TwoChartCech.Mumford _root_.P2MW.S_TwoChartCech_isLocallyConstant_fibreEulerChar.TwoChartCech.Mumford in
theorem solution
    {R : Type u} [CommRing R] [IsNoetherianRing R]
    {C0 C1 : Type u} [AddCommGroup C0] [Module R C0] [AddCommGroup C1] [Module R C1]
    [Module.Flat R C0] [Module.Flat R C1] (d : C0 →ₗ[R] C1)
    [Module.Finite R (LinearMap.ker d)] [Module.Finite R (C1 ⧸ LinearMap.range d)] :
    IsLocallyConstant fun 𝔭 : PrimeSpectrum R =>
      (Module.finrank 𝔭.asIdeal.ResidueField
          (LinearMap.ker (d.baseChange 𝔭.asIdeal.ResidueField)) : ℤ)
        - Module.finrank 𝔭.asIdeal.ResidueField
            ((𝔭.asIdeal.ResidueField ⊗[R] C1) ⧸ LinearMap.range (d.baseChange 𝔭.asIdeal.ResidueField)) := by
  haveI := Mumford.finite_K0 d; haveI := Mumford.flat_K0 d
  haveI : Module.FinitePresentation R (Mumford.K0 d) := Module.finitePresentation_of_finite R _
  have h0 : IsLocallyConstant (Module.rankAtStalk (R := R) (Mumford.K0 d)) :=
    Module.isLocallyConstant_rankAtStalk
  have h1 : IsLocallyConstant (Module.rankAtStalk (R := R) (Fin (Mumford.rank d) → R)) :=
    Module.isLocallyConstant_rankAtStalk
  have h := (h0.prodMk h1).comp (fun p : ℕ × ℕ => (p.1 : ℤ) - p.2)
  convert h using 1
  funext 𝔭
  exact Mumford.fibreEulerChar_eq_of_bijective d 𝔭 (Mumford.bijective_kerMapBaseChange d _)
    (Mumford.bijective_cokerMapBaseChange d _)

end
