/-
H5 Step2 / B1 KEY L4: off support, the actual localized ideal is TOP.
Copyright (c) 2026 H5 contributors. Apache-2.0.
SOURCE ONLY / UNCOMPILED. Native/kernel/BI/Std3/current-context grade absent.

Exact frozen consumer f74bd5284d7b83d66223997f55392b01be86ef56cc3b90902ff89052bb72da01,
LocalizedComapInterface.lean3620B/73lines. This proves EXACT OffSupportLocalizationTop.{u}
with NO proof argument, Field/AV/Noetherian/Cartier/domain/dimension hypothesis.
The supplementary result uses the ORIGINAL canonical germ into X's stalk.

TRUTH PRE-CHECK: a point from the affine prime p is outside the actual
support iff I(U) is not contained in p. An actual a∈I(U)\p becomes a UNIT
under the SAME prime localization's canonical algebraMap. That actual
mapped ideal contains a unit and is top. This is true for every scheme
and every native ideal; multiplicities are not discarded to manufacture
an equality of ideals. A point inside support gives (e.g. (t) at (t)) a
proper local ideal, so the off-support premise is essential.

Native Basic support/affine-zero-locus and Mathlib localization unit/ideal
maps are reused as SINGLE actual Sources, not copied supports, a stalk
Factory or a W07/Stacks alias. C3 keeps L1 StalkIdealTransport and height-
one support-maximality; their code and L2 proof are not edited/reproved.
Original symbolic u, I, U, p, germ/algebraMap and native ideal preserved.
No numeric/transparency/root option or Native/parser/helper/AST/intake.
-/
import ZInQKernel.Contrib.CloudR2NOS.Step2B1.LocalizedComapInterface
import Mathlib.AlgebraicGeometry.IdealSheaf.Basic
import Mathlib.AlgebraicGeometry.Stalk

set_option autoImplicit false
noncomputable section
universe u
open CategoryTheory AlgebraicGeometry

namespace H5OriginalDVR.Lane2.B1OffSupportLocalization

/-- The actual coefficient outside the prime becomes a unit under the
ORIGINAL canonical localization map; the ORIGINAL extended ideal is top.
No domain/Noetherian/field or numerical rank assumption is required. -/
theorem ideal_map_top_of_not_le_prime
    {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
    (p : Ideal R) [p.IsPrime] [IsLocalization.AtPrime S p]
    (I : Ideal R) (hI : ¬ I ≤ p) : I.map (algebraMap R S) = ⊤ := by
  classical
  obtain ⟨a, haI, hap⟩ := Set.not_subset.mp hI
  have hu : IsUnit (algebraMap R S a) :=
    IsLocalization.map_units S (M := p.primeCompl) ⟨a, hap⟩
  exact Ideal.eq_top_of_isUnit_mem _ (Ideal.mem_map_of_mem _ haI) hu

/-- Outside the actual zero support, the affine ideal is not contained in
this affine prime. Native image-zero-locus and support inclusion prove it,
not an assumed support/ideal correspondence for arbitrary divisors. -/
theorem not_le_asIdeal_of_not_mem_support
    {X : Scheme.{u}} (I : X.IdealSheafData) (U : X.affineOpens)
    (p : PrimeSpectrum Γ(X, U.1)) (hη : U.2.fromSpec p ∉ (I.support : Set X)) :
    ¬ I.ideal U ≤ p.asIdeal := by
  intro hle
  apply hη
  have hpZ : p ∈ PrimeSpectrum.zeroLocus (I.ideal U) := hle
  have hx : U.2.fromSpec p ∈ X.zeroLocus (U := U.1) (I.ideal U) ∩ U.1 := by
    rw [← U.2.fromSpec_image_zeroLocus (I.ideal U)]
    exact ⟨p, hpZ, rfl⟩
  exact I.zeroLocus_inter_subset_supportSet U hx

/-- The exact native affine localization is unit off support. -/
theorem off_support_localization_top
    {X : Scheme.{u}} (I : X.IdealSheafData) (U : X.affineOpens)
    (p : PrimeSpectrum Γ(X, U.1)) (hη : U.2.fromSpec p ∉ (I.support : Set X)) :
    Ideal.map (algebraMap Γ(X, U.1) (Localization.AtPrime p.asIdeal)) (I.ideal U) = ⊤ :=
  ideal_map_top_of_not_le_prime p.asIdeal (I.ideal U)
    (not_le_asIdeal_of_not_mem_support I U p hη)

/-- The same statement on the ORIGINAL scheme stalk, with its ACTUAL
presheaf germ. The native algebra-section-stalk dictionary is exactly
this germ, and its actual IsLocalization identifies the same affine prime. -/
theorem off_support_original_stalk_ideal_top
    {X : Scheme.{u}} (I : X.IdealSheafData) (U : X.affineOpens)
    (x : X) (hxU : x ∈ U.1) (hx : x ∉ (I.support : Set X)) :
    Ideal.map (X.presheaf.germ U.1 x hxU).hom (I.ideal U) = ⊤ := by
  letI : Algebra Γ(X, U.1) (X.presheaf.stalk x) :=
    TopCat.Presheaf.algebra_section_stalk X.presheaf ⟨x, hxU⟩
  let p := U.2.primeIdealOf ⟨x, hxU⟩
  letI : IsLocalization.AtPrime (X.presheaf.stalk x) p.asIdeal :=
    U.2.isLocalization_stalk ⟨x, hxU⟩
  have hp : U.2.fromSpec p ∉ (I.support : Set X) := by
    dsimp only [p]
    rw [U.2.fromSpec_primeIdealOf]
    exact hx
  exact ideal_map_top_of_not_le_prime p.asIdeal (I.ideal U)
    (not_le_asIdeal_of_not_mem_support I U p hp)

/-- EXACT frozen consumer Prop, no extra proof parameter or new assumption. -/
theorem offSupportLocalizationTop :
    ZInQ.Contrib.CloudR2NOS.Step2B1.OffSupportLocalizationTop.{u} := by
  intro X I U p hη
  exact off_support_localization_top I U p hη

end H5OriginalDVR.Lane2.B1OffSupportLocalization
