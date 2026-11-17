/-
oldSHA: 9ca69226b3271bd26c98a7119fcce05412ad596aa00184aec5ff9d10e39d1107
newedition: compile-fixes-20261117/nativecartiercodimension-001
change notice: SOURCE ONLY / UNCOMPILED. Proof-only repair of run
h5v5w4-nativecartiercodimension-91ecf62f-001: supply the pinned fromSpec
open-immersion instance explicitly; reflect the finite ENat contradiction to Nat.
All public types, hypotheses, order, results, universes, imports and options unchanged.
Original, staged, forked and published sources remain untouched; parent alone probes.
-/
/-
Copyright (c) 2026 H5 contributors. Apache-2.0.
Native Cartier-component codimension support for C2 A3 and C3 B2.d2.
SOURCE ONLY / UNCOMPILED. All original scheme/point/ideal/ring parameters
are universe u. No catenarity, UFD/normal, dimension cap or characteristic
premise is hidden in these Cartier assertions.

Krull PIT is used on the ACTUAL regular-principal affine equation. A
component generic point has no strictly more general point in the same
closed support, so its affine prime is genuinely minimal over the equation.
Nonzerodivisor + nonunit gives height at least1; PIT gives at most1.
All strict-inclusion work uses the actual affine prime-height inequality.
No support-to-IDEAL identification or multiplicity assertion is made.
-/
import ZInQKernel.Contrib.CloudW07JacobiansCurves.Jacobian.AlgebraicGeometry.IdealSheaf.EffectiveCartier
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.AlgebraicGeometry.Stalk
import Mathlib.RingTheory.Ideal.KrullsHeightTheorem
import Mathlib.Topology.Sober
import Mathlib.Topology.Separation.Basic
import Mathlib.Tactic

set_option autoImplicit false
noncomputable section
universe u

open CategoryTheory AlgebraicGeometry TopologicalSpace
open scoped nonZeroDivisors

namespace H5OriginalDVR.Lane5.I0Native

/-- Maximal irreducible subsets of a closed set are closed; this is derived. -/
theorem maximal_irreducible_subset_closed
    {T : Type u} [TopologicalSpace T] (B E : Set T) (hB : IsClosed B)
    (hE : Maximal (fun Z : Set T => Z ⊆ B ∧ IsIrreducible Z) E) : IsClosed E := by
  have hclB : closure E ⊆ B := closure_minimal hE.1.1 hB
  have hclE : closure E ⊆ E := hE.2 ⟨hclB, hE.1.2.closure⟩ subset_closure
  have heq : closure E = E := Set.Subset.antisymm hclE subset_closure
  simpa only [heq] using (isClosed_closure (s := E))

/-- The generic point of a maximal support component has no proper
more-general point lying in that same closed support. -/
theorem maximal_generic_no_generization
    {T : Type u} [TopologicalSpace T] [T0Space T]
    (B E : Set T) (hB : IsClosed B)
    (hE : Maximal (fun Z : Set T => Z ⊆ B ∧ IsIrreducible Z) E)
    (x : T) (hx : IsGenericPoint x E) (y : T) (hyB : y ∈ B) (hyx : y ⤳ x) : y = x := by
  have hclB : closure ({y} : Set T) ⊆ B :=
    closure_minimal (Set.singleton_subset_iff.mpr hyB) hB
  have hEcl : E ⊆ closure ({y} : Set T) :=
    hx.symm.trans_subset (specializes_iff_closure_subset.mp hyx)
  have hclE : closure ({y} : Set T) ⊆ E :=
    hE.2 ⟨hclB, isIrreducible_singleton.closure⟩ hEcl
  have hy : IsGenericPoint y E := Set.Subset.antisymm hclE hEcl
  exact (hx.eq hy).symm

/-- The subtype/component version needed by C2's literal A3 interface. -/
theorem component_generic_no_generization
    {T : Type u} [TopologicalSpace T] [T0Space T]
    (C : irreducibleComponents T) (x : T) (hx : IsGenericPoint x (C : Set T))
    (y : T) (hyx : y ⤳ x) : y = x := by
  have hCcl : (C : Set T) ⊆ closure ({y} : Set T) :=
    hx.symm.trans_subset (specializes_iff_closure_subset.mp hyx)
  have hclC : closure ({y} : Set T) ⊆ C :=
    C.property.2 isIrreducible_singleton.closure hCcl
  have hy : IsGenericPoint y (C : Set T) := Set.Subset.antisymm hclC hCcl
  exact (hx.eq hy).symm

/-- A component-generic point of an ACTUAL Cartier support has original
stalk dimension1. The no-generization input is produced by the preceding
component lemmas at applications, not a new original-NOS assumption. -/
theorem cartier_stalk_dim_one_of_no_generization
    {X : Scheme.{u}} [IsNoetherian X] (D : X.IdealSheafData) (hD : D.IsInvertible)
    (x : X) (hxD : x ∈ D.support)
    (hmin : ∀ y : X, y ∈ D.support → y ⤳ x → y = x) :
    ringKrullDim (X.presheaf.stalk x) = 1 := by
  obtain ⟨V, hxV, b, hb, hJ⟩ := hD x
  let p : PrimeSpectrum Γ(X, V.1) := V.2.primeIdealOf ⟨x, hxV⟩
  let J : Ideal Γ(X, V.1) := D.ideal V
  letI : IsNoetherianRing Γ(X, V.1) := IsLocallyNoetherian.component_noetherian V
  letI : J.IsPrincipal := ⟨b, hJ⟩
  have hpzero : p ∈ PrimeSpectrum.zeroLocus (J : Set Γ(X, V.1)) := by
    rw [← V.2.fromSpec_preimage_zeroLocus]
    change V.2.fromSpec (V.2.primeIdealOf ⟨x, hxV⟩) ∈ X.zeroLocus (J : Set Γ(X, V.1))
    rw [V.2.fromSpec_primeIdealOf]
    exact (D.mem_support_iff_of_mem hxV).mp hxD
  have hJp : J ≤ p.asIdeal := (PrimeSpectrum.mem_zeroLocus p J).mp hpzero
  have hpmin : p.asIdeal ∈ J.minimalPrimes := by
    refine ⟨⟨p.isPrime, hJp⟩, ?_⟩
    intro q hq hqp
    let q₀ : PrimeSpectrum Γ(X, V.1) := ⟨q, hq.1⟩
    have hqzero : q₀ ∈ PrimeSpectrum.zeroLocus (J : Set Γ(X, V.1)) := hq.2
    let y : X := V.2.fromSpec q₀
    have hyV : y ∈ V.1 := V.2.range_fromSpec.le ⟨q₀, rfl⟩
    have hyZero : y ∈ X.zeroLocus (J : Set Γ(X, V.1)) :=
      ((V.2.fromSpec_image_zeroLocus J).le ⟨q₀, hqzero, rfl⟩).1
    have hyD : y ∈ D.support := (D.mem_support_iff_of_mem hyV).mpr hyZero
    have hqp' : q₀ ≤ p := hqp
    have hyx : y ⤳ x := by
      have h := ((PrimeSpectrum.le_iff_specializes q₀ p).mp hqp').map
        V.2.fromSpec.continuous
      simpa only [y, p, V.2.fromSpec_primeIdealOf] using h
    have hyEq : y = x := hmin y hyD hyx
    have hqpEq : q₀ = p :=
      (Scheme.Hom.isOpenEmbedding V.2.fromSpec
        (H := IsAffineOpen.isOpenImmersion_fromSpec V.2)).injective
        (hyEq.trans (V.2.fromSpec_primeIdealOf ⟨x, hxV⟩).symm)
    exact (congrArg PrimeSpectrum.asIdeal hqpEq).ge
  have hbJ : b ∈ J := by
    change b ∈ D.ideal V
    rw [hJ]
    exact Ideal.mem_span_singleton_self b
  have hnu : ¬ IsUnit b := fun hu =>
    p.isPrime.ne_top (Ideal.eq_top_of_isUnit_mem p.asIdeal (hJp hbJ) hu)
  have hJh : J.height = 1 := by
    change (D.ideal V).height = 1
    rw [hJ]
    exact Ideal.height_span_singleton_eq_one_of_mem_nonZeroDivisors hb hnu
  have hph : p.asIdeal.height = 1 := le_antisymm
    (Ideal.height_le_one_of_isPrincipal_of_mem_minimalPrimes J p.asIdeal hpmin)
    (by rw [← hJh]; exact Ideal.height_mono hJp)
  letI : Algebra Γ(X, V.1) (X.presheaf.stalk x) :=
    TopCat.Presheaf.algebra_section_stalk X.presheaf ⟨x, hxV⟩
  letI : IsLocalization.AtPrime (X.presheaf.stalk x) p.asIdeal :=
    V.2.isLocalization_stalk ⟨x, hxV⟩
  calc ringKrullDim (X.presheaf.stalk x)
      = (p.asIdeal.height : WithBot ℕ∞) :=
        IsLocalization.AtPrime.ringKrullDim_eq_height p.asIdeal (X.presheaf.stalk x)
    _ = 1 := by rw [hph]; rfl

/-- Strict specialization between two codimension-one original stalks is
impossible. This uses affine prime chains, not catenarity. -/
theorem stalk_dim_one_specialization_eq
    {X : Scheme.{u}} (x y : X) (hyx : y ⤳ x)
    (hx : ringKrullDim (X.presheaf.stalk x) = 1)
    (hy : ringKrullDim (X.presheaf.stalk y) = 1) : y = x := by
  obtain ⟨V, hV, hxV, -⟩ := exists_isAffineOpen_mem_and_subset
    (x := x) (U := ⊤) (show x ∈ (⊤ : X.Opens) from trivial)
  have hyV : y ∈ V := hyx.mem_open V.isOpen hxV
  let p : PrimeSpectrum Γ(X, V) := hV.primeIdealOf ⟨x, hxV⟩
  let q : PrimeSpectrum Γ(X, V) := hV.primeIdealOf ⟨y, hyV⟩
  have hqpSpecializes : q ⤳ p := hV.fromSpec.isOpenEmbedding.isInducing.specializes_iff.mp
    (by simpa only [q, p, hV.fromSpec_primeIdealOf] using hyx)
  have hqp : q.asIdeal ≤ p.asIdeal := (PrimeSpectrum.le_iff_specializes q p).mpr hqpSpecializes
  have hpheight : p.asIdeal.height = 1 := by
    letI : Algebra Γ(X, V) (X.presheaf.stalk x) :=
      TopCat.Presheaf.algebra_section_stalk X.presheaf ⟨x, hxV⟩
    letI : IsLocalization.AtPrime (X.presheaf.stalk x) p.asIdeal :=
      hV.isLocalization_stalk ⟨x, hxV⟩
    exact_mod_cast (IsLocalization.AtPrime.ringKrullDim_eq_height p.asIdeal
      (X.presheaf.stalk x)).symm.trans hx
  have hqheight : q.asIdeal.height = 1 := by
    letI : Algebra Γ(X, V) (X.presheaf.stalk y) :=
      TopCat.Presheaf.algebra_section_stalk X.presheaf ⟨y, hyV⟩
    letI : IsLocalization.AtPrime (X.presheaf.stalk y) q.asIdeal :=
      hV.isLocalization_stalk ⟨y, hyV⟩
    exact_mod_cast (IsLocalization.AtPrime.ringKrullDim_eq_height q.asIdeal
      (X.presheaf.stalk y)).symm.trans hy
  by_contra hne
  have hstrict : q.asIdeal < p.asIdeal := lt_of_le_of_ne hqp (fun he => by
    have hpq : q = p := PrimeSpectrum.ext_iff.mpr he
    exact hne (by simpa only [q, p, hV.fromSpec_primeIdealOf] using congrArg hV.fromSpec hpq))
  have hbad := Ideal.height_add_one_le_of_lt_of_isPrime hstrict
  rw [hpheight, hqheight] at hbad
  exact (by decide : ¬ ((1 : ℕ) + 1 ≤ 1))
    ((ENat.natCast_le_natCast (n := 1 + 1) (m := 1)).mp hbad)

end H5OriginalDVR.Lane5.I0Native
