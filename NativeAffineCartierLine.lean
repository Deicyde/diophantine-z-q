/-
H5 Step2 / native auxiliary Cartier divisor line and ACTUAL section.
Copyright (c) 2026 H5 contributors. Apache-2.0.
SOURCE ONLY / UNCOMPILED. No I0/FBS/kernel/Native acceptance by this file.

For an ACTUAL native invertible ideal D, construct its SAME divisor line
D.toModules-dual and the actual canonical section by inverse evaluation,
tensoring the native ideal inclusion and the left unitor. Its zero IDEAL is
D, not merely a support with unknown multiplicity. No Stacks Cartier/sheaf
predicate, rank equality, selected section/model or Picard/ample Fact.

The C5 input is exact SameAbVarAffineComplement from4d5: a pending native
producer theorem, not an assumed original NOS input. This adapter constructs
only the AUXILIARY line on SAME Hbar, not a replacement for descent Ms/M/beta.
Finiteness of its ideal stabilizer and native FBS remain Lane2/App1 obligations.
-/
import Step2DelegatedInterfaces

set_option autoImplicit false
noncomputable section
universe u
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory
open scoped CategoryTheory.MonObj AlgebraicGeometry.Scheme.Modules

namespace H5OriginalDVR.Lane2.NativeAffineCartierLine

/-- The zero IDEAL of the actual Cartier-ideal inclusion is the same D. -/
theorem ideal_inclusion_zeroLocus {X : Scheme.{u}} (D : X.IdealSheafData)
    (hD : D.IsInvertible) :
    letI := hD.isInvertible_toModules
    D.toModulesι.zeroLocus = D := by
  letI := hD.isInvertible_toModules
  have key (x : X) : ∃ U : X.affineOpens, x ∈ U.1 ∧
      D.toModulesι.zeroLocus.ideal U = D.ideal U := by
    obtain ⟨U, hx, b, hb, hgen⟩ := hD x
    obtain ⟨s, hs⟩ := D.exists_toModulesι_app_eq (hgen ▸ Ideal.mem_span_singleton_self b)
    have hframe := hD.isFreeGenerator s (fun V h => by
      rw [hs, ← D.map_ideal h, hgen, Ideal.map_span, Set.image_singleton]
      rfl)
    refine ⟨U, hx, ?_⟩
    rw [Scheme.Modules.Hom.ideal_zeroLocus D.toModulesι U hframe
      (Scheme.Modules.isFreeGenerator_one U.1) (b := b) (by simpa using hs), hgen]
  choose U hx hU using key
  exact Scheme.IdealSheafData.ext_of_iSup_eq_top U
    (eq_top_iff.mpr fun x _ => TopologicalSpace.Opens.mem_iSup.mpr ⟨x, hx x⟩) hU

/-- Actual canonical section of the SAME native divisor line. Inverse
native evaluation maps unit to D-module tensor its dual, then the ideal
inclusion and unitor map it to that dual. No scalar/rank/line alias. -/
def divisorSection {X : Scheme.{u}} (D : X.IdealSheafData) (hD : D.IsInvertible) :
    Scheme.Modules.unit X ⟶ D.toModulesᵛ := by
  letI := hD.isInvertible_toModules
  exact (Scheme.Modules.tensorObjDualIsoUnit D.toModules).inv ≫
    (D.toModulesι ▷ D.toModulesᵛ) ≫ (λ_ D.toModulesᵛ).hom

/-- The canonical section cuts out the COMPLETE ORIGINAL D ideal. -/
theorem divisorSection_zeroLocus {X : Scheme.{u}} (D : X.IdealSheafData)
    (hD : D.IsInvertible) :
    letI := hD.isInvertible_toModules
    (divisorSection D hD).zeroLocus = D := by
  letI := hD.isInvertible_toModules
  let E := Scheme.Modules.tensorObjDualIsoUnit D.toModules
  let q := D.toModulesι ▷ D.toModulesᵛ
  have e : Arrow.mk q ≅ Arrow.mk (divisorSection D hD) :=
    Arrow.isoMk E (λ_ D.toModulesᵛ) (by simp [divisorSection, q, E])
  exact (Scheme.Modules.Hom.zeroLocus_eq_of_arrowIso q (divisorSection D hD) e).symm.trans
    ((Scheme.Modules.Hom.zeroLocus_whiskerRight D.toModulesι D.toModulesᵛ).trans
      (ideal_inclusion_zeroLocus D hD))

/-- A point outside D proves the ACTUAL section is nonzero. Empty schemes
are not assigned a nonzero section. No integrality/characteristic is needed. -/
theorem divisorSection_ne_zero {X : Scheme.{u}} (D : X.IdealSheafData)
    (hD : D.IsInvertible) (x : X) (hx : x ∉ D.support) : divisorSection D hD ≠ 0 := by
  letI := hD.isInvertible_toModules
  intro hz
  have hzero : D = ⊥ := by
    rw [← divisorSection_zeroLocus D hD]
    exact (Scheme.Modules.Hom.zeroLocus_eq_bot_iff _).mpr hz
  apply hx
  rw [hzero, Scheme.IdealSheafData.support_bot]
  trivial

/-- C5's exact native affine-complement output constructs SOME auxiliary
native invertible EFFECTIVE line on the SAME original A. It is NOT yet FBS,
not a chosen model/ample line premise, and never substitutes descent Ms.
The support complement and actual theta-zero-IDEAL are both retained. -/
theorem auxiliary_effective_line_of_affine_complement
    (hCore : H5OriginalDVR.Lane2.Step2DelegatedInterfaces.SameAbVarAffineComplement.{u})
    {K : Type u} [Field K] [IsAlgClosed K]
    (A : Grp (Over (Spec (CommRingCat.of K)))) [PkgI2.IsAbelianVariety A]
    (U : A.X.left.Opens) (hU : IsAffineOpen U)
    (hunit : (η[A.X]).left (IsLocalRing.closedPoint K) ∈ U) :
    ∃ (N : A.X.left.Modules) (hN : N.IsInvertible),
      letI := hN
      ∃ (θ : Scheme.Modules.unit A.X.left ⟶ N) (_ : θ ≠ 0)
        (D : A.X.left.IdealSheafData) (_ : D.IsInvertible),
        (D.support : Set A.X.left) = (U : Set A.X.left)ᶜ ∧
        D = θ.zeroLocus ∧ Nonempty (N ≅ D.toModulesᵛ) := by
  obtain ⟨D, hD, hsupp⟩ := hCore A U hU hunit
  letI := hD.isInvertible_toModules
  let N := D.toModulesᵛ
  let θ := divisorSection D hD
  have hout : (η[A.X]).left (IsLocalRing.closedPoint K) ∉ D.support := by
    change (η[A.X]).left (IsLocalRing.closedPoint K) ∉ (D.support : Set A.X.left)
    rw [hsupp]
    exact not_not.mpr hunit
  exact ⟨N, inferInstance, θ, divisorSection_ne_zero D hD _ hout,
    D, hD, hsupp, (divisorSection_zeroLocus D hD).symm, ⟨Iso.refl _⟩⟩

end H5OriginalDVR.Lane2.NativeAffineCartierLine
