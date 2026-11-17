/-
Copyright (c) 2026 H5/NOS Round-2 lane4 contributors.
Released under Apache 2.0 license as described in the project LICENSE.

H5 closed-section plan GM11 (Step 3): the assembly I2 ⇒ I3. SOURCE ONLY, UNCOMPILED.
Native HELD. No kernel/ABI/admission grade is claimed.

`finiteBySections_tensorPow_of_closedFibre` is the general statement (any `X` proper and flat over
a DVR, any invertible `M`); `step3_I3` is its literal instance on the SAME stage `H`, `M` with the
I2 data of seam 6ad6ca04 (`s`, `k`, `g`, `Hs`, `Ms`) and the I3 conclusion fixed with C5:
`∃ a > 0, FiniteBySections (M.tensorPow a) H.X.hom` (native W07 power, FLT predicate).

The seven sub-gaps (G1)–(G7) of `Step3Gaps.lean` are EXPLICIT hypotheses here, never Facts or
axioms. Everything else is proved from them, the held W07/Mathlib bodies, and `Step3Proved.lean`:
Serre vanishing on the closed fibre (S1), section lifting over the DVR (S2), spreading generation
from the closed fibre (S3), quasi-finite ⇒ finite over the local base (S4). The integer `a` is
`b * (n₀ + 1)` with `b` from I2 and `n₀` from S1; the sections are literal lifts of a finite
presentation of the closed-fibre restriction of `M^a`. No relative ampleness, vanishing,
presentation, model, Factory, rank or Pic⁰ input; no Source/W07 power alias; no dimension or
characteristic restriction.
-/
import ZInQKernel.Contrib.CloudR2NOS.ClosedSection.Step3Proved
import ZInQKernel.HDecomp.Objects

set_option autoImplicit false

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry

attribute [local instance] MvPolynomial.gradedAlgebra

namespace ZInQ.Contrib.CloudR2NOS.ClosedSection

local notation "Pres" => ZInQ.Contrib.CloudW03NeronSurj.FLT.AlgebraicGeometry.Scheme.Modules.ProjPresentation
local notation "FBS" => ZInQ.Contrib.CloudW03NeronSurj.FLT.AlgebraicGeometry.Scheme.Modules.FiniteBySections

/-- **Step 3, general form.** For `X` proper and flat over a DVR `C` and `M` invertible: if a
positive native power of the literal closed-fibre restriction of `M` is finite-by-sections over the
residue field, then a positive native power of `M` is finite-by-sections over `C`. -/
theorem finiteBySections_tensorPow_of_closedFibre
    (hG1 : PresentationTwistIso.{u}) (hG2 : FiniteBySectionsNativePow.{u})
    (hG3 : UniformizerSequence.{u}) (hG4 : FramesNearOfPullback.{u})
    (hG5 : PresentationOfFramesNear.{u}) (hG6 : QuasiFiniteOnClosedFibre.{u})
    (hG7 : PresentationOfIso.{u})
    {C : Type u} [CommRing C] [IsDomain C] [IsDiscreteValuationRing C]
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of C)) [IsProper f] [Flat f]
    (M : X.Modules) [M.IsInvertible]
    (hI2 : ∃ b : ℕ, 0 < b ∧ FBS
        (R := ↥((Spec (CommRingCat.of C)).residueField (IsLocalRing.closedPoint C)))
        (((Scheme.Modules.pullback (f.fiberι (IsLocalRing.closedPoint C))).obj M).tensorPow b)
        (f.fiberToSpecResidueField (IsLocalRing.closedPoint C))) :
    ∃ a : ℕ, 0 < a ∧ FBS (M.tensorPow a) f := by
  classical
  let s := IsLocalRing.closedPoint C
  let i := f.fiberι s
  let Ms := (Scheme.Modules.pullback i).obj M
  haveI : IsProper (f.fiberToSpecResidueField s) := by
    show IsProper (pullback.snd f ((Spec (CommRingCat.of C)).fromSpecResidueField s))
    infer_instance
  obtain ⟨b, hb, hFBS⟩ := hI2
  -- (1) a finite presentation of `Ms^b` on the literal closed fibre (I2)
  obtain ⟨N, 𝔓, h𝔓⟩ := id hFBS
  -- (2) Serre vanishing on the closed fibre (S1, uses G1)
  obtain ⟨n₀, hvan⟩ := exists_subsingleton_H_tensorPow_of_presentation hG1 𝔓 h𝔓
  let n := n₀ + 1
  have hn : 0 < n := Nat.succ_pos n₀
  let a := b * n
  have ha : 0 < a := Nat.mul_pos hb hn
  -- (3) a finite presentation of `(Ms^b)^n` (G2)
  obtain ⟨N', 𝔓n, h𝔓n⟩ := hG2 hFBS n hn
  -- (4) transported to the literal closed-fibre restriction of `M^a` (G7)
  let e : (Ms.tensorPow b).tensorPow n ≅ (Scheme.Modules.pullback i).obj (M.tensorPow a) :=
    (tensorPowMulIso Ms b n).symm ≪≫ (pullbackTensorPowIso i M a).symm
  obtain ⟨𝔔s, h𝔔sπ, -⟩ := hG7 𝔓n e
  have h𝔔sfin : IsFinite 𝔔s.toProj := by
    rw [h𝔔sπ]
    exact h𝔓n
  -- (5) `H¹` of the literal closed-fibre restriction of `M^a` vanishes (S1 along `e`)
  have h1 : Subsingleton (((Scheme.Modules.pullback i).obj (M.tensorPow a)).H 1) := by
    haveI := hvan n (Nat.le_succ n₀) 1 Nat.one_pos
    exact (Scheme.Modules.H.mapLinearEquiv e.symm 1).toEquiv.subsingleton
  -- (6) literal lifts of the sections of `𝔔s` (S2, uses G3)
  have hlift := surjective_pullbackSection_of_subsingleton_H_one hG3 f (M.tensorPow a) h1
  choose σ hσ using fun j => hlift (𝔔s.σ j)
  -- (7) the lifts generate along the closed fibre (frames of `𝔔s` + G4), hence everywhere (S3)
  have hgen : ∀ x : X, ∃ j, FramesNear (M.tensorPow a) (σ j) x := by
    refine framesNear_of_closedFibre f (M.tensorPow a) σ fun x hx => ?_
    obtain ⟨y, rfl⟩ : ∃ y, i.base y = x := by
      have hmem : x ∈ Set.range i.base := by
        rw [Scheme.Hom.range_fiberι]
        exact hx
      exact hmem
    obtain ⟨j, hj⟩ : ∃ j, 𝔔s.toProj.base y ∈ Proj.basicOpen
        (MvPolynomial.homogeneousSubmodule (Fin (N' + 1))
          ↥((Spec (CommRingCat.of C)).residueField s)) (MvPolynomial.X j) := by
      have hcov := Proj.iSup_basicOpen_eq_top
        (MvPolynomial.homogeneousSubmodule (Fin (N' + 1)) ↥((Spec (CommRingCat.of C)).residueField s))
        (MvPolynomial.X : Fin (N' + 1) → MvPolynomial (Fin (N' + 1))
          ↥((Spec (CommRingCat.of C)).residueField s))
        (ZInQ.Contrib.CloudW03NeronSurj.FLT.AlgebraicGeometry.ProjSpace.irrelevant_le_span_X
          ↥((Spec (CommRingCat.of C)).residueField s) N')
      have hz : 𝔔s.toProj.base y ∈ (⊤ : (Proj (MvPolynomial.homogeneousSubmodule (Fin (N' + 1))
          ↥((Spec (CommRingCat.of C)).residueField s))).Opens) := trivial
      rw [← hcov, TopologicalSpace.Opens.mem_iSup] at hz
      exact hz
    refine ⟨j, hG4 i (M.tensorPow a) (σ j) y ?_⟩
    rw [hσ j]
    exact ⟨_, hj, fun V hV => 𝔔s.frame j V hV⟩
  -- (8) a presentation of `M^a` over `C` with exactly these sections (G5)
  obtain ⟨𝔔, h𝔔σ⟩ := hG5 f (M.tensorPow a) N' σ hgen
  -- (9) quasi-finite over the closed point (G6), hence finite (S4)
  have hqf := hG6 f (M.tensorPow a) N' 𝔔 𝔔s
    (fun j => by rw [h𝔔σ]; exact (hσ j).symm) h𝔔sfin
  refine ⟨a, ha, ?_⟩
  unfold ZInQ.Contrib.CloudW03NeronSurj.FLT.AlgebraicGeometry.Scheme.Modules.FiniteBySections
  exact ⟨N', 𝔔, isFinite_toProj_of_quasiFiniteAt_closedFibre f 𝔔 hqf⟩

/-- **Step 3 on the SAME stage (I2 ⇒ I3).** For the constructed stage group `H` over the DVR `C`
and the SAME line `M`, with I2 in the exact form fixed with C2 (seam 6ad6ca04 data), the I3
conclusion fixed with C5 holds. The sub-gaps (G1)–(G7) remain explicit hypotheses. -/
theorem step3_I3
    (hG1 : PresentationTwistIso.{u}) (hG2 : FiniteBySectionsNativePow.{u})
    (hG3 : UniformizerSequence.{u}) (hG4 : FramesNearOfPullback.{u})
    (hG5 : PresentationOfFramesNear.{u}) (hG6 : QuasiFiniteOnClosedFibre.{u})
    (hG7 : PresentationOfIso.{u})
    {C : Type u} [CommRing C] [IsDomain C] [IsDiscreteValuationRing C]
    (H : Grp (Over (Spec (CommRingCat.of C)))) [PkgI2.IsAbelianScheme H]
    (M : H.X.left.Modules) [M.IsInvertible]
    (hI2 :
      let s := IsLocalRing.closedPoint C
      let k : Type u := (Spec (CommRingCat.of C)).residueField s
      let g := (Spec (CommRingCat.of C)).fromSpecResidueField s
      let Hs := (Over.pullback g).mapGrp.obj H
      let Ms := (Scheme.Modules.pullback (H.X.hom.fiberι s)).obj M
      ∃ b : ℕ, 0 < b ∧ FBS (R := k) (Ms.tensorPow b) Hs.X.hom) :
    ∃ a : ℕ, 0 < a ∧ FBS (M.tensorPow a) H.X.hom := by
  haveI : IsProper H.X.hom := PkgI2.IsAbelianScheme.proper
  haveI : Smooth H.X.hom := PkgI2.IsAbelianScheme.smooth
  haveI : Flat H.X.hom := inferInstance
  exact finiteBySections_tensorPow_of_closedFibre hG1 hG2 hG3 hG4 hG5 hG6 hG7 H.X.hom M hI2

end ZInQ.Contrib.CloudR2NOS.ClosedSection
