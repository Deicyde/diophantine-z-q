/-
Copyright (c) 2026 H5/NOS Round-2 lane4 contributors.
Released under Apache 2.0 license as described in the project LICENSE.

H5 closed-section plan GM11 (Step 3: I2 ⇒ I3), exact sub-results. SOURCE ONLY, UNCOMPILED.
Native HELD. No kernel/ABI/admission grade is claimed.

Each `def … : Prop` below is ONE precisely stated, genuinely missing mathematical sub-result.
None is installed as an axiom, instance or Fact; they appear only as explicit hypotheses of
the Step-3 assembly (`Step3Assembly.lean`) and are to be PROVED in later batches.
Blueprints are named where the read-only FLT clone `~/flt-src` (anthropics/fermats-last-theorem
@ 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0) has a statement/proof to adapt;
adapted text must keep that attribution. No FLT body is ported wholesale here.

Exact definitions used (lead binding 2026-11-17): `ProjPresentation`, `FiniteBySections` from the
historical lane4 port module
`ZInQKernel.Contrib.CloudR2NOS.Source.Definitions.Def_AlgebraicGeometry_ModulesProjPresentation`,
namespace `ZInQ.Contrib.CloudW03NeronSurj.FLT` (same text as upstream
`Definitions/Def_AlgebraicGeometry_ModulesProjPresentation.lean`, sha256 322c614e…33c9, up to the
namespace wrap). Its port options (maxHeartbeats/synthInstance) are a separate later rebinding.
All module powers here are NATIVE W07 `tensorPow`; there is no Source/W07 power alias.
EDITION 2 (2026-11-17, rqprobe2 run 98c75ff5 l.130:6 "Invalid argument name `R` for function
…Scheme.Modules.ProjPresentation"; the hint lists only `M`, `f`, `N`): in Lean 4.35 the
section-variable parameters `{R} [CommRing R] {X}` of the STRUCTURE `ProjPresentation` (port
Def_AlgebraicGeometry_ModulesProjPresentation l.54–56) are not addressable as named arguments, so
`Pres … (R := κ) …` is replaced by the explicit form `@<full name> κ _ _ M' f' N` (same binder
order: R, CommRing R, X, M, f, N). EDITION 3 (rqprobe4 run 98c75ff5 l.136:10 "unexpected syntax"):
`@` needs an identifier, not the `Pres` local notation, so the full constant name
`ZInQ.Contrib.CloudW03NeronSurj.FLT.AlgebraicGeometry.Scheme.Modules.ProjPresentation` is spelled out. No other change; statement unchanged. The constant is the H5 port's
(no W03 module declares `ProjPresentation`; W03 tree searched). Supersedes cf900663 and 30a970fe (both kept frozen).
-/
import ZInQKernel.Contrib.CloudR2NOS.Source.Definitions.Def_AlgebraicGeometry_ModulesProjPresentation
import ZInQKernel.Contrib.CloudW07JacobiansCurves.Jacobian.AlgebraicGeometry.Cohomology.Basic
import ZInQKernel.Contrib.CloudW07JacobiansCurves.Jacobian.AlgebraicGeometry.Modules.TensorPower
import ZInQKernel.Contrib.CloudW07JacobiansCurves.Jacobian.AlgebraicGeometry.ProjectiveSpectrum.Twist.Polynomial
import Mathlib.AlgebraicGeometry.Fiber
import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite

set_option autoImplicit false

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

attribute [local instance] MvPolynomial.gradedAlgebra

namespace ZInQ.Contrib.CloudR2NOS.ClosedSection

/-- The FLT presentation structure (exact ported constant). -/
local notation "Pres" => ZInQ.Contrib.CloudW03NeronSurj.FLT.AlgebraicGeometry.Scheme.Modules.ProjPresentation
/-- The FLT finite-by-sections predicate (exact ported constant). -/
local notation "FBS" => ZInQ.Contrib.CloudW03NeronSurj.FLT.AlgebraicGeometry.Scheme.Modules.FiniteBySections

/-- `σ` freely generates `M` on a neighbourhood of `x`, in exactly the FLT frame convention
used by `ProjPresentation.frame`. -/
def FramesNear {X : Scheme.{u}} (M : X.Modules) (σ : Γ(M, ⊤)) (x : X) : Prop :=
  ∃ U : X.Opens, x ∈ U ∧ ∀ V : X.Opens, V ≤ U →
    Function.Bijective fun g : Γ(X, V) =>
      g • (M.presheaf.map (homOfLE (le_top : V ≤ ⊤)).op σ : Γ(M, V))

/-- The literal pulled-back global section (adjunction unit), as used by the FLT blueprints. -/
def pullbackSection {X Y : Scheme.{u}} (i : Y ⟶ X) {M : X.Modules} (σ : Γ(M, ⊤)) :
    Γ((Scheme.Modules.pullback i).obj M, ⊤) :=
  show Γ((Scheme.Modules.pullback i).obj M, i ⁻¹ᵁ ⊤) from
    (((Scheme.Modules.pullbackPushforwardAdjunction i).unit.app M).app ⊤) σ

/-- **(G1) presentation ⇒ pullback of 𝒪(1).** A presentation identifies the presented module
with the pullback of the W07 twist `𝒪(1)` along a map `φ` that is finite whenever `toProj` is.
The coordinates are `ULift.{u} (Fin (N+1))` because the held W07 Serre vanishing
(`exists_subsingleton_H_tensor_pullback_twist_of_isFinite`) takes coordinates in the scheme
universe `u`, while the FLT presentation uses `Fin (N+1) : Type`; the intended `φ` is
`𝔓.toProj` followed by the `Proj` isomorphism of the graded renaming `MvPolynomial.rename
Equiv.ulift` (no other map). Route: W07 `nonempty_iso_of_isFreeGenerator` on the cover
`toProj⁻¹ D₊(Xᵢ)`, with generators `σ i` (the presentation frames) and the pulled-back W07
`twistPowSection 1` (free by `isFreeGenerator_twistPowSection` and
`IsFreeGenerator.exists_pullback`); the transition functions agree by `app_ratio_smul`, and the
renaming is handled with W07 `ProjectiveSpectrum/Twist/Pullback`. No FLT blueprint. -/
def PresentationTwistIso : Prop :=
  ∀ {R : Type u} [CommRing R] {X : Scheme.{u}} {f : X ⟶ Spec (CommRingCat.of R)}
    {L : X.Modules} {N : ℕ} (𝔓 : Pres L f N),
    ∃ φ : X ⟶ Proj (MvPolynomial.homogeneousSubmodule (ULift.{u} (Fin (N + 1))) R),
      (IsFinite 𝔓.toProj → IsFinite φ) ∧
      Nonempty (L ≅ (Scheme.Modules.pullback φ).obj
        (Proj.twist (MvPolynomial.homogeneousSubmodule (ULift.{u} (Fin (N + 1))) R) 1))

/-- **(G2) positive native powers of a finitely presented-by-sections module.**
Blueprint: FLT `Scheme.Modules.FiniteBySections.tensorPow`
(Theorems/Thm_AlgebraicGeometry_Scheme_Modules_FiniteBySections_tensorPow.lean, blob 6334b2a6…;
proof P2M/Sol/S_…FiniteBySections_tensorPow.lean, 329 lines: degree-`n` word sections and the
Veronese charts), re-done for the NATIVE W07 power. -/
def FiniteBySectionsNativePow : Prop :=
  ∀ {R : Type u} [CommRing R] {X : Scheme.{u}} {f : X ⟶ Spec (CommRingCat.of R)} [IsProper f]
    {L : X.Modules}, FBS L f → ∀ n : ℕ, 0 < n → FBS (L.tensorPow n) f

/-- **(G3) uniformizer sequence.** For `X` flat over a DVR `C`, an invertible `F` and a
uniformizer `ϖ`, the sequence `0 → F --ϖ--> F → i_* i^* F → 0` (with `i` the closed-fibre
inclusion `f.fiberι (closedPoint C)` and the literal adjunction unit) is short exact.
No FLT blueprint (W07/Mathlib sheaf level). -/
def UniformizerSequence : Prop :=
  ∀ {C : Type u} [CommRing C] [IsDomain C] [IsDiscreteValuationRing C]
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of C)) [Flat f]
    (F : X.Modules) [F.IsInvertible] (ϖ : C), Irreducible ϖ →
    ∃ w : F.smulHom (f.appTop ((Scheme.ΓSpecIso (CommRingCat.of C)).inv ϖ)) ≫
        (Scheme.Modules.pullbackPushforwardAdjunction
          (f.fiberι (IsLocalRing.closedPoint C))).unit.app F = 0,
      (ShortComplex.mk _ _ w).ShortExact

/-- **(G4) generation descends along pullback at points.** For invertible `M`, if the
pulled-back section generates `i^*M` near `y` then the section generates `M` near `i y`
(Nakayama on the stalk). Blueprint: the pointwise step inside FLT
`exists_basicOpen_forall_exists_frame_of_frame_pullback` (Thm blob 72392093…). -/
def FramesNearOfPullback : Prop :=
  ∀ {X Y : Scheme.{u}} (i : Y ⟶ X) (M : X.Modules) [M.IsInvertible] (σ : Γ(M, ⊤)) (y : Y),
    FramesNear ((Scheme.Modules.pullback i).obj M) (pullbackSection i σ) y →
      FramesNear M σ (i.base y)

/-- **(G5) presentation from pointwise generating sections.** Blueprint: FLT
`exists_projPresentation_of_iSup_eq_top` (Thm blob c5ecac6e…) applied to the frame loci,
glued by FLT `bijective_smul_of_forall_exists_bijective_smul` (Thm blob a7a3c262…). -/
def PresentationOfFramesNear : Prop :=
  ∀ {R : Type u} [CommRing R] {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R))
    (M : X.Modules) (N : ℕ) (σ : Fin (N + 1) → Γ(M, ⊤)),
    (∀ x : X, ∃ j, FramesNear M (σ j) x) → ∃ 𝔓 : Pres M f N, 𝔓.σ = σ

/-- **(G6) quasi-finiteness over the closed point from the closed fibre.** If a presentation
`𝔔` of `M` over a local base restricts, on the literal closed fibre, to the sections of a
presentation `𝔔s` with FINITE map, then `𝔔.toProj` is quasi-finite at every point over the
closed point. Blueprint: FLT `ProjPresentation.exists_baseChange_of_isPullback`,
`ProjPresentation.locallyQuasiFinite_of_forall_exists_eq_sum_smul` and
`Scheme.Hom.quasiFiniteAt_of_isPullback_of_locallyQuasiFinite`, as composed in
P2M/Sol/S_…exists_away_finiteBySections_tensorPow_of_forall_geometricFibre.lean lines 156–198. -/
def QuasiFiniteOnClosedFibre : Prop :=
  ∀ {C : Type u} [CommRing C] [IsLocalRing C] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of C)) [IsProper f] (M : X.Modules) [M.IsInvertible]
    (N : ℕ) (𝔔 : Pres M f N)
    (𝔔s : @ZInQ.Contrib.CloudW03NeronSurj.FLT.AlgebraicGeometry.Scheme.Modules.ProjPresentation
      ↥((Spec (CommRingCat.of C)).residueField (IsLocalRing.closedPoint C)) _ _
      ((Scheme.Modules.pullback (f.fiberι (IsLocalRing.closedPoint C))).obj M)
      (f.fiberToSpecResidueField (IsLocalRing.closedPoint C)) N),
    (∀ j, 𝔔s.σ j = pullbackSection (f.fiberι (IsLocalRing.closedPoint C)) (𝔔.σ j)) →
    IsFinite 𝔔s.toProj →
    ∀ x : X, f.base x = IsLocalRing.closedPoint C → 𝔔.toProj.QuasiFiniteAt x

/-- **(G7) transport of a presentation along a module isomorphism** (same map, transported
sections). Blueprint: FLT `ProjPresentation.exists_of_iso` (Thm blob 48ff3fb2…). -/
def PresentationOfIso : Prop :=
  ∀ {R : Type u} [CommRing R] {X : Scheme.{u}} {f : X ⟶ Spec (CommRingCat.of R)}
    {M M' : X.Modules} {N : ℕ} (𝔓 : Pres M f N) (e : M ≅ M'),
    ∃ 𝔓' : Pres M' f N, 𝔓'.toProj = 𝔓.toProj ∧ ∀ j, 𝔓'.σ j = (e.hom.app ⊤) (𝔓.σ j)

end ZInQ.Contrib.CloudR2NOS.ClosedSection
