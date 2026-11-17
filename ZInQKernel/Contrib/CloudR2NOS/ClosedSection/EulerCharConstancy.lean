/-
Copyright (c) 2026 H5/NOS Round-2 lane4 contributors.
Released under Apache 2.0 license as described in the project LICENSE.

H5 closed-section plan GM10 / interface I4 (consumer: C3 Step 1, ).
SOURCE ONLY, UNCOMPILED. Native HELD. No kernel/ABI/admission grade is claimed.

Constancy of the native (W07) fibre Euler characteristic of an invertible sheaf in a
proper, locally finitely presented, flat family over a preconnected base.

This is a thin composition of the HELD, already proved W07 theorem
`AlgebraicGeometry.Scheme.Modules.isLocallyConstant_eulerCharFiber`
(fork `…/CloudW07JacobiansCurves/Jacobian/AlgebraicGeometry/Cohomology/DirectImage/EulerCharacteristic.lean`,
sha256 ed4820b5c7a4430f1422b5fe6d5f973b0142af044d7a9090e062a5c4de45ee55), which needs no
Noetherian, DVR, smoothness, characteristic or dimension hypothesis. So the planned DVR
specialization route is not needed.

* Flatness of the coefficient over the base is DERIVED from flatness of the family
  (W07 `isFlatOver_of_isInvertible`, Modules/Flat.lean); it is not a premise.
* Finite presentation and quasi-coherence of an invertible sheaf are the standard
  instances (W07 `SheafOfModules.IsInvertible.isFiniteLocallyFree`,
  `SheafOfModules.IsFiniteLocallyFree.isFinitePresentation`; Mathlib
  `IsFinitePresentation → IsQuasicoherent`).
* No χ value, constancy, family, fibre identification or Fact is assumed.

The specialization to C3's twist family `p₁^*M ⊗ m^*N ⊗ p₁^*Nᵛ` on `A ×_K A` (fibre
identifications at `z` and at the unit) is NOT done here; C3 performs it on top of
`eulerChar_pullback_eq_of_preconnectedSpace` below.
EDITION 2 (2026-11-17, world 004 run h5v5w4-closedsection-eulercharconstancy-bddc708c, first compile of
this file): (i) Lean 4.35 term layout — in `(letI : T := ⟨…⟩⏎ body)` the more-indented next line is
absorbed into the letI VALUE, so an explicit `;` now ends each of the 3 letI values (63:70, 79:70
"expected ';' or line break"). (ii) 52:3 `IsFinitePresentation F` was not found by instance search;
the two W07 facts (Jacobian/Algebra/Category/ModuleCat/Sheaf/LocallyFree.lean l.86–87
`IsInvertible.isFiniteLocallyFree`, l.151–152 `IsFiniteLocallyFree.isFinitePresentation`) are now
applied explicitly as `haveI` in the two theorems that consume the W07 Euler-characteristic API
(as W07 itself does, Modules/Flat.lean l.62). Statements unchanged. Supersedes 8b994970 (kept frozen).
EDITION 3 (h5w4p1 run bddc708c l.79:5 `failed to synthesize SheafOfModules.IsQuasicoherent`): the W07 Euler API
also needs quasi-coherence; `haveI := SheafOfModules.IsInvertible.isQuasicoherent.{u, u, u} F` (the pattern that
compiled in C3's I1BaseChange) is added beside the two finiteness `haveI`s. Supersedes 05f39043 (kept frozen).
EDITION 4 (p7o1 run bddc708c l.65:65/81:65): W07 `SheafOfModules.IsInvertible.isQuasicoherent` takes the
INVERTIBILITY PROOF explicitly ({moduleSheaf} (invertible : moduleSheaf.IsInvertible), W07 Jacobian/Algebra/Category/
ModuleCat/Sheaf/Quasicoherent.lean l.83–84), not the module: now `… := SheafOfModules.IsInvertible.isQuasicoherent
‹F.IsInvertible›` with the stated type `F.IsQuasicoherent` (the 62:52/78:65 unsolved goals were the error-recovery
consequence). Supersedes d2f5d2ca (kept frozen).
EDITION 5 (p7o2 l.70:31/86:31: the lemma's universes defaulted to 0 when applied to `‹F.IsInvertible›`): now
dot notation on the instance, `(inferInstance : F.IsInvertible).isQuasicoherent`, so the universes are taken from
F's type. Supersedes 00da9454 (kept frozen).
-/
import ZInQKernel.Contrib.CloudW07JacobiansCurves.Jacobian.AlgebraicGeometry.Cohomology.DirectImage.EulerCharacteristic
import ZInQKernel.Contrib.CloudW07JacobiansCurves.Jacobian.AlgebraicGeometry.Cohomology.FiberBaseChange
import ZInQKernel.Contrib.CloudW07JacobiansCurves.Jacobian.AlgebraicGeometry.Cohomology.FiberField
import ZInQKernel.Contrib.CloudW07JacobiansCurves.Jacobian.AlgebraicGeometry.Modules.Flat

set_option autoImplicit false

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace ZInQ.Contrib.CloudR2NOS.ClosedSection

/-- **GM10 core.** Over a preconnected base, the native fibre Euler characteristic of an
invertible sheaf in a proper, locally finitely presented, flat family takes the same value
at every point of the base. -/
theorem eulerCharFiber_eq_of_preconnectedSpace
    {X T : Scheme.{u}} (f : X ⟶ T) [IsProper f] [LocallyOfFinitePresentation f] [Flat f]
    [PreconnectedSpace T] (F : X.Modules) [F.IsInvertible] (t t' : T) :
    F.eulerCharFiber f t = F.eulerCharFiber f t' := by
  haveI : F.IsFiniteLocallyFree := SheafOfModules.IsInvertible.isFiniteLocallyFree F
  haveI : F.IsFinitePresentation := SheafOfModules.IsFiniteLocallyFree.isFinitePresentation F
  haveI : F.IsQuasicoherent := (inferInstance : F.IsInvertible).isQuasicoherent
  exact (Scheme.Modules.isLocallyConstant_eulerCharFiber f F
    (Scheme.Modules.isFlatOver_of_isInvertible f F)).apply_eq_of_preconnectedSpace t t'

/-- The native Euler characteristic over a field `K` of the LITERAL fibre of `f` at a
`K`-point `w` of the base (the scheme `pullback f w` with its projection to `Spec K`, and the
coefficient pulled back along `pullback.fst f w`) is the fibre Euler characteristic of `F` at
the image point of `w`. -/
theorem eulerChar_pullback_eq_eulerCharFiber
    {K : Type u} [Field K] {X T : Scheme.{u}} (f : X ⟶ T) [IsProper f]
    (F : X.Modules) [F.IsInvertible] (w : Spec (CommRingCat.of K) ⟶ T) :
    (letI : (pullback f w).Over (Spec (CommRingCat.of K)) := ⟨pullback.snd f w⟩;
      ((Scheme.Modules.pullback (pullback.fst f w)).obj F).eulerChar K) =
      F.eulerCharFiber f (w.base (IsLocalRing.closedPoint K)) := by
  haveI : F.IsFiniteLocallyFree := SheafOfModules.IsInvertible.isFiniteLocallyFree F
  haveI : F.IsFinitePresentation := SheafOfModules.IsFiniteLocallyFree.isFinitePresentation F
  haveI : F.IsQuasicoherent := (inferInstance : F.IsInvertible).isQuasicoherent
  exact (Scheme.Modules.eulerCharFiber_eq_eulerChar (pullback.snd f w)
      ((Scheme.Modules.pullback (pullback.fst f w)).obj F) (IsLocalRing.closedPoint K)).symm.trans
    (Scheme.Modules.eulerCharFiber_pullback_of_isPullback f F w (pullback.fst f w)
      (pullback.snd f w) (IsPullback.of_hasPullback f w) (IsLocalRing.closedPoint K))

/-- **GM10, rational-point form (the I4 core delivered to C3).** For a proper, locally
finitely presented, flat family `f : X ⟶ T` over a preconnected base, an invertible `F` on `X`,
and two `K`-points `z z'` of `T`, the native Euler characteristics over `K` of the two literal
fibres (with the literal pulled-back coefficients) are equal. -/
theorem eulerChar_pullback_eq_of_preconnectedSpace
    {K : Type u} [Field K] {X T : Scheme.{u}} (f : X ⟶ T)
    [IsProper f] [LocallyOfFinitePresentation f] [Flat f] [PreconnectedSpace T]
    (F : X.Modules) [F.IsInvertible] (z z' : Spec (CommRingCat.of K) ⟶ T) :
    (letI : (pullback f z).Over (Spec (CommRingCat.of K)) := ⟨pullback.snd f z⟩;
      ((Scheme.Modules.pullback (pullback.fst f z)).obj F).eulerChar K) =
    (letI : (pullback f z').Over (Spec (CommRingCat.of K)) := ⟨pullback.snd f z'⟩;
      ((Scheme.Modules.pullback (pullback.fst f z')).obj F).eulerChar K) :=
  (eulerChar_pullback_eq_eulerCharFiber f F z).trans
    ((eulerCharFiber_eq_of_preconnectedSpace f F _ _).trans
      (eulerChar_pullback_eq_eulerCharFiber f F z').symm)

end ZInQ.Contrib.CloudR2NOS.ClosedSection
