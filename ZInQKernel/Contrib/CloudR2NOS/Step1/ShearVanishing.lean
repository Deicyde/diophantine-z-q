/-
H5 FIX EDITION STEP-F1 (NEW edition, 2026-11-17, H5 lane3 ). SOURCE ONLY, UNCOMPILED by lane3.
Base file: step1-i1/src/ZInQKernel/Contrib/CloudR2NOS/Step1/ShearVanishing.lean (sha256 25a5d3e770b774511c30a32baa883d9f03a7302e1266fb2d0774f0a7febdf04d).
Body changes relative to the base: ONLY P3 (record step-fix1/FIX_RECORD_STEP_F1.json). The base header below describes the BASE edition.
-/
/-
v2 (R1 v2, lead-approved 04:09Z; v1 ac46af71 is in history/): R1a, R1b and GM5′ additionally assume
`[IsSeparated fX] [IsProper fX]` and finitely presented coefficients. This is an INTERNAL
strengthening; the application (fX = H̄ → Spec k̄ proper, L' invertible) satisfies it.
H5 lane3 Step 1, component GM5′: shear vanishing. 2026-11-17. New file. SOURCE-ONLY,
UNCOMPILED. Universe u, any field K, no characteristic or dimension restriction.

ROUTE SIMPLIFICATION, reported to the lead. Plan c3e58087 §3 steps 4–5 used
* full Pic⁰ vanishing on Y (GM4), and
* Künneth on H̄×Y (GM2).
NEITHER is needed. Taking `R^q pr₂_*` of the shear isomorphism and then global sections on `Y`
proves, for every `q`,
  `H^q(X, L) ⊗ Γ(Y, O_Y) ≅ Γ(Y, R^q pr₂_*(pr₁^*L ⊗ pr₂^*Q)) ≅ H^q(X, L) ⊗ Γ(Y, Q) = 0`.
So `H^q(X, L) = 0` follows from `Γ(Y, Q) = 0` ALONE. That vanishing is elementary for a nontrivial
`Q ∈ Pic⁰(Y)`; see `CoreGap` part R3 in `I1Assembly.lean`.

The theorem below is generic: any `X`, `Y` over `K`, an automorphism `ψ` of `X ×_K Y` over `Y`,
and an isomorphism `ψ^*(pr₁^*L) ≅ pr₁^*L ⊗ pr₂^*Q`. The abelian-variety instance is
* `X = H̄`, `Y` the abelian subvariety;
* `ψ(a, y) = (a + y, y)`;
* the isomorphism from the seesaw (GM1).

It uses three UNPROVED sub-gaps, stated exactly below. Each is true for the stated hypotheses.
* R1a and R1b: relative flat base change, `R^q pr₂_* pr₁^*F ≅ H^q(X,F) ⊗_K O_Y`, plus the
  invertible projection formula. The W07 support identified is:
  - `Scheme.Modules.invertibleProjectionIso` (Modules/ProjectionFormula, degree 0);
  - `nonempty_H_baseChange_linearEquiv` (Cohomology/FlatBaseChange);
  - `higherDirectImagePullbackIsoRestrict` (DirectImage/Restrict);
  - `isQuasicoherent_higherDirectImage`;
  - `exists_bijective_semilinearMap_sections_higherDirectImage_H`.
  The missing pieces are deriving the degree-0 projection iso through the exact autoequivalence
  `tensorRight`, and the affine-local assembly.
* R2: `R^q f_*` is invariant under an automorphism over the base. The missing piece is
  `R^q f_*(ψ^*E) ≅ R^q (ψ⁻¹ ≫ f)_* E` together with `ψ⁻¹ ≫ f = f`.
-/
import ZInQKernel.Contrib.CloudW07JacobiansCurves.Jacobian.AlgebraicGeometry.Cohomology.DirectImage.Basic
import ZInQKernel.Contrib.CloudW07JacobiansCurves.Jacobian.AlgebraicGeometry.Cohomology.Isomorphism
import ZInQKernel.Contrib.CloudW07JacobiansCurves.Jacobian.AlgebraicGeometry.Modules.ProjectionFormula
import Mathlib.AlgebraicGeometry.Morphisms.Proper

set_option autoImplicit false

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory
open AlgebraicGeometry.Scheme.Modules
open scoped AlgebraicGeometry.Scheme.Modules

namespace ZInQ.Contrib.CloudR2NOS.Step1

/-- R1a (UNPROVED): if `Γ(Y, G) = 0` for an invertible `G`, then every `R^q pr₂_*(pr₁^*F ⊗ pr₂^*G)`
has no global sections. This follows from `R^q pr₂_*(pr₁^*F ⊗ pr₂^*G) ≅ H^q(X,F) ⊗_K G`. -/
def RelativeVanishingSections : Prop :=
  ∀ {K : Type u} [Field K] {X Y : Scheme.{u}} (fX : X ⟶ Spec (CommRingCat.of K))
    (fY : Y ⟶ Spec (CommRingCat.of K)) [QuasiCompact fX] [QuasiSeparated fX] [IsSeparated fX]
    [IsProper fX] [CompactSpace Y]
    [HasInjectiveResolutions (Limits.pullback fX fY).Modules]
    (F : X.Modules) [F.IsQuasicoherent] [F.IsFinitePresentation] (G : Y.Modules) [G.IsInvertible]
    (q : ℕ),
    Subsingleton (G.H 0) →
      Subsingleton (((higherDirectImage (pullback.snd fX fY) q).obj
        ((Scheme.Modules.pullback (pullback.fst fX fY)).obj F ⊗
          (Scheme.Modules.pullback (pullback.snd fX fY)).obj G)).H 0)

/-- R1b (UNPROVED): if `R^q pr₂_*(pr₁^*F)` has no global sections on a nonempty `Y`, then
`h^q(X, F) = 0`. This follows from `R^q pr₂_* pr₁^*F ≅ H^q(X,F) ⊗_K O_Y` and `K ↪ Γ(Y, O_Y)`. -/
def RelativeDetectionSections : Prop :=
  ∀ {K : Type u} [Field K] {X Y : Scheme.{u}} (fX : X ⟶ Spec (CommRingCat.of K))
    (fY : Y ⟶ Spec (CommRingCat.of K)) [QuasiCompact fX] [QuasiSeparated fX] [IsSeparated fX]
    [IsProper fX] [CompactSpace Y]
    [Nonempty Y] [HasInjectiveResolutions (Limits.pullback fX fY).Modules]
    (F : X.Modules) [F.IsQuasicoherent] [F.IsFinitePresentation] (q : ℕ),
    Subsingleton (((higherDirectImage (pullback.snd fX fY) q).obj
        ((Scheme.Modules.pullback (pullback.fst fX fY)).obj F)).H 0) →
      (letI : X.Over (Spec (CommRingCat.of K)) := ⟨fX⟩; F.finrankH K q) = 0

/-- R2 (UNPROVED): higher direct images are invariant under an automorphism over the base. -/
def HigherDirectImageAutomorphism : Prop :=
  ∀ {Z B : Scheme.{u}} [HasInjectiveResolutions Z.Modules] (f : Z ⟶ B) (ψ : Z ⟶ Z) [IsIso ψ],
    ψ ≫ f = f → ∀ (E : Z.Modules) (q : ℕ),
      Nonempty ((higherDirectImage f q).obj ((Scheme.Modules.pullback ψ).obj E) ≅
        (higherDirectImage f q).obj E)

/-- GM5′ (shear vanishing), proved from R1a, R1b and R2: all cohomology of `L` vanishes, so
`χ(L) = 0`. -/
theorem finrankH_eq_zero_of_shear (hR1a : RelativeVanishingSections.{u})
    (hR1b : RelativeDetectionSections.{u}) (hR2 : HigherDirectImageAutomorphism.{u})
    {K : Type u} [Field K] {X Y : Scheme.{u}} (fX : X ⟶ Spec (CommRingCat.of K))
    (fY : Y ⟶ Spec (CommRingCat.of K)) [QuasiCompact fX] [QuasiSeparated fX] [IsSeparated fX]
    [IsProper fX] [CompactSpace Y]
    [Nonempty Y] [HasInjectiveResolutions (Limits.pullback fX fY).Modules]
    (L : X.Modules) [L.IsQuasicoherent] [L.IsFinitePresentation] (Q : Y.Modules) [Q.IsInvertible]
    (hQ : Subsingleton (Q.H 0))
    (ψ : Limits.pullback fX fY ⟶ Limits.pullback fX fY) [IsIso ψ]
    (hψ : ψ ≫ pullback.snd fX fY = pullback.snd fX fY)
    (σ : (Scheme.Modules.pullback ψ).obj ((Scheme.Modules.pullback (pullback.fst fX fY)).obj L) ≅
      (Scheme.Modules.pullback (pullback.fst fX fY)).obj L ⊗
        (Scheme.Modules.pullback (pullback.snd fX fY)).obj Q) (q : ℕ) :
    (letI : X.Over (Spec (CommRingCat.of K)) := ⟨fX⟩; L.finrankH K q) = 0 := by
  apply hR1b fX fY L q
  obtain ⟨e⟩ := hR2 (pullback.snd fX fY) ψ hψ
    ((Scheme.Modules.pullback (pullback.fst fX fY)).obj L) q
  -- `R^q pr₂_*(pr₁^*L) ≅ R^q pr₂_*(ψ^*pr₁^*L) ≅ R^q pr₂_*(pr₁^*L ⊗ pr₂^*Q)`
  let e' := e.symm ≪≫ (higherDirectImage (pullback.snd fX fY) q).mapIso σ
  haveI : Subsingleton (((higherDirectImage (pullback.snd fX fY) q).obj
      ((Scheme.Modules.pullback (pullback.fst fX fY)).obj L ⊗
        (Scheme.Modules.pullback (pullback.snd fX fY)).obj Q)).H 0) := hR1a fX fY L Q q hQ
  exact (H.mapLinearEquiv e' 0).toEquiv.subsingleton

/-- GM5′ in Euler form. -/
theorem eulerChar_eq_zero_of_shear (hR1a : RelativeVanishingSections.{u})
    (hR1b : RelativeDetectionSections.{u}) (hR2 : HigherDirectImageAutomorphism.{u})
    {K : Type u} [Field K] {X Y : Scheme.{u}} (fX : X ⟶ Spec (CommRingCat.of K))
    (fY : Y ⟶ Spec (CommRingCat.of K)) [QuasiCompact fX] [QuasiSeparated fX] [IsSeparated fX]
    [IsProper fX] [CompactSpace Y]
    [Nonempty Y] [HasInjectiveResolutions (Limits.pullback fX fY).Modules]
    (L : X.Modules) [L.IsQuasicoherent] [L.IsFinitePresentation] (Q : Y.Modules) [Q.IsInvertible]
    (hQ : Subsingleton (Q.H 0))
    (ψ : Limits.pullback fX fY ⟶ Limits.pullback fX fY) [IsIso ψ]
    (hψ : ψ ≫ pullback.snd fX fY = pullback.snd fX fY)
    (σ : (Scheme.Modules.pullback ψ).obj ((Scheme.Modules.pullback (pullback.fst fX fY)).obj L) ≅
      (Scheme.Modules.pullback (pullback.fst fX fY)).obj L ⊗
        (Scheme.Modules.pullback (pullback.snd fX fY)).obj Q) :
    (letI : X.Over (Spec (CommRingCat.of K)) := ⟨fX⟩; L.eulerChar K) = 0 := by
  letI : X.Over (Spec (CommRingCat.of K)) := ⟨fX⟩
  have h : ∀ q, L.finrankH K q = 0 := fun q =>
    finrankH_eq_zero_of_shear hR1a hR1b hR2 fX fY L Q hQ ψ hψ σ q
  simp only [Scheme.Modules.eulerChar, h, Nat.cast_zero, mul_zero, finsum_zero]

end ZInQ.Contrib.CloudR2NOS.Step1
