/-
H5 lane3 Step 1, components (i) Γ(Y, O_Y) = K and (ii) R3. 2026-11-17. v2, interface v2: R3 takes
the internal `[IsProperIntegralGroup Y]`. v1 da09e4df is in history/. The abelian-variety lemmas
are kept, since C4 imports them. New file. SOURCE-ONLY,
UNCOMPILED. Universe u, any characteristic.

(i) PROVED from C5's held and independently compiled PureMathlibGlobalFunctions
`appTop_bijective` (independent review 002, receipt 09b1c66b). Its inputs are derived:
* `IsProper` from the abelian variety;
* `IsIntegral` from geometric integrality over a field (`GeometricallyIntegral.isIntegral_of_subsingleton`);
* the identity section `η` as the rational point.

(ii) R3 `SectionsVanishFromInversion` (Interfaces.lean): PROVED from
* I5b;
* the W07 bijectivity of cohomological pullback along an isomorphism (`H.pullback_bijective`);
* ONE explicit sub-gap, `TrivialOfSectionsBothWays`: on a proper integral `K`-scheme with a
  rational point, if `L ⊗ M ≅ O` and both `L` and `M` have nonzero global sections, then `L ≅ O`.
  Proof plan for that sub-gap, true, with W07/PMGF support named:
  - for nonzero `s ∈ Γ(L)` and `t ∈ Γ(M)`, `s ⊗ t ≠ 0` on an integral scheme (W07
    `tmulSection`, `IsFreeGenerator.tmulSection` on a trivializing affine, plus a domain);
  - its image under `L ⊗ M ≅ O` is a nonzero global function, hence a unit (PMGF
    `nonzero_globalFunctions_are_units`);
  - so `s` is a free generator locally (W07 `isFreeGenerator_of_bijective_smul`), and
    `homOfGlobalSection s` is an iso.
-/
import ZInQKernel.Contrib.CloudR2NOS.Step1.Interfaces
import PureMathlibGlobalFunctions
import ZInQKernel.Contrib.CloudW07JacobiansCurves.Jacobian.AlgebraicGeometry.Cohomology.Isomorphism

set_option autoImplicit false

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory
open scoped CategoryTheory.MonObj AlgebraicGeometry.Scheme.Modules

namespace ZInQ.Contrib.CloudR2NOS.Step1

/-- An abelian variety over a field is an integral scheme. -/
theorem isIntegral_of_isAbelianVariety {K : Type u} [Field K]
    (Y : Grp (Over (Spec (CommRingCat.of K)))) [PkgI2.IsAbelianVariety Y] : IsIntegral Y.X.left := by
  haveI : GeometricallyIntegral Y.X.hom := PkgI2.IsAbelianVariety.geomIntegral
  exact GeometricallyIntegral.isIntegral_of_subsingleton Y.X.hom

/-- (i): `Γ(Spec K) → Γ(Y, O_Y)` is bijective. This is the PMGF theorem at the identity section. -/
theorem appTop_bijective_of_isAbelianVariety {K : Type u} [Field K]
    (Y : Grp (Over (Spec (CommRingCat.of K)))) [PkgI2.IsAbelianVariety Y] :
    Function.Bijective Y.X.hom.appTop := by
  haveI : IsProper Y.X.hom := PkgI2.IsAbelianVariety.proper
  haveI : IsIntegral Y.X.left := isIntegral_of_isAbelianVariety Y
  exact ZInQ.Contrib.CloudR2NOS.FieldAmpleness.PureMathlibGlobalFunctions.appTop_bijective
    Y.X.hom (η[Y.X] : Pt K ⟶ Y.X).left (Over.w (η[Y.X] : Pt K ⟶ Y.X))

/-- Sub-gap of R3 (UNPROVED; plan in the header): sections in both directions trivialize. -/
def TrivialOfSectionsBothWays : Prop :=
  ∀ {K : Type u} [Field K] {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of K)) [IsProper f]
    [IsIntegral X] (ε : Spec (CommRingCat.of K) ⟶ X), ε ≫ f = 𝟙 _ →
    ∀ (L M : X.Modules) [L.IsInvertible] [M.IsInvertible],
      Nonempty (L ⊗ M ≅ 𝟙_ X.Modules) → ¬ Subsingleton (L.H 0) → ¬ Subsingleton (M.H 0) →
        Nonempty (L ≅ 𝟙_ X.Modules)

/-- R3, proved from I5b and `TrivialOfSectionsBothWays`. -/
theorem sectionsVanishFromInversion (hTriv : TrivialOfSectionsBothWays.{u}) :
    SectionsVanishFromInversion.{u} := by
  intro hI5b K _ _ Y _ Q _ hinv hnt
  by_contra hns
  haveI : IsProper Y.X.hom := IsProperIntegralGroup.proper
  haveI : IsIntegral Y.X.left := isIntegral_of_isProperIntegralGroup Y
  haveI : IsIso (ι[Y.X]).left :=
    (inferInstance : IsIso ((Over.forget (Spec (CommRingCat.of K))).map ι[Y.X]))
  obtain ⟨e⟩ := hI5b Y Q hinv
  -- a nonzero section of `Q` pulls back to a nonzero section of `ι^*Q` (`ι` is an isomorphism)
  have hns' : ¬ Subsingleton (((Scheme.Modules.pullback (ι[Y.X]).left).obj Q).H 0) := by
    intro h
    exact hns ⟨fun a b =>
      (Scheme.Modules.H.pullback_bijective (ι[Y.X]).left Q 0).injective (@Subsingleton.elim _ h _ _)⟩
  exact hnt (hTriv Y.X.hom (η[Y.X] : Pt K ⟶ Y.X).left (Over.w (η[Y.X] : Pt K ⟶ Y.X)) Q
    ((Scheme.Modules.pullback (ι[Y.X]).left).obj Q) ⟨β_ _ _ ≪≫ e⟩ hns hns')

end ZInQ.Contrib.CloudR2NOS.Step1
