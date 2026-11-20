import ZInQKernel.Contrib.CloudR2NeronExistence.Henselian.Vendor.P2M.SeventhStalkConstruction.Prelude


namespace ZInQ.Contrib.CloudR2NeronExistence.Henselian
h77_bridge_namespace

h77_import_shared
h77_open "CategoryTheory.Limits"
h77_open "AlgebraicGeometry CategoryTheory TensorProduct"
h77_open "TensorProduct"
h77_open "AlgebraicGeometry NeronModelInfra GoodReductionJacobian"
open ZInQ.Contrib.CloudW03NeronSurj.FLT

namespace P2MW.S_NeronModelInfra_exists_n_eq_and_formallySmooth_stalk_of_isOmegaMinimal_of_genericFibreRestrict_comp_eq_mul
h77_bridge_namespace

set_option autoImplicit false


set_option backward.isDefEq.respectTransparency.instanceSearchTypes false

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry NeronModelInfra GoodReductionJacobian
open scoped _root_.TensorProduct

universe u

theorem original_pullback_fraction_predicate
    {R : Type u} [rBase : CommRing R] [domainBase : IsDomain R] [dvrBase : IsDiscreteValuationRing R]
    (K : Type u) [givenK : Field K] [aRK : Algebra R K] [fractionRK : IsFractionRing R K]
    {XK : Scheme.{u}} {gK : XK ⟶ Spec (CommRingCat.of K)}
    (d : ℕ)
    (ω : Γ((ZInQ.Contrib.CloudR2NeronExistence.Henselian.AlgebraicGeometry.Scheme.Hom.topDifferentials gK) d, ⊤))
    (X : Scheme.{u}) (f : X ⟶ Spec (CommRingCat.of R))
    (Z : Scheme.{u}) (z : Z ⟶ Spec (CommRingCat.of R))
    (T : ComponentReading R K gK d ω)
    (η : ↑(pullback z f)) (U₀ : (pullback z f).Opens) (hηU : η ∈ U₀)
    (v : (U₀ : Scheme.{u}) ⟶ pullback z T.f)
 :
    let ηU : ↥U₀ := ⟨η, hηU⟩;
    let η' : ↥(pullback z T.f) := v.base ηU;
    letI rOpen : CommRing ((U₀ : Scheme.{u}).presheaf.stalk ηU) := _root_.CommRingCat.commRing ((U₀ : Scheme.{u}).presheaf.stalk ηU);
    letI rPullback : CommRing ((pullback z T.f).presheaf.stalk η') := _root_.CommRingCat.commRing ((pullback z T.f).presheaf.stalk η');
    letI algO'O : Algebra ((pullback z T.f).presheaf.stalk η') ((U₀ : Scheme.{u}).presheaf.stalk ηU) := (v.stalkMap ηU).hom.toAlgebra;
    ∀ (hdomO : IsDomain ((U₀ : Scheme.{u}).presheaf.stalk ηU)),
    letI : IsDomain ((U₀ : Scheme.{u}).presheaf.stalk ηU) := hdomO;
    letI fieldOpen : Field (FractionRing ((U₀ : Scheme.{u}).presheaf.stalk ηU)) := @FractionRing.field ((U₀ : Scheme.{u}).presheaf.stalk ηU) rOpen hdomO;
    let F := FractionRing ((U₀ : Scheme.{u}).presheaf.stalk ηU);
    ∀ (hfrac : letI : Algebra ((pullback z T.f).presheaf.stalk η') (FractionRing ((U₀ : Scheme.{u}).presheaf.stalk ηU)) :=
        ((algebraMap ((U₀ : Scheme.{u}).presheaf.stalk ηU) (FractionRing ((U₀ : Scheme.{u}).presheaf.stalk ηU))).comp (v.stalkMap ηU).hom).toAlgebra;
        IsFractionRing ((pullback z T.f).presheaf.stalk η') (FractionRing ((U₀ : Scheme.{u}).presheaf.stalk ηU))),
    IsFractionRing ((pullback z T.f).presheaf.stalk η') F := by
  classical
  intro ηU η'
  let O : Type u := ((U₀ : Scheme.{u}).presheaf.stalk ηU)
  let P : Type u := ((pullback z T.f).presheaf.stalk η')
  letI rOpen : CommRing O := _root_.CommRingCat.commRing ((U₀ : Scheme.{u}).presheaf.stalk ηU)
  letI rPullback : CommRing P := _root_.CommRingCat.commRing ((pullback z T.f).presheaf.stalk η')
  let δP : P →+* O := (v.stalkMap ηU).hom
  letI algO'O : Algebra P O := δP.toAlgebra
  intro hdomO
  letI : IsDomain O := hdomO
  letI fieldOpen : Field (FractionRing O) := @FractionRing.field O rOpen hdomO
  intro F
  intro hfrac
  have hmap : ∀ r : P,
      algebraMap P F r =
        algebraMap O F (δP r) :=
    fun _ => rfl
  have hUnits : ∀ s : nonZeroDivisors P,
      IsUnit (algebraMap O F (δP s)) := by
    letI : Algebra P F :=
      ((algebraMap O F).comp δP).toAlgebra
    letI : IsFractionRing P F := hfrac
    exact IsLocalization.map_units F
  have hSurj : ∀ q : F, ∃ x : P × nonZeroDivisors P,
      q * algebraMap O F (δP x.2) =
        algebraMap O F (δP x.1) := by
    letI : Algebra P F :=
      ((algebraMap O F).comp δP).toAlgebra
    letI : IsFractionRing P F := hfrac
    exact @IsLocalization.surj P rPullback.toCommSemiring (nonZeroDivisors P) F
      fieldOpen.toCommRing.toCommSemiring
      (((algebraMap O F).comp δP).toAlgebra) hfrac
  have hEqual : ∀ x y : P,
      algebraMap O F (δP x) =
        algebraMap O F (δP y) →
      ∃ s : nonZeroDivisors P, s * x = s * y := by
    letI : Algebra P F :=
      ((algebraMap O F).comp δP).toAlgebra
    letI : IsFractionRing P F := hfrac
    intro x y hxy
    exact IsLocalization.exists_of_eq (M := nonZeroDivisors P) hxy
  apply (isLocalization_iff (M := nonZeroDivisors P) (S := F)).mpr
  refine ⟨?_, ?_, ?_⟩
  · intro s
    rw [hmap]
    exact hUnits s
  · intro q
    have quotientRepresentation := hSurj q
    obtain ⟨x, hx⟩ := quotientRepresentation
    exact ⟨x, by simpa only [hmap] using hx⟩
  · intro x y hxy
    rw [hmap x, hmap y] at hxy
    exact hEqual x y hxy

theorem stalk_chart_left_form_equality
    {R : Type u} [rBase : CommRing R] [domainBase : IsDomain R] [dvrBase : IsDiscreteValuationRing R]
    (K : Type u) [givenK : Field K] [aRK : Algebra R K] [fractionRK : IsFractionRing R K]
    {XK : Scheme.{u}} {gK : XK ⟶ Spec (CommRingCat.of K)}
    (d : ℕ)
    (ω : Γ((ZInQ.Contrib.CloudR2NeronExistence.Henselian.AlgebraicGeometry.Scheme.Hom.topDifferentials gK) d, ⊤))
    (LXK : RelativeGroupLaw K gK)
    (hleft : (∀ (L F : Type u) [Field L] [Field F] [Algebra K L] [Algebra L F] [Algebra K F] [IsScalarTower K L F]
        (a : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap K L))) gK)
        (x : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap K F))) gK)
        (U' U'' : XK.Opens) (hU' : IsAffineOpen U') (hU'' : IsAffineOpen U'')
        [Algebra Γ(XK, U') F] [Algebra Γ(XK, U'') F],
        letI := (ZInQ.Contrib.CloudR2NeronExistence.Henselian.AlgebraicGeometry.Scheme.Hom.sectionsAlgebra gK) U'; letI := (ZInQ.Contrib.CloudR2NeronExistence.Henselian.AlgebraicGeometry.Scheme.Hom.sectionsAlgebra gK) U''
        ∀ [IsScalarTower K Γ(XK, U') F] [IsScalarTower K Γ(XK, U'') F],
        Spec.map (CommRingCat.ofHom (algebraMap Γ(XK, U') F)) ≫ hU'.fromSpec = x.1 →
        Spec.map (CommRingCat.ofHom (algebraMap Γ(XK, U'') F)) ≫ hU''.fromSpec =
          (LXK.mul (Spec.map (CommRingCat.ofHom (algebraMap K F)))
            ⟨Spec.map (CommRingCat.ofHom (algebraMap L F)) ≫ a.1, by
              rw [Category.assoc, a.2, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
                ← IsScalarTower.algebraMap_eq]⟩ x).1 →
        ∀ (ω' : ⋀[Γ(XK, U')]^d ((ZInQ.Contrib.CloudR2NeronExistence.Henselian.AlgebraicGeometry.Scheme.Hom.kaehlerPresheaf gK).obj (op U')))
          (ω'' : ⋀[Γ(XK, U'')]^d ((ZInQ.Contrib.CloudR2NeronExistence.Henselian.AlgebraicGeometry.Scheme.Hom.kaehlerPresheaf gK).obj (op U''))),
          (ZInQ.Contrib.CloudR2NeronExistence.Henselian.AlgebraicGeometry.Scheme.Hom.topToSections gK) d U' ω' = ((ZInQ.Contrib.CloudR2NeronExistence.Henselian.AlgebraicGeometry.Scheme.Hom.topDifferentials gK) d).presheaf.map (homOfLE le_top).op ω →
          (ZInQ.Contrib.CloudR2NeronExistence.Henselian.AlgebraicGeometry.Scheme.Hom.topToSections gK) d U'' ω'' = ((ZInQ.Contrib.CloudR2NeronExistence.Henselian.AlgebraicGeometry.Scheme.Hom.topDifferentials gK) d).presheaf.map (homOfLE le_top).op ω →
          TopFormOrder.topFormMap K L Γ(XK, U'') F d ω'' = TopFormOrder.topFormMap K L Γ(XK, U') F d ω'))
    (D : MinimalComponentData R K gK d ω)
    (X : Scheme.{u}) (f : X ⟶ Spec (CommRingCat.of R))
    (e : SchemeHomOver (pullback.snd f (specGenericFibreInclusion R K)) gK)
    (Z : Scheme.{u}) (z : Z ⟶ Spec (CommRingCat.of R))
    (uK : SchemeHomOver (pullback.snd z (specGenericFibreInclusion R K)) gK)
    (T : ComponentReading R K gK d ω)
    (η : ↑(pullback z f)) (U₀ : (pullback z f).Opens) (hηU : η ∈ U₀)
    (v : (U₀ : Scheme.{u}) ⟶ pullback z T.f)
    (hv₁ : v ≫ pullback.fst z T.f = U₀.ι ≫ pullback.fst z f)
 :
    let ηU : ↥U₀ := ⟨η, hηU⟩;
    let η' : ↥(pullback z T.f) := v.base ηU;
    let ζ₀ : ↥Z := (pullback.fst z T.f).base η';
    let y₁ : ↥T.Y := (pullback.snd z T.f).base η';
    letI rOpen : CommRing ((U₀ : Scheme.{u}).presheaf.stalk ηU) := _root_.CommRingCat.commRing ((U₀ : Scheme.{u}).presheaf.stalk ηU);
    letI rPrime : CommRing (Z.presheaf.stalk ζ₀) := _root_.CommRingCat.commRing (Z.presheaf.stalk ζ₀);
    letI rPullback : CommRing ((pullback z T.f).presheaf.stalk η') := _root_.CommRingCat.commRing ((pullback z T.f).presheaf.stalk η');
    letI rAux : CommRing (T.Y.presheaf.stalk y₁) := _root_.CommRingCat.commRing (T.Y.presheaf.stalk y₁);
    letI rXStalk : CommRing (X.presheaf.stalk ((pullback.snd z f).base (U₀.ι.base ηU))) := _root_.CommRingCat.commRing (X.presheaf.stalk ((pullback.snd z f).base (U₀.ι.base ηU)));
    letI algR'O' : Algebra (Z.presheaf.stalk ζ₀) ((pullback z T.f).presheaf.stalk η') := ((pullback.fst z T.f).stalkMap η').hom.toAlgebra;
    letI algO'O : Algebra ((pullback z T.f).presheaf.stalk η') ((U₀ : Scheme.{u}).presheaf.stalk ηU) := (v.stalkMap ηU).hom.toAlgebra;
    letI algR'O : Algebra (Z.presheaf.stalk ζ₀) ((U₀ : Scheme.{u}).presheaf.stalk ηU) :=
      ((v.stalkMap ηU).hom.comp ((pullback.fst z T.f).stalkMap η').hom).toAlgebra;
    letI algRR' : Algebra R (Z.presheaf.stalk ζ₀) := stalkAlgebra z ζ₀;
    letI algRO' : Algebra R ((pullback z T.f).presheaf.stalk η') := ((algebraMap (Z.presheaf.stalk ζ₀) ((pullback z T.f).presheaf.stalk η')).comp (algebraMap R (Z.presheaf.stalk ζ₀))).toAlgebra;
    letI algRO : Algebra R ((U₀ : Scheme.{u}).presheaf.stalk ηU) := ((algebraMap (Z.presheaf.stalk ζ₀) ((U₀ : Scheme.{u}).presheaf.stalk ηU)).comp (algebraMap R (Z.presheaf.stalk ζ₀))).toAlgebra;
    letI algRO₁ : Algebra R (T.Y.presheaf.stalk y₁) := stalkAlgebra T.f y₁;
    letI algO₁O' : Algebra (T.Y.presheaf.stalk y₁) ((pullback z T.f).presheaf.stalk η') := ((pullback.snd z T.f).stalkMap η').hom.toAlgebra;
    letI algO₁O : Algebra (T.Y.presheaf.stalk y₁) ((U₀ : Scheme.{u}).presheaf.stalk ηU) := ((algebraMap ((pullback z T.f).presheaf.stalk η') ((U₀ : Scheme.{u}).presheaf.stalk ηU)).comp (algebraMap (T.Y.presheaf.stalk y₁) ((pullback z T.f).presheaf.stalk η'))).toAlgebra;
    letI algRX : Algebra R (X.presheaf.stalk ((pullback.snd z f).base (U₀.ι.base ηU))) := stalkAlgebra f ((pullback.snd z f).base (U₀.ι.base ηU));
    letI algXO : Algebra (X.presheaf.stalk ((pullback.snd z f).base (U₀.ι.base ηU))) ((U₀ : Scheme.{u}).presheaf.stalk ηU) := ((U₀.ι ≫ pullback.snd z f).stalkMap ηU).hom.toAlgebra;
    ∀ (hdomO : IsDomain ((U₀ : Scheme.{u}).presheaf.stalk ηU))
      (hdomR' : IsDomain (Z.presheaf.stalk ζ₀)),
    letI : IsDomain ((U₀ : Scheme.{u}).presheaf.stalk ηU) := hdomO;
    letI fieldOpen : Field (FractionRing ((U₀ : Scheme.{u}).presheaf.stalk ηU)) := @FractionRing.field ((U₀ : Scheme.{u}).presheaf.stalk ηU) rOpen hdomO;
    letI : IsDomain (Z.presheaf.stalk ζ₀) := hdomR';
    letI fieldPrime : Field (FractionRing (Z.presheaf.stalk ζ₀)) := @FractionRing.field (Z.presheaf.stalk ζ₀) rPrime hdomR';
    let F := FractionRing ((U₀ : Scheme.{u}).presheaf.stalk ηU);
    let K' := FractionRing (Z.presheaf.stalk ζ₀);
    ∀ (aKF : Algebra K F)
      (aKKprime : Algebra K K')
      (aKprimeF : Algebra K' F),
    letI algKF : Algebra K F := aKF;
    letI algKK' : Algebra K K' := aKKprime;
    letI algK'F : Algebra K' F := aKprimeF;
    ∀ (originalRPrimeFraction : IsScalarTower R (Z.presheaf.stalk ζ₀) K')
      (originalROpenField : IsScalarTower R ((U₀ : Scheme.{u}).presheaf.stalk ηU) F)
      (originalRKOpen : IsScalarTower R K F)
      (originalRKKprime : IsScalarTower R K K')
      (originalKKprimeOpen : IsScalarTower K K' F),
    letI : IsScalarTower R (Z.presheaf.stalk ζ₀) K' := originalRPrimeFraction;
    letI : IsScalarTower R ((U₀ : Scheme.{u}).presheaf.stalk ηU) F := originalROpenField;
    letI : IsScalarTower R K F := originalRKOpen;
    letI : IsScalarTower R K K' := originalRKKprime;
    letI : IsScalarTower K K' F := originalKKprimeOpen;
    ∀ (originalRAuxField : IsScalarTower R (T.Y.presheaf.stalk y₁) F)
      (originalRXFTower : IsScalarTower R (X.presheaf.stalk ((pullback.snd z f).base (U₀.ι.base ηU))) F),
    letI : IsScalarTower R (T.Y.presheaf.stalk y₁) F := originalRAuxField;
    letI : IsScalarTower R (X.presheaf.stalk ((pullback.snd z f).base (U₀.ι.base ηU))) F := originalRXFTower;
    ∀ (halgZ : Z.fromSpecStalk ζ₀ ≫ z = Spec.map (CommRingCat.ofHom (algebraMap R (Z.presheaf.stalk ζ₀))))
      (halgO : (U₀ : Scheme.{u}).fromSpecStalk ηU ≫ (U₀.ι ≫ pullback.fst z f ≫ z) =
        Spec.map (CommRingCat.ofHom (algebraMap R ((U₀ : Scheme.{u}).presheaf.stalk ηU))))
      (halg₁ : T.Y.fromSpecStalk y₁ ≫ T.f = Spec.map (CommRingCat.ofHom (algebraMap R (T.Y.presheaf.stalk y₁))))
      (halgX : X.fromSpecStalk ((pullback.snd z f).base (U₀.ι.base ηU)) ≫ f =
        Spec.map (CommRingCat.ofHom (algebraMap R (X.presheaf.stalk ((pullback.snd z f).base (U₀.ι.base ηU)))))),
    ∀ (htrans :         (LXK.mul (Spec.map (CommRingCat.ofHom (algebraMap K F)))
        ⟨Spec.map (CommRingCat.ofHom (algebraMap K' F)) ≫
            (NeronModelInfra.schemeHomOverComp
              (pointGenericFibre (K := K) (K' := K')
                (⟨Z.fromSpecStalk ((pullback.fst z T.f).base (v.base ⟨η, hηU⟩)), halgZ⟩ :
                  SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap R (Z.presheaf.stalk ((pullback.fst z T.f).base (v.base ⟨η, hηU⟩)))))) z)) uK).1, by
          rw [Category.assoc, (NeronModelInfra.schemeHomOverComp _ uK).2, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
            ← IsScalarTower.algebraMap_eq]⟩
        (NeronModelInfra.schemeHomOverComp
          (pointGenericFibre (K := K) (K' := F)
            (⟨(U₀ : Scheme.{u}).fromSpecStalk ⟨η, hηU⟩, halgO⟩ :
              SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap R ((U₀ : Scheme.{u}).presheaf.stalk ⟨η, hηU⟩)))) (U₀.ι ≫ pullback.fst z f ≫ z)))
          (NeronModelInfra.schemeHomOverComp
            (genericFibreRestrict R K f (U₀.ι ≫ pullback.fst z f ≫ z)
              ⟨U₀.ι ≫ pullback.snd z f, by rw [Category.assoc, ← pullback.condition]⟩) e))).1 =
      (NeronModelInfra.schemeHomOverComp
        (pointGenericFibre (K := K) (K' := F)
          (⟨T.Y.fromSpecStalk ((pullback.snd z T.f).base (v.base ⟨η, hηU⟩)), halg₁⟩ :
            SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap R (T.Y.presheaf.stalk ((pullback.snd z T.f).base (v.base ⟨η, hηU⟩)))))) T.f))
        T.e).1),
    ∀ (c : D.ι),
    letI rComponent : CommRing ((D.C c).Y.presheaf.stalk (D.C c).y) := _root_.CommRingCat.commRing ((D.C c).Y.presheaf.stalk (D.C c).y);
    letI domainComponent : IsDomain ((D.C c).Y.presheaf.stalk (D.C c).y) := (D.C c).isDomain;
    letI fieldComponent : Field (FractionRing ((D.C c).Y.presheaf.stalk (D.C c).y)) := @FractionRing.field ((D.C c).Y.presheaf.stalk (D.C c).y) rComponent domainComponent;
    letI rSections : CommRing Γ(XK, (D.C c).U) := _root_.CommRingCat.commRing Γ(XK, (D.C c).U);
    ∀ (algF₀F : Algebra (FractionRing ((D.C c).Y.presheaf.stalk (D.C c).y)) (FractionRing ((U₀ : Scheme.{u}).presheaf.stalk ηU)))
      (hTowK : letI := (D.C c).algebraK; IsScalarTower K (FractionRing ((D.C c).Y.presheaf.stalk (D.C c).y)) (FractionRing ((U₀ : Scheme.{u}).presheaf.stalk ηU))),
    letI : Algebra R ((D.C c).Y.presheaf.stalk (D.C c).y) := (D.C c).algebra;
    letI : Algebra K (FractionRing ((D.C c).Y.presheaf.stalk (D.C c).y)) := (D.C c).algebraK;
    letI : IsScalarTower R K (FractionRing ((D.C c).Y.presheaf.stalk (D.C c).y)) := (D.C c).isScalarTower;
    letI : Algebra (FractionRing ((D.C c).Y.presheaf.stalk (D.C c).y)) (FractionRing ((U₀ : Scheme.{u}).presheaf.stalk ηU)) := algF₀F;
    letI : letI := (D.C c).algebraK; IsScalarTower K (FractionRing ((D.C c).Y.presheaf.stalk (D.C c).y)) (FractionRing ((U₀ : Scheme.{u}).presheaf.stalk ηU)) := hTowK;
    letI := (ZInQ.Contrib.CloudR2NeronExistence.Henselian.AlgebraicGeometry.Scheme.Hom.sectionsAlgebra gK) (D.C c).U;
    letI := (D.C c).algebraU;
    letI algUcF : Algebra Γ(XK, (D.C c).U) (FractionRing ((U₀ : Scheme.{u}).presheaf.stalk ηU)) :=
      ((algebraMap (FractionRing ((D.C c).Y.presheaf.stalk (D.C c).y)) (FractionRing ((U₀ : Scheme.{u}).presheaf.stalk ηU))).comp (algebraMap Γ(XK, (D.C c).U) (FractionRing ((D.C c).Y.presheaf.stalk (D.C c).y)))).toAlgebra;
    ∀ (hKUc : IsScalarTower K Γ(XK, (D.C c).U) (FractionRing ((U₀ : Scheme.{u}).presheaf.stalk ηU))),
    letI : IsScalarTower K Γ(XK, (D.C c).U) (FractionRing ((U₀ : Scheme.{u}).presheaf.stalk ηU)) := hKUc;
    ∀ (U'' : XK.Opens),
    letI rUSections : CommRing Γ(XK, U'') := _root_.CommRingCat.commRing Γ(XK, U'');
    letI := (ZInQ.Contrib.CloudR2NeronExistence.Henselian.AlgebraicGeometry.Scheme.Hom.sectionsAlgebra gK) U'';
    ∀ (hU'' : IsAffineOpen U'')
      (algU'' : Algebra Γ(XK, U'') (FractionRing ((U₀ : Scheme.{u}).presheaf.stalk ⟨η, hηU⟩))),
    letI : Algebra Γ(XK, U'') (FractionRing ((U₀ : Scheme.{u}).presheaf.stalk ηU)) := algU'';
    ∀ (hKU'' : letI := (ZInQ.Contrib.CloudR2NeronExistence.Henselian.AlgebraicGeometry.Scheme.Hom.sectionsAlgebra gK) U''; IsScalarTower K Γ(XK, U'') (FractionRing ((U₀ : Scheme.{u}).presheaf.stalk ⟨η, hηU⟩))),
    letI : letI := (ZInQ.Contrib.CloudR2NeronExistence.Henselian.AlgebraicGeometry.Scheme.Hom.sectionsAlgebra gK) U''; IsScalarTower K Γ(XK, U'') (FractionRing ((U₀ : Scheme.{u}).presheaf.stalk ⟨η, hηU⟩)) := hKU'';
    ∀ (hx'' : Spec.map (CommRingCat.ofHom (algebraMap Γ(XK, U'') (FractionRing ((U₀ : Scheme.{u}).presheaf.stalk ⟨η, hηU⟩)))) ≫ hU''.fromSpec =
        (NeronModelInfra.schemeHomOverComp
          (pointGenericFibre (K := K) (K' := (FractionRing ((U₀ : Scheme.{u}).presheaf.stalk ⟨η, hηU⟩)))
            (⟨T.Y.fromSpecStalk ((pullback.snd z T.f).base (v.base ⟨η, hηU⟩)), halg₁⟩ : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap R (T.Y.presheaf.stalk ((pullback.snd z T.f).base (v.base ⟨η, hηU⟩)))))) T.f))
          T.e).1)
      (ωU'' : ⋀[Γ(XK, U'')]^d ((ZInQ.Contrib.CloudR2NeronExistence.Henselian.AlgebraicGeometry.Scheme.Hom.kaehlerPresheaf gK).obj (op U'')))
      (hωU'' : (ZInQ.Contrib.CloudR2NeronExistence.Henselian.AlgebraicGeometry.Scheme.Hom.topToSections gK) d U'' ωU'' = ((ZInQ.Contrib.CloudR2NeronExistence.Henselian.AlgebraicGeometry.Scheme.Hom.topDifferentials gK) d).presheaf.map (homOfLE le_top).op ω),
    ∀ (hxX : (Spec.map (CommRingCat.ofHom (algebraMap Γ(XK, (D.C c).U) (FractionRing ((U₀ : Scheme.{u}).presheaf.stalk ηU)))) ≫ (D.C c).hU.fromSpec =
      (NeronModelInfra.schemeHomOverComp
        (pointGenericFibre (K := K) (K' := (FractionRing ((U₀ : Scheme.{u}).presheaf.stalk ηU)))
          (⟨X.fromSpecStalk ((pullback.snd z f).base (U₀.ι.base ηU)), halgX⟩ :
            SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap R (X.presheaf.stalk ((pullback.snd z f).base (U₀.ι.base ηU)))))) f)) e).1)),
    TopFormOrder.topFormMap K K' Γ(XK, U'') F d ωU'' = TopFormOrder.topFormMap K K' Γ(XK, (D.C c).U) F d (D.C c).ωU := by
  classical
  intro ηU η' ζ₀ y₁
  let O : Type u := ((U₀ : Scheme.{u}).presheaf.stalk ηU)
  let S : Type u := (Z.presheaf.stalk ζ₀)
  let P : Type u := ((pullback z T.f).presheaf.stalk η')
  let A : Type u := (T.Y.presheaf.stalk y₁)
  let ξ : ↥X := ((pullback.snd z f).base (U₀.ι.base ηU))
  let X₀ : Type u := X.presheaf.stalk ξ
  letI rOpen : CommRing O := _root_.CommRingCat.commRing ((U₀ : Scheme.{u}).presheaf.stalk ηU)
  letI rPrime : CommRing S := _root_.CommRingCat.commRing (Z.presheaf.stalk ζ₀)
  letI rPullback : CommRing P := _root_.CommRingCat.commRing ((pullback z T.f).presheaf.stalk η')
  letI rAux : CommRing A := _root_.CommRingCat.commRing (T.Y.presheaf.stalk y₁)
  letI rXStalk : CommRing X₀ := _root_.CommRingCat.commRing (X.presheaf.stalk ((pullback.snd z f).base (U₀.ι.base ηU)))
  let δP : P →+* O := (v.stalkMap ηU).hom
  let δS : S →+* P := ((pullback.fst z T.f).stalkMap η').hom
  let δA : A →+* P := ((pullback.snd z T.f).stalkMap η').hom
  let δX : X₀ →+* O := ((U₀.ι ≫ pullback.snd z f).stalkMap ηU).hom
  letI algR'O' : Algebra S P := δS.toAlgebra
  letI algO'O : Algebra P O := δP.toAlgebra
  letI algR'O : Algebra S O :=
    (δP.comp δS).toAlgebra
  letI algRR' : Algebra R S := stalkAlgebra z ζ₀
  letI algRO' : Algebra R P := ((algebraMap S P).comp (algebraMap R S)).toAlgebra
  letI algRO : Algebra R O := ((algebraMap S O).comp (algebraMap R S)).toAlgebra
  letI algRO₁ : Algebra R A := stalkAlgebra T.f y₁
  letI algO₁O' : Algebra A P := δA.toAlgebra
  letI algO₁O : Algebra A O := ((algebraMap P O).comp (algebraMap A P)).toAlgebra
  letI algRX : Algebra R X₀ := stalkAlgebra f ξ
  letI algXO : Algebra X₀ O := δX.toAlgebra
  intro hdomO hdomR'
  letI : IsDomain O := hdomO
  letI fieldOpen : Field (FractionRing O) := @FractionRing.field O rOpen hdomO
  letI : IsDomain S := hdomR'
  letI fieldPrime : Field (FractionRing S) := @FractionRing.field S rPrime hdomR'
  intro F K'
  intro aKF aKKprime aKprimeF
  letI algKF : Algebra K F := aKF
  letI algKK' : Algebra K K' := aKKprime
  letI algK'F : Algebra K' F := aKprimeF
  intro originalRPrimeFraction originalROpenField originalRKOpen originalRKKprime originalKKprimeOpen
  letI : IsScalarTower R S K' := originalRPrimeFraction
  letI : IsScalarTower R O F := originalROpenField
  letI : IsScalarTower R K F := originalRKOpen
  letI : IsScalarTower R K K' := originalRKKprime
  letI : IsScalarTower K K' F := originalKKprimeOpen
  intro originalRAuxField originalRXFTower
  letI : IsScalarTower R A F := originalRAuxField
  letI : IsScalarTower R X₀ F := originalRXFTower
  intro halgZ halgO halg₁ halgX
  intro htrans
  intro c
  let C : ComponentReading R K gK d ω := D.C c
  let O₀ : Type u := (C.Y.presheaf.stalk C.y)
  let F₀ : Type u := FractionRing O₀
  letI rComponent : CommRing O₀ := _root_.CommRingCat.commRing ((D.C c).Y.presheaf.stalk (D.C c).y)
  letI domainComponent : IsDomain O₀ := C.isDomain
  letI fieldComponent : Field F₀ := @FractionRing.field O₀ rComponent domainComponent
  let Bc : Type u := Γ(XK, C.U)
  letI rSections : CommRing Bc := _root_.CommRingCat.commRing Γ(XK, (D.C c).U)
  intro algF₀F hTowK
  letI : Algebra R O₀ := C.algebra
  letI : Algebra K F₀ := C.algebraK
  letI : IsScalarTower R K F₀ := C.isScalarTower
  letI : Algebra F₀ F := algF₀F
  letI : letI := C.algebraK; IsScalarTower K F₀ F := hTowK
  letI := (ZInQ.Contrib.CloudR2NeronExistence.Henselian.AlgebraicGeometry.Scheme.Hom.sectionsAlgebra gK) C.U
  letI := C.algebraU
  letI algUcF : Algebra Bc F :=
    ((algebraMap F₀ F).comp (algebraMap Bc F₀)).toAlgebra
  intro hKUc
  letI : IsScalarTower K Bc F := hKUc
  intro U''
  let Bu : Type u := Γ(XK, U'')
  letI rUSections : CommRing Bu := _root_.CommRingCat.commRing Γ(XK, U'')
  letI := (ZInQ.Contrib.CloudR2NeronExistence.Henselian.AlgebraicGeometry.Scheme.Hom.sectionsAlgebra gK) U''
  intro hU'' algU''
  letI : Algebra Bu F := algU''
  intro hKU''
  letI : letI := (ZInQ.Contrib.CloudR2NeronExistence.Henselian.AlgebraicGeometry.Scheme.Hom.sectionsAlgebra gK) U''; IsScalarTower K Bu F := hKU''
  intro hx'' ωU'' hωU''
  intro hxX
  let u : (U₀ : Scheme.{u}) ⟶ Spec (CommRingCat.of R) := U₀.ι ≫ pullback.fst z f ≫ z
  let q : (U₀ : Scheme.{u}) ⟶ X := U₀.ι ≫ pullback.snd z f
  have hq : q ≫ f = u := by rw [Category.assoc, ← pullback.condition]
  let pointU : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap K F))) gK := (NeronModelInfra.schemeHomOverComp
    (pointGenericFibre (K := K) (K' := F)
      (⟨(U₀ : Scheme.{u}).fromSpecStalk ηU, halgO⟩ :
        SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap R O))) u))
    (NeronModelInfra.schemeHomOverComp (genericFibreRestrict R K f u ⟨q, hq⟩) e))
  let pointX : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap K F))) gK := (NeronModelInfra.schemeHomOverComp
    (pointGenericFibre (K := K) (K' := F)
      (⟨X.fromSpecStalk ξ, halgX⟩ :
        SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap R X₀))) f)) e)
  let pointZ : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap K K'))) gK := (NeronModelInfra.schemeHomOverComp
    (pointGenericFibre (K := K) (K' := K')
      (⟨Z.fromSpecStalk ζ₀, halgZ⟩ :
        SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap R S))) z)) uK)
  have hxpt :=
    @ConstructionInterface.generic_fibre_stalk_chart_point_fixed
      R rBase K givenK aRK X (U₀ : Scheme.{u}) XK f u q hq ηU gK e
      algRO halgO algRX halgX F fieldOpen.toCommRing
      (inferInstance : Algebra O F) (inferInstance : Algebra X₀ F)
      (inferInstance : Algebra R F) algKF originalROpenField originalRXFTower originalRKOpen
      (inferInstance : IsScalarTower X₀ O F)
  exact @hleft K' F fieldPrime fieldOpen algKK' algK'F algKF originalKKprimeOpen
    pointZ pointU C.U U'' C.hU hU'' algUcF algU'' hKUc hKU''
    (hxX.trans hxpt.symm) (hx''.trans htrans.symm)
    C.ωU ωU'' C.hωU hωU'' 

theorem top_form_image_equality
    {R : Type u} [rBase : CommRing R] [domainBase : IsDomain R] [dvrBase : IsDiscreteValuationRing R]
    (K : Type u) [givenK : Field K] [aRK : Algebra R K] [fractionRK : IsFractionRing R K]
    {XK : Scheme.{u}} {gK : XK ⟶ Spec (CommRingCat.of K)}
    (d : ℕ)
    (ω : Γ((ZInQ.Contrib.CloudR2NeronExistence.Henselian.AlgebraicGeometry.Scheme.Hom.topDifferentials gK) d, ⊤))
    (D : MinimalComponentData R K gK d ω)
    (X : Scheme.{u}) (f : X ⟶ Spec (CommRingCat.of R))
    (Z : Scheme.{u}) (z : Z ⟶ Spec (CommRingCat.of R))
    (T : ComponentReading R K gK d ω)
    (η : ↑(pullback z f)) (U₀ : (pullback z f).Opens) (hηU : η ∈ U₀)
    (v : (U₀ : Scheme.{u}) ⟶ pullback z T.f)
 :
    let ηU : ↥U₀ := ⟨η, hηU⟩;
    let η' : ↥(pullback z T.f) := v.base ηU;
    let ζ₀ : ↥Z := (pullback.fst z T.f).base η';
    letI rOpen : CommRing ((U₀ : Scheme.{u}).presheaf.stalk ηU) := _root_.CommRingCat.commRing ((U₀ : Scheme.{u}).presheaf.stalk ηU);
    letI rPrime : CommRing (Z.presheaf.stalk ζ₀) := _root_.CommRingCat.commRing (Z.presheaf.stalk ζ₀);
    ∀ (hdomO : IsDomain ((U₀ : Scheme.{u}).presheaf.stalk ηU))
      (hdomR' : IsDomain (Z.presheaf.stalk ζ₀)),
    letI : IsDomain ((U₀ : Scheme.{u}).presheaf.stalk ηU) := hdomO;
    letI fieldOpen : Field (FractionRing ((U₀ : Scheme.{u}).presheaf.stalk ηU)) := @FractionRing.field ((U₀ : Scheme.{u}).presheaf.stalk ηU) rOpen hdomO;
    letI : IsDomain (Z.presheaf.stalk ζ₀) := hdomR';
    letI fieldPrime : Field (FractionRing (Z.presheaf.stalk ζ₀)) := @FractionRing.field (Z.presheaf.stalk ζ₀) rPrime hdomR';
    let F := FractionRing ((U₀ : Scheme.{u}).presheaf.stalk ηU);
    let K' := FractionRing (Z.presheaf.stalk ζ₀);
    ∀ (aKF : Algebra K F)
      (aKKprime : Algebra K K')
      (aKprimeF : Algebra K' F),
    letI algKF : Algebra K F := aKF;
    letI algKK' : Algebra K K' := aKKprime;
    letI algK'F : Algebra K' F := aKprimeF;
    ∀ (originalKKprimeOpen : IsScalarTower K K' F),
    letI : IsScalarTower K K' F := originalKKprimeOpen;
    ∀ (c : D.ι),
    letI rComponent : CommRing ((D.C c).Y.presheaf.stalk (D.C c).y) := _root_.CommRingCat.commRing ((D.C c).Y.presheaf.stalk (D.C c).y);
    letI domainComponent : IsDomain ((D.C c).Y.presheaf.stalk (D.C c).y) := (D.C c).isDomain;
    letI fieldComponent : Field (FractionRing ((D.C c).Y.presheaf.stalk (D.C c).y)) := @FractionRing.field ((D.C c).Y.presheaf.stalk (D.C c).y) rComponent domainComponent;
    letI rSections : CommRing Γ(XK, (D.C c).U) := _root_.CommRingCat.commRing Γ(XK, (D.C c).U);
    ∀ (algF₀F : Algebra (FractionRing ((D.C c).Y.presheaf.stalk (D.C c).y)) (FractionRing ((U₀ : Scheme.{u}).presheaf.stalk ηU)))
      (hTowK : letI := (D.C c).algebraK; IsScalarTower K (FractionRing ((D.C c).Y.presheaf.stalk (D.C c).y)) (FractionRing ((U₀ : Scheme.{u}).presheaf.stalk ηU))),
    letI : Algebra R ((D.C c).Y.presheaf.stalk (D.C c).y) := (D.C c).algebra;
    letI : Algebra K (FractionRing ((D.C c).Y.presheaf.stalk (D.C c).y)) := (D.C c).algebraK;
    letI : IsScalarTower R K (FractionRing ((D.C c).Y.presheaf.stalk (D.C c).y)) := (D.C c).isScalarTower;
    letI : Algebra (FractionRing ((D.C c).Y.presheaf.stalk (D.C c).y)) (FractionRing ((U₀ : Scheme.{u}).presheaf.stalk ηU)) := algF₀F;
    letI : letI := (D.C c).algebraK; IsScalarTower K (FractionRing ((D.C c).Y.presheaf.stalk (D.C c).y)) (FractionRing ((U₀ : Scheme.{u}).presheaf.stalk ηU)) := hTowK;
    letI := (ZInQ.Contrib.CloudR2NeronExistence.Henselian.AlgebraicGeometry.Scheme.Hom.sectionsAlgebra gK) (D.C c).U;
    letI := (D.C c).algebraU;
    letI algUcF : Algebra Γ(XK, (D.C c).U) (FractionRing ((U₀ : Scheme.{u}).presheaf.stalk ηU)) :=
      ((algebraMap (FractionRing ((D.C c).Y.presheaf.stalk (D.C c).y)) (FractionRing ((U₀ : Scheme.{u}).presheaf.stalk ηU))).comp (algebraMap Γ(XK, (D.C c).U) (FractionRing ((D.C c).Y.presheaf.stalk (D.C c).y)))).toAlgebra;
    ∀ (hKUc : IsScalarTower K Γ(XK, (D.C c).U) (FractionRing ((U₀ : Scheme.{u}).presheaf.stalk ηU)))
      (towUcF₀F : IsScalarTower Γ(XK, (D.C c).U) (FractionRing ((D.C c).Y.presheaf.stalk (D.C c).y)) (FractionRing ((U₀ : Scheme.{u}).presheaf.stalk ηU))),
    letI : IsScalarTower K Γ(XK, (D.C c).U) (FractionRing ((U₀ : Scheme.{u}).presheaf.stalk ηU)) := hKUc;
    letI : IsScalarTower Γ(XK, (D.C c).U) (FractionRing ((D.C c).Y.presheaf.stalk (D.C c).y)) (FractionRing ((U₀ : Scheme.{u}).presheaf.stalk ηU)) := towUcF₀F;
    letI : IsScalarTower K Γ(XK, (D.C c).U) (FractionRing ((D.C c).Y.presheaf.stalk (D.C c).y)) := (D.C c).isScalarTowerU;
    ∀ (U'' : XK.Opens),
    letI rUSections : CommRing Γ(XK, U'') := _root_.CommRingCat.commRing Γ(XK, U'');
    letI := (ZInQ.Contrib.CloudR2NeronExistence.Henselian.AlgebraicGeometry.Scheme.Hom.sectionsAlgebra gK) U'';
    ∀ (hU'' : IsAffineOpen U'')
      (algU'' : Algebra Γ(XK, U'') (FractionRing ((U₀ : Scheme.{u}).presheaf.stalk ⟨η, hηU⟩))),
    letI : Algebra Γ(XK, U'') (FractionRing ((U₀ : Scheme.{u}).presheaf.stalk ηU)) := algU'';
    ∀ (hKU'' : letI := (ZInQ.Contrib.CloudR2NeronExistence.Henselian.AlgebraicGeometry.Scheme.Hom.sectionsAlgebra gK) U''; IsScalarTower K Γ(XK, U'') (FractionRing ((U₀ : Scheme.{u}).presheaf.stalk ⟨η, hηU⟩))),
    letI : letI := (ZInQ.Contrib.CloudR2NeronExistence.Henselian.AlgebraicGeometry.Scheme.Hom.sectionsAlgebra gK) U''; IsScalarTower K Γ(XK, U'') (FractionRing ((U₀ : Scheme.{u}).presheaf.stalk ⟨η, hηU⟩)) := hKU'';
    ∀ (ωU'' : ⋀[Γ(XK, U'')]^d ((ZInQ.Contrib.CloudR2NeronExistence.Henselian.AlgebraicGeometry.Scheme.Hom.kaehlerPresheaf gK).obj (op U''))),
    ∀ (hleftη : TopFormOrder.topFormMap K K' Γ(XK, U'') F d ωU'' = TopFormOrder.topFormMap K K' Γ(XK, (D.C c).U) F d (D.C c).ωU)
      (h23 : (TopFormOrder.topFormMap K (FractionRing (Z.presheaf.stalk ζ₀)) Γ(XK, (D.C c).U) (FractionRing ((U₀ : Scheme.{u}).presheaf.stalk ηU)) d (D.C c).ωU =
      TopFormOrder.topFormMap K (FractionRing (Z.presheaf.stalk ζ₀)) (FractionRing ((D.C c).Y.presheaf.stalk (D.C c).y)) (FractionRing ((U₀ : Scheme.{u}).presheaf.stalk ηU)) d
        ((D.C c).a • TopFormOrder.topFormMap R K ((D.C c).Y.presheaf.stalk (D.C c).y) (FractionRing ((D.C c).Y.presheaf.stalk (D.C c).y)) d
          (exteriorPower.ιMulti ((D.C c).Y.presheaf.stalk (D.C c).y) d (D.C c).b)))),
    TopFormOrder.topFormMap K K' F F d (TopFormOrder.topFormMap K K Γ(XK, U'') F d ωU'') =
      TopFormOrder.topFormMap K K' (FractionRing ((D.C c).Y.presheaf.stalk (D.C c).y)) F d
        ((D.C c).a • TopFormOrder.topFormMap R K ((D.C c).Y.presheaf.stalk (D.C c).y) (FractionRing ((D.C c).Y.presheaf.stalk (D.C c).y)) d (exteriorPower.ιMulti ((D.C c).Y.presheaf.stalk (D.C c).y) d (D.C c).b)) := by
  classical
  intro ηU η' ζ₀
  let O : Type u := ((U₀ : Scheme.{u}).presheaf.stalk ηU)
  let S : Type u := (Z.presheaf.stalk ζ₀)
  letI rOpen : CommRing O := _root_.CommRingCat.commRing ((U₀ : Scheme.{u}).presheaf.stalk ηU)
  letI rPrime : CommRing S := _root_.CommRingCat.commRing (Z.presheaf.stalk ζ₀)
  intro hdomO hdomR'
  letI : IsDomain O := hdomO
  letI fieldOpen : Field (FractionRing O) := @FractionRing.field O rOpen hdomO
  letI : IsDomain S := hdomR'
  letI fieldPrime : Field (FractionRing S) := @FractionRing.field S rPrime hdomR'
  intro F K'
  intro aKF aKKprime aKprimeF
  letI algKF : Algebra K F := aKF
  letI algKK' : Algebra K K' := aKKprime
  letI algK'F : Algebra K' F := aKprimeF
  intro originalKKprimeOpen
  letI : IsScalarTower K K' F := originalKKprimeOpen
  intro c
  let C : ComponentReading R K gK d ω := D.C c
  let O₀ : Type u := (C.Y.presheaf.stalk C.y)
  let F₀ : Type u := FractionRing O₀
  letI rComponent : CommRing O₀ := _root_.CommRingCat.commRing ((D.C c).Y.presheaf.stalk (D.C c).y)
  letI domainComponent : IsDomain O₀ := C.isDomain
  letI fieldComponent : Field F₀ := @FractionRing.field O₀ rComponent domainComponent
  let Bc : Type u := Γ(XK, C.U)
  letI rSections : CommRing Bc := _root_.CommRingCat.commRing Γ(XK, (D.C c).U)
  intro algF₀F hTowK
  letI : Algebra R O₀ := C.algebra
  letI : Algebra K F₀ := C.algebraK
  letI : IsScalarTower R K F₀ := C.isScalarTower
  letI : Algebra F₀ F := algF₀F
  letI : letI := C.algebraK; IsScalarTower K F₀ F := hTowK
  letI := (ZInQ.Contrib.CloudR2NeronExistence.Henselian.AlgebraicGeometry.Scheme.Hom.sectionsAlgebra gK) C.U
  letI := C.algebraU
  letI algUcF : Algebra Bc F :=
    ((algebraMap F₀ F).comp (algebraMap Bc F₀)).toAlgebra
  intro hKUc towUcF₀F
  letI : IsScalarTower K Bc F := hKUc
  letI : IsScalarTower Bc F₀ F := towUcF₀F
  letI : IsScalarTower K Bc F₀ := C.isScalarTowerU
  intro U''
  let Bu : Type u := Γ(XK, U'')
  letI rUSections : CommRing Bu := _root_.CommRingCat.commRing Γ(XK, U'')
  letI := (ZInQ.Contrib.CloudR2NeronExistence.Henselian.AlgebraicGeometry.Scheme.Hom.sectionsAlgebra gK) U''
  intro hU'' algU''
  letI : Algebra Bu F := algU''
  intro hKU''
  letI : letI := (ZInQ.Contrib.CloudR2NeronExistence.Henselian.AlgebraicGeometry.Scheme.Hom.sectionsAlgebra gK) U''; IsScalarTower K Bu F := hKU''
  intro ωU''
  intro hleftη h23
  let σ := TopFormOrder.topFormMap K K Bu F d ωU''
  let θ := C.a • TopFormOrder.topFormMap R K O₀
    F₀ d
      (exteriorPower.ιMulti O₀ d C.b)
  let V : Type u := (⋀[Bu]^d ((ZInQ.Contrib.CloudR2NeronExistence.Henselian.AlgebraicGeometry.Scheme.Hom.kaehlerPresheaf gK).obj (op U'')))
  let W : Type u := ExteriorAlgebra.exteriorPower F d (KaehlerDifferential K' F)
  let x0 : W := TopFormOrder.topFormMap K K' F F d σ
  let x1 : W := TopFormOrder.topFormMap K K' Bu F d ωU''
  let x2 : W := TopFormOrder.topFormMap K K' Bc F d C.ωU
  let x3 : W := TopFormOrder.topFormMap K K' F₀ F d θ
  let composite : V → W := fun s =>
    TopFormOrder.topFormMap K K' F F d (TopFormOrder.topFormMap K K Bu F d s)
  let direct : V → W := fun s => TopFormOrder.topFormMap K K' Bu F d s
  have hOperator :=
    @ConstructionInterface.section_kaehler_operator_fixed K K' F givenK fieldPrime fieldOpen
      algKK' algKF algK'F originalKKprimeOpen XK gK U'' d algU'' hKU''
  have h01 := ConstructionInterface.fixed_function_evaluation V W
    composite direct hOperator ωU''
  have h12 : x1 = x2 := hleftη
  exact ConstructionInterface.four_endpoint_equality_fixed W x0 x1 x2 x3 h01 h12 h23

theorem image_order_and_bijective_stalk_construction
    {R : Type u} [rBase : CommRing R] [domainBase : IsDomain R] [dvrBase : IsDiscreteValuationRing R]
    (K : Type u) [givenK : Field K] [aRK : Algebra R K] [fractionRK : IsFractionRing R K]
    {XK : Scheme.{u}} {gK : XK ⟶ Spec (CommRingCat.of K)}
    (d : ℕ)
    (ω : Γ((ZInQ.Contrib.CloudR2NeronExistence.Henselian.AlgebraicGeometry.Scheme.Hom.topDifferentials gK) d, ⊤))
    (D : MinimalComponentData R K gK d ω) (hD : D.IsOmegaMinimal)
    (X : Scheme.{u}) (f : X ⟶ Spec (CommRingCat.of R))
    (Z : Scheme.{u}) (z : Z ⟶ Spec (CommRingCat.of R))
    (T : ComponentReading R K gK d ω)
    (η : ↑(pullback z f)) (U₀ : (pullback z f).Opens) (hηU : η ∈ U₀)
    (v : (U₀ : Scheme.{u}) ⟶ pullback z T.f)
 :
    let ηU : ↥U₀ := ⟨η, hηU⟩;
    let η' : ↥(pullback z T.f) := v.base ηU;
    let ζ₀ : ↥Z := (pullback.fst z T.f).base η';
    let y₁ : ↥T.Y := (pullback.snd z T.f).base η';
    letI rOpen : CommRing ((U₀ : Scheme.{u}).presheaf.stalk ηU) := _root_.CommRingCat.commRing ((U₀ : Scheme.{u}).presheaf.stalk ηU);
    letI rPrime : CommRing (Z.presheaf.stalk ζ₀) := _root_.CommRingCat.commRing (Z.presheaf.stalk ζ₀);
    letI rPullback : CommRing ((pullback z T.f).presheaf.stalk η') := _root_.CommRingCat.commRing ((pullback z T.f).presheaf.stalk η');
    letI rAux : CommRing (T.Y.presheaf.stalk y₁) := _root_.CommRingCat.commRing (T.Y.presheaf.stalk y₁);
    letI rXStalk : CommRing (X.presheaf.stalk ((pullback.snd z f).base (U₀.ι.base ηU))) := _root_.CommRingCat.commRing (X.presheaf.stalk ((pullback.snd z f).base (U₀.ι.base ηU)));
    letI algR'O' : Algebra (Z.presheaf.stalk ζ₀) ((pullback z T.f).presheaf.stalk η') := ((pullback.fst z T.f).stalkMap η').hom.toAlgebra;
    letI algO'O : Algebra ((pullback z T.f).presheaf.stalk η') ((U₀ : Scheme.{u}).presheaf.stalk ηU) := (v.stalkMap ηU).hom.toAlgebra;
    letI algR'O : Algebra (Z.presheaf.stalk ζ₀) ((U₀ : Scheme.{u}).presheaf.stalk ηU) :=
      ((v.stalkMap ηU).hom.comp ((pullback.fst z T.f).stalkMap η').hom).toAlgebra;
    letI algRR' : Algebra R (Z.presheaf.stalk ζ₀) := stalkAlgebra z ζ₀;
    letI algRO' : Algebra R ((pullback z T.f).presheaf.stalk η') := ((algebraMap (Z.presheaf.stalk ζ₀) ((pullback z T.f).presheaf.stalk η')).comp (algebraMap R (Z.presheaf.stalk ζ₀))).toAlgebra;
    letI algRO : Algebra R ((U₀ : Scheme.{u}).presheaf.stalk ηU) := ((algebraMap (Z.presheaf.stalk ζ₀) ((U₀ : Scheme.{u}).presheaf.stalk ηU)).comp (algebraMap R (Z.presheaf.stalk ζ₀))).toAlgebra;
    letI algRO₁ : Algebra R (T.Y.presheaf.stalk y₁) := stalkAlgebra T.f y₁;
    letI algO₁O' : Algebra (T.Y.presheaf.stalk y₁) ((pullback z T.f).presheaf.stalk η') := ((pullback.snd z T.f).stalkMap η').hom.toAlgebra;
    letI algO₁O : Algebra (T.Y.presheaf.stalk y₁) ((U₀ : Scheme.{u}).presheaf.stalk ηU) := ((algebraMap ((pullback z T.f).presheaf.stalk η') ((U₀ : Scheme.{u}).presheaf.stalk ηU)).comp (algebraMap (T.Y.presheaf.stalk y₁) ((pullback z T.f).presheaf.stalk η'))).toAlgebra;
    letI algRX : Algebra R (X.presheaf.stalk ((pullback.snd z f).base (U₀.ι.base ηU))) := stalkAlgebra f ((pullback.snd z f).base (U₀.ι.base ηU));
    letI algXO : Algebra (X.presheaf.stalk ((pullback.snd z f).base (U₀.ι.base ηU))) ((U₀ : Scheme.{u}).presheaf.stalk ηU) := ((U₀.ι ≫ pullback.snd z f).stalkMap ηU).hom.toAlgebra;
    ∀ (hdomO : IsDomain ((U₀ : Scheme.{u}).presheaf.stalk ηU))
      (hdomR' : IsDomain (Z.presheaf.stalk ζ₀)),
    letI : IsDomain ((U₀ : Scheme.{u}).presheaf.stalk ηU) := hdomO;
    letI fieldOpen : Field (FractionRing ((U₀ : Scheme.{u}).presheaf.stalk ηU)) := @FractionRing.field ((U₀ : Scheme.{u}).presheaf.stalk ηU) rOpen hdomO;
    letI : IsDomain (Z.presheaf.stalk ζ₀) := hdomR';
    letI fieldPrime : Field (FractionRing (Z.presheaf.stalk ζ₀)) := @FractionRing.field (Z.presheaf.stalk ζ₀) rPrime hdomR';
    let F := FractionRing ((U₀ : Scheme.{u}).presheaf.stalk ηU);
    let K' := FractionRing (Z.presheaf.stalk ζ₀);
    ∀ (hdomO' : IsDomain ((pullback z T.f).presheaf.stalk η'))
      (hdvrO : IsDiscreteValuationRing ((U₀ : Scheme.{u}).presheaf.stalk ηU))
      (hdvrR' : IsDiscreteValuationRing (Z.presheaf.stalk ζ₀))
      (hlocR' : IsLocalHom (algebraMap R (Z.presheaf.stalk ζ₀)))
      (originalPrimeOpenLocal : IsLocalHom (algebraMap (Z.presheaf.stalk ζ₀) ((U₀ : Scheme.{u}).presheaf.stalk ηU))),
    letI : IsDomain ((pullback z T.f).presheaf.stalk η') := hdomO';
    letI : IsDiscreteValuationRing ((U₀ : Scheme.{u}).presheaf.stalk ηU) := hdvrO;
    letI : IsDiscreteValuationRing (Z.presheaf.stalk ζ₀) := hdvrR';
    letI : IsLocalHom (algebraMap R (Z.presheaf.stalk ζ₀)) := hlocR';
    letI : IsLocalHom (algebraMap (Z.presheaf.stalk ζ₀) ((U₀ : Scheme.{u}).presheaf.stalk ηU)) := originalPrimeOpenLocal;
    ∀ (originalPrimePullbackOpen : IsScalarTower (Z.presheaf.stalk ζ₀) ((pullback z T.f).presheaf.stalk η') ((U₀ : Scheme.{u}).presheaf.stalk ηU))
      (originalRPrimePullback : IsScalarTower R (Z.presheaf.stalk ζ₀) ((pullback z T.f).presheaf.stalk η'))
      (originalRPrimeOpen : IsScalarTower R (Z.presheaf.stalk ζ₀) ((U₀ : Scheme.{u}).presheaf.stalk ηU))
      (originalRAuxPullback : IsScalarTower R (T.Y.presheaf.stalk y₁) ((pullback z T.f).presheaf.stalk η'))
      (originalAuxPullbackOpen : IsScalarTower (T.Y.presheaf.stalk y₁) ((pullback z T.f).presheaf.stalk η') ((U₀ : Scheme.{u}).presheaf.stalk ηU))
      (originalRAuxOpen : IsScalarTower R (T.Y.presheaf.stalk y₁) ((U₀ : Scheme.{u}).presheaf.stalk ηU))
      (originalRXOpen : IsScalarTower R (X.presheaf.stalk ((pullback.snd z f).base (U₀.ι.base ηU))) ((U₀ : Scheme.{u}).presheaf.stalk ηU))
      (originalPrimePullbackField : IsScalarTower (Z.presheaf.stalk ζ₀) ((pullback z T.f).presheaf.stalk η') F)
      (originalRAuxField : IsScalarTower R (T.Y.presheaf.stalk y₁) F),
    letI : IsScalarTower (Z.presheaf.stalk ζ₀) ((pullback z T.f).presheaf.stalk η') ((U₀ : Scheme.{u}).presheaf.stalk ηU) := originalPrimePullbackOpen;
    letI : IsScalarTower R (Z.presheaf.stalk ζ₀) ((pullback z T.f).presheaf.stalk η') := originalRPrimePullback;
    letI : IsScalarTower R (Z.presheaf.stalk ζ₀) ((U₀ : Scheme.{u}).presheaf.stalk ηU) := originalRPrimeOpen;
    letI : IsScalarTower R (T.Y.presheaf.stalk y₁) ((pullback z T.f).presheaf.stalk η') := originalRAuxPullback;
    letI : IsScalarTower (T.Y.presheaf.stalk y₁) ((pullback z T.f).presheaf.stalk η') ((U₀ : Scheme.{u}).presheaf.stalk ηU) := originalAuxPullbackOpen;
    letI : IsScalarTower R (T.Y.presheaf.stalk y₁) ((U₀ : Scheme.{u}).presheaf.stalk ηU) := originalRAuxOpen;
    letI : IsScalarTower R (X.presheaf.stalk ((pullback.snd z f).base (U₀.ι.base ηU))) ((U₀ : Scheme.{u}).presheaf.stalk ηU) := originalRXOpen;
    letI : IsScalarTower (Z.presheaf.stalk ζ₀) ((pullback z T.f).presheaf.stalk η') F := originalPrimePullbackField;
    letI : IsScalarTower R (T.Y.presheaf.stalk y₁) F := originalRAuxField;
    ∀ (hRR'_map : Ideal.map (algebraMap R (Z.presheaf.stalk ζ₀)) (IsLocalRing.maximalIdeal R) = IsLocalRing.maximalIdeal (Z.presheaf.stalk ζ₀))
      (hO : Ideal.map (algebraMap (Z.presheaf.stalk ζ₀) ((U₀ : Scheme.{u}).presheaf.stalk ηU)) (IsLocalRing.maximalIdeal (Z.presheaf.stalk ζ₀)) = IsLocalRing.maximalIdeal ((U₀ : Scheme.{u}).presheaf.stalk ηU))
      (ϖ : R)
      (hϖ : IsLocalRing.maximalIdeal R = Ideal.span {ϖ}),
    ∀ (aKF : Algebra K F)
      (aKKprime : Algebra K K')
      (aKprimeF : Algebra K' F),
    letI algKF : Algebra K F := aKF;
    letI algKK' : Algebra K K' := aKKprime;
    letI algK'F : Algebra K' F := aKprimeF;
    ∀ (originalRKKprime : IsScalarTower R K K')
      (originalPrimeFractionField : IsScalarTower (Z.presheaf.stalk ζ₀) K' F)
      (originalRKOpen : IsScalarTower R K F)
      (originalKKprimeOpen : IsScalarTower K K' F),
    letI : IsScalarTower R K K' := originalRKKprime;
    letI : IsScalarTower (Z.presheaf.stalk ζ₀) K' F := originalPrimeFractionField;
    letI : IsScalarTower R K F := originalRKOpen;
    letI : IsScalarTower K K' F := originalKKprimeOpen;
    ∀ (hbc' : Function.Bijective
        ((KaehlerDifferential.map R (Z.presheaf.stalk ζ₀) ((pullback z T.f).presheaf.stalk η')
          ((pullback z T.f).presheaf.stalk η')).restrictScalars ((pullback z T.f).presheaf.stalk η') ∘ₗ
            KaehlerDifferential.mapBaseChange R (T.Y.presheaf.stalk y₁) ((pullback z T.f).presheaf.stalk η')))
      (originalPullbackFraction : IsFractionRing ((pullback z T.f).presheaf.stalk η') F),
    letI : IsFractionRing ((pullback z T.f).presheaf.stalk η') F := originalPullbackFraction;
    ∀ (c : D.ι),
    letI rComponent : CommRing ((D.C c).Y.presheaf.stalk (D.C c).y) := _root_.CommRingCat.commRing ((D.C c).Y.presheaf.stalk (D.C c).y);
    letI domainComponent : IsDomain ((D.C c).Y.presheaf.stalk (D.C c).y) := (D.C c).isDomain;
    letI fieldComponent : Field (FractionRing ((D.C c).Y.presheaf.stalk (D.C c).y)) := @FractionRing.field ((D.C c).Y.presheaf.stalk (D.C c).y) rComponent domainComponent;
    ∀ (φ : ((D.C c).Y.presheaf.stalk (D.C c).y) →+* (X.presheaf.stalk ((pullback.snd z f).base (U₀.ι.base ηU))))
      (algF₀F : Algebra (FractionRing ((D.C c).Y.presheaf.stalk (D.C c).y)) (FractionRing ((U₀ : Scheme.{u}).presheaf.stalk ηU)))
      (hTowK : letI := (D.C c).algebraK; IsScalarTower K (FractionRing ((D.C c).Y.presheaf.stalk (D.C c).y)) (FractionRing ((U₀ : Scheme.{u}).presheaf.stalk ηU))),
    letI : Algebra R ((D.C c).Y.presheaf.stalk (D.C c).y) := (D.C c).algebra;
    letI : Algebra K (FractionRing ((D.C c).Y.presheaf.stalk (D.C c).y)) := (D.C c).algebraK;
    letI : IsScalarTower R K (FractionRing ((D.C c).Y.presheaf.stalk (D.C c).y)) := (D.C c).isScalarTower;
    letI : Algebra (FractionRing ((D.C c).Y.presheaf.stalk (D.C c).y)) (FractionRing ((U₀ : Scheme.{u}).presheaf.stalk ηU)) := algF₀F;
    letI : letI := (D.C c).algebraK; IsScalarTower K (FractionRing ((D.C c).Y.presheaf.stalk (D.C c).y)) (FractionRing ((U₀ : Scheme.{u}).presheaf.stalk ηU)) := hTowK;
    letI algO₀O : Algebra ((D.C c).Y.presheaf.stalk (D.C c).y) ((U₀ : Scheme.{u}).presheaf.stalk ηU) := ((algebraMap (X.presheaf.stalk ((pullback.snd z f).base (U₀.ι.base ηU))) ((U₀ : Scheme.{u}).presheaf.stalk ηU)).comp φ).toAlgebra;
    ∀ (originalComponentFractionOpen : IsScalarTower ((D.C c).Y.presheaf.stalk (D.C c).y) (FractionRing ((D.C c).Y.presheaf.stalk (D.C c).y)) (FractionRing ((U₀ : Scheme.{u}).presheaf.stalk ηU)))
      (originalRComponentOpen : IsScalarTower R ((D.C c).Y.presheaf.stalk (D.C c).y) ((U₀ : Scheme.{u}).presheaf.stalk ηU))
      (originalRComponentField : IsScalarTower R ((D.C c).Y.presheaf.stalk (D.C c).y) (FractionRing ((U₀ : Scheme.{u}).presheaf.stalk ηU)))
      (originalComponentOpenLocal : IsLocalHom (algebraMap ((D.C c).Y.presheaf.stalk (D.C c).y) ((U₀ : Scheme.{u}).presheaf.stalk ηU)))
      (hdomO₀ : IsDomain ((D.C c).Y.presheaf.stalk (D.C c).y))
      (hdvrO₀ : IsDiscreteValuationRing ((D.C c).Y.presheaf.stalk (D.C c).y))
      (hlocO₀ : IsLocalHom (algebraMap R ((D.C c).Y.presheaf.stalk (D.C c).y)))
      (hidxO₀ : IsIndexOneExtension R ((D.C c).Y.presheaf.stalk (D.C c).y)),
    letI : IsScalarTower ((D.C c).Y.presheaf.stalk (D.C c).y) (FractionRing ((D.C c).Y.presheaf.stalk (D.C c).y)) (FractionRing ((U₀ : Scheme.{u}).presheaf.stalk ηU)) := originalComponentFractionOpen;
    letI : IsScalarTower R ((D.C c).Y.presheaf.stalk (D.C c).y) ((U₀ : Scheme.{u}).presheaf.stalk ηU) := originalRComponentOpen;
    letI : IsScalarTower R ((D.C c).Y.presheaf.stalk (D.C c).y) (FractionRing ((U₀ : Scheme.{u}).presheaf.stalk ηU)) := originalRComponentField;
    letI : IsLocalHom (algebraMap ((D.C c).Y.presheaf.stalk (D.C c).y) ((U₀ : Scheme.{u}).presheaf.stalk ηU)) := originalComponentOpenLocal;
    letI : IsLocalHom (algebraMap R ((D.C c).Y.presheaf.stalk (D.C c).y)) := hlocO₀;
    ∀ (hbc : Function.Bijective
      ((KaehlerDifferential.map R (Z.presheaf.stalk ζ₀) ((U₀ : Scheme.{u}).presheaf.stalk ηU) ((U₀ : Scheme.{u}).presheaf.stalk ηU)).restrictScalars ((U₀ : Scheme.{u}).presheaf.stalk ηU) ∘ₗ
        KaehlerDifferential.mapBaseChange R ((D.C c).Y.presheaf.stalk (D.C c).y) ((U₀ : Scheme.{u}).presheaf.stalk ηU))),
    ∀ (U'' : XK.Opens),
    letI rUSections : CommRing Γ(XK, U'') := _root_.CommRingCat.commRing Γ(XK, U'');
    letI := (ZInQ.Contrib.CloudR2NeronExistence.Henselian.AlgebraicGeometry.Scheme.Hom.sectionsAlgebra gK) U'';
    ∀ (hU'' : IsAffineOpen U'')
      (algU'' : Algebra Γ(XK, U'') (FractionRing ((U₀ : Scheme.{u}).presheaf.stalk ⟨η, hηU⟩))),
    letI : Algebra Γ(XK, U'') (FractionRing ((U₀ : Scheme.{u}).presheaf.stalk ηU)) := algU'';
    ∀ (hKU'' : letI := (ZInQ.Contrib.CloudR2NeronExistence.Henselian.AlgebraicGeometry.Scheme.Hom.sectionsAlgebra gK) U''; IsScalarTower K Γ(XK, U'') (FractionRing ((U₀ : Scheme.{u}).presheaf.stalk ⟨η, hηU⟩))),
    letI : letI := (ZInQ.Contrib.CloudR2NeronExistence.Henselian.AlgebraicGeometry.Scheme.Hom.sectionsAlgebra gK) U''; IsScalarTower K Γ(XK, U'') (FractionRing ((U₀ : Scheme.{u}).presheaf.stalk ⟨η, hηU⟩)) := hKU'';
    ∀ (ωU'' : ⋀[Γ(XK, U'')]^d ((ZInQ.Contrib.CloudR2NeronExistence.Henselian.AlgebraicGeometry.Scheme.Hom.kaehlerPresheaf gK).obj (op U''))),
    ∀ (b₁ : Module.Basis (Fin d) (T.Y.presheaf.stalk ((pullback.snd z T.f).base (v.base ⟨η, hηU⟩))) (Ω[(T.Y.presheaf.stalk ((pullback.snd z T.f).base (v.base ⟨η, hηU⟩)))⁄R]))
      (w₁ : (T.Y.presheaf.stalk ((pullback.snd z T.f).base (v.base ⟨η, hηU⟩)))ˣ)
      (hread : letI := (ZInQ.Contrib.CloudR2NeronExistence.Henselian.AlgebraicGeometry.Scheme.Hom.sectionsAlgebra gK) U''
      TopFormOrder.topFormMap K K Γ(XK, U'') (FractionRing ((U₀ : Scheme.{u}).presheaf.stalk ⟨η, hηU⟩)) d ωU'' =
        (algebraMap (T.Y.presheaf.stalk ((pullback.snd z T.f).base (v.base ⟨η, hηU⟩))) (FractionRing ((U₀ : Scheme.{u}).presheaf.stalk ⟨η, hηU⟩)) (w₁ : (T.Y.presheaf.stalk ((pullback.snd z T.f).base (v.base ⟨η, hηU⟩)))) *
            algebraMap (T.Y.presheaf.stalk ((pullback.snd z T.f).base (v.base ⟨η, hηU⟩))) (FractionRing ((U₀ : Scheme.{u}).presheaf.stalk ⟨η, hηU⟩)) (algebraMap R (T.Y.presheaf.stalk ((pullback.snd z T.f).base (v.base ⟨η, hηU⟩))) ϖ) ^ T.n) •
          TopFormOrder.topFormMap R K (T.Y.presheaf.stalk ((pullback.snd z T.f).base (v.base ⟨η, hηU⟩))) (FractionRing ((U₀ : Scheme.{u}).presheaf.stalk ⟨η, hηU⟩)) d
            (exteriorPower.ιMulti (T.Y.presheaf.stalk ((pullback.snd z T.f).base (v.base ⟨η, hηU⟩))) d b₁)),
    ∀ (hX : TopFormOrder.topFormMap K K' F F d (TopFormOrder.topFormMap K K Γ(XK, U'') F d ωU'') =
      TopFormOrder.topFormMap K K' (FractionRing ((D.C c).Y.presheaf.stalk (D.C c).y)) F d
        ((D.C c).a • TopFormOrder.topFormMap R K ((D.C c).Y.presheaf.stalk (D.C c).y) (FractionRing ((D.C c).Y.presheaf.stalk (D.C c).y)) d (exteriorPower.ιMulti ((D.C c).Y.presheaf.stalk (D.C c).y) d (D.C c).b))),
    (∃ c : D.ι, T.n = (D.C c).n) ∧
      Function.Bijective (KaehlerDifferential.mapBaseChange (Z.presheaf.stalk ζ₀)
        ((pullback z T.f).presheaf.stalk η') ((U₀ : Scheme.{u}).presheaf.stalk ηU)) := by
  classical
  intro ηU η' ζ₀ y₁
  let O : Type u := ((U₀ : Scheme.{u}).presheaf.stalk ηU)
  let S : Type u := (Z.presheaf.stalk ζ₀)
  let P : Type u := ((pullback z T.f).presheaf.stalk η')
  let A : Type u := (T.Y.presheaf.stalk y₁)
  let ξ : ↥X := ((pullback.snd z f).base (U₀.ι.base ηU))
  let X₀ : Type u := X.presheaf.stalk ξ
  letI rOpen : CommRing O := _root_.CommRingCat.commRing ((U₀ : Scheme.{u}).presheaf.stalk ηU)
  letI rPrime : CommRing S := _root_.CommRingCat.commRing (Z.presheaf.stalk ζ₀)
  letI rPullback : CommRing P := _root_.CommRingCat.commRing ((pullback z T.f).presheaf.stalk η')
  letI rAux : CommRing A := _root_.CommRingCat.commRing (T.Y.presheaf.stalk y₁)
  letI rXStalk : CommRing X₀ := _root_.CommRingCat.commRing (X.presheaf.stalk ((pullback.snd z f).base (U₀.ι.base ηU)))
  let δP : P →+* O := (v.stalkMap ηU).hom
  let δS : S →+* P := ((pullback.fst z T.f).stalkMap η').hom
  let δA : A →+* P := ((pullback.snd z T.f).stalkMap η').hom
  let δX : X₀ →+* O := ((U₀.ι ≫ pullback.snd z f).stalkMap ηU).hom
  letI algR'O' : Algebra S P := δS.toAlgebra
  letI algO'O : Algebra P O := δP.toAlgebra
  letI algR'O : Algebra S O :=
    (δP.comp δS).toAlgebra
  letI algRR' : Algebra R S := stalkAlgebra z ζ₀
  letI algRO' : Algebra R P := ((algebraMap S P).comp (algebraMap R S)).toAlgebra
  letI algRO : Algebra R O := ((algebraMap S O).comp (algebraMap R S)).toAlgebra
  letI algRO₁ : Algebra R A := stalkAlgebra T.f y₁
  letI algO₁O' : Algebra A P := δA.toAlgebra
  letI algO₁O : Algebra A O := ((algebraMap P O).comp (algebraMap A P)).toAlgebra
  letI algRX : Algebra R X₀ := stalkAlgebra f ξ
  letI algXO : Algebra X₀ O := δX.toAlgebra
  intro hdomO hdomR'
  letI : IsDomain O := hdomO
  letI fieldOpen : Field (FractionRing O) := @FractionRing.field O rOpen hdomO
  letI : IsDomain S := hdomR'
  letI fieldPrime : Field (FractionRing S) := @FractionRing.field S rPrime hdomR'
  intro F K'
  intro hdomO' hdvrO hdvrR' hlocR' originalPrimeOpenLocal
  letI : IsDomain P := hdomO'
  letI : IsDiscreteValuationRing O := hdvrO
  letI : IsDiscreteValuationRing S := hdvrR'
  letI : IsLocalHom (algebraMap R S) := hlocR'
  letI : IsLocalHom (algebraMap S O) := originalPrimeOpenLocal
  intro originalPrimePullbackOpen originalRPrimePullback originalRPrimeOpen originalRAuxPullback originalAuxPullbackOpen originalRAuxOpen originalRXOpen originalPrimePullbackField originalRAuxField
  letI : IsScalarTower S P O := originalPrimePullbackOpen
  letI : IsScalarTower R S P := originalRPrimePullback
  letI : IsScalarTower R S O := originalRPrimeOpen
  letI : IsScalarTower R A P := originalRAuxPullback
  letI : IsScalarTower A P O := originalAuxPullbackOpen
  letI : IsScalarTower R A O := originalRAuxOpen
  letI : IsScalarTower R X₀ O := originalRXOpen
  letI : IsScalarTower S P F := originalPrimePullbackField
  letI : IsScalarTower R A F := originalRAuxField
  intro hRR'_map hO ϖ hϖ
  intro aKF aKKprime aKprimeF
  letI algKF : Algebra K F := aKF
  letI algKK' : Algebra K K' := aKKprime
  letI algK'F : Algebra K' F := aKprimeF
  intro originalRKKprime originalPrimeFractionField originalRKOpen originalKKprimeOpen
  letI : IsScalarTower R K K' := originalRKKprime
  letI : IsScalarTower S K' F := originalPrimeFractionField
  letI : IsScalarTower R K F := originalRKOpen
  letI : IsScalarTower K K' F := originalKKprimeOpen
  intro hbc' originalPullbackFraction
  letI : IsFractionRing P F := originalPullbackFraction
  intro c
  let C : ComponentReading R K gK d ω := D.C c
  let O₀ : Type u := (C.Y.presheaf.stalk C.y)
  let F₀ : Type u := FractionRing O₀
  letI rComponent : CommRing O₀ := _root_.CommRingCat.commRing ((D.C c).Y.presheaf.stalk (D.C c).y)
  letI domainComponent : IsDomain O₀ := C.isDomain
  letI fieldComponent : Field F₀ := @FractionRing.field O₀ rComponent domainComponent
  intro φ algF₀F hTowK
  letI : Algebra R O₀ := C.algebra
  letI : Algebra K F₀ := C.algebraK
  letI : IsScalarTower R K F₀ := C.isScalarTower
  letI : Algebra F₀ F := algF₀F
  letI : letI := C.algebraK; IsScalarTower K F₀ F := hTowK
  letI algO₀O : Algebra O₀ O := ((algebraMap X₀ O).comp φ).toAlgebra
  intro originalComponentFractionOpen originalRComponentOpen originalRComponentField originalComponentOpenLocal hdomO₀ hdvrO₀ hlocO₀ hidxO₀
  letI : IsScalarTower O₀ F₀ F := originalComponentFractionOpen
  letI : IsScalarTower R O₀ O := originalRComponentOpen
  letI : IsScalarTower R O₀ F := originalRComponentField
  letI : IsLocalHom (algebraMap O₀ O) := originalComponentOpenLocal
  letI : IsLocalHom (algebraMap R O₀) := hlocO₀
  intro hbc
  intro U''
  let Bu : Type u := Γ(XK, U'')
  letI rUSections : CommRing Bu := _root_.CommRingCat.commRing Γ(XK, U'')
  letI := (ZInQ.Contrib.CloudR2NeronExistence.Henselian.AlgebraicGeometry.Scheme.Hom.sectionsAlgebra gK) U''
  intro hU'' algU''
  letI : Algebra Bu F := algU''
  intro hKU''
  letI : letI := (ZInQ.Contrib.CloudR2NeronExistence.Henselian.AlgebraicGeometry.Scheme.Hom.sectionsAlgebra gK) U''; IsScalarTower K Bu F := hKU''
  intro ωU''
  intro b₁ w₁ hread
  intro hX
  let σ := TopFormOrder.topFormMap K K Bu F d ωU''
  have hmin := @ConstructionInterface.minimality_order_bound_fixed R K rBase domainBase dvrBase givenK aRK XK gK d ω D hD c T
  have finish_order := ConstructionInterface.canonical_fraction_prefix_fixed R K S
    (O₀ := O₀)
    (O₁ := A) (O' := P)
    (O := O)
    (rBase := rBase) (rPrimeBase := rPrime)
    (givenK := givenK) (aRK := aRK)
    (domainR := domainBase) (dvrR := dvrBase)
    (fractionRK := fractionRK)
    (domainPrime := hdomR') (dvrPrime := hdvrR') (algBasePrime := algRR') (localBasePrime := hlocR')
    (aKKprime := algKK') (towerRKKprime := originalRKKprime)
    (rComponent := rComponent)
    (domainComponent := hdomO₀) (dvrComponent := hdvrO₀)
    (aRComponent := C.algebra) (localBaseComponent := hlocO₀)
    (aKComponent := C.algebraK) (towerRKComponent := C.isScalarTower)
    (rAux := rAux) (aRAux := algRO₁)
    (rPullback := rPullback)
    (domainPullback := hdomO') (aPrimePullback := algR'O') (aAuxPullback := algO₁O') (aRPullback := algRO')
    (towerRAuxPullback := originalRAuxPullback) (towerRPrimePullback := originalRPrimePullback)
    (rOpen := rOpen)
    (domainOpen := hdomO) (dvrOpen := hdvrO) (aPrimeOpen := algR'O) (localPrimeOpen := originalPrimeOpenLocal)
    (aROpen := algRO) (towerRPrimeOpen := originalRPrimeOpen)
    (aComponentOpen := algO₀O) (localComponentOpen := originalComponentOpenLocal)
    (towerRComponentOpen := originalRComponentOpen) (aPullbackOpen := algO'O)
    (towerPrimePullbackOpen := originalPrimePullbackOpen) (aAuxOpen := algO₁O)
    (towerAuxPullbackOpen := originalAuxPullbackOpen) (towerRAuxOpen := originalRAuxOpen)
    (fractionPullback := originalPullbackFraction) (aPrimeFieldOpen := algK'F)
    (towerPrimePullbackField := originalPrimePullbackField) (towerPrimeFractionField := originalPrimeFractionField)
    (aKOpen := algKF) (towerRKOpen := originalRKOpen) (towerKKprimeOpen := originalKKprimeOpen)
    (aComponentFieldOpen := algF₀F) (towerComponentFractionOpen := originalComponentFractionOpen)
    (towerKComponentOpen := hTowK) (towerRAuxField := originalRAuxField)
    (ϖ := ϖ) (hϖ := hϖ) (hO₀ := hidxO₀.map_maximalIdeal) (d := d)
    (b₀ := C.b) (a := C.a) (ha := C.ha0)
    (b₁ := b₁) (w₁ := w₁) (m := T.n) (hbc' := hbc') (hO := hO) (hbc := hbc)
  have finish_read := finish_order (σ) hread
  have finish_compare := finish_read hX
  have finish_min := finish_compare hmin
  have hsq := finish_min hRR'_map
  exact ⟨⟨c, hsq.1⟩, hsq.2⟩

end P2MW.S_NeronModelInfra_exists_n_eq_and_formallySmooth_stalk_of_isOmegaMinimal_of_genericFibreRestrict_comp_eq_mul
end ZInQ.Contrib.CloudR2NeronExistence.Henselian
