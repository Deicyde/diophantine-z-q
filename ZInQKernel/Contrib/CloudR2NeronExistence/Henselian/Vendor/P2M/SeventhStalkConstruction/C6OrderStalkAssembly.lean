import ZInQKernel.Contrib.CloudR2NeronExistence.Henselian.Vendor.P2M.SeventhStalkConstruction.Prelude
import ZInQKernel.Contrib.CloudR2NeronExistence.Henselian.Vendor.P2M.SeventhStalkConstruction.C5ImageConstruction


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

theorem paired_stalk_front_outputs
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
    ∀ (hfrac : letI : Algebra ((pullback z T.f).presheaf.stalk η') (FractionRing ((U₀ : Scheme.{u}).presheaf.stalk ηU)) :=
        ((algebraMap ((U₀ : Scheme.{u}).presheaf.stalk ηU) (FractionRing ((U₀ : Scheme.{u}).presheaf.stalk ηU))).comp (v.stalkMap ηU).hom).toAlgebra;
        IsFractionRing ((pullback z T.f).presheaf.stalk η') (FractionRing ((U₀ : Scheme.{u}).presheaf.stalk ηU))),
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
    letI originalRPrimeFractionCaptured := originalRPrimeFraction;
    letI originalROpenFieldCaptured := originalROpenField;
    letI originalRKOpenCaptured := originalRKOpen;
    letI originalRKKprimeCaptured := originalRKKprime;
    letI originalKKprimeOpenCaptured := originalKKprimeOpen;
    ∀ (originalRAuxField : IsScalarTower R (T.Y.presheaf.stalk y₁) F)
      (originalRXFTower : IsScalarTower R (X.presheaf.stalk ((pullback.snd z f).base (U₀.ι.base ηU))) F),
    letI originalRAuxFieldCaptured := originalRAuxField;
    letI originalRXFTowerCaptured := originalRXFTower;
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
    letI hTowKCaptured := hTowK;
    letI := (ZInQ.Contrib.CloudR2NeronExistence.Henselian.AlgebraicGeometry.Scheme.Hom.sectionsAlgebra gK) (D.C c).U;
    letI := (D.C c).algebraU;
    letI algUcF : Algebra Γ(XK, (D.C c).U) (FractionRing ((U₀ : Scheme.{u}).presheaf.stalk ηU)) :=
      ((algebraMap (FractionRing ((D.C c).Y.presheaf.stalk (D.C c).y)) (FractionRing ((U₀ : Scheme.{u}).presheaf.stalk ηU))).comp (algebraMap Γ(XK, (D.C c).U) (FractionRing ((D.C c).Y.presheaf.stalk (D.C c).y)))).toAlgebra;
    ∀ (hKUc : IsScalarTower K Γ(XK, (D.C c).U) (FractionRing ((U₀ : Scheme.{u}).presheaf.stalk ηU))),
    letI hKUcCaptured := hKUc;
    ∀ (U'' : XK.Opens),
    letI rUSections : CommRing Γ(XK, U'') := _root_.CommRingCat.commRing Γ(XK, U'');
    letI := (ZInQ.Contrib.CloudR2NeronExistence.Henselian.AlgebraicGeometry.Scheme.Hom.sectionsAlgebra gK) U'';
    ∀ (hU'' : IsAffineOpen U'')
      (algU'' : Algebra Γ(XK, U'') (FractionRing ((U₀ : Scheme.{u}).presheaf.stalk ⟨η, hηU⟩))),
    letI : Algebra Γ(XK, U'') (FractionRing ((U₀ : Scheme.{u}).presheaf.stalk ηU)) := algU'';
    ∀ (hKU'' : letI := (ZInQ.Contrib.CloudR2NeronExistence.Henselian.AlgebraicGeometry.Scheme.Hom.sectionsAlgebra gK) U''; IsScalarTower K Γ(XK, U'') (FractionRing ((U₀ : Scheme.{u}).presheaf.stalk ⟨η, hηU⟩))),
    letI hKU''Captured := hKU'';
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
    (IsFractionRing ((pullback z T.f).presheaf.stalk η') F) ∧
      (TopFormOrder.topFormMap K K' Γ(XK, U'') F d ωU'' = TopFormOrder.topFormMap K K' Γ(XK, (D.C c).U) F d (D.C c).ωU) := by
  classical
  intro ηU η' ζ₀ y₁
  let OObj := ((U₀ : Scheme.{u}).presheaf.stalk ηU)
  let SObj := (Z.presheaf.stalk ζ₀)
  let PObj := ((pullback z T.f).presheaf.stalk η')
  let AObj := (T.Y.presheaf.stalk y₁)
  let ξ : ↥X := ((pullback.snd z f).base (U₀.ι.base ηU))
  let XObj := X.presheaf.stalk ξ
  let O : Type u := OObj
  let S : Type u := SObj
  let P : Type u := PObj
  let A : Type u := AObj
  let X₀ : Type u := XObj
  letI rOpen : CommRing O := _root_.CommRingCat.commRing OObj
  letI rPrime : CommRing S := _root_.CommRingCat.commRing SObj
  letI rPullback : CommRing P := _root_.CommRingCat.commRing PObj
  letI rAux : CommRing A := _root_.CommRingCat.commRing AObj
  letI rXStalk : CommRing X₀ := _root_.CommRingCat.commRing XObj
  let δP : P →+* O := (v.stalkMap ηU).hom
  let δS : S →+* P := ((pullback.fst z T.f).stalkMap η').hom
  let δA : A →+* P := ((pullback.snd z T.f).stalkMap η').hom
  let δX : X₀ →+* O := ((U₀.ι ≫ pullback.snd z f).stalkMap ηU).hom
  letI algR'O' : Algebra S P := δS.toAlgebra
  letI algO'O : Algebra P O := δP.toAlgebra
  letI algR'O : Algebra S O := (δP.comp δS).toAlgebra

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
  intro hfrac
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
  let O₀Obj := C.Y.presheaf.stalk C.y
  let O₀ : Type u := O₀Obj
  letI rComponent : CommRing O₀ := _root_.CommRingCat.commRing O₀Obj
  letI domainComponent : IsDomain O₀ := C.isDomain
  let F₀ : Type u := FractionRing O₀
  letI fieldComponent : Field F₀ := @FractionRing.field O₀ rComponent domainComponent
  let BcObj := Γ(XK, C.U)
  let Bc : Type u := BcObj
  letI rSections : CommRing Bc := _root_.CommRingCat.commRing BcObj
  intro algF₀F hTowK
  letI : Algebra R O₀ := C.algebra
  letI : Algebra K F₀ := C.algebraK
  letI : IsScalarTower R K F₀ := C.isScalarTower
  letI : Algebra F₀ F := algF₀F
  letI : letI := C.algebraK; IsScalarTower K F₀ F := hTowK
  letI := (ZInQ.Contrib.CloudR2NeronExistence.Henselian.AlgebraicGeometry.Scheme.Hom.sectionsAlgebra gK) C.U
  letI := C.algebraU
  letI algUcF : Algebra Bc F := ((algebraMap F₀ F).comp (algebraMap Bc F₀)).toAlgebra
  intro hKUc
  letI : IsScalarTower K Bc F := hKUc
  letI : IsScalarTower K Bc F₀ := C.isScalarTowerU
  intro U''
  let BuObj := Γ(XK, U'')
  let Bu : Type u := BuObj
  letI rUSections : CommRing Bu := _root_.CommRingCat.commRing BuObj
  letI := (ZInQ.Contrib.CloudR2NeronExistence.Henselian.AlgebraicGeometry.Scheme.Hom.sectionsAlgebra gK) U''
  intro hU'' algU''
  letI : Algebra Bu F := algU''
  intro hKU''
  letI : letI := (ZInQ.Contrib.CloudR2NeronExistence.Henselian.AlgebraicGeometry.Scheme.Hom.sectionsAlgebra gK) U''; IsScalarTower K Bu F := hKU''
  intro hx'' ωU'' hωU''
  intro hxX
  have fractionPredicate :=
    @original_pullback_fraction_predicate
      R rBase domainBase dvrBase K givenK aRK fractionRK XK gK d ω
      X f Z z T η U₀ hηU v hdomO hfrac
  letI : IsFractionRing P F := fractionPredicate
  have leftFormEquality :=
    @stalk_chart_left_form_equality
      R rBase domainBase dvrBase K givenK aRK fractionRK XK gK d ω
      LXK hleft D X f e Z z uK T η U₀ hηU v hv₁
      hdomO hdomR' aKF aKKprime aKprimeF
      originalRPrimeFraction originalROpenField originalRKOpen originalRKKprime originalKKprimeOpen
      originalRAuxField originalRXFTower halgZ halgO halg₁ halgX htrans
      c algF₀F hTowK hKUc U'' hU'' algU'' hKU'' hx'' ωU'' hωU'' hxX
  exact ⟨fractionPredicate, leftFormEquality⟩


theorem paired_stalk_construction_outputs
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
    letI originalPrimePullbackOpenCaptured := originalPrimePullbackOpen;
    letI originalRPrimePullbackCaptured := originalRPrimePullback;
    letI originalRPrimeOpenCaptured := originalRPrimeOpen;
    letI originalRAuxPullbackCaptured := originalRAuxPullback;
    letI originalAuxPullbackOpenCaptured := originalAuxPullbackOpen;
    letI originalRAuxOpenCaptured := originalRAuxOpen;
    letI originalRXOpenCaptured := originalRXOpen;
    letI originalPrimePullbackFieldCaptured := originalPrimePullbackField;
    letI originalRAuxFieldCaptured := originalRAuxField;
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
    letI originalRKKprimeCaptured := originalRKKprime;
    letI originalPrimeFractionFieldCaptured := originalPrimeFractionField;
    letI originalRKOpenCaptured := originalRKOpen;
    letI originalKKprimeOpenCaptured := originalKKprimeOpen;
    ∀ (hbc' : Function.Bijective
        ((KaehlerDifferential.map R (Z.presheaf.stalk ζ₀) ((pullback z T.f).presheaf.stalk η')
          ((pullback z T.f).presheaf.stalk η')).restrictScalars ((pullback z T.f).presheaf.stalk η') ∘ₗ
            KaehlerDifferential.mapBaseChange R (T.Y.presheaf.stalk y₁) ((pullback z T.f).presheaf.stalk η'))),
    ∀ (c : D.ι),
    letI rComponent : CommRing ((D.C c).Y.presheaf.stalk (D.C c).y) := _root_.CommRingCat.commRing ((D.C c).Y.presheaf.stalk (D.C c).y);
    letI domainComponent : IsDomain ((D.C c).Y.presheaf.stalk (D.C c).y) := (D.C c).isDomain;
    letI fieldComponent : Field (FractionRing ((D.C c).Y.presheaf.stalk (D.C c).y)) := @FractionRing.field ((D.C c).Y.presheaf.stalk (D.C c).y) rComponent domainComponent;
    letI rSections : CommRing Γ(XK, (D.C c).U) := _root_.CommRingCat.commRing Γ(XK, (D.C c).U);
    ∀ (φ : ((D.C c).Y.presheaf.stalk (D.C c).y) →+* (X.presheaf.stalk ((pullback.snd z f).base (U₀.ι.base ηU))))
      (algF₀F : Algebra (FractionRing ((D.C c).Y.presheaf.stalk (D.C c).y)) (FractionRing ((U₀ : Scheme.{u}).presheaf.stalk ηU)))
      (hTowK : letI := (D.C c).algebraK; IsScalarTower K (FractionRing ((D.C c).Y.presheaf.stalk (D.C c).y)) (FractionRing ((U₀ : Scheme.{u}).presheaf.stalk ηU))),
    letI : Algebra R ((D.C c).Y.presheaf.stalk (D.C c).y) := (D.C c).algebra;
    letI : Algebra K (FractionRing ((D.C c).Y.presheaf.stalk (D.C c).y)) := (D.C c).algebraK;
    letI : IsScalarTower R K (FractionRing ((D.C c).Y.presheaf.stalk (D.C c).y)) := (D.C c).isScalarTower;
    letI : Algebra (FractionRing ((D.C c).Y.presheaf.stalk (D.C c).y)) (FractionRing ((U₀ : Scheme.{u}).presheaf.stalk ηU)) := algF₀F;
    letI hTowKCaptured := hTowK;
    letI algO₀O : Algebra ((D.C c).Y.presheaf.stalk (D.C c).y) ((U₀ : Scheme.{u}).presheaf.stalk ηU) := ((algebraMap (X.presheaf.stalk ((pullback.snd z f).base (U₀.ι.base ηU))) ((U₀ : Scheme.{u}).presheaf.stalk ηU)).comp φ).toAlgebra;
    ∀ (originalComponentFractionOpen : IsScalarTower ((D.C c).Y.presheaf.stalk (D.C c).y) (FractionRing ((D.C c).Y.presheaf.stalk (D.C c).y)) (FractionRing ((U₀ : Scheme.{u}).presheaf.stalk ηU)))
      (originalRComponentOpen : IsScalarTower R ((D.C c).Y.presheaf.stalk (D.C c).y) ((U₀ : Scheme.{u}).presheaf.stalk ηU))
      (originalRComponentField : IsScalarTower R ((D.C c).Y.presheaf.stalk (D.C c).y) (FractionRing ((U₀ : Scheme.{u}).presheaf.stalk ηU)))
      (originalComponentOpenLocal : IsLocalHom (algebraMap ((D.C c).Y.presheaf.stalk (D.C c).y) ((U₀ : Scheme.{u}).presheaf.stalk ηU)))
      (hdomO₀ : IsDomain ((D.C c).Y.presheaf.stalk (D.C c).y))
      (hdvrO₀ : IsDiscreteValuationRing ((D.C c).Y.presheaf.stalk (D.C c).y))
      (hlocO₀ : IsLocalHom (algebraMap R ((D.C c).Y.presheaf.stalk (D.C c).y)))
      (hidxO₀ : IsIndexOneExtension R ((D.C c).Y.presheaf.stalk (D.C c).y)),
    letI originalComponentFractionOpenCaptured := originalComponentFractionOpen;
    letI originalRComponentOpenCaptured := originalRComponentOpen;
    letI originalRComponentFieldCaptured := originalRComponentField;
    letI : IsLocalHom (algebraMap ((D.C c).Y.presheaf.stalk (D.C c).y) ((U₀ : Scheme.{u}).presheaf.stalk ηU)) := originalComponentOpenLocal;
    letI : IsLocalHom (algebraMap R ((D.C c).Y.presheaf.stalk (D.C c).y)) := hlocO₀;
    letI := (ZInQ.Contrib.CloudR2NeronExistence.Henselian.AlgebraicGeometry.Scheme.Hom.sectionsAlgebra gK) (D.C c).U;
    letI := (D.C c).algebraU;
    letI algUcF : Algebra Γ(XK, (D.C c).U) (FractionRing ((U₀ : Scheme.{u}).presheaf.stalk ηU)) :=
      ((algebraMap (FractionRing ((D.C c).Y.presheaf.stalk (D.C c).y)) (FractionRing ((U₀ : Scheme.{u}).presheaf.stalk ηU))).comp (algebraMap Γ(XK, (D.C c).U) (FractionRing ((D.C c).Y.presheaf.stalk (D.C c).y)))).toAlgebra;
    ∀ (hKUc : IsScalarTower K Γ(XK, (D.C c).U) (FractionRing ((U₀ : Scheme.{u}).presheaf.stalk ηU)))
      (towUcF₀F : IsScalarTower Γ(XK, (D.C c).U) (FractionRing ((D.C c).Y.presheaf.stalk (D.C c).y)) (FractionRing ((U₀ : Scheme.{u}).presheaf.stalk ηU))),
    letI hKUcCaptured := hKUc;
    letI towUcF₀FCaptured := towUcF₀F;
    letI : IsScalarTower K Γ(XK, (D.C c).U) (FractionRing ((D.C c).Y.presheaf.stalk (D.C c).y)) := (D.C c).isScalarTowerU;
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
    letI hKU''Captured := hKU'';
    ∀ (ωU'' : ⋀[Γ(XK, U'')]^d ((ZInQ.Contrib.CloudR2NeronExistence.Henselian.AlgebraicGeometry.Scheme.Hom.kaehlerPresheaf gK).obj (op U''))),
    ∀ (b₁ : Module.Basis (Fin d) (T.Y.presheaf.stalk ((pullback.snd z T.f).base (v.base ⟨η, hηU⟩))) (Ω[(T.Y.presheaf.stalk ((pullback.snd z T.f).base (v.base ⟨η, hηU⟩)))⁄R]))
      (w₁ : (T.Y.presheaf.stalk ((pullback.snd z T.f).base (v.base ⟨η, hηU⟩)))ˣ)
      (hread : letI := (ZInQ.Contrib.CloudR2NeronExistence.Henselian.AlgebraicGeometry.Scheme.Hom.sectionsAlgebra gK) U''
      TopFormOrder.topFormMap K K Γ(XK, U'') (FractionRing ((U₀ : Scheme.{u}).presheaf.stalk ⟨η, hηU⟩)) d ωU'' =
        (algebraMap (T.Y.presheaf.stalk ((pullback.snd z T.f).base (v.base ⟨η, hηU⟩))) (FractionRing ((U₀ : Scheme.{u}).presheaf.stalk ⟨η, hηU⟩)) (w₁ : (T.Y.presheaf.stalk ((pullback.snd z T.f).base (v.base ⟨η, hηU⟩)))) *
            algebraMap (T.Y.presheaf.stalk ((pullback.snd z T.f).base (v.base ⟨η, hηU⟩))) (FractionRing ((U₀ : Scheme.{u}).presheaf.stalk ⟨η, hηU⟩)) (algebraMap R (T.Y.presheaf.stalk ((pullback.snd z T.f).base (v.base ⟨η, hηU⟩))) ϖ) ^ T.n) •
          TopFormOrder.topFormMap R K (T.Y.presheaf.stalk ((pullback.snd z T.f).base (v.base ⟨η, hηU⟩))) (FractionRing ((U₀ : Scheme.{u}).presheaf.stalk ⟨η, hηU⟩)) d
            (exteriorPower.ιMulti (T.Y.presheaf.stalk ((pullback.snd z T.f).base (v.base ⟨η, hηU⟩))) d b₁)),
    ∀ (h23 : (TopFormOrder.topFormMap K (FractionRing (Z.presheaf.stalk ζ₀)) Γ(XK, (D.C c).U) (FractionRing ((U₀ : Scheme.{u}).presheaf.stalk ηU)) d (D.C c).ωU =
      TopFormOrder.topFormMap K (FractionRing (Z.presheaf.stalk ζ₀)) (FractionRing ((D.C c).Y.presheaf.stalk (D.C c).y)) (FractionRing ((U₀ : Scheme.{u}).presheaf.stalk ηU)) d
        ((D.C c).a • TopFormOrder.topFormMap R K ((D.C c).Y.presheaf.stalk (D.C c).y) (FractionRing ((D.C c).Y.presheaf.stalk (D.C c).y)) d
          (exteriorPower.ιMulti ((D.C c).Y.presheaf.stalk (D.C c).y) d (D.C c).b)))),
    ∀ (hFront : (IsFractionRing ((pullback z T.f).presheaf.stalk η') F) ∧
      (TopFormOrder.topFormMap K K' Γ(XK, U'') F d ωU'' = TopFormOrder.topFormMap K K' Γ(XK, (D.C c).U) F d (D.C c).ωU)),
    (∃ c : D.ι, T.n = (D.C c).n) ∧
      Function.Bijective (KaehlerDifferential.mapBaseChange (Z.presheaf.stalk ζ₀)
        ((pullback z T.f).presheaf.stalk η') ((U₀ : Scheme.{u}).presheaf.stalk ηU)) := by
  classical
  intro ηU η' ζ₀ y₁
  let OObj := ((U₀ : Scheme.{u}).presheaf.stalk ηU)
  let SObj := (Z.presheaf.stalk ζ₀)
  let PObj := ((pullback z T.f).presheaf.stalk η')
  let AObj := (T.Y.presheaf.stalk y₁)
  let ξ : ↥X := ((pullback.snd z f).base (U₀.ι.base ηU))
  let XObj := X.presheaf.stalk ξ
  let O : Type u := OObj
  let S : Type u := SObj
  let P : Type u := PObj
  let A : Type u := AObj
  let X₀ : Type u := XObj
  letI rOpen : CommRing O := _root_.CommRingCat.commRing OObj
  letI rPrime : CommRing S := _root_.CommRingCat.commRing SObj
  letI rPullback : CommRing P := _root_.CommRingCat.commRing PObj
  letI rAux : CommRing A := _root_.CommRingCat.commRing AObj
  letI rXStalk : CommRing X₀ := _root_.CommRingCat.commRing XObj
  let δP : P →+* O := (v.stalkMap ηU).hom
  let δS : S →+* P := ((pullback.fst z T.f).stalkMap η').hom
  let δA : A →+* P := ((pullback.snd z T.f).stalkMap η').hom
  let δX : X₀ →+* O := ((U₀.ι ≫ pullback.snd z f).stalkMap ηU).hom
  letI algR'O' : Algebra S P := δS.toAlgebra
  letI algO'O : Algebra P O := δP.toAlgebra
  letI algR'O : Algebra S O := (δP.comp δS).toAlgebra

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
  intro originalPrimePullbackOpen originalRPrimePullback originalRPrimeOpen
    originalRAuxPullback originalAuxPullbackOpen originalRAuxOpen originalRXOpen
    originalPrimePullbackField originalRAuxField
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
  intro hbc'
  intro c
  let C : ComponentReading R K gK d ω := D.C c
  let O₀Obj := C.Y.presheaf.stalk C.y
  let O₀ : Type u := O₀Obj
  letI rComponent : CommRing O₀ := _root_.CommRingCat.commRing O₀Obj
  letI domainComponent : IsDomain O₀ := C.isDomain
  let F₀ : Type u := FractionRing O₀
  letI fieldComponent : Field F₀ := @FractionRing.field O₀ rComponent domainComponent
  let BcObj := Γ(XK, C.U)
  let Bc : Type u := BcObj
  letI rSections : CommRing Bc := _root_.CommRingCat.commRing BcObj
  intro φ algF₀F hTowK
  letI : Algebra R O₀ := C.algebra
  letI : Algebra K F₀ := C.algebraK
  letI : IsScalarTower R K F₀ := C.isScalarTower
  letI : Algebra F₀ F := algF₀F
  letI : letI := C.algebraK; IsScalarTower K F₀ F := hTowK
  letI algO₀O : Algebra O₀ O := ((algebraMap X₀ O).comp φ).toAlgebra
  intro originalComponentFractionOpen originalRComponentOpen originalRComponentField
    originalComponentOpenLocal hdomO₀ hdvrO₀ hlocO₀ hidxO₀
  letI : IsScalarTower O₀ F₀ F := originalComponentFractionOpen
  letI : IsScalarTower R O₀ O := originalRComponentOpen
  letI : IsScalarTower R O₀ F := originalRComponentField
  letI : IsLocalHom (algebraMap O₀ O) := originalComponentOpenLocal
  letI : IsLocalHom (algebraMap R O₀) := hlocO₀
  letI := (ZInQ.Contrib.CloudR2NeronExistence.Henselian.AlgebraicGeometry.Scheme.Hom.sectionsAlgebra gK) C.U
  letI := C.algebraU
  letI algUcF : Algebra Bc F := ((algebraMap F₀ F).comp (algebraMap Bc F₀)).toAlgebra
  intro hKUc towUcF₀F
  letI : IsScalarTower K Bc F := hKUc
  letI : IsScalarTower Bc F₀ F := towUcF₀F
  letI : IsScalarTower K Bc F₀ := C.isScalarTowerU
  intro hbc
  intro U''
  let BuObj := Γ(XK, U'')
  let Bu : Type u := BuObj
  letI rUSections : CommRing Bu := _root_.CommRingCat.commRing BuObj
  letI := (ZInQ.Contrib.CloudR2NeronExistence.Henselian.AlgebraicGeometry.Scheme.Hom.sectionsAlgebra gK) U''
  intro hU'' algU''
  letI : Algebra Bu F := algU''
  intro hKU''
  letI : letI := (ZInQ.Contrib.CloudR2NeronExistence.Henselian.AlgebraicGeometry.Scheme.Hom.sectionsAlgebra gK) U''; IsScalarTower K Bu F := hKU''
  intro ωU''
  intro b₁ w₁ hread
  intro h23
  intro hFront
  obtain ⟨fractionPredicate, leftFormEquality⟩ := hFront
  letI : IsFractionRing P F := fractionPredicate
  have imageEquality :=
    @top_form_image_equality
      R rBase domainBase dvrBase K givenK aRK fractionRK XK gK d ω
      D X f Z z T η U₀ hηU v hdomO hdomR' aKF aKKprime aKprimeF
      originalKKprimeOpen c algF₀F hTowK hKUc towUcF₀F
      U'' hU'' algU'' hKU'' ωU'' leftFormEquality h23
  have constructionPair :=
    @image_order_and_bijective_stalk_construction
      R rBase domainBase dvrBase K givenK aRK fractionRK XK gK d ω
      D hD X f Z z T η U₀ hηU v hdomO hdomR'
      hdomO' hdvrO hdvrR' hlocR' originalPrimeOpenLocal
      originalPrimePullbackOpen originalRPrimePullback originalRPrimeOpen
      originalRAuxPullback originalAuxPullbackOpen originalRAuxOpen originalRXOpen
      originalPrimePullbackField originalRAuxField hRR'_map hO ϖ hϖ
      aKF aKKprime aKprimeF originalRKKprime originalPrimeFractionField originalRKOpen originalKKprimeOpen
      hbc' fractionPredicate c φ algF₀F hTowK
      originalComponentFractionOpen originalRComponentOpen originalRComponentField
      originalComponentOpenLocal hdomO₀ hdvrO₀ hlocO₀ hidxO₀ hbc
      U'' hU'' algU'' hKU'' ωU'' b₁ w₁ hread imageEquality
  exact constructionPair


theorem formal_smoothness_and_paired_outputs_construction
    {R : Type u} [rBase : CommRing R] [domainBase : IsDomain R] [dvrBase : IsDiscreteValuationRing R]
    (K : Type u) [givenK : Field K] [aRK : Algebra R K]
    {XK : Scheme.{u}} {gK : XK ⟶ Spec (CommRingCat.of K)}
    (d : ℕ)
    (ω : Γ((ZInQ.Contrib.CloudR2NeronExistence.Henselian.AlgebraicGeometry.Scheme.Hom.topDifferentials gK) d, ⊤))
    (D : MinimalComponentData R K gK d ω)
    (X : Scheme.{u}) (f : X ⟶ Spec (CommRingCat.of R)) [smoothX : Smooth f]
    (Z : Scheme.{u}) (z : Z ⟶ Spec (CommRingCat.of R)) [smoothZ : Smooth z]
    (T : ComponentReading R K gK d ω)
    (η : ↑(pullback z f)) (U₀ : (pullback z f).Opens) (hηU : η ∈ U₀)
    (v : (U₀ : Scheme.{u}) ⟶ pullback z T.f)
    (hv₁ : v ≫ pullback.fst z T.f = U₀.ι ≫ pullback.fst z f)
    [lfpPullbackFst : LocallyOfFinitePresentation (pullback.fst z f)]
    [lfpComparison : LocallyOfFinitePresentation (v ≫ pullback.fst z T.f)]
 :
    let ηU : ↥U₀ := ⟨η, hηU⟩;
    let η' : ↥(pullback z T.f) := v.base ηU;
    let ζ₀ : ↥Z := (pullback.fst z T.f).base η';
    letI rOpen : CommRing ((U₀ : Scheme.{u}).presheaf.stalk ηU) := _root_.CommRingCat.commRing ((U₀ : Scheme.{u}).presheaf.stalk ηU);
    letI rPrime : CommRing (Z.presheaf.stalk ζ₀) := _root_.CommRingCat.commRing (Z.presheaf.stalk ζ₀);
    letI rPullback : CommRing ((pullback z T.f).presheaf.stalk η') := _root_.CommRingCat.commRing ((pullback z T.f).presheaf.stalk η');
    letI algR'O' : Algebra (Z.presheaf.stalk ζ₀) ((pullback z T.f).presheaf.stalk η') := ((pullback.fst z T.f).stalkMap η').hom.toAlgebra;
    letI algO'O : Algebra ((pullback z T.f).presheaf.stalk η') ((U₀ : Scheme.{u}).presheaf.stalk ηU) := (v.stalkMap ηU).hom.toAlgebra;
    letI algR'O : Algebra (Z.presheaf.stalk ζ₀) ((U₀ : Scheme.{u}).presheaf.stalk ηU) :=
      ((v.stalkMap ηU).hom.comp ((pullback.fst z T.f).stalkMap η').hom).toAlgebra;
    letI originalPrimePullbackOpen : IsScalarTower (Z.presheaf.stalk ζ₀) ((pullback z T.f).presheaf.stalk η')
      ((U₀ : Scheme.{u}).presheaf.stalk ηU) := IsScalarTower.of_algebraMap_eq (fun _ => rfl);
    ∀ (hPair : (∃ c : D.ι, T.n = (D.C c).n) ∧
      Function.Bijective (KaehlerDifferential.mapBaseChange (Z.presheaf.stalk ζ₀)
        ((pullback z T.f).presheaf.stalk η') ((U₀ : Scheme.{u}).presheaf.stalk ηU))),
    (∃ c : D.ι, T.n = (D.C c).n) ∧
      letI : Algebra ((pullback z T.f).presheaf.stalk (v.base ⟨η, hηU⟩)) ((U₀ : Scheme.{u}).presheaf.stalk ⟨η, hηU⟩) := (v.stalkMap ⟨η, hηU⟩).hom.toAlgebra
      Algebra.FormallySmooth ((pullback z T.f).presheaf.stalk (v.base ⟨η, hηU⟩)) ((U₀ : Scheme.{u}).presheaf.stalk ⟨η, hηU⟩) := by
  classical
  letI smoothAux : Smooth T.f := T.smooth
  haveI smoothPullbackFst : Smooth (pullback.fst z f) := inferInstance
  intro ηU η' ζ₀
  let OObj := ((U₀ : Scheme.{u}).presheaf.stalk ηU)
  let SObj := (Z.presheaf.stalk ζ₀)
  let PObj := ((pullback z T.f).presheaf.stalk η')
  let O : Type u := OObj
  let S : Type u := SObj
  let P : Type u := PObj
  letI rOpen : CommRing O := _root_.CommRingCat.commRing OObj
  letI rPrime : CommRing S := _root_.CommRingCat.commRing SObj
  letI rPullback : CommRing P := _root_.CommRingCat.commRing PObj
  let δP : P →+* O := (v.stalkMap ηU).hom
  let δS : S →+* P := ((pullback.fst z T.f).stalkMap η').hom
  letI algR'O' : Algebra S P := δS.toAlgebra
  letI algO'O : Algebra P O := δP.toAlgebra
  letI algR'O : Algebra S O := (δP.comp δS).toAlgebra
  haveI originalPrimePullbackOpen : IsScalarTower (Z.presheaf.stalk ζ₀) ((pullback z T.f).presheaf.stalk η')
      ((U₀ : Scheme.{u}).presheaf.stalk ηU) := IsScalarTower.of_algebraMap_eq (fun _ => rfl)

  have hFS : Algebra.FormallySmooth (Z.presheaf.stalk ζ₀) ((U₀ : Scheme.{u}).presheaf.stalk ηU) := by
    haveI : Smooth (v ≫ pullback.fst z T.f) := by rw [hv₁]; infer_instance
    have hmem : ηU ∈ (v ≫ pullback.fst z T.f).smoothLocus := by
      rw [Scheme.Hom.smoothLocus_eq_top]; trivial
    have hfs : ((v ≫ pullback.fst z T.f).stalkMap ηU).hom.FormallySmooth := (Scheme.Hom.mem_smoothLocus).mp hmem
    rw [Scheme.Hom.stalkMap_comp] at hfs
    exact hfs

  intro hPair
  obtain ⟨orderWitness, stalkBijective⟩ := hPair
  refine ⟨orderWitness, ?_⟩

  haveI := Algebra.FormallyEtale.of_formallySmooth_of_bijective_mapBaseChange stalkBijective
  exact inferInstance
end P2MW.S_NeronModelInfra_exists_n_eq_and_formallySmooth_stalk_of_isOmegaMinimal_of_genericFibreRestrict_comp_eq_mul
end ZInQ.Contrib.CloudR2NeronExistence.Henselian
