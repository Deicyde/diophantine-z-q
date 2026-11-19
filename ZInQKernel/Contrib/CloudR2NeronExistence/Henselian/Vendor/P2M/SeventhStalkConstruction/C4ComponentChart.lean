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

theorem exists_component_chart_reading_data
    {R : Type u} [rBase : CommRing R] [domainBase : IsDomain R] [dvrBase : IsDiscreteValuationRing R]
    (K : Type u) [givenK : Field K] [aRK : Algebra R K] [fractionRK : IsFractionRing R K]
    {XK : Scheme.{u}} {gK : XK ⟶ Spec (CommRingCat.of K)}
    [smoothGeneric : Smooth gK] [separatedGeneric : IsSeparated gK]
    [finiteTypeGeneric : LocallyOfFiniteType gK] [compactGeneric : QuasiCompact gK]
    (d : ℕ) [dimensionGeneric : SmoothOfRelativeDimension d gK]
    (ω : Γ((ZInQ.Contrib.CloudR2NeronExistence.Henselian.AlgebraicGeometry.Scheme.Hom.topDifferentials gK) d, ⊤))
    (D : MinimalComponentData R K gK d ω)
    (X : Scheme.{u}) (f : X ⟶ Spec (CommRingCat.of R))
    (e : SchemeHomOver (pullback.snd f (specGenericFibreInclusion R K)) gK)
    (V : ∀ c : D.ι, ((D.C c).Y).Opens) (j : ∀ c : D.ι, SchemeHomOver ((V c).ι ≫ (D.C c).f) f)
    [smoothX : Smooth f] [separatedX : IsSeparated f]
    [finiteTypeX : LocallyOfFiniteType f] [compactX : QuasiCompact f] [isoGenericX : IsIso e.1]
    (hyV : ∀ c, (D.C c).y ∈ V c)
    (hVK : ∀ c (y' : ↥(D.C c).Y), (D.C c).f.base y' ≠ IsLocalRing.closedPoint R → y' ∈ V c)
    (hjopen : ∀ c, IsOpenImmersion (j c).1)
    (hjchart : ∀ c, (genericFibreRestrict R K f ((V c).ι ≫ (D.C c).f) (j c)).1 ≫ e.1 =
      (genericFibreRestrict R K (D.C c).f ((V c).ι ≫ (D.C c).f) ⟨(V c).ι, rfl⟩).1 ≫ (D.C c).e.1)
    (hcover : ∀ x : ↥X, ∃ c, x ∈ Set.range (j c).1.base)
    (Z : Scheme.{u}) (z : Z ⟶ Spec (CommRingCat.of R))
    (T : ComponentReading R K gK d ω)
    (η : ↑(pullback z f)) (U₀ : (pullback z f).Opens) (hηU : η ∈ U₀)
    (v : (U₀ : Scheme.{u}) ⟶ pullback z T.f) :
    let ηU : ↥U₀ := ⟨η, hηU⟩;
    let η' : ↥(pullback z T.f) := v.base ηU;
    let ζ₀ : ↥Z := (pullback.fst z T.f).base η';
    letI rOpen : CommRing ((U₀ : Scheme.{u}).presheaf.stalk ηU) := _root_.CommRingCat.commRing ((U₀ : Scheme.{u}).presheaf.stalk ηU);
    letI rPrime : CommRing (Z.presheaf.stalk ζ₀) := _root_.CommRingCat.commRing (Z.presheaf.stalk ζ₀);
    letI rPullback : CommRing ((pullback z T.f).presheaf.stalk η') := _root_.CommRingCat.commRing ((pullback z T.f).presheaf.stalk η');
    letI rXStalk : CommRing (X.presheaf.stalk ((pullback.snd z f).base (U₀.ι.base ηU))) := _root_.CommRingCat.commRing (X.presheaf.stalk ((pullback.snd z f).base (U₀.ι.base ηU)));
    letI algR'O' : Algebra (Z.presheaf.stalk ζ₀) ((pullback z T.f).presheaf.stalk η') := ((pullback.fst z T.f).stalkMap η').hom.toAlgebra;
    letI algO'O : Algebra ((pullback z T.f).presheaf.stalk η') ((U₀ : Scheme.{u}).presheaf.stalk ηU) := (v.stalkMap ηU).hom.toAlgebra;
    letI algR'O : Algebra (Z.presheaf.stalk ζ₀) ((U₀ : Scheme.{u}).presheaf.stalk ηU) :=
      ((v.stalkMap ηU).hom.comp ((pullback.fst z T.f).stalkMap η').hom).toAlgebra;
    letI algRR' : Algebra R (Z.presheaf.stalk ζ₀) := stalkAlgebra z ζ₀;
    letI algRO : Algebra R ((U₀ : Scheme.{u}).presheaf.stalk ηU) := ((algebraMap (Z.presheaf.stalk ζ₀) ((U₀ : Scheme.{u}).presheaf.stalk ηU)).comp (algebraMap R (Z.presheaf.stalk ζ₀))).toAlgebra;
    letI algRX : Algebra R (X.presheaf.stalk ((pullback.snd z f).base (U₀.ι.base ηU))) := stalkAlgebra f ((pullback.snd z f).base (U₀.ι.base ηU));
    letI algXO : Algebra (X.presheaf.stalk ((pullback.snd z f).base (U₀.ι.base ηU))) ((U₀ : Scheme.{u}).presheaf.stalk ηU) := ((U₀.ι ≫ pullback.snd z f).stalkMap ηU).hom.toAlgebra;
    ∀ (hdomO : IsDomain ((U₀ : Scheme.{u}).presheaf.stalk ηU)),
    letI : IsDomain ((U₀ : Scheme.{u}).presheaf.stalk ηU) := hdomO;
    letI fieldOpen : Field (FractionRing ((U₀ : Scheme.{u}).presheaf.stalk ηU)) := @FractionRing.field ((U₀ : Scheme.{u}).presheaf.stalk ηU) rOpen hdomO;
    ∀ (algKF : Algebra K (FractionRing ((U₀ : Scheme.{u}).presheaf.stalk ηU))),
    letI : Algebra K (FractionRing ((U₀ : Scheme.{u}).presheaf.stalk ηU)) := algKF;
    ∀ (hξsp : f.base ((pullback.snd z f).base (U₀.ι.base ηU)) = IsLocalRing.closedPoint R) (hξmax : ∀ y : ↥X, y ⤳ ((pullback.snd z f).base (U₀.ι.base ηU)) →
        f.base y = IsLocalRing.closedPoint R → y = ((pullback.snd z f).base (U₀.ι.base ηU))) (halgX : X.fromSpecStalk ((pullback.snd z f).base (U₀.ι.base ηU)) ≫ f =
        Spec.map (CommRingCat.ofHom (algebraMap R (X.presheaf.stalk ((pullback.snd z f).base (U₀.ι.base ηU)))))) (originalRKOpen : IsScalarTower R K (FractionRing ((U₀ : Scheme.{u}).presheaf.stalk ηU))) (originalRXFTower : IsScalarTower R (X.presheaf.stalk ((pullback.snd z f).base (U₀.ι.base ηU))) (FractionRing ((U₀ : Scheme.{u}).presheaf.stalk ηU))) (hinjXO : Function.Injective (algebraMap (X.presheaf.stalk ((pullback.snd z f).base (U₀.ι.base ηU))) ((U₀ : Scheme.{u}).presheaf.stalk ηU))),
    letI : IsScalarTower R K (FractionRing ((U₀ : Scheme.{u}).presheaf.stalk ηU)) := originalRKOpen;
    letI : IsScalarTower R (X.presheaf.stalk ((pullback.snd z f).base (U₀.ι.base ηU))) (FractionRing ((U₀ : Scheme.{u}).presheaf.stalk ηU)) := originalRXFTower;
    ∃ (c : D.ι),
    letI rComponent : CommRing ((D.C c).Y.presheaf.stalk (D.C c).y) := _root_.CommRingCat.commRing ((D.C c).Y.presheaf.stalk (D.C c).y);
    letI domainComponent : IsDomain ((D.C c).Y.presheaf.stalk (D.C c).y) := (D.C c).isDomain;
    letI fieldComponent : Field (FractionRing ((D.C c).Y.presheaf.stalk (D.C c).y)) := @FractionRing.field ((D.C c).Y.presheaf.stalk (D.C c).y) rComponent domainComponent;
    letI rSections : CommRing Γ(XK, (D.C c).U) := _root_.CommRingCat.commRing Γ(XK, (D.C c).U);
    ∃ (φ : ((D.C c).Y.presheaf.stalk (D.C c).y) →+* (X.presheaf.stalk ((pullback.snd z f).base (U₀.ι.base ηU)))) (hc : (j c).1.base ⟨(D.C c).y, hyV c⟩ = ((pullback.snd z f).base (U₀.ι.base ηU))) (hφbij : Function.Bijective φ) (hφloc : IsLocalHom φ) (hφR : letI := (D.C c).algebra;
        φ.comp (algebraMap R ((D.C c).Y.presheaf.stalk (D.C c).y)) = algebraMap R (X.presheaf.stalk ((pullback.snd z f).base (U₀.ι.base ηU)))) (algF₀F : Algebra (FractionRing ((D.C c).Y.presheaf.stalk (D.C c).y)) (FractionRing ((U₀ : Scheme.{u}).presheaf.stalk ηU))) (hTowO₀ : letI : Algebra ((D.C c).Y.presheaf.stalk (D.C c).y) (FractionRing ((U₀ : Scheme.{u}).presheaf.stalk ηU)) := ((algebraMap (X.presheaf.stalk ((pullback.snd z f).base (U₀.ι.base ηU))) (FractionRing ((U₀ : Scheme.{u}).presheaf.stalk ηU))).comp φ).toAlgebra;
        IsScalarTower ((D.C c).Y.presheaf.stalk (D.C c).y) (FractionRing ((D.C c).Y.presheaf.stalk (D.C c).y)) (FractionRing ((U₀ : Scheme.{u}).presheaf.stalk ηU))) (hTowK : letI := (D.C c).algebraK; IsScalarTower K (FractionRing ((D.C c).Y.presheaf.stalk (D.C c).y)) (FractionRing ((U₀ : Scheme.{u}).presheaf.stalk ηU))),
    letI : Algebra R ((D.C c).Y.presheaf.stalk (D.C c).y) := (D.C c).algebra;
    letI : Algebra K (FractionRing ((D.C c).Y.presheaf.stalk (D.C c).y)) := (D.C c).algebraK;
    letI : IsScalarTower R K (FractionRing ((D.C c).Y.presheaf.stalk (D.C c).y)) := (D.C c).isScalarTower;
    letI : Algebra (FractionRing ((D.C c).Y.presheaf.stalk (D.C c).y)) (FractionRing ((U₀ : Scheme.{u}).presheaf.stalk ηU)) := algF₀F;
    letI := (ZInQ.Contrib.CloudR2NeronExistence.Henselian.AlgebraicGeometry.Scheme.Hom.sectionsAlgebra gK) (D.C c).U;
    letI := (D.C c).algebraU;
    letI algUcF : Algebra Γ(XK, (D.C c).U) (FractionRing ((U₀ : Scheme.{u}).presheaf.stalk ηU)) :=
      ((algebraMap (FractionRing ((D.C c).Y.presheaf.stalk (D.C c).y)) (FractionRing ((U₀ : Scheme.{u}).presheaf.stalk ηU))).comp (algebraMap Γ(XK, (D.C c).U) (FractionRing ((D.C c).Y.presheaf.stalk (D.C c).y)))).toAlgebra;
    (Spec.map (CommRingCat.ofHom (algebraMap Γ(XK, (D.C c).U) (FractionRing ((U₀ : Scheme.{u}).presheaf.stalk ηU)))) ≫ (D.C c).hU.fromSpec =
      (NeronModelInfra.schemeHomOverComp
        (pointGenericFibre (K := K) (K' := (FractionRing ((U₀ : Scheme.{u}).presheaf.stalk ηU)))
          (⟨X.fromSpecStalk ((pullback.snd z f).base (U₀.ι.base ηU)), halgX⟩ :
            SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap R (X.presheaf.stalk ((pullback.snd z f).base (U₀.ι.base ηU)))))) f)) e).1) := by
  classical
  intro ηU η' ζ₀
  letI rOpen : CommRing ((U₀ : Scheme.{u}).presheaf.stalk ηU) := _root_.CommRingCat.commRing ((U₀ : Scheme.{u}).presheaf.stalk ηU)
  letI rPrime : CommRing (Z.presheaf.stalk ζ₀) := _root_.CommRingCat.commRing (Z.presheaf.stalk ζ₀)
  letI rPullback : CommRing ((pullback z T.f).presheaf.stalk η') := _root_.CommRingCat.commRing ((pullback z T.f).presheaf.stalk η')
  letI rXStalk : CommRing (X.presheaf.stalk ((pullback.snd z f).base (U₀.ι.base ηU))) := _root_.CommRingCat.commRing (X.presheaf.stalk ((pullback.snd z f).base (U₀.ι.base ηU)))
  letI algR'O' : Algebra (Z.presheaf.stalk ζ₀) ((pullback z T.f).presheaf.stalk η') := ((pullback.fst z T.f).stalkMap η').hom.toAlgebra
  letI algO'O : Algebra ((pullback z T.f).presheaf.stalk η') ((U₀ : Scheme.{u}).presheaf.stalk ηU) := (v.stalkMap ηU).hom.toAlgebra
  letI algR'O : Algebra (Z.presheaf.stalk ζ₀) ((U₀ : Scheme.{u}).presheaf.stalk ηU) :=
    ((v.stalkMap ηU).hom.comp ((pullback.fst z T.f).stalkMap η').hom).toAlgebra
  letI algRR' : Algebra R (Z.presheaf.stalk ζ₀) := stalkAlgebra z ζ₀
  letI algRO : Algebra R ((U₀ : Scheme.{u}).presheaf.stalk ηU) := ((algebraMap (Z.presheaf.stalk ζ₀) ((U₀ : Scheme.{u}).presheaf.stalk ηU)).comp (algebraMap R (Z.presheaf.stalk ζ₀))).toAlgebra
  letI algRX : Algebra R (X.presheaf.stalk ((pullback.snd z f).base (U₀.ι.base ηU))) := stalkAlgebra f ((pullback.snd z f).base (U₀.ι.base ηU))
  letI algXO : Algebra (X.presheaf.stalk ((pullback.snd z f).base (U₀.ι.base ηU))) ((U₀ : Scheme.{u}).presheaf.stalk ηU) := ((U₀.ι ≫ pullback.snd z f).stalkMap ηU).hom.toAlgebra
  intro hdomO
  letI : IsDomain ((U₀ : Scheme.{u}).presheaf.stalk ηU) := hdomO
  letI fieldOpen : Field (FractionRing ((U₀ : Scheme.{u}).presheaf.stalk ηU)) := @FractionRing.field ((U₀ : Scheme.{u}).presheaf.stalk ηU) rOpen hdomO
  intro algKF
  letI : Algebra K (FractionRing ((U₀ : Scheme.{u}).presheaf.stalk ηU)) := algKF
  intro hξsp hξmax halgX originalRKOpen originalRXFTower hinjXO
  letI : IsScalarTower R K (FractionRing ((U₀ : Scheme.{u}).presheaf.stalk ηU)) := originalRKOpen
  letI : IsScalarTower R (X.presheaf.stalk ((pullback.snd z f).base (U₀.ι.base ηU))) (FractionRing ((U₀ : Scheme.{u}).presheaf.stalk ηU)) := originalRXFTower
  let F := FractionRing ((U₀ : Scheme.{u}).presheaf.stalk ηU)
  obtain ⟨c, φ, hc, hφbij, hφloc, hφR, algF₀F, hTowO₀, hTowK, hxX⟩ :=
    @NeronModelInfra.MinimalComponentData.exists_ringHom_stalk_chart_comp_eq_pointGenericFibre_of_forall_specializes
      R rBase domainBase dvrBase K givenK aRK fractionRK
      XK gK smoothGeneric separatedGeneric finiteTypeGeneric compactGeneric
      d dimensionGeneric ω D X f e V j smoothX separatedX finiteTypeX compactX isoGenericX
      hyV hVK hjopen hjchart hcover ((pullback.snd z f).base (U₀.ι.base ηU)) hξsp hξmax
      algRX halgX F fieldOpen
      (inferInstance : Algebra (X.presheaf.stalk ((pullback.snd z f).base (U₀.ι.base ηU))) F)
      (inferInstance : Algebra R F) algKF originalRXFTower originalRKOpen
      (by rw [IsScalarTower.algebraMap_eq (X.presheaf.stalk ((pullback.snd z f).base (U₀.ι.base ηU)))
        ((U₀ : Scheme.{u}).presheaf.stalk ηU) F]
          exact (IsFractionRing.injective ((U₀ : Scheme.{u}).presheaf.stalk ηU) F).comp hinjXO)
  refine ⟨c, ?_⟩
  letI rComponent : CommRing ((D.C c).Y.presheaf.stalk (D.C c).y) := _root_.CommRingCat.commRing ((D.C c).Y.presheaf.stalk (D.C c).y)
  letI domainComponent : IsDomain ((D.C c).Y.presheaf.stalk (D.C c).y) := (D.C c).isDomain
  letI fieldComponent : Field (FractionRing ((D.C c).Y.presheaf.stalk (D.C c).y)) := @FractionRing.field ((D.C c).Y.presheaf.stalk (D.C c).y) rComponent domainComponent
  letI rSections : CommRing Γ(XK, (D.C c).U) := _root_.CommRingCat.commRing Γ(XK, (D.C c).U)
  refine ⟨φ, hc, hφbij, hφloc, hφR, algF₀F, hTowO₀, hTowK, ?_⟩
  letI : Algebra R ((D.C c).Y.presheaf.stalk (D.C c).y) := (D.C c).algebra
  letI : Algebra K (FractionRing ((D.C c).Y.presheaf.stalk (D.C c).y)) := (D.C c).algebraK
  letI : IsScalarTower R K (FractionRing ((D.C c).Y.presheaf.stalk (D.C c).y)) := (D.C c).isScalarTower
  letI : Algebra (FractionRing ((D.C c).Y.presheaf.stalk (D.C c).y)) (FractionRing ((U₀ : Scheme.{u}).presheaf.stalk ηU)) := algF₀F
  letI := (ZInQ.Contrib.CloudR2NeronExistence.Henselian.AlgebraicGeometry.Scheme.Hom.sectionsAlgebra gK) (D.C c).U
  letI := (D.C c).algebraU
  letI algUcF : Algebra Γ(XK, (D.C c).U) (FractionRing ((U₀ : Scheme.{u}).presheaf.stalk ηU)) :=
    ((algebraMap (FractionRing ((D.C c).Y.presheaf.stalk (D.C c).y)) (FractionRing ((U₀ : Scheme.{u}).presheaf.stalk ηU))).comp (algebraMap Γ(XK, (D.C c).U) (FractionRing ((D.C c).Y.presheaf.stalk (D.C c).y)))).toAlgebra
  exact hxX

theorem component_chart_stalk_tower_index_data
    {R : Type u} [rBase : CommRing R] [domainBase : IsDomain R] [dvrBase : IsDiscreteValuationRing R]
    (K : Type u) [givenK : Field K] [aRK : Algebra R K]
    {XK : Scheme.{u}} {gK : XK ⟶ Spec (CommRingCat.of K)}
    (d : ℕ)
    (ω : Γ((ZInQ.Contrib.CloudR2NeronExistence.Henselian.AlgebraicGeometry.Scheme.Hom.topDifferentials gK) d, ⊤))
    (D : MinimalComponentData R K gK d ω)
    (X : Scheme.{u}) (f : X ⟶ Spec (CommRingCat.of R))
    (Z : Scheme.{u}) (z : Z ⟶ Spec (CommRingCat.of R))
    (T : ComponentReading R K gK d ω)
    (η : ↑(pullback z f)) (U₀ : (pullback z f).Opens) (hηU : η ∈ U₀)
    (v : (U₀ : Scheme.{u}) ⟶ pullback z T.f) :
    let ηU : ↥U₀ := ⟨η, hηU⟩;
    let η' : ↥(pullback z T.f) := v.base ηU;
    let ζ₀ : ↥Z := (pullback.fst z T.f).base η';
    letI rOpen : CommRing ((U₀ : Scheme.{u}).presheaf.stalk ηU) := _root_.CommRingCat.commRing ((U₀ : Scheme.{u}).presheaf.stalk ηU);
    letI rPrime : CommRing (Z.presheaf.stalk ζ₀) := _root_.CommRingCat.commRing (Z.presheaf.stalk ζ₀);
    letI rPullback : CommRing ((pullback z T.f).presheaf.stalk η') := _root_.CommRingCat.commRing ((pullback z T.f).presheaf.stalk η');
    letI rXStalk : CommRing (X.presheaf.stalk ((pullback.snd z f).base (U₀.ι.base ηU))) := _root_.CommRingCat.commRing (X.presheaf.stalk ((pullback.snd z f).base (U₀.ι.base ηU)));
    letI algR'O' : Algebra (Z.presheaf.stalk ζ₀) ((pullback z T.f).presheaf.stalk η') := ((pullback.fst z T.f).stalkMap η').hom.toAlgebra;
    letI algO'O : Algebra ((pullback z T.f).presheaf.stalk η') ((U₀ : Scheme.{u}).presheaf.stalk ηU) := (v.stalkMap ηU).hom.toAlgebra;
    letI algR'O : Algebra (Z.presheaf.stalk ζ₀) ((U₀ : Scheme.{u}).presheaf.stalk ηU) :=
      ((v.stalkMap ηU).hom.comp ((pullback.fst z T.f).stalkMap η').hom).toAlgebra;
    letI algRR' : Algebra R (Z.presheaf.stalk ζ₀) := stalkAlgebra z ζ₀;
    letI algRO : Algebra R ((U₀ : Scheme.{u}).presheaf.stalk ηU) := ((algebraMap (Z.presheaf.stalk ζ₀) ((U₀ : Scheme.{u}).presheaf.stalk ηU)).comp (algebraMap R (Z.presheaf.stalk ζ₀))).toAlgebra;
    letI algRX : Algebra R (X.presheaf.stalk ((pullback.snd z f).base (U₀.ι.base ηU))) := stalkAlgebra f ((pullback.snd z f).base (U₀.ι.base ηU));
    letI algXO : Algebra (X.presheaf.stalk ((pullback.snd z f).base (U₀.ι.base ηU))) ((U₀ : Scheme.{u}).presheaf.stalk ηU) := ((U₀.ι ≫ pullback.snd z f).stalkMap ηU).hom.toAlgebra;
    ∀ (hdomO : IsDomain ((U₀ : Scheme.{u}).presheaf.stalk ηU)),
    letI : IsDomain ((U₀ : Scheme.{u}).presheaf.stalk ηU) := hdomO;
    letI fieldOpen : Field (FractionRing ((U₀ : Scheme.{u}).presheaf.stalk ηU)) := @FractionRing.field ((U₀ : Scheme.{u}).presheaf.stalk ηU) rOpen hdomO;
    ∀ (originalRXOTower : IsScalarTower R (X.presheaf.stalk ((pullback.snd z f).base (U₀.ι.base ηU))) ((U₀ : Scheme.{u}).presheaf.stalk ηU)) (originalROpenField : IsScalarTower R ((U₀ : Scheme.{u}).presheaf.stalk ηU) (FractionRing ((U₀ : Scheme.{u}).presheaf.stalk ηU))),
    letI : IsScalarTower R (X.presheaf.stalk ((pullback.snd z f).base (U₀.ι.base ηU))) ((U₀ : Scheme.{u}).presheaf.stalk ηU) := originalRXOTower;
    letI : IsScalarTower R ((U₀ : Scheme.{u}).presheaf.stalk ηU) (FractionRing ((U₀ : Scheme.{u}).presheaf.stalk ηU)) := originalROpenField;
    ∀ (c : D.ι),
    letI rComponent : CommRing ((D.C c).Y.presheaf.stalk (D.C c).y) := _root_.CommRingCat.commRing ((D.C c).Y.presheaf.stalk (D.C c).y);
    letI domainComponent : IsDomain ((D.C c).Y.presheaf.stalk (D.C c).y) := (D.C c).isDomain;
    letI fieldComponent : Field (FractionRing ((D.C c).Y.presheaf.stalk (D.C c).y)) := @FractionRing.field ((D.C c).Y.presheaf.stalk (D.C c).y) rComponent domainComponent;
    ∀ (φ : ((D.C c).Y.presheaf.stalk (D.C c).y) →+* (X.presheaf.stalk ((pullback.snd z f).base (U₀.ι.base ηU)))) (hφloc : IsLocalHom φ) (hφR : letI := (D.C c).algebra;
        φ.comp (algebraMap R ((D.C c).Y.presheaf.stalk (D.C c).y)) = algebraMap R (X.presheaf.stalk ((pullback.snd z f).base (U₀.ι.base ηU)))) (algF₀F : Algebra (FractionRing ((D.C c).Y.presheaf.stalk (D.C c).y)) (FractionRing ((U₀ : Scheme.{u}).presheaf.stalk ηU))) (hTowO₀ : letI : Algebra ((D.C c).Y.presheaf.stalk (D.C c).y) (FractionRing ((U₀ : Scheme.{u}).presheaf.stalk ηU)) := ((algebraMap (X.presheaf.stalk ((pullback.snd z f).base (U₀.ι.base ηU))) (FractionRing ((U₀ : Scheme.{u}).presheaf.stalk ηU))).comp φ).toAlgebra;
        IsScalarTower ((D.C c).Y.presheaf.stalk (D.C c).y) (FractionRing ((D.C c).Y.presheaf.stalk (D.C c).y)) (FractionRing ((U₀ : Scheme.{u}).presheaf.stalk ηU))),
    letI : Algebra R ((D.C c).Y.presheaf.stalk (D.C c).y) := (D.C c).algebra;
    letI : Algebra K (FractionRing ((D.C c).Y.presheaf.stalk (D.C c).y)) := (D.C c).algebraK;
    letI : IsScalarTower R K (FractionRing ((D.C c).Y.presheaf.stalk (D.C c).y)) := (D.C c).isScalarTower;
    letI : Algebra (FractionRing ((D.C c).Y.presheaf.stalk (D.C c).y)) (FractionRing ((U₀ : Scheme.{u}).presheaf.stalk ηU)) := algF₀F;
    letI algO₀O : Algebra ((D.C c).Y.presheaf.stalk (D.C c).y) ((U₀ : Scheme.{u}).presheaf.stalk ηU) := ((algebraMap (X.presheaf.stalk ((pullback.snd z f).base (U₀.ι.base ηU))) ((U₀ : Scheme.{u}).presheaf.stalk ηU)).comp φ).toAlgebra;
    ∃ (originalComponentFractionOpen : IsScalarTower ((D.C c).Y.presheaf.stalk (D.C c).y) (FractionRing ((D.C c).Y.presheaf.stalk (D.C c).y)) (FractionRing ((U₀ : Scheme.{u}).presheaf.stalk ηU))) (originalRComponentOpen : IsScalarTower R ((D.C c).Y.presheaf.stalk (D.C c).y) ((U₀ : Scheme.{u}).presheaf.stalk ηU)) (originalRComponentField : IsScalarTower R ((D.C c).Y.presheaf.stalk (D.C c).y) (FractionRing ((U₀ : Scheme.{u}).presheaf.stalk ηU))) (originalComponentOpenLocal : IsLocalHom (algebraMap ((D.C c).Y.presheaf.stalk (D.C c).y) ((U₀ : Scheme.{u}).presheaf.stalk ηU))) (hdomO₀ : IsDomain ((D.C c).Y.presheaf.stalk (D.C c).y)) (hdvrO₀ : IsDiscreteValuationRing ((D.C c).Y.presheaf.stalk (D.C c).y)) (hlocO₀ : IsLocalHom (algebraMap R ((D.C c).Y.presheaf.stalk (D.C c).y))),
    IsIndexOneExtension R ((D.C c).Y.presheaf.stalk (D.C c).y) := by
  classical
  intro ηU η' ζ₀
  letI rOpen : CommRing ((U₀ : Scheme.{u}).presheaf.stalk ηU) := _root_.CommRingCat.commRing ((U₀ : Scheme.{u}).presheaf.stalk ηU)
  letI rPrime : CommRing (Z.presheaf.stalk ζ₀) := _root_.CommRingCat.commRing (Z.presheaf.stalk ζ₀)
  letI rPullback : CommRing ((pullback z T.f).presheaf.stalk η') := _root_.CommRingCat.commRing ((pullback z T.f).presheaf.stalk η')
  letI rXStalk : CommRing (X.presheaf.stalk ((pullback.snd z f).base (U₀.ι.base ηU))) := _root_.CommRingCat.commRing (X.presheaf.stalk ((pullback.snd z f).base (U₀.ι.base ηU)))
  letI algR'O' : Algebra (Z.presheaf.stalk ζ₀) ((pullback z T.f).presheaf.stalk η') := ((pullback.fst z T.f).stalkMap η').hom.toAlgebra
  letI algO'O : Algebra ((pullback z T.f).presheaf.stalk η') ((U₀ : Scheme.{u}).presheaf.stalk ηU) := (v.stalkMap ηU).hom.toAlgebra
  letI algR'O : Algebra (Z.presheaf.stalk ζ₀) ((U₀ : Scheme.{u}).presheaf.stalk ηU) :=
    ((v.stalkMap ηU).hom.comp ((pullback.fst z T.f).stalkMap η').hom).toAlgebra
  letI algRR' : Algebra R (Z.presheaf.stalk ζ₀) := stalkAlgebra z ζ₀
  letI algRO : Algebra R ((U₀ : Scheme.{u}).presheaf.stalk ηU) := ((algebraMap (Z.presheaf.stalk ζ₀) ((U₀ : Scheme.{u}).presheaf.stalk ηU)).comp (algebraMap R (Z.presheaf.stalk ζ₀))).toAlgebra
  letI algRX : Algebra R (X.presheaf.stalk ((pullback.snd z f).base (U₀.ι.base ηU))) := stalkAlgebra f ((pullback.snd z f).base (U₀.ι.base ηU))
  letI algXO : Algebra (X.presheaf.stalk ((pullback.snd z f).base (U₀.ι.base ηU))) ((U₀ : Scheme.{u}).presheaf.stalk ηU) := ((U₀.ι ≫ pullback.snd z f).stalkMap ηU).hom.toAlgebra
  intro hdomO
  letI : IsDomain ((U₀ : Scheme.{u}).presheaf.stalk ηU) := hdomO
  letI fieldOpen : Field (FractionRing ((U₀ : Scheme.{u}).presheaf.stalk ηU)) := @FractionRing.field ((U₀ : Scheme.{u}).presheaf.stalk ηU) rOpen hdomO
  intro originalRXOTower originalROpenField
  letI : IsScalarTower R (X.presheaf.stalk ((pullback.snd z f).base (U₀.ι.base ηU))) ((U₀ : Scheme.{u}).presheaf.stalk ηU) := originalRXOTower
  letI : IsScalarTower R ((U₀ : Scheme.{u}).presheaf.stalk ηU) (FractionRing ((U₀ : Scheme.{u}).presheaf.stalk ηU)) := originalROpenField
  intro c
  letI rComponent : CommRing ((D.C c).Y.presheaf.stalk (D.C c).y) := _root_.CommRingCat.commRing ((D.C c).Y.presheaf.stalk (D.C c).y)
  letI domainComponent : IsDomain ((D.C c).Y.presheaf.stalk (D.C c).y) := (D.C c).isDomain
  letI fieldComponent : Field (FractionRing ((D.C c).Y.presheaf.stalk (D.C c).y)) := @FractionRing.field ((D.C c).Y.presheaf.stalk (D.C c).y) rComponent domainComponent
  intro φ hφloc hφR algF₀F hTowO₀
  letI : Algebra R ((D.C c).Y.presheaf.stalk (D.C c).y) := (D.C c).algebra
  letI : Algebra K (FractionRing ((D.C c).Y.presheaf.stalk (D.C c).y)) := (D.C c).algebraK
  letI : IsScalarTower R K (FractionRing ((D.C c).Y.presheaf.stalk (D.C c).y)) := (D.C c).isScalarTower
  letI : Algebra (FractionRing ((D.C c).Y.presheaf.stalk (D.C c).y)) (FractionRing ((U₀ : Scheme.{u}).presheaf.stalk ηU)) := algF₀F
  letI algO₀O : Algebra ((D.C c).Y.presheaf.stalk (D.C c).y) ((U₀ : Scheme.{u}).presheaf.stalk ηU) := ((algebraMap (X.presheaf.stalk ((pullback.snd z f).base (U₀.ι.base ηU))) ((U₀ : Scheme.{u}).presheaf.stalk ηU)).comp φ).toAlgebra
  let F := FractionRing ((U₀ : Scheme.{u}).presheaf.stalk ηU)
  haveI originalComponentFractionOpen : IsScalarTower ((D.C c).Y.presheaf.stalk (D.C c).y) (FractionRing ((D.C c).Y.presheaf.stalk (D.C c).y)) F := @IsScalarTower.of_algebraMap_eq ((D.C c).Y.presheaf.stalk (D.C c).y) (FractionRing ((D.C c).Y.presheaf.stalk (D.C c).y)) F
    rComponent.toCommSemiring fieldComponent.toCommRing.toCommSemiring fieldOpen.toSemiring
    (inferInstance : Algebra ((D.C c).Y.presheaf.stalk (D.C c).y) (FractionRing ((D.C c).Y.presheaf.stalk (D.C c).y))) algF₀F (inferInstance : Algebra ((D.C c).Y.presheaf.stalk (D.C c).y) F) (fun x => by
      have h := @IsScalarTower.algebraMap_apply ((D.C c).Y.presheaf.stalk (D.C c).y) (FractionRing ((D.C c).Y.presheaf.stalk (D.C c).y)) F
        rComponent.toCommSemiring fieldComponent.toCommRing.toCommSemiring fieldOpen.toSemiring
        (inferInstance : Algebra ((D.C c).Y.presheaf.stalk (D.C c).y) (FractionRing ((D.C c).Y.presheaf.stalk (D.C c).y))) algF₀F
        (((algebraMap (X.presheaf.stalk ((pullback.snd z f).base (U₀.ι.base ηU))) F).comp φ).toAlgebra) hTowO₀ x
      rw [← h, IsScalarTower.algebraMap_apply ((D.C c).Y.presheaf.stalk (D.C c).y) ((U₀ : Scheme.{u}).presheaf.stalk ηU) F x]
      show _ = (algebraMap (X.presheaf.stalk ((pullback.snd z f).base (U₀.ι.base ηU))) F) (φ x)
      rw [IsScalarTower.algebraMap_apply (X.presheaf.stalk ((pullback.snd z f).base (U₀.ι.base ηU))) ((U₀ : Scheme.{u}).presheaf.stalk ηU) F (φ x)]
      rfl)
  haveI originalRComponentOpen : IsScalarTower R ((D.C c).Y.presheaf.stalk (D.C c).y) ((U₀ : Scheme.{u}).presheaf.stalk ηU) := @IsScalarTower.of_algebraMap_eq R ((D.C c).Y.presheaf.stalk (D.C c).y) ((U₀ : Scheme.{u}).presheaf.stalk ηU)
    rBase.toCommSemiring rComponent.toCommSemiring rOpen.toSemiring
    (D.C c).algebra algO₀O algRO (fun r => by
      show algebraMap R ((U₀ : Scheme.{u}).presheaf.stalk ηU) r = algebraMap (X.presheaf.stalk ((pullback.snd z f).base (U₀.ι.base ηU))) ((U₀ : Scheme.{u}).presheaf.stalk ηU) (φ (algebraMap R ((D.C c).Y.presheaf.stalk (D.C c).y) r))
      rw [← RingHom.comp_apply φ, hφR, ← IsScalarTower.algebraMap_apply R (X.presheaf.stalk ((pullback.snd z f).base (U₀.ι.base ηU))) ((U₀ : Scheme.{u}).presheaf.stalk ηU)])
  haveI originalRComponentField : IsScalarTower R ((D.C c).Y.presheaf.stalk (D.C c).y) F := @IsScalarTower.of_algebraMap_eq R ((D.C c).Y.presheaf.stalk (D.C c).y) F
    rBase.toCommSemiring rComponent.toCommSemiring fieldOpen.toSemiring
    (D.C c).algebra (inferInstance : Algebra ((D.C c).Y.presheaf.stalk (D.C c).y) F) (inferInstance : Algebra R F) (fun x => by
      rw [IsScalarTower.algebraMap_apply ((D.C c).Y.presheaf.stalk (D.C c).y) ((U₀ : Scheme.{u}).presheaf.stalk ηU) F, IsScalarTower.algebraMap_apply R ((U₀ : Scheme.{u}).presheaf.stalk ηU) F,
        ← IsScalarTower.algebraMap_apply R ((D.C c).Y.presheaf.stalk (D.C c).y) ((U₀ : Scheme.{u}).presheaf.stalk ηU)])
  haveI originalComponentOpenLocal : IsLocalHom (algebraMap ((D.C c).Y.presheaf.stalk (D.C c).y) ((U₀ : Scheme.{u}).presheaf.stalk ηU)) :=
    @RingHom.isLocalHom_comp ((D.C c).Y.presheaf.stalk (D.C c).y) (X.presheaf.stalk ((pullback.snd z f).base (U₀.ι.base ηU))) ((U₀ : Scheme.{u}).presheaf.stalk ηU)
    rComponent.toSemiring rXStalk.toSemiring rOpen.toSemiring
    ((U₀.ι ≫ pullback.snd z f).stalkMap ηU).hom φ
    (inferInstance : IsLocalHom ((U₀.ι ≫ pullback.snd z f).stalkMap ηU).hom) hφloc
  obtain ⟨hdomO₀, hdvrO₀, hlocO₀, hidxO₀⟩ :=
    @NeronModelInfra.isIndexOneExtension_stalk_of_smooth_of_forall_specializes
      R rBase domainBase dvrBase (D.C c).Y (D.C c).f (D.C c).smooth
      (D.C c).y (D.C c).hy (D.C c).hmax (D.C c).algebra (D.C c).halg
  exact ⟨originalComponentFractionOpen, originalRComponentOpen, originalRComponentField,
    originalComponentOpenLocal, hdomO₀, hdvrO₀, hlocO₀, hidxO₀⟩

theorem component_chart_delta_zero_bijective
    {R : Type u} [rBase : CommRing R] [domainBase : IsDomain R] [dvrBase : IsDiscreteValuationRing R]
    (K : Type u) [givenK : Field K] [aRK : Algebra R K]
    {XK : Scheme.{u}} {gK : XK ⟶ Spec (CommRingCat.of K)}
    (d : ℕ)
    (ω : Γ((ZInQ.Contrib.CloudR2NeronExistence.Henselian.AlgebraicGeometry.Scheme.Hom.topDifferentials gK) d, ⊤))
    (D : MinimalComponentData R K gK d ω)
    (X : Scheme.{u}) (f : X ⟶ Spec (CommRingCat.of R))
    (Z : Scheme.{u}) (z : Z ⟶ Spec (CommRingCat.of R))
    (T : ComponentReading R K gK d ω)
    (η : ↑(pullback z f)) (U₀ : (pullback z f).Opens) (hηU : η ∈ U₀)
    (v : (U₀ : Scheme.{u}) ⟶ pullback z T.f)
    (hv₁ : v ≫ pullback.fst z T.f = U₀.ι ≫ pullback.fst z f) :
    let ηU : ↥U₀ := ⟨η, hηU⟩;
    let η' : ↥(pullback z T.f) := v.base ηU;
    let ζ₀ : ↥Z := (pullback.fst z T.f).base η';
    letI rOpen : CommRing ((U₀ : Scheme.{u}).presheaf.stalk ηU) := _root_.CommRingCat.commRing ((U₀ : Scheme.{u}).presheaf.stalk ηU);
    letI rPrime : CommRing (Z.presheaf.stalk ζ₀) := _root_.CommRingCat.commRing (Z.presheaf.stalk ζ₀);
    letI rPullback : CommRing ((pullback z T.f).presheaf.stalk η') := _root_.CommRingCat.commRing ((pullback z T.f).presheaf.stalk η');
    letI rXStalk : CommRing (X.presheaf.stalk ((pullback.snd z f).base (U₀.ι.base ηU))) := _root_.CommRingCat.commRing (X.presheaf.stalk ((pullback.snd z f).base (U₀.ι.base ηU)));
    letI algR'O' : Algebra (Z.presheaf.stalk ζ₀) ((pullback z T.f).presheaf.stalk η') := ((pullback.fst z T.f).stalkMap η').hom.toAlgebra;
    letI algO'O : Algebra ((pullback z T.f).presheaf.stalk η') ((U₀ : Scheme.{u}).presheaf.stalk ηU) := (v.stalkMap ηU).hom.toAlgebra;
    letI algR'O : Algebra (Z.presheaf.stalk ζ₀) ((U₀ : Scheme.{u}).presheaf.stalk ηU) :=
      ((v.stalkMap ηU).hom.comp ((pullback.fst z T.f).stalkMap η').hom).toAlgebra;
    letI algRR' : Algebra R (Z.presheaf.stalk ζ₀) := stalkAlgebra z ζ₀;
    letI algRO : Algebra R ((U₀ : Scheme.{u}).presheaf.stalk ηU) := ((algebraMap (Z.presheaf.stalk ζ₀) ((U₀ : Scheme.{u}).presheaf.stalk ηU)).comp (algebraMap R (Z.presheaf.stalk ζ₀))).toAlgebra;
    letI algRX : Algebra R (X.presheaf.stalk ((pullback.snd z f).base (U₀.ι.base ηU))) := stalkAlgebra f ((pullback.snd z f).base (U₀.ι.base ηU));
    letI algXO : Algebra (X.presheaf.stalk ((pullback.snd z f).base (U₀.ι.base ηU))) ((U₀ : Scheme.{u}).presheaf.stalk ηU) := ((U₀.ι ≫ pullback.snd z f).stalkMap ηU).hom.toAlgebra;
    ∀ (c : D.ι),
    letI rComponent : CommRing ((D.C c).Y.presheaf.stalk (D.C c).y) := _root_.CommRingCat.commRing ((D.C c).Y.presheaf.stalk (D.C c).y);
    ∀ (φ : ((D.C c).Y.presheaf.stalk (D.C c).y) →+* (X.presheaf.stalk ((pullback.snd z f).base (U₀.ι.base ηU)))) (hφbij : Function.Bijective φ) (hφR : letI := (D.C c).algebra;
        φ.comp (algebraMap R ((D.C c).Y.presheaf.stalk (D.C c).y)) = algebraMap R (X.presheaf.stalk ((pullback.snd z f).base (U₀.ι.base ηU)))),
    letI : Algebra R ((D.C c).Y.presheaf.stalk (D.C c).y) := (D.C c).algebra;
    letI algO₀O : Algebra ((D.C c).Y.presheaf.stalk (D.C c).y) ((U₀ : Scheme.{u}).presheaf.stalk ηU) := ((algebraMap (X.presheaf.stalk ((pullback.snd z f).base (U₀.ι.base ηU))) ((U₀ : Scheme.{u}).presheaf.stalk ηU)).comp φ).toAlgebra;
    ∀ (halgZ : Z.fromSpecStalk ζ₀ ≫ z = Spec.map (CommRingCat.ofHom (algebraMap R (Z.presheaf.stalk ζ₀)))) (halgX : X.fromSpecStalk ((pullback.snd z f).base (U₀.ι.base ηU)) ≫ f =
        Spec.map (CommRingCat.ofHom (algebraMap R (X.presheaf.stalk ((pullback.snd z f).base (U₀.ι.base ηU)))))) (originalRPrimeOpen : IsScalarTower R (Z.presheaf.stalk ζ₀) ((U₀ : Scheme.{u}).presheaf.stalk ηU)) (originalRComponentOpen : IsScalarTower R ((D.C c).Y.presheaf.stalk (D.C c).y) ((U₀ : Scheme.{u}).presheaf.stalk ηU)),
    letI : IsScalarTower R (Z.presheaf.stalk ζ₀) ((U₀ : Scheme.{u}).presheaf.stalk ηU) := originalRPrimeOpen;
    letI : IsScalarTower R ((D.C c).Y.presheaf.stalk (D.C c).y) ((U₀ : Scheme.{u}).presheaf.stalk ηU) := originalRComponentOpen;
    Function.Bijective
      ((KaehlerDifferential.map R (Z.presheaf.stalk ζ₀) ((U₀ : Scheme.{u}).presheaf.stalk ηU) ((U₀ : Scheme.{u}).presheaf.stalk ηU)).restrictScalars ((U₀ : Scheme.{u}).presheaf.stalk ηU) ∘ₗ
        KaehlerDifferential.mapBaseChange R ((D.C c).Y.presheaf.stalk (D.C c).y) ((U₀ : Scheme.{u}).presheaf.stalk ηU)) := by
  classical
  intro ηU η' ζ₀
  letI rOpen : CommRing ((U₀ : Scheme.{u}).presheaf.stalk ηU) := _root_.CommRingCat.commRing ((U₀ : Scheme.{u}).presheaf.stalk ηU)
  letI rPrime : CommRing (Z.presheaf.stalk ζ₀) := _root_.CommRingCat.commRing (Z.presheaf.stalk ζ₀)
  letI rPullback : CommRing ((pullback z T.f).presheaf.stalk η') := _root_.CommRingCat.commRing ((pullback z T.f).presheaf.stalk η')
  letI rXStalk : CommRing (X.presheaf.stalk ((pullback.snd z f).base (U₀.ι.base ηU))) := _root_.CommRingCat.commRing (X.presheaf.stalk ((pullback.snd z f).base (U₀.ι.base ηU)))
  letI algR'O' : Algebra (Z.presheaf.stalk ζ₀) ((pullback z T.f).presheaf.stalk η') := ((pullback.fst z T.f).stalkMap η').hom.toAlgebra
  letI algO'O : Algebra ((pullback z T.f).presheaf.stalk η') ((U₀ : Scheme.{u}).presheaf.stalk ηU) := (v.stalkMap ηU).hom.toAlgebra
  letI algR'O : Algebra (Z.presheaf.stalk ζ₀) ((U₀ : Scheme.{u}).presheaf.stalk ηU) :=
    ((v.stalkMap ηU).hom.comp ((pullback.fst z T.f).stalkMap η').hom).toAlgebra
  letI algRR' : Algebra R (Z.presheaf.stalk ζ₀) := stalkAlgebra z ζ₀
  letI algRO : Algebra R ((U₀ : Scheme.{u}).presheaf.stalk ηU) := ((algebraMap (Z.presheaf.stalk ζ₀) ((U₀ : Scheme.{u}).presheaf.stalk ηU)).comp (algebraMap R (Z.presheaf.stalk ζ₀))).toAlgebra
  letI algRX : Algebra R (X.presheaf.stalk ((pullback.snd z f).base (U₀.ι.base ηU))) := stalkAlgebra f ((pullback.snd z f).base (U₀.ι.base ηU))
  letI algXO : Algebra (X.presheaf.stalk ((pullback.snd z f).base (U₀.ι.base ηU))) ((U₀ : Scheme.{u}).presheaf.stalk ηU) := ((U₀.ι ≫ pullback.snd z f).stalkMap ηU).hom.toAlgebra
  intro c
  letI rComponent : CommRing ((D.C c).Y.presheaf.stalk (D.C c).y) := _root_.CommRingCat.commRing ((D.C c).Y.presheaf.stalk (D.C c).y)
  intro φ hφbij hφR
  letI : Algebra R ((D.C c).Y.presheaf.stalk (D.C c).y) := (D.C c).algebra
  letI algO₀O : Algebra ((D.C c).Y.presheaf.stalk (D.C c).y) ((U₀ : Scheme.{u}).presheaf.stalk ηU) := ((algebraMap (X.presheaf.stalk ((pullback.snd z f).base (U₀.ι.base ηU))) ((U₀ : Scheme.{u}).presheaf.stalk ηU)).comp φ).toAlgebra
  intro halgZ halgX originalRPrimeOpen originalRComponentOpen
  letI : IsScalarTower R (Z.presheaf.stalk ζ₀) ((U₀ : Scheme.{u}).presheaf.stalk ηU) := originalRPrimeOpen
  letI : IsScalarTower R ((D.C c).Y.presheaf.stalk (D.C c).y) ((U₀ : Scheme.{u}).presheaf.stalk ηU) := originalRComponentOpen
  exact @T3Glue.bijective_map_comp_mapBaseChange_stalk_of_isOpenImmersion
    R rBase X Z (U₀ : Scheme.{u}) f z U₀.ι
    (inferInstance : IsOpenImmersion U₀.ι) ηU
    (v ≫ pullback.fst z T.f) hv₁ ζ₀ rfl algRR' halgZ algRX halgX
    ((D.C c).Y.presheaf.stalk (D.C c).y) rComponent (D.C c).algebra φ hφbij hφR algRO algR'O algO₀O
    (fun a => by
      rw [Scheme.Hom.stalkMap_comp]
      simp [TopCat.Presheaf.stalkCongr_hom, TopCat.Presheaf.stalkSpecializes_refl]
      rfl)
    (fun b => rfl) originalRPrimeOpen originalRComponentOpen

theorem component_chart_section_field_towers
    {R : Type u} [rBase : CommRing R] [domainBase : IsDomain R] [dvrBase : IsDiscreteValuationRing R]
    (K : Type u) [givenK : Field K] [aRK : Algebra R K]
    {XK : Scheme.{u}} {gK : XK ⟶ Spec (CommRingCat.of K)}
    (d : ℕ)
    (ω : Γ((ZInQ.Contrib.CloudR2NeronExistence.Henselian.AlgebraicGeometry.Scheme.Hom.topDifferentials gK) d, ⊤))
    (D : MinimalComponentData R K gK d ω)
    (X : Scheme.{u}) (f : X ⟶ Spec (CommRingCat.of R))
    (Z : Scheme.{u}) (z : Z ⟶ Spec (CommRingCat.of R))
    (η : ↑(pullback z f)) (U₀ : (pullback z f).Opens) (hηU : η ∈ U₀) :
    let ηU : ↥U₀ := ⟨η, hηU⟩;
    letI rOpen : CommRing ((U₀ : Scheme.{u}).presheaf.stalk ηU) := _root_.CommRingCat.commRing ((U₀ : Scheme.{u}).presheaf.stalk ηU);
    ∀ (hdomO : IsDomain ((U₀ : Scheme.{u}).presheaf.stalk ηU)),
    letI : IsDomain ((U₀ : Scheme.{u}).presheaf.stalk ηU) := hdomO;
    letI fieldOpen : Field (FractionRing ((U₀ : Scheme.{u}).presheaf.stalk ηU)) := @FractionRing.field ((U₀ : Scheme.{u}).presheaf.stalk ηU) rOpen hdomO;
    ∀ (algKF : Algebra K (FractionRing ((U₀ : Scheme.{u}).presheaf.stalk ηU))),
    letI : Algebra K (FractionRing ((U₀ : Scheme.{u}).presheaf.stalk ηU)) := algKF;
    ∀ (c : D.ι),
    letI rComponent : CommRing ((D.C c).Y.presheaf.stalk (D.C c).y) := _root_.CommRingCat.commRing ((D.C c).Y.presheaf.stalk (D.C c).y);
    letI domainComponent : IsDomain ((D.C c).Y.presheaf.stalk (D.C c).y) := (D.C c).isDomain;
    letI fieldComponent : Field (FractionRing ((D.C c).Y.presheaf.stalk (D.C c).y)) := @FractionRing.field ((D.C c).Y.presheaf.stalk (D.C c).y) rComponent domainComponent;
    letI rSections : CommRing Γ(XK, (D.C c).U) := _root_.CommRingCat.commRing Γ(XK, (D.C c).U);
    ∀ (algF₀F : Algebra (FractionRing ((D.C c).Y.presheaf.stalk (D.C c).y)) (FractionRing ((U₀ : Scheme.{u}).presheaf.stalk ηU))) (hTowK : letI := (D.C c).algebraK; IsScalarTower K (FractionRing ((D.C c).Y.presheaf.stalk (D.C c).y)) (FractionRing ((U₀ : Scheme.{u}).presheaf.stalk ηU))),
    letI : Algebra R ((D.C c).Y.presheaf.stalk (D.C c).y) := (D.C c).algebra;
    letI : Algebra K (FractionRing ((D.C c).Y.presheaf.stalk (D.C c).y)) := (D.C c).algebraK;
    letI : IsScalarTower R K (FractionRing ((D.C c).Y.presheaf.stalk (D.C c).y)) := (D.C c).isScalarTower;
    letI : Algebra (FractionRing ((D.C c).Y.presheaf.stalk (D.C c).y)) (FractionRing ((U₀ : Scheme.{u}).presheaf.stalk ηU)) := algF₀F;
    letI : letI := (D.C c).algebraK; IsScalarTower K (FractionRing ((D.C c).Y.presheaf.stalk (D.C c).y)) (FractionRing ((U₀ : Scheme.{u}).presheaf.stalk ηU)) := hTowK;
    letI := (ZInQ.Contrib.CloudR2NeronExistence.Henselian.AlgebraicGeometry.Scheme.Hom.sectionsAlgebra gK) (D.C c).U;
    letI := (D.C c).algebraU;
    letI algUcF : Algebra Γ(XK, (D.C c).U) (FractionRing ((U₀ : Scheme.{u}).presheaf.stalk ηU)) :=
      ((algebraMap (FractionRing ((D.C c).Y.presheaf.stalk (D.C c).y)) (FractionRing ((U₀ : Scheme.{u}).presheaf.stalk ηU))).comp (algebraMap Γ(XK, (D.C c).U) (FractionRing ((D.C c).Y.presheaf.stalk (D.C c).y)))).toAlgebra;
    ∃ (hKUc : IsScalarTower K Γ(XK, (D.C c).U) (FractionRing ((U₀ : Scheme.{u}).presheaf.stalk ηU))),
    IsScalarTower Γ(XK, (D.C c).U) (FractionRing ((D.C c).Y.presheaf.stalk (D.C c).y)) (FractionRing ((U₀ : Scheme.{u}).presheaf.stalk ηU)) := by
  classical
  intro ηU
  letI rOpen : CommRing ((U₀ : Scheme.{u}).presheaf.stalk ηU) := _root_.CommRingCat.commRing ((U₀ : Scheme.{u}).presheaf.stalk ηU)
  intro hdomO
  letI : IsDomain ((U₀ : Scheme.{u}).presheaf.stalk ηU) := hdomO
  letI fieldOpen : Field (FractionRing ((U₀ : Scheme.{u}).presheaf.stalk ηU)) := @FractionRing.field ((U₀ : Scheme.{u}).presheaf.stalk ηU) rOpen hdomO
  intro algKF
  letI : Algebra K (FractionRing ((U₀ : Scheme.{u}).presheaf.stalk ηU)) := algKF
  intro c
  letI rComponent : CommRing ((D.C c).Y.presheaf.stalk (D.C c).y) := _root_.CommRingCat.commRing ((D.C c).Y.presheaf.stalk (D.C c).y)
  letI domainComponent : IsDomain ((D.C c).Y.presheaf.stalk (D.C c).y) := (D.C c).isDomain
  letI fieldComponent : Field (FractionRing ((D.C c).Y.presheaf.stalk (D.C c).y)) := @FractionRing.field ((D.C c).Y.presheaf.stalk (D.C c).y) rComponent domainComponent
  letI rSections : CommRing Γ(XK, (D.C c).U) := _root_.CommRingCat.commRing Γ(XK, (D.C c).U)
  intro algF₀F hTowK
  letI : Algebra R ((D.C c).Y.presheaf.stalk (D.C c).y) := (D.C c).algebra
  letI : Algebra K (FractionRing ((D.C c).Y.presheaf.stalk (D.C c).y)) := (D.C c).algebraK
  letI : IsScalarTower R K (FractionRing ((D.C c).Y.presheaf.stalk (D.C c).y)) := (D.C c).isScalarTower
  letI : Algebra (FractionRing ((D.C c).Y.presheaf.stalk (D.C c).y)) (FractionRing ((U₀ : Scheme.{u}).presheaf.stalk ηU)) := algF₀F
  letI : letI := (D.C c).algebraK; IsScalarTower K (FractionRing ((D.C c).Y.presheaf.stalk (D.C c).y)) (FractionRing ((U₀ : Scheme.{u}).presheaf.stalk ηU)) := hTowK
  letI := (ZInQ.Contrib.CloudR2NeronExistence.Henselian.AlgebraicGeometry.Scheme.Hom.sectionsAlgebra gK) (D.C c).U
  letI := (D.C c).algebraU
  letI algUcF : Algebra Γ(XK, (D.C c).U) (FractionRing ((U₀ : Scheme.{u}).presheaf.stalk ηU)) :=
    ((algebraMap (FractionRing ((D.C c).Y.presheaf.stalk (D.C c).y)) (FractionRing ((U₀ : Scheme.{u}).presheaf.stalk ηU))).comp (algebraMap Γ(XK, (D.C c).U) (FractionRing ((D.C c).Y.presheaf.stalk (D.C c).y)))).toAlgebra
  let F := FractionRing ((U₀ : Scheme.{u}).presheaf.stalk ηU)
  have hKUc : IsScalarTower K Γ(XK, (D.C c).U) F := @IsScalarTower.of_algebraMap_eq K Γ(XK, (D.C c).U) F
    givenK.toCommRing.toCommSemiring rSections.toCommSemiring fieldOpen.toSemiring
    ((ZInQ.Contrib.CloudR2NeronExistence.Henselian.AlgebraicGeometry.Scheme.Hom.sectionsAlgebra gK) (D.C c).U) algUcF algKF (fun x => by
      show algebraMap K F x = algebraMap (FractionRing ((D.C c).Y.presheaf.stalk (D.C c).y)) F (algebraMap Γ(XK, (D.C c).U) (FractionRing ((D.C c).Y.presheaf.stalk (D.C c).y)) (algebraMap K Γ(XK, (D.C c).U) x))
      rw [← @IsScalarTower.algebraMap_apply K Γ(XK, (D.C c).U) (FractionRing ((D.C c).Y.presheaf.stalk (D.C c).y))
        givenK.toCommRing.toCommSemiring rSections.toCommSemiring fieldComponent.toSemiring
        ((ZInQ.Contrib.CloudR2NeronExistence.Henselian.AlgebraicGeometry.Scheme.Hom.sectionsAlgebra gK) (D.C c).U)
        (D.C c).algebraU (D.C c).algebraK (D.C c).isScalarTowerU x, ← IsScalarTower.algebraMap_apply K (FractionRing ((D.C c).Y.presheaf.stalk (D.C c).y)) F])
  haveI := hKUc
  have towUcF₀F : IsScalarTower Γ(XK, (D.C c).U) (FractionRing ((D.C c).Y.presheaf.stalk (D.C c).y)) F := @IsScalarTower.of_algebraMap_eq Γ(XK, (D.C c).U) (FractionRing ((D.C c).Y.presheaf.stalk (D.C c).y)) F
    rSections.toCommSemiring fieldComponent.toCommRing.toCommSemiring fieldOpen.toSemiring
    (D.C c).algebraU algF₀F algUcF (fun _ => rfl)
  exact ⟨hKUc, towUcF₀F⟩

theorem component_chart_reading_image
    {R : Type u} [rBase : CommRing R] [domainBase : IsDomain R] [dvrBase : IsDiscreteValuationRing R]
    (K : Type u) [givenK : Field K] [aRK : Algebra R K]
    {XK : Scheme.{u}} {gK : XK ⟶ Spec (CommRingCat.of K)}
    (d : ℕ)
    (ω : Γ((ZInQ.Contrib.CloudR2NeronExistence.Henselian.AlgebraicGeometry.Scheme.Hom.topDifferentials gK) d, ⊤))
    (D : MinimalComponentData R K gK d ω)
    (X : Scheme.{u}) (f : X ⟶ Spec (CommRingCat.of R))
    (Z : Scheme.{u}) (z : Z ⟶ Spec (CommRingCat.of R))
    (T : ComponentReading R K gK d ω)
    (η : ↑(pullback z f)) (U₀ : (pullback z f).Opens) (hηU : η ∈ U₀)
    (v : (U₀ : Scheme.{u}) ⟶ pullback z T.f) :
    let ηU : ↥U₀ := ⟨η, hηU⟩;
    let η' : ↥(pullback z T.f) := v.base ηU;
    let ζ₀ : ↥Z := (pullback.fst z T.f).base η';
    letI rOpen : CommRing ((U₀ : Scheme.{u}).presheaf.stalk ηU) := _root_.CommRingCat.commRing ((U₀ : Scheme.{u}).presheaf.stalk ηU);
    letI rPrime : CommRing (Z.presheaf.stalk ζ₀) := _root_.CommRingCat.commRing (Z.presheaf.stalk ζ₀);
    ∀ (hdomO : IsDomain ((U₀ : Scheme.{u}).presheaf.stalk ηU)) (hdomR' : IsDomain (Z.presheaf.stalk ζ₀)),
    letI : IsDomain ((U₀ : Scheme.{u}).presheaf.stalk ηU) := hdomO;
    letI fieldOpen : Field (FractionRing ((U₀ : Scheme.{u}).presheaf.stalk ηU)) := @FractionRing.field ((U₀ : Scheme.{u}).presheaf.stalk ηU) rOpen hdomO;
    letI : IsDomain (Z.presheaf.stalk ζ₀) := hdomR';
    letI fieldPrime : Field (FractionRing (Z.presheaf.stalk ζ₀)) := @FractionRing.field (Z.presheaf.stalk ζ₀) rPrime hdomR';
    ∀ (algKF : Algebra K (FractionRing ((U₀ : Scheme.{u}).presheaf.stalk ηU))) (algKK' : Algebra K (FractionRing (Z.presheaf.stalk ζ₀))) (algK'F : Algebra (FractionRing (Z.presheaf.stalk ζ₀)) (FractionRing ((U₀ : Scheme.{u}).presheaf.stalk ηU))),
    letI : Algebra K (FractionRing ((U₀ : Scheme.{u}).presheaf.stalk ηU)) := algKF;
    letI : Algebra K (FractionRing (Z.presheaf.stalk ζ₀)) := algKK';
    letI : Algebra (FractionRing (Z.presheaf.stalk ζ₀)) (FractionRing ((U₀ : Scheme.{u}).presheaf.stalk ηU)) := algK'F;
    ∀ (c : D.ι),
    letI rComponent : CommRing ((D.C c).Y.presheaf.stalk (D.C c).y) := _root_.CommRingCat.commRing ((D.C c).Y.presheaf.stalk (D.C c).y);
    letI domainComponent : IsDomain ((D.C c).Y.presheaf.stalk (D.C c).y) := (D.C c).isDomain;
    letI fieldComponent : Field (FractionRing ((D.C c).Y.presheaf.stalk (D.C c).y)) := @FractionRing.field ((D.C c).Y.presheaf.stalk (D.C c).y) rComponent domainComponent;
    letI rSections : CommRing Γ(XK, (D.C c).U) := _root_.CommRingCat.commRing Γ(XK, (D.C c).U);
    ∀ (algF₀F : Algebra (FractionRing ((D.C c).Y.presheaf.stalk (D.C c).y)) (FractionRing ((U₀ : Scheme.{u}).presheaf.stalk ηU))) (hTowK : letI := (D.C c).algebraK; IsScalarTower K (FractionRing ((D.C c).Y.presheaf.stalk (D.C c).y)) (FractionRing ((U₀ : Scheme.{u}).presheaf.stalk ηU))) (originalKKprimeOpen : IsScalarTower K (FractionRing (Z.presheaf.stalk ζ₀)) (FractionRing ((U₀ : Scheme.{u}).presheaf.stalk ηU))),
    letI : Algebra R ((D.C c).Y.presheaf.stalk (D.C c).y) := (D.C c).algebra;
    letI : Algebra K (FractionRing ((D.C c).Y.presheaf.stalk (D.C c).y)) := (D.C c).algebraK;
    letI : IsScalarTower R K (FractionRing ((D.C c).Y.presheaf.stalk (D.C c).y)) := (D.C c).isScalarTower;
    letI : Algebra (FractionRing ((D.C c).Y.presheaf.stalk (D.C c).y)) (FractionRing ((U₀ : Scheme.{u}).presheaf.stalk ηU)) := algF₀F;
    letI : letI := (D.C c).algebraK; IsScalarTower K (FractionRing ((D.C c).Y.presheaf.stalk (D.C c).y)) (FractionRing ((U₀ : Scheme.{u}).presheaf.stalk ηU)) := hTowK;
    letI : IsScalarTower K (FractionRing (Z.presheaf.stalk ζ₀)) (FractionRing ((U₀ : Scheme.{u}).presheaf.stalk ηU)) := originalKKprimeOpen;
    letI := (ZInQ.Contrib.CloudR2NeronExistence.Henselian.AlgebraicGeometry.Scheme.Hom.sectionsAlgebra gK) (D.C c).U;
    letI := (D.C c).algebraU;
    letI algUcF : Algebra Γ(XK, (D.C c).U) (FractionRing ((U₀ : Scheme.{u}).presheaf.stalk ηU)) :=
      ((algebraMap (FractionRing ((D.C c).Y.presheaf.stalk (D.C c).y)) (FractionRing ((U₀ : Scheme.{u}).presheaf.stalk ηU))).comp (algebraMap Γ(XK, (D.C c).U) (FractionRing ((D.C c).Y.presheaf.stalk (D.C c).y)))).toAlgebra;
    ∀ (hKUc : IsScalarTower K Γ(XK, (D.C c).U) (FractionRing ((U₀ : Scheme.{u}).presheaf.stalk ηU))) (towUcF₀F : IsScalarTower Γ(XK, (D.C c).U) (FractionRing ((D.C c).Y.presheaf.stalk (D.C c).y)) (FractionRing ((U₀ : Scheme.{u}).presheaf.stalk ηU))),
    letI : IsScalarTower K Γ(XK, (D.C c).U) (FractionRing ((U₀ : Scheme.{u}).presheaf.stalk ηU)) := hKUc;
    letI : IsScalarTower Γ(XK, (D.C c).U) (FractionRing ((D.C c).Y.presheaf.stalk (D.C c).y)) (FractionRing ((U₀ : Scheme.{u}).presheaf.stalk ηU)) := towUcF₀F;
    letI : IsScalarTower K Γ(XK, (D.C c).U) (FractionRing ((D.C c).Y.presheaf.stalk (D.C c).y)) := (D.C c).isScalarTowerU;
    (TopFormOrder.topFormMap K (FractionRing (Z.presheaf.stalk ζ₀)) Γ(XK, (D.C c).U) (FractionRing ((U₀ : Scheme.{u}).presheaf.stalk ηU)) d (D.C c).ωU =
      TopFormOrder.topFormMap K (FractionRing (Z.presheaf.stalk ζ₀)) (FractionRing ((D.C c).Y.presheaf.stalk (D.C c).y)) (FractionRing ((U₀ : Scheme.{u}).presheaf.stalk ηU)) d
        ((D.C c).a • TopFormOrder.topFormMap R K ((D.C c).Y.presheaf.stalk (D.C c).y) (FractionRing ((D.C c).Y.presheaf.stalk (D.C c).y)) d
          (exteriorPower.ιMulti ((D.C c).Y.presheaf.stalk (D.C c).y) d (D.C c).b))) := by
  classical
  intro ηU η' ζ₀
  letI rOpen : CommRing ((U₀ : Scheme.{u}).presheaf.stalk ηU) := _root_.CommRingCat.commRing ((U₀ : Scheme.{u}).presheaf.stalk ηU)
  letI rPrime : CommRing (Z.presheaf.stalk ζ₀) := _root_.CommRingCat.commRing (Z.presheaf.stalk ζ₀)
  intro hdomO hdomR'
  letI : IsDomain ((U₀ : Scheme.{u}).presheaf.stalk ηU) := hdomO
  letI fieldOpen : Field (FractionRing ((U₀ : Scheme.{u}).presheaf.stalk ηU)) := @FractionRing.field ((U₀ : Scheme.{u}).presheaf.stalk ηU) rOpen hdomO
  letI : IsDomain (Z.presheaf.stalk ζ₀) := hdomR'
  letI fieldPrime : Field (FractionRing (Z.presheaf.stalk ζ₀)) := @FractionRing.field (Z.presheaf.stalk ζ₀) rPrime hdomR'
  intro algKF algKK' algK'F
  letI : Algebra K (FractionRing ((U₀ : Scheme.{u}).presheaf.stalk ηU)) := algKF
  letI : Algebra K (FractionRing (Z.presheaf.stalk ζ₀)) := algKK'
  letI : Algebra (FractionRing (Z.presheaf.stalk ζ₀)) (FractionRing ((U₀ : Scheme.{u}).presheaf.stalk ηU)) := algK'F
  intro c
  letI rComponent : CommRing ((D.C c).Y.presheaf.stalk (D.C c).y) := _root_.CommRingCat.commRing ((D.C c).Y.presheaf.stalk (D.C c).y)
  letI domainComponent : IsDomain ((D.C c).Y.presheaf.stalk (D.C c).y) := (D.C c).isDomain
  letI fieldComponent : Field (FractionRing ((D.C c).Y.presheaf.stalk (D.C c).y)) := @FractionRing.field ((D.C c).Y.presheaf.stalk (D.C c).y) rComponent domainComponent
  letI rSections : CommRing Γ(XK, (D.C c).U) := _root_.CommRingCat.commRing Γ(XK, (D.C c).U)
  intro algF₀F hTowK originalKKprimeOpen
  letI : Algebra R ((D.C c).Y.presheaf.stalk (D.C c).y) := (D.C c).algebra
  letI : Algebra K (FractionRing ((D.C c).Y.presheaf.stalk (D.C c).y)) := (D.C c).algebraK
  letI : IsScalarTower R K (FractionRing ((D.C c).Y.presheaf.stalk (D.C c).y)) := (D.C c).isScalarTower
  letI : Algebra (FractionRing ((D.C c).Y.presheaf.stalk (D.C c).y)) (FractionRing ((U₀ : Scheme.{u}).presheaf.stalk ηU)) := algF₀F
  letI : letI := (D.C c).algebraK; IsScalarTower K (FractionRing ((D.C c).Y.presheaf.stalk (D.C c).y)) (FractionRing ((U₀ : Scheme.{u}).presheaf.stalk ηU)) := hTowK
  letI : IsScalarTower K (FractionRing (Z.presheaf.stalk ζ₀)) (FractionRing ((U₀ : Scheme.{u}).presheaf.stalk ηU)) := originalKKprimeOpen
  letI := (ZInQ.Contrib.CloudR2NeronExistence.Henselian.AlgebraicGeometry.Scheme.Hom.sectionsAlgebra gK) (D.C c).U
  letI := (D.C c).algebraU
  letI algUcF : Algebra Γ(XK, (D.C c).U) (FractionRing ((U₀ : Scheme.{u}).presheaf.stalk ηU)) :=
    ((algebraMap (FractionRing ((D.C c).Y.presheaf.stalk (D.C c).y)) (FractionRing ((U₀ : Scheme.{u}).presheaf.stalk ηU))).comp (algebraMap Γ(XK, (D.C c).U) (FractionRing ((D.C c).Y.presheaf.stalk (D.C c).y)))).toAlgebra
  intro hKUc towUcF₀F
  letI : IsScalarTower K Γ(XK, (D.C c).U) (FractionRing ((U₀ : Scheme.{u}).presheaf.stalk ηU)) := hKUc
  letI : IsScalarTower Γ(XK, (D.C c).U) (FractionRing ((D.C c).Y.presheaf.stalk (D.C c).y)) (FractionRing ((U₀ : Scheme.{u}).presheaf.stalk ηU)) := towUcF₀F
  letI : IsScalarTower K Γ(XK, (D.C c).U) (FractionRing ((D.C c).Y.presheaf.stalk (D.C c).y)) := (D.C c).isScalarTowerU
  let F := FractionRing ((U₀ : Scheme.{u}).presheaf.stalk ηU)
  let K' := FractionRing (Z.presheaf.stalk ζ₀)
  exact ConstructionInterface.component_image_from_reading_data_fixed K K'
    Γ(XK, (D.C c).U) (FractionRing ((D.C c).Y.presheaf.stalk (D.C c).y)) F
    (k0 := givenK) (k1 := fieldPrime) (rB := rSections)
    (e0 := fieldComponent) (f0 := fieldOpen) (a01 := algKK')
    (a0B := (ZInQ.Contrib.CloudR2NeronExistence.Henselian.AlgebraicGeometry.Scheme.Hom.sectionsAlgebra gK) (D.C c).U)
    (aBE := (D.C c).algebraU) (aEF := algF₀F) (aBF := algUcF)
    (a0E := (D.C c).algebraK) (a0F := algKF) (a1F := algK'F)
    (hBEF := towUcF₀F) (h0BE := (D.C c).isScalarTowerU)
    (h0EF := hTowK) (h01F := originalKKprimeOpen) (h0BF := hKUc) d
    (D.C c).ωU
    ((D.C c).a • TopFormOrder.topFormMap R K ((D.C c).Y.presheaf.stalk (D.C c).y)
      (FractionRing ((D.C c).Y.presheaf.stalk (D.C c).y)) d
        (exteriorPower.ιMulti ((D.C c).Y.presheaf.stalk (D.C c).y) d (D.C c).b))
    (D.C c).ha

end P2MW.S_NeronModelInfra_exists_n_eq_and_formallySmooth_stalk_of_isOmegaMinimal_of_genericFibreRestrict_comp_eq_mul
end ZInQ.Contrib.CloudR2NeronExistence.Henselian
