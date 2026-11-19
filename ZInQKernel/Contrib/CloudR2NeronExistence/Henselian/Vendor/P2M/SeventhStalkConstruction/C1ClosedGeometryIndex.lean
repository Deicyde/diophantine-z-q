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
theorem closed_geometry_and_index_construction    {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (K : Type u) [Field K] [Algebra R K] [IsFractionRing R K]
    {XK : Scheme.{u}} {gK : XK ⟶ Spec (CommRingCat.of K)}
    [Smooth gK] [IsSeparated gK] [LocallyOfFiniteType gK] [QuasiCompact gK]
    (LXK : RelativeGroupLaw K gK)
    (d : ℕ) [SmoothOfRelativeDimension d gK]
    (ω : Γ((ZInQ.Contrib.CloudR2NeronExistence.Henselian.AlgebraicGeometry.Scheme.Hom.topDifferentials gK) d, ⊤)) (hωframe : Scheme.Modules.IsFrameOn ω ⊤)
    (X : Scheme.{u}) (f : X ⟶ Spec (CommRingCat.of R))
    (e : SchemeHomOver (pullback.snd f (specGenericFibreInclusion R K)) gK)
    [Smooth f] [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f] [IsIso e.1]
    (Z : Scheme.{u}) (z : Z ⟶ Spec (CommRingCat.of R)) [Smooth z] [QuasiCompact z]
    (uK : SchemeHomOver (pullback.snd z (specGenericFibreInclusion R K)) gK)
    (η : ↑(pullback z f)) (hη : (pullback.fst z f ≫ z).base η = IsLocalRing.closedPoint R)
    (hmax : ∀ y : ↑(pullback z f), y ⤳ η → (pullback.fst z f ≫ z).base y = IsLocalRing.closedPoint R → y = η)
    (T : ComponentReading R K gK d ω)
    (U₀ : (pullback z f).Opens) (hηU : η ∈ U₀) (τ₀ : SchemeHomOver (U₀.ι ≫ pullback.fst z f ≫ z) T.f)
    (hτ₀ : (NeronModelInfra.schemeHomOverComp
              (genericFibreRestrict R K T.f (U₀.ι ≫ pullback.fst z f ≫ z) τ₀) T.e).1 =
            pullback.map (U₀.ι ≫ pullback.fst z f ≫ z) (specGenericFibreInclusion R K)
                (pullback.fst z f ≫ z) (specGenericFibreInclusion R K) U₀.ι (𝟙 _) (𝟙 _)
                (Category.comp_id _) ((Category.comp_id _).trans (Category.id_comp _).symm) ≫
              (LXK.mul (pullback.snd (pullback.fst z f ≫ z) (specGenericFibreInclusion R K))
                (NeronModelInfra.schemeHomOverComp
                  (genericFibreRestrict R K z (pullback.fst z f ≫ z) ⟨pullback.fst z f, rfl⟩) uK)
                (NeronModelInfra.schemeHomOverComp
                  (genericFibreRestrict R K f (pullback.fst z f ≫ z)
                    ⟨pullback.snd z f, pullback.condition.symm⟩) e)).1)
    (v : (U₀ : Scheme.{u}) ⟶ pullback z T.f) (hv₁ : v ≫ pullback.fst z T.f = U₀.ι ≫ pullback.fst z f)
    (hv₂ : v ≫ pullback.snd z T.f = τ₀.1)
    (hgen : T.y ⤳ τ₀.1.base ⟨η, hηU⟩)
    [aRZ : Algebra R (Z.presheaf.stalk ((pullback.fst z T.f).base (v.base ⟨η, hηU⟩)))]
    [aRU : Algebra R ((U₀ : Scheme.{u}).presheaf.stalk ⟨η, hηU⟩)]
    (halgZ : Z.fromSpecStalk ((pullback.fst z T.f).base (v.base ⟨η, hηU⟩)) ≫ z =
      Spec.map (CommRingCat.ofHom (algebraMap R (Z.presheaf.stalk ((pullback.fst z T.f).base (v.base ⟨η, hηU⟩))))))
    (halgO : (U₀ : Scheme.{u}).fromSpecStalk ⟨η, hηU⟩ ≫ (U₀.ι ≫ pullback.fst z f ≫ z) =
      Spec.map (CommRingCat.ofHom (algebraMap R ((U₀ : Scheme.{u}).presheaf.stalk ⟨η, hηU⟩)))) :
    let ηU : ↥U₀ := ⟨η, hηU⟩;
    let η' : ↥(pullback z T.f) := v.base ηU;
    let ζ₀ : ↥Z := (pullback.fst z T.f).base η';
    let y₁ : ↥T.Y := (pullback.snd z T.f).base η';
    (T.y ⤳ y₁) ∧
    (∀ y : ↥U₀, y ⤳ ηU → (U₀.ι ≫ pullback.fst z f ≫ z).base y = IsLocalRing.closedPoint R → y = ηU) ∧
    (T.f.base y₁ = IsLocalRing.closedPoint R) ∧
    (f.base ((pullback.snd z f).base (U₀.ι.base ηU)) = IsLocalRing.closedPoint R) ∧
    (∀ y : ↥X, y ⤳ ((pullback.snd z f).base (U₀.ι.base ηU)) → f.base y = IsLocalRing.closedPoint R →
      y = ((pullback.snd z f).base (U₀.ι.base ηU))) ∧
    (z.base ζ₀ = IsLocalRing.closedPoint R) ∧
    (∀ y : ↥Z, y ⤳ ζ₀ → z.base y = IsLocalRing.closedPoint R → y = ζ₀) ∧
    (∃ (domO : IsDomain ((U₀ : Scheme.{u}).presheaf.stalk ηU))
       (domO' : IsDomain ((pullback z T.f).presheaf.stalk η')),
      (letI : Algebra ((pullback z T.f).presheaf.stalk η') (FractionRing ((U₀ : Scheme.{u}).presheaf.stalk ηU)) :=
        ((algebraMap ((U₀ : Scheme.{u}).presheaf.stalk ηU) (FractionRing ((U₀ : Scheme.{u}).presheaf.stalk ηU))).comp
          (v.stalkMap ηU).hom).toAlgebra;
        IsFractionRing ((pullback z T.f).presheaf.stalk η') (FractionRing ((U₀ : Scheme.{u}).presheaf.stalk ηU))) ∧
      (∃ (_ : IsDomain ((U₀ : Scheme.{u}).presheaf.stalk ηU))
         (_ : IsDiscreteValuationRing ((U₀ : Scheme.{u}).presheaf.stalk ηU))
         (_ : IsLocalHom (algebraMap R ((U₀ : Scheme.{u}).presheaf.stalk ηU))),
        IsIndexOneExtension R ((U₀ : Scheme.{u}).presheaf.stalk ηU)) ∧
      (∃ (_ : IsDomain (Z.presheaf.stalk ζ₀)) (_ : IsDiscreteValuationRing (Z.presheaf.stalk ζ₀))
         (_ : IsLocalHom (algebraMap R (Z.presheaf.stalk ζ₀))),
        IsIndexOneExtension R (Z.presheaf.stalk ζ₀))) := by
  haveI : Smooth (pullback.fst z f) := inferInstance
  let ηU : ↥U₀ := ⟨η, hηU⟩
  let η' : ↥(pullback z T.f) := v.base ηU
  let ζ₀ : ↥Z := (pullback.fst z T.f).base η'
  let y₁ : ↥T.Y := (pullback.snd z T.f).base η'
  obtain ⟨hgen₁, hmaxU, hy₁sp, hξsp, hξmax, hζ₀sp, hζ₀max⟩ :=
    ConstructionInterface.closed_fibre_point_facts f z T U₀ η hηU hη hmax τ₀ v hv₁ hv₂ hgen
  obtain ⟨hdomO, hdomO', hfrac⟩ :=
    NeronModelInfra.isFractionRing_stalk_of_genericFibreRestrict_comp_eq_mul_of_pullback_lift
      K LXK d ω X f e Z z uK η T U₀ hηU τ₀ hτ₀ v hv₁ hv₂
  haveI := hdomO
  haveI := hdomO'
  obtain ⟨hIndexO, hIndexZ⟩ := ConstructionInterface.paired_closed_stalk_index_facts z
    (U₀.ι ≫ pullback.fst z f ≫ z) ζ₀ ηU
    (aRZ := aRZ) (aRU := aRU) hζ₀sp (by simpa using hη)
    hζ₀max hmaxU halgZ halgO
  exact ⟨hgen₁, hmaxU, hy₁sp, hξsp, hξmax, hζ₀sp, hζ₀max,
    ⟨hdomO, hdomO', hfrac, hIndexO, hIndexZ⟩⟩

end P2MW.S_NeronModelInfra_exists_n_eq_and_formallySmooth_stalk_of_isOmegaMinimal_of_genericFibreRestrict_comp_eq_mul
end ZInQ.Contrib.CloudR2NeronExistence.Henselian
