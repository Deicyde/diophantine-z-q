/-
Copyright (c) 2026 H5/NOS Round-2 lane4 contributors.
Released under Apache 2.0 license as described in the project LICENSE.

H5 scheme-only effective descent, route Q. This follows the Parent-approved plan
SCHEME_DESCENT_NATIVE_PLAN_001, sha 7a0aede9.

Sub-statement Q10: descent compatibility of a presentation by descended sections. If every
section of `𝔗` is carried to itself by the descent datum `ψ`, the two composites
`X'' ⇉ X' → ℙ^M_{S'} → ℙ^M_S` agree.

NATIVE assembly. SOURCE ONLY, UNCOMPILED. Universe u. The only option is autoImplicit false.

Suppliers:
* route-E edition `ProjPresentation.exists_baseChange_of_isPullback`;
* route-Q (a′) edition `ProjPresentation.toProj_eq_of_forall_sections_eq_univ` (Q9, universe u);
* lane4 G7 `PresentationBasics.presentationOfIso`;
* Mathlib `Proj.map_comp`.
-/
import ZInQKernel.Contrib.CloudR2NOS.ClosedSection.PresentationBasics
import ZInQKernel.Contrib.CloudR2NOS.Source.Theorems.Thm_AlgebraicGeometry_Scheme_Modules_ProjPresentation_exists_baseChange_of_isPullback
import ZInQKernel.Contrib.CloudR2NOS.Source.Theorems.Thm_AlgebraicGeometry_Scheme_Modules_ProjPresentation_toProj_eq_of_forall_sections_eq_univ

set_option autoImplicit false

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

attribute [local instance] MvPolynomial.gradedAlgebra

namespace ZInQ.Contrib.CloudR2NOS.Descent

local notation "Pres" => ZInQ.Contrib.CloudW03NeronSurj.FLT.AlgebraicGeometry.Scheme.Modules.ProjPresentation
local notation "PSmap" => ZInQ.Contrib.CloudW03NeronSurj.FLT.AlgebraicGeometry.ProjSpace.map
local notation "PSgr" => ZInQ.Contrib.CloudW03NeronSurj.FLT.AlgebraicGeometry.ProjSpace.mvMapGraded
local notation "pbSec" => ZInQ.Contrib.CloudR2NOS.ClosedSection.pullbackSection

/-- Functoriality of `ℙⁿ` along a tower `R → A → B`.

Truth check: `MvPolynomial.map` composes along the tower, and `Proj.map` is contravariantly
functorial. -/
theorem projSpaceMap_comp (R A B : Type u) [CommRing R] [CommRing A] [CommRing B] [Algebra R A]
    [Algebra A B] [Algebra R B] [IsScalarTower R A B] (n : ℕ) :
    PSmap A B n ≫ PSmap R A n = PSmap R B n := by
  have key : ∀ (g₁ g₂ : MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R →+*ᵍ
      MvPolynomial.homogeneousSubmodule (Fin (n + 1)) B) (_ : g₁ = g₂) (p₁ p₂),
      Proj.map g₁ p₁ = Proj.map g₂ p₂ := by
    rintro g₁ _ rfl _ _; rfl
  have hcomp : (PSgr A B n).comp (PSgr R A n) = PSgr R B n := by
    ext x
    change MvPolynomial.map (algebraMap A B) (MvPolynomial.map (algebraMap R A) x) =
      MvPolynomial.map (algebraMap R B) x
    rw [MvPolynomial.map_map, ← IsScalarTower.algebraMap_eq]
  rw [ZInQ.Contrib.CloudW03NeronSurj.FLT.AlgebraicGeometry.ProjSpace.map_eq,
    ZInQ.Contrib.CloudW03NeronSurj.FLT.AlgebraicGeometry.ProjSpace.map_eq,
    ZInQ.Contrib.CloudW03NeronSurj.FLT.AlgebraicGeometry.ProjSpace.map_eq, ← Proj.map_comp]
  exact key _ _ hcomp _ _

/-- With the right `S'`-algebra structure on `S' ⊗[S] S'`, the scalar tower still holds. -/
theorem isScalarTower_rightAlgebra (S S' : Type u) [CommRing S] [CommRing S'] [Algebra S S'] :
    letI : Algebra S' (S' ⊗[S] S') := Algebra.TensorProduct.rightAlgebra
    IsScalarTower S S' (S' ⊗[S] S') := by
  letI : Algebra S' (S' ⊗[S] S') := Algebra.TensorProduct.rightAlgebra
  refine IsScalarTower.of_algebraMap_eq fun s => ?_
  change algebraMap S (S' ⊗[S] S') s = (1 : S') ⊗ₜ[S] algebraMap S S' s
  rw [Algebra.TensorProduct.algebraMap_apply, Algebra.TensorProduct.tmul_one_eq_one_tmul]

/-- **Q10.** Descent compatibility. Let `𝔗` present `L'` over `S'`, and suppose each section
of `𝔗` is carried by the descent datum `ψ` from its `a₁`-pullback to its `a₂`-pullback. Then
`a₁ ≫ 𝔗.toProj ≫ ProjSpace.map S S' M = a₂ ≫ 𝔗.toProj ≫ ProjSpace.map S S' M`.

Truth check: both composites are the presentation map, over `S'⊗S'`, of a presentation of
`a₂^*L'` with sections `a₂^*τ`. The first uses the base change along `incL` followed by
transport along `ψ`; the second uses the base change along `incR`. Presentation maps are
determined by their sections (Q9). -/
theorem toProj_comp_map_eq {S : Type u} [CommRing S] (S' : Type u) [CommRing S'] [Algebra S S']
    {X' : Scheme.{u}} {f' : X' ⟶ Spec (CommRingCat.of S')} {L' : X'.Modules}
    {X'' : Scheme.{u}} {f'' : X'' ⟶ Spec (CommRingCat.of (S' ⊗[S] S'))} {a₁ a₂ : X'' ⟶ X'}
    (ha₁ : IsPullback a₁ f'' f' (Spec.map (CommRingCat.ofHom
      (Algebra.TensorProduct.includeLeft : S' →ₐ[S] S' ⊗[S] S').toRingHom)))
    (ha₂ : IsPullback a₂ f'' f' (Spec.map (CommRingCat.ofHom
      (Algebra.TensorProduct.includeRight : S' →ₐ[S] S' ⊗[S] S').toRingHom)))
    (ψ : (Scheme.Modules.pullback a₁).obj L' ≅ (Scheme.Modules.pullback a₂).obj L')
    {M : ℕ} (𝔗 : Pres L' f' M)
    (hτ : ∀ j, ψ.hom.app ⊤ (pbSec a₁ (𝔗.σ j)) = pbSec a₂ (𝔗.σ j)) :
    a₁ ≫ 𝔗.toProj ≫ PSmap S S' M = a₂ ≫ 𝔗.toProj ≫ PSmap S S' M := by
  -- the base change along `incL` (the default `S'`-algebra structure on `S' ⊗[S] S'`)
  have hL : (Algebra.TensorProduct.includeLeft : S' →ₐ[S] S' ⊗[S] S').toRingHom =
      algebraMap S' (S' ⊗[S] S') := RingHom.ext fun _ => rfl
  have ha₁' : IsPullback a₁ f'' f' (Spec.map (CommRingCat.ofHom (algebraMap S' (S' ⊗[S] S')))) := by
    rw [← hL]; exact ha₁
  obtain ⟨𝔗₁, h𝔗₁σ, h𝔗₁, -⟩ :=
    ZInQ.Contrib.CloudW03NeronSurj.FLT.AlgebraicGeometry.Scheme.Modules.ProjPresentation.exists_baseChange_of_isPullback
      ha₁' 𝔗
  have e₁ : a₁ ≫ 𝔗.toProj ≫ PSmap S S' M = 𝔗₁.toProj ≫ PSmap S (S' ⊗[S] S') M := by
    rw [← projSpaceMap_comp S S' (S' ⊗[S] S') M, ← Category.assoc 𝔗₁.toProj, h𝔗₁,
      Category.assoc]
  -- the base change along `incR` (the right `S'`-algebra structure)
  obtain ⟨𝔗₂, h𝔗₂σ, h𝔗₂⟩ : ∃ 𝔗₂ : Pres ((Scheme.Modules.pullback a₂).obj L') f'' M,
      (∀ i, 𝔗₂.σ i = (((Scheme.Modules.pullbackPushforwardAdjunction a₂).unit.app L').app ⊤)
        (𝔗.σ i)) ∧
      𝔗₂.toProj ≫ PSmap S (S' ⊗[S] S') M = a₂ ≫ 𝔗.toProj ≫ PSmap S S' M := by
    letI : Algebra S' (S' ⊗[S] S') := Algebra.TensorProduct.rightAlgebra
    haveI : IsScalarTower S S' (S' ⊗[S] S') := isScalarTower_rightAlgebra S S'
    have hR : (Algebra.TensorProduct.includeRight : S' →ₐ[S] S' ⊗[S] S').toRingHom =
        algebraMap S' (S' ⊗[S] S') := RingHom.ext fun _ => rfl
    have ha₂' : IsPullback a₂ f'' f' (Spec.map (CommRingCat.ofHom (algebraMap S' (S' ⊗[S] S')))) := by
      rw [← hR]; exact ha₂
    obtain ⟨𝔗₂, h𝔗₂σ, h𝔗₂, -⟩ :=
      ZInQ.Contrib.CloudW03NeronSurj.FLT.AlgebraicGeometry.Scheme.Modules.ProjPresentation.exists_baseChange_of_isPullback
        ha₂' 𝔗
    refine ⟨𝔗₂, h𝔗₂σ, ?_⟩
    rw [← projSpaceMap_comp S S' (S' ⊗[S] S') M, ← Category.assoc 𝔗₂.toProj, h𝔗₂, Category.assoc]
  -- transport the `incL` presentation along `ψ` (G7)
  obtain ⟨𝔗₁', h𝔗₁'toProj, h𝔗₁'σ⟩ :=
    ZInQ.Contrib.CloudR2NOS.ClosedSection.PresentationBasics.presentationOfIso 𝔗₁ ψ
  -- the two presentations of `a₂^*L'` have the same sections (descendedness)
  have hσ : ∀ i, 𝔗₁'.σ i = 𝔗₂.σ i := fun i => by
    rw [h𝔗₁'σ, h𝔗₁σ, h𝔗₂σ]
    exact hτ i
  -- Q9: presentation maps are determined by their sections
  have hT : 𝔗₁'.toProj = 𝔗₂.toProj :=
    ZInQ.Contrib.CloudW03NeronSurj.FLT.AlgebraicGeometry.Scheme.Modules.ProjPresentation.toProj_eq_of_forall_sections_eq_univ
      𝔗₁' 𝔗₂ hσ
  rw [e₁, ← h𝔗₁'toProj, hT, h𝔗₂]

end ZInQ.Contrib.CloudR2NOS.Descent
