/-
Adapted from AxiomMath/Stacks c496df0d9beea9deaeabcea8492605f9a0a2313b.
Source: StacksFrontier/AlgebraicGeometry/GroupScheme/Differentials.lean,
lines 57–160 and 217–245. Source SHA256: 7687483fd1cb00109bc3ea84ef14386ca89c1ffaa7bc7da28d6ce08d9faaa460.
Apache-2.0; see LICENSE and NOTICE.md. Changes: omit conormal comparisons;
isolate declarations; omit citation attributes; use the existing Jacobian
field-module theorem instead of a quasi-coherence hypothesis.
-/
import Mathlib.AlgebraicGeometry.Modules.Tilde
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackFree
import Mathlib.CategoryTheory.Monoidal.Cartesian.Grp
import Mathlib.CategoryTheory.Monoidal.Cartesian.Over
import Mathlib.LinearAlgebra.Basis.VectorSpace
import ZInQKernel.Contrib.CloudW07JacobiansCurves.Jacobian.AlgebraicGeometry.Modules.Field
import ZInQKernel.Contrib.CloudB3W16Cartier.Vendor.StacksFrontier.AlgebraicGeometry.Morphisms.Differentials.BaseChange

namespace ZInQ.Contrib.CloudB3W16Cartier.Vendor
open _root_.AlgebraicGeometry _root_.CategoryTheory
noncomputable section
universe u

namespace AlgebraicGeometry.Scheme.Modules
/-- Pullback preserves a free module sheaf. Adapted from Stacks
`Flatness/Devissage/Complete/Transport.lean`, lines 199–205. -/
def pullbackFreeIso {X Y : Scheme.{u}} (f : X ⟶ Y) (I : Type u) :
    (Scheme.Modules.pullback f).obj (SheafOfModules.free (R := Y.ringCatSheaf) I) ≅
      SheafOfModules.free (R := X.ringCatSheaf) I :=
  haveI : (SheafOfModules.pushforward f.toRingCatSheafHom).IsRightAdjoint :=
    inferInstanceAs ((Scheme.Modules.pushforward f).IsRightAdjoint)
  haveI : (TopologicalSpace.Opens.map f.base).Final := final_of_representablyFlat _
  SheafOfModules.pullbackObjFreeIso f.toRingCatSheafHom I
end AlgebraicGeometry.Scheme.Modules

open CategoryTheory CategoryTheory.Limits CartesianMonoidalCategory
open scoped CategoryTheory.MonObj CategoryTheory.MonoidalCategory


namespace AlgebraicGeometry.GroupSchemeDifferentials

open AlgebraicGeometry.Scheme.Hom

variable {S G : Scheme.{u}} (f : G ⟶ S) [GrpObj (Over.mk f)]

/-- The multiplication of a group scheme as a morphism of schemes `G ×_S G ⟶ G`. -/
noncomputable def mul : pullback f f ⟶ G := (μ[Over.mk f]).left

/-- The identity section of a group scheme as a morphism of schemes `S ⟶ G`. -/
noncomputable def identity : S ⟶ G := (η[Over.mk f]).left

/-- The identity section is a section of the structure morphism. -/
@[simp]
lemma identity_comp : identity f ≫ f = 𝟙 S := (η[Over.mk f]).w

/-- Multiplication is a morphism over `S`, written against the second projection. -/
lemma mul_comp : mul f ≫ f = pullback.snd f f ≫ f := by
  have hw := (μ[Over.mk f]).w
  simp only [Over.tensorObj_hom, Over.mk_hom] at hw
  rw [show mul f = (μ[Over.mk f]).left from rfl, hw, pullback.condition]

/-- **The shearing automorphism** `(g, h) ↦ (m(g, h), h)` of `G ×_S G`, as an automorphism of
`(Over.mk f) ⊗ (Over.mk f)` in the category of schemes over `S`.  Its inverse is
`(g, h) ↦ (g h⁻¹, h)`. -/
noncomputable def shearIso : (Over.mk f ⊗ Over.mk f) ≅ (Over.mk f ⊗ Over.mk f) where
  hom := lift μ[Over.mk f] (snd _ _)
  inv := lift (fst _ _ / snd _ _) (snd _ _)
  hom_inv_id := by apply hom_ext <;> simp [GrpObj.comp_div, MonObj.mul_eq_mul]
  inv_hom_id := by apply hom_ext <;> simp [MonObj.comp_mul, MonObj.mul_eq_mul]

/-- **Multiplication and the second projection exhibit `G ×_S G` as a fibre product of `f` with
itself.** -/
lemma isPullback_mul : IsPullback (mul f) (pullback.snd f f) f f := by
  refine IsPullback.of_iso_pullback ⟨mul_comp f⟩ ((Over.forget S).mapIso (shearIso f)) ?_ ?_
  · change ((shearIso f).hom ≫ fst (Over.mk f) (Over.mk f)).left = _
    simp [shearIso, mul]
  · change ((shearIso f).hom ≫ snd (Over.mk f) (Over.mk f)).left = _
    simp [shearIso]

/-- The morphism `(e ∘ f, 1) : G ⟶ G ×_S G`. -/
noncomputable def unitSection : G ⟶ pullback f f :=
  (lift (toUnit (Over.mk f) ≫ η[Over.mk f]) (𝟙 (Over.mk f))).left

/-- The composite of `(e ∘ f, 1)` with multiplication is the identity. -/
@[simp]
lemma unitSection_mul : unitSection f ≫ mul f = 𝟙 G := by
  change (lift (toUnit (Over.mk f) ≫ η[Over.mk f]) (𝟙 (Over.mk f)) ≫ μ[Over.mk f]).left = _
  rw [MonObj.lift_comp_one_left]
  rfl

/-- The first component of `(e ∘ f, 1)` is `e ∘ f`. -/
@[simp]
lemma unitSection_fst : unitSection f ≫ pullback.fst f f = f ≫ identity f := by
  change (lift (toUnit (Over.mk f) ≫ η[Over.mk f]) (𝟙 (Over.mk f)) ≫ fst _ _).left = _
  simp [identity]

/-- The second component of `(e ∘ f, 1)` is the identity. -/
@[simp]
lemma unitSection_snd : unitSection f ≫ pullback.snd f f = 𝟙 G := by
  change (lift (toUnit (Over.mk f) ≫ η[Over.mk f]) (𝟙 (Over.mk f)) ≫ snd _ _).left = _
  simp

/-- **The shearing comparison on relative differentials**, `m^*Ω_{G/S} ≅ pr₀^*Ω_{G/S}`.  Both
sides are identified with `Ω_{(G ×_S G)/G}` by the base change isomorphism of
[Stacks, Tag 01V0], applied to the cartesian square of `isPullback_mul` and to the standard
pullback square. -/
noncomputable def shearDifferentialsIso :
    (Scheme.Modules.pullback (mul f)).obj (relativeDifferentials f) ≅
      (Scheme.Modules.pullback (pullback.fst f f)).obj (relativeDifferentials f) :=
  haveI : IsIso (relativeDifferentialsMap (mul f) f (pullback.snd f f) f (isPullback_mul f).w) :=
    isIso_relativeDifferentialsMap_of_isPullback (mul f) (pullback.snd f f) f f (isPullback_mul f)
  haveI : IsIso (relativeDifferentialsMap (pullback.fst f f) f (pullback.snd f f) f
      (IsPullback.of_hasPullback f f).w) :=
    isIso_relativeDifferentialsMap_of_isPullback (pullback.fst f f) (pullback.snd f f) f f
      (IsPullback.of_hasPullback f f)
  (asIso (relativeDifferentialsMap (mul f) f (pullback.snd f f) f (isPullback_mul f).w)).trans
    (asIso (relativeDifferentialsMap (pullback.fst f f) f (pullback.snd f f) f
      (IsPullback.of_hasPullback f f).w)).symm

/-- **The canonical isomorphism `Ω_{G/S} ≅ f^*e^*Ω_{G/S}`.**  The sheaf of relative
differentials of a group scheme is the inverse image of its restriction along the identity
section. -/
noncomputable def relativeDifferentialsIsoPullbackIdentity :
    relativeDifferentials f ≅
      (Scheme.Modules.pullback f).obj
        ((Scheme.Modules.pullback (identity f)).obj (relativeDifferentials f)) :=
  ((Scheme.Modules.pullbackId G).app (relativeDifferentials f)).symm ≪≫
  (Scheme.Modules.pullbackCongr (unitSection_mul f).symm).app (relativeDifferentials f) ≪≫
  ((Scheme.Modules.pullbackComp (unitSection f) (mul f)).app (relativeDifferentials f)).symm ≪≫
  (Scheme.Modules.pullback (unitSection f)).mapIso (shearDifferentialsIso f) ≪≫
  (Scheme.Modules.pullbackComp (unitSection f) (pullback.fst f f)).app
    (relativeDifferentials f) ≪≫
  (Scheme.Modules.pullbackCongr (unitSection_fst f)).app (relativeDifferentials f) ≪≫
  ((Scheme.Modules.pullbackComp f (identity f)).app (relativeDifferentials f)).symm
/-- **A quasi-coherent module on the spectrum of a field is free.** -/
theorem exists_free_iso_of_isQuasicoherent_spec_field (k : Type u) [Field k]
    (N : (Spec (CommRingCat.of k)).Modules) :
    ∃ I : Type u,
      Nonempty (N ≅ SheafOfModules.free (R := (Spec (CommRingCat.of k)).ringCatSheaf) I) := by
  haveI : IsIso N.fromTildeΓ :=
    _root_.AlgebraicGeometry.Scheme.Modules.isIso_fromTildeΓ_of_isField
      (Field.toIsField k) N
  let R : CommRingCat.{u} := CommRingCat.of k
  let V : ModuleCat.{u} R := (modulesSpecToSheaf.obj N).presheaf.obj (.op ⊤)
  let _ : Field (R : Type u) := inferInstanceAs (Field k)
  let b := Module.Basis.ofVectorSpace (R : Type u) (V : Type u)
  refine ⟨Module.Basis.ofVectorSpaceIndex (R : Type u) (V : Type u), ⟨?_⟩⟩
  exact (asIso N.fromTildeΓ).symm ≪≫ (tilde.functor R).mapIso b.repr.toModuleIso ≪≫
    tildeFinsupp _

/-- **Freeness over a field.**  If the base is the spectrum of a field, the sheaf of relative
differentials of a group scheme is a free `𝒪_G`-module. -/
theorem exists_free_iso_relativeDifferentials_of_field (k : Type u) [Field k] (G : Scheme.{u})
    (f : G ⟶ Spec (CommRingCat.of k)) [GrpObj (Over.mk f)] :
    ∃ I : Type u,
      Nonempty (relativeDifferentials f ≅
        SheafOfModules.free (R := G.ringCatSheaf) I) := by
  obtain ⟨I, ⟨e⟩⟩ := exists_free_iso_of_isQuasicoherent_spec_field k
    ((Scheme.Modules.pullback (identity f)).obj (relativeDifferentials f))
  exact ⟨I, ⟨relativeDifferentialsIsoPullbackIdentity f ≪≫
    (Scheme.Modules.pullback f).mapIso e ≪≫ Scheme.Modules.pullbackFreeIso f I⟩⟩

end AlgebraicGeometry.GroupSchemeDifferentials

end
end ZInQ.Contrib.CloudB3W16Cartier.Vendor
