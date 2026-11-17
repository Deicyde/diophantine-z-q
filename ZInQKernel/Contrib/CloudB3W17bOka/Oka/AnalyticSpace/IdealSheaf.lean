/-
Copyright (c) 2026 Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten
-/
import Mathlib.Topology.Sheaves.LocallySurjective
import ZInQKernel.Contrib.CloudB3W17bOka.Oka.Algebra.Category.ModuleCat.Sheaf.Coherent.Stability
import ZInQKernel.Contrib.CloudB3W17bOka.Oka.AnalyticSpace.Coherent

/-!
# Coherence of finitely generated ideal sheaves

`ComplexAnalytic.AnalyticSpace.isCoherentStructureSheaf` says that `𝒪_X` is coherent over
itself. This file turns that into the statement downstream users need: the ideal sheaf generated
by finitely many global sections of `𝒪_X` is coherent, and the sheaf of relations between them
is of finite type.

The mechanism is the two-out-of-three stability of coherence, applied to
`sectionsHom : 𝒪 ^ I ⟶ 𝒪`. The only subtlety is that **no coherence of `𝒪 ^ I` is available or
needed**: `SheafOfModules.IsCoherent.image_of_isFiniteType` asks only that the *source* be of
finite type, because the image is a quotient of the source (hence of finite type) and a finite
type subsheaf of a coherent sheaf is coherent. A finite free sheaf of modules is of finite type
by `SheafOfModules.isFiniteType_free`, so nothing more is required.

## Main definitions

- `AlgebraicGeometry.LocallyRingedSpace.sectionsHom`: the morphism `𝒪_Y ^ I ⟶ 𝒪_Y` given by
  multiplication by a family of global sections, computed on sections over an open set by
  `AlgebraicGeometry.LocallyRingedSpace.val_app_sectionsHom`.
- `AlgebraicGeometry.LocallyRingedSpace.idealSheaf`: the ideal sheaf they generate, defined as
  the image of `sectionsHom`, with its inclusion `idealSheafι` into `𝒪_Y`.

## Main results

- `AlgebraicGeometry.LocallyRingedSpace.isCoherent_idealSheaf`: on a locally ringed space with
  coherent structure sheaf, a finitely generated ideal sheaf is coherent.
- `AlgebraicGeometry.LocallyRingedSpace.isFiniteType_kernel_sectionsHom`: the sheaf of relations
  between finitely many global sections is of finite type. On `ℂ^n` this is Oka's coherence
  lemma, read through the sheaf-of-modules formalism.
- `AlgebraicGeometry.LocallyRingedSpace.isCoherent_cokernel_sectionsHom`: the quotient
  `𝒪_Y ⧸ (f₁, …, f_k)` is coherent.
- `AlgebraicGeometry.LocallyRingedSpace.not_isZero_cokernel_sectionsHom_of_germ_mem`: that
  quotient is **not** the zero sheaf, as soon as the `f i` have a common zero. Coherence holds of
  the zero sheaf, so without this the results above are consistent with being about nothing. It
  rests on `AlgebraicGeometry.LocallyRingedSpace.not_epi_sectionsHom_of_germ_mem`, which is the
  same statement read through `Epi`.
- `AlgebraicGeometry.LocallyRingedSpace.isZero_cokernel_sectionsHom_one`: the converse extreme,
  that the quotient by the unit ideal *is* zero. This is what makes the hypothesis of the
  previous result necessary rather than decorative.
- `ComplexAnalytic.AnalyticSpace.isCoherent_idealSheaf`: the same for a complex analytic space,
  where the hypothesis is discharged by the main theorem.

## Implementation notes

`LocallyRingedSpace.IsCoherentStructureSheaf` is a `def`, not an `abbrev`, so instance search
does not unfold it; coherence of `𝒪_Y` has to be introduced in its unfolded form
`(SheafOfModules.unit Y.ringSheaf).IsCoherent` before the stability lemmas will fire. The same
reducibility boundary is why `Oka/AnalyticSpace/Noetherian.lean` registers two forms of the
stalk instance.

The non-vacuity results go through `Epi` rather than through the sections of the cokernel,
because the cokernel of a morphism of sheaves of modules is a sheafification and its sections
are not computable term by term, whereas `Epi f ↔ IsZero (cokernel f)` in an abelian category
and `Epi` is exactly what `Oka/Algebra/Category/ModuleCat/Sheaf/LocallySurjective.lean` makes
elementary. Reading the resulting equation of sections in `Γ(V, 𝒪_Y)` is a matter of type
ascription only: the scalar action of `SheafOfModules.unit Y.ringSheaf` on itself and its
restriction maps are definitionally the multiplication and the restriction maps of `𝒪_Y`.

## References

- [Jean-Pierre Serre, *Faisceaux algébriques cohérents*][serre1955], §2
- [Hans Grauert and Reinhold Remmert, *Coherent analytic sheaves*][grauert-remmert1984], §A
-/

open CategoryTheory Limits TopologicalSpace Opposite AlgebraicGeometry

universe u

namespace AlgebraicGeometry.LocallyRingedSpace

variable (Y : LocallyRingedSpace.{u})

/-- The morphism `𝒪_Y ^ I ⟶ 𝒪_Y` of sheaves of modules given by multiplication by a family
`f : I → Γ(Y, 𝒪_Y)` of global sections. -/
noncomputable def sectionsHom {I : Type u} (f : I → Y.presheaf.obj (op ⊤)) :
    SheafOfModules.free (R := Y.ringSheaf) I ⟶ SheafOfModules.unit Y.ringSheaf :=
  (SheafOfModules.freeHomEquiv _).symm
    (fun i ↦ SheafOfModules.sectionOfTerminal isTerminalTop _ (f i))

@[simp]
lemma freeHomEquiv_sectionsHom {I : Type u} (f : I → Y.presheaf.obj (op ⊤)) (i : I) :
    SheafOfModules.freeHomEquiv _ (Y.sectionsHom f) i =
      SheafOfModules.sectionOfTerminal isTerminalTop _ (f i) :=
  congrFun (Equiv.apply_symm_apply _ _) i

/-- `sectionsHom` on sections over an open set `V`: it sends a tuple to the corresponding
`𝒪_Y(V)`-combination of the restrictions of the `f i` to `V`.

`freeHomEquiv_sectionsHom` already pins the morphism down, since `freeHomEquiv` is an `Equiv`,
but this is the elementwise form a downstream proof will want. The scalar action has to be `•`
and not `*`: `Y.ringSheaf.obj.obj (op V)` and `Y.presheaf.obj (op V)` share a carrier but are
not the same type as far as elaboration is concerned. -/
@[simp]
lemma val_app_sectionsHom {I : Type u} [Fintype I] [DecidableEq I]
    (f : I → Y.presheaf.obj (op ⊤)) (V : Opens ↑Y.toPresheafedSpace)
    (b : (SheafOfModules.free (R := Y.ringSheaf) I).val.obj (op V)) :
    (Y.sectionsHom f).val.app (op V) b =
      ∑ i : I, SheafOfModules.freeEval (R := Y.ringSheaf) (I := I) (op V) b i •
        (SheafOfModules.unit Y.ringSheaf).val.map (homOfLE (le_top (a := V))).op
          ((f i : Y.presheaf.obj (op ⊤)) : (SheafOfModules.unit Y.ringSheaf).val.obj (op ⊤)) := by
  rw [SheafOfModules.val_app_eq_sum]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [Y.freeHomEquiv_sectionsHom f i]
  rfl

/-- The ideal sheaf generated by a family of global sections of the structure sheaf: the image
of `sectionsHom`, i.e. the subsheaf of `𝒪_Y` whose sections over `V` are, locally on `V`, the
`𝒪_Y`-combinations of the `f i`. -/
noncomputable def idealSheaf {I : Type u} (f : I → Y.presheaf.obj (op ⊤)) :
    SheafOfModules.{u} Y.ringSheaf :=
  Abelian.image (Y.sectionsHom f)

/-- The inclusion of the ideal sheaf into the structure sheaf. -/
noncomputable def idealSheafι {I : Type u} (f : I → Y.presheaf.obj (op ⊤)) :
    Y.idealSheaf f ⟶ SheafOfModules.unit Y.ringSheaf :=
  Abelian.image.ι (Y.sectionsHom f)

instance {I : Type u} (f : I → Y.presheaf.obj (op ⊤)) : Mono (Y.idealSheafι f) :=
  inferInstanceAs (Mono (Abelian.image.ι _))

/-- **A finitely generated ideal sheaf on a locally ringed space with coherent structure sheaf
is coherent.**

The point is that no coherence of `𝒪_Y ^ I` is needed: the ideal sheaf is a quotient of it,
hence of finite type, and a finite type subsheaf of a coherent sheaf is coherent. -/
theorem isCoherent_idealSheaf (h : Y.IsCoherentStructureSheaf) {I : Type u} [Finite I]
    (f : I → Y.presheaf.obj (op ⊤)) : (Y.idealSheaf f).IsCoherent :=
  -- `IsCoherentStructureSheaf` is a `def`, so instance search will not unfold it: the
  -- coherence of `𝒪_Y` has to be introduced in its unfolded form.
  haveI : (SheafOfModules.unit Y.ringSheaf).IsCoherent := h
  SheafOfModules.IsCoherent.image_of_isFiniteType _

/-- **The sheaf of relations between finitely many global sections is of finite type**, on a
locally ringed space with coherent structure sheaf.

On `ℂ^n` this is Oka's coherence lemma (`theorem oka` of `Oka/Statement.lean`) read through the
sheaf-of-modules formalism: the relations between finitely many holomorphic functions are, near
every point, generated by finitely many of them. -/
theorem isFiniteType_kernel_sectionsHom (h : Y.IsCoherentStructureSheaf) {I : Type u} [Finite I]
    (f : I → Y.presheaf.obj (op ⊤)) : (kernel (Y.sectionsHom f)).IsFiniteType :=
  haveI : (SheafOfModules.unit Y.ringSheaf).IsCoherent := h
  SheafOfModules.isFiniteType_kernel_of_isCoherent _

/-- **The quotient of the structure sheaf by a finitely generated ideal sheaf is coherent**, on
a locally ringed space with coherent structure sheaf.

This is the third leg of two-out-of-three, `SheafOfModules.IsCoherent.cokernel`, and again only
the finite type of the source `𝒪_Y ^ I` is used. The quotient is the structure sheaf of the
closed subspace cut out by the `f i`, so this is what makes the theory of coherent sheaves
available on an analytic subspace rather than only on the ambient space. -/
theorem isCoherent_cokernel_sectionsHom (h : Y.IsCoherentStructureSheaf) {I : Type u} [Finite I]
    (f : I → Y.presheaf.obj (op ⊤)) : (cokernel (Y.sectionsHom f)).IsCoherent :=
  haveI : (SheafOfModules.unit Y.ringSheaf).IsCoherent := h
  SheafOfModules.IsCoherent.cokernel _

set_option backward.isDefEq.respectTransparency false in
/-- **The morphism `𝒪_Y ^ I ⟶ 𝒪_Y` is not an epimorphism if the `f i` all vanish at a common
point** — that is, if their germs at some `y` all lie in the maximal ideal of `𝒪_{Y,y}`.

An epimorphism of sheaves of modules is locally surjective
(`SheafOfModules.isLocallySurjective_toSheaf_map_of_epi`), so `1` would be an
`𝒪_Y`-combination of the `f i` on some neighbourhood `V` of `y`. Taking germs at `y` puts `1` in
the ideal generated by the germs of the `f i`, which is contained in the maximal ideal. -/
theorem not_epi_sectionsHom_of_germ_mem {I : Type u} [Finite I]
    (f : I → Y.presheaf.obj (op ⊤)) (y : Y)
    (hf : ∀ i, Y.presheaf.germ ⊤ y trivial (f i) ∈
      IsLocalRing.maximalIdeal (Y.presheaf.stalk y)) :
    ¬ Epi (Y.sectionsHom f) := by
  classical
  cases nonempty_fintype I
  intro hepi
  -- an epimorphism is locally surjective, so `1` lifts on a neighbourhood `V` of `y`
  have hloc : TopCat.Presheaf.IsLocallySurjective
      ((SheafOfModules.toSheaf Y.ringSheaf).map (Y.sectionsHom f)).hom :=
    SheafOfModules.isLocallySurjective_toSheaf_map_of_epi (Y.sectionsHom f)
  rw [TopCat.Presheaf.isLocallySurjective_iff] at hloc
  obtain ⟨V, hVtop, ⟨s, hs⟩, hyV⟩ :=
    hloc ⊤ (show ToType (((SheafOfModules.toSheaf Y.ringSheaf).obj
      (SheafOfModules.unit Y.ringSheaf)).obj.obj (op ⊤)) from (1 : Y.presheaf.obj (op ⊤)))
      y trivial
  rw [show ((SheafOfModules.toSheaf Y.ringSheaf).map (Y.sectionsHom f)).hom.app (op V) s =
    (Y.sectionsHom f).val.app (op V) s from rfl, Y.val_app_sectionsHom f V s] at hs
  -- read that equation in `Γ(V, 𝒪_Y)`, where the scalar action is multiplication and the
  -- restriction map of `SheafOfModules.unit` is the one of `𝒪_Y`
  have hs' : ∑ i : I,
      (show ToType (Y.presheaf.obj (op V)) from
        SheafOfModules.freeEval (R := Y.ringSheaf) (I := I) (op V) s i) *
        Y.res (le_top (a := V)) (f i) =
      Y.res (le_top (a := V)) (1 : Y.presheaf.obj (op ⊤)) := hs
  rw [show Y.res (le_top (a := V)) (1 : Y.presheaf.obj (op ⊤)) = 1 from map_one _] at hs'
  have hgerm : ∀ i : I, Y.presheaf.germ V y hyV (Y.res (le_top (a := V)) (f i)) =
      Y.presheaf.germ ⊤ y trivial (f i) :=
    fun i ↦ Y.presheaf.germ_res_apply (homOfLE le_top) y hyV (f i)
  have hg := congrArg (fun z ↦ Y.presheaf.germ V y hyV z) hs'
  simp only [map_sum, map_mul, map_one, hgerm] at hg
  refine (IsLocalRing.maximalIdeal.isMaximal (Y.presheaf.stalk y)).ne_top ?_
  rw [Ideal.eq_top_iff_one, ← hg]
  exact Ideal.sum_mem _ fun i _ ↦ Ideal.mul_mem_left _ _ (hf i)

/-- **The quotient `𝒪_Y ⧸ (f₁, …, f_k)` is not the zero sheaf** as soon as the `f i` have a
common zero `y`, in the sense that their germs at `y` lie in the maximal ideal of `𝒪_{Y,y}`.

`AlgebraicGeometry.LocallyRingedSpace.isCoherent_cokernel_sectionsHom` says that quotient is
coherent, and coherence holds of the zero sheaf; this is what makes the statement about
something. -/
theorem not_isZero_cokernel_sectionsHom_of_germ_mem {I : Type u} [Finite I]
    (f : I → Y.presheaf.obj (op ⊤)) (y : Y)
    (hf : ∀ i, Y.presheaf.germ ⊤ y trivial (f i) ∈
      IsLocalRing.maximalIdeal (Y.presheaf.stalk y)) :
    ¬ IsZero (cokernel (Y.sectionsHom f)) := fun h ↦
  Y.not_epi_sectionsHom_of_germ_mem f y hf (Preadditive.epi_of_isZero_cokernel _ h)

set_option backward.isDefEq.respectTransparency false in
/-- **The quotient by the unit ideal is the zero sheaf.**

This is the sharpness half of
`AlgebraicGeometry.LocallyRingedSpace.not_isZero_cokernel_sectionsHom_of_germ_mem`: some
hypothesis on the `f i` is genuinely needed there, because for the one-element family `f = 1`
the quotient really is `0`. Here `𝒪_Y ^ {*} ⟶ 𝒪_Y` is surjective on sections over *every* open,
which is more than locally surjective. -/
theorem isZero_cokernel_sectionsHom_one :
    IsZero (cokernel (Y.sectionsHom
      (fun _ : PUnit.{u + 1} ↦ (1 : Y.presheaf.obj (op ⊤))))) := by
  haveI : Epi (Y.sectionsHom (fun _ : PUnit.{u + 1} ↦ (1 : Y.presheaf.obj (op ⊤)))) := by
    rw [← SheafOfModules.isLocallySurjective_toSheaf_map_iff_epi]
    apply CategoryTheory.Presheaf.isLocallySurjective_of_surjective
    rintro ⟨V⟩ t
    refine ⟨SheafOfModules.freeEvalSymm (R := Y.ringSheaf) (I := PUnit.{u + 1}) (op V)
      (fun _ ↦ t), ?_⟩
    change (Y.sectionsHom (fun _ : PUnit.{u + 1} ↦ (1 : Y.presheaf.obj (op ⊤)))).val.app (op V)
      (SheafOfModules.freeEvalSymm (R := Y.ringSheaf) (I := PUnit.{u + 1}) (op V) fun _ ↦ t) = t
    rw [Y.val_app_sectionsHom, SheafOfModules.freeEval_freeEvalSymm]
    -- the sum has one term, the scalar action is multiplication, and restriction preserves `1`
    exact (Finset.sum_const _).trans <|
      (one_nsmul _).trans <|
        (congrArg (fun z ↦ (show ToType (Y.presheaf.obj (op V)) from t) * z)
          (show Y.res (le_top (a := V)) (1 : Y.presheaf.obj (op ⊤)) = 1 from map_one _)).trans
          (mul_one _)
  exact Limits.isZero_cokernel_of_epi _

end AlgebraicGeometry.LocallyRingedSpace

namespace ComplexAnalytic.AnalyticSpace

variable (X : AnalyticSpace.{u})

/-- **The ideal sheaf generated by finitely many global holomorphic functions on a complex
analytic space is coherent.**

This is the first consequence of `ComplexAnalytic.AnalyticSpace.isCoherentStructureSheaf`, and
the form in which coherence is used: everything about analytic subsets starts by applying the
two-out-of-three stability properties to a morphism `𝒪_X ^ k ⟶ 𝒪_X`. -/
theorem isCoherent_idealSheaf {I : Type u} [Finite I]
    (f : I → X.presheaf.obj (op ⊤)) :
    (X.toLocallyRingedSpace.idealSheaf f).IsCoherent :=
  X.toLocallyRingedSpace.isCoherent_idealSheaf X.isCoherentStructureSheaf f

/-- **The sheaf of relations between finitely many global holomorphic functions on a complex
analytic space is of finite type.** -/
theorem isFiniteType_kernel_sectionsHom {I : Type u} [Finite I]
    (f : I → X.presheaf.obj (op ⊤)) :
    (kernel (X.toLocallyRingedSpace.sectionsHom f)).IsFiniteType :=
  X.toLocallyRingedSpace.isFiniteType_kernel_sectionsHom X.isCoherentStructureSheaf f

/-- **The quotient of the structure sheaf of a complex analytic space by a finitely generated
ideal sheaf is coherent.** -/
theorem isCoherent_cokernel_sectionsHom {I : Type u} [Finite I]
    (f : I → X.presheaf.obj (op ⊤)) :
    (cokernel (X.toLocallyRingedSpace.sectionsHom f)).IsCoherent :=
  X.toLocallyRingedSpace.isCoherent_cokernel_sectionsHom X.isCoherentStructureSheaf f

end ComplexAnalytic.AnalyticSpace
