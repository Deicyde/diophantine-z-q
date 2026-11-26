import Mathlib.Algebra.Category.Grp.Colimits
import Mathlib.Algebra.Homology.ShortComplex.Ab
import Mathlib.CategoryTheory.Limits.Preserves.FunctorCategory
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Kernels
import Mathlib.CategoryTheory.Sites.Abelian
import Mathlib.CategoryTheory.Sites.LocallyBijective

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits Opposite

namespace RC53.EllAdic

universe u v w

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)

/-- In an abelian sheaf category the cokernel of an epi is zero. If the
sheafification unit is locally injective at the presheaf cokernel, the
class of a section becomes locally zero already in that presheaf cokernel.
Pointwise cokernel exactness then gives actual local lifts of this section. -/
theorem abSheafLocallySurjective_of_epi_of_unit [HasSheafify J Ab.{w}]
    {F G : Sheaf J Ab.{w}} (f : F ⟶ G) [Epi f]
    (hunit : Presheaf.IsLocallyInjective J (toSheafify J (cokernel f.hom))) :
    Presheaf.IsLocallySurjective J f.hom := by
  let L := presheafToSheaf J Ab.{w}
  let R := sheafToPresheaf J Ab.{w}
  let a := sheafificationAdjunction J Ab.{w}
  let Q := cokernel f.hom
  let π : G.obj ⟶ Q := cokernel.π f.hom
  let e : L.obj Q ≅ cokernel f :=
    PreservesCokernel.iso L f.hom ≪≫
      cokernel.mapIso (L.map f.hom) f (asIso (a.counit.app F)) (asIso (a.counit.app G))
        (a.counit.naturality f)
  have hLQ : IsZero (L.obj Q) := (isZero_cokernel_of_epi f).of_iso e
  let η : Q ⟶ R.obj (L.obj Q) := toSheafify J Q
  let : Presheaf.IsLocallyInjective J η := hunit
  have hη : η = 0 := (R.map_isZero hLQ).eq_of_tgt η 0
  constructor
  intro U y
  let q : Q.obj (op U) := π.app (op U) y
  have hq : η.app (op U) q = η.app (op U) 0 := by
    rw [hη]; rfl
  have hcover : Presheaf.equalizerSieve q (0 : Q.obj (op U)) ∈ J U :=
    Presheaf.equalizerSieve_mem J η (X := op U) q 0 hq
  refine J.superset_covering ?_ hcover
  intro V g hg
  change Q.map g.op q = Q.map g.op 0 at hg
  have hn : π.app (op V) (G.obj.map g.op y) = Q.map g.op q :=
    congrArg (fun k : G.obj.obj (op U) ⟶ Q.obj (op V) => k y) (π.naturality g.op)
  have hz : π.app (op V) (G.obj.map g.op y) = 0 :=
    hn.trans (hg.trans (map_zero (Q.map g.op).hom))
  let E := (evaluation Cᵒᵖ Ab.{w}).obj (op V)
  let S := ShortComplex.cokernelSequence f.hom
  have hS : S.Exact := ShortComplex.cokernelSequence_exact f.hom
  have hpoint : Function.Exact (f.hom.app (op V)) (π.app (op V)) :=
    (ShortComplex.ab_exact_iff_function_exact (S.map E)).mp (hS.map E)
  change ∃ x : F.obj.obj (op V), f.hom.app (op V) x = G.obj.map g.op y
  exact (hpoint _).mp hz

/-- This is the epi-to-local-lift implication for abelian sheaves. It does
not assume that the underlying morphism of set-valued sheaves is epi. -/
theorem abSheafLocallySurjective_of_epi [HasSheafify J Ab.{w}] [J.WEqualsLocallyBijective Ab.{w}]
    {F G : Sheaf J Ab.{w}} (f : F ⟶ G) [Epi f] :
    Presheaf.IsLocallySurjective J f.hom :=
  abSheafLocallySurjective_of_epi_of_unit J f inferInstance

end RC53.EllAdic
