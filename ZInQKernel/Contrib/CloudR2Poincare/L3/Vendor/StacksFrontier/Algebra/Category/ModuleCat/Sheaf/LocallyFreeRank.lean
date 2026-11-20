import Mathlib
import ZInQKernel.Contrib.CloudR2Poincare.L3.VendorAlias
import ZInQKernel.Contrib.CloudR2Poincare.L3.Vendor.StacksFrontier.Topology.Sheaves.Stalk.ValuedInCategory
import ZInQKernel.Contrib.CloudR2Poincare.L3.InstanceScope

#cloudR2LocalInstances

/-!
# Isolated Stacks proof port

Upstream: AxiomMath/Stacks, commit `c496df0d9beea9deaeabcea8492605f9a0a2313b`,
module `StacksFrontier.Algebra.Category.ModuleCat.Sheaf.LocallyFreeRank`, Apache-2.0 (see the adjacent L3/LICENSE).
Prominent change notice, 2026-11-14: imports are restricted to the selected proof
closure; source metadata attributes and module-visibility sections are removed;
all new declarations are isolated beneath `ZInQ.Contrib.CloudR2Poincare.L3.StacksPort` to avoid main namespace clashes.
No proof hypothesis or mathematical conclusion is replaced by an assumed fact.
-/

namespace ZInQ.Contrib.CloudR2Poincare.L3.StacksPort
#cloudR2LocalInstances

open _root_.TopologicalSpace _root_.AlgebraicGeometry _root_.CategoryTheory





set_option backward.isDefEq.respectTransparency false

/-
# Problem Description (Stacks Tag 01C9)

Let `(X, O_X)` be a ringed space, i.e. a topological space `X` together with a sheaf of
*commutative* unital rings `O_X`.  For a point `x : X` write `O_{X,x}` for the stalk of
`O_X` at `x`.

* (Locally free sheaf of modules.)  A sheaf `F` of `O_X`-modules is *locally free* if
  every point `x : X` has an open neighbourhood `U`, an index set `I` and an isomorphism
  of `O_X|_U`-modules
    `F|_U ≅ ⊕_{i ∈ I} O_X|_U`,
  where `⊕_{i ∈ I} O_X|_U` denotes the direct sum (coproduct) of `I` copies of the
  structure sheaf restricted to `U`.

* (Locally constant function.)  A function `f : X → S` is *locally constant* if every
  point has an open neighbourhood on which `f` is constant.

* (Support of `O_X` is `X`.)  This means that for every `x : X` the stalk `O_{X,x}` is a
  nonzero ring, equivalently `Nontrivial O_{X,x}` (i.e. `1 ≠ 0`).

## Theorem (Stacks Tag 01C9)

Let `(X, O_X)` be a ringed space such that the support of `O_X` is all of `X`, i.e.
every stalk `O_{X,x}` is a nonzero ring.  Let `F` be a locally free sheaf of
`O_X`-modules.  Then there exists a locally constant function

  `rank_F : X → {0, 1, 2, …} ∪ {∞}`

with the following property: for every point `x : X` and every index set `I` such that
`F` is isomorphic to `⊕_{i ∈ I} O_X|_U` on some open neighbourhood `U` of `x`, the
cardinality of `I` equals `rank_F x`.

This asserts simultaneously:
1. (Well-definedness of the rank at each point.)  The cardinality `|I|` is independent of
   the chosen neighbourhood `U ∋ x` and the chosen trivialisation; this common cardinality
   is `rank_F x`.
2. (Local constancy.)  The function `x ↦ rank_F x` is locally constant on `X`.

The codomain `{0, 1, 2, …} ∪ {∞}` is read as the collection of possible cardinalities of
index sets.  Finite index sets give natural numbers; infinite index sets give infinite
cardinals.  Following the problem statement (which explicitly allows tracking the
cardinalities exactly), we use the type `Cardinal` as the codomain of the rank function:
the symbol `∞` of the informal statement corresponds to an infinite cardinal, and
`rank_F x` records the cardinality `|I|` exactly.  The role of the nonvanishing hypothesis
on the stalks is that over a nonzero commutative ring `R = O_{X,x}` the free module rank is
invariant (invariant basis number): `R^{(I)} ≅ R^{(J)}` implies `|I| = |J|`; without it the
zero ring would make every `R^{(I)}` trivial, breaking well-definedness.

## Formalisation notes

* The structure sheaf `O_X` is modelled as a sheaf of *commutative* unital rings, i.e. a
  term `O : Sheaf (Opens.grothendieckTopology X) CommRingCat`.  Mathlib's `SheafOfModules`
  is taken over a sheaf of (possibly non-commutative) rings, so we transport `O` along the
  forgetful functor `CommRingCat ⥤ RingCat` to obtain the base sheaf of rings `R := O_X`
  over which `F` is a sheaf of modules; commutativity is genuinely recorded by `O`.

* The restriction `F|_U` (resp. `O_X|_U`) of a sheaf of modules (resp. ring sheaf) to an
  open set `U` is the genuine pullback along the open immersion `U ↪ X`, formalised as the
  `SheafOfModules.pushforward`/`sheafPushforwardContinuous` along the open-inclusion functor
  `Opens U ⥤ Opens X` (`restrictMod`/`restrictRing` below).  This carries the inherited
  `O_X|_U`-module structure.

* The direct sum `⊕_{i ∈ I} O_X|_U` is the genuine categorical coproduct of `I` copies of
  the structure sheaf inside the category of sheaves of modules over `O_X|_U`, namely the
  free sheaf of modules `SheafOfModules.free I` (whose universal property identifies it with
  the coproduct of `I` copies of the unit `O_X|_U`).

* A trivialisation `F|_U ≅ ⊕_{i ∈ I} O_X|_U` is therefore a single isomorphism in the
  category `SheafOfModules (O_X|_U)` between the genuine restriction `restrictMod F` and the
  free sheaf of modules `SheafOfModules.free I`.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace
open CategoryTheory AlgebraicGeometry TopologicalSpace CategoryTheory.Limits

universe u

namespace LocallyFreeRank
#cloudR2LocalInstances

-- ## Restriction to an open subset
#cloudR2Vendor inclF in

/-- The open-inclusion functor `Opens U ⥤ Opens X` induced by the open embedding of the
subspace `U` into `X`.  It sends an open subset of `U` to its image, an open subset of
`X`. -/
noncomputable def inclF (X : TopCat.{u}) (U : Opens X) : Opens U ⥤ Opens X :=
  IsOpenMap.functor (f := U.inclusion') (U.isOpenEmbedding'.isOpenMap)
#cloudR2Vendor instFaithful in

/-- The open-inclusion functor `inclF X U` is faithful. -/
local instance instFaithful (X : TopCat.{u}) (U : Opens X) : (inclF X U).Faithful where
  map_injective _ := Subsingleton.elim _ _
#cloudR2Vendor instFull in

/-- The open-inclusion functor `inclF X U` is full. -/
local instance instFull (X : TopCat.{u}) (U : Opens X) : (inclF X U).Full where
  map_surjective {V₁ V₂} f := by
    refine ⟨homOfLE ?_, Subsingleton.elim _ _⟩
    intro x hx
    have hmem : (x : X) ∈ ((inclF X U).obj V₂ : Opens X) := leOfHom f ⟨x, hx, rfl⟩
    obtain ⟨y, hy, hyeq⟩ := hmem
    rwa [Subtype.val_injective hyeq] at hy
#cloudR2Vendor downClosed in

/-- The open-inclusion functor is downwards closed: any open `d ⊆ X` lying under the image
of an open of `U` is itself contained in `U`, hence is the image of an open of `U`. -/
noncomputable def downClosed (X : TopCat.{u}) (U : Opens X) :
    {c : Opens U} → {d : Opens X} → (d ⟶ (inclF X U).obj c) →
      (c' : Opens U) × ((inclF X U).obj c' ≅ d) :=
  fun {c} {d} f => by
    have hdU : (d : Set X) ⊆ (U : Set X) := fun x hx => by
      obtain ⟨y, _, rfl⟩ := leOfHom f hx; exact y.2
    refine ⟨⟨Subtype.val ⁻¹' (d : Set X), d.2.preimage continuous_subtype_val⟩, eqToIso ?_⟩
    apply Opens.ext; ext x
    simp only [inclF, IsOpenMap.functor]
    exact ⟨fun ⟨y, hy, h⟩ => h ▸ hy, fun hx => ⟨⟨x, hdU hx⟩, hx, rfl⟩⟩
#cloudR2Vendor instCoverPreserving in

/-- The open-inclusion functor `inclF X U` sends covering sieves of `U` to covering sieves
of `X`. -/
lemma instCoverPreserving (X : TopCat.{u}) (U : Opens X) :
    CoverPreserving (Opens.grothendieckTopology U) (Opens.grothendieckTopology X) (inclF X U) := by
  constructor
  intro V S hS x hx
  obtain ⟨y, hyV, rfl⟩ := hx
  obtain ⟨W, f, hf, hyW⟩ := hS y hyV
  exact ⟨(inclF X U).obj W, (inclF X U).map f,
    Sieve.image_mem_functorPushforward (inclF X U) S hf, ⟨y, hyW, rfl⟩⟩
#cloudR2Vendor instContinuous in

/-- The open-inclusion functor `inclF X U` is continuous for the Grothendieck topologies
of open covers on `U` and on `X`. -/

local instance instContinuous (X : TopCat.{u}) (U : Opens X) :
    (inclF X U).IsContinuous (Opens.grothendieckTopology U) (Opens.grothendieckTopology X) :=
  Functor.isContinuous_of_coverPreserving
    (compatiblePreservingOfDownwardsClosed _ _ (downClosed X U)) (instCoverPreserving X U)
#cloudR2Vendor restrictRing in

/-- The restriction `R|_U` of a sheaf of rings `R` on `X` to an open subset `U`, obtained
as the pullback along the open immersion `U ↪ X` (`sheafPushforwardContinuous` of the
open-inclusion functor).  This is the genuine `O_X|_U`. -/

noncomputable def restrictRing (X : TopCat.{u}) (U : Opens X)
    (R : Sheaf (Opens.grothendieckTopology X) RingCat.{u}) :
    Sheaf (Opens.grothendieckTopology U) RingCat.{u} :=
  ((inclF X U).sheafPushforwardContinuous RingCat.{u}
    (Opens.grothendieckTopology U) (Opens.grothendieckTopology X)).obj R
#cloudR2Vendor restrictMod in

/-- The restriction `F|_U` of a sheaf of `O_X`-modules `F` to an open subset `U`, with its
inherited `O_X|_U`-module structure.  It is the genuine pullback of `F` along the open
immersion `U ↪ X`, formalised as `SheafOfModules.pushforward` along the open-inclusion
functor over the identity morphism of the restricted ring sheaf `O_X|_U`. -/

noncomputable def restrictMod (X : TopCat.{u}) (U : Opens X)
    (R : Sheaf (Opens.grothendieckTopology X) RingCat.{u})
    (F : SheafOfModules.{u} R) :
    SheafOfModules.{u} (restrictRing X U R) :=
  (SheafOfModules.pushforward
    (J := Opens.grothendieckTopology U) (K := Opens.grothendieckTopology X)
    (F := inclF X U) (𝟙 (restrictRing X U R))).obj F
#cloudR2Vendor restrictModIsoOver in

/-- **The two ways of restricting a sheaf of modules to an open `U` agree on the nose.**
Mathlib's equivalence `TopologicalSpace.Opens.sheafOfModulesEquivOver` between sheaves of modules
on the slice site over `U` and sheaves of modules on the space `U` carries the slice restriction
`F.over U` to the genuine restriction `restrictMod X U R F`, and it does so definitionally: both
are `SheafOfModules.pushforward` along the open-inclusion functor `V ↦ V` of `Opens U ⥤ Opens X`
over the identity of the restricted sheaf of rings.

Naming the identification is what lets a trivialisation be produced from local-generator data:
`SheafOfModules.LocalGeneratorsData` is stated on the slice site, `Trivialization` on the space
`U`, and this is the only step between them. -/
noncomputable def restrictModIsoOver (X : TopCat.{u}) (U : Opens X)
    (R : Sheaf (Opens.grothendieckTopology X) RingCat.{u}) (F : SheafOfModules.{u} R) :
    (U.sheafOfModulesEquivOver R).functor.obj (F.over U) ≅ restrictMod X U R F :=
  Iso.refl _

-- ## Main Definition(s)
#cloudR2Vendor Trivialization in

/-- A *trivialisation* of a sheaf of `O_X`-modules `F` on an open set `U`: an index set `I`
together with an isomorphism, in the category of sheaves of `O_X|_U`-modules,
`F|_U ≅ ⊕_{i ∈ I} O_X|_U`, where `⊕_{i ∈ I} O_X|_U = SheafOfModules.free I` is the
categorical coproduct of `I` copies of the (restricted) structure sheaf.  Here `F|_U` is the
genuine restriction `restrictMod F` carrying the inherited `O_X|_U`-module structure. -/
structure Trivialization (X : TopCat.{u})
    (R : Sheaf (Opens.grothendieckTopology X) RingCat.{u})
    (F : SheafOfModules.{u} R) (U : Opens X) where
  /-- The index set of the free sheaf. -/
  ι : Type u
  /-- The trivialising isomorphism `F|_U ≅ ⊕_{i ∈ ι} O_X|_U` of sheaves of modules over the
  restricted structure sheaf `O_X|_U`. -/
  iso : restrictMod X U R F ≅ SheafOfModules.free.{u} ι
#cloudR2Vendor IsLocallyFree in

/-- A sheaf of `O_X`-modules `F` is *locally free* if every point `x : X` admits an open
neighbourhood `U` on which `F` is trivial, i.e. `F|_U ≅ ⊕_{i ∈ I} O_X|_U` for some index
set `I`. -/

def IsLocallyFree (X : TopCat.{u})
    (R : Sheaf (Opens.grothendieckTopology X) RingCat.{u})
    (F : SheafOfModules.{u} R) : Prop :=
  ∀ x : X, ∃ U : Opens X, x ∈ U ∧ Nonempty (Trivialization X R F U)
#cloudR2Vendor Trivialization.rank in

/-- The cardinality of the index set of a trivialisation. -/
noncomputable def Trivialization.rank {X : TopCat.{u}}
    {R : Sheaf (Opens.grothendieckTopology X) RingCat.{u}}
    {F : SheafOfModules.{u} R} {U : Opens X}
    (t : Trivialization X R F U) : Cardinal.{u} :=
  Cardinal.mk t.ι
#cloudR2Vendor toRingSheaf in

/-- The base sheaf of (possibly non-commutative) rings underlying a structure sheaf of
*commutative* rings `O`, obtained by composing with the forgetful functor
`CommRingCat ⥤ RingCat`.  Sheaves of modules over `O_X` are taken over this base. -/
noncomputable def toRingSheaf (X : TopCat.{u})
    (O : Sheaf (Opens.grothendieckTopology X) CommRingCat.{u}) :
    Sheaf (Opens.grothendieckTopology X) RingCat.{u} :=
  (sheafCompose _ (forget₂ CommRingCat.{u} RingCat.{u})).obj O
#cloudR2Vendor StalksNontrivial in

/-- The hypothesis that the support of `O_X` is all of `X`: every stalk `O_{X,x}` is a
nonzero ring. -/
def StalksNontrivial (X : TopCat.{u})
    (O : Sheaf (Opens.grothendieckTopology X) CommRingCat.{u}) : Prop :=
  ∀ x : X, Nontrivial (ToType (TopCat.Presheaf.stalk (X := X) O.obj x))

-- ## Stalk-of-morphism infrastructure (verified)
#cloudR2Vendor stalkLMap in

/-- From a morphism `f : M ⟶ N` of presheaves of modules over a sheaf of rings `R`, the
induced map on stalks at `x` is `R.stalk x`-linear. -/

noncomputable def stalkLMap {X : TopCat.{u}} {R : TopCat.Presheaf RingCat.{u} X}
    {M N : PresheafOfModules.{u} R} (f : M ⟶ N) (x : X) :
    ToType (TopCat.Presheaf.stalk M.presheaf x) →ₗ[ToType (R.stalk x)]
      ToType (TopCat.Presheaf.stalk N.presheaf x) where
  toFun := (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map ((PresheafOfModules.toPresheaf
      R).map f)
  map_add' a b := map_add _ a b
  map_smul' r m := by
    dsimp
    obtain ⟨U, hxU, m₀, rfl⟩ := TopCat.Presheaf.exists_germ_eq M.presheaf m
    obtain ⟨V, hxV, r₀, rfl⟩ := TopCat.Presheaf.exists_germ_eq R r
    set W : Opens X := U ⊓ V with hW
    have hxW : x ∈ W := ⟨hxU, hxV⟩
    have hr : (ConcreteCategory.hom (R.germ V x hxV)) r₀
        = (ConcreteCategory.hom (R.germ W x hxW))
            ((ConcreteCategory.hom (R.map (homOfLE (inf_le_right)).op)) r₀) := by
      rw [TopCat.Presheaf.germ_res_apply]
    have hm : (ConcreteCategory.hom (TopCat.Presheaf.germ M.presheaf U x hxU)) m₀
        = (ConcreteCategory.hom (TopCat.Presheaf.germ M.presheaf W x hxW))
            ((ConcreteCategory.hom (M.presheaf.map (homOfLE (inf_le_left)).op)) m₀) := by
      rw [TopCat.Presheaf.germ_res_apply]
    rw [hr, hm]
    set rr : ToType (R.obj (Opposite.op W)) := (ConcreteCategory.hom (R.map (homOfLE
        (inf_le_right)).op)) r₀ with hrr
    set mm : ToType (M.presheaf.obj (Opposite.op W)) := (ConcreteCategory.hom (M.presheaf.map
        (homOfLE (inf_le_left)).op)) m₀ with hmm
    rw [← PresheafOfModules.germ_ringCat_smul]
    erw [TopCat.Presheaf.stalkFunctor_map_germ_apply W x hxW ((PresheafOfModules.toPresheaf R).map
        f) (rr • mm)]
    erw [TopCat.Presheaf.stalkFunctor_map_germ_apply W x hxW ((PresheafOfModules.toPresheaf R).map
        f) mm]
    erw [← PresheafOfModules.germ_ringCat_smul N x W hxW rr ((ConcreteCategory.hom
        (((PresheafOfModules.toPresheaf R).map f).app (Opposite.op W))) mm)]
    congr 1
    exact (f.app (Opposite.op W)).hom.map_smul rr mm
#cloudR2Vendor stalkLEquivOfIso in
#cloudR2Vendor instModuleStalkF in

/-- From an isomorphism `e : M ≅ N` of presheaves of modules over a sheaf of rings `R`, the
induced `R.stalk x`-linear equivalence of stalks at `x`. -/
noncomputable def stalkLEquivOfIso {X : TopCat.{u}} {R : TopCat.Presheaf RingCat.{u} X}
    {M N : PresheafOfModules.{u} R} (e : M ≅ N) (x : X) :
    ToType (TopCat.Presheaf.stalk M.presheaf x) ≃ₗ[ToType (R.stalk x)]
      ToType (TopCat.Presheaf.stalk N.presheaf x) := by
  set EE := (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).mapIso
      ((PresheafOfModules.toPresheaf R).mapIso e) with hEE
  refine LinearEquiv.ofLinearMap (stalkLMap e.hom x) (stalkLMap e.inv x) ?_ ?_
  · ext z
    change (ConcreteCategory.hom EE.hom) ((ConcreteCategory.hom EE.inv) z) = z
    exact EE.inv_hom_id_apply z
  · ext z
    change (ConcreteCategory.hom EE.inv) ((ConcreteCategory.hom EE.hom) z) = z
    exact EE.hom_inv_id_apply z

-- ## Key sub-lemmas towards Stacks Tag 01C9

/-
## Proof outline (informal, rigorous)

We use the codomain `Cardinal` and define, for each `x : X`,
`rankF x := Cardinal.mk t.ι` for *some* trivialisation `t` on *some* open neighbourhood of
`x` (which exists by `hF`).  The whole content of the theorem then reduces to the single
algebraic fact `Trivialization.rank_eq_of_mem` below: any two trivialisations whose open
domains both contain `x` have the same rank.  Indeed:

* Well-definedness of the matching property `t.rank = rankF x` is *exactly* an instance of
  `rank_eq_of_mem` (compare an arbitrary `t` with the chosen trivialisation `t_x`).
* Local constancy: if `t_x` is the chosen trivialisation on `U_x ∋ x` then for every `y ∈ U_x`
  the restriction of `t_x` to a neighbourhood of `y` is again a trivialisation containing `y`,
  so `rankF y = rank(t_x) = rankF x`; hence `rankF` is constant on the open `U_x ∋ x`.

The crux `rank_eq_of_mem` is the standard "pass to the stalk + invariant basis number"
argument:

1. A trivialisation `t : F|_U ≅ ⊕_{i∈t.ι} O_X|_U` induces, by applying the stalk functor at
   `x ∈ U`, an isomorphism of `O_{X,x}`-modules `F_x ≅ (t.ι →₀ O_{X,x})`.  (The stalk of the
   restriction `F|_U` at `x ∈ U` is the stalk `F_x` since restriction is along an open
   immersion, an inducing map; and the stalk of the free sheaf `⊕_{i∈I} O_X|_U` is the free
   module `(I →₀ O_{X,x})` because the stalk functor `= colim` preserves the coproduct.)
2. Given two trivialisations `t` (on `U ∋ x`) and `s` (on `V ∋ x`), composing the two stalk
   isomorphisms gives a linear equivalence `(t.ι →₀ O_{X,x}) ≃ₗ[O_{X,x}] (s.ι →₀ O_{X,x})`.
3. Since `O_{X,x}` is a *nonzero* commutative ring (`hO`), it has `StrongRankCondition`
   (`commRing_strongRankCondition`), so taking `Module.rank` of both sides and using
   `rank_finsupp_self` yields `Cardinal.mk t.ι = Cardinal.mk s.ι`, i.e. `t.rank = s.rank`.
-/

/-- The `O_{X,x}`-module structure on the stalk `F_x` of a sheaf of `O_X`-modules at a
point `x`, where `O` is a sheaf of *commutative* rings.  This is Mathlib's
`PresheafOfModules` stalk-module instance, applied through the definitional equality
`(toRingSheaf X O).val = O.val ⋙ forget₂ CommRingCat RingCat` (instance search does not fire
through the `toRingSheaf`/`sheafCompose` wrapper, so we name it). -/
noncomputable local instance instModuleStalkF
    (X : TopCat.{u}) (O : Sheaf (Opens.grothendieckTopology X) CommRingCat.{u})
    (F : SheafOfModules.{u} (toRingSheaf X O)) (x : X) :
    Module (ToType (TopCat.Presheaf.stalk O.obj x))
      (ToType (TopCat.Presheaf.stalk F.val.presheaf x)) :=
  PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier F.val x
#cloudR2Vendor restrictStalkRing in

/-- Abbreviation for the *restricted* ring stalk `kU := (O_X|_U)_{⟨x,hU⟩}`, the natural base
ring over which the stalks of `restrictMod`/`SheafOfModules.free` at `⟨x,hU⟩ : ↥U` are
modules.  (The point lives in the subspace `↥U`, taken as `TopCat.of (U : Type u)`.) -/
noncomputable abbrev restrictStalkRing
    (X : TopCat.{u}) (O : Sheaf (Opens.grothendieckTopology X) CommRingCat.{u})
    (x : X) (U : Opens X) (hU : x ∈ U) : Type u :=
  ToType (@TopCat.Presheaf.stalk RingCat.{u} _ _ (TopCat.of (U : Type u))
    ((restrictRing X U (toRingSheaf X O)).obj) (⟨x, hU⟩ : (U : Type u)))
#cloudR2Vendor instModuleStalkRestrictMod in

/-- The `kU := restrictStalkRing`-module structure on the stalk of the restriction
`restrictMod X U R F` at `⟨x,hU⟩ : ↥U`.  This is Mathlib's `PresheafOfModules` stalk-module
instance for the `PresheafOfModules ((restrictRing …).val)` underlying `restrictMod`, named
so that instance search fires with the base ring written literally as `restrictStalkRing`. -/
noncomputable local instance instModuleStalkRestrictMod
    (X : TopCat.{u}) (O : Sheaf (Opens.grothendieckTopology X) CommRingCat.{u})
    (F : SheafOfModules.{u} (toRingSheaf X O))
    (x : X) (U : Opens X) (hU : x ∈ U) :
    Module (restrictStalkRing X O x U hU)
      (ToType (TopCat.Presheaf.stalk (X := TopCat.of (U : Type u))
          ((restrictMod X U (toRingSheaf X O) F).val.presheaf)
          (⟨x, hU⟩ : (U : Type u)))) :=
  PresheafOfModules.instModuleCarrierStalkRingCatCarrierAbPresheafOpensCarrier
    (X := TopCat.of (U : Type u))
    (R := (restrictRing X U (toRingSheaf X O)).obj)
    (restrictMod X U (toRingSheaf X O) F).val
    (⟨x, hU⟩ : (U : Type u))
#cloudR2Vendor instModuleStalkFree in

/-- The `kU := restrictStalkRing`-module structure on the stalk of the free sheaf
`SheafOfModules.free ι` over the restricted ring sheaf, at `⟨x,hU⟩ : ↥U`.  Named (analogously
to `instModuleStalkRestrictMod`) so that instance search fires with the base ring written
literally as `restrictStalkRing`. -/
noncomputable local instance instModuleStalkFree
    (X : TopCat.{u}) (O : Sheaf (Opens.grothendieckTopology X) CommRingCat.{u})
    (x : X) (U : Opens X) (hU : x ∈ U) (ι : Type u) :
    Module (restrictStalkRing X O x U hU)
      (ToType (TopCat.Presheaf.stalk (X := TopCat.of (U : Type u))
          ((SheafOfModules.free.{u} (R := restrictRing X U (toRingSheaf X O)) ι).val.presheaf)
          (⟨x, hU⟩ : (U : Type u)))) :=
  PresheafOfModules.instModuleCarrierStalkRingCatCarrierAbPresheafOpensCarrier
    (X := TopCat.of (U : Type u))
    (R := (restrictRing X U (toRingSheaf X O)).obj)
    (SheafOfModules.free.{u} (R := restrictRing X U (toRingSheaf X O)) ι).val
    (⟨x, hU⟩ : (U : Type u))
#cloudR2Vendor instModuleStalkUnit in

/-- The `kU := restrictStalkRing`-module structure on the stalk of the unit sheaf
`SheafOfModules.unit (restrictRing X U (toRingSheaf X O))`, at `⟨x,hU⟩ : ↥U`.  Named (analogously
to `instModuleStalkFree`) so that instance search fires with the base ring written literally
as `restrictStalkRing`. -/
noncomputable local instance instModuleStalkUnit
    (X : TopCat.{u}) (O : Sheaf (Opens.grothendieckTopology X) CommRingCat.{u})
    (x : X) (U : Opens X) (hU : x ∈ U) :
    Module (restrictStalkRing X O x U hU)
      (ToType (TopCat.Presheaf.stalk (X := TopCat.of (U : Type u))
          ((SheafOfModules.unit (restrictRing X U (toRingSheaf X O))).val.presheaf)
          (⟨x, hU⟩ : (U : Type u)))) :=
  PresheafOfModules.instModuleCarrierStalkRingCatCarrierAbPresheafOpensCarrier
    (X := TopCat.of (U : Type u))
    (R := (restrictRing X U (toRingSheaf X O)).obj)
    (SheafOfModules.unit (restrictRing X U (toRingSheaf X O))).val
    (⟨x, hU⟩ : (U : Type u))
#cloudR2Vendor Trivialization.stalk_restrictRing_ringEquiv in

/-- **(Sub-lemma (ring): reconciliation of the restricted ring stalk with the ambient stalk.)**
The stalk of the *restricted* structure sheaf `O_X|_U` at `⟨x,hU⟩ : ↥U` is ring-isomorphic to
the ambient stalk `O_{X,x}`.

PROOF (cofinality; no off-the-shelf iso — `stalkPushforward_iso_of_isInducing` does NOT
exist).  `restrictRing` is the *site* pushforward `sheafPushforwardContinuous` along
`inclF X U = IsOpenMap.functor (U.isOpenEmbedding'.isOpenMap)`.  The stalk at `⟨x,hU⟩` is
`colimit ((OpenNhds.inclusion ⟨x,hU⟩).op ⋙ —)`.  Via `IsOpenMap.adjunctionNhds ⟨x,hU⟩`
(`functorNhds ⟨x,hU⟩ ⊣ OpenNhds.map …`) the functor `functorNhds ⟨x,hU⟩` is `Initial`
(`Functor.initial_of_adjunction`), its `.op` is `Final` (`Functor.final_op_of_initial`), and
`Functor.Final.colimitIso` gives `(restrictRing …).val.stalk ⟨x,hU⟩ ≅ O.val.stalk x` (gluing
the neighbourhood diagrams with `OpenNhds.inclusionMapIso`); take the underlying `RingEquiv`. -/
theorem Trivialization.stalk_restrictRing_ringEquiv
    (X : TopCat.{u})
    (O : Sheaf (Opens.grothendieckTopology X) CommRingCat.{u})
    (x : X) {U : Opens X} (hU : x ∈ U) :
    Nonempty (restrictStalkRing X O x U hU ≃+* ToType (TopCat.Presheaf.stalk O.obj x)) := by
  -- Core cofinality iso (in RingCat) for the ring sheaf `R := toRingSheaf X O`:
  -- the stalk of the open-immersion pushforward `restrictRing` at `⟨x,hU⟩` is isomorphic to
  -- the ambient stalk of `R` at `x`.  Build it directly via `Functor.Final.colimitIso`:
  -- `restrictRing` is precomposition with `(inclF X U).op`, and
  -- `OpenNhds.inclusion ⟨x,hU⟩ ⋙ inclF X U = (functorNhds ⟨x,hU⟩) ⋙ OpenNhds.inclusion x`
  -- definitionally; `functorNhds ⟨x,hU⟩` is initial (adjunction), so its `.op` is final.
  have coreIso :
      (@TopCat.Presheaf.stalk RingCat.{u} _ _ (TopCat.of (U : Type u))
        ((restrictRing X U (toRingSheaf X O)).obj) (⟨x, hU⟩ : (U : Type u)))
        ≅ TopCat.Presheaf.stalk (toRingSheaf X O).obj x := by
    have h : IsOpenMap (ConcreteCategory.hom (U.inclusion')) := U.isOpenEmbedding'.isOpenMap
    have hinit : (h.functorNhds (⟨x,hU⟩ : (TopCat.of (U:Type u)))).Initial :=
      Functor.initial_of_adjunction (h.adjunctionNhds (⟨x,hU⟩ : (TopCat.of (U:Type u))))
    have hfin : (h.functorNhds (⟨x,hU⟩ : (TopCat.of (U:Type u)))).op.Final :=
      Functor.final_op_of_initial _
    exact Functor.Final.colimitIso (h.functorNhds (⟨x,hU⟩ : (TopCat.of (U:Type u)))).op
      ((OpenNhds.inclusion x).op ⋙ (toRingSheaf X O).obj)
  -- Underlying `RingEquiv` of the core iso.
  have eCore : restrictStalkRing X O x U hU ≃+*
      ToType (TopCat.Presheaf.stalk ((toRingSheaf X O).obj) x) :=
    coreIso.ringCatIsoToRingEquiv
  -- Reconcile the RingCat-stalk of `toRingSheaf X O` with the CommRingCat-stalk of `O`,
  -- using that `forget₂ CommRingCat RingCat` preserves the (filtered) colimit defining the
  -- stalk; the underlying types agree definitionally.
  have eRecon : ToType (TopCat.Presheaf.stalk ((toRingSheaf X O).obj) x)
      ≃+* ToType (TopCat.Presheaf.stalk O.obj x) :=
    (preservesColimitIso (forget₂ CommRingCat.{u} RingCat.{u})
      ((OpenNhds.inclusion x).op ⋙ O.obj)).symm.ringCatIsoToRingEquiv
  exact ⟨eCore.trans eRecon⟩
#cloudR2Vendor restrictStalkRingEquiv in

/-- The **canonical** ring isomorphism `kU := restrictStalkRing X O x U hU ≃+* O_{X,x}`,
the explicit data version of `stalk_restrictRing_ringEquiv` (same cofinality construction).
We expose it as a `def` so that the module-level sub-lemma `stalk_restrictMod_linearEquiv`
and the assembly body of `stalk_linearEquiv_finsupp` use *one and the same* ring iso — the
module-stalk reconciliation is `kU`-linear only with respect to THIS canonical iso (the colimit
comparison), not an arbitrary one. -/
noncomputable def restrictStalkRingEquiv
    (X : TopCat.{u})
    (O : Sheaf (Opens.grothendieckTopology X) CommRingCat.{u})
    (x : X) {U : Opens X} (hU : x ∈ U) :
    restrictStalkRing X O x U hU ≃+* ToType (TopCat.Presheaf.stalk O.obj x) := by
  have coreIso :
      (@TopCat.Presheaf.stalk RingCat.{u} _ _ (TopCat.of (U : Type u))
        ((restrictRing X U (toRingSheaf X O)).obj) (⟨x, hU⟩ : (U : Type u)))
        ≅ TopCat.Presheaf.stalk (toRingSheaf X O).obj x := by
    have h : IsOpenMap (ConcreteCategory.hom (U.inclusion')) := U.isOpenEmbedding'.isOpenMap
    haveI hinit : (h.functorNhds (⟨x,hU⟩ : (TopCat.of (U:Type u)))).Initial :=
      Functor.initial_of_adjunction (h.adjunctionNhds (⟨x,hU⟩ : (TopCat.of (U:Type u))))
    haveI hfin : (h.functorNhds (⟨x,hU⟩ : (TopCat.of (U:Type u)))).op.Final :=
      Functor.final_op_of_initial _
    exact Functor.Final.colimitIso (h.functorNhds (⟨x,hU⟩ : (TopCat.of (U:Type u)))).op
      ((OpenNhds.inclusion x).op ⋙ (toRingSheaf X O).obj)
  have eCore : restrictStalkRing X O x U hU ≃+*
      ToType (TopCat.Presheaf.stalk ((toRingSheaf X O).obj) x) :=
    coreIso.ringCatIsoToRingEquiv
  have eRecon : ToType (TopCat.Presheaf.stalk ((toRingSheaf X O).obj) x)
      ≃+* ToType (TopCat.Presheaf.stalk O.obj x) :=
    (preservesColimitIso (forget₂ CommRingCat.{u} RingCat.{u})
      ((OpenNhds.inclusion x).op ⋙ O.obj)).symm.ringCatIsoToRingEquiv
  exact eCore.trans eRecon
#cloudR2Vendor apply_eq_of_comp_eq in

/-- Elementwise form of an equation `f ≫ g = h` in a concrete category. -/
private theorem apply_eq_of_comp_eq {C : Type*} [Category C] {FC : C → C → Type*}
    {CC : C → Type*} [∀ X Y, FunLike (FC X Y) (CC X) (CC Y)] [ConcreteCategory C FC]
    {X Y Z : C} {f : X ⟶ Y} {g : Y ⟶ Z} {h : X ⟶ Z} (e : f ≫ g = h) (s : ToType X) :
    g (f s) = h s := by
  rw [← e, ConcreteCategory.comp_apply]

/-- The scalar-action/germ law with the ring presheaf given explicitly as a
functor on opens. The conversion to `TopCat.Presheaf` occurs only at this bridge. -/
private theorem germ_ring_smul_functor (Y : TopCat.{u})
    (R : (Opens Y)ᵒᵖ ⥤ RingCat.{u}) (M : PresheafOfModules.{u} R)
    (p : Y) (V : Opens Y) (hp : p ∈ V) (r : ToType (R.obj (.op V)))
    (m : ToType (M.presheaf.obj (.op V))) :
    TopCat.Presheaf.germ M.presheaf V p hp (r • m) =
      TopCat.Presheaf.germ (show TopCat.Presheaf RingCat.{u} Y from R) V p hp r •
        TopCat.Presheaf.germ M.presheaf V p hp m :=
  PresheafOfModules.germ_ringCat_smul
    (R := (show TopCat.Presheaf RingCat.{u} Y from R)) M p V hp r m

/-- The corresponding bridge for a commutative-ring presheaf and its underlying
ring-module presheaf. The stalk action is the actual commutative-ring action. -/
private theorem germ_commRing_smul_functor (Y : TopCat.{u})
    (O : (Opens Y)ᵒᵖ ⥤ CommRingCat.{u})
    (M : PresheafOfModules.{u} (O ⋙ forget₂ CommRingCat.{u} RingCat.{u}))
    (p : Y) (V : Opens Y) (hp : p ∈ V) (r : ToType (O.obj (.op V)))
    (m : ToType (M.presheaf.obj (.op V))) :
    TopCat.Presheaf.germ (X := Y) M.presheaf V p hp
        ((show ToType ((O ⋙ forget₂ CommRingCat.{u} RingCat.{u}).obj (.op V)) from r) • m) =
      TopCat.Presheaf.germ (X := Y)
          (show TopCat.Presheaf CommRingCat.{u} Y from O) V p hp r •
        TopCat.Presheaf.germ (X := Y) M.presheaf V p hp m :=
  PresheafOfModules.germ_smul (X := Y)
    (R := (show TopCat.Presheaf CommRingCat.{u} Y from O)) M p V hp r m

/-- The additive stalk comparison for open restriction, obtained from the
cofinal neighborhood functor. This construction has no scalar-action proof. -/
private noncomputable def restrictionStalkAddEquiv
    (X : TopCat.{u}) (U : Opens X)
    (R : Sheaf (Opens.grothendieckTopology X) RingCat.{u}) (F : SheafOfModules.{u} R)
    (x : X) (hU : x ∈ U) :
    ToType (TopCat.Presheaf.stalk (X := TopCat.of (U : Type u))
        (restrictMod X U R F).val.presheaf (⟨x, hU⟩ : (U : Type u))) ≃+
      ToType (TopCat.Presheaf.stalk F.val.presheaf x) := by
  let h : IsOpenMap (ConcreteCategory.hom (U.inclusion')) := U.isOpenEmbedding'.isOpenMap
  letI : (h.functorNhds (⟨x, hU⟩ : (U : Type u))).Initial :=
    Functor.initial_of_adjunction (h.adjunctionNhds (⟨x, hU⟩ : (U : Type u)))
  letI : (h.functorNhds (⟨x, hU⟩ : (U : Type u))).op.Final := Functor.final_op_of_initial _
  exact (Functor.Final.colimitIso (h.functorNhds (⟨x, hU⟩ : (U : Type u))).op
    ((OpenNhds.inclusion x).op ⋙ F.val.presheaf)).addCommGroupIsoToAddEquiv

/-- The additive restriction comparison sends an actual restricted germ to the
ambient germ on the image open. This is a single colimit-injection equation. -/
private theorem restrictionStalkAddEquiv_germ
    (X : TopCat.{u}) (U : Opens X)
    (R : Sheaf (Opens.grothendieckTopology X) RingCat.{u}) (F : SheafOfModules.{u} R)
    (x : X) (hU : x ∈ U) (V : Opens (TopCat.of (U : Type u)))
    (hp : (⟨x, hU⟩ : (U : Type u)) ∈ V) (hx : x ∈ (inclF X U).obj V)
    (s : ToType ((restrictMod X U R F).val.presheaf.obj (.op V))) :
    restrictionStalkAddEquiv X U R F x hU
        (TopCat.Presheaf.germ (X := TopCat.of (U : Type u))
          (restrictMod X U R F).val.presheaf V (⟨x, hU⟩ : (U : Type u)) hp s) =
      TopCat.Presheaf.germ F.val.presheaf ((inclF X U).obj V) x hx s := by
  let h : IsOpenMap (ConcreteCategory.hom (U.inclusion')) := U.isOpenEmbedding'.isOpenMap
  letI : (h.functorNhds (⟨x, hU⟩ : (U : Type u))).Initial :=
    Functor.initial_of_adjunction (h.adjunctionNhds (⟨x, hU⟩ : (U : Type u)))
  letI : (h.functorNhds (⟨x, hU⟩ : (U : Type u))).op.Final := Functor.final_op_of_initial _
  exact apply_eq_of_comp_eq
    (Functor.Final.ι_colimitIso_hom (h.functorNhds (⟨x, hU⟩ : (U : Type u))).op
      ((OpenNhds.inclusion x).op ⋙ F.val.presheaf) (.op ⟨V, hp⟩)) s

/-- Forgetting commutativity in the ambient stalk comparison preserves every
germ. This is the inverse filtered-colimit comparison on one injection. -/
private theorem forgetCommRing_stalk_germ
    (X : TopCat.{u}) (O : Sheaf (Opens.grothendieckTopology X) CommRingCat.{u})
    (x : X) (V : Opens X) (hx : x ∈ V) (r : ToType (O.obj.obj (.op V))) :
    (preservesColimitIso (forget₂ CommRingCat.{u} RingCat.{u})
        ((OpenNhds.inclusion x).op ⋙ O.obj)).symm.ringCatIsoToRingEquiv
        (TopCat.Presheaf.germ (toRingSheaf X O).obj V x hx r) =
      TopCat.Presheaf.germ O.obj V x hx r := by
  have hcol := ι_preservesColimitIso_inv (forget₂ CommRingCat.{u} RingCat.{u})
    ((OpenNhds.inclusion x).op ⋙ O.obj) (.op ⟨V, hx⟩)
  exact (apply_eq_of_comp_eq hcol r).trans rfl

/-- The fixed canonical ring equivalence for restriction sends a restricted
ring germ to its ambient commutative-ring germ. Scalar compatibility is thus
proved with the same ring comparison as in the public stalk equivalence. -/
private theorem restrictionStalkRingEquiv_germ
    (X : TopCat.{u}) (O : Sheaf (Opens.grothendieckTopology X) CommRingCat.{u})
    (x : X) {U : Opens X} (hU : x ∈ U) (V : Opens (TopCat.of (U : Type u)))
    (hp : (⟨x, hU⟩ : (U : Type u)) ∈ V) (hx : x ∈ (inclF X U).obj V)
    (r : ToType ((restrictRing X U (toRingSheaf X O)).obj.obj (.op V))) :
    restrictStalkRingEquiv X O x hU
        (TopCat.Presheaf.germ (X := TopCat.of (U : Type u))
          (restrictRing X U (toRingSheaf X O)).obj V (⟨x, hU⟩ : (U : Type u)) hp r) =
      TopCat.Presheaf.germ O.obj ((inclF X U).obj V) x hx r := by
  let h : IsOpenMap (ConcreteCategory.hom (U.inclusion')) := U.isOpenEmbedding'.isOpenMap
  letI : (h.functorNhds (⟨x, hU⟩ : (U : Type u))).Initial :=
    Functor.initial_of_adjunction (h.adjunctionNhds (⟨x, hU⟩ : (U : Type u)))
  letI : (h.functorNhds (⟨x, hU⟩ : (U : Type u))).op.Final := Functor.final_op_of_initial _
  let core := (Functor.Final.colimitIso (h.functorNhds (⟨x, hU⟩ : (U : Type u))).op
    ((OpenNhds.inclusion x).op ⋙ (toRingSheaf X O).obj)).ringCatIsoToRingEquiv
  let recon := (preservesColimitIso (forget₂ CommRingCat.{u} RingCat.{u})
    ((OpenNhds.inclusion x).op ⋙ O.obj)).symm.ringCatIsoToRingEquiv
  have coreEquation : core
      (TopCat.Presheaf.germ (X := TopCat.of (U : Type u))
        (restrictRing X U (toRingSheaf X O)).obj V (⟨x, hU⟩ : (U : Type u)) hp r) =
      TopCat.Presheaf.germ (toRingSheaf X O).obj ((inclF X U).obj V) x hx r :=
    apply_eq_of_comp_eq
      (Functor.Final.ι_colimitIso_hom (h.functorNhds (⟨x, hU⟩ : (U : Type u))).op
        ((OpenNhds.inclusion x).op ⋙ (toRingSheaf X O).obj) (.op ⟨V, hp⟩)) r
  exact (congrArg recon coreEquation).trans
    (forgetCommRing_stalk_germ X O x ((inclF X U).obj V) hx r)

/-- Scalar compatibility on the restriction stalk, split from the additive
comparison and its germ equations. Representatives are restricted to one
common open before either scalar-action bridge is applied. -/
private theorem restrictionStalkAddEquiv_smul
    (X : TopCat.{u}) (O : Sheaf (Opens.grothendieckTopology X) CommRingCat.{u})
    (F : SheafOfModules.{u} (toRingSheaf X O)) (x : X) {U : Opens X} (hU : x ∈ U)
    (c : restrictStalkRing X O x U hU)
    (m : ToType (TopCat.Presheaf.stalk (X := TopCat.of (U : Type u))
      (restrictMod X U (toRingSheaf X O) F).val.presheaf (⟨x, hU⟩ : (U : Type u)))) :
    letI : Module (restrictStalkRing X O x U hU)
        (ToType (TopCat.Presheaf.stalk F.val.presheaf x)) :=
      Module.compHom (ToType (TopCat.Presheaf.stalk F.val.presheaf x))
        (restrictStalkRingEquiv X O x hU).toRingHom
    restrictionStalkAddEquiv X U (toRingSheaf X O) F x hU (c • m) =
      c • restrictionStalkAddEquiv X U (toRingSheaf X O) F x hU m := by
  letI : Module (restrictStalkRing X O x U hU)
      (ToType (TopCat.Presheaf.stalk F.val.presheaf x)) :=
    Module.compHom (ToType (TopCat.Presheaf.stalk F.val.presheaf x))
      (restrictStalkRingEquiv X O x hU).toRingHom
  change restrictionStalkAddEquiv X U (toRingSheaf X O) F x hU (c • m) =
    restrictStalkRingEquiv X O x hU c • restrictionStalkAddEquiv X U (toRingSheaf X O) F x hU m
  obtain ⟨V, hxV, m₀, rfl⟩ := TopCat.Presheaf.exists_germ_eq
    (X := TopCat.of (U : Type u)) (C := AddCommGrpCat.{u})
    (restrictMod X U (toRingSheaf X O) F).val.presheaf m
  obtain ⟨W, hxW, r₀, rfl⟩ := TopCat.Presheaf.exists_germ_eq
    (X := TopCat.of (U : Type u)) (C := RingCat.{u})
    (restrictRing X U (toRingSheaf X O)).obj c
  have hxZ : (⟨x, hU⟩ : (U : Type u)) ∈ V ⊓ W := ⟨hxV, hxW⟩
  rw [← TopCat.Presheaf.germ_res_apply (X := TopCat.of (U : Type u)) (C := RingCat.{u})
      (restrictRing X U (toRingSheaf X O)).obj
      (homOfLE (inf_le_right : V ⊓ W ≤ W)) (⟨x, hU⟩ : (U : Type u)) hxZ r₀,
    ← TopCat.Presheaf.germ_res_apply (X := TopCat.of (U : Type u)) (C := AddCommGrpCat.{u})
      (restrictMod X U (toRingSheaf X O) F).val.presheaf
      (homOfLE (inf_le_left : V ⊓ W ≤ V)) (⟨x, hU⟩ : (U : Type u)) hxZ m₀]
  let rr : ToType ((restrictRing X U (toRingSheaf X O)).obj.obj (.op (V ⊓ W))) :=
    (restrictRing X U (toRingSheaf X O)).obj.map (homOfLE inf_le_right).op r₀
  let mm : ToType ((restrictMod X U (toRingSheaf X O) F).val.presheaf.obj (.op (V ⊓ W))) :=
    (restrictMod X U (toRingSheaf X O) F).val.presheaf.map (homOfLE inf_le_left).op m₀
  have hGerm := germ_ring_smul_functor (TopCat.of (U : Type u))
    (restrictRing X U (toRingSheaf X O)).obj (restrictMod X U (toRingSheaf X O) F).val
    (⟨x, hU⟩ : (U : Type u)) (V ⊓ W) hxZ rr mm
  rw [← hGerm]
  have hximg : x ∈ (inclF X U).obj (V ⊓ W) := ⟨⟨x, hU⟩, hxZ, rfl⟩
  rw [restrictionStalkAddEquiv_germ X U (toRingSheaf X O) F x hU (V ⊓ W) hxZ hximg (rr • mm),
    restrictionStalkAddEquiv_germ X U (toRingSheaf X O) F x hU (V ⊓ W) hxZ hximg mm,
    restrictionStalkRingEquiv_germ X O x hU (V ⊓ W) hxZ hximg rr]
  exact germ_commRing_smul_functor X O.obj F.val x ((inclF X U).obj (V ⊓ W)) hximg rr mm

set_option backward.isDefEq.respectTransparency.types false in
#cloudR2Vendor Trivialization.stalk_restrictMod_linearEquiv in
/-- **(Sub-lemma (a): stalk of the restriction = stalk of `F`.)**  The stalk of the restriction
`restrictMod X U R F` at `⟨x,hU⟩ : ↥U` is `kU`-linearly isomorphic to the ambient stalk `F_x`,
where `F_x` is regarded as a `kU`-module via restriction of scalars along the ring iso
`kU ≃+* O_{X,x}` of `stalk_restrictRing_ringEquiv`.

PROOF.  Same cofinality route as the ring reconciliation, carried out on the underlying
`AddCommGrpCat` presheaf of `F` (which `restrictMod` pushes forward), then lifted through the
module structure; compatibility with the ring iso is naturality of the colimit comparison.

NB: the target `F_x` is given its `kU`-module structure via the **canonical** ring iso
`restrictStalkRingEquiv` (the colimit comparison itself), NOT an arbitrary `e` — the additive
colimit-comparison iso is `kU`-linear only for that specific ring iso. -/
theorem Trivialization.stalk_restrictMod_linearEquiv
    (X : TopCat.{u})
    (O : Sheaf (Opens.grothendieckTopology X) CommRingCat.{u})
    (F : SheafOfModules.{u} (toRingSheaf X O))
    (x : X) {U : Opens X} (hU : x ∈ U) :
    Nonempty
      (@LinearEquiv (restrictStalkRing X O x U hU) (restrictStalkRing X O x U hU) _ _
        (RingHom.id _) (RingHom.id _) _ _
        (ToType (TopCat.Presheaf.stalk (X := TopCat.of (U : Type u))
          ((restrictMod X U (toRingSheaf X O) F).val.presheaf) (⟨x, hU⟩ : (U : Type u))))
        (ToType (TopCat.Presheaf.stalk F.val.presheaf x))
        _ _ _
        (Module.compHom (ToType (TopCat.Presheaf.stalk F.val.presheaf x))
          (restrictStalkRingEquiv X O x hU).toRingHom)) := by
  letI : Module (restrictStalkRing X O x U hU)
      (ToType (TopCat.Presheaf.stalk F.val.presheaf x)) :=
    Module.compHom (ToType (TopCat.Presheaf.stalk F.val.presheaf x))
      (restrictStalkRingEquiv X O x hU).toRingHom
  exact ⟨(restrictionStalkAddEquiv X U (toRingSheaf X O) F x hU).toLinearEquiv
    (fun c m => restrictionStalkAddEquiv_smul X O F x hU c m)⟩
#cloudR2Vendor unitStalkLEquiv in

/-- The stalk of the unit presheaf-of-modules `PresheafOfModules.unit R` (the ring presheaf `R`
regarded as a module over itself) at a point `x` is `R.stalk x`-linearly isomorphic to the ring
stalk `R.stalk x` itself.  The underlying additive isomorphism is the comparison isomorphism for
the forgetful functor `RingCat ⥤ AddCommGrpCat` (which preserves the filtered colimit defining the
stalk), and `R.stalk x`-linearity is multiplication in the ring stalk. -/
noncomputable def unitStalkLEquiv {X : TopCat.{u}} (R : TopCat.Presheaf RingCat.{u} X) (x : X) :
    (ToType (TopCat.Presheaf.stalk (PresheafOfModules.unit R).presheaf x))
      ≃ₗ[ToType (R.stalk x)]
      (ToType (R.stalk x)) := by
  set pIso : (forget₂ RingCat.{u} AddCommGrpCat.{u}).obj (R.stalk x) ≅
      TopCat.Presheaf.stalk (PresheafOfModules.unit R).presheaf x :=
    preservesColimitIso (forget₂ RingCat.{u} AddCommGrpCat.{u})
      ((OpenNhds.inclusion x).op ⋙ R) with hpIso
  set addE : (ToType (TopCat.Presheaf.stalk (PresheafOfModules.unit R).presheaf x)) ≃+
      ToType (R.stalk x) := pIso.symm.addCommGroupIsoToAddEquiv with haddE
  have key : ∀ (U : Opens X) (hxU : x ∈ U) (s : ToType ((PresheafOfModules.unit R).presheaf.obj
      (Opposite.op U))),
      addE ((ConcreteCategory.hom (TopCat.Presheaf.germ (PresheafOfModules.unit R).presheaf U x
          hxU)) s)
      = (ConcreteCategory.hom (R.germ U x hxU)) s := by
    intro U hxU s
    have h := ι_preservesColimitIso_inv (forget₂ RingCat.{u} AddCommGrpCat.{u})
      ((OpenNhds.inclusion x).op ⋙ R) (Opposite.op ⟨U, hxU⟩)
    rw [← hpIso] at h
    have h2 := congrArg (fun (f : _ ⟶ _) => (ConcreteCategory.hom f) s) h
    simp only [ConcreteCategory.comp_apply] at h2
    change (ConcreteCategory.hom pIso.inv)
        ((ConcreteCategory.hom (colimit.ι (((OpenNhds.inclusion x).op ⋙ R) ⋙ forget₂ RingCat.{u}
            AddCommGrpCat.{u}) (Opposite.op ⟨U, hxU⟩))) s)
        = (ConcreteCategory.hom ((forget₂ RingCat.{u} AddCommGrpCat.{u}).map (colimit.ι
            ((OpenNhds.inclusion x).op ⋙ R) (Opposite.op ⟨U, hxU⟩)))) s
    exact h2
  refine
    { toFun := addE
      invFun := addE.symm
      left_inv := addE.left_inv
      right_inv := addE.right_inv
      map_add' := addE.map_add
      map_smul' := ?_ }
  intro r m
  obtain ⟨U, hxU, m₀, rfl⟩ := TopCat.Presheaf.exists_germ_eq (PresheafOfModules.unit R).presheaf m
  obtain ⟨V, hxV, r₀, rfl⟩ := TopCat.Presheaf.exists_germ_eq R r
  set W : Opens X := U ⊓ V with hW
  have hxW : x ∈ W := ⟨hxU, hxV⟩
  have hr : (ConcreteCategory.hom (R.germ V x hxV)) r₀
      = (ConcreteCategory.hom (R.germ W x hxW))
          ((ConcreteCategory.hom (R.map (homOfLE (inf_le_right)).op)) r₀) := by
    rw [TopCat.Presheaf.germ_res_apply]
  have hm : (ConcreteCategory.hom (TopCat.Presheaf.germ (PresheafOfModules.unit R).presheaf U x
      hxU)) m₀
      = (ConcreteCategory.hom (TopCat.Presheaf.germ (PresheafOfModules.unit R).presheaf W x hxW))
          ((ConcreteCategory.hom
              ((PresheafOfModules.unit R).presheaf.map (homOfLE (inf_le_left)).op)) m₀) := by
    rw [TopCat.Presheaf.germ_res_apply]
  rw [hr, hm]
  set rr : ToType (R.obj (Opposite.op W)) := (ConcreteCategory.hom (R.map (homOfLE
      (inf_le_right)).op)) r₀ with hrr
  set mm : ToType ((PresheafOfModules.unit R).presheaf.obj (Opposite.op W)) :=
    (ConcreteCategory.hom ((PresheafOfModules.unit R).presheaf.map (homOfLE (inf_le_left)).op)) m₀
        with hmm
  rw [← PresheafOfModules.germ_ringCat_smul (PresheafOfModules.unit R) x W hxW rr mm]
  rw [key W hxW (rr • mm), key W hxW mm]
  dsimp only [RingHom.id_apply]
  have e1 : (rr • mm : ToType ((PresheafOfModules.unit R).presheaf.obj (Opposite.op W)))
      = (rr • (mm : ToType (R.obj (Opposite.op W))) : ToType (R.obj (Opposite.op W))) := rfl
  rw [e1, smul_eq_mul, map_mul, smul_eq_mul]
#cloudR2Vendor unitStalkLEquiv_germ in

/-- The identification of the stalk of the unit presheaf of modules with the ring stalk sends
the germ of a section to its germ as a function. -/
theorem unitStalkLEquiv_germ {X : TopCat.{u}}
    (R : X.Presheaf RingCat.{u}) (x : X) (U : Opens X) (hx : x ∈ U) (r : R.obj (.op U)) :
    LocallyFreeRank.unitStalkLEquiv R x
        (TopCat.Presheaf.germ (PresheafOfModules.unit R).presheaf U x hx r) =
      R.germ U x hx r :=
  congrArg (fun f => (ConcreteCategory.hom f) r)
    (ι_preservesColimitIso_inv (forget₂ RingCat.{u} AddCommGrpCat.{u})
      ((OpenNhds.inclusion x).op ⋙ R) (.op ⟨U, hx⟩))
#cloudR2Vendor Trivialization.stalk_unit_linearEquiv in

/-- **(Sub-lemma (b.1): stalk of the unit sheaf = the stalk ring.)**  The stalk at `⟨x,hU⟩ : ↥U`
of the underlying presheaf of `SheafOfModules.unit (restrictRing X U (toRingSheaf X O))` is
`kU`-linearly isomorphic to `kU` itself (the rank-one free module).

This is the third bridge of the stalk computation: `unit R` is the ring sheaf `R` regarded as a
module over itself; its underlying `AddCommGrpCat` presheaf is the additive group of `R.val`,
so its `Ab`-stalk is the additive group of the ring stalk `kU = stalk R.val ⟨x,hU⟩` (the
forgetful functor `RingCat ⥤ AddCommGrpCat` preserves the filtered colimit defining the stalk),
and the `kU`-module structure is multiplication in `kU`.  Likely route: identify
`(unit R).val.presheaf` with `(forget₂ RingCat AddCommGrpCat).mapPresheaf R.val` (definitionally
/ via the `unit` API), then the stalk-module structure on `unit` is `kU` acting on itself. -/
theorem Trivialization.stalk_unit_linearEquiv
    (X : TopCat.{u})
    (O : Sheaf (Opens.grothendieckTopology X) CommRingCat.{u})
    (x : X) {U : Opens X} (hU : x ∈ U) :
    Nonempty
      ((ToType (TopCat.Presheaf.stalk (X := TopCat.of (U : Type u))
          ((SheafOfModules.unit (restrictRing X U (toRingSheaf X O))).val.presheaf)
          (⟨x, hU⟩ : (U : Type u))))
        ≃ₗ[restrictStalkRing X O x U hU]
        (restrictStalkRing X O x U hU)) := by
  -- SANITY CHECK PASSED ...
  refine ⟨?_⟩
  exact unitStalkLEquiv (X := TopCat.of (U : Type u))
    (R := (restrictRing X U (toRingSheaf X O)).obj) (x := (⟨x, hU⟩ : (U : Type u)))
#cloudR2Vendor instModuleStalkPresheafCoprod in

/-- The `kU := restrictStalkRing`-module structure on the stalk of the **presheaf-level**
coproduct `∐ (fun _ : ι => (SheafOfModules.unit S).val)` (taken in `PresheafOfModules S.val`),
at `⟨x,hU⟩ : ↥U`.  Named (analogously to `instModuleStalkFree`) so that the `≃ₗ[kU]` statements
of the two b.2 bridge sub-lemmas elaborate. -/
noncomputable local instance instModuleStalkPresheafCoprod
    (X : TopCat.{u}) (O : Sheaf (Opens.grothendieckTopology X) CommRingCat.{u})
    (x : X) (U : Opens X) (hU : x ∈ U) (ι : Type u) :
    Module (restrictStalkRing X O x U hU)
      (ToType (TopCat.Presheaf.stalk (X := TopCat.of (U : Type u))
          ((∐ (fun _ : ι => (SheafOfModules.unit (restrictRing X U (toRingSheaf X O))).val)
            : PresheafOfModules.{u} ((restrictRing X U (toRingSheaf X O)).obj)).presheaf)
          (⟨x, hU⟩ : (U : Type u)))) :=
  PresheafOfModules.instModuleCarrierStalkRingCatCarrierAbPresheafOpensCarrier
    (X := TopCat.of (U : Type u))
    (R := (restrictRing X U (toRingSheaf X O)).obj)
    (∐ (fun _ : ι => (SheafOfModules.unit (restrictRing X U (toRingSheaf X O))).val)
      : PresheafOfModules.{u} ((restrictRing X U (toRingSheaf X O)).obj))
    (⟨x, hU⟩ : (U : Type u))
#cloudR2Vendor stalkFunctor_bijective_of_locally_bijective in

/-- A morphism `f : P ⟶ Q` of `AddCommGrpCat`-presheaves over the open-cover Grothendieck
topology of a space `X` that is *locally injective* and *locally surjective* induces a
**bijection on every topological stalk**.  (The germ argument: lift germs to representatives on
common opens; local injectivity makes the equalizer sieve a cover, so equal germs descend to a
smaller open; local surjectivity makes the image sieve a cover, so every germ of `Q` is hit.)
This is the stalkwise-isomorphism property of a local isomorphism, used to discharge Bridge (I)
(stalk invariance under sheafification). -/
theorem stalkFunctor_bijective_of_locally_bijective
    {X : TopCat.{u}} {P Q : TopCat.Presheaf AddCommGrpCat.{u} X} (f : P ⟶ Q)
    (hinj : Presheaf.IsLocallyInjective (Opens.grothendieckTopology X) f)
    (hsurj : Presheaf.IsLocallySurjective (Opens.grothendieckTopology X) f) (x : X) :
    Function.Bijective
      (ConcreteCategory.hom ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map f)) := by
  constructor
  · -- injective
    intro a b hab
    obtain ⟨U, hxU, sa, rfl⟩ := TopCat.Presheaf.exists_germ_eq P a
    obtain ⟨U', hxU', sb, rfl⟩ := TopCat.Presheaf.exists_germ_eq P b
    have hxW0 : x ∈ U ⊓ U' := ⟨hxU, hxU'⟩
    rw [← TopCat.Presheaf.germ_res_apply P (homOfLE inf_le_left) x hxW0 sa,
      ← TopCat.Presheaf.germ_res_apply P (homOfLE inf_le_right) x hxW0 sb] at hab ⊢
    generalize (ConcreteCategory.hom (P.map (homOfLE inf_le_left).op)) sa = sa' at hab ⊢
    generalize (ConcreteCategory.hom (P.map (homOfLE inf_le_right).op)) sb = sb' at hab ⊢
    rw [TopCat.Presheaf.stalkFunctor_map_germ_apply _ x hxW0 f sa',
      TopCat.Presheaf.stalkFunctor_map_germ_apply _ x hxW0 f sb'] at hab
    obtain ⟨W, hxW, iU, iV, hW⟩ := TopCat.Presheaf.germ_eq Q x hxW0 hxW0 _ _ hab
    rw [← NatTrans.naturality_apply f iU.op, ← NatTrans.naturality_apply f iV.op] at hW
    obtain ⟨V2, j, hj, hxV2⟩ := (hinj.equalizerSieve_mem _ _ hW) x hxW
    rw [← TopCat.Presheaf.germ_res_apply P (j ≫ iU) x hxV2 sa',
      ← TopCat.Presheaf.germ_res_apply P (j ≫ iV) x hxV2 sb']
    congr 1
    simpa [op_comp, Functor.map_comp] using hj
  · -- surjective
    intro t
    obtain ⟨U, hxU, s, rfl⟩ := TopCat.Presheaf.exists_germ_eq Q t
    have hsieve := hsurj.imageSieve_mem (U := U) s
    obtain ⟨V, i, ⟨u, hu⟩, hxV⟩ := hsieve x hxU
    refine ⟨(ConcreteCategory.hom (P.germ V x hxV)) u, ?_⟩
    rw [TopCat.Presheaf.stalkFunctor_map_germ_apply V x hxV f u]
    rw [hu]
    rw [TopCat.Presheaf.germ_res_apply Q i x hxV s]

/-- The canonical comparison from the presheaf coproduct of units to the
underlying presheaf of the free sheaf. -/
private noncomputable def presheafFreeComparison {Y : TopCat.{u}}
    (R : Sheaf (Opens.grothendieckTopology Y) RingCat.{u}) (ι : Type u) :
    (∐ (fun _ : ι => (SheafOfModules.unit R).val) : PresheafOfModules.{u} R.obj) ⟶
      (SheafOfModules.free.{u} (R := R) ι).val :=
  Limits.Sigma.desc (fun i => (SheafOfModules.forget R).map
    (Limits.Sigma.ι (fun _ : ι => SheafOfModules.unit R) i))

/-- One coproduct injection characterizes the preceding comparison. -/
private theorem presheafFreeComparison_ι {Y : TopCat.{u}}
    (R : Sheaf (Opens.grothendieckTopology Y) RingCat.{u}) (ι : Type u) (i : ι) :
    Limits.Sigma.ι (fun _ : ι => (SheafOfModules.unit R).val) i ≫
        presheafFreeComparison R ι =
      (SheafOfModules.forget R).map (Limits.Sigma.ι (fun _ : ι => SheafOfModules.unit R) i) :=
  Limits.Sigma.ι_comp_desc _ i

/-- Sheafification sends the canonical presheaf/free comparison to an
isomorphism. Both mapped cocones are colimiting, with the same injections. -/
private theorem presheafFreeComparison_sheafification_iso {Y : TopCat.{u}}
    (R : Sheaf (Opens.grothendieckTopology Y) RingCat.{u}) (ι : Type u) :
    IsIso ((PresheafOfModules.sheafification (𝟙 R.obj)).map (presheafFreeComparison R ι)) := by
  classical
  let unitS := SheafOfModules.unit R
  let Pfam : ι → PresheafOfModules.{u} R.obj := fun _ => unitS.val
  let SF := PresheafOfModules.sheafification (𝟙 R.obj)
  let adj := PresheafOfModules.sheafificationAdjunction (𝟙 R.obj)
  letI : SF.IsLeftAdjoint := adj.isLeftAdjoint
  letI : PreservesColimitsOfShape (Discrete ι) SF := inferInstance
  let εIso : (SheafOfModules.forget R ⋙ SF) ≅ 𝟭 _ :=
    (eqToIso (rfl : (SheafOfModules.forget R ⋙ PresheafOfModules.restrictScalars (𝟙 R.obj)) ⋙ SF
      = (SheafOfModules.forget R ⋙ SF)).symm) ≪≫ asIso adj.counit
  letI : PreservesColimitsOfShape (Discrete ι) (SheafOfModules.forget R ⋙ SF) :=
    preservesColimitsOfShape_of_natIso εIso.symm
  have hLc : IsColimit (SF.mapCocone (Cofan.mk (∐ Pfam) (Limits.Sigma.ι Pfam))) :=
    isColimitOfPreserves SF (coproductIsCoproduct Pfam)
  have hRc : IsColimit ((SheafOfModules.forget R ⋙ SF).mapCocone
      (Cofan.mk (∐ (fun _ : ι => unitS)) (Limits.Sigma.ι (fun _ : ι => unitS)))) :=
    isColimitOfPreserves (SheafOfModules.forget R ⋙ SF) (coproductIsCoproduct (fun _ : ι => unitS))
  let dnat : (Discrete.functor Pfam ⋙ SF) ≅
      (Discrete.functor (fun _ : ι => unitS) ⋙ (SheafOfModules.forget R ⋙ SF)) :=
    Discrete.natIso (fun _ => Iso.refl _)
  let Φ := IsColimit.coconePointsIsoOfNatIso hLc hRc dnat
  have hΦ : Φ.hom = SF.map (presheafFreeComparison R ι) := by
    apply hLc.hom_ext
    rintro ⟨i⟩
    rw [IsColimit.comp_coconePointsIsoOfNatIso_hom hLc hRc dnat ⟨i⟩]
    have hd : dnat.hom.app ⟨i⟩ = 𝟙 _ := by
      simp only [dnat, Discrete.natIso_hom_app, Iso.refl_hom]
    rw [hd, Category.id_comp]
    simp only [Functor.mapCocone_ι_app, Cofan.mk_ι_app, Functor.comp_map]
    rw [← SF.map_comp, presheafFreeComparison_ι]
  exact hΦ ▸ Φ.isIso_hom

/-- The comparison is a local isomorphism of underlying abelian presheaves;
this is a separate passage from module sheafification to ordinary sheafification. -/
private theorem presheafFreeComparison_localIso {Y : TopCat.{u}}
    (R : Sheaf (Opens.grothendieckTopology Y) RingCat.{u}) (ι : Type u) :
    (Opens.grothendieckTopology Y).W
      ((PresheafOfModules.toPresheaf R.obj).map (presheafFreeComparison R ι)) := by
  letI : IsIso ((PresheafOfModules.sheafification (𝟙 R.obj)).map
      (presheafFreeComparison R ι)) := presheafFreeComparison_sheafification_iso R ι
  have hpsiso : IsIso ((presheafToSheaf (Opens.grothendieckTopology Y) AddCommGrpCat.{u}).map
      ((PresheafOfModules.toPresheaf R.obj).map (presheafFreeComparison R ι))) :=
    inferInstanceAs (IsIso ((SheafOfModules.toSheaf R).map
      ((PresheafOfModules.sheafification (𝟙 R.obj)).map (presheafFreeComparison R ι))))
  exact (GrothendieckTopology.W_iff _ _).mpr hpsiso

/-- The local comparison yields the actual linear equivalence on each stalk.
Only bijectivity of the specified stalk map is used; no choice of a rank map. -/
private theorem presheafFreeComparison_stalkEquiv {Y : TopCat.{u}}
    (R : Sheaf (Opens.grothendieckTopology Y) RingCat.{u}) (ι : Type u) (p : Y) :
    Nonempty
      (ToType (TopCat.Presheaf.stalk (SheafOfModules.free.{u} (R := R) ι).val.presheaf p)
        ≃ₗ[ToType (TopCat.Presheaf.stalk R.obj p)]
        ToType (TopCat.Presheaf.stalk
          (∐ (fun _ : ι => (SheafOfModules.unit R).val) : PresheafOfModules.{u} R.obj).presheaf p)) := by
  let η := presheafFreeComparison R ι
  let ηp := (PresheafOfModules.toPresheaf R.obj).map η
  have hW : (Opens.grothendieckTopology Y).W ηp := presheafFreeComparison_localIso R ι
  have hbij := stalkFunctor_bijective_of_locally_bijective ηp
    hW.isLocallyInjective hW.isLocallySurjective p
  have hg : (stalkLMap η p : _ → _) =
      (ConcreteCategory.hom ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} p).map ηp)) := rfl
  exact ⟨(LinearEquiv.ofBijective (stalkLMap η p) (by rw [hg]; exact hbij)).symm⟩

#cloudR2Vendor Trivialization.stalk_free_presheafCoprod_linearEquiv in
/-- **(b.2 Bridge (I): the sheaf coproduct and the presheaf coproduct have the SAME stalk.)**
The stalk at `⟨x,hU⟩ : ↥U` of the underlying presheaf of the *sheaf* coproduct `free ι`
(`= ∐^{Sheaf} unit`) is `kU`-linearly isomorphic to the stalk of the *presheaf-level* coproduct
`∐^{psh} (unit.val)` (taken in `PresheafOfModules ((restrictRing …).val)`).

THIS IS THE SUBSTANTIVE OBSTRUCTION.
`free ι = ∐^{Sheaf} unit` and the underlying presheaf of a sheaf coproduct is the
*sheafification* of the presheaf coproduct.  The sheafification unit `η : ∐^{psh} unit.val ⟶
(free ι).val` (an `S.val`-`PresheafOfModules` morphism, the comparison from `isColimitFreeCofan`
through the forgetful functor) is a *local isomorphism* for `Opens.grothendieckTopology ↥U`,
hence induces an **isomorphism on every topological stalk** (the stalk is invariant under
sheafification).  PROOF ROUTE (closer's recommended decomposition):
* build `η` as the canonical map `∐^{psh} unit.val ⟶ (free ι).val` (the comparison of the
  presheaf coproduct cocone with the image of `freeCofan ι` under the forgetful functor
  `SheafOfModules.forget` — both are cocones under `fun _ => unit.val`);
* show `η` is locally injective + locally surjective (`Presheaf.IsLocallyInjective`/
  `IsLocallySurjective` for the sheafification unit `toSheafify`), so `(stalkFunctor Ab
  ⟨x,hU⟩).map η.app...` is an iso (via `stalkFunctor_map_injective_of_app_injective` +
  `app_surjective_of_stalkFunctor_map_bijective`-style germ lemmas, confirmed available for
  `AddCommGrpCat`);
* upgrade the additive stalk iso to `kU`-linear via `stalkLMap`/germ-`smul` compatibility
  (`PresheafOfModules.germ_ringCat_smul`, as in `unitStalkLEquiv`/`stalkLMap`). -/
theorem Trivialization.stalk_free_presheafCoprod_linearEquiv
    (X : TopCat.{u})
    (O : Sheaf (Opens.grothendieckTopology X) CommRingCat.{u})
    (x : X) {U : Opens X} (hU : x ∈ U)
    (ι : Type u) :
    Nonempty
      ((ToType (TopCat.Presheaf.stalk (X := TopCat.of (U : Type u))
          ((SheafOfModules.free.{u} (R := restrictRing X U (toRingSheaf X O)) ι).val.presheaf)
          (⟨x, hU⟩ : (U : Type u))))
        ≃ₗ[restrictStalkRing X O x U hU]
        (ToType (TopCat.Presheaf.stalk (X := TopCat.of (U : Type u))
          ((∐ (fun _ : ι => (SheafOfModules.unit (restrictRing X U (toRingSheaf X O))).val)
            : PresheafOfModules.{u} ((restrictRing X U (toRingSheaf X O)).obj)).presheaf)
          (⟨x, hU⟩ : (U : Type u))))) := by
  exact presheafFreeComparison_stalkEquiv (Y := TopCat.of (U : Type u))
    (restrictRing X U (toRingSheaf X O)) ι (⟨x, hU⟩ : (U : Type u))
#cloudR2Vendor Trivialization.stalk_presheafCoprod_directSum_linearEquiv in

/-- **(b.2 Bridges (II)+(III)+(IV): stalk of the presheaf coproduct = direct sum of unit-stalks.)**
The stalk at `⟨x,hU⟩ : ↥U` of the *presheaf-level* coproduct `∐^{psh} (unit.val)` (in
`PresheafOfModules ((restrictRing …).val)`) is `kU`-linearly isomorphic to the direct sum
`⨁ (_ : ι), (unit-stalk)`.

This is the TRACTABLE half (no sheafification).  PROOF ROUTE:
* `PresheafOfModules.toPresheaf` preserves colimits (confirmed:
`preservesColimitsOfSize_of_univLE`),
  so `(∐^{psh} unit.val).presheaf ≅ ∐^{psh,Ab} (unit.val.presheaf)` (coproduct in
  `TopCat.Presheaf Ab ↥U`);
* `TopCat.Presheaf.stalkFunctor AddCommGrpCat ⟨x,hU⟩` `PreservesColimits` (by `inferInstance`),
  so via `preservesColimitIso` / `isColimitOfPreserves` the stalk of that presheaf coproduct is
  the `Ab`-coproduct `∐^{Ab}_ι (stalk (unit.val.presheaf) ⟨x,hU⟩)`;
* identify the `Ab`-coproduct with `⨁` via `ModuleCat.coprodIsoDirectSum` (at the `ModuleCat kU`
  level, where the comparison maps are `LinearEquiv`s);
* thread `kU`-linearity throughout (perform the comparison isos at `ModuleCat kU` level). -/
theorem Trivialization.stalk_presheafCoprod_directSum_linearEquiv
    (X : TopCat.{u})
    (O : Sheaf (Opens.grothendieckTopology X) CommRingCat.{u})
    (x : X) {U : Opens X} (hU : x ∈ U)
    (ι : Type u) :
    Nonempty
      ((ToType (TopCat.Presheaf.stalk (X := TopCat.of (U : Type u))
          ((∐ (fun _ : ι => (SheafOfModules.unit (restrictRing X U (toRingSheaf X O))).val)
            : PresheafOfModules.{u} ((restrictRing X U (toRingSheaf X O)).obj)).presheaf)
          (⟨x, hU⟩ : (U : Type u))))
        ≃ₗ[restrictStalkRing X O x U hU]
        (DirectSum ι (fun _ : ι =>
          (ToType (TopCat.Presheaf.stalk (X := TopCat.of (U : Type u))
            ((SheafOfModules.unit (restrictRing X U (toRingSheaf X O))).val.presheaf)
            (⟨x, hU⟩ : (U : Type u))))))) := by
  -- SANITY CHECK PASSED  (inherits b.2's check: tractable presheaf-coproduct half, no
  -- sheafification; toPresheaf + stalkFunctor both preserve the Discrete ι colimit, so the
  -- stalk of the presheaf coproduct is the Ab/kU-coproduct of unit-stalks = ⨁; well-encoded.)
  -- Bridges (II)+(III)+(IV): toPresheaf preserves coprod ⇒ stalk of presheaf-coprod = ∐ stalks;
  -- stalkFunctor preserves coprod; ModuleCat.coprodIsoDirectSum to land at ⨁.
  classical
  set Y : TopCat.{u} := TopCat.of (U : Type u) with hY
  set p : (Y : Type u) := (⟨x, hU⟩ : (U : Type u)) with hp
  set S : TopCat.Presheaf RingCat.{u} Y := (restrictRing X U (toRingSheaf X O)).obj with hS
  set unitval : PresheafOfModules.{u} S :=
    (SheafOfModules.unit (restrictRing X U (toRingSheaf X O))).val with hunit
  set C : PresheafOfModules.{u} S := ∐ (fun _ : ι => unitval) with hC
  set G : PresheafOfModules.{u} S ⥤ AddCommGrpCat.{u} :=
    (PresheafOfModules.toPresheaf S) ⋙ (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} p) with hG
  have hpc : PreservesColimit (Discrete.functor (fun _ : ι => unitval)) G := by
    have h1 : PreservesColimit (Discrete.functor (fun _ : ι => unitval))
        (PresheafOfModules.toPresheaf S) := inferInstance
    have h2 : PreservesColimit
        ((Discrete.functor (fun _ : ι => unitval)) ⋙ PresheafOfModules.toPresheaf S)
        (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} p) :=
      (inferInstance : PreservesColimits (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} p)
        ).preservesColimitsOfShape.preservesColimit
    exact comp_preservesColimit (PresheafOfModules.toPresheaf S)
      (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} p)
  -- The kU-linear assembled map: ⨁ → stalk(C.presheaf) p, built from the stalk-maps of the
  -- coproduct injections.  This is manifestly kU-linear.
  set kU : Type u := restrictStalkRing X O x U hU with hkU
  set P : ι → PresheafOfModules.{u} S := fun _ => unitval with hP
  set g : (DirectSum ι (fun _ : ι =>
      (ToType (TopCat.Presheaf.stalk (X := Y)
        (unitval.presheaf) p)))) →ₗ[kU]
      (ToType (TopCat.Presheaf.stalk (X := Y) (C.presheaf) p)) :=
    DirectSum.toModule kU ι _ (fun i => stalkLMap (Limits.Sigma.ι P i) p) with hg
  -- The additive comparison iso from the two colimit cocones over `Discrete.functor P ⋙ G`.
  have hcol : IsColimit (G.mapCocone (Cofan.mk (∐ P) (Limits.Sigma.ι P))) :=
    isColimitOfPreserves G (coproductIsCoproduct P)
  -- The DirectSum colimit cocone on the family `fun i => G.obj (P i)`.
  set M : ι → Type u := fun _ => ToType (TopCat.Presheaf.stalk (X := Y) (unitval.presheaf) p)
    with hM
  set Dpt : AddCommGrpCat.{u} := AddCommGrpCat.of (DirectSum ι (fun i => M i)) with hDpt
  set Dcofan : Cofan (fun i => G.obj (P i)) :=
    Cofan.mk Dpt (fun i => AddCommGrpCat.ofHom (DirectSum.lof kU ι M i).toAddMonoidHom) with hDcofan
  have Dcol : IsColimit Dcofan := by
    refine Cofan.IsColimit.mk Dcofan
      (fun t => AddCommGrpCat.ofHom
        (DirectSum.toAddMonoid (fun i => (t.inj i).hom))) ?_ ?_
    · intro t i
      ext m
      change (DirectSum.toAddMonoid (fun i => (t.inj i).hom))
        ((DirectSum.of M i) m) = (t.inj i).hom m
      exact DirectSum.toAddMonoid_of (fun i => (t.inj i).hom) i m
    · intro t m hm
      ext z
      change m.hom z = (DirectSum.toAddMonoid (fun i => (t.inj i).hom)) z
      have key : m.hom = (DirectSum.toAddMonoid (fun i => (t.inj i).hom) :
          (DirectSum ι (fun i => M i)) →+ _) := by
        refine DirectSum.addHom_ext (β := M) (fun i y => ?_)
        have h2 := DFunLike.congr_fun (congrArg AddCommGrpCat.Hom.hom (hm i)) y
        change m.hom ((DirectSum.of M i) y) = (DirectSum.toAddMonoid (fun i => (t.inj i).hom))
          ((DirectSum.of M i) y)
        have hrhs : (DirectSum.toAddMonoid (fun i => (t.inj i).hom))
            ((DirectSum.of M i) y) = (t.inj i).hom y :=
          DirectSum.toAddMonoid_of (fun i => (t.inj i).hom) i y
        rw [hrhs]
        change m.hom ((DirectSum.lof kU ι M i) y) = (t.inj i).hom y
        rw [show (DirectSum.lof kU ι M i) y = (Dcofan.inj i).hom y from rfl, ← h2]
        rfl
      exact DFunLike.congr_fun key z
  -- The additive comparison iso `stalk(C.presheaf) p ≅ DirectSum` (carrier Dpt).
  set Φ := IsColimit.coconePointsIsoOfNatIso hcol Dcol
    (Discrete.natIso (fun _ => Iso.refl _)) with hΦ
  -- `g` agrees with `Φ.inv` as a function, hence is bijective.
  have hgeq : (g : (DirectSum ι (fun i => M i)) → _) = Φ.inv.hom := by
    have hext : g.toAddMonoidHom = Φ.inv.hom := by
      refine DirectSum.addHom_ext (β := M) (fun i y => ?_)
      have hfac := IsColimit.comp_coconePointsIsoOfNatIso_inv hcol Dcol
        (Discrete.natIso (fun _ => Iso.refl _)) ⟨i⟩
      have hfac2 := DFunLike.congr_fun (congrArg AddCommGrpCat.Hom.hom hfac) y
      -- LHS of hfac2: (Dcofan.inj i ≫ Φ.inv).hom y = Φ.inv.hom (lof i y)
      -- RHS: (𝟙 ≫ G.map (Sigma.ι P i)).hom y = (G.map (Sigma.ι P i)).hom y
      change (g.toAddMonoidHom) ((DirectSum.of M i) y) = Φ.inv.hom ((DirectSum.of M i) y)
      have hg1 : (g.toAddMonoidHom) ((DirectSum.of M i) y)
          = (stalkLMap (Limits.Sigma.ι P i) p) y := by
        change g ((DirectSum.of M i) y) = _
        rw [hg]
        rw [show (DirectSum.of M i) y = (DirectSum.lof kU ι M i) y from rfl]
        rw [DirectSum.toModule_lof]
      -- both sides equal (G.map (Sigma.ι P i)).hom y
      have hL : (stalkLMap (Limits.Sigma.ι P i) p) y = (G.map (Limits.Sigma.ι P i)).hom y := rfl
      have hR : Φ.inv.hom ((DirectSum.of M i) y) = (G.map (Limits.Sigma.ι P i)).hom y := by
        have hfac2' : Φ.inv.hom ((DirectSum.lof kU ι M i) y)
            = ((Discrete.natIso (fun _ => Iso.refl ((Discrete.functor P ⋙ G).obj _))).inv.app
                ⟨i⟩ ≫ (G.mapCocone (Cofan.mk (∐ P) (Limits.Sigma.ι P))).ι.app ⟨i⟩).hom y := by
          have := hfac2
          exact this
        change Φ.inv.hom ((DirectSum.lof kU ι M i) y) = _
        rw [hfac2']
        rfl
      rw [hg1, hL, hR]
    exact congrArg (fun (f : _ →+ _) => (f : _ → _)) hext
  have hbij : Function.Bijective (g : (DirectSum ι (fun i => M i)) → _) := by
    rw [hgeq]
    exact (ConcreteCategory.bijective_of_isIso Φ.inv)
  exact ⟨(LinearEquiv.ofBijective g hbij).symm⟩
#cloudR2Vendor Trivialization.stalk_free_directSum_linearEquiv in

/-- **(Sub-lemma (b.2): stalk of free = direct sum of unit-stalks.)**  The stalk at `⟨x,hU⟩ : ↥U`
of the free sheaf `SheafOfModules.free ι` (over the restricted ring sheaf) is `kU`-linearly
isomorphic to the direct sum `⨁ (_ : ι), (unit-stalk)`, where `unit-stalk` is the stalk of
`SheafOfModules.unit`.

This packages the first two bridges of the stalk computation (the substantive content):
`free ι = ∐ (fun _ : ι => unit)` in `SheafOfModules R` (`isColimitFreeCofan`); the underlying
`Ab`-presheaf of this *sheaf* coproduct is the *sheafification* of the presheaf coproduct (so
the forgetful functor does NOT directly preserve it), but the topological stalk is invariant
under sheafification, and `stalkFunctor AddCommGrpCat ⟨x,hU⟩` (which `PreservesColimits` by
`inferInstance`) preserves the presheaf coproduct.  Hence the stalk of `free ι` is the `Ab`/
`kU`-coproduct of the stalks of `unit`, identified with `DirectSum` via
`ModuleCat.coprodIsoDirectSum`.
The crux obligation is reconciling the *site* sheafification for `Opens.grothendieckTopology ↥U`
with the space-level `TopCat.Presheaf` stalk so a sheafification-stalk-iso applies. -/
theorem Trivialization.stalk_free_directSum_linearEquiv
    (X : TopCat.{u})
    (O : Sheaf (Opens.grothendieckTopology X) CommRingCat.{u})
    (x : X) {U : Opens X} (hU : x ∈ U)
    (ι : Type u) :
    Nonempty
      ((ToType (TopCat.Presheaf.stalk (X := TopCat.of (U : Type u))
          ((SheafOfModules.free.{u} (R := restrictRing X U (toRingSheaf X O)) ι).val.presheaf)
          (⟨x, hU⟩ : (U : Type u))))
        ≃ₗ[restrictStalkRing X O x U hU]
        (DirectSum ι (fun _ : ι =>
          (ToType (TopCat.Presheaf.stalk (X := TopCat.of (U : Type u))
            ((SheafOfModules.unit (restrictRing X U (toRingSheaf X O))).val.presheaf)
            (⟨x, hU⟩ : (U : Type u))))))) := by
  -- Both sides carry the same restricted stalk-ring action.
  -- ASSEMBLY (Bridge (I) ∘ Bridges (II)+(III)+(IV)): compose the two bridge sub-lemmas.
  obtain ⟨eI⟩ := Trivialization.stalk_free_presheafCoprod_linearEquiv X O x hU ι
  obtain ⟨eII⟩ := Trivialization.stalk_presheafCoprod_directSum_linearEquiv X O x hU ι
  exact ⟨eI.trans eII⟩
#cloudR2Vendor Trivialization.stalk_free_linearEquiv in

/-- The stalk of `SheafOfModules.free ι` over the restricted ring sheaf, at `⟨x, hU⟩ : ↥U`, is
`kU`-linearly isomorphic to the free module `ι →₀ kU`. -/
theorem Trivialization.stalk_free_linearEquiv
    (X : TopCat.{u})
    (O : Sheaf (Opens.grothendieckTopology X) CommRingCat.{u})
    (x : X) {U : Opens X} (hU : x ∈ U)
    (ι : Type u) :
    Nonempty
      ((ToType (TopCat.Presheaf.stalk (X := TopCat.of (U : Type u))
          ((SheafOfModules.free.{u} (R := restrictRing X U (toRingSheaf X O)) ι).val.presheaf)
          (⟨x, hU⟩ : (U : Type u))))
        ≃ₗ[restrictStalkRing X O x U hU]
        (ι →₀ restrictStalkRing X O x U hU)) := by
  -- The free stalk and its finsupp model use the same index type and scalar ring.
  classical
  -- (b.2): free-stalk ≃ₗ[kU] ⨁ (_ : ι), (unit-stalk)
  obtain ⟨eDS⟩ := Trivialization.stalk_free_directSum_linearEquiv X O x hU ι
  -- (b.1): unit-stalk ≃ₗ[kU] kU
  obtain ⟨eUnit⟩ := Trivialization.stalk_unit_linearEquiv X O x hU
  -- ⨁ (unit-stalk) ≃ₗ[kU] ⨁ (_ : ι), kU, applying eUnit summandwise
  let eCongr :
      (DirectSum ι (fun _ : ι =>
        (ToType (TopCat.Presheaf.stalk (X := TopCat.of (U : Type u))
          ((SheafOfModules.unit (restrictRing X U (toRingSheaf X O))).val.presheaf)
          (⟨x, hU⟩ : (U : Type u))))))
        ≃ₗ[restrictStalkRing X O x U hU]
        (DirectSum ι (fun _ : ι => restrictStalkRing X O x U hU)) :=
    DirectSum.congrLinearEquiv (fun _ : ι => eUnit)
  -- Final: ⨁ (_ : ι), kU ≃ₗ[kU] (ι →₀ kU)
  refine ⟨eDS.trans (eCongr.trans (finsuppLEquivDirectSum
    (restrictStalkRing X O x U hU) (restrictStalkRing X O x U hU) ι).symm)⟩

/-- Transport a linear equivalence to a finsupp module through a ring
isomorphism. The source module is restricted along the same ring isomorphism. -/
private noncomputable def transportFinsuppLinearEquiv
    {R S M : Type u} [Ring R] [Ring S] [AddCommGroup M] [Module S M]
    (e : R ≃+* S) {ι : Type u}
    (g : letI : Module R M := Module.compHom M e.toRingHom
      M ≃ₗ[R] (ι →₀ R)) : M ≃ₗ[S] (ι →₀ S) := by
  letI : Module R M := Module.compHom M e.toRingHom
  let h : M ≃+ (ι →₀ S) := g.toAddEquiv.trans (Finsupp.mapRange.addEquiv e.toAddEquiv)
  refine
    { toFun := h
      invFun := h.symm
      left_inv := h.left_inv
      right_inv := h.right_inv
      map_add' := h.map_add
      map_smul' := ?_ }
  intro c m
  change h (c • m) = c • h m
  have hsmul : c • m = (e.symm c) • m := by
    have h1 : (e.symm c) • m = (e (e.symm c)) • m := rfl
    rw [h1, e.apply_symm_apply]
  have hg := g.map_smul (e.symm c) m
  rw [hsmul]
  change Finsupp.mapRange.addEquiv e.toAddEquiv (g.toAddEquiv ((e.symm c) • m)) = c • _
  have hgg : g.toAddEquiv (e.symm c • m) = e.symm c • g m := hg
  rw [hgg]
  ext i
  change (Finsupp.mapRange.addEquiv e.toAddEquiv (e.symm c • g m)) i =
    (c • Finsupp.mapRange.addEquiv e.toAddEquiv (g m)) i
  have he : ∀ y : R, e.toAddEquiv y = e y := fun _ => rfl
  simp only [Finsupp.mapRange.addEquiv_apply, Finsupp.mapRange_apply, Finsupp.coe_smul,
    Pi.smul_apply, smul_eq_mul, he, map_mul, e.apply_symm_apply]

/-- A trivialization first gives a linear equivalence over the restricted
stalk ring. Its construction is separated from the change-of-scalars proof. -/
private theorem Trivialization.stalk_restricted_finsupp
    (X : TopCat.{u}) (O : Sheaf (Opens.grothendieckTopology X) CommRingCat.{u})
    (F : SheafOfModules.{u} (toRingSheaf X O)) (x : X) {U : Opens X} (hU : x ∈ U)
    (t : Trivialization X (toRingSheaf X O) F U) :
    Nonempty
      (letI : Module (restrictStalkRing X O x U hU)
          (ToType (TopCat.Presheaf.stalk F.val.presheaf x)) :=
        Module.compHom (ToType (TopCat.Presheaf.stalk F.val.presheaf x))
          (restrictStalkRingEquiv X O x hU).toRingHom
       ToType (TopCat.Presheaf.stalk F.val.presheaf x) ≃ₗ[restrictStalkRing X O x U hU]
         (t.ι →₀ restrictStalkRing X O x U hU)) := by
  letI : Module (restrictStalkRing X O x U hU)
      (ToType (TopCat.Presheaf.stalk F.val.presheaf x)) :=
    Module.compHom (ToType (TopCat.Presheaf.stalk F.val.presheaf x))
      (restrictStalkRingEquiv X O x hU).toRingHom
  obtain ⟨ea⟩ := Trivialization.stalk_restrictMod_linearEquiv X O F x hU
  obtain ⟨eb⟩ := Trivialization.stalk_free_linearEquiv X O x hU t.ι
  let mid := stalkLEquivOfIso (X := TopCat.of (U : Type u))
    (R := (restrictRing X U (toRingSheaf X O)).obj)
    ((SheafOfModules.forget (restrictRing X U (toRingSheaf X O))).mapIso t.iso)
    (⟨x, hU⟩ : (U : Type u))
  exact ⟨ea.symm.trans (mid.trans eb)⟩

#cloudR2Vendor Trivialization.stalk_linearEquiv_finsupp in
/-- **(Crux helper_01c9.)**  A trivialisation `t : F|_U ≅ ⊕_{i∈t.ι} O_X|_U` over an open `U ∋ x`
induces, on passing to stalks at `x`, an `O_{X,x}`-linear equivalence of the stalk `F_x`
with the free `O_{X,x}`-module `t.ι →₀ O_{X,x}`.

ASSEMBLY (from the three sub-lemmas above + verified `stalkLEquivOfIso`):
* `e : kU ≃+* k` from `stalk_restrictRing_ringEquiv`.
* `stalkLEquivOfIso ((SheafOfModules.forget _).mapIso t.iso) ⟨x,hU⟩` gives the middle
  `kU`-linear equiv `(restrictMod)-stalk ≃ₗ[kU] (free t.ι)-stalk` (NB: `t.iso` is a
  `SheafOfModules` iso; push it to the underlying `PresheafOfModules` iso via the forgetful
  functor, then apply the verified `stalkLEquivOfIso`).
* sub-lemma (a) `ea : (restrictMod)-stalk ≃ₗ[kU] F_x` (with `F_x` a `kU`-module via `e`).
* sub-lemma (b) `eb : (free t.ι)-stalk ≃ₗ[kU] (t.ι →₀ kU)`.
* Compose `ea.symm ≪ mid ≪ eb : F_x ≃ₗ[kU] (t.ι →₀ kU)`, then transport scalars along
  `e : kU ≃+* k` (with `Finsupp.mapRange.linearEquiv`/`LinearEquiv` semilinear-cast) to get
  the `k`-linear equiv `F_x ≃ₗ[k] (t.ι →₀ k)`. -/
theorem Trivialization.stalk_linearEquiv_finsupp
    (X : TopCat.{u})
    (O : Sheaf (Opens.grothendieckTopology X) CommRingCat.{u})
    (F : SheafOfModules.{u} (toRingSheaf X O))
    (x : X) {U : Opens X} (hU : x ∈ U)
    (t : Trivialization X (toRingSheaf X O) F U) :
    Nonempty (ToType (TopCat.Presheaf.stalk F.val.presheaf x)
      ≃ₗ[ToType (TopCat.Presheaf.stalk O.obj x)]
      (t.ι →₀ ToType (TopCat.Presheaf.stalk O.obj x))) := by
  obtain ⟨g⟩ := Trivialization.stalk_restricted_finsupp X O F x hU t
  exact ⟨transportFinsuppLinearEquiv (restrictStalkRingEquiv X O x hU) g⟩
#cloudR2Vendor Trivialization.rank_eq_of_mem in

/-- **Well-definedness of the rank (crux).**  Any two trivialisations of `F` whose open
domains both contain the point `x` have the same rank.  This is the invariant-basis-number
argument carried out on the stalk `F_x`, which is a free `O_{X,x}`-module on each
trivialisation's index set; over the nonzero commutative ring `O_{X,x}` the cardinality of a
free basis is an invariant. -/

theorem Trivialization.rank_eq_of_mem
    (X : TopCat.{u})
    (O : Sheaf (Opens.grothendieckTopology X) CommRingCat.{u})
    (hO : StalksNontrivial X O)
    (F : SheafOfModules.{u} (toRingSheaf X O))
    (x : X) {U V : Opens X} (hU : x ∈ U) (hV : x ∈ V)
    (t : Trivialization X (toRingSheaf X O) F U)
    (s : Trivialization X (toRingSheaf X O) F V) :
    t.rank = s.rank := by
  -- Let `k := O_{X,x}`, a nonzero commutative ring (`hO x` + the `CommRingCat` stalk).
  -- `et : Fx ≃ₗ[k] (t.ι →₀ k)` and `es : Fx ≃ₗ[k] (s.ι →₀ k)` from the crux helper_01c9.
  -- Then `es.symm.trans et : (s.ι →₀ k) ≃ₗ[k] (t.ι →₀ k)`; over the nonzero comm ring `k`
  -- (`StrongRankCondition` via `commRing_strongRankCondition`) `LinearEquiv.rank_eq` +
  -- `rank_finsupp_self` give `Cardinal.mk s.ι = Cardinal.mk t.ι`.
  -- The nonzero stalk-ring hypothesis ensures invariant basis number.
  classical
  obtain ⟨et⟩ := Trivialization.stalk_linearEquiv_finsupp X O F x hU t
  obtain ⟨es⟩ := Trivialization.stalk_linearEquiv_finsupp X O F x hV s
  -- `k = O_{X,x}` is a nonzero commutative ring, hence has the strong rank condition.
  have : Nontrivial (ToType (TopCat.Presheaf.stalk O.obj x)) := hO x
  have : StrongRankCondition (ToType (TopCat.Presheaf.stalk O.obj x)) :=
    commRing_strongRankCondition _
  -- The composite linear equivalence between the two finsupp free modules.
  have hrank : Module.rank (ToType (TopCat.Presheaf.stalk O.obj x))
      (s.ι →₀ ToType (TopCat.Presheaf.stalk O.obj x))
      = Module.rank (ToType (TopCat.Presheaf.stalk O.obj x))
        (t.ι →₀ ToType (TopCat.Presheaf.stalk O.obj x)) :=
    (es.symm.trans et).rank_eq
  -- `rank_finsupp_self` rewrites both ranks to the (lifted) cardinality of the index set.
  rw [rank_finsupp_self, rank_finsupp_self] at hrank
  -- In universe `u` the `Cardinal.lift` is the identity, so we recover `mk s.ι = mk t.ι`.
  simp only [Cardinal.lift_id] at hrank
  change Cardinal.mk t.ι = Cardinal.mk s.ι
  exact hrank.symm
#cloudR2Vendor exists_locallyConstant_rank in

/-- **Stacks Tag 01C9.**  Let `X` be a ringed space whose structure sheaf `O_X` is a sheaf
of commutative rings all of whose stalks `O_{X,x}` are nonzero, and let `F` be a locally
free sheaf of `O_X`-modules.  Then there is a locally constant function
`rank_F : X → Cardinal` such that for every point `x` and every trivialisation `t` of `F` on
an open neighbourhood `U` of `x`, the cardinality of the index set of `t` equals `rank_F x`.

This single statement encodes both that the rank at a point is well defined (independent of
the trivialisation chosen) and that the resulting function is locally constant. -/

theorem exists_locallyConstant_rank
    (X : TopCat.{u})
    (O : Sheaf (Opens.grothendieckTopology X) CommRingCat.{u})
    (hO : StalksNontrivial X O)
    (F : SheafOfModules.{u} (toRingSheaf X O))
    (hF : IsLocallyFree X (toRingSheaf X O) F) :
    ∃ rankF : X → Cardinal.{u},
      IsLocallyConstant rankF ∧
      ∀ (x : X) (U : Opens X), x ∈ U →
        ∀ t : Trivialization X (toRingSheaf X O) F U, t.rank = rankF x := by
  classical
  -- For each `x`, `hF x` provides an open neighbourhood and a trivialisation there.  Choose
  -- them: `Ux x` an open with `x ∈ Ux x`, and `tx x : Trivialization … (Ux x)`.
  set Ux : X → Opens X := fun x => (hF x).choose with hUx
  have hxUx : ∀ x, x ∈ Ux x := fun x => (hF x).choose_spec.1
  have hne : ∀ x, Nonempty (Trivialization X (toRingSheaf X O) F (Ux x)) :=
    fun x => (hF x).choose_spec.2
  set tx : ∀ x, Trivialization X (toRingSheaf X O) F (Ux x) := fun x => (hne x).some with htx
  -- Define the rank function as the rank of the chosen trivialisation at each point.
  refine ⟨fun x => (tx x).rank, ?_, ?_⟩
  · -- LOCAL CONSTANCY.  We show `rankF` is constant on each chosen neighbourhood `Ux x`.
    -- Via `IsLocallyConstant.iff_exists_open`: for each `x` exhibit the open `(Ux x : Set X)`
    -- containing `x` on which `rankF` is constant.  For `y ∈ Ux x`, both `tx x` (a
    -- trivialisation on `Ux x`, and `y ∈ Ux x`) and `tx y` (on `Ux y`, with `y ∈ Ux y`) are
    -- trivialisations whose domains contain `y`, so `Trivialization.rank_eq_of_mem` at `y`
    -- gives `(tx y).rank = (tx x).rank`, i.e. `rankF y = rankF x`.  This branch is fully
    -- discharged below using only `rank_eq_of_mem` (the single crux open goal).
    -- SANITY CHECK PASSED
    rw [IsLocallyConstant.iff_exists_open]
    intro x
    refine ⟨(Ux x : Set X), (Ux x).isOpen, hxUx x, ?_⟩
    intro y hy
    -- `tx y` on `Ux y ∋ y` and `tx x` on `Ux x ∋ y` (since `y ∈ Ux x`):
    exact Trivialization.rank_eq_of_mem X O hO F y (hxUx y) hy (tx y) (tx x)
  · -- MATCHING PROPERTY / WELL-DEFINEDNESS.  For any `x`, open `U ∋ x` and trivialisation
    -- `t` on `U`: apply `Trivialization.rank_eq_of_mem` at `x` to the pair `t` (on `U ∋ x`)
    -- and the chosen `tx x` (on `Ux x ∋ x`).  This gives `t.rank = (tx x).rank = rankF x`.
    -- SANITY CHECK PASSED
    intro x U hxU t
    exact Trivialization.rank_eq_of_mem X O hO F x hxU (hxUx x) t (tx x)

end LocallyFreeRank

end ZInQ.Contrib.CloudR2Poincare.L3.StacksPort
