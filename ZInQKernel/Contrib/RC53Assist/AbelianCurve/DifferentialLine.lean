import ZInQKernel.Contrib.RC53Assist.AbelianCurve.SmoothCurve
import Mathlib.Algebra.Category.ModuleCat.Differentials.Presheaf
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.Topology.Sheaves.CommRingCat

/-!
# The differential-line reduction

The sheaf used here is the actual sheafification of relative Kähler differentials,
with the same definition as `Scheme.Hom.relativeDifferentials` in the vendored
Jacobian library. It is not a vector space chosen to have dimension one.

Two unproved mathematical propositions are explicitly named. The first is
triviality of the cotangent sheaf of a smooth group curve (Milne, cited 2008
notes, IV, Proposition 6.4(a)–(b), printed p. 152). The second is the general
comparison between regular sheaf differentials and regular Weil differentials.
Neither proposition mentions elliptic function fields or Weierstrass models.
They are hypotheses of the reduction, not axioms or proved declarations.

Constancy of global functions and the resulting dimension of the global
sections of a trivial line sheaf are proved here. This is the rank-one case
of Milne, IV, Proposition 6.6, printed p. 152.
-/

set_option maxHeartbeats 800000
set_option autoImplicit false
set_option linter.style.haveILetI false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace ZInQ.Contrib.RC53Assist.AbelianCurve

open AlgebraicGeometry CategoryTheory Limits Opposite TopologicalSpace
open PresheafOfModules PresheafOfModulesOfCommRing
open PresheafOfModulesOfCommRing.DifferentialsConstruction

/-- DEFINITION. The inverse-image structure presheaf associated to a scheme morphism.
Locator: the vendored Jacobian library, `AlgebraicGeometry/Differentials/Presheaf.lean`,
`Scheme.Hom.pullbackPresheaf`. -/
abbrev inverseImageStructure {X S : Scheme.{0}} (f : X ⟶ S) :
    TopCat.Presheaf CommRingCat.{0} X :=
  (TopCat.Presheaf.pullback CommRingCat f.base).obj S.presheaf

/-- DEFINITION. The adjoint of the structure-sheaf map, from the inverse image to the source
structure presheaf. Locator: the vendored Jacobian library,
`AlgebraicGeometry/Differentials/Presheaf.lean`, `Scheme.Hom.pullbackPresheafToPresheaf`. -/
def inverseImageStructureMap {X S : Scheme.{0}} (f : X ⟶ S) :
    inverseImageStructure f ⟶ X.presheaf :=
  ((TopCat.Presheaf.pullbackPushforwardAdjunction CommRingCat f.base).homEquiv _ _).symm f.c

/-- DEFINITION. The actual sheaf of relative Kähler differentials of a scheme morphism.
Locator: the vendored Jacobian library, `AlgebraicGeometry/Modules/Differentials.lean`,
`Scheme.Hom.relativeDifferentials`, lines 81–91; the sheafification in that definition. -/
def differentialSheaf {X S : Scheme.{0}} (f : X ⟶ S) : X.Modules :=
  (sheafification (𝟙 X.ringCatSheaf.obj)).obj
    (relativeDifferentials' (inverseImageStructureMap f))

/-- DEFINITION. The ground-field map to global regular functions.
Locator: `TauCeti/AlgebraicGeometry/Modules/GlobalSections.lean`,
`Scheme.Modules.baseRingToGlobalSections`. -/
def globalFunctionsMap {k : Type} [Field k] {X : Scheme.{0}} (f : X ⟶ Spec (.of k)) :
    k →+* Γ(X, ⊤) :=
  ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop).hom

/-- DEFINITION. The scalar action on the global sections of a sheaf over the specified base.
Locator: `TauCeti/AlgebraicGeometry/Modules/GlobalSections.lean`,
`Scheme.Modules.globalSectionsBaseModule`. -/
@[instance_reducible]
def globalSectionsModule {k : Type} [Field k] {X : Scheme.{0}}
    (f : X ⟶ Spec (.of k)) (M : X.Modules) : Module k Γ(M, ⊤) :=
  Module.compHom Γ(M, ⊤) (globalFunctionsMap f)

/-- THEOREM (proved). All global functions on a proper geometrically integral scheme are
constants. No rational point is assumed. Locator:
`TauCeti/AlgebraicGeometry/Geometrically/GlobalSections.lean`,
`Scheme.baseRingToGlobalSections_bijective_of_geometricallyIntegral`. -/
theorem globalFunctions_bijective {k : Type} [Field k] {X : Scheme.{0}} [IsIntegral X]
    (f : X ⟶ Spec (.of k)) [UniversallyClosed f] [GeometricallyIntegral f] :
    Function.Bijective (globalFunctionsMap f) := by
  letI := functionFieldAlgebra f
  letI : Nonempty (⊤ : X.Opens) := ⟨⟨genericPoint X, trivial⟩⟩
  letI : Algebra k Γ(X, ⊤) := (globalFunctionsMap f).toAlgebra
  haveI : IsIntegrallyClosedIn k X.functionField := functionField_exact_constants f
  have hint : (globalFunctionsMap f).IsIntegral := by
    apply RingHom.isIntegral_respectsIso.2
      (e := (Scheme.ΓSpecIso (.of k)).symm.commRingCatIsoToRingEquiv)
    exact isIntegral_appTop_of_universallyClosed f
  let φ : Γ(X, ⊤) →ₐ[k] X.functionField :=
    { (X.germToFunctionField ⊤).hom with commutes' := fun _ => rfl }
  refine ⟨(globalFunctionsMap f).injective, fun a => ?_⟩
  have ha : _root_.IsIntegral k a := hint a
  obtain ⟨c, hc⟩ := IsIntegrallyClosedIn.algebraMap_eq_of_integral (ha.map φ)
  exact ⟨c, (X.germToFunctionField_injective ⊤) ((φ.commutes c).trans hc)⟩

/-- DEFINITION. A sheaf isomorphism induces a ground-field-linear equivalence of global
sections. Locator: Mathlib's `Scheme.Modules.Hom.app_smul` and the two inverse identities
of a sheaf isomorphism. -/
def globalSectionsEquiv {k : Type} [Field k] {X : Scheme.{0}}
    (f : X ⟶ Spec (.of k)) {M N : X.Modules} (e : M ≅ N) :
    letI := globalSectionsModule f M
    letI := globalSectionsModule f N
    Γ(M, ⊤) ≃ₗ[k] Γ(N, ⊤) := by
  letI := globalSectionsModule f M
  letI := globalSectionsModule f N
  exact {
    toFun := e.hom.app ⊤
    invFun := e.inv.app ⊤
    map_add' := map_add _
    map_smul' := fun c x => e.hom.app_smul (globalFunctionsMap f c) x
    left_inv := fun x => congr($(e.hom_inv_id).val.app (op ⊤) x)
    right_inv := fun x => congr($(e.inv_hom_id).val.app (op ⊤) x) }

/-- THEOREM (proved, the free-line case of Milne IV.6.6). A trivial line sheaf on a proper
geometrically integral scheme has one-dimensional global sections over its base field.
Locator: Milne, cited 2008 notes, IV, Proposition 6.6, printed p. 152;
`globalFunctions_bijective` and `globalSectionsEquiv` above. -/
theorem finrank_globalSections_trivial_line {k : Type} [Field k] {X : Scheme.{0}} [IsIntegral X]
    (f : X ⟶ Spec (.of k)) [UniversallyClosed f] [GeometricallyIntegral f]
    (M : X.Modules) (e : M ≅ SheafOfModules.unit X.ringCatSheaf) :
    letI := globalSectionsModule f M
    Module.finrank k Γ(M, ⊤) = 1 := by
  letI := globalSectionsModule f M
  let N := SheafOfModules.unit X.ringCatSheaf
  letI := globalSectionsModule f N
  rw [(globalSectionsEquiv f e).finrank_eq]
  letI : Algebra k Γ(X, ⊤) := (globalFunctionsMap f).toAlgebra
  let e₀ : k ≃ₗ[k] Γ(X, ⊤) :=
    LinearEquiv.ofBijective (Algebra.linearMap k Γ(X, ⊤)) (globalFunctions_bijective f)
  have hn : Module.finrank k Γ(X, ⊤) = 1 := by
    rw [← e₀.finrank_eq, Module.finrank_self]
  exact hn

/-- DEFINITION OF AN UNPROVED PRINTED INPUT (consequence form). The relative differential
sheaf of every smooth integral group curve of finite type over the rationals is a trivial line
sheaf. Smoothness supplies local finite type and the explicit quasi-compactness supplies
finite type. Locator: Milne, *Abelian varieties*, version 2.00 (2008), IV,
Proposition 6.4(a)–(b), printed p. 152. This is the manuscript's bibitem `milne-av`,
not I.6.4 or I.6.6. No properness, genus, elliptic-function-field assertion,
or Weierstrass model occurs here. -/
def InvariantDifferentialTrivialization : Prop :=
  ∀ (G : Over (Spec (.of ℚ))) [CategoryTheory.GrpObj G] [IsIntegral G.left] [Smooth G.hom]
    [QuasiCompact G.hom], topologicalKrullDim G.left = 1 →
      Nonempty (differentialSheaf G.hom ≅ SheafOfModules.unit G.left.ringCatSheaf)

/-- DEFINITION OF AN UNPROVED COMPARISON INPUT (consequence form). For every smooth proper
geometrically integral rational curve, its global differential sheaf sections are the regular
Weil differentials of its actual function field. The mathematical map is the residue pairing
on repartitions; only existence of the induced linear equivalence is requested here.
Locators: Silverman, manuscript bibitem `silverman`, Chapter II, §§4–5, for the curve's rational
and regular differential forms. The specific Weil-repartition formulation is Stichtenoth,
*Algebraic Function Fields and Codes*, second edition, §I.5, especially Definition 1.5.1 and
Remark 1.5.12; that book is NOT CITED in the manuscript. The implementation target is
`TauCeti.weilDifferentialFiltration` at zero, not all Kähler differentials. -/
def RegularDifferentialComparison : Prop :=
  ∀ (X : Scheme.{0}) [IsIntegral X] (f : X ⟶ Spec (.of ℚ))
    [Smooth f] [IsProper f] [GeometricallyIntegral f], topologicalKrullDim X = 1 →
      letI := functionFieldAlgebra f
      letI := globalSectionsModule f (differentialSheaf f)
      Nonempty (Γ(differentialSheaf f, ⊤) ≃ₗ[ℚ]
        ↥(TauCeti.weilDifferentialFiltration (0 : TauCeti.Divisor ℚ X.functionField)))

/-- THEOREM (proved reduction, S2a part 2). Triviality of the actual differential sheaf and the
regular-differential comparison imply genus one. The function-field and exact-constants
hypotheses are proved, not supplied independently.
Locator: Milne IV.6.4 and the free-line case of IV.6.6;
`TauCeti.finrank_weilDifferentialFiltration_zero`. -/
theorem abelian_genus_one_of_differentials
    (hT : InvariantDifferentialTrivialization) (hC : RegularDifferentialComparison)
    (G : Over (Spec (.of ℚ))) [CategoryTheory.GrpObj G] [IsIntegral G.left]
    [Smooth G.hom] [IsProper G.hom] [GeometricallyIntegral G.hom]
    (hdim : topologicalKrullDim G.left = 1) :
    letI := functionFieldAlgebra G.hom
    TauCeti.genus ℚ G.left.functionField = 1 := by
  letI := functionFieldAlgebra G.hom
  letI := globalSectionsModule G.hom (differentialSheaf G.hom)
  obtain ⟨e⟩ := hT G hdim
  obtain ⟨c⟩ := hC G.left G.hom hdim
  rw [← TauCeti.finrank_weilDifferentialFiltration_zero
    (isFunctionField_of_dimension_one G.hom hdim) (functionField_exact_constants G.hom),
    ← c.finrank_eq]
  exact finrank_globalSections_trivial_line G.hom (differentialSheaf G.hom) e

/-- THEOREM (proved reduction, S2a function-field conclusion). The two genuinely geometric
inputs, together with the actual abelian-variety hypotheses, yield an elliptic function field.
The rational place is constructed from the identity's local ring, not assumed.
Locator: `abelian_genus_one_of_differentials` and `ellipticFunctionField_of_genus_one`. -/
theorem abelian_isEllipticFunctionField
    (hT : InvariantDifferentialTrivialization) (hC : RegularDifferentialComparison)
    (G : Over (Spec (.of ℚ))) [CategoryTheory.GrpObj G] [IsIntegral G.left]
    [Smooth G.hom] [IsProper G.hom] [GeometricallyIntegral G.hom]
    (hdim : topologicalKrullDim G.left = 1) :
    letI := functionFieldAlgebra G.hom
    TauCeti.IsEllipticFunctionField ℚ G.left.functionField :=
  ellipticFunctionField_of_genus_one G hdim
    (abelian_genus_one_of_differentials hT hC G hdim)

end ZInQ.Contrib.RC53Assist.AbelianCurve
