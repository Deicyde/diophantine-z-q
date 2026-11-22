import ZInQKernel.Contrib.RC53Assist.AbelianCurveInputs.LocalFacts
import ZInQKernel.Contrib.RC53Assist.S2aNumberField.SmoothCurve
import ZInQKernel.Contrib.RC53Assist.S2aNumberField.BirationalComparison

/-!
# Regular sheaf differentials and regular Weil differentials in characteristic zero

For a smooth proper geometrically integral curve `X` over a field `K` of characteristic zero,
the global sections of the sheafified relative Kähler differentials are `K`-linearly
equivalent to the holomorphic Weil differentials `Ω(0)` of the function field
(`regularDifferentialComparison`). The map is the restriction of a global section to the
generic stalk followed by the normalized cotrace comparison of a separating element.

The statements and proofs are those of the rational version, module
`ZInQKernel.Contrib.RC53Assist.AbelianCurveInputs.RegularComparison` (same declaration names,
namespace `ZInQ.Contrib.RC53Assist.AbelianCurveInputs`), with `ℚ` replaced by `K`: the stalk
calculation of the differential sheaf, its specialization to the generic point, the
place-to-point and point-to-place steps, and unique gluing of global sections. The two local
field facts used there (`LocalUniformizerBasis`, `UniformizerResidueOrder`) are already stated
and proved for every field of characteristic zero (module
`ZInQKernel.Contrib.RC53Assist.AbelianCurveInputs.LocalFacts`). The proof changes are one
explicit scalar-tower instance on stalks (found automatically for `ℚ`-modules), explicit
characteristic-zero hypotheses, and the final comparison stated for a given curve rather than
as a proposition quantified over all rational curves.

Mathematical locator: Silverman, *The Arithmetic of Elliptic Curves*, second edition,
Chapter II, §§4–5; Stichtenoth, *Algebraic Function Fields and Codes*, second edition, §§I.5
and I.7; Stacks Project, Tag 01UM.
-/

set_option maxHeartbeats 800000
set_option autoImplicit false
set_option linter.style.haveILetI false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace ZInQ.Contrib.RC53Assist.S2aNumberField

open AlgebraicGeometry CategoryTheory Limits Opposite TopologicalSpace
open TauCeti TauCeti.AlgebraicGeometry Polynomial Module KaehlerDifferential
open scoped IntermediateField
open ZInQ.Contrib.RC53Assist.AbelianCurve (functionFieldAlgebra stalkAlgebra
  stalk_functionField_tower differentialSheaf inverseImageStructure inverseImageStructureMap
  globalFunctionsMap globalSectionsModule fromFunctionField isFunctionField_of_dimension_one
  functionField_exact_constants)
open ZInQ.Contrib.RC53Assist.AbelianCurveInputs (genericGerm_injective
  existsUnique_section_of_mem_local_stalks stalkSpecializationLinear stalkPlace
  stalkPlace_integers kaehler_local_image_transport localComparison_of_uniformizer_facts
  LocalUniformizerBasis UniformizerResidueOrder comparison RegularAt
  mem_zeroFiltration_iff_regularAt localKaehlerMap localKaehlerMap_injective_of_uniformizerBasis)

variable {K : Type} [Field K]

section SheafGluing

variable {X : Scheme.{0}} [IsIntegral X] (M : X.Modules)

omit [IsIntegral X] in
/-- THEOREM. A germ of a scalar multiple is the scalar germ times the section germ.
Locator: Mathlib `PresheafOfModules.germ_smul`. -/
private theorem moduleGerm_smul (p : X) (U : X.Opens) (hp : p ∈ U)
    (a : Γ(X, U)) (s : Γ(M, U)) :
    M.presheaf.germ U p hp (a • s) =
      X.presheaf.germ U p hp a • M.presheaf.germ U p hp s :=
  PresheafOfModules.germ_smul (R := X.presheaf) M.val p U hp a s

/-- THEOREM. The linear specialization has the usual germ computation.
Locator: Mathlib `TopCat.Presheaf.germ_stalkSpecializes_apply`. -/
private theorem stalkSpecializationLinear_germ (p : X) (U : X.Opens) (hp : p ∈ U)
    (s : Γ(M, U)) :
    letI : Module (X.presheaf.stalk p) (M.presheaf.stalk (genericPoint X)) :=
      Module.compHom _ (algebraMap (X.presheaf.stalk p) X.functionField)
    stalkSpecializationLinear M p (M.presheaf.germ U p hp s) =
      M.presheaf.germ U (genericPoint X) ((genericPoint_specializes p).mem_open U.isOpen hp) s :=
  M.presheaf.germ_stalkSpecializes_apply hp (genericPoint_specializes p) s

end SheafGluing


section DifferentialStalks

open PresheafOfModules PresheafOfModulesOfCommRing
open PresheafOfModulesOfCommRing.DifferentialsConstruction

/-- DEFINITION. The actual sheafified universal relative derivation.
Locator: `DifferentialLine.lean`, `differentialSheaf`, and Mathlib's
`DifferentialsConstruction.derivation'` followed by the sheafification unit. -/
def differentialDerivation {X : Scheme.{0}} (f : X ⟶ Spec (.of K)) :
    PresheafOfModulesOfCommRing.Derivation' (differentialSheaf f).val
      (inverseImageStructureMap f) :=
  (derivation' (inverseImageStructureMap f)).postcomp
    ((sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).unit.app _)

/-- DEFINITION OF LOCAL COMPARISON DATA. At each point, the actual differential
sheaf stalk is the Kähler module of the actual local ring, identifying the
universal derivations on germs. No global sections, properness, dimension,
Weil filtration, or genus occur in this data.
Locator: the standard stalk calculation for relative Kähler differentials,
Silverman Chapter II, §§4–5; the affine calculation in the vendored Jacobian
library, `AlgebraicGeometry/Modules/DifferentialsSections.lean`. -/
structure DifferentialStalkData {X : Scheme.{0}} [IsIntegral X]
    (f : X ⟶ Spec (.of K)) where
  /-- FIELD. The local linear identification. Locator: the stalk calculation of `Ω¹`. -/
  equiv : ∀ p : X,
    letI := stalkAlgebra f p
    KaehlerDifferential K (X.presheaf.stalk p) ≃ₗ[X.presheaf.stalk p]
      (differentialSheaf f).presheaf.stalk p
  /-- FIELD. Compatibility with the universal derivation. Locator: `d a ↦ d a` on germs. -/
  equiv_D_germ : ∀ (p : X) (U : X.Opens) (hp : p ∈ U) (a : Γ(X, U)),
    letI := stalkAlgebra f p
    equiv p (D K (X.presheaf.stalk p) (X.presheaf.germ U p hp a)) =
      (differentialSheaf f).presheaf.germ U p hp
        ((differentialDerivation f).d (X := op U) a)

/-- DEFINITION OF A LOCAL STANDARD FACT. Sheafification and taking stalks give
the canonical local Kähler identifications, compatibly with the universal
derivations. It applies without a properness or curve hypothesis.
Locator: the stalk formula for relative differentials; Silverman Chapter II, §§4–5. -/
def StalkDifferentials : Prop :=
  ∀ (X : Scheme.{0}) [IsIntegral X] (f : X ⟶ Spec (.of K)),
    Nonempty (DifferentialStalkData f)

/-- THEOREM. Canonical local Kähler identifications commute with specialization
to the generic point. Naturality is proved from the universal derivations rather
than included as a new input. Locator: Mathlib
`Derivation.liftKaehlerDifferential_unique` and the germ specialization identity. -/
theorem DifferentialStalkData.specializes_equiv {X : Scheme.{0}} [IsIntegral X]
    {f : X ⟶ Spec (.of K)} (d : DifferentialStalkData f) (p : X) :
    letI := functionFieldAlgebra f
    letI := stalkAlgebra f p
    letI := stalk_functionField_tower f p
    ∀ ξ : KaehlerDifferential K (X.presheaf.stalk p),
      (differentialSheaf f).presheaf.stalkSpecializes (genericPoint_specializes p)
        (d.equiv p ξ) =
      d.equiv (genericPoint X) (KaehlerDifferential.map K K (X.presheaf.stalk p)
        X.functionField ξ) := by
  letI := functionFieldAlgebra f
  letI := stalkAlgebra f p
  haveI := stalk_functionField_tower f p
  let M := differentialSheaf f
  letI : Module K (M.presheaf.stalk (genericPoint X)) :=
    Module.compHom _ (algebraMap K X.functionField)
  letI : Module (X.presheaf.stalk p) (M.presheaf.stalk (genericPoint X)) :=
    Module.compHom _ (algebraMap (X.presheaf.stalk p) X.functionField)
  haveI : IsScalarTower K (X.presheaf.stalk p) (M.presheaf.stalk (genericPoint X)) :=
    IsScalarTower.of_algebraMap_smul fun c ξ => by
      change algebraMap (X.presheaf.stalk p) X.functionField
        (algebraMap K (X.presheaf.stalk p) c) • ξ = algebraMap K X.functionField c • ξ
      rw [← IsScalarTower.algebraMap_apply K (X.presheaf.stalk p) X.functionField]
  haveI : IsScalarTower (X.presheaf.stalk p) X.functionField
      (M.presheaf.stalk (genericPoint X)) :=
    IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  let e : KaehlerDifferential K X.functionField ≃ₗ[X.functionField]
      M.presheaf.stalk (genericPoint X) := d.equiv (genericPoint X)
  let L := (stalkSpecializationLinear M p) ∘ₗ (d.equiv p).toLinearMap
  let R := (e.restrictScalars (X.presheaf.stalk p)).toLinearMap ∘ₗ
    KaehlerDifferential.map K K (X.presheaf.stalk p) X.functionField
  have heq : L = R := by
    apply Derivation.liftKaehlerDifferential_unique
    ext z
    obtain ⟨U, hpU, a, rfl⟩ := X.presheaf.exists_germ_eq z
    haveI : Nonempty U := ⟨⟨p, hpU⟩⟩
    change stalkSpecializationLinear M p
      (d.equiv p (D K (X.presheaf.stalk p) (X.presheaf.germ U p hpU a))) =
      e (KaehlerDifferential.map K K (X.presheaf.stalk p) X.functionField
        (D K (X.presheaf.stalk p) (X.presheaf.germ U p hpU a)))
    rw [d.equiv_D_germ, stalkSpecializationLinear_germ,
      KaehlerDifferential.map_D, X.algebraMap_germ_eq_germToFunctionField]
    exact (d.equiv_D_germ (genericPoint X) U
      ((genericPoint_specializes p).mem_open U.isOpen hpU) a).symm
  intro ξ
  change L ξ = R ξ
  exact LinearMap.congr_fun heq ξ

end DifferentialStalks

section StalkCalculation

open PresheafOfModules PresheafOfModulesOfCommRing
open PresheafOfModulesOfCommRing.DifferentialsConstruction

variable {X : Scheme.{0}} [IsIntegral X] (f : X ⟶ Spec (.of K))

/-- DEFINITION. The universal property of the actual sheafified relative
differentials. Locator: Mathlib's presheaf universal derivation and the
sheafification adjunction; Stacks Project, Tag 01UM. -/
private def differentialHomEquiv (N : X.Modules) :
    (differentialSheaf f ⟶ N) ≃
      PresheafOfModulesOfCommRing.Derivation' N.val (inverseImageStructureMap f) where
  toFun g := (differentialDerivation f).postcomp g.val
  invFun D := ((sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).homEquiv _ _).symm
    ((isUniversal' (inverseImageStructureMap f)).desc D)
  left_inv g := by
    apply ((sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).homEquiv _ _).injective
    rw [Equiv.apply_symm_apply]
    apply (isUniversal' (inverseImageStructureMap f)).postcomp_injective
    rw [Derivation.Universal.fac]
    rfl
  right_inv D := by
    change (derivation' (inverseImageStructureMap f)).postcomp
      (((sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).homEquiv _ _)
        (((sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).homEquiv _ _).symm _)) = D
    rw [Equiv.apply_symm_apply, Derivation.Universal.fac]

omit [IsIntegral X] in
/-- THEOREM. The sheaf universal property sends the universal derivative to the
specified derivative. Locator: `differentialHomEquiv` and the universal derivation. -/
private theorem differentialHomEquiv_symm_app_d (N : X.Modules)
    (D : PresheafOfModulesOfCommRing.Derivation' N.val (inverseImageStructureMap f))
    (U : X.Opensᵒᵖ) (a : X.presheaf.obj U) :
    ((differentialHomEquiv f N).symm D).val.app U
      ((differentialDerivation f).d a) = D.d a :=
  congr($((differentialHomEquiv f N).apply_symm_apply D).d a)

/-- THEOREM. The inverse-image structure map has its defining adjunction identity.
Locator: the presheaf inverse-image adjunction, as in the vendored Jacobian
library, `AlgebraicGeometry/Differentials/Presheaf.lean`. -/
private theorem inverseImageMap_unit {Y S : Scheme.{0}} (g : Y ⟶ S) :
    (TopCat.Presheaf.pullbackPushforwardAdjunction CommRingCat g.base).unit.app S.presheaf ≫
      (TopCat.Presheaf.pushforward CommRingCat g.base).map (inverseImageStructureMap g) = g.c :=
  (Adjunction.homEquiv_unit _ _ _ _).symm.trans (Equiv.apply_symm_apply _ _)

/-- THEOREM. Every structure-sheaf pullback on an open factors through the
inverse-image structure presheaf. Locator: the inverse-image adjunction;
`AlgebraicGeometry/Differentials/Presheaf.lean`, the affine restriction factorization. -/
private theorem inverseImageMap_appLE_factor {Y S : Scheme.{0}} (g : Y ⟶ S)
    (U : S.Opens) (V : Y.Opens) (h : V ≤ g ⁻¹ᵁ U) :
    g.appLE U V h =
      ((TopCat.Presheaf.pullbackPushforwardAdjunction CommRingCat g.base).unit.app
        S.presheaf).app (op U) ≫ (inverseImageStructure g).map (homOfLE h).op ≫
          (inverseImageStructureMap g).app (op V) := by
  rw [(inverseImageStructureMap g).naturality, ← Category.assoc]
  have heq := NatTrans.congr_app (inverseImageMap_unit g) (op U)
  rw [NatTrans.comp_app] at heq
  erw [heq]
  rfl

omit [IsIntegral X] in
/-- THEOREM. The universal sheaf derivative vanishes on base constants on each
open. Locator: the defining relative-derivation condition and
`inverseImageMap_appLE_factor`. -/
private theorem differentialDerivation_base_constant (U : X.Opens) (c : K) :
    (differentialDerivation f).d (X := op U)
      (f.appLE ⊤ U le_top ((Scheme.ΓSpecIso (.of K)).inv c)) = 0 := by
  rw [inverseImageMap_appLE_factor]
  exact PresheafOfModulesOfCommRing.Derivation'.d_app (differentialDerivation f) _

omit [IsIntegral X] in
/-- THEOREM. Pulling a base constant to an open and taking its germ is the
specified base algebra map to the local ring. Locator: `IdentityPlace.lean`,
`stalkAlgebra`, and naturality of restriction. -/
private theorem germ_base_constant (p : X) (U : X.Opens) (hp : p ∈ U) (c : K) :
    letI := stalkAlgebra f p
    X.presheaf.germ U p hp (f.appLE ⊤ U le_top ((Scheme.ΓSpecIso (.of K)).inv c)) =
      algebraMap K (X.presheaf.stalk p) c := by
  letI := stalkAlgebra f p
  change X.presheaf.germ U p hp (f.appLE ⊤ U le_top ((Scheme.ΓSpecIso (.of K)).inv c)) =
    X.presheaf.germ ⊤ p trivial (f.appTop ((Scheme.ΓSpecIso (.of K)).inv c))
  simp only [Scheme.Hom.appLE, Scheme.Hom.appTop, ConcreteCategory.comp_apply]
  rw [X.presheaf.germ_res_apply]
  simp only [Opens.map_top]

omit [IsIntegral X] in
/-- THEOREM. The sheaf derivative commutes with restriction of sections.
Locator: the defining presheaf derivation naturality. -/
private theorem differentialDerivation_map {U V : X.Opensᵒᵖ} (i : U ⟶ V)
    (a : X.presheaf.obj U) :
    (differentialDerivation f).d (X.presheaf.map i a) =
      (differentialSheaf f).presheaf.map i ((differentialDerivation f).d a) :=
  (differentialDerivation f).d_map i a

/-- DEFINITION. The compatible additive maps on neighborhoods defining the
universal derivative on the local ring. Locator: the filtered-colimit definition
of a stalk and compatibility of the sheaf universal derivative with restriction. -/
private def stalkDerivativeCocone (p : X) :
    Cocone ((OpenNhds.inclusion p).op ⋙ X.presheaf ⋙
      (forget₂ CommRingCat RingCat ⋙ forget₂ RingCat AddCommGrpCat)) where
  pt := (differentialSheaf f).presheaf.stalk p
  ι :=
    { app := fun U => AddCommGrpCat.ofHom
        ((differentialDerivation f).d (X := op U.unop.1)) ≫
          (differentialSheaf f).presheaf.germ U.unop.1 p U.unop.2
      naturality := by
        intro U V i
        ext a
        change (differentialSheaf f).presheaf.germ V.unop.1 p V.unop.2
          ((differentialDerivation f).d
            (X.presheaf.map ((OpenNhds.inclusion p).op.map i) a)) =
          (differentialSheaf f).presheaf.germ U.unop.1 p U.unop.2
            ((differentialDerivation f).d a)
        have hD := differentialDerivation_map f ((OpenNhds.inclusion p).op.map i) a
        have hres := (differentialSheaf f).presheaf.germ_res_apply'
          ((OpenNhds.inclusion p).op.map i) p V.unop.2 ((differentialDerivation f).d a)
        exact (congrArg ((differentialSheaf f).presheaf.germ V.unop.1 p V.unop.2) hD).trans
          hres }

/-- DEFINITION. The additive universal derivative on the actual local ring,
obtained by the stalk colimit. Locator: Mathlib's preservation of filtered
colimits by `(forget₂ CommRingCat RingCat ⋙ forget₂ RingCat AddCommGrpCat)`. -/
private def stalkDerivativeAdd (p : X) :
    X.presheaf.stalk p →+ (differentialSheaf f).presheaf.stalk p :=
  ConcreteCategory.hom ((isColimitOfPreserves
    ((forget₂ CommRingCat RingCat ⋙ forget₂ RingCat AddCommGrpCat))
    (colimit.isColimit ((OpenNhds.inclusion p).op ⋙ X.presheaf))).desc
      (stalkDerivativeCocone f p))

omit [IsIntegral X] in
/-- THEOREM. The local additive derivative is the germ of the sheaf derivative.
Locator: the stalk colimit computation `IsColimit.fac`. -/
private theorem stalkDerivativeAdd_germ (p : X) (U : X.Opens) (hp : p ∈ U)
    (a : Γ(X, U)) :
    stalkDerivativeAdd f p (X.presheaf.germ U p hp a) =
      (differentialSheaf f).presheaf.germ U p hp
        ((differentialDerivation f).d (X := op U) a) := by
  have h := (isColimitOfPreserves ((forget₂ CommRingCat RingCat ⋙ forget₂ RingCat AddCommGrpCat))
    (colimit.isColimit ((OpenNhds.inclusion p).op ⋙ X.presheaf))).fac
      (stalkDerivativeCocone f p) (op ⟨U, hp⟩)
  exact ConcreteCategory.congr_hom h a

/-- THEOREM. The local additive derivative kills the constants.
Locator: `germ_base_constant`, `stalkDerivativeAdd_germ`, and the relative
universal derivation. -/
private theorem stalkDerivativeAdd_algebraMap (p : X) (c : K) :
    letI := stalkAlgebra f p
    stalkDerivativeAdd f p (algebraMap K (X.presheaf.stalk p) c) = 0 := by
  letI := stalkAlgebra f p
  rw [← germ_base_constant f p ⊤ trivial c, stalkDerivativeAdd_germ,
    differentialDerivation_base_constant, map_zero]

/-- THEOREM. The local additive derivative satisfies the product rule.
Locator: the product rule for the sheaf derivative, represented on a common
neighborhood; Mathlib `PresheafOfModules.germ_smul`. -/
private theorem stalkDerivativeAdd_mul (p : X) (r s : X.presheaf.stalk p) :
    stalkDerivativeAdd f p (r * s) =
      r • stalkDerivativeAdd f p s + s • stalkDerivativeAdd f p r := by
  obtain ⟨U, hpU, a, rfl⟩ := X.presheaf.exists_germ_eq r
  obtain ⟨V, hpV, b, rfl⟩ := X.presheaf.exists_germ_eq s
  have hpUV : p ∈ U ⊓ V := ⟨hpU, hpV⟩
  rw [← X.presheaf.germ_res_apply (homOfLE (inf_le_left : U ⊓ V ≤ U)) p hpUV a,
    ← X.presheaf.germ_res_apply (homOfLE (inf_le_right : U ⊓ V ≤ V)) p hpUV b,
    ← map_mul (X.presheaf.germ (U ⊓ V) p hpUV).hom,
    stalkDerivativeAdd_germ, stalkDerivativeAdd_germ, stalkDerivativeAdd_germ,
    (differentialDerivation f).d_mul, map_add,
    moduleGerm_smul (differentialSheaf f), moduleGerm_smul (differentialSheaf f)]

/-- DEFINITION. The universal sheaf derivative induces an actual `K`-linear
local-ring derivation. Locator: the preceding additive, constant, and product
identities; the standard construction of differentials on a stalk. -/
private def stalkDerivative (p : X) :
    letI := stalkAlgebra f p
    letI : Module K ((differentialSheaf f).presheaf.stalk p) :=
      Module.compHom _ (algebraMap K (X.presheaf.stalk p))
    Derivation K (X.presheaf.stalk p) ((differentialSheaf f).presheaf.stalk p) := by
  letI := stalkAlgebra f p
  letI : Module K ((differentialSheaf f).presheaf.stalk p) :=
    Module.compHom _ (algebraMap K (X.presheaf.stalk p))
  refine
    { toFun := stalkDerivativeAdd f p
      map_add' := map_add _
      map_smul' := ?_
      map_one_eq_zero' := ?_
      leibniz' := stalkDerivativeAdd_mul f p }
  · intro c r
    rw [RingHom.id_apply, Algebra.smul_def, stalkDerivativeAdd_mul,
      stalkDerivativeAdd_algebraMap, smul_zero, add_zero]
    rfl
  · rw [← map_one (algebraMap K (X.presheaf.stalk p))]
    exact stalkDerivativeAdd_algebraMap f p 1

/-- THEOREM. The local derivation identifies the derivative of a germ with the
germ of its derivative. Locator: `stalkDerivativeAdd_germ`. -/
private theorem stalkDerivative_germ (p : X) (U : X.Opens) (hp : p ∈ U)
    (a : Γ(X, U)) :
    letI := stalkAlgebra f p
    letI : Module K ((differentialSheaf f).presheaf.stalk p) :=
      Module.compHom _ (algebraMap K (X.presheaf.stalk p))
    stalkDerivative f p (X.presheaf.germ U p hp a) =
      (differentialSheaf f).presheaf.germ U p hp
        ((differentialDerivation f).d (X := op U) a) :=
  stalkDerivativeAdd_germ f p U hp a

end StalkCalculation

section SkyscraperCalculation

variable {X : Scheme.{0}} [IsIntegral X] (p : X) (N : Type) [AddCommGroup N]
  [Module (X.presheaf.stalk p) N]

/-- DEFINITION. Sections of the local-ring skyscraper module.
Locator: the stalk-to-skyscraper adjunction; the vendored Jacobian library,
`AlgebraicGeometry/Modules/Stalk.lean`, `SkyscraperSections`. -/
private def LocalSkySections (U : X.Opens) : Type := PLift (p ∈ U) → N

/-- INSTANCE. Pointwise addition on skyscraper sections.
Locator: the additive group of functions into an additive group. -/
private instance localSkyAddGroup (U : X.Opens) : AddCommGroup (LocalSkySections p N U) :=
  inferInstanceAs (AddCommGroup (PLift (p ∈ U) → N))

/-- INSTANCE. Functions act on skyscraper sections through their germs.
Locator: the local-ring module structure of a skyscraper sheaf. -/
private instance localSkySMul (U : X.Opens) : SMul Γ(X, U) (LocalSkySections p N U) :=
  ⟨fun a s hp => X.presheaf.germ U p hp.down a • s hp⟩

/-- INSTANCE. The germ action is a module action on skyscraper sections.
Locator: multiplicativity and additivity of the structure-sheaf germ map. -/
private instance localSkyModule (U : X.Opens) : Module Γ(X, U) (LocalSkySections p N U) where
  one_smul s := by
    funext hp
    change X.presheaf.germ U p hp.down 1 • s hp = s hp
    simp
  mul_smul a b s := by
    funext hp
    change X.presheaf.germ U p hp.down (a * b) • s hp =
      X.presheaf.germ U p hp.down a • (X.presheaf.germ U p hp.down b • s hp)
    simp [mul_smul]
  smul_zero a := by
    funext hp
    change X.presheaf.germ U p hp.down a • (0 : N) = 0
    exact smul_zero _
  smul_add a s t := by
    funext hp
    change X.presheaf.germ U p hp.down a • (s hp + t hp) =
      X.presheaf.germ U p hp.down a • s hp + X.presheaf.germ U p hp.down a • t hp
    exact smul_add _ _ _
  add_smul a b s := by
    funext hp
    change X.presheaf.germ U p hp.down (a + b) • s hp =
      X.presheaf.germ U p hp.down a • s hp + X.presheaf.germ U p hp.down b • s hp
    simp [add_smul]
  zero_smul s := by
    funext hp
    change X.presheaf.germ U p hp.down 0 • s hp = 0
    simp

/-- DEFINITION. The abelian presheaf of a local-ring skyscraper.
Locator: restriction of a function on memberships of the support point. -/
private def localSkyPresheaf : X.Opensᵒᵖ ⥤ AddCommGrpCat where
  obj U := AddCommGrpCat.of (LocalSkySections p N U.unop)
  map i := AddCommGrpCat.ofHom
    { toFun := fun s hp => s ⟨i.unop.le hp.down⟩
      map_zero' := rfl
      map_add' := fun _ _ => rfl }
  map_id _ := rfl
  map_comp _ _ := rfl

/-- INSTANCE. The skyscraper presheaf fibers carry the structure-ring action.
Locator: `localSkyModule`. -/
private instance localSkyPresheafModule (U : X.Opensᵒᵖ) :
    Module (X.ringCatSheaf.obj.obj U) ((localSkyPresheaf p N).obj U) :=
  inferInstanceAs (Module Γ(X, U.unop) (LocalSkySections p N U.unop))

omit [IsIntegral X] in
/-- THEOREM. Skyscraper restrictions respect the germ scalar action.
Locator: Mathlib `TopCat.Presheaf.germ_res_apply`. -/
private theorem localSkyPresheaf_map_smul {U V : X.Opensᵒᵖ} (i : U ⟶ V)
    (a : X.ringCatSheaf.obj.obj U) (s : (localSkyPresheaf p N).obj U) :
    (localSkyPresheaf p N).map i (a • s) =
      X.ringCatSheaf.obj.map i a • (localSkyPresheaf p N).map i s := by
  funext hp
  exact congrArg (fun r => r • s ⟨i.unop.le hp.down⟩)
    (X.presheaf.germ_res_apply i.unop p hp.down a).symm

omit [IsIntegral X] [Module (X.presheaf.stalk p) N] in
/-- THEOREM. Skyscraper sections satisfy unique gluing.
Locator: the stalk-to-skyscraper adjunction, with gluing at the support point. -/
private theorem localSkyPresheaf_isSheaf :
    Presheaf.IsSheaf (Opens.grothendieckTopology X) (localSkyPresheaf p N) := by
  classical
  apply (TopCat.Presheaf.isSheaf_iff_isSheafUniqueGluing (X := X.carrier)
    (localSkyPresheaf p N)).mpr
  intro ι cover sections compatible
  choose index index_mem using fun hp : PLift (p ∈ iSup cover) => Opens.mem_iSup.mp hp.down
  let glued : LocalSkySections p N (iSup cover) :=
    fun hp => sections (index hp) ⟨index_mem hp⟩
  refine ⟨glued, ?_, ?_⟩
  · intro i
    funext hp
    exact congrFun (compatible (index ⟨(Opens.leSupr cover i).le hp.down⟩) i)
      ⟨⟨index_mem ⟨(Opens.leSupr cover i).le hp.down⟩, hp.down⟩⟩
  · intro other hother
    funext hp
    exact congrFun (hother (index hp)) ⟨index_mem hp⟩

/-- DEFINITION. The actual module skyscraper with specified local-ring fiber.
Locator: the stalk-to-skyscraper adjunction;
`AlgebraicGeometry/Modules/Stalk.lean`, `skyscraper`. -/
private def localSky : X.Modules where
  val := PresheafOfModules.ofPresheaf (localSkyPresheaf p N)
    (fun _ _ i a s => localSkyPresheaf_map_smul p N i a s)
  isSheaf := localSkyPresheaf_isSheaf p N

/-- DEFINITION. A local-ring-linear map on the stalk gives a sheaf map to its
skyscraper. Locator: the stalk-to-skyscraper adjunction, defined on germs. -/
private def toLocalSky {M : X.Modules} (l : M.presheaf.stalk p →ₗ[X.presheaf.stalk p] N) :
    M ⟶ localSky p N :=
  ⟨PresheafOfModules.homMk
    { app := fun U => AddCommGrpCat.ofHom
        { toFun := fun s => show LocalSkySections p N U.unop from
            fun hp => l (M.presheaf.germ U.unop p hp.down s)
          map_zero' := by
            funext hp
            simp only [map_zero]
            rfl
          map_add' := by
            intro s t
            funext hp
            simp only [map_add]
            rfl }
      naturality := by
        intro U V i
        ext s
        funext hp
        exact congrArg l (M.presheaf.germ_res_apply i.unop p hp.down s) }
    (fun U a s => by
      funext hp
      exact (congrArg l (moduleGerm_smul M p U.unop hp.down a s)).trans
        (l.map_smul _ _))⟩

omit [IsIntegral X] in
/-- THEOREM. The map to the skyscraper is evaluation of the map on the section germ.
Locator: `toLocalSky`. -/
private theorem toLocalSky_app {M : X.Modules}
    (l : M.presheaf.stalk p →ₗ[X.presheaf.stalk p] N)
    (U : X.Opens) (s : Γ(M, U)) (hp : p ∈ U) :
    (toLocalSky p N l).app U s ⟨hp⟩ = l (M.presheaf.germ U p hp s) := rfl

/-- DEFINITION. The additive stalk map induced by a sheaf map to a skyscraper,
expressed as its compatible neighborhood evaluations.
Locator: the filtered-colimit definition of a stalk. -/
private def localSkyMapCocone {M : X.Modules} (h : M ⟶ localSky p N) :
    Cocone ((OpenNhds.inclusion p).op ⋙ M.presheaf) where
  pt := AddCommGrpCat.of N
  ι :=
    { app := fun U => AddCommGrpCat.ofHom
        { toFun := fun s => h.app U.unop.1 s ⟨U.unop.2⟩
          map_zero' := by
            rw [map_zero]
            rfl
          map_add' := by
            intro s t
            rw [map_add]
            rfl }
      naturality := by
        intro U V i
        ext s
        have hn := h.mapPresheaf.naturality_apply ((OpenNhds.inclusion p).op.map i) s
        exact congrArg (fun z => z ⟨V.unop.2⟩) hn }

/-- DEFINITION. The additive map on a stalk furnished by its colimit.
Locator: `localSkyMapCocone` and `colimit.desc`. -/
private def localSkyMapAdd {M : X.Modules} (h : M ⟶ localSky p N) :
    M.presheaf.stalk p →+ N :=
  ConcreteCategory.hom (colimit.desc _ (localSkyMapCocone p N h))

omit [IsIntegral X] in
/-- THEOREM. Evaluation of the induced stalk map on a germ is the skyscraper
component at the support point. Locator: the stalk colimit identity. -/
private theorem localSkyMapAdd_germ {M : X.Modules} (h : M ⟶ localSky p N)
    (U : X.Opens) (hp : p ∈ U) (s : Γ(M, U)) :
    localSkyMapAdd p N h (M.presheaf.germ U p hp s) = h.app U s ⟨hp⟩ := by
  have hc := (colimit.isColimit ((OpenNhds.inclusion p).op ⋙ M.presheaf)).fac
    (localSkyMapCocone p N h) (op ⟨U, hp⟩)
  exact ConcreteCategory.congr_hom hc s

/-- DEFINITION. A compatible additive stalk map is linear when it respects
germ scalar multiplication. Locator: the local-ring action on a sheaf stalk;
`AlgebraicGeometry/Modules/Stalk.lean`, `stalkLinearMapMk`. -/
private def localStalkLinearMapMk {M : X.Modules} (l : M.presheaf.stalk p →+ N)
    (hl : ∀ (U : X.Opens) (hp : p ∈ U) (a : Γ(X, U)) (s : Γ(M, U)),
      l (M.presheaf.germ U p hp (a • s)) =
        X.presheaf.germ U p hp a • l (M.presheaf.germ U p hp s)) :
    M.presheaf.stalk p →ₗ[X.presheaf.stalk p] N where
  __ := l
  map_smul' r ξ := by
    obtain ⟨U, hpU, a, rfl⟩ := X.presheaf.exists_germ_eq r
    obtain ⟨V, hpV, s, rfl⟩ := M.presheaf.exists_germ_eq ξ
    have hpUV : p ∈ U ⊓ V := ⟨hpU, hpV⟩
    rw [← X.presheaf.germ_res_apply (homOfLE (inf_le_left : U ⊓ V ≤ U)) p hpUV a,
      ← M.presheaf.germ_res_apply (homOfLE (inf_le_right : U ⊓ V ≤ V)) p hpUV s,
      ← moduleGerm_smul M p (U ⊓ V) hpUV]
    exact hl _ hpUV _ _

/-- DEFINITION. A sheaf map to the local-ring skyscraper induces a local-ring
linear map on the stalk. Locator: the stalk-to-skyscraper adjunction. -/
private def localSkyMapLinear {M : X.Modules} (h : M ⟶ localSky p N) :
    M.presheaf.stalk p →ₗ[X.presheaf.stalk p] N :=
  localStalkLinearMapMk p N (localSkyMapAdd p N h) (fun U hp a s => by
    rw [localSkyMapAdd_germ, localSkyMapAdd_germ]
    exact congrArg (fun z => z ⟨hp⟩) (h.app_smul a s))

/-- THEOREM. The induced linear stalk map evaluates a germ by the corresponding
skyscraper component. Locator: `localSkyMapAdd_germ`. -/
private theorem localSkyMapLinear_germ {M : X.Modules} (h : M ⟶ localSky p N)
    (U : X.Opens) (hp : p ∈ U) (s : Γ(M, U)) :
    localSkyMapLinear p N h (M.presheaf.germ U p hp s) = h.app U s ⟨hp⟩ :=
  localSkyMapAdd_germ p N h U hp s

end SkyscraperCalculation

section StalkEquivalence

open PresheafOfModulesOfCommRing

variable {X : Scheme.{0}} [IsIntegral X] (f : X ⟶ Spec (.of K))

omit [IsIntegral X] in
/-- THEOREM. A section of the inverse-image structure presheaf has a representative
on a base open. Locator: the filtered left Kan extension defining presheaf pullback;
`AlgebraicGeometry/Modules/Differentials.lean`, the inverse-image representative lemma. -/
private theorem inverseImageStructureMap_exists_appLE (W : X.Opens)
    (b : (inverseImageStructure f).obj (op W)) :
    ∃ (V : (Spec (.of K)).Opens) (h : W ≤ f ⁻¹ᵁ V) (a : Γ(Spec (.of K), V)),
      (inverseImageStructureMap f).app (op W) b = f.appLE V W h a := by
  haveI : IsFiltered (CostructuredArrow (Opens.map f.base).op (op W)) :=
    IsFiltered.of_equivalence (structuredArrowOpEquivalence _ _)
  obtain ⟨g, a, rfl⟩ := Concrete.isColimit_exists_rep _
    ((Opens.map f.base).op.isPointwiseLeftKanExtensionLeftKanExtensionUnit
      (Spec (.of K)).presheaf (op W)) b
  refine ⟨g.left.unop, leOfHom g.hom.unop, a, ?_⟩
  rw [inverseImageMap_appLE_factor]
  have hunit :
      ((TopCat.Presheaf.pullbackPushforwardAdjunction CommRingCat f.base).unit.app
        (Spec (.of K)).presheaf).app g.left ≫
          (inverseImageStructure f).map (homOfLE (leOfHom g.hom.unop)).op =
      ((Functor.LeftExtension.mk _ ((Opens.map f.base).op.leftKanExtensionUnit
        (Spec (.of K)).presheaf)).coconeAt (op W)).ι.app g := by
    rw [TopCat.Presheaf.pullbackPushforwardAdjunction, Functor.lanAdjunction_unit]
    rfl
  rw [← Category.assoc, hunit]
  rfl

/-- DEFINITION. The local-ring universal Kähler derivative, as a relative sheaf
derivation into the corresponding skyscraper module.
Locator: the universal property of Kähler differentials and the stalk-to-skyscraper
adjunction; the vanishing on the inverse image is proved from its base representative. -/
private def localKaehlerSkyDerivation (p : X) :
    letI := stalkAlgebra f p
    PresheafOfModulesOfCommRing.Derivation'
      (localSky p (KaehlerDifferential K (X.presheaf.stalk p))).val
      (inverseImageStructureMap f) := by
  letI := stalkAlgebra f p
  refine
    { d := fun {U} =>
        { toFun := fun a => show LocalSkySections p
            (KaehlerDifferential K (X.presheaf.stalk p)) U.unop from
              fun hp => D K (X.presheaf.stalk p) (X.presheaf.germ U.unop p hp.down a)
          map_zero' := by
            funext hp
            change D K (X.presheaf.stalk p) (X.presheaf.germ U.unop p hp.down 0) = 0
            simp only [map_zero]
          map_add' := by
            intro a b
            funext hp
            change D K (X.presheaf.stalk p) (X.presheaf.germ U.unop p hp.down (a + b)) =
              D K (X.presheaf.stalk p) (X.presheaf.germ U.unop p hp.down a) +
                D K (X.presheaf.stalk p) (X.presheaf.germ U.unop p hp.down b)
            simp only [map_add] }
      d_mul := ?_
      d_map := ?_
      d_app := ?_ }
  · intro U a b
    funext hp
    change D K (X.presheaf.stalk p) (X.presheaf.germ U.unop p hp.down (a * b)) =
      X.presheaf.germ U.unop p hp.down a •
        D K (X.presheaf.stalk p) (X.presheaf.germ U.unop p hp.down b) +
      X.presheaf.germ U.unop p hp.down b •
        D K (X.presheaf.stalk p) (X.presheaf.germ U.unop p hp.down a)
    rw [map_mul]
    exact (D K (X.presheaf.stalk p)).leibniz _ _
  · intro U V i a
    funext hp
    exact congrArg (D K (X.presheaf.stalk p))
      (X.presheaf.germ_res_apply i.unop p hp.down a)
  · intro W b
    funext hp
    obtain ⟨V, h, a, ha⟩ := inverseImageStructureMap_exists_appLE f W.unop b
    obtain rfl : V = ⊤ := eq_top_iff.mpr fun y _ =>
      Subsingleton.elim (f p) y ▸ h hp.down
    obtain ⟨c, rfl⟩ := (ConcreteCategory.bijective_of_isIso
      (Scheme.ΓSpecIso (.of K)).inv).2 a
    change D K (X.presheaf.stalk p)
      (X.presheaf.germ W.unop p hp.down ((inverseImageStructureMap f).app W b)) = 0
    rw [ha, germ_base_constant f p W.unop hp.down c]
    exact (D K (X.presheaf.stalk p)).map_algebraMap c

/-- DEFINITION. The universal derivation on the local ring gives the canonical
map from its Kähler module into the differential sheaf stalk.
Locator: `stalkDerivative` and `Derivation.liftKaehlerDifferential`. -/
private def localKaehlerToSheaf (p : X) :
    letI := stalkAlgebra f p
    KaehlerDifferential K (X.presheaf.stalk p) →ₗ[X.presheaf.stalk p]
      (differentialSheaf f).presheaf.stalk p := by
  letI := stalkAlgebra f p
  letI : Module K ((differentialSheaf f).presheaf.stalk p) :=
    Module.compHom _ (algebraMap K (X.presheaf.stalk p))
  haveI : IsScalarTower K (X.presheaf.stalk p) ((differentialSheaf f).presheaf.stalk p) :=
    IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  exact (stalkDerivative f p).liftKaehlerDifferential

/-- THEOREM. The canonical map takes the Kähler derivative of a germ to the
sheaf derivative germ. Locator: the defining universal derivation. -/
private theorem localKaehlerToSheaf_D_germ (p : X) (U : X.Opens) (hp : p ∈ U)
    (a : Γ(X, U)) :
    letI := stalkAlgebra f p
    localKaehlerToSheaf f p (D K (X.presheaf.stalk p) (X.presheaf.germ U p hp a)) =
      (differentialSheaf f).presheaf.germ U p hp
        ((differentialDerivation f).d (X := op U) a) := by
  letI := stalkAlgebra f p
  letI : Module K ((differentialSheaf f).presheaf.stalk p) :=
    Module.compHom _ (algebraMap K (X.presheaf.stalk p))
  haveI : IsScalarTower K (X.presheaf.stalk p) ((differentialSheaf f).presheaf.stalk p) :=
    IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  change (stalkDerivative f p).liftKaehlerDifferential
    (D K (X.presheaf.stalk p) (X.presheaf.germ U p hp a)) = _
  rw [Derivation.liftKaehlerDifferential_comp_D]
  exact stalkDerivative_germ f p U hp a

/-- DEFINITION. The inverse map comes from the relative sheaf universal property
with target the local Kähler skyscraper and then its stalk evaluation.
Locator: `differentialHomEquiv` and `localSkyMapLinear`. -/
private def sheafToLocalKaehler (p : X) :
    letI := stalkAlgebra f p
    (differentialSheaf f).presheaf.stalk p →ₗ[X.presheaf.stalk p]
      KaehlerDifferential K (X.presheaf.stalk p) := by
  letI := stalkAlgebra f p
  exact localSkyMapLinear p (KaehlerDifferential K (X.presheaf.stalk p))
    ((differentialHomEquiv f _).symm (localKaehlerSkyDerivation f p))

/-- THEOREM. The inverse map sends a sheaf derivative germ to its local-ring
Kähler derivative. Locator: the sheaf universal property with skyscraper target. -/
private theorem sheafToLocalKaehler_D_germ (p : X) (U : X.Opens) (hp : p ∈ U)
    (a : Γ(X, U)) :
    letI := stalkAlgebra f p
    sheafToLocalKaehler f p ((differentialSheaf f).presheaf.germ U p hp
      ((differentialDerivation f).d (X := op U) a)) =
      D K (X.presheaf.stalk p) (X.presheaf.germ U p hp a) := by
  letI := stalkAlgebra f p
  change localSkyMapLinear p (KaehlerDifferential K (X.presheaf.stalk p))
    ((differentialHomEquiv f _).symm (localKaehlerSkyDerivation f p))
      ((differentialSheaf f).presheaf.germ U p hp ((differentialDerivation f).d a)) = _
  rw [localSkyMapLinear_germ]
  exact congrArg (fun s => s ⟨hp⟩) (differentialHomEquiv_symm_app_d f
    (localSky p (KaehlerDifferential K (X.presheaf.stalk p)))
      (localKaehlerSkyDerivation f p) (op U) a)

/-- DEFINITION (proved local isomorphism). The stalk of the actual relative
Kähler differential sheaf is canonically the Kähler module of the actual local
ring, compatibly with both universal derivations. No smoothness is needed.
Locator: Stacks Project, Tag 01UM; the sheaf and local-ring universal properties
and the stalk-to-skyscraper adjunction. -/
def stalkKaehlerEquiv (p : X) :
    letI := stalkAlgebra f p
    KaehlerDifferential K (X.presheaf.stalk p) ≃ₗ[X.presheaf.stalk p]
      (differentialSheaf f).presheaf.stalk p := by
  letI := stalkAlgebra f p
  let Θ := localKaehlerToSheaf f p
  let δ := sheafToLocalKaehler f p
  have hleft : δ ∘ₗ Θ = LinearMap.id := by
    apply Derivation.liftKaehlerDifferential_unique
    ext z
    obtain ⟨U, hp, a, rfl⟩ := X.presheaf.exists_germ_eq z
    change sheafToLocalKaehler f p
      (localKaehlerToSheaf f p (D K (X.presheaf.stalk p) (X.presheaf.germ U p hp a))) =
        D K (X.presheaf.stalk p) (X.presheaf.germ U p hp a)
    rw [localKaehlerToSheaf_D_germ, sheafToLocalKaehler_D_germ]
  let M := differentialSheaf f
  let g : M ⟶ localSky p (M.presheaf.stalk p) :=
    toLocalSky p (M.presheaf.stalk p) (Θ ∘ₗ δ)
  let h : M ⟶ localSky p (M.presheaf.stalk p) :=
    toLocalSky p (M.presheaf.stalk p) LinearMap.id
  have hmaps : g = h := by
    apply (differentialHomEquiv f _).injective
    ext U a
    funext hp
    change g.app U.unop ((differentialDerivation f).d a) ⟨hp.down⟩ =
      h.app U.unop ((differentialDerivation f).d a) ⟨hp.down⟩
    rw [show g = toLocalSky p (M.presheaf.stalk p) (Θ ∘ₗ δ) from rfl,
      show h = toLocalSky p (M.presheaf.stalk p) LinearMap.id from rfl,
      toLocalSky_app, toLocalSky_app, LinearMap.comp_apply, LinearMap.id_apply]
    change localKaehlerToSheaf f p (sheafToLocalKaehler f p
      (M.presheaf.germ U.unop p hp.down ((differentialDerivation f).d a))) = _
    rw [sheafToLocalKaehler_D_germ, localKaehlerToSheaf_D_germ]
  refine { Θ with
    invFun := δ
    left_inv := LinearMap.congr_fun hleft
    right_inv := ?_ }
  intro ξ
  obtain ⟨U, hp, s, rfl⟩ := M.presheaf.exists_germ_eq ξ
  have heq := congrArg (fun b : M ⟶ localSky p (M.presheaf.stalk p) => b.app U s ⟨hp⟩) hmaps
  change (toLocalSky p (M.presheaf.stalk p) (Θ ∘ₗ δ)).app U s ⟨hp⟩ =
    (toLocalSky p (M.presheaf.stalk p) LinearMap.id).app U s ⟨hp⟩ at heq
  rw [toLocalSky_app, toLocalSky_app, LinearMap.comp_apply, LinearMap.id_apply] at heq
  exact heq

/-- THEOREM. The canonical stalk isomorphism respects the universal derivative
of every section germ. Locator: `localKaehlerToSheaf_D_germ`. -/
theorem stalkKaehlerEquiv_D_germ (p : X) (U : X.Opens) (hp : p ∈ U) (a : Γ(X, U)) :
    letI := stalkAlgebra f p
    stalkKaehlerEquiv f p (D K (X.presheaf.stalk p) (X.presheaf.germ U p hp a)) =
      (differentialSheaf f).presheaf.germ U p hp ((differentialDerivation f).d (X := op U) a) :=
  localKaehlerToSheaf_D_germ f p U hp a

/-- THEOREM. The canonical local Kähler identifications are proved for every
integral scheme over `K`; they are not a remaining comparison input.
Locator: `stalkKaehlerEquiv` and its universal-derivation computation. -/
theorem stalkDifferentials : StalkDifferentials (K := K) := by
  intro X _ f
  exact ⟨{
    equiv := stalkKaehlerEquiv f
    equiv_D_germ := stalkKaehlerEquiv_D_germ f }⟩

end StalkEquivalence

section SchemePlaces


/-- THEOREM. The local ring of a smooth integral curve over `K` is either a field
or a discrete valuation ring. Locator: `SmoothCurve.lean`,
`smooth_curve_valuation_stalk`, including its local-dimension proof. -/
theorem stalk_isField_or_discreteValuationRing {X : Scheme.{0}} [IsIntegral X]
    (f : X ⟶ Spec (.of K)) [Smooth f] (hdim : topologicalKrullDim X = 1) (p : X) :
    IsField (X.presheaf.stalk p) ∨ IsDiscreteValuationRing (X.presheaf.stalk p) := by
  haveI := smooth_stalk_regular f p
  have hle : ringKrullDim (X.presheaf.stalk p) ≤ 1 := by
    rw [ringKrullDim_stalk_eq_coheight]
    have h := Order.coheight_le_krullDim p
    have heq : topologicalKrullDim X = Order.krullDim X :=
      Order.krullDim_eq_of_orderIso (irreducibleSetEquivPoints (α := X))
    rw [← heq, hdim] at h
    exact_mod_cast h
  by_cases h₁ : ringKrullDim (X.presheaf.stalk p) = 1
  · right
    apply IsLocalRing.finrank_CotangentSpace_eq_one_iff.mp
    have h := (IsRegularLocalRing.iff_finrank_cotangentSpace (R := X.presheaf.stalk p)).mp
      (inferInstance : IsRegularLocalRing (X.presheaf.stalk p))
    rw [h₁] at h
    exact_mod_cast h
  · left
    have h₀ : ringKrullDim (X.presheaf.stalk p) ≤ 0 :=
      ENat.WithBot.lt_add_one_iff.mp (lt_of_le_of_ne hle h₁)
    haveI : Ring.KrullDimLE 0 (X.presheaf.stalk p) := ⟨by exact_mod_cast h₀⟩
    exact Ring.KrullDimLE.isField_of_isDomain (R := X.presheaf.stalk p)

/-- THEOREM. A fraction-field embedding out of a field is surjective.
Locator: Mathlib `IsFractionRing.algEquiv`. -/
private theorem fractionMap_surjective {A K : Type} [Field A] [Field K]
    [Algebra A K] [IsFractionRing A K] : Function.Surjective (algebraMap A K) := by
  let e : A ≃ₐ[A] K := IsFractionRing.algEquiv A A K
  intro z
  obtain ⟨a, ha⟩ := e.surjective z
  refine ⟨a, ?_⟩
  have hc : e a = algebraMap A K a := by simpa using e.commutes a
  exact hc.symm.trans ha

/-- THEOREM. Every place of the actual function field of a smooth proper curve over `K`
is represented by a discrete local ring on the curve. Properness is used
only through the valuative criterion; no genus or differential comparison is used.
Locator: Silverman Chapter II, §§2 and 4; Mathlib's valuative criterion and
`TauCeti.Place.eq_of_integers_le`. -/
theorem everyPlace_has_stalk_model {X : Scheme.{0}} [IsIntegral X]
    (f : X ⟶ Spec (.of K)) [Smooth f] [IsProper f] (hdim : topologicalKrullDim X = 1) :
    letI := functionFieldAlgebra f
    ∀ P : Place K X.functionField, ∃ p : X,
      IsDiscreteValuationRing (X.presheaf.stalk p) ∧
      P.integers.toSubring = (⊤ : Subring (X.presheaf.stalk p)).map
        (algebraMap (X.presheaf.stalk p) X.functionField) := by
  letI := functionFieldAlgebra f
  intro P
  let i : Spec X.functionField ⟶ Spec (.of P.integers) :=
    Spec.map (CommRingCat.ofHom (algebraMap P.integers X.functionField))
  let s : Spec (.of P.integers) ⟶ Spec (.of K) :=
    Spec.map (CommRingCat.ofHom (algebraMap K P.integers))
  have hsquare : CommSq (fromFunctionField X) i f s := ⟨by
    rw [fromFunctionField_structure]
    dsimp only [i, s]
    rw [← Spec.map_comp]
    congr 1⟩
  have hex : ValuativeCriterion.Existence f :=
    (UniversallyClosed.eq_valuativeCriterion ▸ (inferInstance : UniversallyClosed f)).1
  obtain ⟨⟨l, hl, -⟩⟩ := hex
    { R := P.integers, domain := inferInstance, K := X.functionField,
      i₁ := fromFunctionField X, i₂ := s, commSq := hsquare }
  let p : X := l (IsLocalRing.closedPoint P.integers)
  let φ : X.presheaf.stalk p ⟶ CommRingCat.of P.integers := Scheme.stalkClosedPointTo l
  have hφ : φ ≫ CommRingCat.ofHom (algebraMap P.integers X.functionField) =
      CommRingCat.ofHom (algebraMap (X.presheaf.stalk p) X.functionField) := by
    apply Spec.map_injective
    apply (cancel_mono (X.fromSpecStalk p)).mp
    rw [Spec.map_comp, Category.assoc]
    change i ≫ (Spec.map (Scheme.stalkClosedPointTo l) ≫ X.fromSpecStalk p) = _
    rw [Scheme.Spec_stalkClosedPointTo_fromSpecStalk, hl]
    exact (Scheme.SpecMap_stalkSpecializes_fromSpecStalk (genericPoint_specializes p)).symm
  have hmem : ∀ a : X.presheaf.stalk p,
      algebraMap (X.presheaf.stalk p) X.functionField a ∈ P.integers := by
    intro a
    have heq := ConcreteCategory.congr_hom hφ a
    change (φ a : X.functionField) = algebraMap (X.presheaf.stalk p) X.functionField a at heq
    exact heq ▸ (φ a).2
  rcases stalk_isField_or_discreteValuationRing f hdim p with hp | hp
  · letI := hp.toField
    have hall : ∀ z : X.functionField, z ∈ P.integers := by
      intro z
      obtain ⟨a, rfl⟩ := fractionMap_surjective (A := X.presheaf.stalk p) (K := X.functionField) z
      exact hmem a
    exact (P.integers_ne_top (top_unique fun z _ => hall z)).elim
  · haveI := hp
    let Q : Place K X.functionField := stalkPlace f p
    have hQP : Q.integers ≤ P.integers := by
      change Q.integers.toSubring ≤ P.integers.toSubring
      rw [show Q.integers.toSubring = (⊤ : Subring (X.presheaf.stalk p)).map
        (algebraMap (X.presheaf.stalk p) X.functionField) from stalkPlace_integers f p]
      rintro z ⟨a, -, rfl⟩
      exact hmem a
    have heq : Q = P := Place.eq_of_integers_le hQP
    refine ⟨p, hp, ?_⟩
    rw [← heq]
    exact stalkPlace_integers f p

end SchemePlaces

section RingModels

variable {k : Type} [Field k] {A B : Type} [CommRing A] [CommRing B]
  [Algebra k A] [Algebra k B] [Algebra A B] [IsScalarTower k A B]

/-- THEOREM. A bijective algebra map induces a bijective Kähler differential map.
Locator: Mathlib `KaehlerDifferential.ker_map_of_surjective` and
`KaehlerDifferential.map_surjective_of_surjective`. -/
private theorem kaehlerMap_bijective_of_bijective
    (h : Function.Bijective (algebraMap A B)) :
    Function.Bijective (KaehlerDifferential.map k k A B) := by
  refine ⟨?_, KaehlerDifferential.map_surjective_of_surjective k k A B h.2⟩
  rw [← LinearMap.ker_eq_bot, KaehlerDifferential.ker_map_of_surjective k A B h.2]
  have hfs : Function.Injective
      ((Finsupp.mapRange.linearMap (Algebra.linearMap A B)).comp
        (Finsupp.lmapDomain A A (algebraMap A B))) :=
    (Finsupp.mapRange_injective (algebraMap A B) (map_zero _) h.1).comp
      (Finsupp.mapDomain_injective h.1)
  rw [LinearMap.ker_eq_bot.mpr hfs, Submodule.map_bot]

end RingModels


section CurveComparison

/-- DEFINITION. The constants-linear map from the Kähler module of a scheme's
local ring to the Kähler module of its actual function field.
Locator: Mathlib `KaehlerDifferential.map`; the scalar towers in `IdentityPlace.lean`. -/
def stalkKaehlerMap {X : Scheme.{0}} [IsIntegral X]
    (f : X ⟶ Spec (.of K)) (p : X) :
    letI := functionFieldAlgebra f
    letI := stalkAlgebra f p
    letI := stalk_functionField_tower f p
    KaehlerDifferential K (X.presheaf.stalk p) →ₗ[K]
      KaehlerDifferential K X.functionField := by
  letI := functionFieldAlgebra f
  letI := stalkAlgebra f p
  haveI := stalk_functionField_tower f p
  exact (KaehlerDifferential.map K K (X.presheaf.stalk p) X.functionField).restrictScalars K

/-- THEOREM. Local uniformizer bases imply that every stalk Kähler localization
map on a smooth integral curve is injective. The field case is proved separately.
Locator: `stalk_isField_or_discreteValuationRing`, `stalkPlace_integers`, and
`kaehler_local_image_transport`. -/
theorem stalkKaehlerMap_injective [CharZero K] (hB : LocalUniformizerBasis)
    {X : Scheme.{0}} [IsIntegral X] (f : X ⟶ Spec (.of K)) [Smooth f]
    (hdim : topologicalKrullDim X = 1) (p : X) :
    letI := functionFieldAlgebra f
    Function.Injective (stalkKaehlerMap f p) := by
  letI := functionFieldAlgebra f
  letI := stalkAlgebra f p
  haveI := stalk_functionField_tower f p
  have hF := isFunctionField_of_dimension_one f hdim
  rcases stalk_isField_or_discreteValuationRing f hdim p with hp | hp
  · letI := hp.toField
    exact (kaehlerMap_bijective_of_bijective (k := K)
      (A := X.presheaf.stalk p) (B := X.functionField)
      ⟨IsFractionRing.injective _ _, fractionMap_surjective⟩).1
  · haveI := hp
    let P : Place K X.functionField := stalkPlace f p
    obtain ⟨t, ht, b, hb⟩ := hB K X.functionField hF P
    exact (kaehler_local_image_transport P (stalkPlace_integers f p)
      (IsFractionRing.injective _ _)
      (localKaehlerMap_injective_of_uniformizerBasis hF P t ht b hb)).1

/-- THEOREM. Regularity at every place is membership in the Kähler localization
image of every actual local ring of a smooth proper geometrically integral curve.
All point-to-place and place-to-point steps are proved, not supplied as inputs.
Locator: Silverman Chapter II, §§4–5; `everyPlace_has_stalk_model` above. -/
theorem regularAt_iff_mem_stalk_ranges [CharZero K] (hB : LocalUniformizerBasis)
    (hO : UniformizerResidueOrder) {X : Scheme.{0}} [IsIntegral X]
    (f : X ⟶ Spec (.of K)) [Smooth f] [IsProper f] [GeometricallyIntegral f]
    (hdim : topologicalKrullDim X = 1) (x : X.functionField)
    (hx : letI := functionFieldAlgebra f; Transcendental K x) :
    letI := functionFieldAlgebra f
    let hF := isFunctionField_of_dimension_one f hdim
    let hex := functionField_exact_constants f
    letI := hF.finiteDimensional_adjoin hx
    letI := weilDifferentialSpaceModule hF
    ∀ η : KaehlerDifferential K X.functionField,
      (∀ P : Place K X.functionField, RegularAt P (comparison hF hex hx η)) ↔
      ∀ p : X, letI := stalkAlgebra f p
        η ∈ (stalkKaehlerMap f p).range := by
  letI := functionFieldAlgebra f
  let hF := isFunctionField_of_dimension_one f hdim
  let hex := functionField_exact_constants f
  haveI := hF.finiteDimensional_adjoin hx
  letI := weilDifferentialSpaceModule hF
  dsimp only
  intro η
  constructor
  · intro hη p
    letI := stalkAlgebra f p
    haveI := stalk_functionField_tower f p
    rcases stalk_isField_or_discreteValuationRing f hdim p with hp | hp
    · letI := hp.toField
      exact (kaehlerMap_bijective_of_bijective (k := K)
        (A := X.presheaf.stalk p) (B := X.functionField)
        ⟨IsFractionRing.injective _ _, fractionMap_surjective⟩).2 η
    · haveI := hp
      let P : Place K X.functionField := stalkPlace f p
      have hloc := localComparison_of_uniformizer_facts hB hO K X.functionField
        hF hex x hx P
      exact (kaehler_local_image_transport P (stalkPlace_integers f p)
        (IsFractionRing.injective _ _) hloc.1).2 η |>.mpr ((hloc.2 η).mp (hη P))
  · intro hη P
    obtain ⟨p, hp, hP⟩ := everyPlace_has_stalk_model f hdim P
    letI := stalkAlgebra f p
    haveI := stalk_functionField_tower f p
    have hloc := localComparison_of_uniformizer_facts hB hO K X.functionField
      hF hex x hx P
    exact (hloc.2 η).mpr
      (((kaehler_local_image_transport P hP (IsFractionRing.injective _ _) hloc.1).2 η).mp
        (hη p))

end CurveComparison

section GlobalSections


variable {X : Scheme.{0}} [IsIntegral X] (f : X ⟶ Spec (.of K))

/-- DEFINITION. Restriction of global sections to the actual generic sheaf stalk,
as a constants-linear map with the specified structure morphism.
Locator: Mathlib `PresheafOfModules.germ_smul`; `DifferentialLine.lean`,
`globalSectionsModule` and `functionFieldAlgebra`. -/
private def genericGermLinear (M : X.Modules) :
    letI := functionFieldAlgebra f
    letI := globalSectionsModule f M
    letI : Module K (M.presheaf.stalk (genericPoint X)) :=
      Module.compHom _ (algebraMap K X.functionField)
    Γ(M, ⊤) →ₗ[K] M.presheaf.stalk (genericPoint X) := by
  letI := functionFieldAlgebra f
  letI := globalSectionsModule f M
  letI : Module K (M.presheaf.stalk (genericPoint X)) :=
    Module.compHom _ (algebraMap K X.functionField)
  refine { toFun := M.presheaf.germ ⊤ (genericPoint X) trivial
           map_add' := map_add _
           map_smul' := ?_ }
  intro c s
  change M.presheaf.germ ⊤ (genericPoint X) trivial ((globalFunctionsMap f c) • s) =
    algebraMap K X.functionField c • M.presheaf.germ ⊤ (genericPoint X) trivial s
  rw [moduleGerm_smul M]
  rfl

/-- DEFINITION. The canonical rational Kähler differential of a global sheaf
section, using the local stalk calculation, not an assumed global equivalence.
Locator: Silverman Chapter II, §§4–5; `DifferentialStalkData.equiv_D_germ`. -/
def rationalRestriction (d : DifferentialStalkData f) :
    letI := functionFieldAlgebra f
    letI := globalSectionsModule f (differentialSheaf f)
    Γ(differentialSheaf f, ⊤) →ₗ[K] KaehlerDifferential K X.functionField := by
  letI := functionFieldAlgebra f
  letI := globalSectionsModule f (differentialSheaf f)
  let M := differentialSheaf f
  letI : Module K (M.presheaf.stalk (genericPoint X)) :=
    Module.compHom _ (algebraMap K X.functionField)
  haveI : IsScalarTower K X.functionField (M.presheaf.stalk (genericPoint X)) :=
    IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  let e : KaehlerDifferential K X.functionField ≃ₗ[X.functionField]
      M.presheaf.stalk (genericPoint X) := d.equiv (genericPoint X)
  exact (e.symm.restrictScalars K).toLinearMap ∘ₗ genericGermLinear f M

/-- THEOREM. Injectivity of the local Kähler maps implies injectivity of
specialization for the actual differential sheaf stalks.
Locator: the local Kähler identification and `DifferentialStalkData.specializes_equiv`. -/
theorem DifferentialStalkData.specializes_injective (d : DifferentialStalkData f)
    (hinj : letI := functionFieldAlgebra f
      ∀ p : X, Function.Injective (stalkKaehlerMap f p)) :
    ∀ p : X, Function.Injective
      ((differentialSheaf f).presheaf.stalkSpecializes (genericPoint_specializes p)) := by
  letI := functionFieldAlgebra f
  intro p a b hab
  letI := stalkAlgebra f p
  haveI := stalk_functionField_tower f p
  apply (d.equiv p).symm.injective
  apply hinj p
  apply (d.equiv (genericPoint X)).injective
  change d.equiv (genericPoint X)
      (KaehlerDifferential.map K K (X.presheaf.stalk p) X.functionField
        ((d.equiv p).symm a)) =
    d.equiv (genericPoint X)
      (KaehlerDifferential.map K K (X.presheaf.stalk p) X.functionField
        ((d.equiv p).symm b))
  rw [← d.specializes_equiv p, ← d.specializes_equiv p,
    LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]
  exact hab

/-- THEOREM. Restriction of global sheaf differentials to rational Kähler
differentials is injective once the local Kähler maps are injective.
Locator: the torsion-free sheaf criterion `genericGerm_injective`. -/
theorem rationalRestriction_injective (d : DifferentialStalkData f)
    (hinj : letI := functionFieldAlgebra f
      ∀ p : X, Function.Injective (stalkKaehlerMap f p)) :
    letI := functionFieldAlgebra f
    letI := globalSectionsModule f (differentialSheaf f)
    Function.Injective (rationalRestriction f d) := by
  letI := functionFieldAlgebra f
  letI := globalSectionsModule f (differentialSheaf f)
  letI : Nonempty (⊤ : X.Opens) := ⟨⟨genericPoint X, trivial⟩⟩
  intro s t hst
  apply genericGerm_injective (differentialSheaf f) (d.specializes_injective f hinj) ⊤
  change (d.equiv (genericPoint X)).symm
      ((differentialSheaf f).presheaf.germ ⊤ (genericPoint X) trivial s) =
    (d.equiv (genericPoint X)).symm
      ((differentialSheaf f).presheaf.germ ⊤ (genericPoint X) trivial t) at hst
  exact (d.equiv (genericPoint X)).symm.injective hst

/-- THEOREM. The image of global restriction is exactly membership in every
actual local Kähler image. Its reverse direction is proved by unique sheaf
gluing, not included in any input.
Locator: Silverman Chapter II, §§4–5; `existsUnique_section_of_mem_local_stalks`. -/
theorem rationalRestriction_range_iff_mem_stalk_ranges (d : DifferentialStalkData f)
    (hinj : letI := functionFieldAlgebra f
      ∀ p : X, Function.Injective (stalkKaehlerMap f p)) :
    letI := functionFieldAlgebra f
    letI := globalSectionsModule f (differentialSheaf f)
    ∀ η : KaehlerDifferential K X.functionField,
      η ∈ (rationalRestriction f d).range ↔
        ∀ p : X, letI := stalkAlgebra f p
          η ∈ (stalkKaehlerMap f p).range := by
  letI := functionFieldAlgebra f
  letI := globalSectionsModule f (differentialSheaf f)
  letI : Nonempty (⊤ : X.Opens) := ⟨⟨genericPoint X, trivial⟩⟩
  let M := differentialSheaf f
  let e : KaehlerDifferential K X.functionField ≃ₗ[X.functionField]
      M.presheaf.stalk (genericPoint X) := d.equiv (genericPoint X)
  intro η
  constructor
  · rintro ⟨s, rfl⟩ p
    letI := stalkAlgebra f p
    haveI := stalk_functionField_tower f p
    let ξ := (d.equiv p).symm (M.presheaf.germ ⊤ p trivial s)
    refine ⟨ξ, ?_⟩
    apply e.injective
    change d.equiv (genericPoint X)
      (KaehlerDifferential.map K K (X.presheaf.stalk p) X.functionField ξ) =
        e (e.symm (M.presheaf.germ ⊤ (genericPoint X) trivial s))
    rw [LinearEquiv.apply_symm_apply, ← d.specializes_equiv p]
    change M.presheaf.stalkSpecializes (genericPoint_specializes p)
      (d.equiv p ((d.equiv p).symm (M.presheaf.germ ⊤ p trivial s))) = _
    rw [LinearEquiv.apply_symm_apply,
      M.presheaf.germ_stalkSpecializes_apply (U := ⊤) (y := p)
        trivial (genericPoint_specializes p)]
  · intro hη
    let q : M.presheaf.stalk (genericPoint X) := e η
    have hlocal : ∀ p ∈ (⊤ : X.Opens), q ∈ Set.range
        (M.presheaf.stalkSpecializes (genericPoint_specializes p)) := by
      intro p _
      letI := stalkAlgebra f p
      haveI := stalk_functionField_tower f p
      obtain ⟨ξ, hξ⟩ := hη p
      refine ⟨d.equiv p ξ, ?_⟩
      exact (d.specializes_equiv p ξ).trans (congrArg e hξ)
    obtain ⟨s, hs, -⟩ := existsUnique_section_of_mem_local_stalks M
      (d.specializes_injective f hinj) ⊤ q hlocal
    refine ⟨s, ?_⟩
    change e.symm (M.presheaf.germ ⊤ (genericPoint X) trivial s) = η
    rw [hs]
    exact e.symm_apply_apply η

end GlobalSections

/-- THEOREM (proved, the regular-differential comparison in characteristic zero). For a
smooth proper geometrically integral curve over a field of characteristic zero, the global
sections of the sheafified relative Kähler differentials are `K`-linearly equivalent to the
holomorphic Weil differentials `Ω(0)` of the function field. The map is restriction to the
generic stalk followed by the normalized cotrace comparison; it is injective, and its image is
`Ω(0)` by the local uniformizer facts, proper place coverage and unique gluing.
Locator: Silverman Chapter II, §§4–5; Stichtenoth §§I.5 and I.7; the rational version
`AbelianCurveInputs.regularDifferentialComparison_of_local_inputs`, whose two local inputs are
`AbelianCurveInputs.LocalFacts.localUniformizerBasis` and
`AbelianCurveInputs.LocalFacts.uniformizerResidueOrder`, proved for every field of
characteristic zero. -/
theorem regularDifferentialComparison [CharZero K] (X : Scheme.{0}) [IsIntegral X]
    (f : X ⟶ Spec (.of K)) [Smooth f] [IsProper f] [GeometricallyIntegral f]
    (hdim : topologicalKrullDim X = 1) :
    letI := functionFieldAlgebra f
    letI := globalSectionsModule f (differentialSheaf f)
    Nonempty (Γ(differentialSheaf f, ⊤) ≃ₗ[K]
      ↥(weilDifferentialFiltration (0 : Divisor K X.functionField))) := by
  have hS := stalkDifferentials (K := K)
  have hB := ZInQ.Contrib.RC53Assist.AbelianCurveInputs.LocalFacts.localUniformizerBasis
  have hO := ZInQ.Contrib.RC53Assist.AbelianCurveInputs.LocalFacts.uniformizerResidueOrder
  letI := functionFieldAlgebra f
  letI := globalSectionsModule f
    (differentialSheaf f)
  obtain ⟨d⟩ := hS X f
  have hinj : ∀ p : X, Function.Injective (stalkKaehlerMap f p) :=
    stalkKaehlerMap_injective hB f hdim
  have hRinj := rationalRestriction_injective f d hinj
  let hF := isFunctionField_of_dimension_one f hdim
  let hex := functionField_exact_constants f
  obtain ⟨x, hx⟩ := hF.exists_transcendental
  haveI := hF.finiteDimensional_adjoin hx
  letI := weilDifferentialSpaceModule hF
  haveI := isScalarTower_weilDifferentialSpace hF
  let φ := (comparison hF hex hx).restrictScalars K
  let L : Γ(differentialSheaf f, ⊤) →ₗ[K]
      Module.Dual K ↥(repartitionSpace K X.functionField) :=
    (weilDifferentialSpace K X.functionField).subtype ∘ₗ φ.toLinearMap ∘ₗ
      rationalRestriction f d
  let W := weilDifferentialFiltration (0 : Divisor K X.functionField)
  have hLmem : ∀ s, L s ∈ W := by
    intro s
    change (φ (rationalRestriction f d s) : Module.Dual K
      ↥(repartitionSpace K X.functionField)) ∈ W
    rw [mem_zeroFiltration_iff_regularAt]
    exact (regularAt_iff_mem_stalk_ranges hB hO f hdim x hx
      (rationalRestriction f d s)).mpr
        ((rationalRestriction_range_iff_mem_stalk_ranges f d hinj
          (rationalRestriction f d s)).mp ⟨s, rfl⟩)
  let L₀ := L.codRestrict W hLmem
  have hLinj : Function.Injective L₀ := by
    intro s t hst
    have hv := congrArg (fun z : W => (z : Module.Dual K
      ↥(repartitionSpace K X.functionField))) hst
    change L s = L t at hv
    apply hRinj
    apply φ.injective
    exact Subtype.ext hv
  have hLsurj : Function.Surjective L₀ := by
    intro ω
    let w : ↥(weilDifferentialSpace K X.functionField) :=
      ⟨ω, weilDifferentialFiltration_le_weilDifferentialSpace _ ω.2⟩
    let η : KaehlerDifferential K X.functionField := φ.symm w
    have hmem : (φ η : Module.Dual K ↥(repartitionSpace K X.functionField)) ∈ W := by
      change (φ (φ.symm w) : Module.Dual K ↥(repartitionSpace K X.functionField)) ∈ W
      rw [LinearEquiv.apply_symm_apply]
      exact ω.2
    have hregular : ∀ P : Place K X.functionField, RegularAt P (comparison hF hex hx η) :=
      (mem_zeroFiltration_iff_regularAt (φ η)).mp hmem
    have hrange := (rationalRestriction_range_iff_mem_stalk_ranges f d hinj η).mpr
      ((regularAt_iff_mem_stalk_ranges hB hO f hdim x hx η).mp hregular)
    obtain ⟨s, hs⟩ := hrange
    refine ⟨s, Subtype.ext ?_⟩
    change (φ (rationalRestriction f d s) : Module.Dual K
      ↥(repartitionSpace K X.functionField)) = (ω : Module.Dual K
        ↥(repartitionSpace K X.functionField))
    rw [hs]
    exact congrArg Subtype.val (φ.apply_symm_apply w)
  exact ⟨LinearEquiv.ofBijective L₀ ⟨hLinj, hLsurj⟩⟩
end ZInQ.Contrib.RC53Assist.S2aNumberField
