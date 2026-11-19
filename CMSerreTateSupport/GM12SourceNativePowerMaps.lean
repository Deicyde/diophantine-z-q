/-
NEW SOURCE FIX EDITION — 2026-11-17, GM12 Source/native lookup repair.
The old 1b2f786547077ec30ed0846078ae2a676e42bfb8dd2536b194d4ff1ba8218bd1
edition remains frozen. Four dotted Source constructor names are now contiguous
qualified identifiers; their existing Source-prefixed targets are unchanged.
The tensor comparison locally installs the EXISTING root W07 theorem
SheafOfModules.isMonoidal_W at the SAME X.sheaf, solely for the existing native
tensorObjIsoSheafification comparison factor. Source powers/tensor/sheafify,
Source mapIso/pullbackIso constructors, native powers, all public written types,
binders, universe u, imports and options are retained. No dictionary alias,
new hypothesis/coherence premise or Source-to-native object substitution is made.
SOURCE ONLY, UNCOMPILED; Parent-only probe and C6 review required. F25 remains gated.
-/
/-
H5 Lane5 GM12: literal Source/native tensor-power and pullback maps.
SOURCE ONLY / UNCOMPILED. No native run, Source provider recovery or Type0 port.

NO-LINE ANALYSIS: PkgI2.HasGoodReduction A O asks only for an actual abelian
scheme GROUP over the ORIGINAL O and a generic-fibre GROUP isomorphism to the
SAME original A/K. It has no line bundle premise. L0 and M are existential
witnesses; closed sections and psi/cocycle are intermediate effective-descent
data. The later no-line theorem must descend Source M^n with beta^n to
L0' = Source power of the SAME L0, not substitute a new model or line.

The literal Source constructors are kept under their existing exact names.
Their historical Source.Definitions binding is NOT available in fork2880;
this module does not recover or rebind them. Availability/default-limit
binding is a separate Parent gate. The common sheafification is compared
by its actual constructor, not by a tensor-power alias or an ABI claim.

Blueprint attribution: frenzymath/FLT, commit 6e837e75..., Apache-2.0,
Anthropic, PBC, Def_SheafOfModules_Monoidal and Def_ModulesTensorPowV2;
only constructor shape is used. The W07 native tensor/pullback primitives
remain in their unchanged Apache-2.0 sources. All proofs below are new
universe-u compositions, not import or compilation of the FLT closure.
-/
import GM12NativePowerMaps
import ZInQKernel.Contrib.CloudR2NOS.Source.Definitions.Def_SheafOfModules_Monoidal
import ZInQKernel.Contrib.CloudR2NOS.Source.Definitions.Def_AlgebraicGeometry_ModulesTensorPowV2
import ZInQKernel.Contrib.CloudR2NOS.Source.Definitions.Def_AlgebraicGeometry_GradedOAlgebraSectionRing

set_option autoImplicit false
noncomputable section
universe u

open CategoryTheory MonoidalCategory AlgebraicGeometry

namespace H5OriginalDVR.Lane5.GM12.SourcePower

local notation "SPow" =>
  ZInQ.Contrib.CloudW03NeronSurj.FLT.AlgebraicGeometry.Scheme.Modules.tensorPow
local notation "STensor" =>
  ZInQ.Contrib.CloudW03NeronSurj.FLT.AlgebraicGeometry.Scheme.Modules.tensor
local notation "SSheafify" =>
  ZInQ.Contrib.CloudW03NeronSurj.FLT.AlgebraicGeometry.Scheme.Modules.sheafify

variable {X : Scheme.{u}}

/-- Compare the actual sheafification constructors on the same presheaf.
This is a narrowly written constructor calculation, not equality of the
Source/native monoidal structures or of their tensor powers. -/
def sheafificationComparison (X : Scheme.{u}) (P : X.PresheafOfModules) :
    (SSheafify X).obj P ≅ (Scheme.Modules.sheafification X).obj P := by
  change (_root_.PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).obj P ≅
    (_root_.PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).obj P
  exact Iso.refl _

/-- The Source tensor is compared to the native tensor through actual
sheafification/tensorator/counit maps, not a claimed tensor equality. -/
def tensorIso (M N : X.Modules) : STensor M N ≅ M ⊗ N :=
  letI := _root_.SheafOfModules.isMonoidal_W X.sheaf
  (ZInQ.Contrib.CloudW03NeronSurj.FLT.AlgebraicGeometry.Scheme.Modules.tensorIsoSheafify M N).symm ≪≫
    sheafificationComparison X (M.val ⊗ N.val) ≪≫
    (_root_.SheafOfModules.tensorObjIsoSheafification (R := X.sheaf) M N).symm

/-- The two units are identified through the actual structure-module object. -/
def zeroIso (M : X.Modules) : SPow M 0 ≅ M.tensorPow 0 :=
  eqToIso (show SPow M 0 = _root_.SheafOfModules.unit X.ringCatSheaf from
    ZInQ.Contrib.CloudW03NeronSurj.FLT.AlgebraicGeometry.Scheme.Modules.tensorUnit_eq (X := X)) ≪≫
    (eqToIso (show M.tensorPow 0 = _root_.SheafOfModules.unit X.ringCatSheaf from rfl)).symm

/-- Literal right-recursive Source powers versus left-recursive W07 powers.
At each successor, use the actual tensor comparison, the preceding power
isomorphism and the native braiding. No raw alias is assumed, even for lines. -/
def iso (M : X.Modules) : (n : ℕ) → SPow M n ≅ M.tensorPow n
  | 0 => zeroIso M
  | n + 1 => tensorIso (SPow M n) M ≪≫
      (iso M n ⊗ᵢ Iso.refl M) ≪≫ (β_ (M.tensorPow n) M)

/-- The successor isomorphism is the prescribed actual map construction. -/
theorem iso_succ (M : X.Modules) (n : ℕ) :
    iso M (n + 1) = tensorIso (SPow M n) M ≪≫
      (iso M n ⊗ᵢ Iso.refl M) ≪≫ (β_ (M.tensorPow n) M) := rfl

/-- Map on literal Source power objects through the fixed comparison.
It is built from the original morphism; it does not choose new line data. -/
def map {M N : X.Modules} (f : M ⟶ N) (n : ℕ) :
    SPow M n ⟶ SPow N n :=
  (iso M n).hom ≫ NativePower.map f n ≫ (iso N n).inv

@[simp]
theorem map_id (M : X.Modules) (n : ℕ) : map (𝟙 M) n = 𝟙 (SPow M n) := by
  simp only [map, NativePower.map_id, Category.id_comp, Iso.hom_inv_id]

@[simp]
theorem map_comp {M N P : X.Modules} (f : M ⟶ N) (g : N ⟶ P) (n : ℕ) :
    map (f ≫ g) n = map f n ≫ map g n := by
  simp only [map, NativePower.map_comp, Category.assoc, Iso.inv_hom_id_assoc]

/-- A genuine functor on the literal Source power objects. -/
def functor (n : ℕ) : X.Modules ⥤ X.Modules where
  obj M := SPow M n
  map f := map f n
  map_id M := map_id M n
  map_comp f g := map_comp f g n

/-- Canonical Source power of the original isomorphism. The actual body of
this constructor is held in the recovered GradedOAlgebraSectionRing Source;
it is not replaced by the conjugated native functor above. -/
def mapIso {M N : X.Modules} (e : M ≅ N) (n : ℕ) :
    SPow M n ≅ SPow N n :=
  ZInQ.Contrib.CloudW03NeronSurj.FLT.AlgebraicGeometry.Scheme.Modules.tensorPowMapIso e n

/-- Canonical Source monoidal pullback/power comparison. This actual Source
constructor (unit comparison, then tensorator and recursion) is held as
READ text; its separate default-limit binding is not asserted here. -/
def pullbackIso {Y : Scheme.{u}} (f : X ⟶ Y) (M : Y.Modules) (n : ℕ) :
    (Scheme.Modules.pullback f).obj (SPow M n) ≅
      SPow ((Scheme.Modules.pullback f).obj M) n :=
  ZInQ.Contrib.CloudW03NeronSurj.FLT.AlgebraicGeometry.Scheme.Modules.pullbackTensorPowIso f M n

/-- The original beta yields its Source power on the SAME maps and modules. -/
def betaPow {U A : Scheme.{u}} (i : U ⟶ X) (q : U ⟶ A)
    (M : X.Modules) (L : A.Modules)
    (beta : (Scheme.Modules.pullback i).obj M ≅
      (Scheme.Modules.pullback q).obj L) (n : ℕ) :
    (Scheme.Modules.pullback i).obj (SPow M n) ≅
      (Scheme.Modules.pullback q).obj (SPow L n) :=
  pullbackIso i M n ≪≫ mapIso beta n ≪≫ (pullbackIso q L n).symm

/-- Generic stage form: q lands in the original generic-open group, whose
line is r^*L0. Set L0' = SPow L0 n on the SAME original A, and compare beta^n
with q^*r^*L0'. These are actual functorial maps, not a new L0 or a Fact. -/
def originalBetaPow {U V A : Scheme.{u}} (i : U ⟶ X) (q : U ⟶ V) (r : V ⟶ A)
    (M : X.Modules) (L0 : A.Modules)
    (beta : (Scheme.Modules.pullback i).obj M ≅
      (Scheme.Modules.pullback q).obj ((Scheme.Modules.pullback r).obj L0)) (n : ℕ) :
    (Scheme.Modules.pullback i).obj (SPow M n) ≅
      (Scheme.Modules.pullback q).obj
        ((Scheme.Modules.pullback r).obj (SPow L0 n)) :=
  betaPow i q M ((Scheme.Modules.pullback r).obj L0) beta n ≪≫
    (Scheme.Modules.pullback q).mapIso (pullbackIso r L0 n).symm

/-- Native invertibility is transported along the actual power comparison;
this does not itself assert the Source invertibility predicate equivalence. -/
theorem nativeInvertible (M : X.Modules) [M.IsInvertible] (n : ℕ) :
    (SPow M n).IsInvertible := by
  letI : (M.tensorPow n).IsInvertible := NativePower.invertible M n
  refine (Scheme.Modules.isInvertible_iff_forall_exists_pullback_unit _).2 ?_
  intro x
  obtain ⟨U, hx, ⟨e⟩⟩ :=
    (_root_.SheafOfModules.IsInvertible.exists_isoUnit
      (inferInstance : (M.tensorPow n).IsInvertible) x)
  exact ⟨U, hx, ⟨(Scheme.Modules.pullback U.ι).mapIso (iso M n) ≪≫ e⟩⟩

end H5OriginalDVR.Lane5.GM12.SourcePower
