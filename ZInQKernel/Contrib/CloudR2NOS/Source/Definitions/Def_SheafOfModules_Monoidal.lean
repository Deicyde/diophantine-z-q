/-
NEW H5 FIX EDITION 2 — 2026-11-17, explicit generic target dictionary.
The previous d5545bb501af39b4981267e34a8c27bf5747806e29a1cec6b4b900785c6c53d8
edition remains frozen history. Parent's sheafmono-probe-001 elaborated all three
Scheme.Modules Source dictionary specializations; only the generic target lookup
in the scheme sheafification Monoidal instance failed (old line168).

Only two scheme-specialization proof bodies change beyond this header. Each now
installs, locally at the literal generic SheafOfModules (ringSheaf X.sheaf.obj
X.ringCatSheaf.property) type, the EXACT existing Source Scheme.Modules.monoidalCategory X.
The functor proof applies the EXISTING fully-qualified Source sheafifyFunctor_monoidal;
the tensor comparison applies the EXISTING Source tensorIsoSheafify on the SAME L/M.
Every generic constructor, public written type, import, universe, old option,
unit and tensor construction is unchanged. No W07 dictionary is substituted.
No new hypothesis/equality/alias/Fact, Type0 restriction or numeric/root/budget change.
SOURCE ONLY, UNCOMPILED. This candidate still needs Parent's immediate probe and
C6 review; it does not assert integrated Source/native F25 or NOS acceptance.
-/
/-
NEW H5 FIX EDITION — 2026-11-17, explicit Source monoidal specialization.
Supersedes the owned non-V2 Source edition62301cb7381c9972b891bc4c7c77b88d61842f32d661deb70d47001bb94b3700;
that historical file and Parent stages remain unchanged.

The generic prefixed Source sheaf monoidal/symmetric/closed constructors are
unchanged. Only the three Scheme.Modules specialization bodies now apply those
EXACT named constructors explicitly, at X.sheaf.obj and X.ringCatSheaf.property,
instead of asking instance search to recover them through the category-copy alias.
This follows the named-specialization pattern visible in W07 Modules/Tensor,
but does NOT import or substitute W07's different monoidal dictionary.

Every public definition/type, sheafify/unit/tensor construction, proof outside
those specialization bodies, import, universe and existing option is unchanged.
The existing tensorUnit_eq and tensorIsoSheafify are retained as real probe checks.
No new equality/alias/Fact, final hypothesis, Type0 narrowing, budget or option raise.
SOURCE ONLY, UNCOMPILED. Parent's immediate probe and C6 review are still required;
this candidate alone does not close F25 or Source/native dictionary coherence.
-/
/-
NEW SOURCE EDITION — actual non-V2 monoidal constructor binding for GM12.
Not historical recovery and not Source/native expression or ABI identity.

Source: anthropics/fermats-last-theorem,
6e837e75355538c7f80bab5b956861e86c4eacc2,
Definitions/Def_SheafOfModules_Monoidal.lean.
Copyright 2026 Anthropic, PBC; Apache-2.0; original LICENSE/ATTRIBUTION kept.
Actual raw SHA846aba9acb77e2a5cf35ef0bc73a9d8ebbf59db446acf1d928a228efd4d89da0.

NOTICE OF MODIFICATION: only the documented namespace-prefix/import rewrite,
dual namespace/open shims and port-utility import are applied. All original
constructor/proof/binder/universe/instance/option text is unchanged. No numeric
budget is inserted. The historical18018a7d... is a comparison anchor, not a
source-body recipe. This NEW edition needs C6 review and later default-limit
elaboration separately; missing imports are NOT silently provided or fetched.
-/
import Mathlib
import ZInQKernel.Contrib.CloudR2NOS.Source.Definitions.Def_PresheafOfModules_InternalHom
import ZInQKernel.Contrib.CloudR2NOS.Source.Theorems.Thm_PresheafOfModules_isMonoidal_inverseImage_W_toPresheaf
import ZInQKernel.Contrib.CloudR2NOS.Source.PortUtilExt

namespace ZInQ.Contrib.CloudW03NeronSurj.FLT

open ZInQ.Contrib.CloudW03NeronSurj.FLT

set_option autoImplicit false

universe u

open CategoryTheory MonoidalCategory Limits
r2nos_open_dual "CategoryTheory MonoidalCategory Limits"

noncomputable section

namespace SheafOfModules
r2nos_namespace_dual

variable {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
  (𝒪 : Cᵒᵖ ⥤ CommRingCat.{u}) (h𝒪 : Presheaf.IsSheaf J (𝒪 ⋙ forget₂ CommRingCat RingCat))
  [J.WEqualsLocallyBijective AddCommGrpCat.{u}] [HasWeakSheafify J AddCommGrpCat.{u}]

abbrev ringSheaf : Sheaf J RingCat.{u} := ⟨𝒪 ⋙ forget₂ CommRingCat RingCat, h𝒪⟩

abbrev PMod := PresheafOfModules.{u} (𝒪 ⋙ forget₂ CommRingCat RingCat)

abbrev presheafW (J : GrothendieckTopology C) (𝒪 : Cᵒᵖ ⥤ CommRingCat.{u}) :
    MorphismProperty (PMod 𝒪) :=
  (J.W (A := AddCommGrpCat.{u})).inverseImage
    (PresheafOfModules.toPresheaf (𝒪 ⋙ forget₂ CommRingCat RingCat))

abbrev sheafifyFunctor : PMod 𝒪 ⥤ SheafOfModules.{u} (ringSheaf 𝒪 h𝒪) :=
  PresheafOfModules.sheafification (R := ringSheaf 𝒪 h𝒪) (𝟙 (𝒪 ⋙ forget₂ CommRingCat RingCat))

abbrev toPMod : SheafOfModules.{u} (ringSheaf 𝒪 h𝒪) ⥤ PMod 𝒪 :=
  SheafOfModules.forget (ringSheaf 𝒪 h𝒪) ⋙
    PresheafOfModules.restrictScalars (𝟙 (𝒪 ⋙ forget₂ CommRingCat RingCat))

abbrev sheafifyAdj : sheafifyFunctor 𝒪 h𝒪 ⊣ toPMod 𝒪 h𝒪 :=
  PresheafOfModules.sheafificationAdjunction (R := ringSheaf 𝒪 h𝒪)
    (𝟙 (𝒪 ⋙ forget₂ CommRingCat RingCat))

instance : (toPMod 𝒪 h𝒪).Faithful := (sheafifyAdj 𝒪 h𝒪).fullyFaithfulROfIsIsoCounit.faithful
instance : (toPMod 𝒪 h𝒪).Full := (sheafifyAdj 𝒪 h𝒪).fullyFaithfulROfIsIsoCounit.full

instance : (sheafifyFunctor 𝒪 h𝒪).IsLocalization (presheafW J 𝒪) := inferInstance

include h𝒪 in

theorem presheafW_isMonoidal : (presheafW J 𝒪).IsMonoidal :=
  PresheafOfModules.isMonoidal_inverseImage_W_toPresheaf 𝒪 (ringSheaf 𝒪 h𝒪) (𝟙 _)

def sheafifyCounitIso (M : SheafOfModules.{u} (ringSheaf 𝒪 h𝒪)) :
    (sheafifyFunctor 𝒪 h𝒪).obj ((toPMod 𝒪 h𝒪).obj M) ≅ M :=
  (asIso (sheafifyAdj 𝒪 h𝒪).counit).app M

variable [J.HasSheafCompose (forget₂ RingCat.{u} AddCommGrpCat.{u})]

set_option backward.isDefEq.respectTransparency false in

def sheafifyUnitIso : (sheafifyFunctor 𝒪 h𝒪).obj (𝟙_ (PMod 𝒪)) ≅
    (unit (ringSheaf 𝒪 h𝒪) : SheafOfModules.{u} (ringSheaf 𝒪 h𝒪)) :=
  sheafifyCounitIso 𝒪 h𝒪 (unit (ringSheaf 𝒪 h𝒪))

instance monoidalCategory : MonoidalCategory (SheafOfModules.{u} (ringSheaf 𝒪 h𝒪)) :=
  letI := presheafW_isMonoidal 𝒪 h𝒪
  inferInstanceAs (MonoidalCategory
    (LocalizedMonoidal (L := sheafifyFunctor 𝒪 h𝒪) (W := presheafW J 𝒪) (sheafifyUnitIso 𝒪 h𝒪)))

instance symmetricCategory : SymmetricCategory (SheafOfModules.{u} (ringSheaf 𝒪 h𝒪)) :=
  letI := presheafW_isMonoidal 𝒪 h𝒪
  inferInstanceAs (SymmetricCategory
    (LocalizedMonoidal (L := sheafifyFunctor 𝒪 h𝒪) (W := presheafW J 𝒪) (sheafifyUnitIso 𝒪 h𝒪)))

instance sheafifyFunctor_monoidal : (sheafifyFunctor 𝒪 h𝒪).Monoidal :=
  letI := presheafW_isMonoidal 𝒪 h𝒪
  inferInstanceAs (Localization.Monoidal.toMonoidalCategory
    (L := sheafifyFunctor 𝒪 h𝒪) (W := presheafW J 𝒪) (sheafifyUnitIso 𝒪 h𝒪)).Monoidal

@[simp] theorem tensorUnit_eq : 𝟙_ (SheafOfModules.{u} (ringSheaf 𝒪 h𝒪)) = unit _ := rfl

instance monoidalClosed : MonoidalClosed (SheafOfModules.{u} (ringSheaf 𝒪 h𝒪)) :=
  Monoidal.Reflective.monoidalClosed (sheafifyAdj 𝒪 h𝒪)

def tensorIsoSheafify (L M : SheafOfModules.{u} (ringSheaf 𝒪 h𝒪)) :
    (sheafifyFunctor 𝒪 h𝒪).obj (L.val ⊗ M.val) ≅ L ⊗ M :=
  (Functor.Monoidal.μIso (sheafifyFunctor 𝒪 h𝒪) L.val M.val).symm ≪≫
    (sheafifyCounitIso 𝒪 h𝒪 L ⊗ᵢ sheafifyCounitIso 𝒪 h𝒪 M)

end SheafOfModules

namespace AlgebraicGeometry
r2nos_namespace_dual

variable (X : Scheme.{u})

instance Scheme.PresheafOfModules.monoidalCategory : MonoidalCategory X.PresheafOfModules :=
  inferInstanceAs (MonoidalCategory (_root_.PresheafOfModules.{u} (X.sheaf.obj ⋙ forget₂ CommRingCat RingCat)))
instance Scheme.PresheafOfModules.symmetricCategory : SymmetricCategory X.PresheafOfModules :=
  inferInstanceAs (SymmetricCategory (_root_.PresheafOfModules.{u} (X.sheaf.obj ⋙ forget₂ CommRingCat RingCat)))
instance Scheme.PresheafOfModules.monoidalClosed : MonoidalClosed X.PresheafOfModules :=
  inferInstanceAs (MonoidalClosed (_root_.PresheafOfModules.{u} (X.sheaf.obj ⋙ forget₂ CommRingCat RingCat)))

instance Scheme.Modules.monoidalCategory : MonoidalCategory X.Modules :=
  _root_.ZInQ.Contrib.CloudW03NeronSurj.FLT.SheafOfModules.monoidalCategory
    X.sheaf.obj X.ringCatSheaf.property
instance Scheme.Modules.symmetricCategory : SymmetricCategory X.Modules :=
  _root_.ZInQ.Contrib.CloudW03NeronSurj.FLT.SheafOfModules.symmetricCategory
    X.sheaf.obj X.ringCatSheaf.property
instance Scheme.Modules.monoidalClosed : MonoidalClosed X.Modules :=
  _root_.ZInQ.Contrib.CloudW03NeronSurj.FLT.SheafOfModules.monoidalClosed
    X.sheaf.obj X.ringCatSheaf.property

variable {X}

abbrev Scheme.Modules.tensor (L M : X.Modules) : X.Modules := L ⊗ M

abbrev Scheme.Modules.dual (L : X.Modules) : X.Modules := (ihom L).obj (𝟙_ X.Modules)

@[simp] theorem Scheme.Modules.tensorUnit_eq :
    𝟙_ X.Modules = SheafOfModules.unit X.ringCatSheaf := rfl

variable (X) in

abbrev Scheme.Modules.sheafify : X.PresheafOfModules ⥤ X.Modules :=
  SheafOfModules.sheafifyFunctor X.sheaf.obj X.ringCatSheaf.property

instance : (Scheme.Modules.sheafify X).Monoidal :=
  letI : MonoidalCategory (SheafOfModules.{u}
      (SheafOfModules.ringSheaf X.sheaf.obj X.ringCatSheaf.property)) :=
    _root_.ZInQ.Contrib.CloudW03NeronSurj.FLT.AlgebraicGeometry.Scheme.Modules.monoidalCategory X
  _root_.ZInQ.Contrib.CloudW03NeronSurj.FLT.SheafOfModules.sheafifyFunctor_monoidal
    X.sheaf.obj X.ringCatSheaf.property

def Scheme.Modules.tensorIsoSheafify (L M : X.Modules) :
    (Scheme.Modules.sheafify X).obj (L.val ⊗ M.val) ≅ L ⊗ M :=
  letI : MonoidalCategory (SheafOfModules.{u}
      (SheafOfModules.ringSheaf X.sheaf.obj X.ringCatSheaf.property)) :=
    _root_.ZInQ.Contrib.CloudW03NeronSurj.FLT.AlgebraicGeometry.Scheme.Modules.monoidalCategory X
  _root_.ZInQ.Contrib.CloudW03NeronSurj.FLT.SheafOfModules.tensorIsoSheafify
    X.sheaf.obj X.ringCatSheaf.property L M

end AlgebraicGeometry

end

end ZInQ.Contrib.CloudW03NeronSurj.FLT
