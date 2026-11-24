import ZInQKernel.Contrib.CloudR2CM.SerreTate.NOSAdapter
import ZInQKernel.Contrib.OneProof.MumfordGroupLawNeron

/-!
# Proper global group models from good reduction at every finite place

Statements only. The Dedekind Néron-existence input is used unchanged.
Good reduction is the project predicate for an actual abelian group scheme
with its group-compatible generic identification. The conclusion retains
the original variety and its actual global group model, with properness
as an additional conclusion rather than as a model-construction field.
-/

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry

namespace HDec.CMSerreTate

/-- The P4 obligation. A Néron model obtained from the unchanged Dedekind
existence input, together with good reduction at every finite place of the
extension field, gives the proper global group model required by CM
potential good reduction. -/
def P4ProperModel : Prop :=
  _root_.ZInQ.Contrib.GroupLawNeron.NeronSchemeExtensionDedekind →
  ∀ (L : Type) [Field L] [NumberField L] (E : _root_.ZInQ.DefFaltings.AbVar L)
    (L₁ : Type) [Field L₁] [NumberField L₁] [Algebra L L₁],
    GoodAtFinitePlaces ((HDec.LeafAdopt.abVarEquiv L E).baseChange L₁) →
    ∃ 𝒢 : _root_.ZInQ.DefFaltings.GroupModel E L₁, IsProper 𝒢.G.hom

end HDec.CMSerreTate
