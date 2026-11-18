import ZInQKernel.Contrib.CloudR2Poincare.L3.NativeLerayOne
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
# The actual low-degree Leray sequence as a field-linear dimension bound

Both arrows are the already-certified canonical native maps. Their field
linearity follows from their proved global-function scalar laws and the
actual equality of compatible structure maps, not from an AddEquiv or rank.
-/

noncomputable section
open CategoryTheory AlgebraicGeometry Limits

namespace ZInQ.Contrib.CloudR2Poincare.L3.HOneRank

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
variable {k : Type u} [Field k] {P X : Scheme.{u}}
    [P.Over (Spec (.of k))] [X.Over (Spec (.of k))]

/-- Compatibility of the native field actions for an actual morphism over k. -/
theorem globalSectionsFieldAction_comp (p : P ⟶ X) [p.IsOver (Spec (.of k))] (c : k) :
    p.appTop (Scheme.globalSectionsRingHom k (X := X) c) =
      Scheme.globalSectionsRingHom k (X := P) c := by
  have hp : p ≫ (X ↘ Spec (.of k)) = (P ↘ Spec (.of k)) :=
    (Scheme.Hom.isOver_iff (Spec (.of k))).mp inferInstance
  change p.appTop (((Scheme.ΓSpecIso (.of k)).inv ≫
      (X ↘ Spec (.of k)).appTop) c) =
    (((Scheme.ΓSpecIso (.of k)).inv ≫ (P ↘ Spec (.of k)).appTop) c)
  rw [← hp, Scheme.Hom.comp_appTop]
  rfl

/-- The literal Ext-defined native inflation, as a k-linear map. -/
def inflationLinearMap (p : P ⟶ X) [p.IsOver (Spec (.of k))] (F : P.Modules) :
    ((Scheme.Modules.pushforward p).obj F).H 1 →ₗ[k] F.H 1 :=
  { Scheme.Modules.H.mapOfAdjunction p (𝟙 ((Scheme.Modules.pushforward p).obj F)) 1 with
    map_smul' := fun c z => by
      change Scheme.Modules.H.mapOfAdjunction p (𝟙 ((Scheme.Modules.pushforward p).obj F)) 1
          (Scheme.globalSectionsRingHom k (X := X) c • z) =
        Scheme.globalSectionsRingHom k (X := P) c •
          Scheme.Modules.H.mapOfAdjunction p (𝟙 ((Scheme.Modules.pushforward p).obj F)) 1 z
      rw [Scheme.Modules.H.mapOfAdjunction_smul, globalSectionsFieldAction_comp] }

/-- The same canonical native Leray edge, as a k-linear map. -/
def edgeLinearMap (p : P ⟶ X) [p.IsOver (Spec (.of k))] (F : P.Modules) :
    F.H 1 →ₗ[k] ((Scheme.Modules.higherDirectImage p 1).obj F).H 0 :=
  { nativeLerayOneEdge p F with
    map_smul' := fun c z => by
      change nativeLerayOneEdge p F (Scheme.globalSectionsRingHom k (X := P) c • z) =
        Scheme.globalSectionsRingHom k (X := X) c • nativeLerayOneEdge p F z
      rw [← globalSectionsFieldAction_comp p c, nativeLerayOneEdge_smul] }

/-- Rank-nullity for the actual canonical sequence, with its honest finiteness
inputs. The geometric product theorem discharges all three finiteness inputs. -/
theorem nativeLerayOne_finrank_le (p : P ⟶ X) [p.IsOver (Spec (.of k))] (F : P.Modules)
    [Module.Finite k (F.H 1)]
    [Module.Finite k (((Scheme.Modules.pushforward p).obj F).H 1)]
    [Module.Finite k (((Scheme.Modules.higherDirectImage p 1).obj F).H 0)] :
    Module.finrank k (F.H 1) ≤
      Module.finrank k (((Scheme.Modules.pushforward p).obj F).H 1) +
        Module.finrank k (((Scheme.Modules.higherDirectImage p 1).obj F).H 0) := by
  let α := inflationLinearMap (k := k) p F
  let β := edgeLinearMap (k := k) p F
  have hker : LinearMap.ker β = LinearMap.range α := by
    ext z
    exact SetLike.ext_iff.mp (nativeLerayOneExact p F).2.symm z
  have hα : Module.finrank k (LinearMap.range α) ≤
      Module.finrank k (((Scheme.Modules.pushforward p).obj F).H 1) :=
    LinearMap.finrank_range_le α
  have hβ : Module.finrank k (LinearMap.range β) ≤
      Module.finrank k (((Scheme.Modules.higherDirectImage p 1).obj F).H 0) :=
    (LinearMap.range β).finrank_le
  have hr := LinearMap.finrank_range_add_finrank_ker β
  rw [hker] at hr
  omega

end ZInQ.Contrib.CloudR2Poincare.L3.HOneRank
