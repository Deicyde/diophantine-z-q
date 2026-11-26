module

public import Mathlib.Tactic.CrossRefAttribute
public import Mathlib.CategoryTheory.Sites.CoverLifting

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3

/-! # Composition of cocontinuous functors

## Main results

* Stacks 03L5, first half -- a composition of cocontinuous functors between sites is
  cocontinuous -- is `CategoryTheory.isCocontinuous_comp`, registered below.
* `ranOpCompIso`: the presheaf-level isomorphism `(u.op ⋙ v.op).ran ≅ u.op.ran ⋙ v.op.ran`.
* `sheafPushforwardCocontinuousCompIso`: the direct image functor of the morphism of topoi
  attached to `u ⋙ v` is isomorphic to the composition of those attached to `u` and to `v`
  (Stacks 03L5, second half).

Tags covered: 03L5.
-/

@[expose] public section

open CategoryTheory

universe u

variable {C : Type u} [SmallCategory C]
variable {D : Type u} [SmallCategory D]
variable {E : Type u} [SmallCategory E]
variable (J : GrothendieckTopology C) (K : GrothendieckTopology D)
    (L : GrothendieckTopology E)


/-- The presheaf-level natural isomorphism `(u.op ⋙ v.op).ran ≅ u.op.ran ⋙ v.op.ran`, obtained
from uniqueness of right adjoints applied to the right Kan extension adjunctions. -/
noncomputable irreducible_def ranOpCompIso (u : C ⥤ D) (v : D ⥤ E) :
    (u.op ⋙ v.op).ran (H := Type u) ≅ u.op.ran ⋙ v.op.ran :=
  Adjunction.rightAdjointUniq
    (Functor.ranAdjunction (u.op ⋙ v.op) (Type u))
    ((Functor.ranAdjunction v.op (Type u)).comp (Functor.ranAdjunction u.op (Type u)))

/-- **Stacks 03L5**, second half. The canonical natural isomorphism between the direct image
functor of the morphism of topoi attached to `u ⋙ v` and the composition of the direct image
functors attached to `u` and to `v`. -/
@[stacks 03L5 "(2)"]
noncomputable def sheafPushforwardCocontinuousCompIso (u : C ⥤ D) (v : D ⥤ E)
    [u.IsCocontinuous J K] [v.IsCocontinuous K L] :
    haveI : (u ⋙ v).IsCocontinuous J L := CategoryTheory.isCocontinuous_comp u v J K
    (u ⋙ v).sheafPushforwardCocontinuous (Type u) J L ≅
      u.sheafPushforwardCocontinuous (Type u) J K ⋙
        v.sheafPushforwardCocontinuous (Type u) K L :=
  haveI : (u ⋙ v).IsCocontinuous J L := CategoryTheory.isCocontinuous_comp u v J K
  Functor.fullyFaithfulCancelRight (sheafToPresheaf L (Type u))
    (Functor.isoWhiskerLeft (sheafToPresheaf J (Type u)) (ranOpCompIso u v))
