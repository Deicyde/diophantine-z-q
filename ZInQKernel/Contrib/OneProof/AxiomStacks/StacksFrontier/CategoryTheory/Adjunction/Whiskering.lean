module

public import Mathlib.Algebra.Category.Grp.Adjunctions
public import Mathlib.CategoryTheory.Adjunction.Limits
public import Mathlib.CategoryTheory.Adjunction.Whiskering
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
import Mathlib.Tactic.CrossRefAttribute

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3

/-!
# Free abelian presheaves

The free abelian presheaf `Z_G = G ⋙ AddCommGrpCat.free` and its adjunction with the forgetful
functor `PAb(C) ⥤ PSh(C)` are `AddCommGrpCat.adj.whiskerRight Cᵒᵖ`.
-/

@[expose] public section

-- Tag 03A8: `Mor(h_U, F) = F(U)`, `Mor(Z_G, A) = Mor(G, A)`, and their composite
-- `Mor(Z_U, A) = A(U)`, all natural.

-- Tag 03A9: `Z_(-)` is a left adjoint, so `⊕ Z_{G_i} → Z_{∐ G_i}` is an isomorphism.
