import C10Frobenius
import StacksFrontier.AlgebraicGeometry.Picard.FrobeniusTorsion

set_option autoImplicit false

/-!
# Frobenius group endomorphisms over finite fields

Use the existing q-power geometric Frobenius, where q = #k = p^f. The exponent
comes from the actual finite base field; the p-power map alone is not assumed
to be k-linear. This is packaging, not the C10 reduction or Tate comparison.
-/

noncomputable section

open CategoryTheory AlgebraicGeometry Stacks.Frobenius

namespace C10Frobenius.FiniteField

universe u

variable {k : Type u} [Field k] [Fintype k] (p f : ℕ) [Fact p.Prime] [CharP k p]
  (hcard : Fintype.card k = p ^ f)

/-- The pinned q-power geometric Frobenius is natural for finite-field schemes. -/
theorem geometric_naturality {X Y : Over (Spec (.of k))} (g : X ⟶ Y) :
    geometricFrobenius X p f hcard ≫ g = g ≫ geometricFrobenius Y p f hcard := by
  apply Over.OverMorphism.ext
  change (geometricFrobenius X p f hcard).left ≫ g.left =
    g.left ≫ (geometricFrobenius Y p f hcard).left
  rw [geometricFrobenius_left, geometricFrobenius_left]
  exact absoluteFrobeniusPow_naturality g.left p _ _ f

/-- The existing finite-field geometric Frobenius, bundled without changing its maps. -/
def geometricNatTrans : 𝟭 (Over (Spec (.of k))) ⟶ 𝟭 (Over (Spec (.of k))) where
  app X := geometricFrobenius X p f hcard
  naturality {_ _} g := (geometric_naturality p f hcard g).symm

/-- Lift q-power Frobenius through upstream cartesian group-functor machinery. -/
def geometricGroupNatTrans :
    𝟭 (Grp (Over (Spec (.of k)))) ⟶ 𝟭 (Grp (Over (Spec (.of k)))) :=
  Functor.mapGrpIdIso.inv ≫ Functor.mapGrpNatTrans (geometricNatTrans p f hcard) ≫
    Functor.mapGrpIdIso.hom

/-- q-power Frobenius as an endomorphism of an actual group scheme over k. -/
def endomorphism (A : Grp (Over (Spec (.of k)))) : A ⟶ A :=
  (geometricGroupNatTrans p f hcard).app A

/-- The group adapter has exactly the upstream geometric-Frobenius map. -/
@[simp] theorem endomorphism_hom (A : Grp (Over (Spec (.of k)))) :
    (endomorphism p f hcard A).hom.hom = geometricFrobenius A.X p f hcard := by
  change 𝟙 A.X ≫ geometricFrobenius A.X p f hcard ≫ 𝟙 A.X = _
  simp

/-- q-power geometric Frobenius preserves the original group law over every finite field. -/
theorem isMonHom_geometricFrobenius (A : Grp (Over (Spec (.of k)))) :
    IsMonHom (geometricFrobenius A.X p f hcard) := by
  rw [← endomorphism_hom]
  infer_instance

/-- The actual group endomorphism is natural for morphisms over the same finite base. -/
theorem endomorphism_naturality {A B : Grp (Over (Spec (.of k)))} (g : A ⟶ B) :
    endomorphism p f hcard A ≫ g = g ≫ endomorphism p f hcard B :=
  ((geometricGroupNatTrans p f hcard).naturality g).symm

/-- On test-scheme points, q-power Frobenius is precomposition by the f-fold Frobenius. -/
theorem endomorphism_onPoints (A : Grp (Over (Spec (.of k))))
    {T : Over (Spec (.of k))} (x : T ⟶ A.X) :
    (x ≫ (endomorphism p f hcard A).hom.hom).left =
      absoluteFrobeniusPow T.left p (isInCharacteristic_of_over T) f ≫ x.left := by
  change x.left ≫ (endomorphism p f hcard A).hom.hom.left = _
  rw [endomorphism_hom, geometricFrobenius_left]
  exact (absoluteFrobeniusPow_naturality x.left p _ _ f).symm

/-- The packaged map raises global sections to the cardinality of the finite base field. -/
theorem endomorphism_appTop (A : Grp (Over (Spec (.of k)))) (s : Γ(A.X.left, ⊤)) :
    (endomorphism p f hcard A).hom.hom.left.appTop s = s ^ Fintype.card k := by
  rw [endomorphism_hom, geometricFrobenius_left, absoluteFrobeniusPow_appTop_apply, ← hcard]

end C10Frobenius.FiniteField
