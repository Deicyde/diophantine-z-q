import Mathlib.Algebra.Category.Grp.AB
import Mathlib.Algebra.Category.Grp.Ulift
import Mathlib.AlgebraicGeometry.Sites.Etale
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.HasExt
import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
import Mathlib.NumberTheory.Padics.RingHoms
import ZInQKernel.HDecomp.Objects

/-! The classical étale side of T10. The site and coefficient tower below are an
on-the-spot (c) encoding of classical étale cohomology. No comparison to pro-étale
cohomology and no semilinear naturality are assumed here. -/

open CategoryTheory AlgebraicGeometry Abelian Limits MonObj

namespace T10Milne86

noncomputable section

private abbrev J : GrothendieckTopology Scheme.{0} := Scheme.etaleTopology

local instance : EssentiallySmall.{1} Scheme.{0} :=
  EssentiallySmall.mk' (AsSmall.equiv : Scheme.{0} ≌ AsSmall.{1} Scheme.{0})

local instance : HasSheafify J Ab.{1} :=
  hasSheafifyEssentiallySmallSite J Ab.{1}

local instance : IsGrothendieckAbelian.{1} (Sheaf J Ab.{1}) :=
  Sheaf.isGrothendieckAbelian_of_essentiallySmall _ _

/-- Sheafified free abelian representable on the big étale site. Hom from this
sheaf is evaluation at `X`; Ext from it computes the derived sections at `X`. -/
private def sectionsSource : Scheme.{0} ⥤ Sheaf J Ab.{1} :=
  uliftYoneda.{1} ⋙ (Functor.whiskeringRight _ _ _).obj AddCommGrpCat.free ⋙
    presheafToSheaf J _

private abbrev constAb : Ab.{0} ⥤ Sheaf J Ab.{1} :=
  AddCommGrpCat.uliftFunctor.{1} ⋙ constantSheaf J Ab.{1}

local instance : (constantSheaf J Ab.{1}).Additive := by
  let := preservesBinaryBiproducts_of_preservesBinaryCoproducts (constantSheaf J Ab.{1})
  exact Functor.additive_of_preservesBinaryBiproducts _

private abbrev coeff (ℓ n : ℕ) := constAb.obj (AddCommGrpCat.of (ZMod (ℓ ^ n)))

/-- `H¹_et(X, ℤ/ℓⁿ)` as derived evaluation of the constant coefficient sheaf
on the big étale site, using the universe raised form of Mathlib's `Sheaf.H'`. -/
abbrev FiniteH1 (X : Scheme.{0}) (ℓ n : ℕ) : Type 1 :=
  Ext (sectionsSource.obj X) (coeff ℓ n) 1

private def changeCoeffs (X : Scheme.{0}) {ℓ m n : ℕ}
    (f : ZMod (ℓ ^ m) →+ ZMod (ℓ ^ n)) : FiniteH1 X ℓ m →+ FiniteH1 X ℓ n :=
  (Ext.mk₀ (constAb.map (AddCommGrpCat.ofHom f))).postcomp _ (add_zero 1)

private theorem changeCoeffs_comp (X : Scheme.{0}) {ℓ l m n : ℕ}
    (f : ZMod (ℓ ^ l) →+ ZMod (ℓ ^ m)) (g : ZMod (ℓ ^ m) →+ ZMod (ℓ ^ n))
    (x : FiniteH1 X ℓ l) :
    changeCoeffs X g (changeCoeffs X f x) = changeCoeffs X (g.comp f) x := by
  unfold changeCoeffs
  change (x.comp (Ext.mk₀ (constAb.map (AddCommGrpCat.ofHom f))) (add_zero 1)).comp
      (Ext.mk₀ (constAb.map (AddCommGrpCat.ofHom g))) (add_zero 1) = _
  rw [Ext.comp_assoc_of_third_deg_zero, Ext.mk₀_comp_mk₀, ← Functor.map_comp]
  rfl

private def scalar (X : Scheme.{0}) (ℓ n : ℕ) [Fact ℓ.Prime] (a : ℤ_[ℓ]) :
    FiniteH1 X ℓ n →+ FiniteH1 X ℓ n :=
  changeCoeffs X (AddMonoidHom.mulLeft (PadicInt.toZModPow n a))

instance (X : Scheme.{0}) (ℓ n : ℕ) [Fact ℓ.Prime] : Module ℤ_[ℓ] (FiniteH1 X ℓ n) where
  smul a x := scalar X ℓ n a x
  one_smul x := by
    change scalar X ℓ n 1 x = x
    simp only [scalar, map_one, show AddMonoidHom.mulLeft (1 : ZMod (ℓ ^ n)) =
      AddMonoidHom.id _ from AddMonoidHom.ext (one_mul ·)]
    change x.comp (Ext.mk₀ (constAb.map (𝟙 (AddCommGrpCat.of (ZMod (ℓ ^ n))))))
      (add_zero 1) = x
    rw [CategoryTheory.Functor.map_id, Ext.comp_mk₀_id]
  mul_smul a b x := by
    change scalar X ℓ n (a * b) x = scalar X ℓ n a (scalar X ℓ n b x)
    simp only [scalar, map_mul, changeCoeffs_comp]
    apply congrArg (fun f : ZMod (ℓ ^ n) →+ ZMod (ℓ ^ n) => changeCoeffs X f x)
    ext t
    exact mul_assoc _ _ _
  smul_zero a := map_zero (scalar X ℓ n a)
  smul_add a x y := map_add (scalar X ℓ n a) x y
  add_smul a b x := by
    change scalar X ℓ n (a + b) x = scalar X ℓ n a x + scalar X ℓ n b x
    have h (s t : ZMod (ℓ ^ n)) : AddMonoidHom.mulLeft (s + t) =
        AddMonoidHom.mulLeft s + AddMonoidHom.mulLeft t := AddMonoidHom.ext (add_mul s t)
    simp only [scalar, map_add, h]
    let f := AddCommGrpCat.ofHom (AddMonoidHom.mulLeft (PadicInt.toZModPow n a))
    let g := AddCommGrpCat.ofHom (AddMonoidHom.mulLeft (PadicInt.toZModPow n b))
    change x.comp (Ext.mk₀ (constAb.map (f + g))) (add_zero 1) = _
    rw [Functor.map_add, Ext.mk₀_add, Ext.comp_add]
    rfl
  zero_smul x := by
    change scalar X ℓ n 0 x = 0
    simp only [scalar, map_zero, show AddMonoidHom.mulLeft (0 : ZMod (ℓ ^ n)) = 0 from
      AddMonoidHom.ext (zero_mul ·)]
    change x.comp (Ext.mk₀ (constAb.map (0 : AddCommGrpCat.of (ZMod (ℓ ^ n)) ⟶ _)))
      (add_zero 1) = 0
    rw [Functor.map_zero, Ext.mk₀_zero, Ext.comp_zero]

private def reduce (ℓ n : ℕ) : ZMod (ℓ ^ (n + 1)) →+* ZMod (ℓ ^ n) :=
  ZMod.castHom (pow_dvd_pow ℓ (Nat.le_succ n)) _

private def transition (X : Scheme.{0}) (ℓ n : ℕ) [Fact ℓ.Prime] :
    FiniteH1 X ℓ (n + 1) →ₗ[ℤ_[ℓ]] FiniteH1 X ℓ n where
  __ := changeCoeffs X (reduce ℓ n).toAddMonoidHom
  map_smul' a x := by
    change changeCoeffs X (reduce ℓ n).toAddMonoidHom (scalar X ℓ (n + 1) a x) =
      scalar X ℓ n a (changeCoeffs X (reduce ℓ n).toAddMonoidHom x)
    simp only [scalar, changeCoeffs_comp]
    apply congrArg (fun f : ZMod (ℓ ^ (n + 1)) →+ ZMod (ℓ ^ n) => changeCoeffs X f x)
    ext t
    change reduce ℓ n (PadicInt.toZModPow (n + 1) a * t) =
      PadicInt.toZModPow n a * reduce ℓ n t
    rw [map_mul]
    congr 1
    exact PadicInt.cast_toZModPow n (n + 1) (Nat.le_succ n) a

/-- Classical `H¹_et(X, ℤ_ℓ)`: the inverse limit under coefficient reduction. -/
def EtaleH1 (X : Scheme.{0}) (ℓ : ℕ) [Fact ℓ.Prime] :
    Submodule ℤ_[ℓ] (∀ n, FiniteH1 X ℓ n) where
  carrier := {x | ∀ n, transition X ℓ n (x (n + 1)) = x n}
  zero_mem' n := map_zero (transition X ℓ n)
  add_mem' hx hy n := by simp [hx n, hy n]
  smul_mem' a x hx n := by simp [hx n]

private def finitePull {X Y : Scheme.{0}} (f : X ⟶ Y) (ℓ n : ℕ) :
    FiniteH1 Y ℓ n →+ FiniteH1 X ℓ n :=
  (Ext.mk₀ (sectionsSource.map f)).precomp _ (zero_add 1)

private theorem finitePull_changeCoeffs {X Y : Scheme.{0}} (f : X ⟶ Y) {ℓ m n : ℕ}
    (g : ZMod (ℓ ^ m) →+ ZMod (ℓ ^ n)) (x : FiniteH1 Y ℓ m) :
    finitePull f ℓ n (changeCoeffs Y g x) = changeCoeffs X g (finitePull f ℓ m x) :=
  (Ext.comp_assoc_of_third_deg_zero _ _ _ (zero_add 1)).symm

/-- The pullback on classical degree-one cohomology induced by a scheme map. -/
def etalePull {X Y : Scheme.{0}} (f : X ⟶ Y) (ℓ : ℕ) [Fact ℓ.Prime] :
    EtaleH1 Y ℓ →ₗ[ℤ_[ℓ]] EtaleH1 X ℓ where
  toFun x := ⟨fun n => finitePull f ℓ n (x.1 n), fun n => by
    change changeCoeffs X (reduce ℓ n).toAddMonoidHom (finitePull f ℓ (n + 1) (x.1 (n + 1))) = _
    rw [← finitePull_changeCoeffs]
    exact congrArg (finitePull f ℓ n) (x.2 n)⟩
  map_add' _ _ := Subtype.ext (funext fun n => map_add (finitePull f ℓ n) _ _)
  map_smul' a x := Subtype.ext (funext fun n =>
    finitePull_changeCoeffs f (AddMonoidHom.mulLeft (PadicInt.toZModPow n a)) (x.1 n))

open PkgI3

private def geometricMap {K : Type} [Field K] {A B : AbVar K} (f : AbVar.Hom A B) :
    (A.baseChange (AlgebraicClosure K)).X.left ⟶ (B.baseChange (AlgebraicClosure K)).X.left :=
  ((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap K (AlgebraicClosure K))))).map f.hom).left

/-- J. S. Milne, *Abelian varieties*, in Cornell–Silverman (eds.), *Arithmetic
Geometry* (Springer, 1986), Theorem 15.1(a) (locator and wording UNVERIFIED).
Degree one: for a prime invertible in the base field, the classical geometric
étale cohomology is the linear dual of the Tate module, naturally in the
abelian variety. The naturality clause here is for homomorphisms over `K`.
It makes no assertion about semilinear maps or pro-étale cohomology. -/
def Milne86Thm15_1a : Prop :=
  ∀ (K : Type) [Field K] (ℓ : ℕ) [Fact ℓ.Prime], (ℓ : K) ≠ 0 →
    ∃ φ : ∀ A : AbVar K, EtaleH1 (A.baseChange (AlgebraicClosure K)).X.left ℓ ≃ₗ[ℤ_[ℓ]]
        Module.Dual ℤ_[ℓ] (A.T ℓ),
      ∀ {A B : AbVar K} (f : AbVar.Hom A B)
        (x : EtaleH1 (B.baseChange (AlgebraicClosure K)).X.left ℓ),
        φ A (etalePull (geometricMap f) ℓ x) = (AbVar.homT f).dualMap (φ B x)

end

end T10Milne86

#print axioms T10Milne86.etalePull
#print axioms T10Milne86.changeCoeffs_comp
#print axioms T10Milne86.finitePull_changeCoeffs
#print axioms T10Milne86.Milne86Thm15_1a
