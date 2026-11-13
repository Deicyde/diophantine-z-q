import AxiomBridge.Points
import TateComparison

noncomputable section
open CategoryTheory AlgebraicGeometry Limits MonoidalCategory
open scoped MonObj

/-- A composed smoke-test datum, not a new free/rank or registered-provider claim. -/
def geometricTateEquiv {k : Type} [Field k] (A : PkgI3.AbVar k)
    (ℓ : ℕ) [Fact ℓ.Prime] : A.T ℓ ≃ₗ[ℤ_[ℓ]]
      Stacks.AbelianGroup.tateModule
        (Additive (𝟙_ (Over (Spec (CommRingCat.of (AlgebraicClosure k)))) ⟶
          (A.baseChange (AlgebraicClosure k)).X)) ℓ :=
  AxiomBridge.TateComparison.ofPointEquiv ℓ
    (AxiomBridge.pointsBaseChangeMulEquiv A (AlgebraicClosure k)).toAdditive

example {k : Type} [Field k] (A : PkgI3.AbVar k) (ℓ : ℕ) [Fact ℓ.Prime]
    (x : A.T ℓ) (n : ℕ) :
    (geometricTateEquiv A ℓ x).1 n = Additive.ofMul
      (AxiomBridge.pointsBaseChangeMulEquiv A (AlgebraicClosure k) (x.1 n).toMul) := rfl

def baseChangedHom {k : Type} [Field k] (A B : PkgI3.AbVar k)
    (φ : PkgI3.AbVar.Hom A B) :
    PkgI2.baseChange (ObjBridge.toGrp A) (AlgebraicClosure k) ⟶
      PkgI2.baseChange (ObjBridge.toGrp B) (AlgebraicClosure k) :=
  (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap k (AlgebraicClosure k))))).mapGrp.map
    (ObjBridge.grpOfHom φ)

example {k : Type} [Field k] (A B : PkgI3.AbVar k) (ℓ : ℕ) [Fact ℓ.Prime]
    (φ : PkgI3.AbVar.Hom A B) (x : A.T ℓ) :
    geometricTateEquiv B ℓ (PkgI3.AbVar.homT φ x) =
      Stacks.AbelianGroup.tateModuleMap ℓ
        (IsMonHom.monoidHom (baseChangedHom A B φ).hom.hom
          (𝟙_ (Over (Spec (CommRingCat.of (AlgebraicClosure k)))))).toAdditive
        (geometricTateEquiv A ℓ x) := by
  apply AxiomBridge.TateComparison.ofPointEquiv_natural
  intro y
  exact congrArg Additive.ofMul
    (AxiomBridge.pointsBaseChangeMulEquiv_ptMap A (AlgebraicClosure k) φ y.toMul)

#print axioms geometricTateEquiv
