import ZInQKernel.Contrib.CloudB3W13.Dictionary.D5.KernelGroup
import ZInQKernel.Contrib.CloudB3W13.Dictionary.D5.FiniteLevel
import ZInQKernel.Contrib.OneProof.ShimuraGoodReductionNoGuard

/-!
# D5: unchanged level points at every geometric field

Original dictionary proof, 2026-11-16, W13 D5 with Metamate/agentcloud assistance.
The geometric level map is precomposition of the supplied kernel `eta`.
Faithfulness is proved by the epimorphism of field spectra, not assumed as
an extra geometric-level condition. All types here are existing kernel types.
-/

set_option backward.isDefEq.respectTransparency.types true
set_option backward.isDefEq.respectTransparency.instanceSearchTypes true

noncomputable section

namespace ZInQ.Contrib.CloudB2Shimura.Dictionary.D5

open CategoryTheory AlgebraicGeometry
open MonoidalCategory CartesianMonoidalCategory MonObj
open PkgI3 LeafQM

variable {K k : Type} [Field K] [Field k]

/-- The field map, as a morphism into the kernel's rational-point object. -/
def geometricToK (s : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of K)) :
    Over.mk s ⟶ AbVar.ptObj (K := K) K :=
  Over.homMk s (by
    rw [kernelPtObj_self]
    dsimp only [AbVar.ptObj, Over.mk_left, Over.mk_hom]
    exact Category.comp_id s)

/-- Precomposition on the actual original group of points. -/
def geometricPointsMap (A : AbVar K)
    (s : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of K)) :
    A.Pt K →* (Over.mk s ⟶ A.X) where
  toFun x := geometricToK s ≫ x
  map_one' := MonObj.comp_one _
  map_mul' x y := MonObj.comp_mul _ _ _

@[simp] theorem geometricPointsMap_left (A : AbVar K)
    (s : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of K)) (x : A.Pt K) :
    (geometricPointsMap A s x).left = s ≫ x.left := rfl

/-- Base change of rational points to a geometric field preserves actual equality. -/
theorem geometricPointsMap_injective (A : AbVar K)
    (s : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of K)) :
    Function.Injective (geometricPointsMap A s) := by
  haveI : Epi s := SGRSplit.epi_spec_field s
  intro x y h
  apply Over.OverMorphism.ext
  apply (cancel_epi s).mp
  exact congrArg CommaMorphism.left h

/-- The supplied level structure, base-changed by the supplied field map. -/
def geometricEta (P : AV.QML3 K)
    (s : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of K)) :
    O →+ Additive (Over.mk s ⟶ P.A.X) :=
  (geometricPointsMap P.A s).toAdditive.comp P.e.eta

@[simp] theorem geometricEta_left (P : AV.QML3 K)
    (s : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of K)) (a : O) :
    (Additive.toMul (geometricEta P s a)).left =
      s ≫ (Additive.toMul (P.e.eta a)).left := rfl

/-- The original kernel remains exactly `3𝒪` over every geometric field. -/
theorem geometricEta_ker (P : AV.QML3 K)
    (s : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of K)) (a : O) :
    geometricEta P s a = 0 ↔ ∃ b : O, a = 3 * b := by
  rw [← P.e.ker]
  change (geometricPointsMap P.A s).toAdditive (P.e.eta a) = 0 ↔ P.e.eta a = 0
  constructor
  · intro h
    have hinj : Function.Injective (geometricPointsMap P.A s).toAdditive := by
      intro x y hxy
      apply Additive.toMul.injective
      apply geometricPointsMap_injective P.A s
      exact congrArg Additive.toMul hxy
    apply hinj
    simpa only [map_zero] using h
  · intro h
    rw [h, map_zero]

/-- Geometric generation from the count of the genuine geometric torsion group. -/
theorem geometricEta_surjective (P : AV.QML3 K)
    (s : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of K))
    (hcard : Nat.card {x : Additive (Over.mk s ⟶ P.A.X) // (3 : ℕ) • x = 0} = 81)
    (x : Additive (Over.mk s ⟶ P.A.X)) (hx : (3 : ℕ) • x = 0) :
    ∃ a : O, geometricEta P s a = x :=
  eta_surjective_of_torsion_card (geometricEta P s) (geometricEta_ker P s) hcard x hx

end ZInQ.Contrib.CloudB2Shimura.Dictionary.D5
