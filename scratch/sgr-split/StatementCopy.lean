import ZInQKernel.OneProof.H.TailW

/-! sgr-split: verbatim copy of `HDec.CurveSplitGR.IsShimuraModelNoGuard` and
`HDec.CurveSplitGR.ShimuraGoodReductionNoGuard` (`ZInQKernel/OneProof/H/TailW.lean` lines 713-742), in the
namespace `HDec.SGRCopy`, checked definitionally equal to the chain's. -/

noncomputable section

namespace HDec

namespace SGRCopy

open CategoryTheory AlgebraicGeometry Limits LeafQM.AV VertWitness

/-- `IsShimuraModel` without its last clause (the `ℚ̄`-point guard). -/
def IsShimuraModelNoGuard (p : ℕ) [Fact p.Prime] (𝒴 : Over (Spec (CommRingCat.of (Zloc p))))
    (𝒜 : QMFamily 𝒴.left) : Prop :=
    IsProper 𝒴.hom ∧ SmoothOfRelativeDimension 1 𝒴.hom ∧
    (∀ (K : Type) [Field K] [Algebra ℚ K] (y : Spec (CommRingCat.of K) ⟶ 𝒴.left),
      ∃ P : QML3 K, IsFibreOf 𝒜 y P) ∧
    (∀ (y y' : Spec (CommRingCat.of Qbar) ⟶ 𝒴.left) (P P' : QML3 Qbar),
      IsFibreOf 𝒜 y P → IsFibreOf 𝒜 y' P' → M3.mk P = M3.mk P' → y = y') ∧
    (∀ P : QML3 Qbar, ∃ y : Spec (CommRingCat.of Qbar) ⟶ 𝒴.left, IsFibreOf 𝒜 y P) ∧
    (∀ α : LeafQM.O ≃+* LeafQM.O, ∃ g : 𝒴 ≅ 𝒴, ∀ (y : Spec (CommRingCat.of Qbar) ⟶ 𝒴.left) (P P' : QML3 Qbar),
      IsFibreOf 𝒜 y P → IsFibreOf 𝒜 (y ≫ g.hom.left) P' → M3.mk P' = M3.twist α (M3.mk P)) ∧
    (∀ u : (LeafQM.O)ˣ, ∃ g : 𝒴 ≅ 𝒴, ∀ (y : Spec (CommRingCat.of Qbar) ⟶ 𝒴.left) (P P' : QML3 Qbar),
      IsFibreOf 𝒜 y P → IsFibreOf 𝒜 (y ≫ g.hom.left) P' → M3.mk P' = M3.rightMul u (M3.mk P))

/-- `ShimuraGoodReduction` without the guard clause. -/
def ShimuraGoodReductionNoGuard : Prop :=
  ∀ (p : ℕ) [Fact p.Prime], 324 < p →
    ∃ (𝒴 : Over (Spec (CommRingCat.of (Zloc p)))) (𝒜 : QMFamily 𝒴.left), IsShimuraModelNoGuard p 𝒴 𝒜

example : SGRCopy.ShimuraGoodReductionNoGuard ↔ CurveSplitGR.ShimuraGoodReductionNoGuard := Iff.rfl

end SGRCopy

end HDec
