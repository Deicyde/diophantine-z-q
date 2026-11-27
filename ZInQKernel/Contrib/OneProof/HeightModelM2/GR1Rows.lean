import ZInQKernel.Contrib.OneProof.HeightModelM.Rows
import ZInQKernel.Contrib.OneProof.HeightModelM2.Commutative
import ZInQKernel.Contrib.OneProof.HeightModelM2.GlobalDet

/-! # The GR1 rows with a commutative model and the global-sections lattice

`IsGR1StableHeightGlobal A x` is `IsGR1StableHeightOriginal A x` stated as GR1 §2.3 (p. 351)
states it, with the two readings of the fidelity record made literal:

* the model is a commutative semi-abelian model (`IsSemiAbelianModel 𝒜 ∧ IsCommMonObj 𝒜.G`);
* the lattice is the module of global sections of `ε*Ω^g` (`globalDetLattice`), in place of the
  stalk-built `printedDetLattice`.

`isGR1StableHeightGlobal_iff`: the two predicates are equivalent (`groupModel_isCommMonObj`,
`globalDetLattice_eq`). Hence the rows over the new predicate are equivalent to the current ones:
`gaudronRemondThm14GR1Global_iff`, `gaudronRemondSec9LowerGR1Global_iff` and
`gaudronRemondSec9LowerGR1WeakGlobal_iff`. -/

noncomputable section

open CategoryTheory AlgebraicGeometry Limits Topology MonObj
open ZInQ.DefFaltings ZInQ.HeightSplit ZInQ.HeightGlue ZInQ.HeightDict ZInQ.HeightFix
open ZInQ.R3Residual ZInQ.H5Glue ZInQ.SemistabAssembly CToPrinted ZInQ.GR14Printed
open ZInQ.HeightModelM
open scoped NumberField

namespace ZInQ.HeightModelM2

/-- **Gaudron–Rémond's stable height, original normalization, as GR1 §2.3 prints it**: `x = h_F(A)`
computed on a commutative semi-abelian group model `𝒜` of `A` over the ring of integers of a
number field `K'` over the base, with a nonzero global section `η` of `ε*Ω^g_{𝒜/𝒪_{K'}}`
(`globalDetLattice`) of finite index. -/
def IsGR1StableHeightGlobal {K : Type} [Field K] (A : PkgI3.AbVar K) (x : ℝ) : Prop :=
  ∃ (K' : Type) (_ : Field K') (_ : NumberField K') (_ : Algebra K K') (𝒜 : GroupModel A K')
    (g : ℕ), (IsSemiAbelianModel 𝒜 ∧ IsCommMonObj 𝒜.G) ∧ A.dim = (g : WithBot ℕ∞) ∧
    ∃ eta ∈ globalDetLattice 𝒜 g, eta ≠ 0 ∧ secIndex (globalDetLattice 𝒜 g) eta ≠ 0 ∧
      ∃ r : (K' →+* ℂ) → ℝ, (∀ τ, IsAnMetricSq 𝒜 τ eta (r τ)) ∧
        x = (Real.log (secIndex (globalDetLattice 𝒜 g) eta) -
          (1 / 2) * ∑ τ : K' →+* ℂ, Real.log (r τ)) / Module.finrank ℚ K'

/-- **The predicate as GR1 prints it is the tree's predicate.** -/
theorem isGR1StableHeightGlobal_iff {K : Type} [Field K] {A : PkgI3.AbVar K} {x : ℝ} :
    IsGR1StableHeightGlobal A x ↔ IsGR1StableHeightOriginal A x := by
  constructor
  · rintro ⟨K', iF, iN, iA, 𝒜, g, ⟨hsa, -⟩, hg, eta, heta, hne, hsec, r, hr, hx⟩
    rw [globalDetLattice_eq] at heta hsec hx
    exact ⟨K', iF, iN, iA, 𝒜, g, hsa, hg, eta, heta, hne, hsec, r, hr, hx⟩
  · rintro ⟨K', iF, iN, iA, 𝒜, g, hsa, hg, eta, heta, hne, hsec, r, hr, hx⟩
    rw [← globalDetLattice_eq] at heta hsec hx
    exact ⟨K', iF, iN, iA, 𝒜, g, ⟨hsa, groupModel_isCommMonObj 𝒜⟩, hg, eta, heta, hne, hsec, r,
      hr, hx⟩

/-- `GaudronRemondThm14GR1` over `IsGR1StableHeightGlobal`. -/
def GaudronRemondThm14GR1Global : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (A B : PkgI3.AbVar K) (g : ℕ) (x : ℝ), 1 ≤ g →
    A.dim = (g : WithBot ℕ∞) → IsGR1StableHeightGlobal A x →
    (∃ φ : A.X ⟶ B.X, IsIsogenyPrinted φ) →
    (∃ φ : A.X ⟶ B.X, IsIsogenyPrinted φ ∧
      (isogDeg φ : ℝ) ≤ grKappa g (Module.finrank ℚ K) x) ∧
    (∃ ψ : B.X ⟶ A.X, IsIsogenyPrinted ψ ∧
      (isogDeg ψ : ℝ) ≤ grKappa g (Module.finrank ℚ K) x)

/-- **The Thm 1.4 row is unchanged** by the commutative model and the global-sections lattice. -/
theorem gaudronRemondThm14GR1Global_iff :
    GaudronRemondThm14GR1Global ↔ GaudronRemondThm14GR1 :=
  ⟨fun h K _ _ A B g x hg1 hg hx hiso =>
      h K A B g x hg1 hg (isGR1StableHeightGlobal_iff.mpr hx) hiso,
    fun h K _ _ A B g x hg1 hg hx hiso =>
      h K A B g x hg1 hg (isGR1StableHeightGlobal_iff.mp hx) hiso⟩

/-- The field `gaudronRemondThm14GR1` from its statement over `IsGR1StableHeightGlobal`. -/
theorem gaudronRemondThm14GR1_of_global (h : GaudronRemondThm14GR1Global) :
    GaudronRemondThm14GR1 :=
  gaudronRemondThm14GR1Global_iff.mp h

/-- `GaudronRemondSec9LowerGR1` (GR1 Cor. 8.4) over `IsGR1StableHeightGlobal`. -/
def GaudronRemondSec9LowerGR1Global : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (A : PkgI3.AbVar K) (g : ℕ), A.dim = (g : WithBot ℕ∞) →
    ∀ x : ℝ, IsGR1StableHeightGlobal A x →
      -((g : ℝ) / 2 * Real.log (2 * Real.pi)) ≤ x + (g : ℝ) / 2 * Real.log Real.pi

/-- **The Cor. 8.4 row is unchanged.** -/
theorem gaudronRemondSec9LowerGR1Global_iff :
    GaudronRemondSec9LowerGR1Global ↔ GaudronRemondSec9LowerGR1 :=
  ⟨fun h K _ _ A g hg x hx => h K A g hg x (isGR1StableHeightGlobal_iff.mpr hx),
    fun h K _ _ A g hg x hx => h K A g hg x (isGR1StableHeightGlobal_iff.mp hx)⟩

/-- `GaudronRemondSec9LowerGR1Weak` over `IsGR1StableHeightGlobal`. -/
def GaudronRemondSec9LowerGR1WeakGlobal : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (A : PkgI3.AbVar K) (g : ℕ), A.dim = (g : WithBot ℕ∞) →
    ∀ x : ℝ, IsGR1StableHeightGlobal A x → -(3 / 2) * (g : ℝ) ≤ x

/-- **The weak Cor. 8.4 row is unchanged.** -/
theorem gaudronRemondSec9LowerGR1WeakGlobal_iff :
    GaudronRemondSec9LowerGR1WeakGlobal ↔ GaudronRemondSec9LowerGR1Weak :=
  ⟨fun h K _ _ A g hg x hx => h K A g hg x (isGR1StableHeightGlobal_iff.mpr hx),
    fun h K _ _ A g hg x hx => h K A g hg x (isGR1StableHeightGlobal_iff.mp hx)⟩

/-- The field `gaudronRemondSec9LowerGR1Weak` from its statement over
`IsGR1StableHeightGlobal`. -/
theorem gaudronRemondSec9LowerGR1Weak_of_global (h : GaudronRemondSec9LowerGR1WeakGlobal) :
    GaudronRemondSec9LowerGR1Weak :=
  gaudronRemondSec9LowerGR1WeakGlobal_iff.mp h

end ZInQ.HeightModelM2
