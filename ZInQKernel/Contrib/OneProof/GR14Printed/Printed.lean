import ZInQKernel.Contrib.OneProof.SemistablePrintedReadings
import ZInQKernel.Contrib.OneProof.GR14Printed.DimZero
import ZInQKernel.Contrib.OneProof.GR14Printed.FiniteKernel

/-! # GR14Printed: the printed form of Gaudron–Rémond Thm 1.4 and the field

`GaudronRemondThm14Printed` is the field `ZInQ.SemistabAssembly.GaudronRemondThm14AnSS` with the
two clauses the print has and the field lacks: `1 ≤ g` (Duke Math. J. 163 (2014), p. 2058) and
isogenies "surjectif de noyau fini" (§2, p. 2062; `IsIsogenyPrinted`). Everything else (the height
`IsAnStableHeightSS`, `κ = grKappa`, the degree `isogDeg`, the two separate isogenies) is the
field's, unchanged.

* B1: `GaudronRemondThm14AnSSPos` (the field with `1 ≤ g`) gives the field with the proved `g = 0`
  case (`gaudronRemondThm14AnSS_of_pos`).
* B2: the printed form and `GaudronRemondThm14AnSSPos` are equivalent (`isIsogenyPrinted_iff`).
* `gaudronRemondThm14AnSS_of_printed : GaudronRemondThm14Printed → GaudronRemondThm14AnSS`, and
  the converse (`gaudronRemondThm14Printed_iff`): the restatement is a same-strength rewording of
  the row, weaker as a statement only through `1 ≤ g`.
-/

open CategoryTheory
open ZInQ.DefFaltings ZInQ.SemistabAssembly

namespace ZInQ.GR14Printed

/-- **The field restricted to `g ≥ 1`** (B1): `GaudronRemondThm14AnSS` with `1 ≤ g` added. -/
def GaudronRemondThm14AnSSPos : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (A B : PkgI3.AbVar K) (g : ℕ) (x : ℝ), 1 ≤ g →
    A.dim = (g : WithBot ℕ∞) → IsAnStableHeightSS A x →
    (∃ φ : A.X ⟶ B.X, IsIsogeny φ) →
    (∃ φ : A.X ⟶ B.X, IsIsogeny φ ∧ (isogDeg φ : ℝ) ≤ grKappa g (Module.finrank ℚ K) x) ∧
    (∃ ψ : B.X ⟶ A.X, IsIsogeny ψ ∧ (isogDeg ψ : ℝ) ≤ grKappa g (Module.finrank ℚ K) x)

/-- **B1**: the restricted form and the proved `g = 0` case give the field. -/
theorem gaudronRemondThm14AnSS_of_pos (h : GaudronRemondThm14AnSSPos) :
    GaudronRemondThm14AnSS := by
  intro K _ _ A B g x hg hx hiso
  rcases Nat.eq_zero_or_pos g with rfl | hpos
  · exact gr14_dim_zero A B hg _ x hiso
  · exact h K A B g x hpos hg hx hiso

/-- The field gives the restricted form (it is weaker). -/
theorem gaudronRemondThm14AnSSPos_of_field (h : GaudronRemondThm14AnSS) :
    GaudronRemondThm14AnSSPos :=
  fun K _ _ A B g x _ hg hx hiso => h K A B g x hg hx hiso

/-- **The printed form** of Gaudron–Rémond, Duke Math. J. 163 (2014), Thm 1.4 (p. 2060; `κ(A)`
and `g ≥ 1`, p. 2058; isogenies "surjectif de noyau fini" and the degree, §2, p. 2062), specialized
to `k = K`, over the same height as the field: `GaudronRemondThm14AnSS` with `1 ≤ g` added and
`IsIsogeny` replaced by `IsIsogenyPrinted` (hypothesis and conclusion). -/
def GaudronRemondThm14Printed : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (A B : PkgI3.AbVar K) (g : ℕ) (x : ℝ), 1 ≤ g →
    A.dim = (g : WithBot ℕ∞) → IsAnStableHeightSS A x →
    (∃ φ : A.X ⟶ B.X, IsIsogenyPrinted φ) →
    (∃ φ : A.X ⟶ B.X, IsIsogenyPrinted φ ∧
      (isogDeg φ : ℝ) ≤ grKappa g (Module.finrank ℚ K) x) ∧
    (∃ ψ : B.X ⟶ A.X, IsIsogenyPrinted ψ ∧
      (isogDeg ψ : ℝ) ≤ grKappa g (Module.finrank ℚ K) x)

/-- **B2**: the printed form gives the restricted form (`isIsogenyPrinted_iff`). -/
theorem gaudronRemondThm14AnSSPos_of_printed (h : GaudronRemondThm14Printed) :
    GaudronRemondThm14AnSSPos := by
  intro K _ _ A B g x hg1 hg hx hiso
  obtain ⟨φ, hφ⟩ := hiso
  obtain ⟨⟨φ', h1, h2⟩, ⟨ψ', h3, h4⟩⟩ :=
    h K A B g x hg1 hg hx ⟨φ, isIsogenyPrinted_of_isIsogeny hφ⟩
  exact ⟨⟨φ', isIsogeny_of_isIsogenyPrinted h1, h2⟩,
    ⟨ψ', isIsogeny_of_isIsogenyPrinted h3, h4⟩⟩

/-- The restricted form gives the printed form. -/
theorem gaudronRemondThm14Printed_of_pos (h : GaudronRemondThm14AnSSPos) :
    GaudronRemondThm14Printed := by
  intro K _ _ A B g x hg1 hg hx hiso
  obtain ⟨φ, hφ⟩ := hiso
  obtain ⟨⟨φ', h1, h2⟩, ⟨ψ', h3, h4⟩⟩ :=
    h K A B g x hg1 hg hx ⟨φ, isIsogeny_of_isIsogenyPrinted hφ⟩
  exact ⟨⟨φ', isIsogenyPrinted_of_isIsogeny h1, h2⟩,
    ⟨ψ', isIsogenyPrinted_of_isIsogeny h3, h4⟩⟩

/-- **The field from the printed form** (B1 and B2). -/
theorem gaudronRemondThm14AnSS_of_printed (h : GaudronRemondThm14Printed) :
    GaudronRemondThm14AnSS :=
  gaudronRemondThm14AnSS_of_pos (gaudronRemondThm14AnSSPos_of_printed h)

/-- The printed form and the field are equivalent: the restatement neither gains nor loses
strength. -/
theorem gaudronRemondThm14Printed_iff :
    GaudronRemondThm14Printed ↔ GaudronRemondThm14AnSS :=
  ⟨gaudronRemondThm14AnSS_of_printed, fun h =>
    gaudronRemondThm14Printed_of_pos (gaudronRemondThm14AnSSPos_of_field h)⟩

end ZInQ.GR14Printed
