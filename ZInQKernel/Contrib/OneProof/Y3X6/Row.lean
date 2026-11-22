import ZInQKernel.Contrib.OneProof.CMFoldRebase.Top3
import ZInQKernel.Contrib.OneProof.Y3ToP1j

/-! # y3-x6: the moduli row over `Y₃` alone (no `X₆` witness)

Task y3-x6 (2026-11-17). Report: `docs/research/y3-x6.md`; log: `scratch/y3-x6/log.md`.

The moduli row of the chain (`HDec.LeafAdopt.R1R2fpRepW`, and its `_r5` copy on the CM-branch route) carries an
`X₆ = X₀(6,1)` witness `(X, Ψ, fY, π₆)` with `X6Props`, `R2X6PropsIff`, `X6Surj`; the readers of those clauses
need, on `Y₃` only:

* R2 on `Y₃` (`R2fpProps`): the fibres of `π : Y₃ → P¹` and the CM values;
* `π` onto `P¹(ℚ̄)` (A4: a fibre over `J(u)`);
* the converse CM clauses (a point over `0, ∞, −16/27` has CM), for Lemma NV step 2 and for the CM objects.

All three are clauses of y3-p1j's leaf `Y3P1j.Y3ToP1jAt` (the manuscript's map `Y₃ → P¹_j`, diophantine_zq.tex
L420-440). So the row is restated over `Y₃` (`R1R2fpY3`): a fine witness `(Y, Φ)`, `π : Y → P¹` with
`Y3ToP1jAt`, the Hecke operators (`R1heckeProps`) and reciprocity (`R1recProps`). It is produced from
`Y3P1j.Y3ToP1j` and the ray-class leaf `ShimuraGlue.Ray.RayClassCM` (which carries its own fine witness), with the
proved glue `heckeOfFine_proof`. The readers' statements are reproved below on the new row (§2); they are the
hand-written replacements used by the generated copies `Y3X6/Copy*.lean`. -/

set_option linter.all false

noncomputable section

namespace Y3X6

open CategoryTheory AlgebraicGeometry Limits
open LeafQM LeafQM.AV HDec.QMSplit.Moduli

/-! ## 1. The row -/

/-- **The moduli row over `Y₃`** (y3-x6): a fine witness `(Y, Φ)` of the level-3 moduli problem, the Hecke
operators as automorphisms, `π : Y → P¹` with the clauses of the manuscript's map `Y₃ → P¹_j` (`Y3ToP1jAt`:
fibres = `Aut 𝒪`-twist classes, CM values `0, ∞, −16/27` as biconditionals, onto `P¹(ℚ̄)`, fibres of at most 324
points), and Shimura reciprocity at the three CM kinds (`R1recProps`). No `X₆`. -/
def R1R2fpY3 : Prop :=
  ∃ (Y : Over (Spec (CommRingCat.of ℚ))) (Φ : PtEquiv Y) (π : ToP1 Y.left),
    R1fpProps Y Φ ∧ R1heckeProps Y Φ ∧ Y3P1j.Y3ToP1jAt Y Φ π ∧ R1recProps Y Φ

/-- `R2fpProps` from the clauses of `Y3ToP1jAt` (the forward CM implications). -/
theorem r2fp_of_at {Y : Over (Spec (CommRingCat.of ℚ))} {Φ : PtEquiv Y} {π : ToP1 Y.left}
    (h : Y3P1j.Y3ToP1jAt Y Φ π) : R2fpProps Y Φ π := by
  intro y y' P Q hP hQ
  obtain ⟨a, b, c, d⟩ := h.1 y y' P Q hP hQ
  exact ⟨a, b.1, c.1, d.1⟩

/-- **The row from the leaves** (glue, proved): `Y3ToP1j` on the fine witness of the ray-class leaf, the Hecke
operators from `heckeOfFine_proof`, reciprocity from the ray-class leaf (`reciprocityCanonical_of_rayClass`,
`r1rec_of_reciprocityCanonical`, `reciprocityOfFine_of_r1rec`). -/
theorem r1r2fpY3_of (hY : Y3P1j.Y3ToP1j) (hR : ShimuraGlue.Ray.RayClassCM) : R1R2fpY3 := by
  have hrec := reciprocityOfFine_of_r1rec
    (r1rec_of_reciprocityCanonical (ShimuraGlue.Ray.reciprocityCanonical_of_rayClass hR))
  obtain ⟨Y, Φ, h1, -⟩ := hR
  obtain ⟨π, hπ⟩ := hY Y Φ h1
  exact ⟨Y, Φ, π, h1, heckeOfFine_proof Y Φ h1, hπ, hrec Y Φ h1⟩

/-! ## 2. The readers of the `X₆` clauses, on the new row -/

/-- The form consumed on `Y₃` (`LeafQM.AV.R1R2fp_Y`): R1fp + R1hecke + R2fp on one `Y` with one `π`. -/
theorem r1r2fp_Y (h : R1R2fpY3) : ∃ (Y : Over (Spec (CommRingCat.of ℚ))) (Φ : PtEquiv Y)
    (π : ToP1 Y.left), R1fpProps Y Φ ∧ R1heckeProps Y Φ ∧ R2fpProps Y Φ π := by
  obtain ⟨Y, Φ, π, h1, hh, hπ, -⟩ := h
  exact ⟨Y, Φ, π, h1, hh, r2fp_of_at hπ⟩

/-- **Lemma NV step 2, point form** (`LeafQM.AV.residue_unramified_over_branch`): a `ℚ̄`-point over `0`, `∞` or
`−16/27` has CM (the biconditional CM clauses of `Y3ToP1jAt`), hence an unramified residue field above 5
(`R1recProps`). On the `X₆` row this needed `CMExists` and the fibre clause on `X₆` (`cm_of_val`). -/
theorem residue_unramified_over_branch (h : R1R2fpY3) :
    ∃ (Y : Over (Spec (CommRingCat.of ℚ))) (Φ : PtEquiv Y) (π : ToP1 Y.left),
      R1fpProps Y Φ ∧ R2fpProps Y Φ π ∧
      ∀ (y : fieldPt Qbar ⟶ Y),
        (π.val (K := Qbar) y.left = OnePoint.some 0 ∨
          π.val (K := Qbar) y.left = OnePoint.infty ∨
          π.val (K := Qbar) y.left = OnePoint.some (-16 / 27)) →
        UnramifiedAbove5 (residueImage (X := Y.left) y.left) := by
  obtain ⟨Y, Φ, π, h1, -, hπ, hrec⟩ := h
  refine ⟨Y, Φ, π, h1, r2fp_of_at hπ, fun y hv => ?_⟩
  have hP : Φ Qbar y = M3.mk (Quotient.out (Φ Qbar y)) := (Quotient.out_eq _).symm
  refine hrec y _ hP ?_
  obtain ⟨-, h4, h3, h24⟩ := hπ.1 y y _ _ hP hP
  rcases hv with hv | hv | hv
  · exact Or.inl (h4.2 hv)
  · exact Or.inr (Or.inl (h3.2 hv))
  · exact Or.inr (Or.inr (h24.2 hv))

/-- **A4, choosing a fibre** (`LeafQM.AV.exists_fibre_object`): over every `t ∈ P¹(ℚ̄)` there is a `ℚ̄`-point
with an object and `π(y) = t` (the surjectivity clause of `Y3ToP1jAt`). -/
theorem exists_fibre_object (h : R1R2fpY3) :
    ∃ (Y : Over (Spec (CommRingCat.of ℚ))) (Φ : PtEquiv Y) (π : ToP1 Y.left),
      R1fpProps Y Φ ∧ R2fpProps Y Φ π ∧
      ∀ t : OnePoint Qbar, ∃ (y : fieldPt Qbar ⟶ Y) (P : QML3 Qbar),
        Φ Qbar y = M3.mk P ∧ π.val (K := Qbar) y.left = t := by
  obtain ⟨Y, Φ, π, h1, -, hπ, -⟩ := h
  refine ⟨Y, Φ, π, h1, r2fp_of_at hπ, fun t => ?_⟩
  obtain ⟨y, hy⟩ := hπ.2.1 t
  exact ⟨y, Quotient.out (Φ Qbar y), (Quotient.out_eq _).symm, hy⟩

/-- **CM objects of the three kinds** (`LeafQM.AV.Pin.cm_objects_of_R1R2fp`): the points over `0`, `∞`, `−16/27`
(surjectivity) have CM by `ℤ[i]`, `ℤ[ζ₃]`, `ℤ[√−6]` (the biconditional CM clauses). -/
theorem cm_objects (h : R1R2fpY3) :
    (∃ P : QML3 Qbar, HasCM4 P.q) ∧ (∃ P : QML3 Qbar, HasCM3 P.q) ∧
      (∃ P : QML3 Qbar, HasCM24 P.q) := by
  obtain ⟨Y, Φ, π, -, -, hπ, -⟩ := h
  have hP : ∀ y : fieldPt Qbar ⟶ Y, Φ Qbar y = M3.mk (Quotient.out (Φ Qbar y)) :=
    fun y => (Quotient.out_eq _).symm
  obtain ⟨y₄, hy₄⟩ := hπ.2.1 (OnePoint.some 0)
  obtain ⟨y₃, hy₃⟩ := hπ.2.1 OnePoint.infty
  obtain ⟨y₂, hy₂⟩ := hπ.2.1 (OnePoint.some (-16 / 27))
  exact ⟨⟨_, (hπ.1 y₄ y₄ _ _ (hP y₄) (hP y₄)).2.1.2 hy₄⟩,
    ⟨_, (hπ.1 y₃ y₃ _ _ (hP y₃) (hP y₃)).2.2.1.2 hy₃⟩,
    ⟨_, (hπ.1 y₂ y₂ _ _ (hP y₂) (hP y₂)).2.2.2.2 hy₂⟩⟩

/-- **`R1rec` (object form) from the row** (`HDec.HSyn.r1rec_of_rep`): the object `P` is the object at a point
`y` of the fine witness, the witness's reciprocity clause makes `ℚ(y)` unramified above 5, and
`fieldOfModuli3 P ⊆ ℚ(y)`. -/
theorem r1rec_of_row (h : R1R2fpY3) : LeafQM.AV.R1rec := by
  obtain ⟨Y, Φ, π, h1, -, -, hrec⟩ := h
  intro P hcm
  have hy : Φ _ ((Φ _).symm (LeafQM.AV.M3.mk P)) = LeafQM.AV.M3.mk P := Equiv.apply_symm_apply _ _
  exact _root_.ZInQ.LeafFold9.unramifiedAbove5_mono (_root_.ZInQ.LeafFold9.fieldOfModuli3_le h1 _ P hy)
    (hrec _ P hy hcm)

end Y3X6
