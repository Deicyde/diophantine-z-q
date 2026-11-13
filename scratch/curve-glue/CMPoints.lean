import ZInQKernel.HDecomp.QM.Pin

/-!
# curve-glue, part 1: the CM points that `MobiusGlue` needs

Task curve-glue (2026-11-13). A review of g0-split remarked that the proof of `MobiusGlue`
(`scratch/mobius-glue/MobiusGlue.lean`, `mobiusGlue_of_curveFacts`) needs `ℚ̄`-points of `Y'`
over `0`, `∞` and `−16/27` whose objects have CM by `ℤ[i]`, `ℤ[ζ₃]`, `ℤ[√−6]`, while `R2fpProps`
only states the one-way implications "CM ⇒ value".

Settled here (all compiled):
* `MobiusGlue` (kernel, `ZInQKernel/HDecomp/QM/Pin.lean`) already **carries the CM objects as a
  hypothesis** (its fifth premise). Given them, the CM *points* over `0, ∞, −16/27` exist on
  every `(Y, Φ, π)` with `R2fpProps`, because `Φ Qbar` is a bijection onto `M3 Qbar`
  (`cm_points_of_objects`); only the one-way clauses of `R2fpProps` are used.
* The CM objects follow from the leaf bundle `R1R2fp` (kernel `cm_objects_of_R1R2fp`: `CMExists`
  on `X₆` and the second half of `X6Surj`, i.e. every QM pair over `ℚ̄` carries a level-3
  structure). Hence `cm_points_of_R1R2fp`.
* For the repaired bundle `R1R2fpRep` (which has no `CMExists` clause, only the biconditional
  `R2X6PropsIff`), `CMExists` follows from the biconditionals and the first half of `X6Surj`
  (`cmExists_of_iff`, copied from `scratch/h-decomposition/Leaves.lean`, LeafAdopt) and so the
  CM points exist too (`cm_points_of_R1R2fpRep`).
* `mobiusGlue_noCM_of`: the form of `MobiusGlue` without the CM premise follows from
  `MobiusGlue` and either bundle.

No `sorry`, no `axiom`.
-/

noncomputable section

namespace LeafQM

namespace AV

namespace CurveGlue

open CategoryTheory AlgebraicGeometry Limits
open PkgI3 Pin

/-! ## Copied verbatim from `scratch/h-decomposition/Leaves.lean` (namespace `LeafAdopt`) -/

/-- **R1pi0 (rv-blueprints Q4): `X₆` is geometrically connected over `ℚ`.** For the level-one
curve `X₆ = X₀(6,1)` of the bundle, `X₆ ×_ℚ ℚ̄` is connected (`π₀(X₆_ℚ̄) = 1`), the input of
h-b1 M10 (Lemma NV step 4) and of the shape `ℚ(t)(√(at), √(b(t−1)))` in A10 step 2.
*Published*: Deligne, Sém. Bourbaki 389 (1971), §2: `π₀(Sh_{K₀}) = ℚ^×_{>0}\𝔸_f^×/nrd(K₀)`,
trivial for `K₀ = 𝒪̂^×` since `nrd(𝒪̂^×) = ℤ̂^×` (locator UNVERIFIED; rv-blueprints re-derived the
computation, and `π₀(Y₃) = 2` from `nrd(1 + 3𝒪₃) = 1 + 3ℤ₃`). *Alternative*: rv-blueprints Q4
sketches a glue proof from `R5fpCount` and the CM clauses (Kummer parity of branch points;
SPECULATIVE, not checked in detail). Counted inside leaf R1 (same publications), not as a new
leaf. -/
def R1pi0Props (X : Over (Spec (CommRingCat.of ℚ))) : Prop :=
  GeometricallyConnected X.hom

/-- **R2 on `X₆` with biconditional CM clauses (rv-blueprints Q5).** As `R2X6Props`, with
"CM by `ℤ[i]` (resp. `ℤ[ζ₃]`, `ℤ[√−6]`) `↔` `π₆ = 0` (resp. `∞`, `−16/27`)". *Published*:
Baba–Granath 2008, Thm 2.1 and the §3.1 elliptic-order table (each of `CM(−4)`, `CM(−3)`,
`CM(−24)` is one `W`-orbit, the fibre over the corresponding value); a consequence, as
`R2X6Props` is. In the bundle it is not an extra assumption: `r2X6PropsIff_of` derives it from
`R2X6Props` and `CMExists`. -/
def R2X6PropsIff (X : Over (Spec (CommRingCat.of ℚ)))
    (Ψ : (fieldPt Qbar ⟶ X) ≃ Quotient (pairSetoid Qbar)) (π₆ : ToP1 X.left) : Prop :=
  ∀ (x x' : fieldPt Qbar ⟶ X) (P Q : QMPair Qbar),
    Ψ x = Quotient.mk _ P → Ψ x' = Quotient.mk _ Q →
      (π₆.val (K := Qbar) x.left = π₆.val (K := Qbar) x'.left ↔
          ∃ α : O ≃+* O, Nonempty (QMIso (P.q.twist α) Q.q)) ∧
      (HasCM4 P.q ↔ π₆.val (K := Qbar) x.left = OnePoint.some 0) ∧
      (HasCM3 P.q ↔ π₆.val (K := Qbar) x.left = OnePoint.infty) ∧
      (HasCM24 P.q ↔ π₆.val (K := Qbar) x.left = OnePoint.some (-16 / 27))

/-- The repaired bundle (docstring abridged; the statement is verbatim from LeafAdopt). -/
def R1R2fpRep : Prop :=
  ∃ (Y : Over (Spec (CommRingCat.of ℚ))) (Φ : PtEquiv Y)
    (X : Over (Spec (CommRingCat.of ℚ))) (Ψ : (fieldPt Qbar ⟶ X) ≃ Quotient (pairSetoid Qbar))
    (fY : Y ⟶ X) (π₆ : ToP1 X.left),
    R1fpProps Y Φ ∧ R1heckeProps Y Φ ∧ X6Props Y Φ X Ψ fY ∧ R2X6PropsIff X Ψ π₆ ∧
      R1recProps Y Φ ∧ X6Surj Y X fY π₆ ∧ R5ptProps X Ψ ∧ R1pi0Props X

variable {X : Over (Spec (CommRingCat.of ℚ))} {Ψ : (fieldPt Qbar ⟶ X) ≃ Quotient (pairSetoid Qbar)}
  {π₆ : ToP1 X.left}

/-- The biconditional form gives back the one-way form. -/
theorem r2X6Props_of_iff (h : R2X6PropsIff X Ψ π₆) : R2X6Props X Ψ π₆ := by
  intro x x' P Q hP hQ
  obtain ⟨hf, h4, h3, h24⟩ := h x x' P Q hP hQ
  exact ⟨hf, h4.1, h3.1, h24.1⟩

/-- **Glue (proved): existence of the three CM points** from the biconditionals and the
surjectivity of `π₆` on `ℚ̄`-points (the first half of `X6Surj`). -/
theorem cmExists_of_iff (h : R2X6PropsIff X Ψ π₆)
    (hs : ∀ t : OnePoint Qbar, ∃ x : fieldPt Qbar ⟶ X, π₆.val (K := Qbar) x.left = t) :
    CMExists X Ψ := by
  refine ⟨?_, ?_, ?_⟩
  · obtain ⟨x, hx⟩ := hs (OnePoint.some 0)
    exact ⟨x, (Ψ x).out, (Quotient.out_eq _).symm,
      ((h x x _ _ (Quotient.out_eq _).symm (Quotient.out_eq _).symm).2.1).2 hx⟩
  · obtain ⟨x, hx⟩ := hs OnePoint.infty
    exact ⟨x, (Ψ x).out, (Quotient.out_eq _).symm,
      ((h x x _ _ (Quotient.out_eq _).symm (Quotient.out_eq _).symm).2.2.1).2 hx⟩
  · obtain ⟨x, hx⟩ := hs (OnePoint.some (-16 / 27))
    exact ⟨x, (Ψ x).out, (Quotient.out_eq _).symm,
      ((h x x _ _ (Quotient.out_eq _).symm (Quotient.out_eq _).symm).2.2.2).2 hx⟩

/-- **Glue (proved)**: the repaired bundle implies leaf-qm-fp's `R1R2fp`. -/
theorem R1R2fp_of_rep (h : R1R2fpRep) : R1R2fp := by
  obtain ⟨Y, Φ, X, Ψ, fY, π₆, h1, hh, h6, h2, hr, hs, h5, -⟩ := h
  exact ⟨Y, Φ, X, Ψ, fY, π₆, h1, hh, h6, r2X6Props_of_iff h2, cmExists_of_iff h2 hs.1, hr, hs, h5⟩

/-! ## New: CM points on any triple -/

/-- The three CM objects (the fifth premise of `MobiusGlue`). -/
def CMObjects : Prop :=
  (∃ P : QML3 Qbar, HasCM4 P.q) ∧ (∃ P : QML3 Qbar, HasCM3 P.q) ∧ (∃ P : QML3 Qbar, HasCM24 P.q)

/-- The three CM points of `(Y, Φ, π)` over `0, ∞, −16/27`. -/
def CMPoints (Y : Over (Spec (CommRingCat.of ℚ))) (Φ : PtEquiv Y) (π : ToP1 Y.left) : Prop :=
  (∃ (y : fieldPt Qbar ⟶ Y) (P : QML3 Qbar), Φ Qbar y = M3.mk P ∧ HasCM4 P.q ∧
      π.val (K := Qbar) y.left = OnePoint.some 0) ∧
  (∃ (y : fieldPt Qbar ⟶ Y) (P : QML3 Qbar), Φ Qbar y = M3.mk P ∧ HasCM3 P.q ∧
      π.val (K := Qbar) y.left = OnePoint.infty) ∧
  (∃ (y : fieldPt Qbar ⟶ Y) (P : QML3 Qbar), Φ Qbar y = M3.mk P ∧ HasCM24 P.q ∧
      π.val (K := Qbar) y.left = OnePoint.some (-16 / 27))

/-- **CM points from CM objects** (`Φ Qbar` is onto; only the one-way clauses of `R2fpProps`). -/
theorem cm_points_of_objects {Y : Over (Spec (CommRingCat.of ℚ))} {Φ : PtEquiv Y}
    {π : ToP1 Y.left} (h2 : R2fpProps Y Φ π) (hCM : CMObjects) : CMPoints Y Φ π := by
  obtain ⟨⟨P₄, c₄⟩, ⟨P₃, c₃⟩, ⟨P₂, c₂⟩⟩ := hCM
  have e : ∀ P : QML3 Qbar, Φ Qbar ((Φ Qbar).symm (M3.mk P)) = M3.mk P :=
    fun P => Equiv.apply_symm_apply _ _
  refine ⟨⟨_, P₄, e P₄, c₄, ?_⟩, ⟨_, P₃, e P₃, c₃, ?_⟩, ⟨_, P₂, e P₂, c₂, ?_⟩⟩
  · exact ((h2 _ _ P₄ P₄ (e P₄) (e P₄)).2.1) c₄
  · exact ((h2 _ _ P₃ P₃ (e P₃) (e P₃)).2.2.1) c₃
  · exact ((h2 _ _ P₂ P₂ (e P₂) (e P₂)).2.2.2) c₂

/-- **CM points on every triple, from the leaf bundle `R1R2fp`** (via `CMExists`, `X6Surj`). -/
theorem cm_points_of_R1R2fp (h : R1R2fp) {Y : Over (Spec (CommRingCat.of ℚ))} {Φ : PtEquiv Y}
    {π : ToP1 Y.left} (h2 : R2fpProps Y Φ π) : CMPoints Y Φ π :=
  cm_points_of_objects h2 (cm_objects_of_R1R2fp h)

/-- **CM points on every triple, from the repaired bundle `R1R2fpRep`** (`CMExists` from the
biconditionals and `π₆` onto; level-3 structures from `Y₃ → X₆` onto). -/
theorem cm_points_of_R1R2fpRep (h : R1R2fpRep) {Y : Over (Spec (CommRingCat.of ℚ))}
    {Φ : PtEquiv Y} {π : ToP1 Y.left} (h2 : R2fpProps Y Φ π) : CMPoints Y Φ π :=
  cm_points_of_R1R2fp (R1R2fp_of_rep h) h2

/-- `MobiusGlue` without its CM premise. -/
def MobiusGlueNoCM : Prop :=
  ∀ (Y Y' : Over (Spec (CommRingCat.of ℚ))) (Φ : PtEquiv Y) (Φ' : PtEquiv Y')
    (π : ToP1 Y.left) (π' : ToP1 Y'.left) (g : Y' ⟶ Y),
    R1fpProps Y Φ → R2fpProps Y Φ π → R1fpProps Y' Φ' → R2fpProps Y' Φ' π' →
    (∀ (K : Type) [Field K] [Algebra ℚ K] (y : fieldPt K ⟶ Y'), Φ' K y = Φ K (y ≫ g)) →
    ∀ y : fieldPt Qbar ⟶ Y', π'.val (K := Qbar) y.left = π.val (K := Qbar) (y ≫ g).left

/-- **The CM premise of `MobiusGlue` is discharged by the leaf bundle.** -/
theorem mobiusGlue_noCM_of (hM : MobiusGlue) (h : R1R2fp) : MobiusGlueNoCM :=
  fun Y Y' Φ Φ' π π' g h1 h2 h1' h2' hg =>
    hM Y Y' Φ Φ' π π' g h1 h2 h1' h2' (cm_objects_of_R1R2fp h) hg

theorem mobiusGlue_noCM_of_rep (hM : MobiusGlue) (h : R1R2fpRep) : MobiusGlueNoCM :=
  mobiusGlue_noCM_of hM (R1R2fp_of_rep h)

end CurveGlue

end AV

end LeafQM

end

#print axioms LeafQM.AV.CurveGlue.cm_points_of_R1R2fp
#print axioms LeafQM.AV.CurveGlue.cm_points_of_R1R2fpRep
#print axioms LeafQM.AV.CurveGlue.mobiusGlue_noCM_of_rep
