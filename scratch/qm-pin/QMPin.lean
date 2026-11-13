import ZInQKernel.HDecomp.QM.Leaves

/-!
# qm-pin: pinning the moduli map `Φ` of the QM leaves by the universal family

Task qm-pin (2026-11-13), repairing rv-g0pieces §4. See `docs/research/qm-pin.md`.

`LeafQM.AV.R1fpProps` asks only that `Φ` be natural under field maps, so a non-geometric natural
relabeling `τ` of the field points of `Y` keeps it (rv-g0pieces `r1fp_relabel`, `r1fp_exotic`).
Repair: R1(a) says that `Y₃` *represents* the moduli functor, so it carries a universal object
`(𝒜, ι, η)`: an abelian scheme `𝒜 → Y₃` of relative dimension 2 with `𝒪`-action and level-3
sections, and the class of a field point `y` is the class of the fibre `y*𝒜`. The clause
`R1famProps` below states exactly this, over the same definitions (`QML3`, `M3`, `fieldPt`,
`PtEquiv`), with the fibre expressed as a pullback square (as `IsBaseChangeOf` does for base
change). `R1fpPropsPin` = `R1fpProps` + `R1famProps` is the repaired clause list; the integration
renames it to `R1fpProps`.

Contents.
* §1 `QMFamily`, `IsFibreOf`, `R1famProps`, `R1fpPropsPin`, `R1R2fpPin` (the repaired leaf).
* §2 The glue of `QM/Leaves.lean` re-proved on the repaired clause list (A4, A7, NV step 2,
  M9 through `cm_of_val`, notes-fix's strengthened `fibre_conjugates_isomorphic`).
* §3 The relabeling attack re-run: relabelings induced by automorphisms of `Y` keep the repaired
  clauses (`r1fpPin_aut`, `r2fp_aut`) and do not change any fibre statement (`transfer_pointwise`);
  a natural relabeling keeps `R1famProps` only through a proper smooth family realizing it
  (`r1famProps_relabel_iff`). `PinUnique` (every two triples satisfying the repaired clauses are
  isomorphic) is the algebraic-geometry statement that closes the attack: argued in the report,
  not compiled. Under `PinUnique`, statements quantified over all triples are equivalent to the
  statement for one triple (`pointwise_of_witness`).
No `sorry`, no `axiom`.
-/

noncomputable section

namespace LeafQM

namespace AV

namespace Pin

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open PkgI3

/-! ## §1 The universal family and the repaired clause list -/

/-- **A family of level-3 QM abelian surfaces over a scheme `S`** (the data of an object of the
moduli problem over `S`, without the group law, which rigidity recovers): a scheme `𝒜 → S`,
proper and smooth of relative dimension 2, with endomorphisms `ι(a)` over `S` (`a ∈ 𝒪`) and
sections `η(a) : S → 𝒜` (`a ∈ 𝒪`; for the universal object, the images of the constant sections
under the level structure `(𝒪/3𝒪)_S ≅ 𝒜[3]`). -/
structure QMFamily (S : Scheme.{0}) where
  F : Over S
  proper : IsProper F.hom
  smooth : SmoothOfRelativeDimension 2 F.hom
  iota : O → (F.left ⟶ F.left)
  iota_over : ∀ a : O, iota a ≫ F.hom = F.hom
  eta : O → (S ⟶ F.left)
  eta_sec : ∀ a : O, eta a ≫ F.hom = 𝟙 S

/-- **`P` is the fibre of the family `𝒜` at the field point `y : Spec K → S`**: a morphism
`g : P.A → 𝒜` making `P.A → Spec K` the pullback of `𝒜 → S` along `y`, carrying `ι_P` to `ι_𝒜`
and the level points `η_P(a)` to the sections `η_𝒜(a)` (same shape as `IsBaseChangeOf`). -/
def IsFibreOf {S : Scheme.{0}} (𝒜 : QMFamily S) {K : Type} [Field K]
    (y : Spec (CommRingCat.of K) ⟶ S) (P : QML3 K) : Prop :=
  ∃ g : P.A.X.left ⟶ 𝒜.F.left,
    IsPullback g P.A.X.hom 𝒜.F.hom y ∧
    (∀ a : O, (P.q.iota a).hom.left ≫ g = g ≫ 𝒜.iota a) ∧
    (∀ a : O, (Additive.toMul (P.e.eta a)).left ≫ g = y ≫ 𝒜.eta a)

/-- **R1fam, clause**: `Φ` is induced by a family: there is a family `𝒜` over `Y` (the universal
object of R1(a), polarization forgotten) such that the class `Φ_K(y)` of every field point is
the class of the fibre `y*𝒜`. -/
def R1famProps (Y : Over (Spec (CommRingCat.of ℚ))) (Φ : PtEquiv Y) : Prop :=
  ∃ 𝒜 : QMFamily Y.left, ∀ (K : Type) [Field K] [Algebra ℚ K] (y : fieldPt K ⟶ Y) (P : QML3 K),
    Φ K y = M3.mk P → IsFibreOf 𝒜 y.left P

/-- **R1fp, repaired clause list** (to replace `LeafQM.AV.R1fpProps`): the four old clauses and
`R1famProps`. -/
def R1fpPropsPin (Y : Over (Spec (CommRingCat.of ℚ))) (Φ : PtEquiv Y) : Prop :=
  IsProper Y.hom ∧ SmoothOfRelativeDimension 1 Y.hom ∧ Nonempty (fieldPt Qbar ⟶ Y) ∧
  (∀ (K L : Type) [Field K] [Field L] [Algebra ℚ K] [Algebra ℚ L] (f : K →ₐ[ℚ] L)
    (y : fieldPt K ⟶ Y) (P : QML3 K), Φ K y = M3.mk P →
      ∃ Q : QML3 L, Φ L (fieldMap f ≫ y) = M3.mk Q ∧ IsBaseChangeOf (f : K →+* L) P Q) ∧
  R1famProps Y Φ

theorem R1fpPropsPin.old {Y : Over (Spec (CommRingCat.of ℚ))} {Φ : PtEquiv Y}
    (h : R1fpPropsPin Y Φ) : R1fpProps Y Φ :=
  ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1⟩

theorem R1fpPropsPin.fam {Y : Over (Spec (CommRingCat.of ℚ))} {Φ : PtEquiv Y}
    (h : R1fpPropsPin Y Φ) : R1famProps Y Φ :=
  h.2.2.2.2

theorem R1fpPropsPin.mk' {Y : Over (Spec (CommRingCat.of ℚ))} {Φ : PtEquiv Y}
    (h : R1fpProps Y Φ) (hf : R1famProps Y Φ) : R1fpPropsPin Y Φ :=
  ⟨h.1, h.2.1, h.2.2.1, h.2.2.2, hf⟩

/-- **The repaired leaf bundle** (`LeafQM.AV.R1R2fp` with `R1fpPropsPin` for `R1fpProps`). -/
def R1R2fpPin : Prop :=
  ∃ (Y : Over (Spec (CommRingCat.of ℚ))) (Φ : PtEquiv Y)
    (X : Over (Spec (CommRingCat.of ℚ))) (Ψ : (fieldPt Qbar ⟶ X) ≃ Quotient (pairSetoid Qbar))
    (fY : Y ⟶ X) (π₆ : ToP1 X.left),
    R1fpPropsPin Y Φ ∧ R1heckeProps Y Φ ∧ X6Props Y Φ X Ψ fY ∧ R2X6Props X Ψ π₆ ∧
      CMExists X Ψ ∧ R1recProps Y Φ ∧ X6Surj Y X fY π₆ ∧ R5ptProps X Ψ

/-- The repaired bundle implies the old one (so every old glue theorem applies). -/
theorem R1R2fp_of_pin (h : R1R2fpPin) : R1R2fp := by
  obtain ⟨Y, Φ, X, Ψ, fY, π₆, h1, h⟩ := h
  exact ⟨Y, Φ, X, Ψ, fY, π₆, h1.old, h⟩

/-! ## §2 The glue of `QM/Leaves.lean` on the repaired clause list

Each proof is the kernel proof with `obtain ⟨-, -, -, hnat⟩ := h1` replaced by
`obtain ⟨-, -, -, hnat, -⟩ := h1` (the only change the integration needs in `QM/Leaves.lean`),
or the kernel theorem applied to `h1.old`. -/

theorem R1fp_of_R1R2fpPin (h : R1R2fpPin) :
    ∃ (Y : Over (Spec (CommRingCat.of ℚ))) (Φ : PtEquiv Y), R1fpPropsPin Y Φ := by
  obtain ⟨Y, Φ, -, -, -, -, h1, -, -, -, -, -, -, -⟩ := h
  exact ⟨Y, Φ, h1⟩

theorem R1R2fpPin_Y (h : R1R2fpPin) : ∃ (Y : Over (Spec (CommRingCat.of ℚ))) (Φ : PtEquiv Y)
    (π : ToP1 Y.left), R1fpPropsPin Y Φ ∧ R1heckeProps Y Φ ∧ R2fpProps Y Φ π := by
  obtain ⟨Y, Φ, X, Ψ, fY, π₆, h1, hh, hX, h2, -, -, -, -⟩ := h
  exact ⟨Y, Φ, π₆.comp fY.left, h1, hh, R2fpProps_of_X6 hX h2⟩

/-- A7 (kernel `conj_twist_of_rational`), from the repaired clause list. -/
theorem conj_twist_of_rational_pin {Y : Over (Spec (CommRingCat.of ℚ))} {Φ : PtEquiv Y}
    (h1 : R1fpPropsPin Y Φ) (π : ToP1 Y.left)
    (hfib : ∀ (y y' : fieldPt Qbar ⟶ Y) (P Q : QML3 Qbar),
      Φ Qbar y = M3.mk P → Φ Qbar y' = M3.mk Q →
      (π.val (K := Qbar) y.left = π.val (K := Qbar) y'.left ↔
          ∃ α : O ≃+* O, Nonempty (QMIso (P.q.twist α) Q.q)))
    (y : fieldPt Qbar ⟶ Y) (P : QML3 Qbar) (hP : Φ Qbar y = M3.mk P) (j₀ : ℚ)
    (hj : π.val (K := Qbar) y.left = OnePoint.some (algebraMap ℚ Qbar j₀))
    (σ : Qbar ≃ₐ[ℚ] Qbar) :
    ∃ Q : QML3 Qbar, IsBaseChangeOf (σ : Qbar →+* Qbar) P Q ∧
      ∃ α : O ≃+* O, Nonempty (QMIso (P.q.twist α) Q.q) := by
  obtain ⟨-, -, -, hnat, -⟩ := h1
  obtain ⟨Q, hQ, hbc⟩ := hnat Qbar Qbar (σ : Qbar →ₐ[ℚ] Qbar) y P hP
  refine ⟨Q, hbc, (hfib y _ P Q hP hQ).1 ?_⟩
  calc π.val (K := Qbar) y.left = OnePoint.some (algebraMap ℚ Qbar j₀) := hj
    _ = (OnePoint.some (algebraMap ℚ Qbar j₀)).map (σ : Qbar →+* Qbar) := by simp
    _ = (π.val (K := Qbar) y.left).map (σ : Qbar →+* Qbar) := by rw [hj]
    _ = π.val (K := Qbar) (fieldMap (σ : Qbar →ₐ[ℚ] Qbar) ≫ y).left :=
        (π.val_comp (σ : Qbar →+* Qbar) y.left).symm

/-- A7, manuscript form (kernel `conj_iso_of_rational`), via the projection to the old list. -/
theorem conj_iso_of_rational_pin {Y : Over (Spec (CommRingCat.of ℚ))} {Φ : PtEquiv Y}
    {π : ToP1 Y.left} (h1 : R1fpPropsPin Y Φ) (h2 : R2fpProps Y Φ π)
    {K : Type} [Field K] [Algebra ℚ K] (y : fieldPt K ⟶ Y) (P : QML3 K) (hP : Φ K y = M3.mk P)
    (j₀ : ℚ) (hj : π.val (K := K) y.left = OnePoint.some (algebraMap ℚ K j₀))
    (e₁ e₂ : K →ₐ[ℚ] Qbar) :
    ∃ Q₁ Q₂ : QML3 Qbar, IsBaseChangeOf (e₁ : K →+* Qbar) P Q₁ ∧
      IsBaseChangeOf (e₂ : K →+* Qbar) P Q₂ ∧
      ∃ α : O ≃+* O, Nonempty (QMIso (Q₁.q.twist α) Q₂.q) :=
  conj_iso_of_rational h1.old h2 y P hP j₀ hj e₁ e₂

/-- NV step 2 (kernel `unramified_over_branch`). -/
theorem unramified_over_branch_pin (h : R1R2fpPin ∧ R1rec) :
    ∃ (Y : Over (Spec (CommRingCat.of ℚ))) (Φ : PtEquiv Y) (π : ToP1 Y.left),
      R1fpPropsPin Y Φ ∧ R2fpProps Y Φ π ∧
      ∀ (y : fieldPt Qbar ⟶ Y) (P : QML3 Qbar), Φ Qbar y = M3.mk P →
        (π.val (K := Qbar) y.left = OnePoint.some 0 ∨
          π.val (K := Qbar) y.left = OnePoint.infty ∨
          π.val (K := Qbar) y.left = OnePoint.some (-16 / 27)) →
        UnramifiedAbove5 (fieldOfModuli3 P) := by
  obtain ⟨⟨Y, Φ, X, Ψ, fY, π₆, h1, -, hX, h2, hE, -, -, -⟩, hrec⟩ := h
  refine ⟨Y, Φ, π₆.comp fY.left, h1, R2fpProps_of_X6 hX h2, fun y P hP hv => hrec P ?_⟩
  obtain ⟨-, -, -, -, -, hf⟩ := hX
  have hc := cm_of_val h2 hE (y ≫ fY) P.forget (hf y P hP)
  have e : (π₆.comp fY.left).val (K := Qbar) y.left = π₆.val (K := Qbar) (y ≫ fY).left :=
    ToP1.val_comp_right π₆ fY.left y.left
  rw [e] at hv
  rcases hv with hv | hv | hv
  · exact Or.inl (hc.1 hv)
  · exact Or.inr (Or.inl (hc.2.1 hv))
  · exact Or.inr (Or.inr (hc.2.2 hv))

/-- NV step 2, point form (kernel `residue_unramified_over_branch`). -/
theorem residue_unramified_over_branch_pin (h : R1R2fpPin) :
    ∃ (Y : Over (Spec (CommRingCat.of ℚ))) (Φ : PtEquiv Y) (π : ToP1 Y.left),
      R1fpPropsPin Y Φ ∧ R2fpProps Y Φ π ∧
      ∀ (y : fieldPt Qbar ⟶ Y),
        (π.val (K := Qbar) y.left = OnePoint.some 0 ∨
          π.val (K := Qbar) y.left = OnePoint.infty ∨
          π.val (K := Qbar) y.left = OnePoint.some (-16 / 27)) →
        UnramifiedAbove5 (residueImage (X := Y.left) y.left) := by
  obtain ⟨Y, Φ, X, Ψ, fY, π₆, h1, -, hX, h2, hE, hrec, -, -⟩ := h
  refine ⟨Y, Φ, π₆.comp fY.left, h1, R2fpProps_of_X6 hX h2, fun y hv => ?_⟩
  have hP : Φ Qbar y = M3.mk (Quotient.out (Φ Qbar y)) := (Quotient.out_eq _).symm
  refine hrec y _ hP ?_
  obtain ⟨-, -, -, -, -, hf⟩ := hX
  have hc := cm_of_val h2 hE (y ≫ fY) _ (hf y _ hP)
  have e : (π₆.comp fY.left).val (K := Qbar) y.left = π₆.val (K := Qbar) (y ≫ fY).left :=
    ToP1.val_comp_right π₆ fY.left y.left
  rw [e] at hv
  rcases hv with hv | hv | hv
  · exact Or.inl (hc.1 hv)
  · exact Or.inr (Or.inl (hc.2.1 hv))
  · exact Or.inr (Or.inr (hc.2.2 hv))

/-- A4 (kernel `exists_fibre_object`). -/
theorem exists_fibre_object_pin (h : R1R2fpPin) :
    ∃ (Y : Over (Spec (CommRingCat.of ℚ))) (Φ : PtEquiv Y) (π : ToP1 Y.left),
      R1fpPropsPin Y Φ ∧ R2fpProps Y Φ π ∧
      ∀ t : OnePoint Qbar, ∃ (y : fieldPt Qbar ⟶ Y) (P : QML3 Qbar),
        Φ Qbar y = M3.mk P ∧ π.val (K := Qbar) y.left = t := by
  obtain ⟨Y, Φ, X, Ψ, fY, π₆, h1, -, hX, h2, -, -, ⟨hπ, hf⟩, -⟩ := h
  refine ⟨Y, Φ, π₆.comp fY.left, h1, R2fpProps_of_X6 hX h2, fun t => ?_⟩
  obtain ⟨x, hx⟩ := hπ t
  obtain ⟨y, rfl⟩ := hf x
  refine ⟨y, Quotient.out (Φ Qbar y), (Quotient.out_eq _).symm, ?_⟩
  have e : (π₆.comp fY.left).val (K := Qbar) y.left = π₆.val (K := Qbar) (y ≫ fY).left :=
    ToP1.val_comp_right π₆ fY.left y.left
  rw [e, hx]

/-- A4 + A7 (notes-fix's strengthened kernel `fibre_conjugates_isomorphic`). -/
theorem fibre_conjugates_isomorphic_pin (h : R1R2fpPin) (j₀ : ℚ) :
    ∃ (Y : Over (Spec (CommRingCat.of ℚ))) (Φ : PtEquiv Y) (π : ToP1 Y.left),
      R1fpPropsPin Y Φ ∧ R2fpProps Y Φ π ∧
      ∃ (y : fieldPt Qbar ⟶ Y) (P : QML3 Qbar), Φ Qbar y = M3.mk P ∧
        π.val (K := Qbar) y.left = OnePoint.some (algebraMap ℚ Qbar j₀) ∧
        ∀ σ : Qbar ≃ₐ[ℚ] Qbar, ∃ Q : QML3 Qbar,
          IsBaseChangeOf (σ : Qbar →+* Qbar) P Q ∧
          ∃ α : O ≃+* O, Nonempty (QMIso (P.q.twist α) Q.q) := by
  obtain ⟨Y, Φ, π, h1, h2, hfib⟩ := exists_fibre_object_pin h
  obtain ⟨y, P, hP, hy⟩ := hfib (OnePoint.some (algebraMap ℚ Qbar j₀))
  exact ⟨Y, Φ, π, h1, h2, y, P, hP, hy, fun σ => conj_twist_of_rational_pin h1 π
    (fun y y' P Q hP hQ => (h2 y y' P Q hP hQ).1) y P hP j₀ hy σ⟩

/-- All glue conclusions on one witness (kernel `leaves_on_one_witness`). -/
theorem leaves_on_one_witness_pin (h : R1R2fpPin) :
    ∃ (Y : Over (Spec (CommRingCat.of ℚ))) (Φ : PtEquiv Y) (π : ToP1 Y.left),
      R1fpPropsPin Y Φ ∧ R1heckeProps Y Φ ∧ R2fpProps Y Φ π ∧
      (∀ t : OnePoint Qbar, ∃ (y : fieldPt Qbar ⟶ Y) (P : QML3 Qbar),
        Φ Qbar y = M3.mk P ∧ π.val (K := Qbar) y.left = t) ∧
      (∀ y : fieldPt Qbar ⟶ Y,
        (π.val (K := Qbar) y.left = OnePoint.some 0 ∨
          π.val (K := Qbar) y.left = OnePoint.infty ∨
          π.val (K := Qbar) y.left = OnePoint.some (-16 / 27)) →
        UnramifiedAbove5 (residueImage (X := Y.left) y.left)) := by
  obtain ⟨Y, Φ, X, Ψ, fY, π₆, h1, hh, hX, h2, hE, hrec, ⟨hπ, hf⟩, -⟩ := h
  have e : ∀ z : fieldPt Qbar ⟶ Y,
      (π₆.comp fY.left).val (K := Qbar) z.left = π₆.val (K := Qbar) (z ≫ fY).left :=
    fun z => ToP1.val_comp_right π₆ fY.left z.left
  refine ⟨Y, Φ, π₆.comp fY.left, h1, hh, R2fpProps_of_X6 hX h2, fun t => ?_, fun y hv => ?_⟩
  · obtain ⟨x, hx⟩ := hπ t
    obtain ⟨y, rfl⟩ := hf x
    exact ⟨y, Quotient.out (Φ Qbar y), (Quotient.out_eq _).symm, by rw [e, hx]⟩
  · have hP : Φ Qbar y = M3.mk (Quotient.out (Φ Qbar y)) := (Quotient.out_eq _).symm
    refine hrec y _ hP ?_
    obtain ⟨-, -, -, -, -, hfo⟩ := hX
    have hc := cm_of_val h2 hE (y ≫ fY) _ (hfo y _ hP)
    rw [e] at hv
    rcases hv with hv | hv | hv
    · exact Or.inl (hc.1 hv)
    · exact Or.inr (Or.inl (hc.2.1 hv))
    · exact Or.inr (Or.inr (hc.2.2 hv))

/-- **Repaired leaf bundle** (to replace `QMLeaves`). -/
structure QMLeavesPin : Prop where
  r1r2 : R1R2fpPin
  r1rec : R1rec
  r5 : R5fp
  r5count : R5fpCount

theorem QMLeavesPin.old (h : QMLeavesPin) : QMLeaves := ⟨R1R2fp_of_pin h.r1r2, h.r1rec, h.r5, h.r5count⟩

/-! ## §3 The relabeling attack, re-run

`relabel Φ τ` and `IsNaturalRelabel` are rv-g0pieces' definitions (copied). -/

/-- (rv-g0pieces) A family of bijections of the field points of `Y`, natural in the field. -/
def IsNaturalRelabel (Y : Over (Spec (CommRingCat.of ℚ)))
    (τ : ∀ (K : Type) [Field K] [Algebra ℚ K], (fieldPt K ⟶ Y) ≃ (fieldPt K ⟶ Y)) : Prop :=
  ∀ (K L : Type) [Field K] [Field L] [Algebra ℚ K] [Algebra ℚ L] (f : K →ₐ[ℚ] L)
    (y : fieldPt K ⟶ Y), τ L (fieldMap f ≫ y) = fieldMap f ≫ τ K y

/-- (rv-g0pieces) `Φ` precomposed with a relabeling `τ`. -/
def relabel {Y : Over (Spec (CommRingCat.of ℚ))} (Φ : PtEquiv Y)
    (τ : ∀ (K : Type) [Field K] [Algebra ℚ K], (fieldPt K ⟶ Y) ≃ (fieldPt K ⟶ Y)) : PtEquiv Y :=
  fun K _ _ => (τ K).trans (Φ K)

/-- **What survives of rv-g0pieces' `r1fp_relabel`.** A natural relabeling keeps the repaired
clause list iff some family `𝒜'` over `Y` has the object of `τ y` as its fibre at every `y`:
the old clauses are kept for free (rv-g0pieces), the family is not. -/
theorem r1fpPin_relabel_iff {Y : Over (Spec (CommRingCat.of ℚ))} {Φ : PtEquiv Y}
    {τ : ∀ (K : Type) [Field K] [Algebra ℚ K], (fieldPt K ⟶ Y) ≃ (fieldPt K ⟶ Y)}
    (h : R1fpPropsPin Y Φ) (hτ : IsNaturalRelabel Y τ) :
    R1fpPropsPin Y (relabel Φ τ) ↔
      ∃ 𝒜' : QMFamily Y.left, ∀ (K : Type) [Field K] [Algebra ℚ K] (y : fieldPt K ⟶ Y)
        (P : QML3 K), Φ K (τ K y) = M3.mk P → IsFibreOf 𝒜' y.left P := by
  constructor
  · intro h'
    exact h'.fam
  · intro hf
    obtain ⟨hp, hs, hpt, hnat, -⟩ := h
    refine ⟨hp, hs, hpt, ?_, hf⟩
    intro K L _ _ _ _ f y P hP
    obtain ⟨Q, hQ, hb⟩ := hnat K L f (τ K y) P hP
    refine ⟨Q, ?_, hb⟩
    show Φ L (τ L (fieldMap f ≫ y)) = _
    rw [hτ K L f y]
    exact hQ

/-- The relabeling of field points by an automorphism `g` of `Y`: `y ↦ y ≫ g`. -/
def autRelabel {Y : Over (Spec (CommRingCat.of ℚ))} (g : Y ≅ Y) :
    ∀ (K : Type) [Field K] [Algebra ℚ K], (fieldPt K ⟶ Y) ≃ (fieldPt K ⟶ Y) :=
  fun _ _ _ =>
    { toFun := fun y => y ≫ g.hom
      invFun := fun y => y ≫ g.inv
      left_inv := fun y => by simp
      right_inv := fun y => by simp }

theorem autRelabel_natural {Y : Over (Spec (CommRingCat.of ℚ))} (g : Y ≅ Y) :
    IsNaturalRelabel Y (autRelabel g) := by
  intro K L _ _ _ _ f y
  show (fieldMap f ≫ y) ≫ g.hom = fieldMap f ≫ (y ≫ g.hom)
  rw [Category.assoc]

/-- The family transported along an automorphism `g` of `S`: same total space, structure map
`𝒜 → S → S` through `g⁻¹`, sections `η ∘ g`. Its fibre at `y` is the fibre of `𝒜` at `y ≫ g`. -/
def QMFamily.transport {S : Scheme.{0}} (𝒜 : QMFamily S) (g : S ≅ S) : QMFamily S where
  F := Over.mk (𝒜.F.hom ≫ g.inv)
  proper := by
    have := 𝒜.proper
    show IsProper (𝒜.F.hom ≫ g.inv)
    infer_instance
  smooth := by
    have := 𝒜.smooth
    show SmoothOfRelativeDimension 2 (𝒜.F.hom ≫ g.inv)
    exact inferInstanceAs (SmoothOfRelativeDimension (2 + 0) (𝒜.F.hom ≫ g.inv))
  iota := 𝒜.iota
  iota_over a := by
    show 𝒜.iota a ≫ 𝒜.F.hom ≫ g.inv = 𝒜.F.hom ≫ g.inv
    rw [← Category.assoc, 𝒜.iota_over]
  eta a := g.hom ≫ 𝒜.eta a
  eta_sec a := by
    show (g.hom ≫ 𝒜.eta a) ≫ 𝒜.F.hom ≫ g.inv = 𝟙 S
    rw [Category.assoc, ← Category.assoc (𝒜.eta a), 𝒜.eta_sec, Category.id_comp, g.hom_inv_id]

theorem isFibreOf_transport {S : Scheme.{0}} (𝒜 : QMFamily S) (g : S ≅ S) {K : Type} [Field K]
    (y : Spec (CommRingCat.of K) ⟶ S) (P : QML3 K) (h : IsFibreOf 𝒜 (y ≫ g.hom) P) :
    IsFibreOf (𝒜.transport g) y P := by
  obtain ⟨g₀, hpb, hι, hη⟩ := h
  refine ⟨g₀, ?_, hι, ?_⟩
  · have sq : IsPullback (𝟙 𝒜.F.left) 𝒜.F.hom (𝒜.F.hom ≫ g.inv) g.inv :=
      IsPullback.of_horiz_isIso ⟨by simp⟩
    have := hpb.paste_horiz sq
    rw [Category.comp_id, Category.assoc, g.hom_inv_id, Category.comp_id] at this
    exact this
  · intro a
    exact (hη a).trans (Category.assoc _ _ _)

/-- **Harmless relabelings survive** (so the repaired leaf pins `Φ` only up to `Aut(Y)`, as the
published theorem does): relabeling by an automorphism of `Y` keeps `R1fpPropsPin`. -/
theorem r1fpPin_aut {Y : Over (Spec (CommRingCat.of ℚ))} {Φ : PtEquiv Y}
    (h : R1fpPropsPin Y Φ) (g : Y ≅ Y) : R1fpPropsPin Y (relabel Φ (autRelabel g)) := by
  refine (r1fpPin_relabel_iff h (autRelabel_natural g)).2 ?_
  obtain ⟨𝒜, h𝒜⟩ := h.fam
  refine ⟨𝒜.transport ((Over.forget _).mapIso g), fun K _ _ y P hP => ?_⟩
  apply isFibreOf_transport
  exact h𝒜 K (y ≫ g.hom) P hP

/-- ... and keeps `R2fpProps` with `π ∘ g`. -/
theorem r2fp_aut {Y : Over (Spec (CommRingCat.of ℚ))} {Φ : PtEquiv Y} {π : ToP1 Y.left}
    (h : R2fpProps Y Φ π) (g : Y ≅ Y) :
    R2fpProps Y (relabel Φ (autRelabel g)) (π.comp g.hom.left) := by
  intro y y' P Q hP hQ
  have e : ∀ z : fieldPt Qbar ⟶ Y,
      (π.comp g.hom.left).val (K := Qbar) z.left = π.val (K := Qbar) (z ≫ g.hom).left :=
    fun z => ToP1.val_comp_right π g.hom.left z.left
  rw [e y, e y']
  exact h (y ≫ g.hom) (y' ≫ g.hom) P Q hP hQ

/-- Two triples are **the same up to an isomorphism** `g : Y' ≅ Y` of the schemes: classes and
`π`-values of `ℚ̄`-points correspond. -/
def SameTriple (Y Y' : Over (Spec (CommRingCat.of ℚ))) (Φ : PtEquiv Y) (Φ' : PtEquiv Y')
    (π : ToP1 Y.left) (π' : ToP1 Y'.left) : Prop :=
  ∃ g : Y' ≅ Y, (∀ (K : Type) [Field K] [Algebra ℚ K] (y : fieldPt K ⟶ Y'),
      Φ' K y = Φ K (y ≫ g.hom)) ∧
    ∀ y : fieldPt Qbar ⟶ Y', π'.val (K := Qbar) y.left = π.val (K := Qbar) (y ≫ g.hom).left

theorem sameTriple_aut {Y : Over (Spec (CommRingCat.of ℚ))} (Φ : PtEquiv Y) (π : ToP1 Y.left)
    (g : Y ≅ Y) : SameTriple Y Y Φ (relabel Φ (autRelabel g)) π (π.comp g.hom.left) :=
  ⟨g, fun _ _ _ _ => rfl, fun y => ToP1.val_comp_right π g.hom.left y.left⟩

/-- **Pointwise fibre statements transfer along `SameTriple`.** Each of `FibreSimple`,
`ThetaPointOfFibre`, `ModularConstituent` (g0-split) is, for fixed `(Y, Φ, π)`, of the form
`∀ u, ∀ y P, Φ y = [P] → π(y) = J(u) → R_u(P)` (for the first two, `FibreOver` is
`∃ emb y P, Φ y = [P] ∧ π y = J(u) ∧ …`, and `R_u(P)` absorbs `∀ K A emb, A_ℚ̄ ≅ P.A → …`). -/
theorem transfer_pointwise {Y Y' : Over (Spec (CommRingCat.of ℚ))} {Φ : PtEquiv Y}
    {Φ' : PtEquiv Y'} {π : ToP1 Y.left} {π' : ToP1 Y'.left}
    (hS : SameTriple Y Y' Φ Φ' π π') (t : OnePoint Qbar) (R : QML3 Qbar → Prop)
    (h : ∀ (y : fieldPt Qbar ⟶ Y) (P : QML3 Qbar), Φ Qbar y = M3.mk P →
      π.val (K := Qbar) y.left = t → R P) :
    ∀ (y' : fieldPt Qbar ⟶ Y') (P : QML3 Qbar), Φ' Qbar y' = M3.mk P →
      π'.val (K := Qbar) y'.left = t → R P := by
  obtain ⟨g, hΦ, hπ⟩ := hS
  intro y' P hP ht
  exact h (y' ≫ g.hom) P ((hΦ Qbar y').symm.trans hP) ((hπ y').symm.trans ht)

/-- The `∃`-form (`FibreOver`'s shape) transfers too. -/
theorem transfer_exists {Y Y' : Over (Spec (CommRingCat.of ℚ))} {Φ : PtEquiv Y}
    {Φ' : PtEquiv Y'} {π : ToP1 Y.left} {π' : ToP1 Y'.left}
    (hS : SameTriple Y Y' Φ Φ' π π') (t : OnePoint Qbar) (R : QML3 Qbar → Prop)
    (h : ∃ (y' : fieldPt Qbar ⟶ Y') (P : QML3 Qbar), Φ' Qbar y' = M3.mk P ∧
      π'.val (K := Qbar) y'.left = t ∧ R P) :
    ∃ (y : fieldPt Qbar ⟶ Y) (P : QML3 Qbar), Φ Qbar y = M3.mk P ∧
      π.val (K := Qbar) y.left = t ∧ R P := by
  obtain ⟨g, hΦ, hπ⟩ := hS
  obtain ⟨y', P, hP, ht, hR⟩ := h
  exact ⟨y' ≫ g.hom, P, (hΦ Qbar y').symm.trans hP, (hπ y').symm.trans ht, hR⟩

/-- **The uniqueness statement that closes the attack** (argued in `docs/research/qm-pin.md` §3,
from R1(a)'s universal property, rigidity, and the quotient argument for `π`; **not compiled**):
any two triples satisfying the repaired clauses are the same up to an isomorphism of schemes. For
the old clauses it is false (rv-g0pieces: `relabel Φ τ` for a non-geometric `τ`). -/
def PinUnique : Prop :=
  ∀ (Y Y' : Over (Spec (CommRingCat.of ℚ))) (Φ : PtEquiv Y) (Φ' : PtEquiv Y')
    (π : ToP1 Y.left) (π' : ToP1 Y'.left),
    R1fpPropsPin Y Φ → R2fpProps Y Φ π → R1fpPropsPin Y' Φ' → R2fpProps Y' Φ' π' →
      SameTriple Y Y' Φ Φ' π π'

/-- **Under `PinUnique`, a fibre statement for one triple is a fibre statement for all**: the
universal quantifier over `(Y, Φ, π)` in g0-split's three pieces costs nothing beyond the
statement for the leaf's own triple. -/
theorem pointwise_of_witness (hU : PinUnique) {Y₀ : Over (Spec (CommRingCat.of ℚ))}
    {Φ₀ : PtEquiv Y₀} {π₀ : ToP1 Y₀.left} (h1 : R1fpPropsPin Y₀ Φ₀) (h2 : R2fpProps Y₀ Φ₀ π₀)
    (R : OnePoint Qbar → QML3 Qbar → Prop)
    (h : ∀ t (y : fieldPt Qbar ⟶ Y₀) (P : QML3 Qbar), Φ₀ Qbar y = M3.mk P →
      π₀.val (K := Qbar) y.left = t → R t P) :
    ∀ (Y : Over (Spec (CommRingCat.of ℚ))) (Φ : PtEquiv Y) (π : ToP1 Y.left),
      R1fpPropsPin Y Φ → R2fpProps Y Φ π →
      ∀ t (y : fieldPt Qbar ⟶ Y) (P : QML3 Qbar), Φ Qbar y = M3.mk P →
        π.val (K := Qbar) y.left = t → R t P :=
  fun Y Φ π h1' h2' t =>
    transfer_pointwise (hU Y₀ Y Φ₀ Φ π₀ π h1 h2 h1' h2') t (R t) (h t)

/-- **Under `PinUnique`, every surviving relabeling is geometric.** If `relabel Φ τ` (with any
`π'`) again satisfies the repaired clause list, then `τ` is `y ↦ y ≫ g` for an automorphism `g`
of `Y`, on field points over every field, and `π'` is `π ∘ g` on `ℚ̄`-points. This is the precise
sense in which the relabeling attack of rv-g0pieces no longer applies (given `PinUnique`). -/
theorem relabel_geometric (hU : PinUnique) {Y : Over (Spec (CommRingCat.of ℚ))} {Φ : PtEquiv Y}
    {π π' : ToP1 Y.left}
    {τ : ∀ (K : Type) [Field K] [Algebra ℚ K], (fieldPt K ⟶ Y) ≃ (fieldPt K ⟶ Y)}
    (h1 : R1fpPropsPin Y Φ) (h2 : R2fpProps Y Φ π)
    (h1' : R1fpPropsPin Y (relabel Φ τ)) (h2' : R2fpProps Y (relabel Φ τ) π') :
    ∃ g : Y ≅ Y, (∀ (K : Type) [Field K] [Algebra ℚ K] (y : fieldPt K ⟶ Y), τ K y = y ≫ g.hom) ∧
      ∀ y : fieldPt Qbar ⟶ Y, π'.val (K := Qbar) y.left = π.val (K := Qbar) (y ≫ g.hom).left := by
  obtain ⟨g, hΦ, hπ⟩ := hU Y Y Φ (relabel Φ τ) π π' h1 h2 h1' h2'
  exact ⟨g, fun K _ _ y => (Φ K).injective (hΦ K y), hπ⟩

/-- **For the old clause list the same uniqueness statement would force every R2-compatible
natural relabeling to be geometric**, which rv-g0pieces' `relabelPt` (a bijection `s` of the
points with residue-field isomorphisms, not continuous) contradicts as soon as it is
R2-compatible. So `PinUniqueOld` is the statement that fails, and the family clause is what
`PinUnique` adds. -/
def PinUniqueOld : Prop :=
  ∀ (Y Y' : Over (Spec (CommRingCat.of ℚ))) (Φ : PtEquiv Y) (Φ' : PtEquiv Y')
    (π : ToP1 Y.left) (π' : ToP1 Y'.left),
    R1fpProps Y Φ → R2fpProps Y Φ π → R1fpProps Y' Φ' → R2fpProps Y' Φ' π' →
      SameTriple Y Y' Φ Φ' π π'

theorem relabel_geometric_old (hU : PinUniqueOld) {Y : Over (Spec (CommRingCat.of ℚ))}
    {Φ : PtEquiv Y} {π : ToP1 Y.left}
    {τ : ∀ (K : Type) [Field K] [Algebra ℚ K], (fieldPt K ⟶ Y) ≃ (fieldPt K ⟶ Y)}
    (h1 : R1fpProps Y Φ) (h2 : R2fpProps Y Φ π) (hτ : IsNaturalRelabel Y τ)
    (hfib : ∀ y y' : fieldPt Qbar ⟶ Y,
      π.val (K := Qbar) (τ Qbar y).left = π.val (K := Qbar) (τ Qbar y').left ↔
        π.val (K := Qbar) y.left = π.val (K := Qbar) y'.left)
    (hcm : ∀ y : fieldPt Qbar ⟶ Y,
      (π.val (K := Qbar) (τ Qbar y).left = OnePoint.some 0 ∨
        π.val (K := Qbar) (τ Qbar y).left = OnePoint.infty ∨
        π.val (K := Qbar) (τ Qbar y).left = OnePoint.some (-16 / 27)) →
      π.val (K := Qbar) y.left = π.val (K := Qbar) (τ Qbar y).left) :
    ∃ g : Y ≅ Y, ∀ (K : Type) [Field K] [Algebra ℚ K] (y : fieldPt K ⟶ Y), τ K y = y ≫ g.hom := by
  -- rv-g0pieces' `r1fp_relabel` and `r2fp_relabel` (re-proved): the relabeled triple satisfies
  -- the old lists.
  have h1' : R1fpProps Y (relabel Φ τ) := by
    obtain ⟨hp, hs, hpt, hnat⟩ := h1
    refine ⟨hp, hs, hpt, ?_⟩
    intro K L _ _ _ _ f y P hP
    obtain ⟨Q, hQ, hb⟩ := hnat K L f (τ K y) P hP
    refine ⟨Q, ?_, hb⟩
    show Φ L (τ L (fieldMap f ≫ y)) = _
    rw [hτ K L f y]
    exact hQ
  have h2' : R2fpProps Y (relabel Φ τ) π := by
    intro y y' P Q hP hQ
    obtain ⟨e1, h4, h3, h24⟩ := h2 (τ Qbar y) (τ Qbar y') P Q hP hQ
    refine ⟨(hfib y y').symm.trans e1, fun hc => ?_, fun hc => ?_, fun hc => ?_⟩
    · have e := h4 hc; rw [hcm y (Or.inl e)]; exact e
    · have e := h3 hc; rw [hcm y (Or.inr (Or.inl e))]; exact e
    · have e := h24 hc; rw [hcm y (Or.inr (Or.inr e))]; exact e
  obtain ⟨g, hΦ, -⟩ := hU Y Y Φ (relabel Φ τ) π π h1 h2 h1' h2'
  exact ⟨g, fun K _ _ y => (Φ K).injective (hΦ K y)⟩

/-! ## §4 Optional strengthening for provability: the universal property on families

`PinUnique` needs R1(a)'s universal property, which the leaf does not carry. The clause
`R1univProps` carries it on families over proper smooth curves (all the comparison needs). With
it, the `Φ`-half of the comparison is compiled (`phi_part`), and what remains is
`MobiusGlue` (a morphism of curves `Y' → P¹` with the fibres and the three values of `π ∘ g` is
`π ∘ g`): algebraic geometry of curves, glue, not a leaf. -/

/-- **R1univ, clause** (the existence half of R1(a)'s universal property, on families over proper
smooth curves `S/ℚ`): every family over `S` all of whose field fibres are objects is classified by
a morphism `g : S → Y`: the class of the object at `s ≫ g` is the fibre at `s`. -/
def R1univProps (Y : Over (Spec (CommRingCat.of ℚ))) (Φ : PtEquiv Y) : Prop :=
  ∀ (S : Over (Spec (CommRingCat.of ℚ))), IsProper S.hom → SmoothOfRelativeDimension 1 S.hom →
    ∀ 𝒜' : QMFamily S.left,
      (∀ (K : Type) [Field K] [Algebra ℚ K] (s : fieldPt K ⟶ S), ∃ P : QML3 K,
        IsFibreOf 𝒜' s.left P) →
      ∃ g : S ⟶ Y, ∀ (K : Type) [Field K] [Algebra ℚ K] (s : fieldPt K ⟶ S) (P : QML3 K),
        IsFibreOf 𝒜' s.left P → Φ K (s ≫ g) = M3.mk P

/-- **The `Φ`-half of the comparison (compiled).** If `(Y, Φ)` has the universal property and
`(Y', Φ')` satisfies the repaired clause list, then `Φ' = Φ ∘ g` for a morphism `g : Y' → Y`. -/
theorem phi_part {Y Y' : Over (Spec (CommRingCat.of ℚ))} {Φ : PtEquiv Y} {Φ' : PtEquiv Y'}
    (hU : R1univProps Y Φ) (h1' : R1fpPropsPin Y' Φ') :
    ∃ g : Y' ⟶ Y, ∀ (K : Type) [Field K] [Algebra ℚ K] (y : fieldPt K ⟶ Y'),
      Φ' K y = Φ K (y ≫ g) := by
  obtain ⟨hp', hs', -, -, ⟨𝒜', h𝒜'⟩⟩ := h1'
  have hall : ∀ (K : Type) [Field K] [Algebra ℚ K] (s : fieldPt K ⟶ Y'), ∃ P : QML3 K,
      IsFibreOf 𝒜' s.left P :=
    fun K _ _ s => ⟨Quotient.out (Φ' K s), h𝒜' K s _ (Quotient.out_eq _).symm⟩
  obtain ⟨g, hg⟩ := hU Y' hp' hs' 𝒜' hall
  refine ⟨g, fun K _ _ y => ?_⟩
  rw [hg K y _ (h𝒜' K y _ (Quotient.out_eq _).symm)]
  exact (Quotient.out_eq _).symm

/-- The fully repaired clause list: family and universal property. -/
def R1fpPropsU (Y : Over (Spec (CommRingCat.of ℚ))) (Φ : PtEquiv Y) : Prop :=
  R1fpPropsPin Y Φ ∧ R1univProps Y Φ

/-- `SameTriple` with a morphism in place of an isomorphism (all the transfer needs). -/
def SameTripleMor (Y Y' : Over (Spec (CommRingCat.of ℚ))) (Φ : PtEquiv Y) (Φ' : PtEquiv Y')
    (π : ToP1 Y.left) (π' : ToP1 Y'.left) : Prop :=
  ∃ g : Y' ⟶ Y, (∀ (K : Type) [Field K] [Algebra ℚ K] (y : fieldPt K ⟶ Y'),
      Φ' K y = Φ K (y ≫ g)) ∧
    ∀ y : fieldPt Qbar ⟶ Y', π'.val (K := Qbar) y.left = π.val (K := Qbar) (y ≫ g).left

theorem transfer_pointwise_mor {Y Y' : Over (Spec (CommRingCat.of ℚ))} {Φ : PtEquiv Y}
    {Φ' : PtEquiv Y'} {π : ToP1 Y.left} {π' : ToP1 Y'.left}
    (hS : SameTripleMor Y Y' Φ Φ' π π') (t : OnePoint Qbar) (R : QML3 Qbar → Prop)
    (h : ∀ (y : fieldPt Qbar ⟶ Y) (P : QML3 Qbar), Φ Qbar y = M3.mk P →
      π.val (K := Qbar) y.left = t → R P) :
    ∀ (y' : fieldPt Qbar ⟶ Y') (P : QML3 Qbar), Φ' Qbar y' = M3.mk P →
      π'.val (K := Qbar) y'.left = t → R P := by
  obtain ⟨g, hΦ, hπ⟩ := hS
  intro y' P hP ht
  exact h (y' ≫ g) P ((hΦ Qbar y').symm.trans hP) ((hπ y').symm.trans ht)

/-- **Glue (not compiled; argued in the report §3.4).** Given a morphism `g : Y' → Y` with
`Φ' = Φ ∘ g`, and CM objects of the three kinds, the two morphisms `π'` and `π ∘ g` to `P¹`
agree on `ℚ̄`-points: they have the same fibres (both `R2fpProps`), so `π' = h ∘ π ∘ g` with `h`
a bijection of `P¹(ℚ̄)` which is a morphism (graph argument on each geometric component of
`Y'`), hence a Möbius map, and `h` fixes `0, ∞, −16/27`. Algebraic geometry of curves. -/
def MobiusGlue : Prop :=
  ∀ (Y Y' : Over (Spec (CommRingCat.of ℚ))) (Φ : PtEquiv Y) (Φ' : PtEquiv Y')
    (π : ToP1 Y.left) (π' : ToP1 Y'.left) (g : Y' ⟶ Y),
    R1fpPropsU Y Φ → R2fpProps Y Φ π → R1fpPropsU Y' Φ' → R2fpProps Y' Φ' π' →
    ((∃ P : QML3 Qbar, HasCM4 P.q) ∧ (∃ P : QML3 Qbar, HasCM3 P.q) ∧
      (∃ P : QML3 Qbar, HasCM24 P.q)) →
    (∀ (K : Type) [Field K] [Algebra ℚ K] (y : fieldPt K ⟶ Y'), Φ' K y = Φ K (y ≫ g)) →
    ∀ y : fieldPt Qbar ⟶ Y', π'.val (K := Qbar) y.left = π.val (K := Qbar) (y ≫ g).left

/-- **The comparison from `R1univProps` and `MobiusGlue` (compiled).** -/
theorem sameTripleMor_of_mobius (hM : MobiusGlue)
    (hCM : (∃ P : QML3 Qbar, HasCM4 P.q) ∧ (∃ P : QML3 Qbar, HasCM3 P.q) ∧
      (∃ P : QML3 Qbar, HasCM24 P.q))
    {Y Y' : Over (Spec (CommRingCat.of ℚ))} {Φ : PtEquiv Y} {Φ' : PtEquiv Y'}
    {π : ToP1 Y.left} {π' : ToP1 Y'.left}
    (h1 : R1fpPropsU Y Φ) (h2 : R2fpProps Y Φ π) (h1' : R1fpPropsU Y' Φ')
    (h2' : R2fpProps Y' Φ' π') : SameTripleMor Y Y' Φ Φ' π π' := by
  obtain ⟨g, hg⟩ := phi_part h1.2 h1'.1
  exact ⟨g, hg, hM Y Y' Φ Φ' π π' g h1 h2 h1' h2' hCM hg⟩

/-- **Pieces from the witness, with `R1univProps` (compiled).** A fibre statement proved for one
triple satisfying the fully repaired list holds for every such triple, given `MobiusGlue` and CM
objects (the latter from the leaves: `CMExists` and `X6Surj`). -/
theorem pointwise_of_witness_mor (hM : MobiusGlue)
    (hCM : (∃ P : QML3 Qbar, HasCM4 P.q) ∧ (∃ P : QML3 Qbar, HasCM3 P.q) ∧
      (∃ P : QML3 Qbar, HasCM24 P.q))
    {Y₀ : Over (Spec (CommRingCat.of ℚ))} {Φ₀ : PtEquiv Y₀} {π₀ : ToP1 Y₀.left}
    (h1 : R1fpPropsU Y₀ Φ₀) (h2 : R2fpProps Y₀ Φ₀ π₀)
    (R : OnePoint Qbar → QML3 Qbar → Prop)
    (h : ∀ t (y : fieldPt Qbar ⟶ Y₀) (P : QML3 Qbar), Φ₀ Qbar y = M3.mk P →
      π₀.val (K := Qbar) y.left = t → R t P) :
    ∀ (Y : Over (Spec (CommRingCat.of ℚ))) (Φ : PtEquiv Y) (π : ToP1 Y.left),
      R1fpPropsU Y Φ → R2fpProps Y Φ π →
      ∀ t (y : fieldPt Qbar ⟶ Y) (P : QML3 Qbar), Φ Qbar y = M3.mk P →
        π.val (K := Qbar) y.left = t → R t P :=
  fun _ _ _ h1' h2' t =>
    transfer_pointwise_mor (sameTripleMor_of_mobius hM hCM h1 h2 h1' h2') t (R t) (h t)

/-- CM objects of the three kinds, from the leaf bundle (`CMExists` on `X₆` and the second half
of `X6Surj`, through the forgetful clause of `X6Props` and `QMIso`-invariance). -/
theorem cm_objects_of_R1R2fp (h : R1R2fp) :
    (∃ P : QML3 Qbar, HasCM4 P.q) ∧ (∃ P : QML3 Qbar, HasCM3 P.q) ∧
      (∃ P : QML3 Qbar, HasCM24 P.q) := by
  obtain ⟨Y, Φ, X, Ψ, fY, π₆, -, -, hX, -, ⟨⟨x₄, P₄, h₄, c₄⟩, ⟨x₃, P₃, h₃, c₃⟩, ⟨x₂, P₂, h₂, c₂⟩⟩,
    -, ⟨-, hs⟩, -⟩ := h
  obtain ⟨-, -, -, -, -, hf⟩ := hX
  have key : ∀ x : fieldPt Qbar ⟶ X, ∀ P : QMPair Qbar, Ψ x = Quotient.mk _ P →
      ∃ Q : QML3 Qbar, Nonempty (QMIso P.q Q.q) := by
    intro x P hP
    obtain ⟨y, rfl⟩ := hs x
    refine ⟨Quotient.out (Φ Qbar y), ?_⟩
    have e := hf y _ (Quotient.out_eq _).symm
    rw [hP] at e
    exact Quotient.exact e
  obtain ⟨Q₄, ⟨g₄⟩⟩ := key x₄ P₄ h₄
  obtain ⟨Q₃, ⟨g₃⟩⟩ := key x₃ P₃ h₃
  obtain ⟨Q₂, ⟨g₂⟩⟩ := key x₂ P₂ h₂
  exact ⟨⟨Q₄, HasCM4.of_iso g₄ c₄⟩, ⟨Q₃, HasCM3.of_iso g₃ c₃⟩, ⟨Q₂, HasCM24.of_iso g₂ c₂⟩⟩

end Pin

end AV

end LeafQM

#print axioms LeafQM.AV.Pin.R1R2fp_of_pin
#print axioms LeafQM.AV.Pin.fibre_conjugates_isomorphic_pin
#print axioms LeafQM.AV.Pin.leaves_on_one_witness_pin
#print axioms LeafQM.AV.Pin.unramified_over_branch_pin
#print axioms LeafQM.AV.Pin.residue_unramified_over_branch_pin
#print axioms LeafQM.AV.Pin.conj_iso_of_rational_pin
#print axioms LeafQM.AV.Pin.r1fpPin_relabel_iff
#print axioms LeafQM.AV.Pin.r1fpPin_aut
#print axioms LeafQM.AV.Pin.r2fp_aut
#print axioms LeafQM.AV.Pin.transfer_pointwise
#print axioms LeafQM.AV.Pin.transfer_exists
#print axioms LeafQM.AV.Pin.pointwise_of_witness
#print axioms LeafQM.AV.Pin.sameTriple_aut
#print axioms LeafQM.AV.Pin.relabel_geometric
#print axioms LeafQM.AV.Pin.relabel_geometric_old
#print axioms LeafQM.AV.Pin.phi_part
#print axioms LeafQM.AV.Pin.transfer_pointwise_mor
#print axioms LeafQM.AV.Pin.sameTripleMor_of_mobius
#print axioms LeafQM.AV.Pin.pointwise_of_witness_mor
#print axioms LeafQM.AV.Pin.cm_objects_of_R1R2fp
