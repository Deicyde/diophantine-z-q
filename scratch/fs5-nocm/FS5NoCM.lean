import ZInQKernel.HDecomp.QM.Leaves
import ZInQKernel.HDecomp.Repo.PRArith
import ZInQKernel.Hypotheses.JHeight

/-!
# fs5-nocm: FS5 `FibreComTrivial` (NoCM on the fibre) from NoCM's inputs

Task fs5-nocm (2026-11-13). See `docs/research/fs5-nocm.md`.

* §A (copied verbatim from `scratch/qm-pin/QMPin.lean`, lines 34-94 and 507-619): `QMFamily`,
  `IsFibreOf`, `R1famProps`, `R1fpPropsPin`, `R1univProps`, `R1fpPropsU`, `SameTripleMor`,
  `transfer_pointwise_mor`, `phi_part`, `MobiusGlue`, `sameTripleMor_of_mobius`,
  `pointwise_of_witness_mor`, `cm_objects_of_R1R2fp`.
* §B FS5 as in `scratch/g0-fibresimple/FibreSimple.lean` (verbatim) and with qm-pin's full repair
  of `R1fpProps` (text of `scratch/qm-pin/QM-Leaves-full.patch`).
* §C the named Props NoCM still needs; §D the arithmetic; §E the proof.
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

namespace FS5NoCM

open CategoryTheory AlgebraicGeometry Limits
open LeafQM.AV LeafQM.AV.Pin ZInQ ZInQ.JHeight PkgI3

/-! ## §B The statement -/

/-- **FS5 as stated by g0-fibresimple** (verbatim from `scratch/g0-fibresimple/FibreSimple.lean`,
`HSyn.G0Split.FibreComTrivial`, with the old `R1fpProps`; kept for reference: g0-fibresimple §2
shows that the old clause list does not pin `Φ`, so this form is not a consequence of the leaves).

**Glue piece FS5 = G6 (NoCM, rv-h-cm §7.2, on the actual fibre object).** For `u ∉ 𝒞` and an
object `P` of `Y₃` at a `ℚ̄`-point over `J(u)`, the centralizer `End_𝒪(P.A)` is `ℤ` (the point is
not a CM point). -/
def FibreComTrivial : Prop :=
  ∀ (Y : Over (Spec (CommRingCat.of ℚ))) (Φ : PtEquiv Y) (π : ToP1 Y.left),
    R1fpProps Y Φ → R2fpProps Y Φ π → ∀ u : ℚ, u ∉ contactSet →
    ∀ (y : fieldPt LeafQM.AV.Qbar ⟶ Y) (P : QML3 LeafQM.AV.Qbar), Φ LeafQM.AV.Qbar y = M3.mk P →
      π.val (K := LeafQM.AV.Qbar) y.left = OnePoint.some (algebraMap ℚ LeafQM.AV.Qbar (Jmap u)) →
      ∀ φ ∈ com P.q, ∃ n : ℤ, φ = (n : PkgI3.AbVar.End P.A)

/-- **`R1fpProps` after qm-pin's full edit** (text of `scratch/qm-pin/QM-Leaves-full.patch`,
lines 63-70: the four old clauses, `R1famProps` and `R1univProps`). After the integration this is
`LeafQM.AV.R1fpProps`. -/
def R1fpPropsFull (Y : Over (Spec (CommRingCat.of ℚ))) (Φ : PtEquiv Y) : Prop :=
  IsProper Y.hom ∧ SmoothOfRelativeDimension 1 Y.hom ∧ Nonempty (fieldPt Qbar ⟶ Y) ∧
  (∀ (K L : Type) [Field K] [Field L] [Algebra ℚ K] [Algebra ℚ L] (f : K →ₐ[ℚ] L)
    (y : fieldPt K ⟶ Y) (P : QML3 K), Φ K y = M3.mk P →
      ∃ Q : QML3 L, Φ L (fieldMap f ≫ y) = M3.mk Q ∧ IsBaseChangeOf (f : K →+* L) P Q) ∧
  R1famProps Y Φ ∧ R1univProps Y Φ

theorem r1fpPropsFull_iff (Y : Over (Spec (CommRingCat.of ℚ))) (Φ : PtEquiv Y) :
    R1fpPropsFull Y Φ ↔ R1fpPropsU Y Φ :=
  ⟨fun ⟨a, b, c, d, e, f⟩ => ⟨⟨a, b, c, d, e⟩, f⟩, fun ⟨⟨a, b, c, d, e⟩, f⟩ => ⟨a, b, c, d, e, f⟩⟩

theorem R1fpPropsFull.old {Y : Over (Spec (CommRingCat.of ℚ))} {Φ : PtEquiv Y}
    (h : R1fpPropsFull Y Φ) : R1fpProps Y Φ := ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1⟩

/-- **FS5 with the repaired QM clauses** (the statement this task proves): `FibreComTrivial`
verbatim, with `R1fpProps` read as after qm-pin's full edit (`R1fpPropsFull`). -/
def FibreComTrivialFull : Prop :=
  ∀ (Y : Over (Spec (CommRingCat.of ℚ))) (Φ : PtEquiv Y) (π : ToP1 Y.left),
    R1fpPropsFull Y Φ → R2fpProps Y Φ π → ∀ u : ℚ, u ∉ contactSet →
    ∀ (y : fieldPt LeafQM.AV.Qbar ⟶ Y) (P : QML3 LeafQM.AV.Qbar), Φ LeafQM.AV.Qbar y = M3.mk P →
      π.val (K := LeafQM.AV.Qbar) y.left = OnePoint.some (algebraMap ℚ LeafQM.AV.Qbar (Jmap u)) →
      ∀ φ ∈ com P.q, ∃ n : ℤ, φ = (n : PkgI3.AbVar.End P.A)

/-- The clause list of the leaf bundle `LeafQM.AV.R1R2fp` on one witness, with `R1fpProps` as
after qm-pin's full edit. -/
def R1R2fpFullProps (Y : Over (Spec (CommRingCat.of ℚ))) (Φ : PtEquiv Y)
    (X : Over (Spec (CommRingCat.of ℚ))) (Ψ : (fieldPt Qbar ⟶ X) ≃ Quotient (pairSetoid Qbar))
    (fY : Y ⟶ X) (π₆ : ToP1 X.left) : Prop :=
  R1fpPropsFull Y Φ ∧ R1heckeProps Y Φ ∧ X6Props Y Φ X Ψ fY ∧ R2X6Props X Ψ π₆ ∧
    CMExists X Ψ ∧ R1recProps Y Φ ∧ X6Surj Y X fY π₆ ∧ R5ptProps X Ψ

/-- **The leaf bundle `LeafQM.AV.R1R2fp` after qm-pin's full edit** (same text, `R1fpProps`
repaired). -/
def R1R2fpFull : Prop :=
  ∃ (Y : Over (Spec (CommRingCat.of ℚ))) (Φ : PtEquiv Y)
    (X : Over (Spec (CommRingCat.of ℚ))) (Ψ : (fieldPt Qbar ⟶ X) ≃ Quotient (pairSetoid Qbar))
    (fY : Y ⟶ X) (π₆ : ToP1 X.left), R1R2fpFullProps Y Φ X Ψ fY π₆

theorem R1R2fp_of_full (h : R1R2fpFull) : R1R2fp := by
  obtain ⟨Y, Φ, X, Ψ, fY, π₆, h1, h⟩ := h
  exact ⟨Y, Φ, X, Ψ, fY, π₆, h1.old, h⟩

/-- **FS5 for the leaf's own triple** (the restatement that qm-pin's `pointwise_of_witness_mor`
allows): for every witness `(Y, Φ, X, Ψ, fY, π₆)` of the repaired leaf bundle, the objects over
`J(u)`, `u ∉ 𝒞`, of the triple `(Y, Φ, π₆ ∘ fY)` have `End_𝒪 = ℤ`. Quantified over all witnesses
(not a `Classical.choice` of one), so it is a statement about the published data, not about a
choice. -/
def FibreComTrivialOwn : Prop :=
  ∀ (Y : Over (Spec (CommRingCat.of ℚ))) (Φ : PtEquiv Y)
    (X : Over (Spec (CommRingCat.of ℚ))) (Ψ : (fieldPt Qbar ⟶ X) ≃ Quotient (pairSetoid Qbar))
    (fY : Y ⟶ X) (π₆ : ToP1 X.left), R1R2fpFullProps Y Φ X Ψ fY π₆ →
    ∀ u : ℚ, u ∉ contactSet →
    ∀ (y : fieldPt Qbar ⟶ Y) (P : QML3 Qbar), Φ Qbar y = M3.mk P →
      (π₆.comp fY.left).val (K := Qbar) y.left = OnePoint.some (algebraMap ℚ Qbar (Jmap u)) →
      ∀ φ ∈ com P.q, ∃ n : ℤ, φ = (n : AbVar.End P.A)

/-! ## §C The named Props NoCM needs -/

/-- **NoCM input N1a (glue; G5-G6, rv-h-cm §7.2 "the CM order"): `End_𝒪(A)` is `ℤ` or an order in
an imaginary quadratic field.** For a QM pair `(A, ι)` over `ℚ̄`, either every element of the
centralizer `com ι = End_𝒪(A)` is an integer, or `com ι` is isomorphic to a subring `R` of the
ring of integers of an imaginary quadratic field `k`, of finite index (`conductor R ≠ 0`).
*Why true* (STANDARD): by Yu's dichotomy (leaf T27, `PkgI3.QMDichotomyYu`, in characteristic 0)
`End⁰(A) ≅ B` or `≅ M₂(k)` with `k` imaginary quadratic; the centralizer of `B` is `ℚ`, resp. the
centre `k` (FS4's argument, `centralizerOfMatrixEnd0_of_homFree`); `com ι = End(A) ∩ com⁰` is a
finitely generated (T6) subring of `ℚ`, resp. of `k`, of rank 1, resp. 2, and integral over `ℤ`,
hence `ℤ`, resp. an order of `k`. Glue from T27 and T6 (not compiled here). -/
def ComIntOrQuadOrder : Prop :=
  ∀ P : QMPair Qbar, (∀ φ ∈ com P.q, ∃ n : ℤ, φ = (n : AbVar.End P.A)) ∨
    ∃ (k : Type) (_ : Field k) (_ : NumberField k) (_ : NumberField.IsTotallyComplex k),
      Module.finrank ℚ k = 2 ∧ ∃ R : Subring k, R ≤ (integralClosure ℤ k).toSubring ∧
        conductor R ≠ 0 ∧ Nonempty (com P.q ≃+* R)

/-- **NoCM input N1b (leaf; "(Emb)" of rv-h-cm §7.2 and rv-nocm §1.2): the CM order has conductor
prime to 6.** If `End_𝒪(A) ≅ R` for an order `R` of an imaginary quadratic field `k`, then the
conductor of `R` is prime to `6 = disc B`.
*Published statement*: the CM points of `X₀(D, 1)` by `R` correspond to optimal embeddings
`R ↪ 𝒪` (Jordan, thesis (Harvard 1981) §3; González–Rotger, J. Math. Soc. Japan 58 (2006) §5;
locators UNVERIFIED), and an order of conductor `f` embeds optimally in the maximal order of the
quaternion division algebra over `ℚ_p` only if `p ∤ f` and `p` does not split in `k` (Vignéras,
*Arithmétique des algèbres de quaternions*, LNM 800, Ch. II §3 / Ch. III §5, theorem numbers
UNVERIFIED; for `p ∤ f`: `k ∩ 𝒪_p = 𝒪_{k,p}` because `𝒪_p` is the set of integral elements).
A consequence of the published statements (only the conductor half is kept). -/
def CMConductorCoprime6 : Prop :=
  ∀ (P : QMPair Qbar) (k : Type) [Field k] [NumberField k] [NumberField.IsTotallyComplex k],
    Module.finrank ℚ k = 2 → ∀ R : Subring k, R ≤ (integralClosure ℤ k).toSubring →
      conductor R ≠ 0 → Nonempty (com P.q ≃+* R) → Nat.Coprime (conductor R) 6

/-- **NoCM input N2 (glue; the Kummer model of `X₆ → X₆/W ≅ P¹`, rv-h-cm §2.3-2.4,
`GlueRepo.PR.fibre_iff`).** On the leaf bundle's `X₆`, for a rational value `j₀ ∉ {0, −16/27}`
of `π₆` (so `t₀ = 1 + 27 j₀/16 ∉ {0, 1, ∞}`):
(i) every `ℚ̄`-point `x` over `j₀` has residue field `ℚ(x) = ℚ(a, b)` for any `a, b ∈ ℚ̄` with
`a² = −t₀`, `b² = 3(t₀ − 1)`;
(ii) the fibre over `j₀` has (at least) four distinct `ℚ̄`-points.
*Why true* (argued; Elkies, "Shimura curve computations", ANTS-III, LNCS 1423 (1998), the curve
`X*(6)` and its double covers (section number UNVERIFIED); the constants `c₀ = −1`, `c₁ = 3` are
derived in rv-h-cm §2.3 and checked against González–Rotger Thm 5.12 on all 24 rows of Elkies'
table, rv-nocm §1.3 Part B (VERIFIED there)): `ℚ(X₆) = ℚ(t)(y₁, y₂)`, `y₁² = −t`,
`y₂² = 3(t − 1)`, with `W ≅ (ℤ/2)²` acting by the sign changes; the affine model is smooth over
`t ∉ {0, 1, ∞}`, so the points over `t₀` are `(t₀, ±a, ±b)` (four, as `ab ≠ 0`) with residue field
generated by their coordinates. On an arbitrary witness of the bundle the statement is the same
statement, transported: with the repaired `R1fpProps` the witness `Y` maps to the genuine `Y₃`
with `Φ = Φ₃ ∘ g`, `π = π₃ ∘ g` (qm-pin `phi_part`, mobius-glue), `fY` is onto `X(ℚ̄)` (`X6Surj`),
`Ψ(fY y) = [forget (Φ y)]` (`X6Props`), and a residue field is the fixed field of the Galois
stabilizer of the point, which `Ψ` matches with the stabilizer of the pair (Galois-equivariance in
`X6Props`). Glue: geometry of an explicit curve plus the identification (not compiled). -/
def X6KummerFibre : Prop :=
  ∀ (Y : Over (Spec (CommRingCat.of ℚ))) (Φ : PtEquiv Y)
    (X : Over (Spec (CommRingCat.of ℚ))) (Ψ : (fieldPt Qbar ⟶ X) ≃ Quotient (pairSetoid Qbar))
    (fY : Y ⟶ X) (π₆ : ToP1 X.left), R1R2fpFullProps Y Φ X Ψ fY π₆ →
    ∀ j₀ : ℚ, j₀ ≠ 0 → j₀ ≠ -16 / 27 →
      (∀ x : fieldPt Qbar ⟶ X, π₆.val (K := Qbar) x.left = OnePoint.some (algebraMap ℚ Qbar j₀) →
        ∀ a b : Qbar, a ^ 2 = -algebraMap ℚ Qbar (1 + 27 * j₀ / 16) →
          b ^ 2 = 3 * (algebraMap ℚ Qbar (1 + 27 * j₀ / 16) - 1) →
          residueImage (X := X.left) x.left = IntermediateField.adjoin ℚ {a, b}) ∧
      ∃ f : Fin 4 → (fieldPt Qbar ⟶ X), Function.Injective f ∧
        ∀ i, π₆.val (K := Qbar) (f i).left = OnePoint.some (algebraMap ℚ Qbar j₀)


/-! ## §D Arithmetic -/

/-- In a number field containing a square root `ι` of `−1`, the prime `2` is not inert:
`(1 + ι)² = 2ι ∈ (2)` but `(1 + ι)/2` is not integral (its fourth power is `−1/4`). -/
theorem two_not_prime_of_sqrt_neg_one {k : Type} [Field k] [NumberField k] (ι : k)
    (hι : ι ^ 2 = -1) : ¬ (Ideal.span {(2 : NumberField.RingOfIntegers k)}).IsPrime := by
  intro hP
  have hint : IsIntegral ℤ ι := by
    refine ⟨Polynomial.X ^ 2 + 1, ?_, ?_⟩
    · exact (Polynomial.monic_X_pow 2).add_of_left
        (by rw [Polynomial.degree_one, Polynomial.degree_X_pow]; norm_num)
    · simp [hι]
  let ιO : NumberField.RingOfIntegers k := ⟨ι, hint⟩
  have hsq : (1 + ιO) ^ 2 = 2 * ιO := by
    apply NumberField.RingOfIntegers.ext
    simp only [map_pow, map_add, map_one, map_mul, map_ofNat]
    change (1 + ι) ^ 2 = 2 * ι
    linear_combination hι
  have hmem : (1 + ιO) ^ 2 ∈ Ideal.span {(2 : NumberField.RingOfIntegers k)} := by
    rw [hsq]; exact Ideal.mul_mem_right _ _ (Ideal.subset_span rfl)
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.mp (hP.mem_of_pow_mem 2 hmem)
  have hck : (c : k) * 2 = 1 + ι := congrArg (fun z : NumberField.RingOfIntegers k => (z : k)) hc
  have h4 : (c : k) ^ 4 = algebraMap ℚ k (-1 / 4) := by
    have : (c : k) ^ 4 = -1 / 4 := by
      linear_combination (1 / 16 : k) * ((c * 2) ^ 3 + (c * 2) ^ 2 * (1 + ι) +
        (c * 2) * (1 + ι) ^ 2 + (1 + ι) ^ 3) * hck + (1 / 16 : k) * (ι ^ 2 + 4 * ι + 5) * hι
    rw [this]; simp
  have hI : IsIntegral ℤ (algebraMap ℚ k (-1 / 4)) := by
    rw [← h4]; exact (NumberField.RingOfIntegers.isIntegral_coe c).pow 4
  have hI' : IsIntegral ℤ (-1 / 4 : ℚ) :=
    (isIntegral_algHom_iff ((Algebra.ofId ℚ k).restrictScalars ℤ)
      (algebraMap ℚ k).injective).mp hI
  obtain ⟨n, hn⟩ := IsIntegrallyClosed.isIntegral_iff.mp hI'
  have : (n : ℚ) * 4 = -1 := by
    rw [show (n : ℚ) = algebraMap ℤ ℚ n from rfl, hn]; norm_num
  have : n * 4 = -1 := by exact_mod_cast this
  omega

/-- `[ℚ(i) : ℚ] = 2` inside `ℚ̄`. -/
theorem finrank_adjoin_sqrt_neg_one (i : Qbar) (hi : i ^ 2 = -1) :
    Module.finrank ℚ (IntermediateField.adjoin ℚ {i}) = 2 := by
  have hirr : Irreducible (Polynomial.X ^ 2 - Polynomial.C (-1 : ℚ)) :=
    X_pow_sub_C_irreducible_of_prime Nat.prime_two (fun b hb => by nlinarith [sq_nonneg b])
  have hmp : minpoly ℚ i = Polynomial.X ^ 2 - Polynomial.C (-1 : ℚ) := by
    refine (minpoly.eq_of_irreducible_of_monic hirr ?_ ?_).symm
    · simp [hi]
    · exact Polynomial.monic_X_pow_sub_C _ two_ne_zero
  have hint : IsIntegral ℚ i := Algebra.IsIntegral.isIntegral i
  rw [IntermediateField.adjoin.finrank hint, hmp, Polynomial.natDegree_X_pow_sub_C]

/-- `ℚ(i h₁, i h₂) = ℚ(i)` for rational `h₁ ≠ 0`, `h₂`. -/
theorem adjoin_pair_eq (i : Qbar) (h₁ h₂ : ℚ) (hh : h₁ ≠ 0) :
    IntermediateField.adjoin ℚ {i * algebraMap ℚ Qbar h₁, i * algebraMap ℚ Qbar h₂} =
      IntermediateField.adjoin ℚ {i} := by
  apply le_antisymm
  · rw [IntermediateField.adjoin_le_iff]
    intro z hz
    rcases hz with rfl | rfl <;>
      exact mul_mem (IntermediateField.mem_adjoin_simple_self ℚ i)
        (IntermediateField.algebraMap_mem _ _)
  · rw [IntermediateField.adjoin_simple_le_iff]
    have h0 : algebraMap ℚ Qbar h₁ ≠ 0 := by simpa using hh
    have hm : i * algebraMap ℚ Qbar h₁ ∈ IntermediateField.adjoin ℚ
        {i * algebraMap ℚ Qbar h₁, i * algebraMap ℚ Qbar h₂} :=
      IntermediateField.subset_adjoin _ _ (Set.mem_insert _ _)
    have := mul_mem hm (IntermediateField.algebraMap_mem _ (h₁⁻¹))
    rwa [map_inv₀, mul_assoc, mul_inv_cancel₀ h0, mul_one] at this

/-- The Elkies identities at `t(u)` (`GlueRepo.PR.t_eq`, `t_sub_one`), in `ℚ̄`: with `i² = −1`,
`(i H/G³)² = −t(u)` and `(i·540F/G³)² = 3(t(u) − 1)`, `t(u) = 1 + 27 J(u)/16`. -/
theorem elkies_sq (u : ℚ) (i : Qbar) (hi : i ^ 2 = -1) :
    (i * algebraMap ℚ Qbar (GlueRepo.PR.Hq u / GlueRepo.PR.Gq u ^ 3)) ^ 2 =
        -algebraMap ℚ Qbar (1 + 27 * Jmap u / 16) ∧
      (i * algebraMap ℚ Qbar (540 * GlueRepo.PR.Fq u / GlueRepo.PR.Gq u ^ 3)) ^ 2 =
        3 * (algebraMap ℚ Qbar (1 + 27 * Jmap u / 16) - 1) := by
  have ht : (1 + 27 * Jmap u / 16 : ℚ) = (GlueRepo.PR.Hq u / GlueRepo.PR.Gq u ^ 3) ^ 2 := by
    rw [div_pow, ← pow_mul]; exact GlueRepo.PR.t_eq u
  have ht1 : (1 + 27 * Jmap u / 16 : ℚ) - 1 =
      -3 * (180 * GlueRepo.PR.Fq u / GlueRepo.PR.Gq u ^ 3) ^ 2 := GlueRepo.PR.t_sub_one u
  constructor
  · rw [ht, mul_pow, hi, map_pow]; ring
  · have e : algebraMap ℚ Qbar (1 + 27 * Jmap u / 16) - 1 =
        algebraMap ℚ Qbar ((1 + 27 * Jmap u / 16 : ℚ) - 1) := by rw [map_sub, map_one]
    rw [e, ht1, mul_pow, hi]
    simp only [map_mul, map_pow, map_neg, map_div₀, map_ofNat]
    ring


/-! ## §E NoCM on the leaf's own witness, and FS5 -/

/-- **NoCM on the leaf bundle's witness** (rv-h-cm §7.2 with the corrected count of rv-nocm §1.1).
Let `y` be a `ℚ̄`-point of the witness `Y` over `J(u)`, `u ∉ 𝒞`, with object `P`, and
`x = fY(y) ∈ X₆`. If `End_𝒪(P.A) ≅ R` were an order of an imaginary quadratic `k` (N1a), its
conductor is prime to 6 (N1b). The residue field of `x` is `ℚ(i)` (N2 (i) with the Elkies
identities), so R5 (`R5ptProps`) gives `2 = h(R)` if `b(k) = 0`, and `2 = 2h(R)` with
`k ↪ ℚ(i)` if `b(k) ≥ 1`; in the second case `k ≅ ℚ(i)`, where `2` ramifies, so `b(k) = 1`.
Either way `#CM(R) = 2^{b(k)} h(R) = 2` (R5fpCount). But the four points of the fibre over
`J(u)` (N2 (ii)) are pairwise distinct points of `X₆`, hence (`Ψ` bijective) four distinct
classes, and each is an `Aut(𝒪)`-twist of `P` (`R2X6Props`), hence CM by `R` (`com_twist`,
`comEquiv`): `#CM(R) ≥ 4`. Contradiction; so `End_𝒪(P.A) = ℤ`. -/
theorem nocm_on_witness (hA : ComIntOrQuadOrder) (hB : CMConductorCoprime6)
    (hK : X6KummerFibre) (hC : R5fpCount)
    {Y : Over (Spec (CommRingCat.of ℚ))} {Φ : PtEquiv Y}
    {X : Over (Spec (CommRingCat.of ℚ))} {Ψ : (fieldPt Qbar ⟶ X) ≃ Quotient (pairSetoid Qbar)}
    {fY : Y ⟶ X} {π₆ : ToP1 X.left} (hW : R1R2fpFullProps Y Φ X Ψ fY π₆)
    (u : ℚ) (hu : u ∉ contactSet) (y : fieldPt Qbar ⟶ Y) (P : QML3 Qbar)
    (hP : Φ Qbar y = M3.mk P)
    (hv : (π₆.comp fY.left).val (K := Qbar) y.left =
      OnePoint.some (algebraMap ℚ Qbar (Jmap u))) :
    ∀ φ ∈ com P.q, ∃ n : ℤ, φ = (n : AbVar.End P.A) := by
  obtain ⟨h1, hh, hX, h2, hE, hrec, hS, h5⟩ := hW
  have hx : Ψ (y ≫ fY) = Quotient.mk _ P.forget := hX.2.2.2.2.2 y P hP
  have hv' : π₆.val (K := Qbar) (y ≫ fY).left =
      OnePoint.some (algebraMap ℚ Qbar (Jmap u)) := by
    exact (ToP1.val_comp_right π₆ fY.left y.left).symm.trans hv
  rcases hA P.forget with hZ | ⟨k, _, _, _, hk2, R, hR, hc0, ⟨e⟩⟩
  · exact hZ
  exfalso
  have hcop : Nat.Coprime (conductor R) 6 := hB P.forget k hk2 R hR hc0 ⟨e⟩
  obtain ⟨hdeg, hemb⟩ := h5 k hk2 R hR hcop (y ≫ fY) P.forget hx ⟨e⟩
  -- the fibre over `J(u)` (N2) and its residue field `ℚ(i)`
  obtain ⟨hres, f, hf, hfv⟩ := hK Y Φ X Ψ fY π₆ ⟨h1, hh, hX, h2, hE, hrec, hS, h5⟩ (Jmap u)
    (GlueRepo.PR.J_ne_zero hu) (GlueRepo.PR.J_ne_branch u)
  obtain ⟨i, hi⟩ := IsAlgClosed.exists_pow_nat_eq (-1 : Qbar) two_pos
  obtain ⟨ha, hb⟩ := elkies_sq u i hi
  have hresEq : residueImage (X := X.left) (y ≫ fY).left = IntermediateField.adjoin ℚ {i} := by
    rw [hres _ hv' _ _ ha hb]
    exact adjoin_pair_eq i _ _ (GlueRepo.PR.h₁_ne_zero u)
  have hfin : Module.finrank ℚ (residueImage (X := X.left) (y ≫ fY).left) = 2 := by
    rw [hresEq]; exact finrank_adjoin_sqrt_neg_one i hi
  rw [hfin] at hdeg
  -- four distinct classes with CM by `R`
  have hcount := hC k hk2 R hR hcop ⟨P.forget, ⟨e⟩⟩
  have hmemS : ∀ j : Fin 4, ∃ P' : QMPair Qbar, Quotient.mk _ P' = Ψ (f j) ∧
      Nonempty (com P'.q ≃+* R) := by
    intro j
    refine ⟨Quotient.out (Ψ (f j)), Quotient.out_eq _, ?_⟩
    have hQ : Ψ (f j) = Quotient.mk _ (Quotient.out (Ψ (f j))) := (Quotient.out_eq _).symm
    obtain ⟨α, ⟨g⟩⟩ := ((h2 (y ≫ fY) (f j) P.forget _ hx hQ).1).1 (hv'.trans (hfv j).symm)
    exact ⟨((comEquiv g).symm.trans (RingEquiv.subringCongr (com_twist P.forget.q α))).trans e⟩
  let F : Fin 4 → {c : Quotient (pairSetoid Qbar) //
      ∃ P' : QMPair Qbar, Quotient.mk _ P' = c ∧ Nonempty (com P'.q ≃+* R)} :=
    fun j => ⟨Ψ (f j), hmemS j⟩
  have hFinj : Function.Injective F := fun a b hab =>
    hf (Ψ.injective (congrArg Subtype.val hab))
  -- `#CM(R) = 2`
  have hcard2 : Nat.card {c : Quotient (pairSetoid Qbar) //
      ∃ P' : QMPair Qbar, Quotient.mk _ P' = c ∧ Nonempty (com P'.q ≃+* R)} = 2 := by
    rw [hcount]
    by_cases hb0 : inertCount6 k = 0
    · simp only [hb0, ↓reduceIte] at hdeg
      rw [hb0]; omega
    · simp only [hb0, ↓reduceIte] at hdeg
      have hh1 : Nat.card (CommRing.Pic R) = 1 := by omega
      obtain ⟨e'⟩ := hemb hb0
      have hik : i ∈ residueImage (X := X.left) (y ≫ fY).left := by
        rw [hresEq]; exact IntermediateField.mem_adjoin_simple_self ℚ i
      have : FiniteDimensional ℚ (residueImage (X := X.left) (y ≫ fY).left) :=
        Module.finite_of_finrank_pos (by rw [hfin]; norm_num)
      have hsurj : Function.Surjective e'.toLinearMap := by
        rw [← LinearMap.injective_iff_surjective_of_finrank_eq_finrank (by rw [hk2, hfin])]
        exact e'.toRingHom.injective
      obtain ⟨ι, hι⟩ := hsurj ⟨i, hik⟩
      have hι2 : ι ^ 2 = -1 := by
        apply e'.toRingHom.injective
        change e' (ι ^ 2) = e' (-1)
        rw [map_pow, map_neg, map_one]
        have : e' ι = ⟨i, hik⟩ := hι
        rw [this]
        apply Subtype.ext
        simp [hi]
      have h2n := two_not_prime_of_sqrt_neg_one ι hι2
      have hb1 : inertCount6 k = 1 := by
        have : inertCount6 k ≤ 1 := by
          unfold inertCount6
          simp only [h2n, ↓reduceIte]
          split_ifs <;> omega
        omega
      rw [hb1, hh1]; norm_num
  have hfinS : Finite {c : Quotient (pairSetoid Qbar) //
      ∃ P' : QMPair Qbar, Quotient.mk _ P' = c ∧ Nonempty (com P'.q ≃+* R)} :=
    Nat.finite_of_card_ne_zero (by rw [hcard2]; norm_num)
  have := Nat.card_le_card_of_injective F hFinj
  rw [hcard2, Nat.card_eq_fintype_card, Fintype.card_fin] at this
  omega

/-- **FS5 for the leaf's own triple, from NoCM's inputs.** -/
theorem fibreComTrivialOwn_of (hA : ComIntOrQuadOrder) (hB : CMConductorCoprime6)
    (hK : X6KummerFibre) (hC : R5fpCount) : FibreComTrivialOwn :=
  fun _ _ _ _ _ _ hW u hu y P hP hv => nocm_on_witness hA hB hK hC hW u hu y P hP hv

/-- **From the leaf's own triple to every triple** (qm-pin's `pointwise_of_witness_mor`, with
`MobiusGlue` and the CM objects of the bundle, `cm_objects_of_R1R2fp`). -/
theorem fibreComTrivialFull_of_own (hL : R1R2fpFull) (hM : MobiusGlue)
    (hO : FibreComTrivialOwn) : FibreComTrivialFull := by
  obtain ⟨Y₀, Φ₀, X, Ψ, fY, π₆, hW⟩ := hL
  have hCM := cm_objects_of_R1R2fp (R1R2fp_of_full ⟨Y₀, Φ₀, X, Ψ, fY, π₆, hW⟩)
  have h1 : R1fpPropsU Y₀ Φ₀ := (r1fpPropsFull_iff _ _).1 hW.1
  have h2 : R2fpProps Y₀ Φ₀ (π₆.comp fY.left) := R2fpProps_of_X6 hW.2.2.1 hW.2.2.2.1
  have key := pointwise_of_witness_mor hM hCM h1 h2
    (fun t P => ∀ u : ℚ, u ∉ contactSet → t = OnePoint.some (algebraMap ℚ Qbar (Jmap u)) →
      ∀ φ ∈ com P.q, ∃ n : ℤ, φ = (n : AbVar.End P.A))
    (fun t y P hP ht u hu htu => hO Y₀ Φ₀ X Ψ fY π₆ hW u hu y P hP (ht.trans htu))
  intro Y Φ π h1' h2' u hu y P hP hv
  exact key Y Φ π ((r1fpPropsFull_iff _ _).1 h1') h2' _ y P hP hv u hu rfl

/-- **FS5 with the repaired QM clauses, proved** from the leaf bundle (after qm-pin's full edit),
`MobiusGlue` (proved by mobius-glue from `CurveRatFactor`, `CurveSurj` and T5), N1a, N1b, N2 and
the leaf R5fpCount. -/
theorem fibreComTrivialFull_of (hL : R1R2fpFull) (hM : MobiusGlue) (hA : ComIntOrQuadOrder)
    (hB : CMConductorCoprime6) (hK : X6KummerFibre) (hC : R5fpCount) :
    FibreComTrivialFull :=
  fibreComTrivialFull_of_own hL hM (fibreComTrivialOwn_of hA hB hK hC)

end FS5NoCM

#print axioms FS5NoCM.two_not_prime_of_sqrt_neg_one
#print axioms FS5NoCM.finrank_adjoin_sqrt_neg_one
#print axioms FS5NoCM.elkies_sq
#print axioms FS5NoCM.nocm_on_witness
#print axioms FS5NoCM.fibreComTrivialOwn_of
#print axioms FS5NoCM.fibreComTrivialFull_of_own
#print axioms FS5NoCM.fibreComTrivialFull_of
