import ZInQKernel.HDecomp.QM.Leaves

/-! Glue of `docs/research/h-decomposition.md`, task qm-pin (`docs/research/qm-pin.md`),
integrated by task pin-apply: the comparison of two triples `(Y, Φ, π)` satisfying the repaired
QM clause lists (`R1famProps`, `R1univProps` in `R1fpProps`), the re-run of rv-g0pieces'
relabeling attack (`r1fpPin_relabel_iff`), and the reduction of pointwise statements to the
leaf's own triple (`pointwise_of_witness_mor`, modulo the named curve glue `MobiusGlue`).
No `sorry`, no `axiom`. -/

noncomputable section

namespace LeafQM

namespace AV

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open PkgI3

variable {K : Type} [Field K]

namespace Pin

/-! ## §3 The relabeling attack, re-run

`relabel Φ τ` and `IsNaturalRelabel` are rv-g0pieces' definitions (copied). Candidate content of
a new kernel module `ZInQKernel/HDecomp/QM/Pin.lean` (task qm-pin), after the full patch. -/

theorem R1fpProps.fam {Y : Over (Spec (CommRingCat.of ℚ))} {Φ : PtEquiv Y}
    (h : R1fpProps Y Φ) : R1famProps Y Φ :=
  h.2.2.2.2.1

theorem R1fpProps.univ {Y : Over (Spec (CommRingCat.of ℚ))} {Φ : PtEquiv Y}
    (h : R1fpProps Y Φ) : R1univProps Y Φ :=
  h.2.2.2.2.2


/-- (rv-g0pieces) A family of bijections of the field points of `Y`, natural in the field. -/
def IsNaturalRelabel (Y : Over (Spec (CommRingCat.of ℚ)))
    (τ : ∀ (K : Type) [Field K] [Algebra ℚ K], (fieldPt K ⟶ Y) ≃ (fieldPt K ⟶ Y)) : Prop :=
  ∀ (K L : Type) [Field K] [Field L] [Algebra ℚ K] [Algebra ℚ L] (f : K →ₐ[ℚ] L)
    (y : fieldPt K ⟶ Y), τ L (fieldMap f ≫ y) = fieldMap f ≫ τ K y

/-- (rv-g0pieces) `Φ` precomposed with a relabeling `τ`. -/
def relabel {Y : Over (Spec (CommRingCat.of ℚ))} (Φ : PtEquiv Y)
    (τ : ∀ (K : Type) [Field K] [Algebra ℚ K], (fieldPt K ⟶ Y) ≃ (fieldPt K ⟶ Y)) : PtEquiv Y :=
  fun K _ _ => (τ K).trans (Φ K)

/-- **What survives of rv-g0pieces' `r1fp_relabel`** (full list). A natural relabeling keeps the
repaired clause list iff some family `𝒜'` over `Y` has the object of `τ y` as its fibre at every
`y`, and the relabeled `Φ` still classifies families. -/
theorem r1fpPin_relabel_iff {Y : Over (Spec (CommRingCat.of ℚ))} {Φ : PtEquiv Y}
    {τ : ∀ (K : Type) [Field K] [Algebra ℚ K], (fieldPt K ⟶ Y) ≃ (fieldPt K ⟶ Y)}
    (h : R1fpProps Y Φ) (hτ : IsNaturalRelabel Y τ) :
    R1fpProps Y (relabel Φ τ) ↔
      (∃ 𝒜' : QMFamily Y.left, ∀ (K : Type) [Field K] [Algebra ℚ K] (y : fieldPt K ⟶ Y)
        (P : QML3 K), Φ K (τ K y) = M3.mk P → IsFibreOf 𝒜' y.left P) ∧
      R1univProps Y (relabel Φ τ) := by
  constructor
  · intro h'
    exact ⟨R1fpProps.fam h', R1fpProps.univ h'⟩
  · rintro ⟨hf, hu⟩
    obtain ⟨hp, hs, hpt, hnat, -, -⟩ := h
    refine ⟨hp, hs, hpt, ?_, hf, hu⟩
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
    IsFibreOf (QMFamily.transport 𝒜 g) y P := by
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
published theorem does): relabeling by an automorphism of `Y` keeps `R1fpProps`. -/
theorem r1fpPin_aut {Y : Over (Spec (CommRingCat.of ℚ))} {Φ : PtEquiv Y}
    (h : R1fpProps Y Φ) (g : Y ≅ Y) : R1fpProps Y (relabel Φ (autRelabel g)) := by
  refine (r1fpPin_relabel_iff h (autRelabel_natural g)).2 ⟨?_, ?_⟩
  · obtain ⟨𝒜, h𝒜⟩ := R1fpProps.fam h
    refine ⟨QMFamily.transport 𝒜 ((Over.forget _).mapIso g), fun K _ _ y P hP => ?_⟩
    apply isFibreOf_transport
    exact h𝒜 K (y ≫ g.hom) P hP
  · intro S hp hs 𝒜' hall
    obtain ⟨g', hg'⟩ := R1fpProps.univ h S hp hs 𝒜' hall
    refine ⟨g' ≫ g.inv, fun K _ _ s P hP => ?_⟩
    show Φ K ((s ≫ g' ≫ g.inv) ≫ g.hom) = M3.mk P
    rw [Category.assoc, Category.assoc, Iso.inv_hom_id, Category.comp_id]
    exact hg' K s P hP

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
    R1fpProps Y Φ → R2fpProps Y Φ π → R1fpProps Y' Φ' → R2fpProps Y' Φ' π' →
      SameTriple Y Y' Φ Φ' π π'

/-- **Under `PinUnique`, a fibre statement for one triple is a fibre statement for all**: the
universal quantifier over `(Y, Φ, π)` in g0-split's three pieces costs nothing beyond the
statement for the leaf's own triple. -/
theorem pointwise_of_witness (hU : PinUnique) {Y₀ : Over (Spec (CommRingCat.of ℚ))}
    {Φ₀ : PtEquiv Y₀} {π₀ : ToP1 Y₀.left} (h1 : R1fpProps Y₀ Φ₀) (h2 : R2fpProps Y₀ Φ₀ π₀)
    (R : OnePoint Qbar → QML3 Qbar → Prop)
    (h : ∀ t (y : fieldPt Qbar ⟶ Y₀) (P : QML3 Qbar), Φ₀ Qbar y = M3.mk P →
      π₀.val (K := Qbar) y.left = t → R t P) :
    ∀ (Y : Over (Spec (CommRingCat.of ℚ))) (Φ : PtEquiv Y) (π : ToP1 Y.left),
      R1fpProps Y Φ → R2fpProps Y Φ π →
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
    (h1 : R1fpProps Y Φ) (h2 : R2fpProps Y Φ π)
    (h1' : R1fpProps Y (relabel Φ τ)) (h2' : R2fpProps Y (relabel Φ τ) π') :
    ∃ g : Y ≅ Y, (∀ (K : Type) [Field K] [Algebra ℚ K] (y : fieldPt K ⟶ Y), τ K y = y ≫ g.hom) ∧
      ∀ y : fieldPt Qbar ⟶ Y, π'.val (K := Qbar) y.left = π.val (K := Qbar) (y ≫ g.hom).left := by
  obtain ⟨g, hΦ, hπ⟩ := hU Y Y Φ (relabel Φ τ) π π' h1 h2 h1' h2'
  exact ⟨g, fun K _ _ y => (Φ K).injective (hΦ K y), hπ⟩

/-! ## §4 Optional strengthening for provability: the universal property on families

`PinUnique` needs R1(a)'s universal property, which the leaf does not carry. The clause
`R1univProps` carries it on families over proper smooth curves (all the comparison needs). With
it, the `Φ`-half of the comparison is compiled (`phi_part`), and what remains is
`MobiusGlue` (a morphism of curves `Y' → P¹` with the fibres and the three values of `π ∘ g` is
`π ∘ g`): algebraic geometry of curves, glue, not a leaf. -/

/-- **The `Φ`-half of the comparison (compiled).** If `(Y, Φ)` has the universal property and
`(Y', Φ')` satisfies the repaired clause list, then `Φ' = Φ ∘ g` for a morphism `g : Y' → Y`. -/
theorem phi_part {Y Y' : Over (Spec (CommRingCat.of ℚ))} {Φ : PtEquiv Y} {Φ' : PtEquiv Y'}
    (hU : R1univProps Y Φ) (h1' : R1fpProps Y' Φ') :
    ∃ g : Y' ⟶ Y, ∀ (K : Type) [Field K] [Algebra ℚ K] (y : fieldPt K ⟶ Y'),
      Φ' K y = Φ K (y ≫ g) := by
  obtain ⟨hp', hs', -, -, ⟨𝒜', h𝒜'⟩, -⟩ := h1'
  have hall : ∀ (K : Type) [Field K] [Algebra ℚ K] (s : fieldPt K ⟶ Y'), ∃ P : QML3 K,
      IsFibreOf 𝒜' s.left P :=
    fun K _ _ s => ⟨Quotient.out (Φ' K s), h𝒜' K s _ (Quotient.out_eq _).symm⟩
  obtain ⟨g, hg⟩ := hU Y' hp' hs' 𝒜' hall
  refine ⟨g, fun K _ _ y => ?_⟩
  rw [hg K y _ (h𝒜' K y _ (Quotient.out_eq _).symm)]
  exact (Quotient.out_eq _).symm

/-- **Every relabeling that survives the repaired clauses is a morphism on points** (pin-apply,
compiled; no `MobiusGlue`): if `Φ` and the relabeled `Φ ∘ τ` both satisfy `R1fpProps`, then
`τ_K(y) = y ≫ g` for one morphism `g : Y → Y`, on field points over every field. With the old
clauses any natural relabeling survived (rv-g0pieces `r1fp_relabel`, `r1fp_exotic`). -/
theorem relabel_is_morphism {Y : Over (Spec (CommRingCat.of ℚ))} {Φ : PtEquiv Y}
    {τ : ∀ (K : Type) [Field K] [Algebra ℚ K], (fieldPt K ⟶ Y) ≃ (fieldPt K ⟶ Y)}
    (h : R1fpProps Y Φ) (h' : R1fpProps Y (relabel Φ τ)) :
    ∃ g : Y ⟶ Y, ∀ (K : Type) [Field K] [Algebra ℚ K] (y : fieldPt K ⟶ Y), τ K y = y ≫ g := by
  obtain ⟨g, hg⟩ := phi_part (R1fpProps.univ h) h'
  exact ⟨g, fun K _ _ y => (Φ K).injective (hg K y)⟩

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
    R1fpProps Y Φ → R2fpProps Y Φ π → R1fpProps Y' Φ' → R2fpProps Y' Φ' π' →
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
    (h1 : R1fpProps Y Φ) (h2 : R2fpProps Y Φ π) (h1' : R1fpProps Y' Φ')
    (h2' : R2fpProps Y' Φ' π') : SameTripleMor Y Y' Φ Φ' π π' := by
  obtain ⟨g, hg⟩ := phi_part (R1fpProps.univ h1) h1'
  exact ⟨g, hg, hM Y Y' Φ Φ' π π' g h1 h2 h1' h2' hCM hg⟩

/-- **Pieces from the witness, with `R1univProps` (compiled).** A fibre statement proved for one
triple satisfying the fully repaired list holds for every such triple, given `MobiusGlue` and CM
objects (the latter from the leaves: `CMExists` and `X6Surj`). -/
theorem pointwise_of_witness_mor (hM : MobiusGlue)
    (hCM : (∃ P : QML3 Qbar, HasCM4 P.q) ∧ (∃ P : QML3 Qbar, HasCM3 P.q) ∧
      (∃ P : QML3 Qbar, HasCM24 P.q))
    {Y₀ : Over (Spec (CommRingCat.of ℚ))} {Φ₀ : PtEquiv Y₀} {π₀ : ToP1 Y₀.left}
    (h1 : R1fpProps Y₀ Φ₀) (h2 : R2fpProps Y₀ Φ₀ π₀)
    (R : OnePoint Qbar → QML3 Qbar → Prop)
    (h : ∀ t (y : fieldPt Qbar ⟶ Y₀) (P : QML3 Qbar), Φ₀ Qbar y = M3.mk P →
      π₀.val (K := Qbar) y.left = t → R t P) :
    ∀ (Y : Over (Spec (CommRingCat.of ℚ))) (Φ : PtEquiv Y) (π : ToP1 Y.left),
      R1fpProps Y Φ → R2fpProps Y Φ π →
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
