import ZInQKernel.Contrib.OneProof.Y3ToP1j
import ZInQKernel.Contrib.OneProof.RayClassShimura
import ZInQKernel.Contrib.OneProof.Y3HodgePrint
import ZInQKernel.Contrib.OneProof.Y3FullThreeZ30

/-!
# Matching the moduli witness: reciprocity and the fibre count on the same `(Y, Φ, π)`

The CM branch quantifies over every witness `(Y, Φ, π)` of the moduli clauses (`R1fpProps Y Φ`,
`R2fpProps Y Φ π`). The class-number bound needs, for that same witness,

1. a set of `ℚ̄`-points of `Y` containing the CM point `y`, with at most `324` elements, and stable under
   the Galois action on `ℂ`-points (the orbit of `y` under reciprocity must stay inside it);
2. the uniformization `Ψ` of Deligne's canonical model for that same `(Y, Φ)`.

For 2, the leaf `DeligneCanonicalModelY3EveryPrint` gives `Ψ` only for witnesses of the printed clause
list `R1fpPropsAbP` (a universal abelian scheme), and the leaf `Y3FullThreeRepZ30` provides one such
witness `(Y', Φ')`. The universal property of `(Y, Φ)` (part of `R1fpProps`), applied to the universal
family of `Y'`, gives `g : Y' → Y` with `Φ(s ∘ g) = Φ'(s)` on points over every field; `Φ` and `Φ'` are
bijections, so `g` is bijective on points over every field, and `Ψ := g ∘ Ψ'` keeps every clause the
class-number bound uses: onto, the double-coset fibres, reciprocity (the Galois action is precomposition,
so it commutes with `g`), and the moduli clause at units (`DeligneCore.map`, `exists_deligneCore`).

For 1, take the `π`-fibre through `y`. The leaf `Y3ToP1j` gives, for the witness `(Y, Φ)`, *some*
`π'` whose fibres have at most `324` points; the quotient clause, shared by `R2fpProps Y Φ π` and
`Y3ToP1jAt Y Φ π'`, says that two points lie in the same `π`-fibre exactly when their QM pairs are
`Aut(𝒪)`-twists of each other, which is also the `π'`-fibre condition. So `π` and `π'` have the same
fibres (`fibre_eq`), and the bound passes to `π` (`fibre_finite_le_324`). The fibre over a rational
value is stable under `Gal(ℚ̄/ℚ)` because `π` is defined over `ℚ` (`ToP1.val_comp`), and every
automorphism of `ℂ` restricts to `ℚ̄` (`exists_restrict_qbar`), which moves `ℂ`-points coming from
`ℚ̄`-points as on `ℚ̄` (`galPt_fieldMap`).
-/

noncomputable section

namespace HDec.CMBranch.CMjReroute

open CategoryTheory AlgebraicGeometry Limits
open _root_.LeafQM _root_.LeafQM.AV ShimuraCFT RayClassCFT

section Fibre

variable {Y : Over (Spec (CommRingCat.of ℚ))} {Φ : PtEquiv Y}

/-- The quotient clause shared by `R2fpProps` and `Y3ToP1jAt`. -/
def QuotClause (Y : Over (Spec (CommRingCat.of ℚ))) (Φ : PtEquiv Y) (π : ToP1 Y.left) : Prop :=
  ∀ (y y' : fieldPt Qbar ⟶ Y) (P Q : QML3 Qbar), Φ Qbar y = M3.mk P → Φ Qbar y' = M3.mk Q →
    (π.val (K := Qbar) y.left = π.val (K := Qbar) y'.left ↔
      ∃ α : O ≃+* O, Nonempty (QMIso (P.q.twist α) Q.q))

theorem quotClause_of_R2 {π : ToP1 Y.left} (h : R2fpProps Y Φ π) : QuotClause Y Φ π :=
  fun y y' P Q hP hQ => (h y y' P Q hP hQ).1

theorem quotClause_of_at {π : ToP1 Y.left} (h : Y3P1j.Y3ToP1jAt Y Φ π) : QuotClause Y Φ π :=
  fun y y' P Q hP hQ => (h.1 y y' P Q hP hQ).1

/-- **Two maps to `P¹` with the quotient clause have the same fibres.** -/
theorem fibre_eq {π π' : ToP1 Y.left} (h : QuotClause Y Φ π) (h' : QuotClause Y Φ π')
    (y : fieldPt Qbar ⟶ Y) :
    {y' : fieldPt Qbar ⟶ Y | π.val (K := Qbar) y'.left = π.val (K := Qbar) y.left} =
      {y' : fieldPt Qbar ⟶ Y | π'.val (K := Qbar) y'.left = π'.val (K := Qbar) y.left} := by
  ext y'
  obtain ⟨P, hP⟩ := Quotient.exists_rep (Φ Qbar y)
  obtain ⟨Q, hQ⟩ := Quotient.exists_rep (Φ Qbar y')
  simp only [Set.mem_ofPred_eq]
  rw [eq_comm (a := π.val (K := Qbar) y'.left), eq_comm (a := π'.val (K := Qbar) y'.left),
    h y y' P Q hP.symm hQ.symm, h' y y' P Q hP.symm hQ.symm]

/-- **The fibre bound for the witness's own `π`.** -/
theorem fibre_finite_le_324 (hY : Y3P1j.Y3ToP1j) (hR1 : R1fpProps Y Φ) {π : ToP1 Y.left}
    (hR2 : R2fpProps Y Φ π) (y : fieldPt Qbar ⟶ Y) :
    {y' : fieldPt Qbar ⟶ Y | π.val (K := Qbar) y'.left = π.val (K := Qbar) y.left}.Finite ∧
      {y' : fieldPt Qbar ⟶ Y | π.val (K := Qbar) y'.left = π.val (K := Qbar) y.left}.ncard ≤
        324 := by
  obtain ⟨π', hπ'⟩ := hY Y Φ hR1
  rw [fibre_eq (quotClause_of_R2 hR2) (quotClause_of_at hπ') y]
  exact hπ'.2.2 _

end Fibre

/-! ## Galois stability of a fibre over a rational value -/

section Galois

variable {Y : Over (Spec (CommRingCat.of ℚ))}

/-- `π` is defined over `ℚ`: a rational value is fixed by `σ ∈ Gal(ℚ̄/ℚ)`. -/
theorem val_fieldMap_of_rat (π : ToP1 Y.left) (σ : Qbar →ₐ[ℚ] Qbar) (y : fieldPt Qbar ⟶ Y)
    (r : ℚ) (hy : π.val (K := Qbar) y.left = OnePoint.some (algebraMap ℚ Qbar r)) :
    π.val (K := Qbar) (fieldMap σ ≫ y).left = OnePoint.some (algebraMap ℚ Qbar r) := by
  rw [Over.comp_left, fieldMap_left]
  have h := ToP1.val_comp π ((σ : Qbar →ₐ[ℚ] Qbar) : Qbar →+* Qbar)
    (y.left : Spec (CommRingCat.of Qbar) ⟶ Y.left)
  rw [hy] at h
  refine h.trans ?_
  simp

/-- Every automorphism of `ℂ` restricts to an automorphism of `ℚ̄` (through `ιC`). -/
theorem exists_restrict_qbar (σC : ℂ ≃+* ℂ) :
    ∃ σ : Qbar ≃ₐ[ℚ] Qbar, ∀ a, σC (ιC a) = ιC (σ a) := by
  obtain ⟨g, hg⟩ := exists_lift_ringHom ((σC : ℂ →+* ℂ).comp (ιC : Qbar →+* ℂ))
  let gA : Qbar →ₐ[ℚ] Qbar := g.toRatAlgHom
  have hbij : Function.Bijective gA := Algebra.IsAlgebraic.algHom_bijective gA
  refine ⟨AlgEquiv.ofBijective gA hbij, fun a => ?_⟩
  rw [AlgEquiv.ofBijective_apply]
  exact (hg a).symm

/-- **The fibre over a rational value is stable under `Aut(ℂ)` acting on `ℂ`-points.** -/
theorem galPt_mem_fibre (π : ToP1 Y.left) (r : ℚ) (σC : ℂ ≃+* ℂ) (y : fieldPt Qbar ⟶ Y)
    (hy : π.val (K := Qbar) y.left = OnePoint.some (algebraMap ℚ Qbar r)) :
    ∃ y' : fieldPt Qbar ⟶ Y, π.val (K := Qbar) y'.left = OnePoint.some (algebraMap ℚ Qbar r) ∧
      galPt σC (fieldMap ιC ≫ y) = fieldMap ιC ≫ y' := by
  obtain ⟨σ, hσ⟩ := exists_restrict_qbar σC
  exact ⟨fieldMap (σ : Qbar →ₐ[ℚ] Qbar) ≫ y, val_fieldMap_of_rat π _ y r hy,
    galPt_fieldMap y σ σC hσ⟩

end Galois

/-! ## The matched witness: a finite, Galois-stable set of at most `324` points through `y` -/

/-- **Witness matching, fibre side.** For the moduli data `(Y, Φ, π)` of the CM branch and a
`ℚ̄`-point `y` over a rational value `J(u)`, the `π`-fibre through `y` is a finite set of at most
`324` `ℚ̄`-points, containing `y`, and stable under the action of `Aut(ℂ)` on `ℂ`-points. -/
theorem matched_fibre (hY : Y3P1j.Y3ToP1j) {Y : Over (Spec (CommRingCat.of ℚ))} {Φ : PtEquiv Y}
    {π : ToP1 Y.left} (hR1 : R1fpProps Y Φ) (hR2 : R2fpProps Y Φ π) (r : ℚ)
    (y : fieldPt Qbar ⟶ Y) (hy : π.val (K := Qbar) y.left = OnePoint.some (algebraMap ℚ Qbar r)) :
    ∃ S : Set (fieldPt Qbar ⟶ Y), y ∈ S ∧ S.Finite ∧ S.ncard ≤ 324 ∧
      ∀ σC : ℂ ≃+* ℂ, ∀ y' ∈ S, ∃ y'' ∈ S, galPt σC (fieldMap ιC ≫ y') = fieldMap ιC ≫ y'' := by
  obtain ⟨hfin, hcard⟩ := fibre_finite_le_324 hY hR1 hR2 y
  refine ⟨{y' : fieldPt Qbar ⟶ Y | π.val (K := Qbar) y'.left = π.val (K := Qbar) y.left}, rfl, hfin,
    hcard, fun σC y' hy' => ?_⟩
  have hy'' : π.val (K := Qbar) y'.left = OnePoint.some (algebraMap ℚ Qbar r) := hy'.trans hy
  obtain ⟨y'', h1, h2⟩ := galPt_mem_fibre π r σC y' hy''
  exact ⟨y'', h1.trans hy.symm, h2⟩


/-! ## Deligne's uniformization for the CM branch's own witness -/

section Deligne

open NumberField IsDedekindDomain

/-- **The clauses of Deligne's uniformization used by the class-number bound**: onto, fibres the
double cosets `B^× \ (ℍ^± × G(𝔸_f) / K₃)`, Shimura's reciprocity law at CM points, and the moduli
clause at units. -/
structure DeligneCore (Y : Over (Spec (CommRingCat.of ℚ))) (Φ : PtEquiv Y)
    (Ψ : Y3Hodge.HPM → BAQˣ → (fieldPt ℂ ⟶ Y)) : Prop where
  onto : ∀ y : fieldPt ℂ ⟶ Y, ∃ z g, Ψ z g = y
  fibre : ∀ z g z' g', Ψ z g = Ψ z' g' ↔ Y3Hodge.DCRelPM z g z' g'
  recip : ∃ (ε : ℤˣ) (δ : Bool),
      ∀ (K : Type) [Field K] [NumberField K] [IsTotallyComplex K], Module.finrank ℚ K = 2 →
      ∀ (κ : K →+* ℂ) (q : K →ₐ[ℚ] LeafQM.B) (z : UpperHalfPlane),
        IsCMPoint q (if δ then κ else (starRingEnd ℂ).comp κ) z →
      ∀ (σ : ℂ ≃+* ℂ) (s : IdeleGroup (𝓞 K) K), ArtinCondC κ σ s →
      ∀ g : BAQˣ, galPt σ (Ψ (Y3Hodge.toPM z) g) = Ψ (Y3Hodge.toPM z) (qHatU q s ^ (ε : ℤ) * g)
  units : Y3Hodge.ModuliAtUnitsHP Y Φ Ψ

theorem DeligneCore.of_body {Y : Over (Spec (CommRingCat.of ℚ))} {Φ : PtEquiv Y}
    {Ψ : Y3Hodge.HPM → BAQˣ → (fieldPt ℂ ⟶ Y)} (hb : Y3Hodge.DeligneBodyAtPM Y Φ Ψ)
    (hU : Y3Hodge.ModuliAtUnitsHP Y Φ Ψ) : DeligneCore Y Φ Ψ :=
  ⟨hb.1, hb.2.1, hb.2.2.2.2, hU⟩

/-- **Transport along a moduli-compatible morphism** `g : Y' → Y` (`Φ(s ∘ g) = Φ'(s)`). -/
theorem DeligneCore.map {Y Y' : Over (Spec (CommRingCat.of ℚ))} {Φ : PtEquiv Y} {Φ' : PtEquiv Y'}
    {Ψ' : Y3Hodge.HPM → BAQˣ → (fieldPt ℂ ⟶ Y')} (hc : DeligneCore Y' Φ' Ψ') (gY : Y' ⟶ Y)
    (hg : ∀ (K : Type) [Field K] [Algebra ℚ K] (s : fieldPt K ⟶ Y'), Φ K (s ≫ gY) = Φ' K s) :
    DeligneCore Y Φ (fun z g => Ψ' z g ≫ gY) where
  onto y := by
    obtain ⟨s, hs⟩ := (Φ' ℂ).surjective (Φ ℂ y)
    obtain ⟨z, g, rfl⟩ := hc.onto s
    exact ⟨z, g, (Φ ℂ).injective (by rw [hg, hs])⟩
  fibre z g z' g' := by
    rw [← hc.fibre]
    constructor
    · intro h
      apply (Φ' ℂ).injective
      rw [← hg, ← hg]
      exact congrArg (Φ ℂ) h
    · intro h
      show Ψ' z g ≫ gY = Ψ' z' g' ≫ gY
      rw [h]
  recip := by
    obtain ⟨ε, δ, h⟩ := hc.recip
    refine ⟨ε, δ, fun K _ _ _ hK κ q z hz σ s hs g => ?_⟩
    have e := h K hK κ q z hz σ s hs g
    show fieldMap (σ : ℂ →+* ℂ).toRatAlgHom ≫ (Ψ' (Y3Hodge.toPM z) g ≫ gY) =
      Ψ' (Y3Hodge.toPM z) (qHatU q s ^ (ε : ℤ) * g) ≫ gY
    rw [← Category.assoc]
    exact congrArg (· ≫ gY) e
  units u hu τ := by
    obtain ⟨P, hP, hH⟩ := hc.units u hu τ
    exact ⟨P, (hg ℂ _).trans hP, hH⟩

/-- **The moduli map from a printed witness to the CM branch's witness.** The universal property of
`(Y, Φ)` applied to the universal abelian scheme of `(Y', Φ')`. -/
theorem exists_moduli_map {Y Y' : Over (Spec (CommRingCat.of ℚ))} {Φ : PtEquiv Y} {Φ' : PtEquiv Y'}
    (hR1 : R1fpProps Y Φ) (h' : Y3Fix.R1fpPropsAbP Y' Φ') :
    ∃ gY : Y' ⟶ Y, ∀ (K : Type) [Field K] [Algebra ℚ K] (s : fieldPt K ⟶ Y'),
      Φ K (s ≫ gY) = Φ' K s := by
  obtain ⟨hp, hs, -, ⟨𝒜, h𝒜⟩, -⟩ := h'
  obtain ⟨g, hg⟩ := hR1.2.2.2.2.2 Y' hp hs 𝒜.toQMFamily (fun K _ _ s => by
    obtain ⟨P, hP⟩ := Quotient.exists_rep (Φ' K s)
    exact ⟨P, h𝒜 K s P hP.symm⟩)
  refine ⟨g, fun K _ _ s => ?_⟩
  obtain ⟨P, hP⟩ := Quotient.exists_rep (Φ' K s)
  rw [hg K s P (h𝒜 K s P hP.symm)]
  exact hP

/-- **Witness matching, reciprocity side.** For every witness `(Y, Φ)` of the CM branch's moduli
clauses there is a `Ψ` with the clauses of Deligne's uniformization that the class-number bound
uses, from the two leaves the CM branch already reads. -/
theorem exists_deligneCore (hModel : _root_.Y3RouteA.Y3FullThreeRepZ30)
    (hDel : _root_.Y3Hodge.DeligneCanonicalModelY3EveryPrint)
    {Y : Over (Spec (CommRingCat.of ℚ))} {Φ : PtEquiv Y} (hR1 : R1fpProps Y Φ) :
    ∃ Ψ, DeligneCore Y Φ Ψ := by
  obtain ⟨Y', Φ', h'⟩ := _root_.Y3RouteA.y3FineModuliAbP_of_z30 hModel
  obtain ⟨Ψ', hb, hU⟩ := hDel Y' Φ' h'
  obtain ⟨gY, hg⟩ := exists_moduli_map hR1 h'
  exact ⟨_, (DeligneCore.of_body hb hU).map gY hg⟩

end Deligne

end HDec.CMBranch.CMjReroute
