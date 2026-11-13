import ZInQKernel.HDecomp.QM.Leaves
import ZInQKernel.HDecomp.Descent.Constants
import ZInQKernel.HDecomp.Descent.B2Glue
import ZInQKernel.Multiplication.Certificate.Constants
import ZInQKernel.Hypotheses.JHeight

/-!
# fibre-cover: the glue Prop `FibreCoverExists` (G2: Prop. TS + Lemma NV)

Task fibre-cover (2026-11-13). The statements `IF`, `T`, `IsModelOver`, `FibreCtx`,
`RationalFibre`, `FibreCoverOut`, `FibreCoverExists` are copied verbatim from
`scratch/g0-mod-field/ModField.lean` (namespace `G0ModField` kept, so the names agree).
-/

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ZInQ LeafQM.AV GlueDescent GlueDescent.B2 GlueDescent.B2Q

namespace G0ModField

/-- Intermediate fields of `ℚ̄/ℚ`. -/
abbrev IF : Type := IntermediateField ℚ Qbar

/-- `T = S_mul ∪ supp M_{S_mul}(u)`, the ramification set (N5 L528). -/
noncomputable def T (u : ℚ) : Finset ℕ := GlueDescent.ramSet Mult.S_mul u

/-- `A`, an abelian variety over the subfield `L ⊆ ℚ̄`, is a model of the surface of the
`ℚ̄`-object `P`: `A_{ℚ̄} ≅ P.A` as `ℚ̄`-schemes (base change along the inclusion `L ⊆ ℚ̄`). -/
def IsModelOver (L : IF) (A : PkgI3.AbVar L) (P : QML3 Qbar) : Prop :=
  Nonempty ((A.baseChange Qbar).X ≅ P.A.X)

/-- **The fibre context** (the hypotheses of `ModularConstituent`): moduli data `(Y, Φ, π)` with
R1-R2's clauses, `u ∉ 𝒞`, and a `ℚ̄`-point `y` of `Y₃` carrying the object `P` and lying over
`J(u)`. -/
def FibreCtx (Y : Over (Spec (CommRingCat.of ℚ))) (Φ : PtEquiv Y) (π : ToP1 Y.left) (u : ℚ)
    (P : QML3 Qbar) : Prop :=
  R1fpProps Y Φ ∧ R2fpProps Y Φ π ∧ u ∉ contactSet ∧
  ∃ y : fieldPt Qbar ⟶ Y, Φ Qbar y = M3.mk P ∧
    π.val (K := Qbar) y.left = OnePoint.some (algebraMap ℚ Qbar (ZInQ.JHeight.Jmap u))

/-- **A rational fibre over `K`** (Glazer N5 L528: "Choose a fiber `A/K`"): `PK` is an object of
`Y₃` over `K ⊆ ℚ̄` at a `K`-point `yK` whose base change to `ℚ̄` carries `P` (so `yK` lies over the
`ℚ̄`-point of `P`, `Φ` being a bijection), and `PK.A` is a model of `P`'s surface. Unlike an
arbitrary `K`-model (a twist of `PK.A` by a cocycle ramified outside `T` can have bad
reduction there), `PK.A` is the fibre of the universal family and has good reduction away
from `3` (G3). -/
def RationalFibre (Y : Over (Spec (CommRingCat.of ℚ))) (Φ : PtEquiv Y) (P : QML3 Qbar) (K : IF)
    (PK : QML3 K) : Prop :=
  (∃ yK : fieldPt K ⟶ Y, Φ K yK = M3.mk PK ∧ Φ Qbar (fieldMap K.val ≫ yK) = M3.mk P) ∧
    IsModelOver K PK.A P

/-- **G2's input, the fibre cover (Prop. TS + Lemma NV, N5 L509-529; remaining).** There is a
separable `f ∈ ℚ[X]` of degree `≤ 324` (the fibre of the normalized cover of `P¹_u` over `u`)
whose splitting field `K = ℚ(roots of f) ⊆ ℚ̄` is unramified outside `T` and contains the residue
field of the point of `P` (a rational fibre `PK/K`, `RationalFibre`). -/
def FibreCoverOut (Y : Over (Spec (CommRingCat.of ℚ))) (Φ : PtEquiv Y) (u : ℚ) (P : QML3 Qbar) :
    Prop :=
  ∃ f : Polynomial ℚ, f.Separable ∧ f.natDegree ≤ 324 ∧
    (∀ p : Nat.Primes, (p : ℕ) ∉ T u →
      UnramifiedAt (IntermediateField.adjoin ℚ (f.rootSet Qbar)) p) ∧
    ∃ PK : QML3 (IntermediateField.adjoin ℚ (f.rootSet Qbar)),
      RationalFibre Y Φ P (IntermediateField.adjoin ℚ (f.rootSet Qbar)) PK



/-- **Remaining (G2): Prop. TS + Lemma NV on the actual fibre** (h-decomposition G2: inputs
R1(d), R2, T1, T2; the valuation case analysis is proved, `GlueRepo.PR.inertia_orders_eq_one_iff`,
and Lemma NV step 2, `LeafQM.AV.residue_unramified_over_branch`). -/
def FibreCoverExists : Prop :=
  ∀ (Y : Over (Spec (CommRingCat.of ℚ))) (Φ : PtEquiv Y) (π : ToP1 Y.left) (u : ℚ)
    (P : QML3 Qbar), FibreCtx Y Φ π u P → FibreCoverOut Y Φ u P


/-! ## Part 1 (proved): `FibreCoverOut` is a statement about the residue field of `y` alone -/

/-- Any two morphisms `Spec K ⟶ Spec ℚ` agree (copied from `scratch/rv-g0pieces/Exotic.lean`). -/
theorem spec_to_specQ_eq {K : Type} [Field K]
    (g h : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of ℚ)) : g = h := by
  rw [← Spec.map_preimage g, ← Spec.map_preimage h]
  congr 1
  apply CommRingCat.hom_ext
  exact Subsingleton.elim _ _

/-- **A `ℚ̄`-point factors through every subfield `K ⊆ ℚ̄` containing its residue field.** -/
theorem exists_factor_of_residueImage_le (Y : Over (Spec (CommRingCat.of ℚ)))
    (y : fieldPt Qbar ⟶ Y) (K : IF) (hK : residueImage (X := Y.left) y.left ≤ K) :
    ∃ yK : fieldPt K ⟶ Y, fieldMap K.val ≫ yK = y := by
  obtain ⟨⟨x, emb⟩, hp⟩ : ∃ q, Scheme.SpecToEquivOfField Qbar Y.left y.left = q := ⟨_, rfl⟩
  unfold residueImage at hK
  rw [hp] at hK
  have hmem : ∀ a, emb a ∈ K := fun a => hK (IntermediateField.subset_adjoin ℚ _ ⟨a, rfl⟩)
  let emb' : Y.left.residueField x ⟶ CommRingCat.of K :=
    CommRingCat.ofHom (emb.hom.codRestrict K hmem)
  have aux : Spec.map (CommRingCat.ofHom ((K.val : K →ₐ[ℚ] Qbar) : K →+* Qbar)) ≫
      (Scheme.SpecToEquivOfField K Y.left).symm ⟨x, emb'⟩ = y.left := by
    apply (Scheme.SpecToEquivOfField Qbar Y.left).injective
    rw [specToEquivOfField_comp, Equiv.apply_symm_apply, hp]
    rfl
  exact ⟨Over.homMk ((Scheme.SpecToEquivOfField K Y.left).symm ⟨x, emb'⟩)
    (spec_to_specQ_eq _ _), Over.OverMorphism.ext aux⟩

/-- The residue field of `z ∘ Spec(K ⊆ ℚ̄)` lies in `K` (scheme form). -/
theorem residueImage_le_aux {X : Scheme.{0}} (K : IF) (z : Spec (CommRingCat.of K) ⟶ X) :
    residueImage (X := X)
      (Spec.map (CommRingCat.ofHom ((K.val : K →ₐ[ℚ] Qbar) : K →+* Qbar)) ≫ z) ≤ K := by
  unfold residueImage
  rw [IntermediateField.adjoin_le_iff, specToEquivOfField_comp]
  rintro _ ⟨a, rfl⟩
  exact ((Scheme.SpecToEquivOfField K X z).2 a).2

/-- The residue field of `y ∘ Spec(K ⊆ ℚ̄)` lies in `K`. -/
theorem residueImage_comp_le (Y : Over (Spec (CommRingCat.of ℚ))) (K : IF)
    (yK : fieldPt K ⟶ Y) : residueImage (X := Y.left) (fieldMap K.val ≫ yK).left ≤ K :=
  residueImage_le_aux K yK.left

/-- A base change along `K ⊆ ℚ̄` of `PK`, isomorphic to `P`, makes `PK.A` a model of `P.A`. -/
theorem isModelOver_of_baseChange {K : IF} {PK : QML3 K} {Q P : QML3 Qbar}
    (hb : IsBaseChangeOf ((K.val : K →ₐ[ℚ] Qbar) : K →+* Qbar) PK Q) (e : Q.Iso P) :
    IsModelOver K PK.A P := by
  obtain ⟨g, hpb, -, -⟩ := hb
  refine ⟨Iso.trans ?_ ⟨e.φ.hom, e.ψ.hom, e.left, e.right⟩⟩
  exact Over.isoMk hpb.isoPullback.symm hpb.isoPullback_inv_snd

/-- **The rational fibre (proved from R1fp alone)**: if `K ⊆ ℚ̄` contains the residue field of
the point `y` of `P`, there is a rational fibre `PK/K` over `P`. -/
theorem rationalFibre_of_le {Y : Over (Spec (CommRingCat.of ℚ))} {Φ : PtEquiv Y}
    (h1 : R1fpProps Y Φ) {y : fieldPt Qbar ⟶ Y} {P : QML3 Qbar} (hy : Φ Qbar y = M3.mk P)
    (K : IF) (hK : residueImage (X := Y.left) y.left ≤ K) :
    ∃ PK : QML3 K, RationalFibre Y Φ P K PK := by
  obtain ⟨yK, hyK⟩ := exists_factor_of_residueImage_le Y y K hK
  obtain ⟨-, -, -, hnat⟩ := h1
  have hPK : Φ K yK = M3.mk (Quotient.out (Φ K yK)) := (Quotient.out_eq _).symm
  obtain ⟨Q, hQ, hb⟩ := hnat K Qbar K.val yK _ hPK
  rw [hyK, hy] at hQ
  have e : Nonempty (P.Iso Q) := Quotient.exact hQ
  exact ⟨_, ⟨yK, hPK, hyK ▸ hy⟩, isModelOver_of_baseChange hb e.some.symm⟩

/-- **The field part of G2's output** for a subfield `F ⊆ ℚ̄`: `F` lies in the splitting field
of a separable `f ∈ ℚ[X]` of degree `≤ 324` unramified outside `T(u)`. -/
def FibreFieldOut (F : IF) (u : ℚ) : Prop :=
  ∃ f : Polynomial ℚ, f.Separable ∧ f.natDegree ≤ 324 ∧
    (∀ p : Nat.Primes, (p : ℕ) ∉ T u →
      UnramifiedAt (IntermediateField.adjoin ℚ (f.rootSet Qbar)) p) ∧
    F ≤ IntermediateField.adjoin ℚ (f.rootSet Qbar)

/-- **`FibreCoverOut` is exactly the field part for the residue field of `y`** (both
directions, from R1fp alone). -/
theorem fibreCoverOut_iff {Y : Over (Spec (CommRingCat.of ℚ))} {Φ : PtEquiv Y}
    (h1 : R1fpProps Y Φ) {y : fieldPt Qbar ⟶ Y} {P : QML3 Qbar} (hy : Φ Qbar y = M3.mk P)
    (u : ℚ) : FibreCoverOut Y Φ u P ↔ FibreFieldOut (residueImage (X := Y.left) y.left) u := by
  constructor
  · rintro ⟨f, hs, hd, hram, PK, ⟨yK, -, hyK⟩, -⟩
    refine ⟨f, hs, hd, hram, ?_⟩
    have : fieldMap (IntermediateField.adjoin ℚ (f.rootSet Qbar)).val ≫ yK = y :=
      (Φ Qbar).injective (hyK.trans hy.symm)
    rw [← this]
    exact residueImage_comp_le Y _ yK
  · rintro ⟨f, hs, hd, hram, hle⟩
    obtain ⟨PK, hPK⟩ := rationalFibre_of_le h1 hy _ hle
    exact ⟨f, hs, hd, hram, PK, hPK⟩

/-- **Independence of the moduli bijection (the relabeling of rv-g0pieces keeps G2).** For two
bijections `Φ, Φ'` on the same `Y`, both with R1fp, and the same point `y`, `FibreCoverOut`
holds for `(Φ, P)` iff it holds for `(Φ', P')`, where `P`, `P'` are the objects of `y`.
In particular a relabeled triple `(Y, Φ ∘ τ, π)` (rv-g0pieces `relabel`, R1fp by
`r1fp_relabel`) satisfies G2 at `y` iff `(Y, Φ, π)` does. -/
theorem fibreCoverOut_indep {Y : Over (Spec (CommRingCat.of ℚ))} {Φ Φ' : PtEquiv Y}
    (h1 : R1fpProps Y Φ) (h1' : R1fpProps Y Φ') {y : fieldPt Qbar ⟶ Y} {P P' : QML3 Qbar}
    (hy : Φ Qbar y = M3.mk P) (hy' : Φ' Qbar y = M3.mk P') (u : ℚ) :
    FibreCoverOut Y Φ u P ↔ FibreCoverOut Y Φ' u P' :=
  (fibreCoverOut_iff h1 hy u).trans (fibreCoverOut_iff h1' hy' u).symm

/-! ## Part 2 (proved): the field part from a degree bound and unramifiedness of `ℚ(y)` -/

/-- **Textbook (STANDARD): the Galois closure of an unramified field is unramified.** If
`ℚ(α) ⊆ ℚ̄` is unramified at `p`, so is the splitting field `ℚ(roots of minpoly α)`, which is
the compositum of the conjugates `σℚ(α) ≅ ℚ(α)`; a compositum of number fields unramified at `p`
is unramified at `p` (Neukirch, *Algebraic Number Theory*, Ch. I §9 or Ch. III §2, the
compositum of unramified extensions; UNVERIFIED locator). Not in Mathlib v4.35 for
`UnramifiedAt` (cf. g0-mod-field's `UnramifiedSup`, the Galois case). -/
def UnramifiedConjugates : Prop :=
  ∀ (α : Qbar) (p : ℕ), UnramifiedAt (IntermediateField.adjoin ℚ {α}) p →
    UnramifiedAt (IntermediateField.adjoin ℚ ((minpoly ℚ α).rootSet Qbar)) p

/-- **The field part from `[F:ℚ] ≤ 324` and `F` unramified outside `T(u)`**: take `f` the
minimal polynomial of a primitive element of `F` (separable in characteristic 0, of degree
`[F:ℚ]`); its splitting field contains `F` and is unramified outside `T(u)` by
`UnramifiedConjugates`. -/
theorem fibreFieldOut_of (hU : UnramifiedConjugates) (F : IF) [FiniteDimensional ℚ F]
    (hd : Module.finrank ℚ F ≤ 324) (u : ℚ)
    (hram : ∀ p : Nat.Primes, (p : ℕ) ∉ T u → UnramifiedAt F p) : FibreFieldOut F u := by
  obtain ⟨β, hF⟩ : ∃ β : Qbar, IntermediateField.adjoin ℚ {β} = F := by
    obtain ⟨α, hα⟩ := Field.exists_primitive_element ℚ F
    refine ⟨α, le_antisymm ?_ ?_⟩
    · rw [IntermediateField.adjoin_simple_le_iff]; exact α.2
    · intro x hx
      have h1 : (⟨x, hx⟩ : F) ∈ IntermediateField.adjoin ℚ {α} := by
        rw [hα]; exact IntermediateField.mem_top
      have h2 : x ∈ (IntermediateField.adjoin ℚ {α}).map F.val := ⟨⟨x, hx⟩, h1, rfl⟩
      rw [IntermediateField.adjoin_map, Set.image_singleton] at h2
      exact h2
  subst hF
  have hint : IsIntegral ℚ β := Algebra.IsIntegral.isIntegral _
  refine ⟨minpoly ℚ β, (minpoly.irreducible hint).separable, ?_, fun p hp => hU _ p (hram p hp), ?_⟩
  · rw [← IntermediateField.adjoin.finrank hint]; exact hd
  · rw [IntermediateField.adjoin_simple_le_iff]
    exact IntermediateField.subset_adjoin ℚ _
      ((Polynomial.mem_rootSet).2 ⟨minpoly.ne_zero hint, minpoly.aeval ℚ _⟩)

/-! ## Part 3: the remaining glue as named Props, and `FibreCoverExists` from them -/

/-- **Glue (G2, degree; Glazer N5 L436-441 and L524-526): the residue field of a point over
`J(u)` has degree `≤ 324`.** For moduli data with R1fp, R2fp, `u ∉ 𝒞`, and a `ℚ̄`-point `y`
with object `P` over `J(u)`, the residue field `ℚ(y) ⊆ ℚ̄` is finite over `ℚ` of degree `≤ 324`.
Argument (glue): the `ℚ`-embeddings of `ℚ(y)` give distinct points `σy` of the fibre over the
rational value `J(u)` (`ToP1.val_comp`), which `Φ` maps injectively into the `Aut 𝒪`-twist class
of `P` (R2fp); that class has at most `4·|(𝒪/3𝒪)^×| ≤ 324` elements (`TwistClassCard`). This
step does not depend on which triple `(Y, Φ, π)` is used. -/
def FibreDegree : Prop :=
  ∀ (Y : Over (Spec (CommRingCat.of ℚ))) (Φ : PtEquiv Y) (π : ToP1 Y.left) (u : ℚ)
    (P : QML3 Qbar) (y : fieldPt Qbar ⟶ Y), R1fpProps Y Φ → R2fpProps Y Φ π →
    u ∉ contactSet → Φ Qbar y = M3.mk P →
    π.val (K := Qbar) y.left = OnePoint.some (algebraMap ℚ Qbar (ZInQ.JHeight.Jmap u)) →
    ∃ _ : FiniteDimensional ℚ (residueImage (X := Y.left) y.left),
      Module.finrank ℚ (residueImage (X := Y.left) y.left) ≤ 324

/-- **Glue (G2, ramification: Prop. TS + Lemma NV, Glazer N5 L484-529; h-decomposition G2 with
inputs R1(d), R2, T1, T2): the residue field of a point over `J(u)` is unramified outside
`T(u) = S_mul ∪ supp M_{S_mul}(u)`.** For the genuine `(Y₃, π)` this is the manuscript's local
calculation: `Y₃ → P¹` has a proper smooth model over `ℤ[1/30]` branched only over `0, ∞, −16/27`
with tame indices; the pullback by `J` has indices `2, 6, 2`, normalized to `2, 1, 1`; the fibre
over `u` is unramified at `p ∉ T(u)` (the valuation case analysis is proved,
`GlueRepo.PR.inertia_orders_eq_one_iff`; Lemma NV step 2 is proved,
`LeafQM.AV.residue_unramified_over_branch`). **Pinning caveat** (fibre-cover §3): as stated it
quantifies over every `(Y, π)` satisfying R1fp, R2fp for some `Φ`; these clauses constrain
`(Y, π)` only through field points, so the genuine proof applies only once `(Y, π)` is pinned
(task qm-pin). Relabelings of `Φ` alone do not matter (`fibreCoverOut_indep`). -/
def FibreUnramified : Prop :=
  ∀ (Y : Over (Spec (CommRingCat.of ℚ))) (Φ : PtEquiv Y) (π : ToP1 Y.left) (u : ℚ)
    (P : QML3 Qbar) (y : fieldPt Qbar ⟶ Y), R1fpProps Y Φ → R2fpProps Y Φ π →
    u ∉ contactSet → Φ Qbar y = M3.mk P →
    π.val (K := Qbar) y.left = OnePoint.some (algebraMap ℚ Qbar (ZInQ.JHeight.Jmap u)) →
    ∀ p : Nat.Primes, (p : ℕ) ∉ T u → UnramifiedAt (residueImage (X := Y.left) y.left) p

/-- **`FibreCoverExists` from the degree bound, Prop. TS + Lemma NV on `ℚ(y)`, and the textbook
fact on Galois closures** (the rational fibre itself is proved from R1fp, `rationalFibre_of_le`). -/
theorem fibreCoverExists_of (hD : FibreDegree) (hR : FibreUnramified)
    (hU : UnramifiedConjugates) : FibreCoverExists := by
  intro Y Φ π u P ⟨h1, h2, hu, y, hy, hπ⟩
  rw [fibreCoverOut_iff h1 hy u]
  obtain ⟨hfd, hd⟩ := hD Y Φ π u P y h1 h2 hu hy hπ
  exact fibreFieldOut_of hU _ hd u (hR Y Φ π u P y h1 h2 hu hy hπ)

end G0ModField

#print axioms G0ModField.fibreCoverOut_iff
#print axioms G0ModField.fibreCoverOut_indep
#print axioms G0ModField.fibreCoverExists_of
