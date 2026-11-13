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

/-! ## Part 4: `FibreDegree` from the intrinsic count `TwistClassCard` -/

/-- **Glue (Glazer N5 L425-441, the degree bound `≤ 4·|(𝒪/3𝒪)^×| ≤ 324`): the `Aut 𝒪`-twist
class of a level-3 object over `ℚ̄` has at most `324` isomorphism classes.** For `P = (A, ι, η)`
over `ℚ̄`, the classes `[Q]` whose QM pair is an `Aut 𝒪`-twist of `(A, ι)` number at most
`4·|(𝒪/3𝒪)^×|`: `Aut 𝒪` modulo inner automorphisms (which give isomorphic pairs) has order 4
(the Atkin–Lehner group `W`), and on a fixed pair the level structures `η : 𝒪 → A[3]` are
determined by `η(1)`, a free generator of the `𝒪/3𝒪`-module `A[3] ≅ 𝒪/3𝒪` (`|A[3]| = 3⁴`,
Mumford §4, UNVERIFIED locator), so there are `|(𝒪/3𝒪)^×| = |GL₂(𝔽₃)| = 48 ≤ 81` of them.
Intrinsic: it mentions no moduli scheme. -/
def TwistClassCard : Prop :=
  ∀ P : QML3 Qbar, ∃ s : Finset (M3 Qbar), s.card ≤ 324 ∧
    ∀ Q : QML3 Qbar, (∃ α : LeafQM.O ≃+* LeafQM.O, Nonempty (QMIso (P.q.twist α) Q.q)) → M3.mk Q ∈ s

/-- Every finite subextension `K ⊆ F` has degree at most the number of embeddings `F → ℚ̄`. -/
theorem finrank_le_of_card_algHom_le (F : IF) (n : ℕ)
    (h : ∀ t : Finset (F →ₐ[ℚ] Qbar), t.card ≤ n) (K : IntermediateField ℚ F)
    [FiniteDimensional ℚ K] : Module.finrank ℚ K ≤ n := by
  classical
  have hext : ∀ e : K →ₐ[ℚ] Qbar, ∃ e' : F →ₐ[ℚ] Qbar, e'.domRestrict K = e := fun e =>
    IsAlgClosed.surjective_domRestrict_of_isAlgebraic (K := ℚ) (L := K) (M := Qbar) (E := F) e
  choose ext hext using hext
  have hinj : Function.Injective ext := fun e₁ e₂ h12 => by
    rw [← hext e₁, ← hext e₂, h12]
  calc Module.finrank ℚ K = Fintype.card (K →ₐ[ℚ] Qbar) := (AlgHom.card ℚ K Qbar).symm
    _ = (Finset.univ.image ext).card := by
        rw [Finset.card_image_of_injective _ hinj, Finset.card_univ]
    _ ≤ n := h _

/-- **A subfield of `ℚ̄` with at most `n` embeddings into `ℚ̄` is finite of degree `≤ n`.** -/
theorem finiteDimensional_of_card_algHom_le (F : IF) (n : ℕ)
    (h : ∀ t : Finset (F →ₐ[ℚ] Qbar), t.card ≤ n) :
    ∃ _ : FiniteDimensional ℚ F, Module.finrank ℚ F ≤ n := by
  classical
  let Pm : ℕ → Prop := fun m => ∃ K : IntermediateField ℚ F,
    FiniteDimensional ℚ K ∧ Module.finrank ℚ K = m
  have h1 : Pm 1 := ⟨⊥, inferInstance, IntermediateField.finrank_bot⟩
  have hn : 1 ≤ n := by
    have := finrank_le_of_card_algHom_le F n h (⊥ : IntermediateField ℚ F)
    rwa [IntermediateField.finrank_bot] at this
  obtain ⟨K₀, hK₀, hK₀r⟩ := Nat.findGreatest_spec hn h1
  have htop : K₀ = ⊤ := by
    refine eq_top_iff.mpr fun x _ => ?_
    let K₁ : IntermediateField ℚ F := K₀ ⊔ IntermediateField.adjoin ℚ {x}
    have : FiniteDimensional ℚ (IntermediateField.adjoin ℚ {x}) :=
      IntermediateField.adjoin.finiteDimensional (Algebra.IsIntegral.isIntegral x)
    have : FiniteDimensional ℚ K₁ := IntermediateField.finiteDimensional_sup _ _
    have hle : K₀ ≤ K₁ := le_sup_left
    have hr : Module.finrank ℚ K₁ ≤ Module.finrank ℚ K₀ := by
      rw [hK₀r]
      exact Nat.le_findGreatest (finrank_le_of_card_algHom_le F n h K₁) ⟨K₁, inferInstance, rfl⟩
    have heq : K₀ = K₁ := IntermediateField.eq_of_le_of_finrank_le hle hr
    rw [heq]
    exact le_sup_right (a := K₀) (IntermediateField.mem_adjoin_simple_self ℚ x)
  have e : (⊤ : IntermediateField ℚ F) ≃ₗ[ℚ] F := IntermediateField.topEquiv.toLinearEquiv
  have : FiniteDimensional ℚ (⊤ : IntermediateField ℚ F) := htop ▸ hK₀
  have : FiniteDimensional ℚ F := e.finiteDimensional
  refine ⟨inferInstance, ?_⟩
  rw [← e.finrank_eq]
  have := finrank_le_of_card_algHom_le F n h (⊤ : IntermediateField ℚ F)
  exact this

/-- **`FibreDegree` from `TwistClassCard`** (no pinning needed): the embeddings `e` of
`F = ℚ(y)` give points `e ∘ y_F` over `J(u)`, pairwise distinct (`F` is generated by the image
of the residue field), whose classes lie in the twist class of `P` (R2fp). -/
theorem fibreDegree_of (hC : TwistClassCard) : FibreDegree := by
  classical
  intro Y Φ π u P y h1 h2 hu hy hπ
  obtain ⟨⟨x, emb⟩, hp⟩ : ∃ q, Scheme.SpecToEquivOfField Qbar Y.left y.left = q := ⟨_, rfl⟩
  have hF : residueImage (X := Y.left) y.left = IntermediateField.adjoin ℚ (Set.range emb) := by
    unfold residueImage; rw [hp]
  rw [hF]
  set F : IF := IntermediateField.adjoin ℚ (Set.range emb) with hFdef
  have hmem : ∀ a, emb a ∈ F := fun a => IntermediateField.subset_adjoin ℚ _ ⟨a, rfl⟩
  let emb' : Y.left.residueField x ⟶ CommRingCat.of F :=
    CommRingCat.ofHom (emb.hom.codRestrict F hmem)
  let zF : Spec (CommRingCat.of F) ⟶ Y.left := (Scheme.SpecToEquivOfField F Y.left).symm ⟨x, emb'⟩
  have hz : ∀ e : F →ₐ[ℚ] Qbar, Scheme.SpecToEquivOfField Qbar Y.left
      (Spec.map (CommRingCat.ofHom (e : F →+* Qbar)) ≫ zF) = ⟨x, emb' ≫ CommRingCat.ofHom e⟩ := by
    intro e
    rw [specToEquivOfField_comp, Equiv.apply_symm_apply]
  have hzy : Spec.map (CommRingCat.ofHom ((F.val : F →ₐ[ℚ] Qbar) : F →+* Qbar)) ≫ zF = y.left := by
    apply (Scheme.SpecToEquivOfField Qbar Y.left).injective
    rw [hz, hp]
    rfl
  let yF : fieldPt F ⟶ Y := Over.homMk zF (spec_to_specQ_eq _ _)
  obtain ⟨s, hs, hsP⟩ := hC P
  apply finiteDimensional_of_card_algHom_le F 324
  intro t
  -- the value of `π` at the points `e ∘ y_F`
  have hy' : (π.val (K := F) zF).map (F.val : F →+* Qbar) =
      OnePoint.some (algebraMap ℚ Qbar (ZInQ.JHeight.Jmap u)) := by
    rw [← π.val_comp (F.val : F →+* Qbar) zF, hzy]
    exact hπ
  have hval : ∀ e : F →ₐ[ℚ] Qbar, π.val (K := Qbar)
      (Spec.map (CommRingCat.ofHom (e : F →+* Qbar)) ≫ zF) =
      OnePoint.some (algebraMap ℚ Qbar (ZInQ.JHeight.Jmap u)) := by
    intro e
    rw [π.val_comp]
    revert hy'
    induction π.val (K := F) zF using OnePoint.rec with
    | infty => intro h; simp at h
    | coe z =>
      intro h
      simp only [OnePoint.map_some] at h ⊢
      have hz' : z = algebraMap ℚ F (ZInQ.JHeight.Jmap u) := by
        apply (F.val : F →+* Qbar).injective
        have h' := OnePoint.coe_injective h
        rw [h']
        exact (F.val.commutes _).symm
      rw [hz']
      exact congrArg _ (e.commutes _)
  let g : (F →ₐ[ℚ] Qbar) → M3 Qbar := fun e => Φ Qbar (fieldMap e ≫ yF)
  have hmaps : ∀ e ∈ t, g e ∈ s := by
    intro e _
    have hQ : Φ Qbar (fieldMap e ≫ yF) = M3.mk (Quotient.out (Φ Qbar (fieldMap e ≫ yF))) :=
      (Quotient.out_eq _).symm
    have := ((h2 y _ P _ hy hQ).1).1 (hπ.trans (hval e).symm)
    show Φ Qbar (fieldMap e ≫ yF) ∈ s
    rw [hQ]
    exact hsP _ this
  have hinj : Set.InjOn g t := by
    intro e₁ _ e₂ _ h12
    have hpt : fieldMap e₁ ≫ yF = fieldMap e₂ ≫ yF := (Φ Qbar).injective h12
    have hl : Spec.map (CommRingCat.ofHom (e₁ : F →+* Qbar)) ≫ zF =
        Spec.map (CommRingCat.ofHom (e₂ : F →+* Qbar)) ≫ zF :=
      congrArg (fun z : fieldPt Qbar ⟶ Y => z.left) hpt
    have hl' := congrArg (Scheme.SpecToEquivOfField Qbar Y.left) hl
    rw [hz, hz] at hl'
    have hemb := eq_of_heq (Sigma.mk.inj_iff.mp hl').2
    apply IntermediateField.algHom_ext_of_eq_adjoin (hS := hFdef)
    rintro _ ⟨a, rfl⟩
    exact congrArg (fun φ : Y.left.residueField x ⟶ CommRingCat.of Qbar => φ a) hemb
  calc t.card ≤ s.card := Finset.card_le_card_of_injOn g hmaps hinj
    _ ≤ 324 := hs

/-- **`FibreCoverExists` from the intrinsic count, Prop. TS + Lemma NV on `ℚ(y)`, and the textbook
fact on Galois closures.** -/
theorem fibreCoverExists_of_twistClassCard (hC : TwistClassCard) (hR : FibreUnramified)
    (hU : UnramifiedConjugates) : FibreCoverExists :=
  fibreCoverExists_of (fibreDegree_of hC) hR hU

/-! ## Part 5: what the ramification step needs from a pinning (only `(Y, π)` up to isomorphism) -/

/-- The residue field can only shrink along a morphism (scheme form). -/
theorem residueImage_comp_le_self_aux {X X' : Scheme.{0}} (h : X ⟶ X')
    (z : Spec (CommRingCat.of Qbar) ⟶ X) :
    residueImage (X := X') (z ≫ h) ≤ residueImage (X := X) z := by
  unfold residueImage
  rw [specToEquivOfField_comp_right]
  apply IntermediateField.adjoin_le_iff.mpr
  rintro _ ⟨a, rfl⟩
  exact IntermediateField.subset_adjoin ℚ _ ⟨_, rfl⟩

/-- The residue field can only shrink along a morphism: `ℚ(h ∘ y) ⊆ ℚ(y)`. -/
theorem residueImage_comp_le_self {Y Y' : Over (Spec (CommRingCat.of ℚ))} (h : Y ⟶ Y')
    (y : fieldPt Qbar ⟶ Y) :
    residueImage (X := Y'.left) (y ≫ h).left ≤ residueImage (X := Y.left) y.left :=
  residueImage_comp_le_self_aux h.left y.left

/-- Along an isomorphism the residue field is unchanged. -/
theorem residueImage_comp_iso {Y Y' : Over (Spec (CommRingCat.of ℚ))} (g : Y ≅ Y')
    (y : fieldPt Qbar ⟶ Y) :
    residueImage (X := Y'.left) (y ≫ g.hom).left = residueImage (X := Y.left) y.left := by
  apply le_antisymm (residueImage_comp_le_self g.hom y)
  have := residueImage_comp_le_self g.inv (y ≫ g.hom)
  rwa [Category.assoc, g.hom_inv_id, Category.comp_id] at this

/-- **Prop. TS + Lemma NV for one curve with one map to `P¹`** (the genuine `(Y₃, π)`): the
residue field of every `ℚ̄`-point over `J(u)`, `u ∉ 𝒞`, is unramified outside `T(u)`. This
mentions no moduli bijection. -/
def FibreUnramifiedOn (Y₀ : Over (Spec (CommRingCat.of ℚ))) (π₀ : ToP1 Y₀.left) : Prop :=
  ∀ (u : ℚ) (y : fieldPt Qbar ⟶ Y₀), u ∉ contactSet →
    π₀.val (K := Qbar) y.left = OnePoint.some (algebraMap ℚ Qbar (ZInQ.JHeight.Jmap u)) →
    ∀ p : Nat.Primes, (p : ℕ) ∉ T u → UnramifiedAt (residueImage (X := Y₀.left) y.left) p

/-- **The pin that `FibreUnramified` needs** (to be supplied by task qm-pin's repair): every
`(Y, π)` admitting a moduli bijection `Φ` with R1fp and R2fp is isomorphic to `(Y₀, π₀)` over
`P¹` on `ℚ̄`-points. `Φ` itself need not be pinned (`fibreCoverOut_indep`). -/
def CurvePinned (Y₀ : Over (Spec (CommRingCat.of ℚ))) (π₀ : ToP1 Y₀.left) : Prop :=
  ∀ (Y : Over (Spec (CommRingCat.of ℚ))) (Φ : PtEquiv Y) (π : ToP1 Y.left),
    R1fpProps Y Φ → R2fpProps Y Φ π →
    ∃ g : Y ≅ Y₀, ∀ y : fieldPt Qbar ⟶ Y,
      π.val (K := Qbar) y.left = π₀.val (K := Qbar) (y ≫ g.hom).left

/-- **`FibreUnramified` from Prop. TS on one curve and the pin of `(Y, π)`.** -/
theorem fibreUnramified_of_pinned (Y₀ : Over (Spec (CommRingCat.of ℚ))) (π₀ : ToP1 Y₀.left)
    (hpin : CurvePinned Y₀ π₀) (h0 : FibreUnramifiedOn Y₀ π₀) : FibreUnramified := by
  intro Y Φ π u P y h1 h2 hu _ hπ p hp
  obtain ⟨g, hg⟩ := hpin Y Φ π h1 h2
  rw [← residueImage_comp_iso g y]
  exact h0 u (y ≫ g.hom) hu ((hg y).symm.trans hπ) p hp

/-- **The composite, corrected form**: `FibreCoverExists` from the intrinsic count, Prop. TS +
Lemma NV on the genuine `(Y₀, π₀)`, the pin of `(Y, π)`, and the textbook fact. -/
theorem fibreCoverExists_of_pinned (Y₀ : Over (Spec (CommRingCat.of ℚ))) (π₀ : ToP1 Y₀.left)
    (hC : TwistClassCard) (hpin : CurvePinned Y₀ π₀) (h0 : FibreUnramifiedOn Y₀ π₀)
    (hU : UnramifiedConjugates) : FibreCoverExists :=
  fibreCoverExists_of_twistClassCard hC (fibreUnramified_of_pinned Y₀ π₀ hpin h0) hU

end G0ModField

#print axioms G0ModField.fibreCoverOut_iff
#print axioms G0ModField.fibreCoverOut_indep
#print axioms G0ModField.fibreCoverExists_of
#print axioms G0ModField.fibreDegree_of
#print axioms G0ModField.fibreCoverExists_of_twistClassCard
#print axioms G0ModField.fibreCoverExists_of_pinned
