/-! ## g0-assemble2: fibre-cover (scratch/fibre-cover/FibreCover.lean lines 15-18 and 74-730, verbatim; lines
19-73 are verbatim copies of g0-mod-field's definitions, part 75) -/

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ZInQ LeafQM.AV GlueDescent GlueDescent.B2 GlueDescent.B2Q
namespace G0ModField

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
  obtain ⟨-, -, -, hnat, -, -⟩ := h1
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

/-! ## Part 6: `TwistClassCard` from 3-torsion and the Atkin–Lehner count -/

/-- **Glue + textbook leaf (`|A[3]| = 3⁴` for an abelian surface; Mumford §4, the kernel's leaf
`PkgI2.TorsionStructure`, which is stated for `A(K̄)[n]`, `K̄ = AlgebraicClosure K`): the
`3`-torsion of `A(ℚ̄)` has at most `81` points.** From `TorsionStructure` at `K = ℚ̄` and the
injection `A(ℚ̄) → A(AlgebraicClosure ℚ̄)` (glue, not compiled here). -/
def TorsionBound3 : Prop :=
  ∀ A : PkgI3.AbVar Qbar, A.dim = 2 → ∃ s : Finset (Additive (A.Pt Qbar)), s.card ≤ 81 ∧
    ∀ x : Additive (A.Pt Qbar), 3 • x = 0 → x ∈ s

/-- **Glue (computation on N5's maximal order `𝒪` of discriminant 6): `Aut 𝒪` modulo inner
automorphisms by units has at most 4 elements.** Every `α ∈ Aut 𝒪` is `w ∘ Ad u` with `w` in a
fixed set of `≤ 4` automorphisms and `u ∈ 𝒪^×`. Reason: `Aut 𝒪 = N_B(𝒪)/ℚ^×` (Skolem–Noether,
T13, proved) and `N_B(𝒪)/ℚ^×𝒪^× ≅ (ℤ/2)²`, the Atkin–Lehner group `W` of the two ramified primes
(Vignéras, *Arithmétique des algèbres de quaternions*, Ch. II §1 / Ch. III §5, UNVERIFIED
locator; N5 L425-429: "at each of the two division primes its quotient … has order two"). -/
def InnerTwistCount : Prop :=
  ∃ W : Finset (LeafQM.O ≃+* LeafQM.O), W.card ≤ 4 ∧
    ∀ α : LeafQM.O ≃+* LeafQM.O, ∃ w ∈ W, ∃ u : (LeafQM.O)ˣ,
      ∀ a : LeafQM.O, α a = w (u * a * ↑u⁻¹)

section TwistCount

variable {K : Type} [Field K]

/-- A level structure is determined by `η(1)`: `η(a) = a·η(1)`. -/
theorem level3_eta_eq {A : PkgI3.AbVar K} {q : QMStr A} (e : Level3 q) (a : LeafQM.O) :
    e.eta a = qmAct q K a (e.eta 1) := by
  rw [← e.linear, _root_.mul_one]

theorem level3_ext {A : PkgI3.AbVar K} {q : QMStr A} (e e' : Level3 q)
    (h : e.eta 1 = e'.eta 1) : e = e' := by
  have heta : e.eta = e'.eta :=
    AddMonoidHom.ext fun a => by rw [level3_eta_eq e a, level3_eta_eq e' a, h]
  cases e; cases e'
  cases heta
  rfl

/-- `η(1)` is a `3`-torsion point. -/
theorem level3_three {A : PkgI3.AbVar K} {q : QMStr A} (e : Level3 q) : 3 • e.eta 1 = 0 := by
  rw [← map_nsmul, nsmul_eq_mul, _root_.mul_one]
  exact (e.ker _).mpr ⟨1, by rw [_root_.mul_one]; rfl⟩

/-- The inner twist `ι ∘ w ∘ Ad u` is isomorphic to `ι ∘ w`, by `ι(w(u))^{-1}`. -/
noncomputable def innerIso {A : PkgI3.AbVar K} (q : QMStr A) (w : LeafQM.O ≃+* LeafQM.O) (u : (LeafQM.O)ˣ)
    (α : LeafQM.O ≃+* LeafQM.O) (hα : ∀ a, α a = w (u * a * ↑u⁻¹)) :
    QMIso (q.twist α) (q.twist w) where
  φ := q.iota (w ↑u⁻¹)
  ψ := q.iota (w ↑u)
  left := by
    show (q.iota (w ↑u) * q.iota (w ↑u⁻¹)).hom = (1 : PkgI3.AbVar.End A).hom
    rw [← map_mul, ← map_mul, Units.mul_inv, map_one, map_one]
  right := by
    show (q.iota (w ↑u⁻¹) * q.iota (w ↑u)).hom = (1 : PkgI3.AbVar.End A).hom
    rw [← map_mul, ← map_mul, Units.inv_mul, map_one, map_one]
  equivariant a := by
    show (q.iota (w ↑u⁻¹) * q.iota (α a)).hom = (q.iota (w a) * q.iota (w ↑u⁻¹)).hom
    rw [hα, ← map_mul, ← map_mul, ← map_mul, ← map_mul, ← _root_.mul_assoc, ← _root_.mul_assoc,
      Units.inv_mul, _root_.one_mul]

/-- Transport of a level structure along a QM isomorphism. -/
noncomputable def transportLevel {A A' : PkgI3.AbVar K} {q : QMStr A} {q' : QMStr A'} (θ : QMIso q q')
    (e : Level3 q) : Level3 q' where
  eta := (PkgI3.AbVar.ptMap (L := K) θ.φ).toAdditive.comp e.eta
  linear a b := by
    change Additive.ofMul (Additive.toMul (e.eta (a * b)) ≫ θ.φ.hom) =
      Additive.ofMul ((Additive.toMul (e.eta b) ≫ θ.φ.hom) ≫ (q'.iota a).hom)
    rw [e.linear]
    change Additive.ofMul ((Additive.toMul (e.eta b) ≫ (q.iota a).hom) ≫ θ.φ.hom) = _
    rw [Category.assoc, θ.equivariant a, Category.assoc]
  ker a := by
    have hinv : Function.LeftInverse (PkgI3.AbVar.ptMap (L := K) θ.ψ).toAdditive
        (PkgI3.AbVar.ptMap (L := K) θ.φ).toAdditive := fun x => by
      change Additive.ofMul ((Additive.toMul x ≫ θ.φ.hom) ≫ θ.ψ.hom) = x
      rw [Category.assoc, θ.left, Category.comp_id]; rfl
    rw [AddMonoidHom.comp_apply, map_eq_zero_iff _ hinv.injective, e.ker]

/-- The transported object is isomorphic to the original. -/
noncomputable def transportIso (Q : QML3 K) {A' : PkgI3.AbVar K} (hs : A'.dim = 2) {q' : QMStr A'}
    (θ : QMIso Q.q q') : Q.Iso ⟨A', hs, q', transportLevel θ Q.e⟩ where
  φ := θ.φ
  ψ := θ.ψ
  left := θ.left
  right := θ.right
  equivariant := θ.equivariant
  level _ := rfl

end TwistCount

/-- **`TwistClassCard` from the 3-torsion bound and the Atkin–Lehner count** (Glazer's
`4·81 = 324`): a class in the twist class of `P` is `[(A, ι∘w, η')]` for `w ∈ W` and a level
structure `η'`, which is determined by the `3`-torsion point `η'(1)`. -/
theorem twistClassCard_of (hT : TorsionBound3) (hW : InnerTwistCount) : TwistClassCard := by
  classical
  intro P
  obtain ⟨s3, hs3, hs3P⟩ := hT P.A P.surface
  obtain ⟨W, hWc, hWα⟩ := hW
  let F : (LeafQM.O ≃+* LeafQM.O) × Additive (P.A.Pt Qbar) → M3 Qbar := fun wx =>
    if h : ∃ e : Level3 (P.q.twist wx.1), e.eta 1 = wx.2 then
      M3.mk ⟨P.A, P.surface, P.q.twist wx.1, h.choose⟩ else M3.mk P
  refine ⟨(W ×ˢ s3).image F, ?_, ?_⟩
  · calc ((W ×ˢ s3).image F).card ≤ (W ×ˢ s3).card := Finset.card_image_le
      _ = W.card * s3.card := Finset.card_product _ _
      _ ≤ 4 * 81 := Nat.mul_le_mul hWc hs3
      _ = 324 := by norm_num
  · rintro Q ⟨α, ⟨f⟩⟩
    obtain ⟨w, hw, u, hu⟩ := hWα α
    let θ : QMIso Q.q (P.q.twist w) := f.symm.trans (innerIso P.q w u α hu)
    let e' := transportLevel θ Q.e
    have hx : e'.eta 1 ∈ s3 := hs3P _ (level3_three e')
    have hex : ∃ e : Level3 (P.q.twist w), e.eta 1 = e'.eta 1 := ⟨e', rfl⟩
    have hF : F (w, e'.eta 1) = M3.mk Q := by
      dsimp only [F]
      rw [dite_eq_left hex, level3_ext _ _ hex.choose_spec]
      exact (Quotient.sound (⟨transportIso Q P.surface θ⟩ : Nonempty _)).symm
    rw [← hF]
    exact Finset.mem_image_of_mem F (Finset.mem_product.mpr ⟨hw, hx⟩)

/-- **The composite with the twist count reduced**: `FibreCoverExists` from the 3-torsion
bound, the Atkin–Lehner count, the pin, Prop. TS + Lemma NV on one curve, and the textbook fact. -/
theorem fibreCoverExists_of_pinned' (Y₀ : Over (Spec (CommRingCat.of ℚ))) (π₀ : ToP1 Y₀.left)
    (hT : TorsionBound3) (hW : InnerTwistCount) (hpin : CurvePinned Y₀ π₀)
    (h0 : FibreUnramifiedOn Y₀ π₀) (hU : UnramifiedConjugates) : FibreCoverExists :=
  fibreCoverExists_of_pinned Y₀ π₀ (twistClassCard_of hT hW) hpin h0 hU

/-! ## Part 7: `TorsionBound3` from the kernel's leaf `TorsionStructure` -/

/-- Precomposition with `Spec L → Spec K` (a field extension) is injective on `K`-points. -/
theorem spec_comp_injective {X : Scheme.{0}} {K L : Type} [Field K] [Field L] (i : K →+* L)
    (z z' : Spec (CommRingCat.of K) ⟶ X)
    (h : Spec.map (CommRingCat.ofHom i) ≫ z = Spec.map (CommRingCat.ofHom i) ≫ z') : z = z' := by
  have h' := congrArg (Scheme.SpecToEquivOfField L X) h
  rw [specToEquivOfField_comp, specToEquivOfField_comp] at h'
  obtain ⟨⟨p1, f1⟩, hp1⟩ : ∃ q, Scheme.SpecToEquivOfField K X z = q := ⟨_, rfl⟩
  obtain ⟨⟨p2, f2⟩, hp2⟩ : ∃ q, Scheme.SpecToEquivOfField K X z' = q := ⟨_, rfl⟩
  rw [hp1, hp2] at h'
  obtain ⟨rfl, hh⟩ := Sigma.mk.inj_iff.mp h'
  have hf : f1 = f2 := by
    ext a
    apply i.injective
    exact congrArg (fun φ : X.residueField p1 ⟶ CommRingCat.of L => φ a) (eq_of_heq hh)
  apply (Scheme.SpecToEquivOfField K X).injective
  rw [hp1, hp2, hf]

/-- `Spec(AlgebraicClosure ℚ̄) → Spec ℚ̄` over `ℚ̄`. -/
noncomputable def specIncl :
    PkgI2.specOver Qbar (AlgebraicClosure Qbar) ⟶ PkgI3.AbVar.ptObj (K := Qbar) Qbar :=
  Over.homMk (Spec.map (CommRingCat.ofHom (algebraMap Qbar (AlgebraicClosure Qbar)))) (by
    simp only [PkgI2.specOver, PkgI3.AbVar.ptObj, Over.mk_hom, ← Spec.map_comp,
      ← CommRingCat.ofHom_comp, Algebra.algebraMap_self, RingHom.comp_id])

/-- **`TorsionBound3` from the textbook leaf `TorsionStructure`** (`A(K̄)[3] ≅ (ℤ/3)⁴` at
`K = ℚ̄`, `K̄ = AlgebraicClosure ℚ̄`): `A(ℚ̄)[3]` injects into `A(K̄)[3]`, which has `81` points. -/
theorem torsionBound3_of (hT : ObjBridge.TorsionStructure) : TorsionBound3 := by
  classical
  intro A hA
  obtain ⟨e, -⟩ := hT Qbar (ObjBridge.toGrp A) 2 3 (by rw [Nat.cast_ofNat]; exact hA)
    (by norm_num) (by norm_num)
  set Tset := PkgI2.torsion (ObjBridge.toGrp A) (AlgebraicClosure Qbar) 3 with hTset
  have : Finite Tset := Finite.of_equiv _ e.symm
  have hTfin : Tset.Finite := Set.toFinite Tset
  have hcard : hTfin.toFinset.card = 81 := by
    rw [← Set.ncard_eq_toFinset_card Tset hTfin, ← Nat.card_coe_set_eq, Nat.card_congr e,
      Nat.card_eq_fintype_card, Fintype.card_fun, ZMod.card, Fintype.card_fin]
    norm_num
  let incl : Additive (A.Pt Qbar) → PkgI2.Pts (ObjBridge.toGrp A) (AlgebraicClosure Qbar) :=
    fun x => specIncl ≫ Additive.toMul x
  have hinj : Function.Injective incl := by
    intro x y hxy
    have hl : Spec.map (CommRingCat.ofHom (algebraMap Qbar (AlgebraicClosure Qbar))) ≫
        (Additive.toMul x).left =
        Spec.map (CommRingCat.ofHom (algebraMap Qbar (AlgebraicClosure Qbar))) ≫
        (Additive.toMul y).left :=
      congrArg (fun f => f.left) hxy
    exact Additive.toMul.injective (Over.OverMorphism.ext (spec_comp_injective _ _ _ hl))
  have htors : ∀ x : Additive (A.Pt Qbar), 3 • x = 0 → incl x ∈ Tset := by
    intro x hx
    show (specIncl ≫ Additive.toMul x) ^ 3 = 1
    have h3 : Additive.toMul x ^ 3 = 1 := by
      rw [← toMul_nsmul, hx]; rfl
    have hpow : ∀ n : ℕ, specIncl ≫ Additive.toMul x ^ n = (specIncl ≫ Additive.toMul x) ^ n := by
      intro n
      induction n with
      | zero => rw [pow_zero, pow_zero, MonObj.comp_one]
      | succ n ih => rw [pow_succ, pow_succ, MonObj.comp_mul, ih]
    rw [← hpow, h3, MonObj.comp_one]
  have hsfin : {x : Additive (A.Pt Qbar) | 3 • x = 0}.Finite :=
    Set.Finite.of_finite_image (hTfin.subset (by rintro _ ⟨x, hx, rfl⟩; exact htors x hx))
      hinj.injOn
  refine ⟨hsfin.toFinset, ?_, fun x hx => hsfin.mem_toFinset.mpr hx⟩
  rw [← hcard]
  exact Finset.card_le_card_of_injOn incl
    (fun x hx => hTfin.mem_toFinset.mpr (htors x (hsfin.mem_toFinset.mp hx))) hinj.injOn

/-- **The composite with the torsion count from the kernel's leaf.** -/
theorem fibreCoverExists_of_leafTorsion (Y₀ : Over (Spec (CommRingCat.of ℚ)))
    (π₀ : ToP1 Y₀.left) (hT : ObjBridge.TorsionStructure) (hW : InnerTwistCount)
    (hpin : CurvePinned Y₀ π₀) (h0 : FibreUnramifiedOn Y₀ π₀) (hU : UnramifiedConjugates) :
    FibreCoverExists :=
  fibreCoverExists_of_pinned' Y₀ π₀ (torsionBound3_of hT) hW hpin h0 hU

/-- The same with the leaf exactly as it appears in the bundle (`TextbookLeaves.t5 :
PkgI2.TorsionStructure.{0}`, scratch/h-decomposition/Leaves.lean). -/
theorem torsionBound3_of_t5 (t5 : PkgI2.TorsionStructure.{0}) : TorsionBound3 :=
  torsionBound3_of (ObjBridge.torsionStructure_iff.mpr t5)

/-! ## Part 8: Prop. TS in Beckmann's inertia form; the valuation analysis is the repository's -/

/-- **Glue from leaves: Prop. TS (specialization inertia) on one cover `π₀ : Y₀ → P¹`**
(N5 L484-525; Beckmann, *On extensions of number fields obtained by specializing branched
coverings*, J. reine angew. Math. 419 (1991), Prop. 4.2, UNVERIFIED number; or T1-T2 with the
integral model R1(d)). For a rational non-branch value `t` and a prime `p > 324` (so
`p ∤ |G|`, `p ∤ 30`: good reduction, and the branch points `0, ∞, −16/27` stay distinct mod `p`),
the residue field of a `ℚ̄`-point over `t` is unramified at `p` once the three Beckmann inertia
orders `e_b / gcd(e_b, m_b)` are `1`: `e = 4, 6, 2` at `0, ∞, −16/27` (the indices of
`Y₃ → P¹`, `RvNocm.ramification_eq_orbifold_order`), `m_b` the intersection multiplicities
`v_p(t)⁺`, `(−v_p(t))⁺`, `v_p(t + 16/27)⁺`. -/
def PropTS (Y₀ : Over (Spec (CommRingCat.of ℚ))) (π₀ : ToP1 Y₀.left) : Prop :=
  ∀ (t : ℚ) (y : fieldPt Qbar ⟶ Y₀), t ≠ 0 → t ≠ -16 / 27 →
    π₀.val (K := Qbar) y.left = OnePoint.some (algebraMap ℚ Qbar t) →
    ∀ p : Nat.Primes, 324 < (p : ℕ) →
      4 ∣ (padicValRat p t).toNat → 6 ∣ (-padicValRat p t).toNat →
      2 ∣ (padicValRat p (t + 16 / 27)).toNat →
      UnramifiedAt (residueImage (X := Y₀.left) y.left) p

/-- **`FibreUnramifiedOn` from Prop. TS**: for `p ∉ T(u)` (so `p > 324` and `p ∤ M_S(u)`), the
three inertia orders at `t = J(u)` are `1` (`GlueRepo.PR.inertia_trivial_iff_not_dvd`, the
repository's valuation case analysis), and `J(u) ≠ 0, −16/27` for `u ∉ 𝒞`. -/
theorem fibreUnramifiedOn_of_propTS (Y₀ : Over (Spec (CommRingCat.of ℚ))) (π₀ : ToP1 Y₀.left)
    (h : PropTS Y₀ π₀) : FibreUnramifiedOn Y₀ π₀ := by
  intro u y hu hπ p hp
  have hp' : (p : ℕ) ∉ Mult.S_mul ∪ (contactSupport Mult.S_mul u).primeFactors := hp
  have hS : ∀ q, q.Prime → q ≤ 324 → q ∈ Mult.S_mul := fun q hq hq' =>
    Mult.mem_S_mul.mpr (Or.inl (Mult.mem_S_ht.mpr ⟨hq, hq'⟩))
  have hpS : (p : ℕ) ∉ Mult.S_mul := fun h' => hp' (Finset.mem_union_left _ h')
  have hp324 : 324 < (p : ℕ) := by
    by_contra h'
    exact hpS (hS _ p.2 (by omega))
  have hndvd : ¬ (p : ℕ) ∣ contactSupport Mult.S_mul u := fun hd =>
    hp' (Finset.mem_union_right _
      (Nat.mem_primeFactors.mpr ⟨p.2, hd, (GlueDescent.contactSupport_pos _ _).ne'⟩))
  have : Fact (p : ℕ).Prime := ⟨p.2⟩
  obtain ⟨h4, h6, h2⟩ :=
    (GlueRepo.PR.inertia_trivial_iff_not_dvd (p := p) Mult.S_mul hS hpS hu).mpr hndvd
  exact h (ZInQ.JHeight.Jmap u) y (GlueRepo.PR.J_ne_zero hu) (GlueRepo.PR.J_ne_branch u) hπ p
    hp324 h4 h6 h2

/-- **The composite on the leaves of the bundle**: `FibreCoverExists` from T5
(`TorsionStructure`), `InnerTwistCount`, the pin `CurvePinned Y₀ π₀`, Prop. TS on `(Y₀, π₀)`, and
`UnramifiedConjugates`. -/
theorem fibreCoverExists_of_propTS (Y₀ : Over (Spec (CommRingCat.of ℚ))) (π₀ : ToP1 Y₀.left)
    (t5 : PkgI2.TorsionStructure.{0}) (hW : InnerTwistCount) (hpin : CurvePinned Y₀ π₀)
    (hTS : PropTS Y₀ π₀) (hU : UnramifiedConjugates) : FibreCoverExists :=
  fibreCoverExists_of_pinned' Y₀ π₀ (torsionBound3_of_t5 t5) hW hpin
    (fibreUnramifiedOn_of_propTS Y₀ π₀ hTS) hU

/-- **Prop. TS for every admissible cover** (the pin-free alternative to `CurvePinned`): every
`(Y, π)` admitting a moduli bijection with R1fp and R2fp satisfies Prop. TS. SPECULATIVE truth
argument (fibre-cover §3.2): R2fp makes every rational fibre of `π` isomorphic, as a Galois set
with residue fields, to a fibre of the genuine `π₀`, a `G`-torsor; by Hilbert irreducibility the
arithmetic monodromy of `π` then acts regularly, so `π` is Galois of degree `|G|` with the same
branch values and indices `4, 6, 2`, and Beckmann's theorem applies with the same inertia orders. -/
def PropTSAll : Prop :=
  ∀ (Y : Over (Spec (CommRingCat.of ℚ))) (Φ : PtEquiv Y) (π : ToP1 Y.left),
    R1fpProps Y Φ → R2fpProps Y Φ π → PropTS Y π

theorem fibreUnramified_of_propTSAll (h : PropTSAll) : FibreUnramified :=
  fun Y Φ π u _ y h1 h2 hu _ hπ => fibreUnramifiedOn_of_propTS Y π (h Y Φ π h1 h2) u y hu hπ

/-- **The pin-free composite**: `FibreCoverExists` from T5, `InnerTwistCount`, `PropTSAll` and
`UnramifiedConjugates`. -/
theorem fibreCoverExists_of_propTSAll (t5 : PkgI2.TorsionStructure.{0}) (hW : InnerTwistCount)
    (hTS : PropTSAll) (hU : UnramifiedConjugates) : FibreCoverExists :=
  fibreCoverExists_of_twistClassCard (twistClassCard_of (torsionBound3_of_t5 t5) hW)
    (fibreUnramified_of_propTSAll hTS) hU

end G0ModField

namespace G0ModField

/-- **`InnerTwistCount` is proved** (g0-assemble2, from aut-o-finite's explicit computation
`Exact.autO_mod_inner_exact`: every `α ∈ Aut 𝒪` is `Ad v ∘ t_k` for one of four `t_k`; then
`α = t_k ∘ Ad (t_k⁻¹ v)`). -/
theorem innerTwistCount_proof : InnerTwistCount := by
  classical
  obtain ⟨t, ht, -⟩ := LeafQM.AV.Pin.Exact.autO_mod_inner_exact
  refine ⟨Finset.univ.image t, Finset.card_image_le.trans (by simp), fun α => ?_⟩
  obtain ⟨k, v, hv⟩ := ht α
  refine ⟨t k, Finset.mem_image_of_mem t (Finset.mem_univ k),
    ⟨(t k).symm (v : LeafQM.O), (t k).symm ((v⁻¹ : (LeafQM.O)ˣ) : LeafQM.O), ?_, ?_⟩, fun a => ?_⟩
  · rw [← map_mul, Units.mul_inv, map_one]
  · rw [← map_mul, Units.inv_mul, map_one]
  · show α a = t k ((t k).symm (v : LeafQM.O) * a * (t k).symm ((v⁻¹ : (LeafQM.O)ˣ) : LeafQM.O))
    rw [map_mul, map_mul, RingEquiv.apply_symm_apply, RingEquiv.apply_symm_apply, hv a]

/-- **`FibreCoverExists` from T5, `PropTSAll` and `UnramifiedConjugates`** (fibre-cover's pin-free
composite with `InnerTwistCount` proved). -/
theorem fibreCoverExists_of_propTSAll' (t5 : PkgI2.TorsionStructure.{0}) (hTS : PropTSAll)
    (hU : UnramifiedConjugates) : FibreCoverExists :=
  fibreCoverExists_of_propTSAll t5 innerTwistCount_proof hTS hU

end G0ModField
