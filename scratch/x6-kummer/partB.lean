
namespace X6Kummer

open CategoryTheory AlgebraicGeometry Limits
open LeafQM.AV LeafQM.AV.Pin PkgI3 FS5NoCM

/-! ## §B Galois action on `ℚ̄`-points and residue fields (glue, compiled) -/

/-- A `ℚ`-subfield of `ℚ̄` is determined by the automorphisms fixing it pointwise (infinite Galois
theory: `E = (ℚ̄)^{Gal(ℚ̄/E)}`, `InfiniteGalois.fixedField_fixingSubgroup`). -/
theorem intermediateField_eq_of_fix_iff (E E' : IntermediateField ℚ Qbar)
    (h : ∀ σ : Qbar ≃ₐ[ℚ] Qbar, (∀ z ∈ E, σ z = z) ↔ (∀ z ∈ E', σ z = z)) : E = E' := by
  have hs : E.fixingSubgroup = E'.fixingSubgroup := by
    ext σ
    rw [IntermediateField.mem_fixingSubgroup_iff, IntermediateField.mem_fixingSubgroup_iff]
    exact h σ
  rw [← InfiniteGalois.fixedField_fixingSubgroup E, hs,
    InfiniteGalois.fixedField_fixingSubgroup]

/-- An automorphism fixing a set fixes the `ℚ`-subfield it generates. -/
theorem fix_adjoin_iff (σ : Qbar ≃ₐ[ℚ] Qbar) (S : Set Qbar) :
    (∀ z ∈ IntermediateField.adjoin ℚ S, σ z = z) ↔ ∀ s ∈ S, σ s = s := by
  constructor
  · intro h s hs
    exact h s (IntermediateField.subset_adjoin ℚ S hs)
  · intro h
    have key : ((σ : Qbar →ₐ[ℚ] Qbar).comp (IntermediateField.adjoin ℚ S).val) =
        (IntermediateField.adjoin ℚ S).val :=
      IntermediateField.adjoin_algHom_ext ℚ (fun s hs => h s hs)
    intro z hz
    exact congrArg (fun φ : IntermediateField.adjoin ℚ S →ₐ[ℚ] Qbar => φ ⟨z, hz⟩) key

/-- Scheme form of `galPt_eq_self_iff`. -/
theorem spec_comp_eq_self_iff {Z : Scheme.{0}} (σ : Qbar ≃ₐ[ℚ] Qbar)
    (y : Spec (CommRingCat.of Qbar) ⟶ Z) :
    Spec.map (CommRingCat.ofHom ((σ : Qbar →ₐ[ℚ] Qbar) : Qbar →+* Qbar)) ≫ y = y ↔
      ∀ s ∈ Set.range (Scheme.SpecToEquivOfField Qbar Z y).2, σ s = s := by
  constructor
  · intro h
    have e := congrArg (Scheme.SpecToEquivOfField Qbar Z) h
    rw [specToEquivOfField_comp] at e
    have e2 := eq_of_heq (Sigma.mk.inj_iff.mp e).2
    rintro _ ⟨w, rfl⟩
    exact ConcreteCategory.congr_hom e2 w
  · intro h
    apply (Scheme.SpecToEquivOfField Qbar Z).injective
    rw [specToEquivOfField_comp]
    refine Sigma.ext rfl (heq_of_eq ?_)
    ext w
    exact h _ ⟨w, rfl⟩

/-- **The stabilizer of a `ℚ̄`-point is the fixing group of its residue field**: for
`σ ∈ Aut(ℚ̄/ℚ)` and `x : Spec ℚ̄ → X` over `ℚ`, `x ∘ Spec σ = x` iff `σ` fixes the image
`ℚ(x) ⊆ ℚ̄` of the residue field pointwise. (A `ℚ̄`-point is its scheme point `p` together with an
embedding `κ(p) ↪ ℚ̄`; composing with `Spec σ` keeps `p` and composes the embedding with `σ`.) -/
theorem galPt_eq_self_iff {X : Over (Spec (CommRingCat.of ℚ))} (σ : Qbar ≃ₐ[ℚ] Qbar)
    (x : fieldPt Qbar ⟶ X) :
    fieldMap (σ : Qbar →ₐ[ℚ] Qbar) ≫ x = x ↔
      ∀ z ∈ residueImage (X := X.left) x.left, σ z = z := by
  rw [show residueImage (X := X.left) x.left = IntermediateField.adjoin ℚ
    (Set.range (Scheme.SpecToEquivOfField Qbar X.left x.left).2) from rfl, fix_adjoin_iff]
  rw [← spec_comp_eq_self_iff σ x.left]
  constructor
  · intro h
    exact congrArg (fun z : fieldPt Qbar ⟶ X => z.left) h
  · intro h
    exact Over.OverMorphism.ext h

/-- The value of `π₆` at `σ·x` is `σ(π₆(x))`; on a rational value it is unchanged. -/
theorem galPt_mem_fibre {X : Over (Spec (CommRingCat.of ℚ))} (π₆ : ToP1 X.left)
    (σ : Qbar ≃ₐ[ℚ] Qbar) (x : fieldPt Qbar ⟶ X) (j : ℚ)
    (hx : π₆.val (K := Qbar) x.left = OnePoint.some (algebraMap ℚ Qbar j)) :
    π₆.val (K := Qbar) (fieldMap (σ : Qbar →ₐ[ℚ] Qbar) ≫ x).left =
      OnePoint.some (algebraMap ℚ Qbar j) := by
  have e := ToP1.val_comp π₆ (((σ : Qbar →ₐ[ℚ] Qbar)) : Qbar →+* Qbar) (y := x.left)
  refine e.trans ?_
  rw [hx]
  change OnePoint.some (σ (algebraMap ℚ Qbar j)) = _
  rw [AlgEquiv.commutes]

/-! ## §C The root-pair algebra -/

theorem ne_neg_self' {a : Qbar} (ha : a ≠ 0) : a ≠ -a := by
  intro h
  apply ha
  have h2 : (2 : Qbar) * a = 0 := by linear_combination h
  rcases mul_eq_zero.mp h2 with h3 | h3
  · exact absurd h3 two_ne_zero
  · exact h3

theorem fix_iff_of_sq_eq (σ : Qbar ≃ₐ[ℚ] Qbar) {p a : Qbar} (h : p ^ 2 = a ^ 2) :
    σ p = p ↔ σ a = a := by
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp h with rfl | rfl
  · rfl
  · rw [map_neg, neg_inj]

/-! ## §D The points form of the Kummer model and the reduction of N2 -/

/-- **The Kummer description of the fibres of `π₆` over rational values, on `ℚ̄`-points**
(the points form of Elkies' model, see `X6KummerModel`): for rational `j₀ ∉ {0, −16/27}`, with
`t₀ = 1 + 27 j₀/16`, a bijection between the `ℚ̄`-points of `X` over `j₀` and the pairs
`(a, b) ∈ ℚ̄²` with `a² = −t₀`, `b² = 3(t₀ − 1)`, equivariant for `Aut(ℚ̄/ℚ)` (acting on points
by `x ↦ x ∘ Spec σ` and on pairs coordinatewise). -/
def KummerFibreEquiv (X : Over (Spec (CommRingCat.of ℚ))) (π₆ : ToP1 X.left) : Prop :=
  ∀ j₀ : ℚ, j₀ ≠ 0 → j₀ ≠ -16 / 27 →
    ∃ e : {x : fieldPt Qbar ⟶ X //
          π₆.val (K := Qbar) x.left = OnePoint.some (algebraMap ℚ Qbar j₀)} ≃
        {p : Qbar × Qbar // p.1 ^ 2 = -algebraMap ℚ Qbar (1 + 27 * j₀ / 16) ∧
          p.2 ^ 2 = 3 * (algebraMap ℚ Qbar (1 + 27 * j₀ / 16) - 1)},
      ∀ (σ : Qbar ≃ₐ[ℚ] Qbar) (x : fieldPt Qbar ⟶ X)
        (hx : π₆.val (K := Qbar) x.left = OnePoint.some (algebraMap ℚ Qbar j₀))
        (hσx : π₆.val (K := Qbar) (fieldMap (σ : Qbar →ₐ[ℚ] Qbar) ≫ x).left =
          OnePoint.some (algebraMap ℚ Qbar j₀)),
        (e ⟨fieldMap (σ : Qbar →ₐ[ℚ] Qbar) ≫ x, hσx⟩).1 =
          (σ (e ⟨x, hx⟩).1.1, σ (e ⟨x, hx⟩).1.2)

/-- **N2′ (intermediate)**: the Kummer description on every witness of the repaired bundle. -/
def X6KummerEquiv : Prop :=
  ∀ (Y : Over (Spec (CommRingCat.of ℚ))) (Φ : PtEquiv Y)
    (X : Over (Spec (CommRingCat.of ℚ))) (Ψ : (fieldPt Qbar ⟶ X) ≃ Quotient (pairSetoid Qbar))
    (fY : Y ⟶ X) (π₆ : ToP1 X.left), R1R2fpFullProps Y Φ X Ψ fY π₆ → KummerFibreEquiv X π₆

/-- **N2 from its points form (compiled).** (i) The residue field of `x` is the fixed field of
its stabilizer (`galPt_eq_self_iff`, infinite Galois theory); by the equivariant bijection the
stabilizer of `x` is that of its pair `(a₁, b₁) = (±a, ±b)`, i.e. the fixing group of
`ℚ(a, b)`. (ii) The four pairs `(±a, ±b)` are distinct (`t₀ ≠ 0, 1`). -/
theorem x6KummerFibre_of_equiv (hE : X6KummerEquiv) : X6KummerFibre := by
  intro Y Φ X Ψ fY π₆ hW j₀ hj0 hj1
  obtain ⟨e, he⟩ := hE Y Φ X Ψ fY π₆ hW j₀ hj0 hj1
  have ht0 : algebraMap ℚ Qbar (1 + 27 * j₀ / 16) ≠ 0 := by
    rw [map_ne_zero]
    intro h
    apply hj1
    linear_combination (16 / 27 : ℚ) * h
  have ht1 : algebraMap ℚ Qbar (1 + 27 * j₀ / 16) - 1 ≠ 0 := by
    rw [← map_one (algebraMap ℚ Qbar), ← map_sub, map_ne_zero]
    intro h
    apply hj0
    linear_combination (16 / 27 : ℚ) * h
  constructor
  · intro x hx a b ha hb
    apply intermediateField_eq_of_fix_iff
    intro σ
    rw [← galPt_eq_self_iff, fix_adjoin_iff]
    have hp := (e ⟨x, hx⟩).2
    have hσx := galPt_mem_fibre π₆ σ x j₀ hx
    have key : fieldMap (σ : Qbar →ₐ[ℚ] Qbar) ≫ x = x ↔
        (σ (e ⟨x, hx⟩).1.1 = (e ⟨x, hx⟩).1.1 ∧ σ (e ⟨x, hx⟩).1.2 = (e ⟨x, hx⟩).1.2) := by
      constructor
      · intro h
        have h1 := he σ x hx hσx
        have h2 : e ⟨fieldMap (σ : Qbar →ₐ[ℚ] Qbar) ≫ x, hσx⟩ = e ⟨x, hx⟩ :=
          congrArg e (Subtype.ext h)
        rw [h2] at h1
        exact ⟨(congrArg Prod.fst h1).symm, (congrArg Prod.snd h1).symm⟩
      · rintro ⟨h1, h2⟩
        have h3 := he σ x hx hσx
        have h4 : e ⟨fieldMap (σ : Qbar →ₐ[ℚ] Qbar) ≫ x, hσx⟩ = e ⟨x, hx⟩ := by
          apply Subtype.ext
          rw [h3, h1, h2]
        exact congrArg Subtype.val (e.injective h4)
    rw [key, fix_iff_of_sq_eq σ (hp.1.trans ha.symm), fix_iff_of_sq_eq σ (hp.2.trans hb.symm)]
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, forall_eq_or_imp, forall_eq]
  · obtain ⟨a, ha⟩ := IsAlgClosed.exists_pow_nat_eq (-algebraMap ℚ Qbar (1 + 27 * j₀ / 16))
      two_pos
    obtain ⟨b, hb⟩ := IsAlgClosed.exists_pow_nat_eq
      (3 * (algebraMap ℚ Qbar (1 + 27 * j₀ / 16) - 1)) two_pos
    have ha0 : a ≠ 0 := by
      rintro rfl
      apply ht0
      linear_combination ha
    have hb0 : b ≠ 0 := by
      rintro rfl
      apply ht1
      linear_combination (-1 / 3 : Qbar) * hb
    have na := ne_neg_self' ha0
    have nb := ne_neg_self' hb0
    have na' : -a ≠ a := fun h => na h.symm
    have nb' : -b ≠ b := fun h => nb h.symm
    let pr : Fin 4 → Qbar × Qbar := ![(a, b), (-a, b), (a, -b), (-a, -b)]
    have hpr : ∀ i, (pr i).1 ^ 2 = -algebraMap ℚ Qbar (1 + 27 * j₀ / 16) ∧
        (pr i).2 ^ 2 = 3 * (algebraMap ℚ Qbar (1 + 27 * j₀ / 16) - 1) := by
      intro i
      fin_cases i <;> simp [pr, ha, hb]
    have hinj : Function.Injective pr := by
      intro i j hij
      fin_cases i <;> fin_cases j <;> simp [pr, Prod.ext_iff, na, nb, na', nb'] at hij ⊢
    refine ⟨fun i => (e.symm ⟨pr i, hpr i⟩).1, ?_, fun i => (e.symm ⟨pr i, hpr i⟩).2⟩
    intro i j hij
    have h1 := e.symm.injective (Subtype.ext hij)
    exact hinj (congrArg Subtype.val h1)

end X6Kummer
