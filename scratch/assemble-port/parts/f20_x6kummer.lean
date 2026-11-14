/-! ## g0-assemble3: x6-kummer (scratch/x6-kummer/part{B,C,D,E}.lean, verbatim): N2 `FS5NoCM.X6KummerFibre` from
`MobiusGlue` and the leaf `X6KummerFibre.X6ConicModel` (`X6Kummer.x6KummerFibre_of_conic`). part0 (§A, fs5-nocm's
definitions, = part a60) and partR (mul-rigidity's Rigidity.lean, = part a15) are not repeated. -/
section G0A3x6_partB
noncomputable section

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

end
end G0A3x6_partB

section G0A3x6_partC
noncomputable section

namespace X6Kummer

open CategoryTheory AlgebraicGeometry Limits
open LeafQM.AV LeafQM.AV.Pin PkgI3 FS5NoCM

/-! ## §E Transport of the Kummer description between witnesses -/

/-- **N2-L (leaf, new): Elkies' Kummer model of `X₆ → X₆/W ≅ P¹`, on `ℚ̄`-points of one
witness.** Some witness `(Y₃, Φ, X₆, Ψ, fY, π₆)` of the (repaired) leaf bundle has the Kummer
description of the fibres of `π₆` over rational `j₀ ∉ {0, −16/27}` (`KummerFibreEquiv`).

*Published statement* (Elkies, "Shimura curve computations", ANTS-III, LNCS 1423 (1998), §3 on
`X*(6)` and its double covers; Kurihara, J. Fac. Sci. Univ. Tokyo 25 (1979), `X₀(6,1)` as the
conic `x² + y² + 3 = 0`; locators UNVERIFIED): `X₆ = X₀(6,1)` is the smooth conic
`C : Y² + 3X² + 3Z² = 0` over `ℚ`, the Atkin–Lehner group acts by the sign changes of `X`, `Y`,
and the quotient map `X₆ → X₆/W ≅ P¹` is `t = −X²/Z²` in Elkies' coordinate `t` on `X*(6)`
(`t = 0, 1, ∞` at the CM points of discriminants `−24, −4, −3`), i.e. `j = 16(t − 1)/27` in the
normalization of R2fp (`j = 0, ∞, −16/27` at `−4, −3, −24`: the Möbius map is fixed by the three
values). *Why the points form is a consequence*: over `j₀ ∈ ℚ` (`Z ≠ 0`, scale `Z = 1`) the points
of `C(ℚ̄)` are the `(X, Y) = (a, b)` with `a² = −t₀`, `b² = −3a² − 3 = 3(t₀ − 1)`; the bijection
`C(ℚ̄) ≅ X₆(ℚ̄)` of an isomorphism of `ℚ`-schemes commutes with `Aut(ℚ̄/ℚ)`. The constants `−1, 3`
are the ones of rv-h-cm §2.3, checked against González–Rotger Thm 5.12 on all 24 rational CM
points of Elkies' table by rv-nocm §1.3 Part B; the conic `Y² + 3X² + 3 = 0` and Kurihara's
`x² + y² + 3 = 0` both correspond to the quaternion algebra `(−1, −3)_ℚ`, ramified at `{3, ∞}`
(so they are isomorphic over `ℚ`; both have no real point). Existential over the witness, like
`LeafQM.AV.R1R2fp` itself: the genuine objects (Shimura–Deligne `Y₃`, the canonical model `X₆`,
Baba–Granath's `π₆`) are a witness. -/
def X6KummerModel : Prop :=
  ∃ (Y : Over (Spec (CommRingCat.of ℚ))) (Φ : PtEquiv Y)
    (X : Over (Spec (CommRingCat.of ℚ))) (Ψ : (fieldPt Qbar ⟶ X) ≃ Quotient (pairSetoid Qbar))
    (fY : Y ⟶ X) (π₆ : ToP1 X.left), R1R2fpFullProps Y Φ X Ψ fY π₆ ∧ KummerFibreEquiv X π₆

/-- **Glue (new): base change of a QM pair over `ℚ̄` along `σ ∈ Aut(ℚ̄/ℚ)` is unique up to
isomorphism of QM pairs.** Two pullback squares of `P.A → Spec ℚ̄` along `Spec σ` give a
`ℚ̄`-isomorphism `Q.A ≅ Q'.A` (uniqueness of pullbacks, `IsPullback.isoIsPullback`) commuting with
`ι` (both sides agree after the pullback projections) and fixing the identity sections; a pointed
morphism of abelian varieties is a homomorphism (rigidity, Mumford §4 Cor. 1; proved in Lean by
mul-rigidity, `G0FibreSimple.rigidityHom`), so it is an isomorphism of QM pairs. -/
def PairBaseChangeUnique : Prop :=
  ∀ (σ : Qbar ≃ₐ[ℚ] Qbar) (P Q Q' : QMPair Qbar),
    IsBaseChangeOfPair (σ : Qbar →+* Qbar) P Q → IsBaseChangeOfPair (σ : Qbar →+* Qbar) P Q' →
      Nonempty (QMIso Q.q Q'.q)

/-- CM objects of the three kinds from one witness of the repaired bundle (the kernel's
`cm_objects_of_R1R2fp`). -/
theorem cm_objects_of_props {Y : Over (Spec (CommRingCat.of ℚ))} {Φ : PtEquiv Y}
    {X : Over (Spec (CommRingCat.of ℚ))} {Ψ : (fieldPt Qbar ⟶ X) ≃ Quotient (pairSetoid Qbar)}
    {fY : Y ⟶ X} {π₆ : ToP1 X.left} (h : R1R2fpFullProps Y Φ X Ψ fY π₆) :
    (∃ P : QML3 Qbar, HasCM4 P.q) ∧ (∃ P : QML3 Qbar, HasCM3 P.q) ∧
      (∃ P : QML3 Qbar, HasCM24 P.q) :=
  cm_objects_of_R1R2fp ⟨Y, Φ, X, Ψ, fY, π₆, h⟩

/-- **Transport (compiled from `MobiusGlue` and `PairBaseChangeUnique`).** If one witness
`W₀` of the repaired bundle has the Kummer description, every witness `W` has it. The map
`H = Ψ₀⁻¹ ∘ Ψ : X(ℚ̄) ≃ X₀(ℚ̄)` satisfies `π₆ = π₀ ∘ H` (qm-pin's `phi_part` gives
`g : Y → Y₀` with `Φ = Φ₀ ∘ g`; `MobiusGlue` gives `π₆ ∘ fY = π₀ ∘ f₀ ∘ g`; `H ∘ fY = f₀ ∘ g` by
the forgetful clause; `fY` is onto `X(ℚ̄)`) and commutes with `Aut(ℚ̄/ℚ)` (the Galois clause of
`X6Props` on both witnesses, and `PairBaseChangeUnique`). -/
theorem kummerFibreEquiv_transport (hM : MobiusGlue) (hB : PairBaseChangeUnique)
    {Y₀ : Over (Spec (CommRingCat.of ℚ))} {Φ₀ : PtEquiv Y₀}
    {X₀ : Over (Spec (CommRingCat.of ℚ))} {Ψ₀ : (fieldPt Qbar ⟶ X₀) ≃ Quotient (pairSetoid Qbar)}
    {f₀ : Y₀ ⟶ X₀} {π₀ : ToP1 X₀.left} (h₀ : R1R2fpFullProps Y₀ Φ₀ X₀ Ψ₀ f₀ π₀)
    (hK₀ : KummerFibreEquiv X₀ π₀)
    {Y : Over (Spec (CommRingCat.of ℚ))} {Φ : PtEquiv Y}
    {X : Over (Spec (CommRingCat.of ℚ))} {Ψ : (fieldPt Qbar ⟶ X) ≃ Quotient (pairSetoid Qbar)}
    {fY : Y ⟶ X} {π₆ : ToP1 X.left} (h : R1R2fpFullProps Y Φ X Ψ fY π₆) :
    KummerFibreEquiv X π₆ := by
  obtain ⟨g, hg⟩ := phi_part (R1fpProps.univ h₀.1) h.1
  have hR₀ := R2fpProps_of_X6 h₀.2.2.1 h₀.2.2.2.1
  have hR := R2fpProps_of_X6 h.2.2.1 h.2.2.2.1
  have hπ := hM Y₀ Y Φ₀ Φ _ _ g h₀.1 hR₀ h.1 hR (cm_objects_of_props h₀) hg
  obtain ⟨-, -, -, hgal, -, hf⟩ := h.2.2.1
  obtain ⟨-, -, -, hgal₀, -, hf₀⟩ := h₀.2.2.1
  obtain ⟨-, hs⟩ := h.2.2.2.2.2.2.1
  let H : (fieldPt Qbar ⟶ X) ≃ (fieldPt Qbar ⟶ X₀) := Ψ.trans Ψ₀.symm
  have hH : ∀ x, Ψ₀ (H x) = Ψ x := fun x => Ψ₀.apply_symm_apply _
  have hHy : ∀ y : fieldPt Qbar ⟶ Y, H (y ≫ fY) = (y ≫ g) ≫ f₀ := by
    intro y
    apply Ψ₀.injective
    rw [hH, hf y _ ((hg Qbar y).trans (Quotient.out_eq _).symm),
      hf₀ (y ≫ g) _ (Quotient.out_eq _).symm]
  have hπH : ∀ x, π₆.val (K := Qbar) x.left = π₀.val (K := Qbar) (H x).left := by
    intro x
    obtain ⟨y, rfl⟩ := hs x
    rw [hHy y]
    calc π₆.val (K := Qbar) (y ≫ fY).left = (π₆.comp fY.left).val (K := Qbar) y.left :=
          (ToP1.val_comp_right π₆ fY.left y.left).symm
      _ = (π₀.comp f₀.left).val (K := Qbar) (y ≫ g).left := hπ y
      _ = π₀.val (K := Qbar) ((y ≫ g) ≫ f₀).left := ToP1.val_comp_right π₀ f₀.left (y ≫ g).left
  have hgalH : ∀ (σ : Qbar ≃ₐ[ℚ] Qbar) (x : fieldPt Qbar ⟶ X),
      H (fieldMap (σ : Qbar →ₐ[ℚ] Qbar) ≫ x) = fieldMap (σ : Qbar →ₐ[ℚ] Qbar) ≫ H x := by
    intro σ x
    apply Ψ₀.injective
    rw [hH]
    obtain ⟨Q, hQ, hbQ⟩ := hgal σ x (Quotient.out (Ψ x)) (Quotient.out_eq _).symm
    obtain ⟨Q', hQ', hbQ'⟩ := hgal₀ σ (H x) (Quotient.out (Ψ x))
      ((hH x).trans (Quotient.out_eq _).symm)
    rw [hQ, hQ']
    obtain ⟨i⟩ := hB σ _ Q Q' hbQ hbQ'
    exact Quotient.sound ⟨i⟩
  intro j₀ hj0 hj1
  obtain ⟨e₀, he₀⟩ := hK₀ j₀ hj0 hj1
  let F : {x : fieldPt Qbar ⟶ X //
        π₆.val (K := Qbar) x.left = OnePoint.some (algebraMap ℚ Qbar j₀)} ≃
      {x : fieldPt Qbar ⟶ X₀ //
        π₀.val (K := Qbar) x.left = OnePoint.some (algebraMap ℚ Qbar j₀)} :=
    H.subtypeEquiv (fun x => by rw [hπH x])
  refine ⟨F.trans e₀, ?_⟩
  intro σ x hx hσx
  have hmem := galPt_mem_fibre π₀ σ (H x) j₀ ((hπH x).symm.trans hx)
  have h1 : F ⟨fieldMap (σ : Qbar →ₐ[ℚ] Qbar) ≫ x, hσx⟩ =
      ⟨fieldMap (σ : Qbar →ₐ[ℚ] Qbar) ≫ H x, hmem⟩ := Subtype.ext (hgalH σ x)
  simp only [Equiv.trans_apply]
  rw [h1]
  exact he₀ σ (H x) _ hmem

/-- **N2′ from the leaf N2-L and glue (compiled).** -/
theorem x6KummerEquiv_of_model (hM : MobiusGlue) (hB : PairBaseChangeUnique)
    (hL : X6KummerModel) : X6KummerEquiv := by
  obtain ⟨Y₀, Φ₀, X₀, Ψ₀, f₀, π₀, h₀, hK₀⟩ := hL
  intro Y Φ X Ψ fY π₆ h
  exact kummerFibreEquiv_transport hM hB h₀ hK₀ h

/-- **N2 `X6KummerFibre` from the leaf N2-L `X6KummerModel`, the existing curve glue
`MobiusGlue` and the new glue `PairBaseChangeUnique` (compiled).** -/
theorem x6KummerFibre_of_model (hM : MobiusGlue) (hB : PairBaseChangeUnique)
    (hL : X6KummerModel) : X6KummerFibre :=
  x6KummerFibre_of_equiv (x6KummerEquiv_of_model hM hB hL)

end X6Kummer


end
end G0A3x6_partC

section G0A3x6_partD
noncomputable section

namespace X6Kummer

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open LeafQM.AV LeafQM.AV.Pin PkgI3 FS5NoCM

/-! ## §F `PairBaseChangeUnique` is a theorem (pullback uniqueness and rigidity) -/

/-- The identity `ℚ̄`-point of an abelian variety over `ℚ̄`, as a morphism of schemes, is the
underlying morphism of the unit `η`. -/
theorem one_pt_left (A : AbVar Qbar) :
    (1 : A.Pt Qbar).left = (η[A.X]).left := by
  rw [Hom.one_def, Over.comp_left, Over.toUnit_left]
  change Spec.map (CommRingCat.ofHom (algebraMap Qbar Qbar)) ≫ _ = _
  rw [Algebra.algebraMap_self, CommRingCat.ofHom_id, Spec.map_id, Category.id_comp]

/-- **`PairBaseChangeUnique` holds.** The two pullback squares give `e : Q.A ≅ Q'.A` over
`Spec ℚ̄` (`IsPullback.isoIsPullback`); `e` and `e⁻¹` fix the identity sections and commute with
`ι` (checked after the pullback projections, `IsPullback.hom_ext`); by rigidity
(`G0FibreSimple.rigidityHom`, mul-rigidity) both are homomorphisms. -/
theorem pairBaseChangeUnique : PairBaseChangeUnique := by
  intro σ P Q Q' ⟨g, hpb, hι, h1⟩ ⟨g', hpb', hι', h1'⟩
  rw [one_pt_left, one_pt_left] at h1 h1'
  let e := hpb.isoIsPullback _ _ hpb'
  have ehf : e.hom ≫ g' = g := by simp [e]
  have ehs : e.hom ≫ Q'.A.X.hom = Q.A.X.hom := by simp [e]
  have eif : e.inv ≫ g = g' := by simp [e]
  have eis : e.inv ≫ Q.A.X.hom = Q'.A.X.hom := by simp [e]
  let eH : Q.A.X ⟶ Q'.A.X := Over.homMk e.hom ehs
  let eI : Q'.A.X ⟶ Q.A.X := Over.homMk e.inv eis
  have hη : η[Q.A.X] ≫ eH = η[Q'.A.X] := by
    apply Over.OverMorphism.ext
    rw [Over.comp_left]
    apply hpb'.hom_ext
    · change ((η[Q.A.X]).left ≫ e.hom) ≫ g' = (η[Q'.A.X]).left ≫ g'
      rw [Category.assoc, ehf]
      exact h1.trans h1'.symm
    · change ((η[Q.A.X]).left ≫ e.hom) ≫ Q'.A.X.hom = (η[Q'.A.X]).left ≫ Q'.A.X.hom
      rw [Category.assoc, ehs, Over.w, Over.w]
  have hη' : η[Q'.A.X] ≫ eI = η[Q.A.X] := by
    rw [← hη, Category.assoc]
    have : eH ≫ eI = 𝟙 _ := by
      apply Over.OverMorphism.ext
      exact e.hom_inv_id
    rw [this, Category.comp_id]
  have : IsMonHom eH := G0FibreSimple.rigidityHom Qbar Q.A Q'.A eH hη
  have : IsMonHom eI := G0FibreSimple.rigidityHom Qbar Q'.A Q.A eI hη'
  refine ⟨⟨AbVar.Hom.mk' eH, AbVar.Hom.mk' eI, ?_, ?_, ?_⟩⟩
  · apply Over.OverMorphism.ext
    exact e.hom_inv_id
  · apply Over.OverMorphism.ext
    exact e.inv_hom_id
  · intro a
    simp only [AbVar.Hom.hom_mk']
    apply Over.OverMorphism.ext
    rw [Over.comp_left, Over.comp_left]
    apply hpb'.hom_ext
    · change ((Q.q.iota a).hom.left ≫ e.hom) ≫ g' = (e.hom ≫ (Q'.q.iota a).hom.left) ≫ g'
      rw [Category.assoc, ehf, hι a, Category.assoc, hι' a, ← Category.assoc, ehf]
    · change ((Q.q.iota a).hom.left ≫ e.hom) ≫ Q'.A.X.hom =
        (e.hom ≫ (Q'.q.iota a).hom.left) ≫ Q'.A.X.hom
      rw [Category.assoc, ehs, Category.assoc, Over.w, Over.w, ehs]

/-- **N2 `X6KummerFibre` from the leaf N2-L `X6KummerModel` and the curve glue `MobiusGlue`
(compiled; `PairBaseChangeUnique` is now a theorem).** -/
theorem x6KummerFibre_of_model' (hM : MobiusGlue) (hL : X6KummerModel) : X6KummerFibre :=
  x6KummerFibre_of_model hM pairBaseChangeUnique hL

end X6Kummer


end
end G0A3x6_partD

section G0A3x6_partE
noncomputable section

namespace X6Kummer

open CategoryTheory AlgebraicGeometry Limits
open LeafQM.AV LeafQM.AV.Pin PkgI3 FS5NoCM

/-! ## §G The leaf in its global (conic) form, and the fibre form from it -/

/-- The `ℚ̄`-points of the conic `C : Y² + 3X² + 3Z² = 0`: the affine part `Z = 1`
(`(X, Y) = (p.1, p.2)` with `p.2² + 3 p.1² + 3 = 0`) and the two points at infinity `[1 : b : 0]`,
`b² = −3`. -/
abbrev ConicPt : Type :=
  {p : Qbar × Qbar // p.2 ^ 2 + 3 * p.1 ^ 2 + 3 = 0} ⊕ {b : Qbar // b ^ 2 = -3}

/-- `Aut(ℚ̄/ℚ)` acting on `C(ℚ̄)` coordinatewise (`C` is defined over `ℚ`). -/
def conicGal (σ : Qbar ≃ₐ[ℚ] Qbar) : ConicPt → ConicPt
  | Sum.inl p => Sum.inl ⟨(σ p.1.1, σ p.1.2), by
      have h := congrArg σ p.2
      simp only [map_add, map_mul, map_pow, map_ofNat, map_zero] at h
      exact h⟩
  | Sum.inr b => Sum.inr ⟨σ b.1, by
      have h := congrArg σ b.2
      simp only [map_pow, map_neg, map_ofNat] at h
      exact h⟩

/-- **The conic model of `(X₆, π₆)` on `ℚ̄`-points**: a bijection `X(ℚ̄) ≃ C(ℚ̄)` commuting with
`Aut(ℚ̄/ℚ)`, under which `π₆ = −16(X² + Z²)/(27 Z²)` (so `∞` at the points at infinity). -/
def ConicModel (X : Over (Spec (CommRingCat.of ℚ))) (π₆ : ToP1 X.left) : Prop :=
  ∃ e : (fieldPt Qbar ⟶ X) ≃ ConicPt,
    (∀ (σ : Qbar ≃ₐ[ℚ] Qbar) (x : fieldPt Qbar ⟶ X),
      e (fieldMap (σ : Qbar →ₐ[ℚ] Qbar) ≫ x) = conicGal σ (e x)) ∧
    (∀ (x : fieldPt Qbar ⟶ X) p, e x = Sum.inl p →
      π₆.val (K := Qbar) x.left = OnePoint.some (-16 * (p.1.1 ^ 2 + 1) / 27)) ∧
    (∀ (x : fieldPt Qbar ⟶ X) b, e x = Sum.inr b → π₆.val (K := Qbar) x.left = OnePoint.infty)

/-- **N2-L′ (leaf, new; the global form of `X6KummerModel`): `X₆ = X₀(6,1)` is the conic
`Y² + 3X² + 3Z² = 0` with `π₆ = −16(X² + Z²)/(27 Z²)`, on `ℚ̄`-points of one witness.**

*Published statement* (Kurihara, J. Fac. Sci. Univ. Tokyo 25 (1979): `X₀(6,1) : x² + y² + 3 = 0`;
Elkies, ANTS-III, LNCS 1423 (1998), §3: `X*(6) = X₆/W` with coordinate `t`, `t = 0, 1, ∞` at the
CM points of discriminants `−24, −4, −3`, and `X₆ = X*(6)(√−t, √(3(t − 1)))`; locators
UNVERIFIED, no network). Put `X = √−t`, `Y = √(3(t−1))`, `Z = 1`: then `Y² + 3X² + 3 = 0`,
`t = −X²/Z²`, `W` acts by the sign changes, and `j = 16(t − 1)/27 = −16(X² + Z²)/(27 Z²)` is the
coordinate of R2fp (`j = 0, ∞, −16/27` at `−4, −3, −24`; a Möbius map is fixed by three values).
An isomorphism of `ℚ`-schemes `X₆ ≅ C` gives a bijection on `ℚ̄`-points commuting with
`Aut(ℚ̄/ℚ)`, compatible with the maps to `P¹`. Consistency checks (VERIFIED by computation in
`scratch/x6-kummer/conic_check.py`): the involutions `X ↦ −X`, `Y ↦ −Y`, `(X,Y) ↦ (−X,−Y)` fix
exactly the two points over `j = −16/27`, `0`, `∞` respectively (Riemann–Hurwitz for a
`(ℤ/2)²`-cover of `P¹` by a genus-0 curve); the residue fields there are `ℚ(√−3)`, `ℚ(i)`,
`ℚ(√−3)`, as González–Rotger Thm 5.12 (the bundle's `R5ptProps`) requires for `ℤ[√−6]` (`b = 0`,
`h = 2`), `ℤ[i]` (`b = 1`, `h = 1`, contains `ℚ(i)`), `ℤ[ζ₃]` (`b = 1`, `h = 1`, contains
`ℚ(√−3)`); `C` and Kurihara's conic both correspond to `(−1, −3)_ℚ`, ramified at `{3, ∞}`. The
fibre fields `ℚ(√−t, √(3(t−1)))` were checked against González–Rotger Thm 5.12 on all 24 rational
CM points of Elkies' table by rv-nocm §1.3 Part B. -/
def X6ConicModel : Prop :=
  ∃ (Y : Over (Spec (CommRingCat.of ℚ))) (Φ : PtEquiv Y)
    (X : Over (Spec (CommRingCat.of ℚ))) (Ψ : (fieldPt Qbar ⟶ X) ≃ Quotient (pairSetoid Qbar))
    (fY : Y ⟶ X) (π₆ : ToP1 X.left), R1R2fpFullProps Y Φ X Ψ fY π₆ ∧ ConicModel X π₆

/-- The fibre condition on the affine conic: `−16(a² + 1)/27 = j₀` iff `a² = −t₀`, and then
`b² = 3(t₀ − 1)`. -/
theorem conic_fibre_iff (j₀ : ℚ) (a b : Qbar) (hab : b ^ 2 + 3 * a ^ 2 + 3 = 0) :
    (-16 * (a ^ 2 + 1) / 27 = algebraMap ℚ Qbar j₀) ↔
      (a ^ 2 = -algebraMap ℚ Qbar (1 + 27 * j₀ / 16) ∧
        b ^ 2 = 3 * (algebraMap ℚ Qbar (1 + 27 * j₀ / 16) - 1)) := by
  have ht : algebraMap ℚ Qbar (1 + 27 * j₀ / 16) = 1 + 27 * algebraMap ℚ Qbar j₀ / 16 := by
    simp only [map_add, map_one, map_div₀, map_mul, map_ofNat]
  rw [ht]
  constructor
  · intro h
    refine ⟨by linear_combination (-27 / 16 : Qbar) * h, by linear_combination hab + (81 / 16 : Qbar) * h⟩
  · rintro ⟨h1, -⟩
    linear_combination (-16 / 27 : Qbar) * h1

/-- **The fibre form from the conic form (compiled).** -/
theorem kummerFibreEquiv_of_conic {X : Over (Spec (CommRingCat.of ℚ))} {π₆ : ToP1 X.left}
    (hC : ConicModel X π₆) : KummerFibreEquiv X π₆ := by
  obtain ⟨e, he, hin, hinf⟩ := hC
  intro j₀ _ _
  -- every point of the fibre is affine
  have aff : ∀ x : fieldPt Qbar ⟶ X,
      π₆.val (K := Qbar) x.left = OnePoint.some (algebraMap ℚ Qbar j₀) →
      ∃ p, e x = Sum.inl p := by
    intro x hx
    rcases hex : e x with p | b
    · exact ⟨p, rfl⟩
    · rw [hinf x b hex] at hx
      exact absurd hx (by simp [OnePoint.infty, OnePoint.some])
  have val_of : ∀ (x : fieldPt Qbar ⟶ X) p, e x = Sum.inl p →
      π₆.val (K := Qbar) x.left = OnePoint.some (algebraMap ℚ Qbar j₀) →
      -16 * (p.1.1 ^ 2 + 1) / 27 = algebraMap ℚ Qbar j₀ := by
    intro x p hp hx
    rw [hin x p hp] at hx
    exact Option.some.inj hx
  let g : ConicPt → Qbar × Qbar := Sum.elim (fun p => p.1) (fun _ => (0, 0))
  have hg : ∀ (x : fieldPt Qbar ⟶ X),
      π₆.val (K := Qbar) x.left = OnePoint.some (algebraMap ℚ Qbar j₀) →
      (g (e x)).1 ^ 2 = -algebraMap ℚ Qbar (1 + 27 * j₀ / 16) ∧
        (g (e x)).2 ^ 2 = 3 * (algebraMap ℚ Qbar (1 + 27 * j₀ / 16) - 1) := by
    intro x hx
    obtain ⟨p, hp⟩ := aff x hx
    rw [hp]
    exact (conic_fibre_iff j₀ p.1.1 p.1.2 p.2).mp (val_of x p hp hx)
  let f : {x : fieldPt Qbar ⟶ X //
        π₆.val (K := Qbar) x.left = OnePoint.some (algebraMap ℚ Qbar j₀)} →
      {p : Qbar × Qbar // p.1 ^ 2 = -algebraMap ℚ Qbar (1 + 27 * j₀ / 16) ∧
        p.2 ^ 2 = 3 * (algebraMap ℚ Qbar (1 + 27 * j₀ / 16) - 1)} :=
    fun x => ⟨g (e x.1), hg x.1 x.2⟩
  have hbij : Function.Bijective f := by
    constructor
    · rintro ⟨x, hx⟩ ⟨x', hx'⟩ h
      obtain ⟨p, hp⟩ := aff x hx
      obtain ⟨p', hp'⟩ := aff x' hx'
      have h1 : g (e x) = g (e x') := congrArg Subtype.val h
      rw [hp, hp'] at h1
      have h2 : p = p' := Subtype.ext h1
      apply Subtype.ext
      apply e.injective
      rw [hp, hp', h2]
    · rintro ⟨⟨a, b⟩, hab⟩
      have hon : b ^ 2 + 3 * a ^ 2 + 3 = 0 := by
        obtain ⟨h1, h2⟩ := hab
        linear_combination h2 + 3 * h1
      let c : ConicPt := Sum.inl ⟨(a, b), hon⟩
      have hx : π₆.val (K := Qbar) (e.symm c).left = OnePoint.some (algebraMap ℚ Qbar j₀) := by
        rw [hin (e.symm c) ⟨(a, b), hon⟩ (e.apply_symm_apply c)]
        congr 1
        exact (conic_fibre_iff j₀ a b hon).mpr hab
      refine ⟨⟨e.symm c, hx⟩, ?_⟩
      apply Subtype.ext
      change g (e (e.symm c)) = (a, b)
      rw [e.apply_symm_apply]
      rfl
  refine ⟨Equiv.ofBijective f hbij, ?_⟩
  intro σ x hx hσx
  change g (e (fieldMap (σ : Qbar →ₐ[ℚ] Qbar) ≫ x)) = (σ (g (e x)).1, σ (g (e x)).2)
  obtain ⟨p, hp⟩ := aff x hx
  rw [he σ x, hp]
  rfl

/-- **N2 from the conic leaf (compiled).** -/
theorem x6KummerModel_of_conic (hL : X6ConicModel) : X6KummerModel := by
  obtain ⟨Y, Φ, X, Ψ, fY, π₆, h, hC⟩ := hL
  exact ⟨Y, Φ, X, Ψ, fY, π₆, h, kummerFibreEquiv_of_conic hC⟩

/-- **N2 `X6KummerFibre` from the conic leaf `X6ConicModel` and `MobiusGlue` (compiled).** -/
theorem x6KummerFibre_of_conic (hM : MobiusGlue) (hL : X6ConicModel) : X6KummerFibre :=
  x6KummerFibre_of_model' hM (x6KummerModel_of_conic hL)

end X6Kummer


end
end G0A3x6_partE
