import ZInQKernel.Contrib.OneProof.GaudronRemondSection9SS

/-!
# `gaudronRemondSec9LowerAnSS` as printed: Gaudron–Rémond, Duke Math. J. 163 (2014), p. 2101

The row `gaudronRemondSec9LowerAnSS` (`ZInQ.BostGR9.GaudronRemondSec9LowerAnSS`) is Bost's lower bound
h_F(A) ≥ −(3/2) dim A for the stable Faltings height in Faltings' original normalization. Its recorded source,
Gaudron–Rémond, Comment. Math. Helv. 89 (2014), Cor. 8.4, proves a stronger bound, and a replacement of the row by
a stronger statement is declined. The inequality of the row itself is printed in Gaudron–Rémond, *Polarisations et
isogénies*, Duke Math. J. 163 (2014), the paper the manuscript cites (§9): on p. 2101, for an abelian variety A of
dimension g ≥ 1 over a number field (the setting of p. 2058), and on pp. 2098 and 2102 for the abelian varieties met
in the proofs. The print attributes the bound to Bost and does not prove it there (a report).

The row also covers g = 0, which the print does not. That case is proved here: an abelian variety of dimension 0 is
`Spec K`, each of its group models has a single complex point at each embedding τ, and the height is 0.

* `GaudronRemondDuke163Bost`: the printed statement, in the row's Lean form, for g ≥ 1 as printed.
* `isAnStableHeightSS_eq_zero_of_dim_zero`, `isAnStableHeightSS_nonneg_of_dim_zero`: at g = 0 the height is 0
  (proved).
* `gaudronRemondSec9LowerAnSS_of_duke163`, `duke163_of_gaudronRemondSec9LowerAnSS`, `gaudronRemondDuke163Bost_iff`:
  the printed statement is equivalent to the row (g = 0 by the proof here, g ≥ 1 by the print).
-/

set_option autoImplicit false

namespace ZInQ.GRDuke163

/-! ## The case g = 0 of the row (proved) -/

section DimZero

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open MeasureTheory NumberField
open ZInQ.DefFaltings ZInQ.HeightDict ZInQ.R3Residual ZInQ.HeightFix
open scoped TensorProduct

/-- **An abelian variety of dimension 0 is one point.** Its underlying space is irreducible (the scheme is
integral) with generic point `ξ`; a point `x ≠ ξ` would give the chain `closure {x} ⊊ closure {ξ}` of irreducible
closed subsets (the space is `T₀`), so the Krull dimension would be positive. -/
theorem subsingleton_of_dim_zero {K : Type} [Field K] (A : PkgI3.AbVar K) (hA : A.dim = (0 : ℕ)) :
    Subsingleton A.X.left := by
  have hdim : topologicalKrullDim A.X.left = 0 := by
    simpa [PkgI3.AbVar.dim] using hA
  have huniv : closure {genericPoint A.X.left} = Set.univ := genericPoint_spec A.X.left
  have key : ∀ x : A.X.left, x = genericPoint A.X.left := by
    intro x
    by_contra hne
    have hpos : 0 < topologicalKrullDim A.X.left := by
      unfold topologicalKrullDim
      rw [Order.krullDim_pos_iff]
      refine ⟨⟨closure {x}, isIrreducible_singleton.closure, isClosed_closure⟩,
        ⟨closure {genericPoint A.X.left}, isIrreducible_singleton.closure, isClosed_closure⟩, ?_⟩
      refine lt_of_le_of_ne ?_ ?_
      · show closure {x} ⊆ closure {genericPoint A.X.left}
        rw [huniv]
        exact Set.subset_univ _
      · intro h
        have h' : closure {x} = closure {genericPoint A.X.left} := congrArg (·.carrier) h
        exact hne ((show IsGenericPoint x Set.univ from h'.trans huniv).eq
          (genericPoint_spec A.X.left))
    rw [hdim] at hpos
    exact lt_irrefl _ hpos
  exact ⟨fun a b => (key a).trans (key b).symm⟩

/-- **An abelian variety of dimension 0 is `Spec K`.** The unit section `e : Spec K → A` is a section of the
separated structure morphism, hence a closed immersion; it is onto the one-point space `A`, whose scheme is reduced,
so `e` is an isomorphism, with inverse the structure morphism. -/
theorem isIso_hom_of_dim_zero {K : Type} [Field K] (A : PkgI3.AbVar K) (hA : A.dim = (0 : ℕ)) :
    IsIso A.X.hom := by
  have := subsingleton_of_dim_zero A hA
  let e : Spec (CommRingCat.of K) ⟶ A.X.left :=
    (η[A.X] : 𝟙_ (Over (Spec (CommRingCat.of K))) ⟶ A.X).left
  have he : e ≫ A.X.hom = 𝟙 _ := Over.w η[A.X]
  have : IsClosedImmersion (e ≫ A.X.hom) := by
    rw [he]
    infer_instance
  have : IsClosedImmersion e := IsClosedImmersion.of_comp e A.X.hom
  have : Surjective e := ⟨fun _ => ⟨Classical.arbitrary _, Subsingleton.elim _ _⟩⟩
  have : IsIso e := isIso_of_isClosedImmersion_of_surjective e
  rw [← IsIso.inv_eq_of_hom_inv_id he]
  infer_instance

/-- **For `dim A = 0`, a group model has at most one complex point at `τ`.** A point `p : Spec ℂ → 𝒢` over
`τ|_{𝓞_L}` factors through the generic fibre `𝒢_L ≅ A_L`, whose structure morphism to `Spec L` is an isomorphism
(the base change of `A ≅ Spec K`); so the factorization, hence `p`, is determined by `Spec ℂ → Spec L`. -/
theorem pts_subsingleton_of_dim_zero {K : Type} [Field K] {A : PkgI3.AbVar K} {L : Type} [Field L]
    [NumberField L] [Algebra K L] (𝒢 : GroupModel A L) (hA : A.dim = (0 : ℕ)) (τ : L →+* ℂ) :
    Subsingleton (𝒢.Pts τ) := by
  have := isIso_hom_of_dim_zero A hA
  have h1 : IsIso (A.baseChange L).X.hom :=
    pullback_snd_iso_of_left_iso A.X.hom (Spec.map (CommRingCat.ofHom (algebraMap K L)))
  have : IsIso 𝒢.gen.hom.left := (Over.forget _).map_isIso 𝒢.gen.hom
  have h2 : IsIso (genericFibre L 𝒢.G).hom := by
    rw [← Over.w 𝒢.gen.hom]
    infer_instance
  let jL : Spec (CommRingCat.of L) ⟶ Spec (CommRingCat.of (𝓞 L)) :=
    Spec.map (CommRingCat.ofHom (algebraMap (𝓞 L) L))
  let jτ : (GroupModel.ptC τ).left ⟶ Spec (CommRingCat.of L) := Spec.map (CommRingCat.ofHom τ)
  have h3 : IsIso (pullback.snd 𝒢.G.hom jL) := h2
  have hw : ∀ p : 𝒢.Pts τ, p.left ≫ 𝒢.G.hom = jτ ≫ jL := by
    intro p
    rw [Over.w p]
    simp only [jτ, jL, GroupModel.ptC, Over.mk_hom, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  constructor
  intro p q
  apply Over.OverMorphism.ext
  have hl : pullback.lift p.left jτ (hw p) = pullback.lift q.left jτ (hw q) :=
    (cancel_mono (pullback.snd 𝒢.G.hom jL)).1
      ((pullback.lift_snd _ _ _).trans (pullback.lift_snd _ _ _).symm)
  rw [← pullback.lift_fst p.left jτ (hw p), ← pullback.lift_fst q.left jτ (hw q), hl]

/-- In a vector space, `m • w = l • w` with `w ≠ 0` gives `l = m`. -/
theorem eq_of_smul_eq_smul_of_ne_zero {F V : Type*} [Field F] [AddCommGroup V] [Module F V] {w : V}
    (hw : w ≠ 0) {l m : F} (h : m • w = l • w) : l = m := by
  by_contra hne
  apply hw
  have hne' : l - m ≠ 0 := sub_ne_zero.mpr hne
  have h0 : (l - m) • w = 0 := by rw [sub_smul, ← h, sub_self]
  rw [← inv_smul_smul₀ hne' w, h0, smul_zero]

/-- Lebesgue measure on `ℂ⁰` is the unit point mass: `λ(ℂ⁰) = 1`. -/
theorem volume_univ_fin_zero : (volume (Set.univ : Set (Fin 0 → ℂ))).toReal = 1 := by
  rw [MeasureTheory.volume_pi, Measure.pi_univ]
  simp

/-- **At g = 0 the height is 0.** For `dim A = 0` and `x` as in `ZInQ.SemistabAssembly.IsAnStableHeightSS`:
* the lattice `⋀⁰ω` is the `𝓞_L`-span of `w₀ = 1 ⊗ 1`, so `η = a • w₀` with `a ≠ 0` and
  `#(⋀⁰ω / 𝓞_L η) = |N_{L/ℚ}(a)|` (`secIndex_smul`);
* the complex points at `τ` are a single point (`pts_subsingleton_of_dim_zero`), and the measure `|τ a|² δ₁` has
  the density of `(i/2)⁰ η̃ ∧ η̄̃` in every chart (`ℂ⁰` is a point of Lebesgue measure 1 and every derivative has
  determinant 1), so the metric is `‖η‖²_τ = |τ a|²`;
* hence `x = (log |N a| − ½ ∑_τ log |τ a|²)/[L:ℚ] = 0` (`sum_log_norm_embeddings_int`). -/
theorem isAnStableHeightSS_eq_zero_of_dim_zero {K : Type} [Field K] (A : PkgI3.AbVar K)
    (hA : A.dim = (0 : ℕ)) (x : ℝ) (hx : ZInQ.SemistabAssembly.IsAnStableHeightSS A x) : x = 0 := by
  obtain ⟨L, iF, iN, iA, 𝒩, g, -, -, hdim, eta, hetaM, heta0, -, r, hr, rfl⟩ := hx
  have hg : g = 0 := by
    rw [hA] at hdim
    exact_mod_cast hdim.symm
  subst hg
  have hfun : ∀ u v : Fin 0 → 𝒩.cotangent, u = v := fun u v => funext fun i => i.elim0
  set w₀ : 𝒩.hodgeSpace 0 :=
    (1 : L) ⊗ₜ[𝓞 L] exteriorPower.ιMulti (𝓞 L) 0 (fun i : Fin 0 => (i.elim0 : 𝒩.cotangent))
    with hw₀
  -- the lattice `⋀⁰ω` is `𝓞_L w₀`
  have hM : printedDetLattice 𝒩 0 = Submodule.span (𝓞 L) {w₀} := by
    unfold printedDetLattice
    congr 1
    ext y
    simp only [Set.mem_range, Set.mem_singleton_iff]
    constructor
    · rintro ⟨v, rfl⟩
      rw [hw₀]
      congr 2
      exact hfun _ _
    · rintro rfl
      exact ⟨fun i => i.elim0, by rw [hw₀]; congr 2; exact hfun _ _⟩
  rw [hM, Submodule.mem_span_singleton] at hetaM
  obtain ⟨a, rfl⟩ := hetaM
  have ha : a ≠ 0 := by
    rintro rfl
    exact heta0 (zero_smul _ _)
  have hw0 : w₀ ≠ 0 := by
    intro h
    exact heta0 (by rw [h, smul_zero])
  -- the index is `|N(a)|`
  have hsec : secIndex (printedDetLattice 𝒩 0) (a • w₀) = (Algebra.norm ℤ a).natAbs := by
    rw [hM, secIndex_smul _ (Submodule.mem_span_singleton_self w₀) hw0 a]
    have h1 : secIndex (Submodule.span (𝓞 L) {w₀}) w₀ = 1 := by
      unfold secIndex
      exact AddSubgroup.relIndex_self _
    rw [h1, _root_.mul_one]
  -- the metric at `τ` is `|τ a|²`
  have hrτ : ∀ τ : L →+* ℂ, r τ = ‖τ (algebraMap (𝓞 L) L a)‖ ^ 2 := by
    intro τ
    let _ : TopologicalSpace (𝒩.Pts τ) := ZInQ.HeightGlue.anTop 𝒩 τ
    let _ : MeasurableSpace (𝒩.Pts τ) := anBorel 𝒩 τ
    have := pts_subsingleton_of_dim_zero 𝒩 hA τ
    let c : NNReal := ‖τ (algebraMap (𝓞 L) L a)‖₊ ^ 2
    let nu₀ : Measure (𝒩.Pts τ) := c • Measure.dirac 1
    have hfin : IsFiniteMeasure nu₀ := inferInstance
    have hdens : ∀ p, HasAnFormDensityAt 𝒩 τ nu₀ (a • w₀) p := by
      intro p φ _ _ U hU s hm l hl ε hε
      refine ⟨Set.univ, Filter.univ_mem, fun E _ _ => ?_⟩
      have hwedge : 𝒩.wedge (fun i => ⟨_, hm i⟩) = w₀ := by
        unfold GroupModel.wedge
        rw [hw₀]
        congr 2
        exact hfun _ _
      rw [hwedge, ← algebraMap_smul L a w₀] at hl
      have hla : l = algebraMap (𝓞 L) L a := eq_of_smul_eq_smul_of_ne_zero hw0 hl
      have hdet : ‖(fderiv ℂ (chartAt 𝒩 τ U s p ∘ φ.symm) (φ p)).det‖ ^ 2 = 1 := by
        rw [show fderiv ℂ (chartAt 𝒩 τ U s p ∘ φ.symm) (φ p) = ContinuousLinearMap.id ℂ _ from
          ContinuousLinearMap.ext fun v => Subsingleton.elim _ _]
        simp [ContinuousLinearMap.det]
      rcases E.eq_empty_or_nonempty with rfl | hne
      · simp
      · rw [hne.eq_univ]
        have himg : φ '' Set.univ = Set.univ :=
          (Set.image_nonempty.mpr Set.univ_nonempty).eq_univ
        rw [himg, hdet, hla]
        simp [nu₀, c, volume_univ_fin_zero, hε.le]
    have huniq := (hr τ).2 nu₀ ⟨hfin, hdens⟩
    rw [← huniq]
    simp [nu₀, c]
  rw [hsec]
  simp_rw [hrτ]
  have hsum : ∑ τ : L →+* ℂ, Real.log (‖τ (algebraMap (𝓞 L) L a)‖ ^ 2) =
      2 * Real.log ((Algebra.norm ℤ a).natAbs : ℝ) := by
    rw [← sum_log_norm_embeddings_int a ha, Finset.mul_sum]
    refine Finset.sum_congr rfl fun τ _ => ?_
    rw [Real.log_pow]
    push_cast
    rfl
  rw [hsum]
  ring

/-- **The row at g = 0** (outside the print): the height of an abelian variety of dimension 0 is `≥ 0` (it is
`0`, `isAnStableHeightSS_eq_zero_of_dim_zero`). -/
theorem isAnStableHeightSS_nonneg_of_dim_zero {K : Type} [Field K] [NumberField K] (A : PkgI3.AbVar K)
    (hA : A.dim = (0 : ℕ)) (x : ℝ) (hx : ZInQ.SemistabAssembly.IsAnStableHeightSS A x) : 0 ≤ x :=
  (isAnStableHeightSS_eq_zero_of_dim_zero A hA x hx).ge

end DimZero

/-! ## The printed statement -/

/-- **Gaudron–Rémond, *Polarisations et isogénies*, Duke Math. J. 163 (2014), 2057–2108, p. 2101** (§9,
"Conclusion des démonstrations", proof of the main theorems; a report of Bost's lower bound):

* p. 2058 (setting and normalization): "Soient donc k un corps de nombres et A une variété abélienne sur k de
  dimension g ≥ 1. […] où h_F(A) est la hauteur de Faltings stable de A (avec la normalisation originale de
  Faltings, voir [GR1, paragraphe 2.3])."
* p. 2101: "en notant que h_F(A) ≥ −3g/2 (minoration de Bost)."
* p. 2098 (the same bound for the factors C_{i,j}) and p. 2102, proof of Cor. 1.5: "Par la minoration de Bost
  utilisée ci-dessus, h_{F,K}(B₁) ≥ h_F(B₁) ≥ −(3/2) dim B₁ ≥ −(3/2) g."

Lean form (the row `ZInQ.BostGR9.GaudronRemondSec9LowerAnSS` with the print's hypothesis g ≥ 1): for every number
field K, every abelian variety A over K of dimension g ≥ 1 (the print's setting, p. 2058), and every real x that is
the stable Faltings height of A in Faltings' original normalization, computed on a model with semistable reduction
as printed (`ZInQ.SemistabAssembly.IsAnStableHeightSS`), −(3/2) g ≤ x. Reading step: "stable" Faltings height read
as the height on a semistable model, as in the row. The row's case g = 0, which the print does not cover, is proved
(`isAnStableHeightSS_eq_zero_of_dim_zero`). Proof in the literature: Gaudron–Rémond, Comment. Math. Helv. 89
(2014), Cor. 8.4, p. 400 (h(A) ≥ −(1/2)(dim A) log(2π), attributed to Bost), with h_F(A) = h(A) − (g/2) log π
(p. 352), so h_F(A) ≥ −g log(π√2) ≥ −(3/2) g. -/
def GaudronRemondDuke163Bost : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (A : PkgI3.AbVar K) (g : ℕ), 1 ≤ g →
    A.dim = g → ∀ x : ℝ, ZInQ.SemistabAssembly.IsAnStableHeightSS A x → -(3 / 2) * (g : ℝ) ≤ x

/-- **The row from the print:** g = 0 by `isAnStableHeightSS_nonneg_of_dim_zero`, g ≥ 1 by the print. -/
theorem gaudronRemondSec9LowerAnSS_of_duke163 (h : GaudronRemondDuke163Bost) :
    ZInQ.BostGR9.GaudronRemondSec9LowerAnSS := by
  intro K _ _ A g hg x hx
  rcases Nat.eq_zero_or_pos g with rfl | hpos
  · simpa using isAnStableHeightSS_nonneg_of_dim_zero A hg x hx
  · exact h K A g hpos hg x hx

/-- The print from the row (the row has no hypothesis on g). -/
theorem duke163_of_gaudronRemondSec9LowerAnSS :
    ZInQ.BostGR9.GaudronRemondSec9LowerAnSS → GaudronRemondDuke163Bost :=
  fun h K _ _ A g _ hg x hx => h K A g hg x hx

/-- The printed statement is equivalent to the row. -/
theorem gaudronRemondDuke163Bost_iff :
    GaudronRemondDuke163Bost ↔ ZInQ.BostGR9.GaudronRemondSec9LowerAnSS :=
  ⟨gaudronRemondSec9LowerAnSS_of_duke163, duke163_of_gaudronRemondSec9LowerAnSS⟩

end ZInQ.GRDuke163
