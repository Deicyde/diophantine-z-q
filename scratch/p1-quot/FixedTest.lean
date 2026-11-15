import ZInQKernel.Contrib.OneProof.QuotientP1.MCRQuotB
import ZInQKernel.Contrib.CloudW03NeronSurj.Vendor.Theorems.Thm_AlgebraicGeometry_Smooth_isDomain_and_isIntegrallyClosed_stalk_of_isDiscreteValuationRing

namespace HDec

set_option maxHeartbeats 1000000
set_option linter.ambiguousOpen false

noncomputable section

namespace MCRQuot

open Polynomial CategoryTheory AlgebraicGeometry Limits LeafQM LeafQM.AV VertWitness HeckeRestNV
open G0ModField PropTSRed PropTSGlue ModelGlue MCRGlue LeafQM.AV.Pin PkgI3

/-- **LEAF (Edixhoven's tame fixed-point theorem, cyclic case over `ℤ_(p)`).** B. Edixhoven, *Néron models and
tame ramification*, Compositio Math. 81 (1992), 291-306, Prop. 3.4 (locator UNVERIFIED): for a smooth `S`-scheme
`X` and a finite group `G` of `S`-automorphisms of order invertible on `S`, the fixed-point scheme `X^G` is smooth
over `S`. Here `S = Spec ℤ_(p)` and `G = ⟨σ⟩` with `σ^n = 1`, `p ∤ n`; `X^G` represents `T ↦ X(T)^G`, which for a
cyclic group is the equalizer of `σ` and the identity in schemes over `S`. -/
def EdixhovenFixedSmooth : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (𝒴 : Over (Spec (CommRingCat.of (Zloc p)))), Smooth 𝒴.hom →
    ∀ (σ : Aut 𝒴.left) (n : ℕ) (hσ : σ.asIso.hom ≫ 𝒴.hom = 𝒴.hom), 0 < n → ¬ p ∣ n → σ ^ n = 1 →
      Smooth (equalizer (Over.homMk σ.asIso.hom hσ : 𝒴 ⟶ 𝒴) (𝟙 𝒴)).hom

/-- Two generizations of a point with a domain stalk have a common generization. -/
theorem exists_common_generization {X : Scheme.{0}} (z : X) [IsDomain (X.presheaf.stalk z)]
    {a b : X} (ha : a ⤳ z) (hb : b ⤳ z) : ∃ ξ : X, ξ ⤳ a ∧ ξ ⤳ b := by
  have hra : a ∈ Set.range (X.fromSpecStalk z) := by rw [Scheme.range_fromSpecStalk]; exact ha
  have hrb : b ∈ Set.range (X.fromSpecStalk z) := by rw [Scheme.range_fromSpecStalk]; exact hb
  obtain ⟨a', rfl⟩ := hra
  obtain ⟨b', rfl⟩ := hrb
  let g : Spec (X.presheaf.stalk z) := genericPoint _
  refine ⟨X.fromSpecStalk z g, ?_, ?_⟩
  · exact ((genericPoint_spec (Spec (X.presheaf.stalk z))).specializes trivial).map
      (X.fromSpecStalk z).continuous
  · exact ((genericPoint_spec (Spec (X.presheaf.stalk z))).specializes trivial).map
      (X.fromSpecStalk z).continuous

/-- **A proper generization of the point of a `ℚ̄`-point has infinitely many `ℚ̄`-points in its closure** (for
`𝒴` locally of finite type over `ℤ_(p)`): the generization lies in the open generic fibre, which is a Jacobson
space; a closed set there with finitely many closed points is a finite set of closed points, and every closed
point carries a `ℚ̄`-point (`exists_qbarPt`). -/
theorem infinite_qbar_closure {p : ℕ} [Fact p.Prime] (𝒴 : Over (Spec (CommRingCat.of (Zloc p))))
    [LocallyOfFiniteType 𝒴.hom] (y : Spec (CommRingCat.of Qbar) ⟶ 𝒴.left) (w : 𝒴.left)
    (hw : w ⤳ qbarPoint y) (hne : w ≠ qbarPoint y) :
    {t : Spec (CommRingCat.of Qbar) ⟶ 𝒴.left | qbarPoint t ∈ closure {w}}.Infinite := by
  set G := genFib 𝒴 with hG
  set j : G.left ⟶ 𝒴.left := pullback.fst 𝒴.hom (specRatToZloc p) with hj
  haveI : IsOpenImmersion j :=
    MorphismProperty.pullback_fst (P := @IsOpenImmersion) _ _ (isOpenImmersion_specRatToZloc p)
  haveI : LocallyOfFiniteType G.hom := by
    show LocallyOfFiniteType (pullback.snd 𝒴.hom (specRatToZloc p)); infer_instance
  haveI : JacobsonSpace G.left := LocallyOfFiniteType.jacobsonSpace G.hom
  obtain ⟨s, hs⟩ := genFib_pt 𝒴 y
  have hsv : j (ptOf s.left) = qbarPoint y := by
    rw [← hs]; rfl
  have hwr : w ∈ Set.range j :=
    hw.mem_open j.isOpenEmbedding.isOpen_range ⟨_, hsv⟩
  obtain ⟨w', rfl⟩ := hwr
  have hw' : w' ⤳ ptOf s.left := by
    rw [← j.isOpenEmbedding.isInducing.specializes_iff, hsv]; exact hw
  have hne' : w' ≠ ptOf s.left := by
    intro h; apply hne; rw [h, hsv]
  -- infinitely many closed points in the closure of `w'`
  have hinf : (closure {w'} ∩ closedPoints G.left).Infinite := by
    intro hfin
    have hcl : IsClosed (closure {w'} ∩ closedPoints G.left) := by
      have : closure {w'} ∩ closedPoints G.left =
          ⋃ c ∈ hfin.toFinset, ({c} : Set G.left) := by
        ext c; simp
      rw [this]
      exact isClosed_biUnion_finset (fun c hc => (hfin.mem_toFinset.mp hc).2)
    have heq := JacobsonSpace.closure_inter_closedPoints_eq_closure
      (S := closure {w'}) isClosed_closure.isLocallyClosed
    rw [hcl.closure_eq, closure_closure] at heq
    have hwc : w' ∈ closure {w'} ∩ closedPoints G.left := by
      rw [heq]; exact subset_closure rfl
    have hwcl : IsClosed ({w'} : Set G.left) := hwc.2
    have : ptOf s.left ∈ ({w'} : Set G.left) := by
      rw [← hwcl.closure_eq]; exact specializes_iff_mem_closure.mp hw'
    exact hne' this.symm
  -- each closed point gives a `ℚ̄`-point of `𝒴`
  have hpt : ∀ c ∈ closure {w'} ∩ closedPoints G.left,
      ∃ t : Spec (CommRingCat.of Qbar) ⟶ 𝒴.left, qbarPoint t = j c := by
    intro c hc
    obtain ⟨emb, y0, hy0⟩ := exists_qbarPt G c hc.2
    refine ⟨y0.left ≫ j, ?_⟩
    change j (qbarPoint y0.left) = j c
    congr 1
    unfold qbarPoint
    rw [hy0, Equiv.apply_symm_apply]
  haveI : Nonempty (Spec (CommRingCat.of Qbar) ⟶ 𝒴.left) := ⟨y⟩
  choose! T hT using hpt
  have hinj : Set.InjOn T (closure {w'} ∩ closedPoints G.left) := by
    intro c hc c' hc' e
    have := (hT c hc).symm.trans ((congrArg qbarPoint e).trans (hT c' hc'))
    exact j.isOpenEmbedding.injective this
  refine Set.Infinite.mono ?_ (hinf.image hinj)
  rintro _ ⟨c, hc, rfl⟩
  show qbarPoint (T c) ∈ closure {j w'}
  rw [hT c hc]
  have := image_closure_subset_closure_image (f := j) j.continuous ⟨c, hc.1, rfl⟩
  simpa [Set.image_singleton] using this

/-- `ℤ_(p)` is a discrete valuation ring. -/
theorem zloc_isDVR (p : ℕ) [Fact p.Prime] : IsDiscreteValuationRing (Zloc p) :=
  IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain ℤ
    (by
      show Ideal.span {((p : ℕ) : ℤ)} ≠ ⊥
      rw [ne_eq, Ideal.span_singleton_eq_bot]
      exact_mod_cast (Fact.out : p.Prime).ne_zero) _

/-- **L5 `TameFixedPointsDisjoint` from Edixhoven's theorem.** The fixed scheme `F` of `σ` is a closed subscheme
(equalizer in `Over S`, `𝒴` separated) and smooth over `ℤ_(p)` (Edixhoven), so its stalks are domains
(`Smooth.isDomain_and_isIntegrallyClosed_stalk_of_isDiscreteValuationRing`). A common point of the closures of the
two fixed points would have a common generization `ξ` of both in `F`; `ξ`, or one of the two points, is then a
proper generization of the point of a `ℚ̄`-point, whose closure (inside the closed `F`) carries infinitely many
`ℚ̄`-points (`infinite_qbar_closure`), all fixed by `σ`. -/
theorem tameFixedPointsDisjoint_of_edixhoven (hE : EdixhovenFixedSmooth) : TameFixedPointsDisjoint := by
  intro p _ 𝒴 hP hS σ n hσ hn hpn hσn hfin y y' hy hy' hne
  haveI := hP
  haveI : Smooth 𝒴.hom := SmoothOfRelativeDimension.smooth 1 𝒴.hom
  haveI : IsDiscreteValuationRing (Zloc p) := zloc_isDVR p
  let f : 𝒴 ⟶ 𝒴 := Over.homMk σ.asIso.hom hσ
  let ι := (equalizer.ι f (𝟙 𝒴)).left
  have hι : ι ≫ σ.asIso.hom = ι := by
    have := congrArg CommaMorphism.left (equalizer.condition f (𝟙 𝒴))
    simpa [f, ι] using this
  have hcl : IsClosed (Set.range ι) := ι.isClosedEmbedding.isClosed_range
  have hfixr : ∀ t : Spec (CommRingCat.of Qbar) ⟶ 𝒴.left, t ≫ σ.asIso.hom = t →
      qbarPoint t ∈ Set.range ι := by
    intro t ht
    let t' : Over.mk (t ≫ 𝒴.hom) ⟶ 𝒴 := Over.homMk t rfl
    have hc : t' ≫ f = t' ≫ 𝟙 𝒴 := by
      ext1; simpa [f, t'] using ht
    refine ⟨(equalizer.lift t' hc).left (IsLocalRing.closedPoint Qbar), ?_⟩
    show ((equalizer.lift t' hc).left ≫ (equalizer.ι f (𝟙 𝒴)).left) _ = _
    rw [← Over.comp_left, equalizer.lift_ι]
    rfl
  -- a point of the range whose closure has infinitely many `ℚ̄`-points contradicts finiteness
  have hbad : ∀ w ∈ Set.range ι,
      ¬ {t : Spec (CommRingCat.of Qbar) ⟶ 𝒴.left | qbarPoint t ∈ closure {w}}.Infinite := by
    intro w hw hinf
    apply hinf
    refine hfin.subset ?_
    intro t ht
    have htr : ptOf t ∈ Set.range ι :=
      closure_minimal (Set.singleton_subset_iff.2 hw) hcl ht
    obtain ⟨t', rfl⟩ := exists_factor_of_mem_range_closedImm ι t htr
    show (t' ≫ ι) ≫ σ.asIso.hom = t' ≫ ι
    rw [Category.assoc, hι]
  haveI : Smooth (equalizer f (𝟙 𝒴)).hom := hE p 𝒴 inferInstance σ n hσ hn hpn hσn
  rw [Set.disjoint_left]
  intro z hz hz'
  obtain ⟨xt, hxt⟩ := hfixr y hy
  obtain ⟨xt', hxt'⟩ := hfixr y' hy'
  have hzr : z ∈ Set.range ι :=
    closure_minimal (Set.singleton_subset_iff.2 (show qbarPoint y ∈ Set.range ι from ⟨xt, hxt⟩)) hcl hz
  obtain ⟨zt, rfl⟩ := hzr
  have hind := ι.isClosedEmbedding.isInducing
  have h1 : xt ⤳ zt := by
    rw [← hind.specializes_iff, hxt]; exact specializes_iff_mem_closure.mpr hz
  have h2 : xt' ⤳ zt := by
    rw [← hind.specializes_iff, hxt']; exact specializes_iff_mem_closure.mpr hz'
  haveI : IsDomain ((equalizer f (𝟙 𝒴)).left.presheaf.stalk zt) :=
    (_root_.ZInQ.Contrib.CloudW03NeronSurj.FLT.AlgebraicGeometry.Smooth.isDomain_and_isIntegrallyClosed_stalk_of_isDiscreteValuationRing
      (Zloc p) (equalizer f (𝟙 𝒴)).hom zt).1
  obtain ⟨ξ, hξ1, hξ2⟩ := exists_common_generization zt h1 h2
  have k1 : ι ξ ⤳ qbarPoint y := by rw [← hxt]; exact hξ1.map ι.continuous
  have k2 : ι ξ ⤳ qbarPoint y' := by rw [← hxt']; exact hξ2.map ι.continuous
  by_cases hξx : ι ξ = qbarPoint y
  · rw [hξx] at k2
    exact hbad _ ⟨xt, hxt⟩ (infinite_qbar_closure 𝒴 y' _ k2 hne)
  · exact hbad _ ⟨ξ, rfl⟩ (infinite_qbar_closure 𝒴 y _ k1 hξx)

end MCRQuot

end

#print axioms HDec.MCRQuot.tameFixedPointsDisjoint_of_edixhoven
