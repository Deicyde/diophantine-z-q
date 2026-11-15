import ZInQKernel.Contrib.CloudW07JacobiansCurves.Jacobian.AlgebraicGeometry.ProjectiveSpace.FiniteSet
import ZInQKernel.Contrib.Dim.SmoothStalk
import ZInQKernel.Contrib.CloudW03NeronSurj.Vendor.Theorems.Thm_AlgebraicGeometry_Smooth_isDiscreteValuationRing_stalk_of_forall_specializes
import Mathlib.AlgebraicGeometry.Fiber
import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen
import ZInQKernel.Contrib.CloudW03NeronSurj.Vendor.Theorems.Thm_AlgebraicGeometry_Smooth_isRegularLocalRing_stalk_of_isDiscreteValuationRing

/-! p1-quot2: EGA II 4.5.4 (Liu Prop. 3.3.36 (b)) over an affine base: a finite set of points of a closed
subscheme of `ℙ(ι; Spec R)` lies in an affine open. The proof is the vendored field case
(`AlgebraicGeometry.exists_isAffineOpen_superset_of_isClosedImmersion`), which uses only that the base is
affine. -/

section AFsec
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

universe u

open CategoryTheory Limits AlgebraicGeometry

namespace P1Quot2

attribute [local instance] MvPolynomial.gradedAlgebra

theorem exists_isAffineOpen_superset_of_isClosedImmersion_spec
    {R : CommRingCat.{u}} {X : Scheme.{u}}
    {ι : Type u} (i : X ⟶ ℙ(ι; Spec R))
    [IsClosedImmersion i] (s : Set X) (hs : s.Finite) :
    ∃ W : X.Opens, IsAffineOpen W ∧ s ⊆ W := by
  classical
  let j := i ≫ ProjectiveSpace.toIntegralModel ι (Spec R)
  obtain ⟨d, hd, f, hf, havoid⟩ :=
    ProjectiveSpectrum.exists_homogeneous_notMem_of_finset
      (grading := MvPolynomial.homogeneousSubmodule ι (ULift.{u} ℤ))
      (hs.image j.base).toFinset
  have hA := Proj.isAffineOpen_basicOpen
    (MvPolynomial.homogeneousSubmodule ι (ULift.{u} ℤ)) f hf hd
  haveI : IsAffineHom (ProjectiveSpace.toIntegralModel ι (Spec R)) := by
    haveI : IsAffineHom (terminal.from (Spec R)) := isAffineHom_of_isAffine _
    exact MorphismProperty.pullback_snd (P := @IsAffineHom) _ _ inferInstance
  refine ⟨j ⁻¹ᵁ Proj.basicOpen _ f, hA.preimage j, fun x hx ↦ ?_⟩
  exact havoid (j.base x) (by simpa using ⟨x, hx, rfl⟩)

end P1Quot2
end
end AFsec

/-! p1-quot2: an integral scheme, proper and smooth of relative dimension 1 over a DVR, has dimension 2. -/

noncomputable section

open CategoryTheory Limits AlgebraicGeometry IsLocalRing Order

namespace P1Quot2

section DVR

variable (R : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]

/-- In `Spec R` (`R` a DVR) a point other than the closed point is the generic point `⊥`. -/
theorem asIdeal_eq_bot_of_ne_closedPoint (v : PrimeSpectrum R) (hv : v ≠ closedPoint R) :
    v.asIdeal = ⊥ := by
  by_contra h
  have hmax : v.asIdeal.IsMaximal := Ring.DimensionLEOne.maximalOfPrime h v.2
  apply hv
  exact PrimeSpectrum.ext (IsLocalRing.eq_maximalIdeal hmax)

/-- If `u ⤳ v` in `Spec R` and `v` is not the closed point, then `u = v`. -/
theorem eq_of_specializes_of_ne_closedPoint {u v : PrimeSpectrum R} (h : u ⤳ v)
    (hv : v ≠ closedPoint R) : u = v := by
  have h' : u.asIdeal ≤ v.asIdeal := (PrimeSpectrum.le_iff_specializes _ _).2 h
  have hb := asIdeal_eq_bot_of_ne_closedPoint R v hv
  have hu : u.asIdeal = ⊥ := le_bot_iff.1 (hb ▸ h')
  exact PrimeSpectrum.ext (hu.trans hb.symm)

/-- If `u ⤳ v` in `Spec R` and `u` is the closed point, then so is `v`. -/
theorem eq_closedPoint_of_specializes {u v : PrimeSpectrum R} (h : u ⤳ v)
    (hu : u = closedPoint R) : v = closedPoint R := by
  by_contra hv
  have := eq_of_specializes_of_ne_closedPoint R h hv
  exact hv (this ▸ hu)

end DVR

/-- An `LTSeries` of length `2`. -/
def lt3 {α : Type*} [Preorder α] {a b c : α} (h1 : a < b) (h2 : b < c) : LTSeries α where
  length := 2
  toFun := ![a, b, c]
  step := fun i => by
    fin_cases i
    · exact h1
    · exact h2

theorem lt3_length {α : Type*} [Preorder α] {a b c : α} (h1 : a < b) (h2 : b < c) :
    (lt3 h1 h2).length = 2 := rfl

theorem lt3_head {α : Type*} [Preorder α] {a b c : α} (h1 : a < b) (h2 : b < c) :
    (lt3 h1 h2).head = a := rfl

variable {R : Type} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
variable {X : Scheme.{0}} (f : X ⟶ Spec (CommRingCat.of R))

/-- The scheme dimension equals the Krull dimension of the specialization order. -/
theorem topologicalKrullDim_eq_krullDim (Y : Scheme.{0}) : topologicalKrullDim Y = Order.krullDim Y :=
  Order.krullDim_eq_of_orderIso (irreducibleSetEquivPoints (α := Y))

set_option backward.isDefEq.respectTransparency.types false in
/-- The fibre over `y` has dimension at most `1` (smooth of relative dimension `1` over `κ(y)`). -/
theorem topologicalKrullDim_fiber_le [SmoothOfRelativeDimension 1 f] (y : Spec (CommRingCat.of R)) :
    topologicalKrullDim (f.fiber y) ≤ 1 := by
  by_cases hne : Nonempty (f.fiber y)
  · haveI := hne
    have : SmoothOfRelativeDimension 1 (f.fiberToSpecResidueField y) := by
      haveI := smoothOfRelativeDimension_isStableUnderBaseChange 1
      exact MorphismProperty.IsStableUnderBaseChange.of_isPullback (P := @SmoothOfRelativeDimension 1)
        (IsPullback.of_hasPullback f _) inferInstance
    have := ZInQ.Contrib.Dim.topologicalKrullDim_eq_of_smoothOfRelativeDimension
      (K := (Spec (CommRingCat.of R)).residueField y) (f.fiberToSpecResidueField y) 1
    rw [this]; rfl
  · haveI : IsEmpty (f.fiber y) := not_nonempty_iff.1 hne
    rw [topologicalKrullDim_eq_krullDim, Order.krullDim_eq_bot]
    exact bot_le

/-- No strict chain of length `2` inside a fibre. -/
theorem not_chain_in_fiber [SmoothOfRelativeDimension 1 f] (y : Spec (CommRingCat.of R))
    {a b c : X} (ha : f a = y) (hb : f b = y) (hc : f c = y) (hab : a < b) (hbc : b < c) : False := by
  let e := f.fiberHomeo y
  let a' := e.symm ⟨a, ha⟩
  let b' := e.symm ⟨b, hb⟩
  let c' := e.symm ⟨c, hc⟩
  have hι : ∀ (u : X) (hu : f u = y), f.fiberι y (e.symm ⟨u, hu⟩) = u := fun u hu =>
    f.fiberι_fiberHomeo_symm y ⟨u, hu⟩
  have hemb := (f.fiberι y).isEmbedding
  have key : ∀ (u v : X) (hu : f u = y) (hv : f v = y), u < v →
      e.symm ⟨u, hu⟩ < e.symm ⟨v, hv⟩ := by
    intro u v hu hv huv
    rw [lt_iff_le_not_ge, Scheme.le_iff_specializes, Scheme.le_iff_specializes] at huv ⊢
    rw [← hemb.isInducing.specializes_iff, ← hemb.isInducing.specializes_iff, hι u hu, hι v hv]
    exact huv
  have h1 := key a b ha hb hab
  have h2 := key b c hb hc hbc
  have hlen := (lt3 h1 h2).length_le_krullDim
  rw [lt3_length, ← topologicalKrullDim_eq_krullDim] at hlen
  have h21 := hlen.trans (topologicalKrullDim_fiber_le f y)
  have : (2 : ℕ) ≤ 1 := by exact_mod_cast h21
  omega

/-- **Every point has coheight at most `2`.** -/
theorem coheight_le_two [SmoothOfRelativeDimension 1 f] (x : X) : coheight x ≤ 2 := by
  by_contra hlt
  push Not at hlt
  have h3 : ((3 : ℕ) : ℕ∞) ≤ coheight x := by
    calc ((3 : ℕ) : ℕ∞) = 2 + 1 := by norm_num
      _ ≤ coheight x := Order.add_one_le_of_lt hlt
  obtain ⟨p, -, hp⟩ := exists_series_of_le_coheight x h3
  have hc : StrictMono (Fin.cast (show 4 = p.length + 1 by omega)) := fun i j h => h
  let a : Fin 4 → X := fun i => p (Fin.cast (show 4 = p.length + 1 by omega) i)
  have ha : StrictMono a := p.strictMono.comp hc
  have h01 : a 0 < a 1 := ha (by decide)
  have h12 : a 1 < a 2 := ha (by decide)
  have h23 : a 2 < a 3 := ha (by decide)
  set s := closedPoint R
  -- specializations map to specializations
  have hsp : ∀ {u v : X}, u < v → f v ⤳ f u := fun {u v} h =>
    (Scheme.le_iff_specializes.1 h.le).map f.continuous
  by_cases h2s : f (a 2) = s
  · have h1s : f (a 1) = s := eq_closedPoint_of_specializes R (hsp h12) h2s
    have h0s : f (a 0) = s := eq_closedPoint_of_specializes R (hsp h01) h1s
    exact not_chain_in_fiber f s h0s h1s h2s h01 h12
  by_cases h1s : f (a 1) = s
  · -- `a 1` is a maximal point of the special fibre: its stalk is a DVR, of dimension `1`
    have h0s : f (a 0) = s := eq_closedPoint_of_specializes R (hsp h01) h1s
    have hgen : ∀ y : X, y ⤳ a 1 → f y = s → y = a 1 := by
      intro y hy hys
      by_contra hne
      have hlt : a 1 < y := by
        exact lt_of_le_not_ge (Scheme.le_iff_specializes.2 hy)
          (fun h => hne (hy.antisymm (Scheme.le_iff_specializes.1 h)).eq)
      exact not_chain_in_fiber f s h0s h1s hys h01 hlt
    haveI : Smooth f := SmoothOfRelativeDimension.smooth 1 f
    obtain ⟨hdom, hdvr⟩ := ZInQ.Contrib.CloudW03NeronSurj.FLT.AlgebraicGeometry.Smooth.isDiscreteValuationRing_stalk_of_forall_specializes
      R f (a 1) h1s hgen
    haveI := hdom
    haveI := hdvr
    have hd : coheight (a 1) = 1 := by
      have := IsDiscreteValuationRing.ringKrullDim_eq_one (X.presheaf.stalk (a 1))
      rw [ringKrullDim_stalk_eq_coheight] at this
      exact_mod_cast this
    have := length_le_coheight_head (p := lt3 h12 h23)
    rw [lt3_length, lt3_head, hd] at this
    have : (2 : ℕ) ≤ 1 := by exact_mod_cast this
    omega
  · have he2 : f (a 2) = f (a 1) := eq_of_specializes_of_ne_closedPoint R (hsp h12) h1s
    have h2s' : f (a 2) ≠ s := by rw [he2]; exact h1s
    have he3 : f (a 3) = f (a 1) :=
      (eq_of_specializes_of_ne_closedPoint R (hsp h23) h2s').trans he2
    exact not_chain_in_fiber f (f (a 1)) rfl he2 he3 h12 h23

set_option backward.isDefEq.respectTransparency.types false in
/-- **An integral scheme, proper and smooth of relative dimension `1` over a DVR, has dimension `2`.** -/
theorem topologicalKrullDim_eq_two [IsIntegral X] [IsProper f] [SmoothOfRelativeDimension 1 f] :
    topologicalKrullDim X = 2 := by
  rw [topologicalKrullDim_eq_krullDim]
  refine le_antisymm ?_ ?_
  · rw [Order.krullDim_eq_iSup_coheight]
    refine iSup_le fun x => ?_
    exact WithBot.coe_le_coe.mpr (coheight_le_two f x)
  · haveI : Smooth f := SmoothOfRelativeDimension.smooth 1 f
    set s := closedPoint R
    -- a point over the generic point of `Spec R`
    let ηR : Spec (CommRingCat.of R) := (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum R)
    have hηRsp : ∀ v : Spec (CommRingCat.of R), ηR ⤳ v := fun v =>
      (PrimeSpectrum.le_iff_specializes (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum R) v).1 bot_le
    have hηR : ηR ≠ s := by
      intro h
      have hm : (s : PrimeSpectrum R).asIdeal = maximalIdeal R := rfl
      apply IsDiscreteValuationRing.not_a_field R
      rw [← hm, ← h]
    obtain ⟨x0⟩ : Nonempty X := inferInstance
    obtain ⟨x', -, hx'⟩ := Flat.generalizingMap f (hηRsp (f x0))
    -- the generic point of `X` lies over `ηR`
    let ηX := genericPoint X
    have hfηX : f ηX = ηR := by
      have : f ηX ⤳ f x' := (genericPoint_specializes x').map f.continuous
      rw [hx'] at this
      exact eq_of_specializes_of_ne_closedPoint R this hηR
    -- the special fibre is nonempty
    have hs : s ∈ Set.range f := by
      have hcl : IsClosed (Set.range f) := f.isClosedMap.isClosed_range
      have hmem : ηR ∈ Set.range f := ⟨x', hx'⟩
      exact hcl.stableUnderSpecialization (hηRsp s) hmem
    obtain ⟨xs, hxs⟩ := hs
    haveI : Nonempty (f.fiber s) := ⟨(f.fiberHomeo s).symm ⟨xs, hxs⟩⟩
    have : SmoothOfRelativeDimension 1 (f.fiberToSpecResidueField s) := by
      haveI := smoothOfRelativeDimension_isStableUnderBaseChange 1
      exact MorphismProperty.IsStableUnderBaseChange.of_isPullback (P := @SmoothOfRelativeDimension 1)
        (IsPullback.of_hasPullback f _) inferInstance
    have hdF := ZInQ.Contrib.Dim.topologicalKrullDim_eq_of_smoothOfRelativeDimension
      (K := (Spec (CommRingCat.of R)).residueField s) (f.fiberToSpecResidueField s) 1
    rw [topologicalKrullDim_eq_krullDim] at hdF
    obtain ⟨b0, b1, hb⟩ := Order.krullDim_pos_iff.1 (by rw [hdF]; exact_mod_cast zero_lt_one)
    have hemb := (f.fiberι s).isEmbedding
    have hc : f.fiberι s b0 < f.fiberι s b1 := by
      rw [lt_iff_le_not_ge, Scheme.le_iff_specializes, Scheme.le_iff_specializes] at hb ⊢
      rwa [hemb.isInducing.specializes_iff, hemb.isInducing.specializes_iff]
    have hfs : ∀ b, f (f.fiberι s b) = s := fun b => by
      have h := (Scheme.Hom.range_fiberι f s).subset ⟨b, rfl⟩
      simpa using h
    have hc2 : f.fiberι s b1 < ηX := by
      refine lt_of_le_not_ge (Scheme.le_iff_specializes.2 (genericPoint_specializes _)) fun h => ?_
      have heq : ηX = f.fiberι s b1 :=
        ((genericPoint_specializes _).antisymm (Scheme.le_iff_specializes.1 h)).eq
      have := hfs b1
      rw [← heq, hfηX] at this
      exact hηR this
    have := (lt3 hc hc2).length_le_krullDim
    rw [lt3_length] at this
    exact_mod_cast this

end P1Quot2

/-! ## Lichtenbaum's theorem and finite sets in affine opens -/

namespace P1Quot2

open CategoryTheory Limits AlgebraicGeometry

/-- **Leaf: Lichtenbaum's projectivity theorem** (published; special case `S = Spec R`, `R` a DVR).
S. Lichtenbaum, *Curves over discrete valuation rings*, Amer. J. Math. 90 (1968), 380–405, Thm. 2.8; Q. Liu,
*Algebraic Geometry and Arithmetic Curves* (Oxford, 2002), Thm. 8.3.16 (locators UNVERIFIED, no network):
let `S` be a Dedekind scheme of dimension 1 and `X → S` a proper flat morphism with `X` integral, regular, of
dimension 2; then `X → S` is projective. "Projective" is Liu's Def. 5.3.? / EGA II 5.5.2 in the form of a
closed immersion into `ℙⁿ_S` over `S` (vendored Jacobian-Challenge `ℙ(Fin (n+1); S)`, the base change of
`Proj ℤ[X₀,…,Xₙ]`); "regular" is Mathlib's `IsRegularLocalRing` at every stalk; "dimension" is the Krull
dimension of the underlying space. -/
def LichtenbaumProjective : Prop :=
  ∀ (R : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] (X : Scheme.{0})
    (f : X ⟶ Spec (CommRingCat.of R)), IsIntegral X → IsProper f → Flat f →
    (∀ x : X, IsRegularLocalRing (X.presheaf.stalk x)) → topologicalKrullDim X = 2 →
    ∃ (n : ℕ) (i : X ⟶ ℙ(Fin (n + 1); Spec (CommRingCat.of R))),
      IsClosedImmersion i ∧ i ≫ ℙ(Fin (n + 1); Spec (CommRingCat.of R)) ↘ Spec (CommRingCat.of R) = f

/-- **Finite sets of points of an integral proper smooth relative curve over a DVR lie in an affine open**,
from Lichtenbaum's theorem: `X` is flat, regular (vendored FLT, smooth over a DVR), of dimension 2
(`topologicalKrullDim_eq_two`), so projective; then EGA II 4.5.4 (`exists_isAffineOpen_superset_of_isClosedImmersion_spec`). -/
theorem exists_affine_of_lichtenbaum (hL : LichtenbaumProjective) {R : Type} [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] {X : Scheme.{0}} (f : X ⟶ Spec (CommRingCat.of R)) [IsIntegral X]
    [IsProper f] [SmoothOfRelativeDimension 1 f] (s : Finset X) :
    ∃ W : X.Opens, IsAffineOpen W ∧ ∀ x ∈ s, x ∈ W := by
  haveI : Smooth f := SmoothOfRelativeDimension.smooth 1 f
  obtain ⟨n, i, hi, -⟩ := hL R X f inferInstance inferInstance inferInstance
    (fun x => ZInQ.Contrib.CloudW03NeronSurj.FLT.AlgebraicGeometry.Smooth.isRegularLocalRing_stalk_of_isDiscreteValuationRing
      R f x) (topologicalKrullDim_eq_two f)
  haveI := hi
  obtain ⟨W, hW, hsW⟩ := exists_isAffineOpen_superset_of_isClosedImmersion_spec i (s : Set X) s.finite_toSet
  exact ⟨W, hW, fun x hx => hsW hx⟩

end P1Quot2

#print axioms P1Quot2.topologicalKrullDim_eq_two
#print axioms P1Quot2.exists_affine_of_lichtenbaum
#print axioms P1Quot2.exists_isAffineOpen_superset_of_isClosedImmersion_spec
