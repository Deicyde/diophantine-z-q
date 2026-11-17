import ZInQKernel.Contrib.OneProof.HeckePin
import ZInQKernel.Contrib.CloudW07JacobiansCurves.Jacobian.AlgebraicGeometry.Curve.Dimension

/-!
# hecke-glue: the inputs `X1TauPoints` and `ConstOnTauPoints` of the Hecke dictionary are proved

Task hecke-glue (2026-11-17). Report: `docs/research/hecke-glue.md`.

`ZInQKernel/Contrib/OneProof/HeckePin.lean` (hecke-pin) reduced the dictionary gap of the r16 rows
`HeckeJ1DS`, `AfShimura` and `AfCharpolyDS965` to three named Props: `X1TauPoints` (leaf candidate),
`AbelJacobiX1` (leaf candidate) and `ConstOnTauPoints` (glue). This file proves two of them outright,
from Mathlib, the vendored CloudW07 curve library and the tree's `WeberField` analysis:

* `tauPlace : TauPlace`: for every `τ ∈ ℍ` the functions `a = P(j_X, t_X)/Q(j_X, t_X) ∈ K(X)` whose
  meromorphic function `P(j, f₁)/Q(j, f₁)` has a finite limit at `τ` form a valuation subring `O` of
  `K(X)`, and the limit `O → ℂ` is a local ring homomorphism (Mathlib's `meromorphicOrderAt`; the
  relations of `IsX1Gen` with the identity theorem make it well defined).
* `exists_cpt_of_place`: a valuation subring of `K(X)` with a local homomorphism to `ℂ` has a center:
  a complex point `x` of the curve `X` at which every `a ∈ O` is regular with the given value
  (valuative criterion of properness; local rings of a smooth curve are valuation rings, CloudW07).
* `x1TauPoints : X1TauPoints` (so `X1TauPoints` is glue, not a leaf).
* `constOnTauPoints_of_x1TauPoints` and `constOnTauPoints : ConstOnTauPoints`: the argument runs over
  `ℚ` (no base change): `x_ρ` lies over a closed point (`j_X(x_ρ) = j(ρ) = 0`, `j_X ≠ 0`); the fibre of
  `g` through it is closed and contains every `x_τ`; a closed set of the curve not containing the
  generic point is finite, and finitely many closed points carry finitely many complex points, while
  `j` takes infinitely many values on `ℍ`; so the generic point maps to the closed point `g(P₀) = 0`,
  whose residue field is `ℚ`, and `g = 0` (Mathlib's `ext_of_fromSpecResidueField_eq`).
* `isHeckeT_unique'`, `isDiamond_unique'`: hecke-pin's pinning of `T_p` and `⟨d⟩`, with no hypothesis.
* `evF_eq_zero_of_heckeJ_eq_zero_of_abelJacobi`, `killsIf_iff_IfDS_of_abelJacobi`: hecke-pin's gap 1,
  with `AbelJacobiX1` as the only remaining input.

No `sorry`; every theorem uses only `propext`, `Classical.choice`, `Quot.sound`.
-/

noncomputable section

namespace AfTateLam.HeckeGlue

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open LeafModCurves PkgI3 PkgI3.AbVar
open AfTateLam.HeckePin

/-! ## 1. The `j`-function on `ℍ` -/

/-- `j(τ)` (`= jL(pp τ)`). -/
def jfun (τ : UpperHalfPlane) : ℂ := X1Igusa.Weber.Jf (τ : ℂ)

theorem continuous_jfun : Continuous jfun :=
  X1Igusa.Weber.diffOn_Jf.continuousOn.comp_continuous UpperHalfPlane.continuous_coe
    fun τ => τ.coe_im_pos

theorem jfun_I : jfun UpperHalfPlane.I = 1728 := X1Igusa.Weber.Jf_I

theorem jfun_ρ : jfun X1Igusa.Weber.τρ = 0 := X1Igusa.Weber.Jf_ρ

open Polynomial in
theorem evAn_CX (N : ℕ) (τ : UpperHalfPlane) :
    X1Igusa.Weber.evAn N (AfTateOr.toQ (C X)) τ = jfun τ := by
  simp [X1Igusa.Weber.evAn, AfTateOr.toQ, jfun, X1Igusa.Weber.Jf]

theorem evAn_one (N : ℕ) (τ : UpperHalfPlane) :
    X1Igusa.Weber.evAn N (AfTateOr.toQ 1) τ = 1 := by
  simp [X1Igusa.Weber.evAn, AfTateOr.toQ]

open Polynomial in
theorem ev2_CX {K : Type*} [CommRing K] (a b : K) : AfTateOr.ev2 (C X) a b = a := by
  simp [AfTateOr.ev2]

theorem ev2_one {K : Type*} [CommRing K] (a b : K) : AfTateOr.ev2 1 a b = 1 := by
  simp [AfTateOr.ev2]

variable {N : ℕ} {X : Over SpecQ} [IsIntegral X.left]

/-- `j_X` is regular at `x_τ` with value `j(τ)`. -/
theorem regAt_jX {jX tX : X.left.functionField} {x : CPt X} {τ : UpperHalfPlane}
    (h : AtTau N jX tX x τ) : RegAt x jX (jfun τ) := by
  have := h (Polynomial.C Polynomial.X) 1 (jfun τ) (by rw [ev2_one]; exact one_ne_zero) (by
    simp only [evAn_CX, evAn_one, div_one]
    exact (continuous_jfun.tendsto τ).mono_left nhdsWithin_le_nhds)
  rwa [ev2_CX, ev2_one, div_one] at this

open Polynomial in
/-- `j_X ≠ 0` in `K(X)`. -/
theorem jX_ne_zero {jX tX : X.left.functionField} (hG : IsX1Gen N X jX tX) : jX ≠ 0 := by
  intro h0
  have := (hG.2 (Polynomial.C Polynomial.X)).1 (by rw [ev2_CX]; exact h0)
  obtain ⟨z, hz, h2, h3⟩ := X1Igusa.Weber.exists_good_point
  have h := this (UpperHalfPlane.ofComplex z) h2 h3
  rw [evAn_CX] at h
  have hJ : X1Igusa.Weber.Jf z ≠ 0 := by
    rw [X1Igusa.Weber.Jf_eq]
    exact div_ne_zero (mul_ne_zero (by norm_num) (pow_ne_zero _ h2)) (X1Igusa.Weber.Dlf_ne z)
  apply hJ
  simpa [jfun, X1Igusa.Weber.Jf, X1Igusa.Weber.ofComplex_coe hz] using h


/-! ## 2. Regular functions at complex points -/

/-- The point of `X` under a complex point. -/
abbrev cpt (x : CPt X) : X.left := x.left (IsLocalRing.closedPoint ℂ)

/-- The value of a rational function at a complex point is unique. -/
theorem regAt_unique {x : CPt X} {a : X.left.functionField} {c c' : ℂ}
    (h : RegAt x a c) (h' : RegAt x a c') : c = c' := by
  obtain ⟨U, hU, s, hle, hs, rfl⟩ := h
  obtain ⟨U', hU', s', hle', hs', rfl⟩ := h'
  have hle'' : ⊤ ≤ x.left ⁻¹ᵁ (U ⊓ U') := fun p hp => ⟨hle hp, hle' hp⟩
  have hne : Nonempty (U ⊓ U' : X.left.Opens) :=
    ⟨⟨cpt x, hle'' (Set.mem_univ (IsLocalRing.closedPoint ℂ))⟩⟩
  have e1 : X.left.presheaf.map (homOfLE (inf_le_left : U ⊓ U' ≤ U)).op s =
      X.left.presheaf.map (homOfLE (inf_le_right : U ⊓ U' ≤ U')).op s' := by
    apply X.left.germToFunctionField_injective (U ⊓ U')
    simp only [Scheme.germToFunctionField, TopCat.Presheaf.germ_res_apply]
    exact hs.trans hs'.symm
  have a1 := congrArg (fun φ => φ.hom s)
    (Scheme.Hom.map_appLE x.left hle'' (homOfLE (inf_le_left : U ⊓ U' ≤ U)).op)
  have a2 := congrArg (fun φ => φ.hom s')
    (Scheme.Hom.map_appLE x.left hle'' (homOfLE (inf_le_right : U ⊓ U' ≤ U')).op)
  simp only [CommRingCat.comp_apply] at a1 a2
  rw [← a1, ← a2, e1]

theorem value_ne_zero_aux {Y : Scheme} (f : Spec (CommRingCat.of ℂ) ⟶ Y) {U : Y.Opens}
    (s : Γ(Y, U)) (hle : ⊤ ≤ f ⁻¹ᵁ U) (h : f (IsLocalRing.closedPoint ℂ) ∈ Y.basicOpen s) :
    (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom (f.appLE U ⊤ hle s) ≠ 0 := by
  intro h0
  have h1 : f.appLE U ⊤ hle s = 0 := by
    have := congrArg (Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv.hom h0
    rwa [map_zero, ← CommRingCat.comp_apply, Iso.hom_inv_id, CommRingCat.id_apply] at this
  have h2 := Scheme.basicOpen_appLE f ⊤ U hle s
  rw [h1, Scheme.basicOpen_zero] at h2
  have h3 : IsLocalRing.closedPoint ℂ ∈ (⊥ : (Spec (CommRingCat.of ℂ)).Opens) := by
    rw [h2]; exact ⟨trivial, h⟩
  exact h3

/-- At the generic point a nonzero rational function has a nonzero value. -/
theorem regAt_ne_zero_of_generic {x : CPt X} {a : X.left.functionField} {c : ℂ}
    (h : RegAt x a c) (ha : a ≠ 0) (hx : cpt x = genericPoint X.left) : c ≠ 0 := by
  obtain ⟨U, hU, s, hle, hs, rfl⟩ := h
  have hη : genericPoint X.left ∈ X.left.basicOpen s := by
    rw [X.left.mem_basicOpen'']
    refine ⟨((genericPoint_spec X.left).mem_open_set_iff U.isOpen).mpr (by simpa using hU), ?_⟩
    have : X.left.germToFunctionField U s = a := hs
    rw [isUnit_iff_ne_zero]
    exact this ▸ ha
  rw [← hx] at hη
  exact value_ne_zero_aux x.left s hle hη

/-! ## 3. Finitely many complex points over finitely many closed points -/

/-- A closed point of a `ℚ`-scheme of finite type has finitely many embeddings `κ(p) → ℂ`. -/
theorem finite_residueField_hom [LocallyOfFiniteType X.hom] (p : X.left) (hp : IsClosed {p}) :
    Finite (X.left.residueField p ⟶ CommRingCat.of ℂ) := by
  have : JacobsonSpace X.left := LocallyOfFiniteType.jacobsonSpace X.hom
  have h1 : LocallyOfFiniteType (X.left.fromSpecResidueField p) :=
    isClosed_singleton_iff_locallyOfFiniteType.mp hp
  have h2 : LocallyOfFiniteType (X.left.fromSpecResidueField p ≫ X.hom) := inferInstance
  obtain ⟨φ, hφ⟩ := Spec.map_surjective (X.left.fromSpecResidueField p ≫ X.hom)
  rw [← hφ, HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)] at h2
  let := φ.hom.toAlgebra
  have : Algebra.FiniteType ℚ (X.left.residueField p) := h2
  have : Module.Finite ℚ (X.left.residueField p) := finite_of_finite_type_of_isJacobsonRing ℚ _
  refine Finite.of_injective (β := X.left.residueField p →ₐ[ℚ] ℂ)
    (fun f => { f.hom with commutes' := fun r => ?_ }) ?_
  · change (f.hom.comp φ.hom) r = algebraMap ℚ ℂ r
    rw [RingHom.ext_rat (f.hom.comp φ.hom) (algebraMap ℚ ℂ)]
  · intro f g h
    ext a
    exact congrArg (fun u : X.left.residueField p →ₐ[ℚ] ℂ => u a) h

/-- Finitely many complex points lie over a finite set of closed points. -/
theorem finite_cpts [LocallyOfFiniteType X.hom] {F : Set X.left} (hF : F.Finite)
    (hcl : ∀ p ∈ F, IsClosed {p}) : {y : CPt X | cpt y ∈ F}.Finite := by
  let e := Scheme.SpecToEquivOfField ℂ X.left
  have hinj : Function.Injective (fun y : CPt X => e y.left) := fun y y' h =>
    Over.OverMorphism.ext (e.injective h)
  have hS : {σ : Σ p, X.left.residueField p ⟶ CommRingCat.of ℂ | σ.1 ∈ F}.Finite := by
    have : {σ : Σ p, X.left.residueField p ⟶ CommRingCat.of ℂ | σ.1 ∈ F} =
        ⋃ p ∈ F, Set.range (Sigma.mk p) := by
      ext ⟨p, f⟩; simp
    rw [this]
    exact hF.biUnion fun p hp => by
      have := finite_residueField_hom p (hcl p hp); exact Set.finite_range _
  exact (hS.preimage hinj.injOn).subset fun y hy => hy

/-! ## 4. Ring homomorphisms out of a field with a map to `ℚ` -/

theorem ringHom_ext_of_toRat {k K : Type*} [Field k] [Field K] (ψ : k →+* ℚ)
    (f₁ f₂ : k →+* K) : f₁ = f₂ := by
  have : CharZero k := RingHom.charZero ψ
  have key : ∀ a, (Rat.castHom k) (ψ a) = a := fun a => ψ.injective (by
    have := RingHom.ext_rat (ψ.comp (Rat.castHom k)) (RingHom.id ℚ)
    exact congrArg (fun u : ℚ →+* ℚ => u (ψ a)) this)
  ext a
  rw [← key a]
  exact congrArg (fun u : ℚ →+* K => u (ψ a))
    (RingHom.ext_rat (f₁.comp (Rat.castHom k)) (f₂.comp (Rat.castHom k)))


/-! ## 5. `ConstOnTauPoints` from `X1TauPoints` -/

/-- **`ConstOnTauPoints` holds, given `X1TauPoints`.** -/
theorem constOnTauPoints_of_x1TauPoints (hP : X1TauPoints) : ConstOnTauPoints := by
  classical
  intro N hN X _ jX tX hC hG P₀ J g hP₀ hc
  choose x hx using hP N hN X jX tX hC hG
  have : IsProper X.hom := hC.proper
  have : SmoothOfRelativeDimension 1 X.hom := hC.smooth
  have : IsLocallyNoetherian X.left := LocallyOfFiniteType.isLocallyNoetherian X.hom
  have : CompactSpace X.left := QuasiCompact.compactSpace_of_compactSpace X.hom
  have : IsNoetherian X.left := {}
  have hdim : topologicalKrullDim X.left ≤ 1 := by
    exact_mod_cast topologicalKrullDim_le_of_smoothOfRelativeDimension X.hom 1
  -- `x_ρ` lies over a closed point
  have hρ : IsClosed {cpt (x X1Igusa.Weber.τρ)} := by
    by_contra hnc
    exact regAt_ne_zero_of_generic (regAt_jX (hx _)) (jX_ne_zero hG)
      (Scheme.eq_genericPoint_of_not_isClosed hdim hnc) jfun_ρ
  have : JacobsonSpace J.X.left := LocallyOfFiniteType.jacobsonSpace J.X.hom
  have : LocallyOfFiniteType g.left := by
    have : LocallyOfFiniteType (g.left ≫ J.X.hom) := by rw [Over.w g]; infer_instance
    exact locallyOfFiniteType_of_comp g.left J.X.hom
  set q := g.left (cpt (x X1Igusa.Weber.τρ)) with hqdef
  have hq : IsClosed {q} := g.left.closedPoints_subset_preimage_closedPoints hρ
  have hpq : ∀ τ, g.left (cpt (x τ)) = q := fun τ => by
    have h := hc τ X1Igusa.Weber.τρ (x τ) (x X1Igusa.Weber.τρ) (hx τ) (hx _)
    have := congrArg (fun h : ptObj (K := ℚ) ℂ ⟶ J.X => h.left (IsLocalRing.closedPoint ℂ)) h
    exact this
  -- the generic point maps to `q`
  have hη : g.left (genericPoint X.left) = q := by
    by_contra hne
    have hopen : IsOpen (g.left ⁻¹' {q})ᶜ := (hq.preimage g.left.continuous).isOpen_compl
    have hF := IsOpen.finite_compl_of_topologicalKrullDim_le_one hdim hopen
      ⟨genericPoint X.left, hne⟩
    rw [compl_compl] at hF
    have hcl : ∀ r ∈ g.left ⁻¹' {q}, IsClosed ({r} : Set X.left) := fun r hr => by
      by_contra h
      exact hne (Scheme.eq_genericPoint_of_not_isClosed hdim h ▸ hr)
    have hS := finite_cpts hF hcl
    let val : CPt X → ℂ := fun y => if h : ∃ c, RegAt y jX c then h.choose else 0
    have hval : ∀ τ, jfun τ = val (x τ) := fun τ => by
      have h1 := regAt_jX (hx τ)
      have h2 : ∃ c, RegAt (x τ) jX c := ⟨_, h1⟩
      simp only [val, dite_eq_left h2]
      exact regAt_unique h1 h2.choose_spec
    have hrange : (Set.range jfun).Countable := by
      refine ((hS.image val).subset ?_).countable
      rintro _ ⟨τ, rfl⟩
      exact ⟨x τ, hpq τ, (hval τ).symm⟩
    have := const_of_countable continuous_jfun hrange UpperHalfPlane.I X1Igusa.Weber.τρ
    rw [jfun_I, jfun_ρ] at this
    norm_num at this
  -- the identity point is `q`
  have hηJ : ∀ a : SpecQ, (η[J.X] : 𝟙_ (Over SpecQ) ⟶ J.X).left a = q := by
    intro a
    have h1 : (P₀ ≫ g).left a = (η[J.X] : 𝟙_ (Over SpecQ) ⟶ J.X).left a := by
      rw [hP₀, Hom.one_def, toUnit_unique (toUnit (𝟙_ (Over SpecQ))) (𝟙 _), Category.id_comp]
    rw [← h1, Over.comp_left, Scheme.Hom.comp_apply]
    have h2 : genericPoint X.left ⤳ P₀.left a := genericPoint_specializes _
    have h3 := h2.map g.left.continuous
    rw [hη] at h3
    exact h3.mem_closed hq rfl
  -- conclusion at the generic point
  apply Over.OverMorphism.ext
  refine ext_of_fromSpecResidueField_eq g.left (1 : X ⟶ J.X).left J.X.hom {genericPoint X.left}
    (dense_iff_closure_eq.mpr (genericPoint_spec X.left).def) ?_
    (by rw [Over.w g, Over.w (1 : X ⟶ J.X)])
  rintro r rfl
  apply (Scheme.SpecToEquivOfField _ J.X.left).injective
  rw [Scheme.SpecToEquivOfField_eq_iff]
  have e1 : (X.left.fromSpecResidueField (genericPoint X.left) ≫ g.left)
      (IsLocalRing.closedPoint _) = q := by
    change g.left ((X.left.fromSpecResidueField (genericPoint X.left)) (IsLocalRing.closedPoint _)) = q
    rw [← hη]; congr 1; exact Scheme.fromSpecResidueField_apply _ _
  have e2 : (X.left.fromSpecResidueField (genericPoint X.left) ≫ (1 : X ⟶ J.X).left)
      (IsLocalRing.closedPoint _) = q := by
    exact hηJ _
  refine ⟨e1.trans e2.symm, ?_⟩
  have hψ : ∀ y : J.X.left, y = q → Nonempty (J.X.left.residueField y ⟶ CommRingCat.of ℚ) := by
    rintro y rfl
    let f0 : Spec (CommRingCat.of ℚ) ⟶ J.X.left := (η[J.X] : 𝟙_ (Over SpecQ) ⟶ J.X).left
    have h0 : f0 (IsLocalRing.closedPoint ℚ) = q := hηJ _
    exact ⟨(J.X.left.residueFieldCongr h0.symm).hom ≫
      J.X.left.descResidueField (Scheme.stalkClosedPointTo f0)⟩
  obtain ⟨ψ⟩ := hψ _ e1
  apply CommRingCat.hom_ext
  exact ringHom_ext_of_toRat ψ.hom _ _


/-! ## 6. Complex points from places: `X1TauPoints` from `TauPlace` -/

/-- Morphisms to `Spec ℚ` are unique. -/
theorem specQ_ext {Y : Scheme} (f g : Y ⟶ SpecQ) : f = g := by
  apply ext_of_isAffine
  rw [← cancel_epi (Scheme.ΓSpecIso (CommRingCat.of ℚ)).inv]
  ext1
  exact RingHom.ext_rat _ _

/-- The value of a section at a complex point is computed in the stalk. -/
theorem value_eq {Y : Scheme} (f : Spec (CommRingCat.of ℂ) ⟶ Y) {U : Y.Opens} (s : Γ(Y, U))
    (hle : ⊤ ≤ f ⁻¹ᵁ U) :
    (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom (f.appLE U ⊤ hle s) =
      Scheme.stalkClosedPointTo f (Y.presheaf.germ U _ (hle trivial) s) := by
  have h := congrArg (fun φ => φ.hom s) (Scheme.germ_stalkClosedPointTo f U (hle trivial))
  refine Eq.trans ?_ h.symm
  rfl

/-- The value at a complex point factoring through `Spec 𝒪_{Y,p}`. -/
theorem value_fromSpecStalk {Y : Scheme} {p : Y} (F : Y.presheaf.stalk p ⟶ CommRingCat.of ℂ)
    [IsLocalHom F.hom] {U : Y.Opens} (s : Γ(Y, U)) (hpU : p ∈ U)
    (f : Spec (CommRingCat.of ℂ) ⟶ Y) (hf : f = Spec.map F ≫ Y.fromSpecStalk p)
    (hle : ⊤ ≤ f ⁻¹ᵁ U) :
    (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom (f.appLE U ⊤ hle s) =
      F (Y.presheaf.germ U p hpU s) := by
  subst hf
  rw [value_eq]
  have := congrArg (fun φ => φ.hom s)
    (Scheme.germ_stalkClosedPointTo_Spec_fromSpecStalk F U (hle trivial))
  exact this

section Place

variable (O : ValuationSubring X.left.functionField) (ev : O →+* ℂ)

theorem charZero_of_place (O : ValuationSubring X.left.functionField) (ev : O →+* ℂ) :
    CharZero X.left.functionField := by
  have : CharZero O := RingHom.charZero ev
  refine ⟨fun m n h => ?_⟩
  have h' : ((m : O) : X.left.functionField) = ((n : O) : X.left.functionField) := by
    simpa using h
  exact Nat.cast_injective (Subtype.ext h')

theorem rat_mem [CharZero X.left.functionField] (hev : ∀ a : O, ev a ≠ 0 → IsUnit a) (r : ℚ) :
    ((r : ℚ) : X.left.functionField) ∈ O := by
  have hd : IsUnit ((r.den : ℕ) : O) := hev _ (by simp)
  obtain ⟨u, hu⟩ := hd
  have hinv : (((u⁻¹ : Oˣ) : O) : X.left.functionField) = ((r.den : X.left.functionField))⁻¹ := by
    apply eq_inv_of_mul_eq_one_left
    have := congrArg (fun y : O => (y : X.left.functionField)) (Units.inv_mul u)
    simp only [hu] at this
    simpa using this
  rw [Rat.cast_def, div_eq_mul_inv]
  exact mul_mem (intCast_mem O _) (by rw [← hinv]; exact ((u⁻¹ : Oˣ) : O).2)

/-- `ℚ → O`. -/
def ratHom [CharZero X.left.functionField] (hev : ∀ a : O, ev a ≠ 0 → IsUnit a) : ℚ →+* O where
  toFun r := ⟨_, rat_mem O ev hev r⟩
  map_one' := by ext; simp
  map_mul' a b := by ext; simp
  map_zero' := by ext; simp
  map_add' a b := by ext; simp

end Place

/-- **The center of a place.** Given a valuation subring `O` of `K(X)` with a local homomorphism
`ev : O → ℂ`, there is a complex point `x` of the curve `X` at which every element `a ∈ O` is
regular with value `ev a` (valuative criterion of properness; the local rings of the smooth curve
are valuation rings). -/
theorem exists_cpt_of_place (hC : IsCurve X) (O : ValuationSubring X.left.functionField)
    (ev : O →+* ℂ) (hev : ∀ a : O, ev a ≠ 0 → IsUnit a) :
    ∃ x : CPt X, ∀ (a : X.left.functionField) (h : a ∈ O), RegAt x a (ev ⟨a, h⟩) := by
  have : IsProper X.hom := hC.proper
  have : SmoothOfRelativeDimension 1 X.hom := hC.smooth
  have := charZero_of_place O ev
  have hUC : ValuativeCriterion.Existence X.hom := by
    have : (ValuativeCriterion.Existence ⊓ @QuasiCompact) X.hom := by
      rw [← UniversallyClosed.eq_valuativeCriterion]; infer_instance
    exact this.1
  let S : ValuativeCommSq X.hom :=
    { R := O
      K := X.left.functionField
      i₁ := X.left.fromSpecStalk (genericPoint X.left)
      i₂ := Spec.map (CommRingCat.ofHom (ratHom O ev hev))
      commSq := ⟨specQ_ext _ _⟩ }
  obtain ⟨⟨ℓ, hℓ1, -⟩⟩ := (hUC S).exists_lift
  -- the center `p` and the local homomorphism `φ : 𝒪_{X,p} → O`
  set p := ℓ (IsLocalRing.closedPoint O) with hp
  let φ := Scheme.stalkClosedPointTo ℓ
  have hℓ : Spec.map φ ≫ X.left.fromSpecStalk p = ℓ := Scheme.Spec_stalkClosedPointTo_fromSpecStalk ℓ
  have hsp : genericPoint X.left ⤳ p := (genericPoint_spec X.left).specializes trivial
  let sp := X.left.presheaf.stalkSpecializes hsp
  have hcomp : φ ≫ CommRingCat.ofHom (algebraMap O X.left.functionField) = sp := by
    apply Spec.map_inj.mp
    rw [← cancel_mono (X.left.fromSpecStalk p), Spec.map_comp, Category.assoc, hℓ,
      Scheme.SpecMap_stalkSpecializes_fromSpecStalk]
    exact hℓ1
  have hcompE : ∀ b, ((φ b : O) : X.left.functionField) = sp b := fun b =>
    congrArg (fun u => u.hom b) hcomp
  -- `O` is the local ring at `p`
  have hval : ValuationRing (X.left.presheaf.stalk p) := Scheme.valuationRing_stalk X.hom p
  have hdom : ∀ a ∈ O, ∃ b, sp b = a := by
    intro a ha
    obtain ⟨b1, b2, hb2, rfl⟩ :=
      IsFractionRing.div_surjective (A := X.left.presheaf.stalk p) (K := X.left.functionField) a
    have hinj : Function.Injective sp := IsFractionRing.injective (X.left.presheaf.stalk p) _
    have hb2' : b2 ≠ 0 := nonZeroDivisors.ne_zero hb2
    have hs2 : sp b2 ≠ 0 := fun h => hb2' (hinj (by rw [h, map_zero]))
    change sp b1 / sp b2 ∈ O at ha
    change ∃ b, sp b = sp b1 / sp b2
    obtain ⟨c, hc | hc⟩ := ValuationRing.cond b1 b2
    · by_cases hb1 : b1 = 0
      · exact ⟨0, by simp [hb1]⟩
      have hs1 : sp b1 ≠ 0 := fun h => hb1 (hinj (by rw [h, map_zero]))
      have hcne : sp c ≠ 0 := fun h => hs2 (by rw [← hc, map_mul, h, mul_zero])
      have hq : sp b1 / sp b2 = (sp c)⁻¹ := by
        rw [← hc, map_mul]; field_simp
      by_cases hu : IsUnit c
      · refine ⟨((hu.unit⁻¹ : (X.left.presheaf.stalk p)ˣ) : X.left.presheaf.stalk p), ?_⟩
        rw [hq]
        apply eq_inv_of_mul_eq_one_left
        rw [← map_mul]
        have : ((hu.unit⁻¹ : (X.left.presheaf.stalk p)ˣ) : X.left.presheaf.stalk p) * c = 1 :=
          hu.val_inv_mul
        rw [this, map_one]
      · exfalso
        apply hu
        apply isUnit_of_map_unit φ.hom
        refine isUnit_iff_exists_inv.mpr ⟨⟨_, ha⟩, Subtype.ext ?_⟩
        change ((φ c : O) : X.left.functionField) * (sp b1 / sp b2) = 1
        rw [hcompE, hq, mul_inv_cancel₀ hcne]
    · exact ⟨c, by rw [← hc, map_mul]; field_simp⟩
  -- the complex point
  have : IsLocalHom ev := ⟨fun a ha => hev a (IsUnit.ne_zero ha)⟩
  have : IsLocalHom (CommRingCat.ofHom ev).hom := ‹IsLocalHom ev›
  let xl : Spec (CommRingCat.of ℂ) ⟶ X.left := Spec.map (CommRingCat.ofHom ev) ≫ ℓ
  have hxl : xl = Spec.map (φ ≫ CommRingCat.ofHom ev) ≫ X.left.fromSpecStalk p := by
    simp only [xl, Spec.map_comp, Category.assoc, hℓ]
  have hxp : ∀ z, xl z = p := fun z => by
    rw [Subsingleton.elim z (IsLocalRing.closedPoint ℂ)]
    exact congrArg ℓ (Spec_closedPoint (f := CommRingCat.ofHom ev))
  have : IsLocalHom (φ ≫ CommRingCat.ofHom ev).hom :=
    inferInstanceAs (IsLocalHom ((CommRingCat.ofHom ev).hom.comp φ.hom))
  refine ⟨Over.homMk xl (specQ_ext _ _), fun a ha => ?_⟩
  obtain ⟨b, hb⟩ := hdom a ha
  obtain ⟨U, hpU, s, hs⟩ := X.left.presheaf.germ_exist b
  have hne : Nonempty U := ⟨⟨p, hpU⟩⟩
  have hle : ⊤ ≤ xl ⁻¹ᵁ U := fun z _ => by
    show xl z ∈ U
    rw [hxp z]; exact hpU
  refine ⟨U, hne, s, hle, ?_, ?_⟩
  · rw [← hb, ← hs]
    exact (TopCat.Presheaf.germ_stalkSpecializes_apply _ _ _ _).symm
  · refine (value_fromSpecStalk (φ ≫ CommRingCat.ofHom ev) s hpU xl hxl hle).trans ?_
    rw [hs]
    change ev (φ b) = ev ⟨a, ha⟩
    congr 1
    exact Subtype.ext ((hcompE b).trans hb)


/-- **GLUE (analytic): the place of `K(X) = ℚ(j_X, t_X)` at `τ ∈ ℍ`.** For a model `X` of DS's
`X₁(N)_alg` with generators `(j_X, t_X)` (`IsX1Gen`) and `τ ∈ ℍ`, there are a valuation subring `O` of
`K(X)` and a local homomorphism `ev : O → ℂ` such that every `P(j_X, t_X)/Q(j_X, t_X)` whose meromorphic
function `P(j, f₁)/Q(j, f₁)` has a limit `c` at `τ` (over the punctured neighbourhood) lies in `O` with
`ev = c`. (`O` = the functions with a finite limit at `τ`, `ev` = the limit.) -/
def TauPlace : Prop :=
  ∀ (N : ℕ), 2 ≤ N → ∀ (X : Over SpecQ) [IsIntegral X.left] (jX tX : X.left.functionField),
    IsX1Gen N X jX tX → ∀ τ : UpperHalfPlane,
      ∃ (O : ValuationSubring X.left.functionField) (ev : O →+* ℂ),
        (∀ a : O, ev a ≠ 0 → IsUnit a) ∧
        ∀ (P Q : Polynomial (Polynomial ℤ)) (c : ℂ), AfTateOr.ev2 Q jX tX ≠ 0 →
          Filter.Tendsto (fun τ' => X1Igusa.Weber.evAn N (AfTateOr.toQ P) τ' /
            X1Igusa.Weber.evAn N (AfTateOr.toQ Q) τ') (nhdsWithin τ {τ}ᶜ) (nhds c) →
          ∃ h : AfTateOr.ev2 P jX tX / AfTateOr.ev2 Q jX tX ∈ O, ev ⟨_, h⟩ = c

/-- **`X1TauPoints` from the place at `τ`.** -/
theorem x1TauPoints_of_tauPlace (hT : TauPlace) : X1TauPoints := by
  intro N hN X _ jX tX hC hG τ
  obtain ⟨O, ev, hev, hO⟩ := hT N hN X jX tX hG τ
  obtain ⟨x, hx⟩ := exists_cpt_of_place hC O ev hev
  refine ⟨x, fun P Q c hQ hlim => ?_⟩
  obtain ⟨h, hc⟩ := hO P Q c hQ hlim
  exact hc ▸ hx _ h

open Filter Topology
open X1Igusa.Weber (Hs isOpen_Hs G2f G3f diffOn_G2f diffOn_G3f exists_good_point)

/-! ## 7. The place at `τ` (proof of `TauPlace`) -/

/-- `F ↦ F(a, b)` as a ring homomorphism. -/
def ev2Hom {K : Type*} [CommRing K] (a b : K) : Polynomial (Polynomial ℤ) →+* K :=
  (Polynomial.evalRingHom b).comp
    (Polynomial.mapRingHom (Polynomial.eval₂RingHom (Int.castRingHom K) a))

theorem ev2_eq {K : Type*} [CommRing K] (F : Polynomial (Polynomial ℤ)) (a b : K) :
    AfTateOr.ev2 F a b = ev2Hom a b F := rfl

/-- The holomorphic function `F(j, f₁)` on `ℍ ⊂ ℂ` (Weber's generic branch). -/
def holHom (N : ℕ) (z : ℂ) : Polynomial (Polynomial ℤ) →+* ℂ :=
  (X1Igusa.Weber.ez N z).comp AfTateOr.toQ

theorem diffOn_hol (hN : 2 ≤ N) (F : Polynomial (Polynomial ℤ)) :
    DifferentiableOn ℂ (fun z => holHom N z F) Hs :=
  X1Igusa.Weber.diffOn_ez hN _

theorem evAn_eq_hol (F : Polynomial (Polynomial ℤ)) (τ : UpperHalfPlane)
    (h2 : (T5Glue.pp τ).g₂ ≠ 0) (h3 : (T5Glue.pp τ).g₃ ≠ 0) :
    X1Igusa.Weber.evAn N (AfTateOr.toQ F) τ = holHom N τ F :=
  X1Igusa.Weber.evAn_eq _ τ h2 h3

/-- A holomorphic function on `ℍ` that is not identically zero is nonzero near `τ`, `≠ τ`. -/
theorem eventually_ne_of_diffOn {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f Hs)
    (hne : ∃ z ∈ Hs, f z ≠ 0) (τ : UpperHalfPlane) : ∀ᶠ z in 𝓝[≠] (τ : ℂ), f z ≠ 0 := by
  have ha : AnalyticAt ℂ f τ := hf.analyticAt (isOpen_Hs.mem_nhds τ.coe_im_pos)
  rcases ha.eventually_eq_zero_or_eventually_ne_zero with h | h
  · obtain ⟨z, hz, hfz⟩ := hne
    exact absurd (X1Igusa.Weber.eq_zero_of_eventually hf τ.coe_im_pos h z hz) hfz
  · exact h

theorem eventually_good (τ : UpperHalfPlane) :
    ∀ᶠ z in 𝓝[≠] (τ : ℂ), G2f z * G3f z ≠ 0 := by
  obtain ⟨z, hz, h2, h3⟩ := exists_good_point
  exact eventually_ne_of_diffOn (diffOn_G2f.mul diffOn_G3f) ⟨z, hz, mul_ne_zero h2 h3⟩ τ

theorem eventually_mem_Hs (τ : UpperHalfPlane) : ∀ᶠ z in 𝓝[≠] (τ : ℂ), z ∈ Hs :=
  nhdsWithin_le_nhds (isOpen_Hs.mem_nhds τ.coe_im_pos)

variable {jX tX : X.left.functionField}

theorem hol_eq_zero_of_ev2 (hN : 2 ≤ N) (hG : IsX1Gen N X jX tX) {F : Polynomial (Polynomial ℤ)}
    (hF : AfTateOr.ev2 F jX tX = 0) : ∀ z ∈ Hs, holHom N z F = 0 := by
  have h := (hG.2 F).1 hF
  have hprod : ∀ z ∈ Hs, (G2f z * G3f z) * holHom N z F = 0 := by
    intro z hz
    by_cases h23 : G2f z * G3f z = 0
    · rw [h23, zero_mul]
    · obtain ⟨h2', h3'⟩ := mul_ne_zero_iff.mp h23
      have := h (UpperHalfPlane.ofComplex z) h2' h3'
      rw [evAn_eq_hol F _ h2' h3', X1Igusa.Weber.ofComplex_coe hz] at this
      rw [this, mul_zero]
  rcases X1Igusa.Weber.eq_zero_or_eq_zero (diffOn_G2f.mul diffOn_G3f) (diffOn_hol hN F) hprod
    with h1 | h1
  · exfalso
    obtain ⟨z, hz, h2, h3⟩ := exists_good_point
    exact mul_ne_zero h2 h3 (h1 z hz)
  · exact h1

theorem ev2_eq_zero_of_hol (hG : IsX1Gen N X jX tX) {F : Polynomial (Polynomial ℤ)}
    (h : ∀ z ∈ Hs, holHom N z F = 0) : AfTateOr.ev2 F jX tX = 0 :=
  (hG.2 F).2 fun τ' h2 h3 => by rw [evAn_eq_hol F τ' h2 h3]; exact h _ τ'.coe_im_pos

theorem eventually_hol_ne (hN : 2 ≤ N) (hG : IsX1Gen N X jX tX) {Q : Polynomial (Polynomial ℤ)}
    (hQ : AfTateOr.ev2 Q jX tX ≠ 0) (τ : UpperHalfPlane) :
    ∀ᶠ z in 𝓝[≠] (τ : ℂ), holHom N z Q ≠ 0 := by
  refine eventually_ne_of_diffOn (diffOn_hol hN Q) ?_ τ
  by_contra h
  push Not at h
  exact hQ (ev2_eq_zero_of_hol hG h)

/-- `(P, Q)` represents `a = P(j_X, t_X)/Q(j_X, t_X)`. -/
def IsRep (jX tX : X.left.functionField) (a : X.left.functionField)
    (P Q : Polynomial (Polynomial ℤ)) : Prop :=
  AfTateOr.ev2 Q jX tX ≠ 0 ∧ a = AfTateOr.ev2 P jX tX / AfTateOr.ev2 Q jX tX

theorem exists_rep (hG : IsX1Gen N X jX tX) (a : X.left.functionField) :
    ∃ P Q, IsRep jX tX a P Q := by
  have hle : Subring.closure {jX, tX} ≤ (ev2Hom jX tX).range := by
    rw [Subring.closure_le]
    rintro y (rfl | rfl)
    · exact ⟨Polynomial.C Polynomial.X, by simp [ev2Hom]⟩
    · exact ⟨Polynomial.X, by simp [ev2Hom]⟩
  have ha : a ∈ Subfield.closure {jX, tX} := hG.1 ▸ Subfield.mem_top a
  obtain ⟨y, hy, z, hz, rfl⟩ := Subfield.mem_closure_iff.mp ha
  obtain ⟨P, rfl⟩ := hle hy
  obtain ⟨Q, rfl⟩ := hle hz
  by_cases hQ : ev2Hom jX tX Q = 0
  · exact ⟨0, 1, by simp [ev2_eq], by simp [ev2_eq, hQ]⟩
  · exact ⟨P, Q, hQ, rfl⟩

/-- The representations of `a` give eventually equal functions near `τ`. -/
theorem rep_eventuallyEq (hN : 2 ≤ N) (hG : IsX1Gen N X jX tX) (τ : UpperHalfPlane)
    {a : X.left.functionField} {P Q P' Q' : Polynomial (Polynomial ℤ)}
    (h : IsRep jX tX a P Q) (h' : IsRep jX tX a P' Q') :
    (fun z => holHom N z P / holHom N z Q) =ᶠ[𝓝[≠] (τ : ℂ)]
      fun z => holHom N z P' / holHom N z Q' := by
  have h0 : AfTateOr.ev2 (P * Q' - P' * Q) jX tX = 0 := by
    have e := h.2.symm.trans h'.2
    rw [div_eq_div_iff h.1 h'.1] at e
    rw [ev2_eq, map_sub, map_mul, map_mul, ← ev2_eq, ← ev2_eq, ← ev2_eq, ← ev2_eq, e, sub_self]
  have hz := hol_eq_zero_of_ev2 hN hG h0
  filter_upwards [eventually_hol_ne hN hG h.1 τ, eventually_hol_ne hN hG h'.1 τ,
    eventually_mem_Hs τ] with z h1 h2 h3
  have := hz z h3
  rw [map_sub, map_mul, map_mul] at this
  rw [div_eq_div_iff h1 h2]
  exact sub_eq_zero.mp this

/-- The meromorphic function of `a ∈ K(X)` near `τ`. -/
def mf (hG : IsX1Gen N X jX tX) (a : X.left.functionField) (z : ℂ) : ℂ :=
  holHom N z (exists_rep hG a).choose / holHom N z (exists_rep hG a).choose_spec.choose

theorem mf_eq (hN : 2 ≤ N) (hG : IsX1Gen N X jX tX) (τ : UpperHalfPlane)
    {a : X.left.functionField} {P Q : Polynomial (Polynomial ℤ)} (h : IsRep jX tX a P Q) :
    mf hG a =ᶠ[𝓝[≠] (τ : ℂ)] fun z => holHom N z P / holHom N z Q :=
  rep_eventuallyEq hN hG τ (exists_rep hG a).choose_spec.choose_spec h


section Ops

variable {a b : X.left.functionField} {P Q P' Q' : Polynomial (Polynomial ℤ)}

theorem isRep_add (h : IsRep jX tX a P Q) (h' : IsRep jX tX b P' Q') :
    IsRep jX tX (a + b) (P * Q' + P' * Q) (Q * Q') := by
  have hQ := h.1; have hQ' := h'.1
  simp only [ev2_eq] at hQ hQ'
  refine ⟨by simp only [ev2_eq, map_mul]; exact mul_ne_zero hQ hQ', ?_⟩
  rw [h.2, h'.2]; simp only [ev2_eq, map_add, map_mul]; field_simp

theorem isRep_mul (h : IsRep jX tX a P Q) (h' : IsRep jX tX b P' Q') :
    IsRep jX tX (a * b) (P * P') (Q * Q') := by
  have hQ := h.1; have hQ' := h'.1
  simp only [ev2_eq] at hQ hQ'
  refine ⟨by simp only [ev2_eq, map_mul]; exact mul_ne_zero hQ hQ', ?_⟩
  rw [h.2, h'.2]; simp only [ev2_eq, map_mul]; field_simp

theorem isRep_neg (h : IsRep jX tX a P Q) : IsRep jX tX (-a) (-P) Q :=
  ⟨h.1, by rw [h.2]; simp only [ev2_eq, map_neg, neg_div]⟩

theorem isRep_zero : IsRep jX tX 0 0 1 := ⟨by simp [ev2_eq], by simp [ev2_eq]⟩

theorem isRep_one : IsRep jX tX 1 1 1 := ⟨by simp [ev2_eq], by simp [ev2_eq]⟩

theorem ev2_ne_of_isRep (h : IsRep jX tX a P Q) (ha : a ≠ 0) : AfTateOr.ev2 P jX tX ≠ 0 := by
  intro h0; apply ha; rw [h.2, h0, zero_div]

theorem isRep_inv (h : IsRep jX tX a P Q) (ha : a ≠ 0) : IsRep jX tX a⁻¹ Q P :=
  ⟨ev2_ne_of_isRep h ha, by rw [h.2, inv_div]⟩

variable (hN : 2 ≤ N) (hG : IsX1Gen N X jX tX) (τ : UpperHalfPlane)
include hN

theorem mf_add (a b : X.left.functionField) :
    mf hG (a + b) =ᶠ[𝓝[≠] (τ : ℂ)] mf hG a + mf hG b := by
  obtain ⟨P, Q, h⟩ := exists_rep hG a
  obtain ⟨P', Q', h'⟩ := exists_rep hG b
  filter_upwards [mf_eq hN hG τ (isRep_add h h'), mf_eq hN hG τ h, mf_eq hN hG τ h',
    eventually_hol_ne hN hG h.1 τ, eventually_hol_ne hN hG h'.1 τ] with z e1 e2 e3 n1 n2
  rw [e1, Pi.add_apply, e2, e3]
  simp only [map_add, map_mul]
  field_simp

theorem mf_mul (a b : X.left.functionField) :
    mf hG (a * b) =ᶠ[𝓝[≠] (τ : ℂ)] mf hG a * mf hG b := by
  obtain ⟨P, Q, h⟩ := exists_rep hG a
  obtain ⟨P', Q', h'⟩ := exists_rep hG b
  filter_upwards [mf_eq hN hG τ (isRep_mul h h'), mf_eq hN hG τ h, mf_eq hN hG τ h',
    eventually_hol_ne hN hG h.1 τ, eventually_hol_ne hN hG h'.1 τ] with z e1 e2 e3 n1 n2
  rw [e1, Pi.mul_apply, e2, e3]
  simp only [map_mul]
  field_simp

theorem mf_neg (a : X.left.functionField) : mf hG (-a) =ᶠ[𝓝[≠] (τ : ℂ)] -mf hG a := by
  obtain ⟨P, Q, h⟩ := exists_rep hG a
  filter_upwards [mf_eq hN hG τ (isRep_neg h), mf_eq hN hG τ h] with z e1 e2
  rw [e1, Pi.neg_apply, e2, map_neg, neg_div]

theorem mf_zero : mf hG 0 =ᶠ[𝓝[≠] (τ : ℂ)] fun _ => 0 := by
  filter_upwards [mf_eq hN hG τ isRep_zero] with z e1
  rw [e1, map_zero, zero_div]

theorem mf_one : mf hG 1 =ᶠ[𝓝[≠] (τ : ℂ)] fun _ => 1 := by
  filter_upwards [mf_eq hN hG τ isRep_one] with z e1
  rw [e1, map_one, div_one]

theorem mf_inv {a : X.left.functionField} (ha : a ≠ 0) :
    mf hG a⁻¹ =ᶠ[𝓝[≠] (τ : ℂ)] (mf hG a)⁻¹ := by
  obtain ⟨P, Q, h⟩ := exists_rep hG a
  filter_upwards [mf_eq hN hG τ (isRep_inv h ha), mf_eq hN hG τ h] with z e1 e2
  rw [e1, Pi.inv_apply, e2, inv_div]

/-- The valuation subring of the place at `τ`: the functions with a finite limit at `τ`. -/
def placeO : ValuationSubring X.left.functionField where
  carrier := {a | ∃ c, Tendsto (mf hG a) (𝓝[≠] (τ : ℂ)) (𝓝 c)}
  mul_mem' := by
    rintro a b ⟨c, hc⟩ ⟨d, hd⟩
    exact ⟨c * d, (hc.mul hd).congr' (mf_mul hN hG τ a b).symm⟩
  one_mem' := ⟨1, tendsto_const_nhds.congr' (mf_one hN hG τ).symm⟩
  add_mem' := by
    rintro a b ⟨c, hc⟩ ⟨d, hd⟩
    exact ⟨c + d, (hc.add hd).congr' (mf_add hN hG τ a b).symm⟩
  zero_mem' := ⟨0, tendsto_const_nhds.congr' (mf_zero hN hG τ).symm⟩
  neg_mem' := by
    rintro a ⟨c, hc⟩
    exact ⟨-c, hc.neg.congr' (mf_neg hN hG τ a).symm⟩
  mem_or_inv_mem' a := by
    by_cases ha : a = 0
    · left; rw [ha]; exact ⟨0, tendsto_const_nhds.congr' (mf_zero hN hG τ).symm⟩
    obtain ⟨P, Q, h⟩ := exists_rep hG a
    have hP := ev2_ne_of_isRep h ha
    have hτ : Hs ∈ 𝓝 (τ : ℂ) := isOpen_Hs.mem_nhds τ.coe_im_pos
    have hm : MeromorphicAt (fun z => holHom N z P / holHom N z Q) (τ : ℂ) :=
      ((diffOn_hol hN P).analyticAt hτ).meromorphicAt.div
        ((diffOn_hol hN Q).analyticAt hτ).meromorphicAt
    rcases lt_or_ge (meromorphicOrderAt (fun z => holHom N z P / holHom N z Q) (τ : ℂ)) 0
      with ho | ho
    · right
      refine ⟨0, (tendsto_inv₀_cobounded.comp
        (tendsto_cobounded_of_meromorphicOrderAt_neg ho)).congr' ?_⟩
      filter_upwards [mf_eq hN hG τ (isRep_inv h ha)] with z e
      rw [e]; simp only [Function.comp, inv_div]
    · left
      obtain ⟨c, hc⟩ := tendsto_nhds_of_meromorphicOrderAt_nonneg hm ho
      exact ⟨c, hc.congr' (mf_eq hN hG τ h).symm⟩

theorem mem_placeO {a : X.left.functionField} :
    a ∈ placeO hN hG τ ↔ ∃ c, Tendsto (mf hG a) (𝓝[≠] (τ : ℂ)) (𝓝 c) := Iff.rfl

theorem lim_unique {a : X.left.functionField} {c d : ℂ}
    (hc : Tendsto (mf hG a) (𝓝[≠] (τ : ℂ)) (𝓝 c)) (hd : Tendsto (mf hG a) (𝓝[≠] (τ : ℂ)) (𝓝 d)) :
    c = d := tendsto_nhds_unique hc hd

/-- The evaluation at `τ`: the limit. -/
def placeEv : placeO hN hG τ →+* ℂ where
  toFun a := ((mem_placeO hN hG τ).mp a.2).choose
  map_one' := lim_unique hN hG τ ((mem_placeO hN hG τ).mp (placeO hN hG τ).one_mem).choose_spec
    (tendsto_const_nhds.congr' (mf_one hN hG τ).symm)
  map_mul' a b := lim_unique hN hG τ ((mem_placeO hN hG τ).mp (a * b).2).choose_spec
    ((((mem_placeO hN hG τ).mp a.2).choose_spec.mul
      ((mem_placeO hN hG τ).mp b.2).choose_spec).congr' (mf_mul hN hG τ a b).symm)
  map_zero' := lim_unique hN hG τ ((mem_placeO hN hG τ).mp (placeO hN hG τ).zero_mem).choose_spec
    (tendsto_const_nhds.congr' (mf_zero hN hG τ).symm)
  map_add' a b := lim_unique hN hG τ ((mem_placeO hN hG τ).mp (a + b).2).choose_spec
    ((((mem_placeO hN hG τ).mp a.2).choose_spec.add
      ((mem_placeO hN hG τ).mp b.2).choose_spec).congr' (mf_add hN hG τ a b).symm)

theorem placeEv_spec (a : placeO hN hG τ) :
    Tendsto (mf hG (a : X.left.functionField)) (𝓝[≠] (τ : ℂ)) (𝓝 (placeEv hN hG τ a)) :=
  ((mem_placeO hN hG τ).mp a.2).choose_spec

theorem placeEv_local (a : placeO hN hG τ) (h : placeEv hN hG τ a ≠ 0) : IsUnit a := by
  have ha : (a : X.left.functionField) ≠ 0 := by
    intro h0
    apply h
    apply lim_unique hN hG τ (placeEv_spec hN hG τ a)
    rw [h0]; exact tendsto_const_nhds.congr' (mf_zero hN hG τ).symm
  have hmem : (a : X.left.functionField)⁻¹ ∈ placeO hN hG τ :=
    ⟨_, ((placeEv_spec hN hG τ a).inv₀ h).congr' (mf_inv hN hG τ ha).symm⟩
  exact isUnit_iff_exists_inv.mpr ⟨⟨_, hmem⟩, Subtype.ext (mul_inv_cancel₀ ha)⟩

end Ops


/-- From the analytic limit on `ℍ` to the generic branch near `τ` in `ℂ`. -/
theorem tendsto_hol (τ : UpperHalfPlane) {P Q : Polynomial (Polynomial ℤ)} {c : ℂ}
    (h : Tendsto (fun τ' => X1Igusa.Weber.evAn N (AfTateOr.toQ P) τ' /
      X1Igusa.Weber.evAn N (AfTateOr.toQ Q) τ') (𝓝[≠] τ) (𝓝 c)) :
    Tendsto (fun z => holHom N z P / holHom N z Q) (𝓝[≠] (τ : ℂ)) (𝓝 c) := by
  have h1 : Tendsto UpperHalfPlane.ofComplex (𝓝[≠] (τ : ℂ)) (𝓝[≠] τ) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
    · rw [UpperHalfPlane.isEmbedding_coe.tendsto_nhds_iff]
      exact (tendsto_id.congr'
        (UpperHalfPlane.eventuallyEq_coe_comp_ofComplex τ.coe_im_pos).symm).mono_left
          nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin, eventually_mem_Hs τ] with z hz hH
      intro heq
      apply hz
      rw [← X1Igusa.Weber.ofComplex_coe hH, Set.mem_singleton_iff.mp heq]
      rfl
  refine (h.comp h1).congr' ?_
  filter_upwards [eventually_good τ, eventually_mem_Hs τ] with z hg hH
  obtain ⟨h2, h3⟩ := mul_ne_zero_iff.mp hg
  simp only [Function.comp]
  rw [evAn_eq_hol P _ h2 h3, evAn_eq_hol Q _ h2 h3, X1Igusa.Weber.ofComplex_coe hH]

/-- **`TauPlace` holds** (the place of `K(X)` at `τ`: functions with a finite limit). -/
theorem tauPlace : TauPlace := by
  intro N hN X _ jX tX hG τ
  refine ⟨placeO hN hG τ, placeEv hN hG τ, placeEv_local hN hG τ, ?_⟩
  intro P Q c hQ hlim
  have hrep : IsRep jX tX (AfTateOr.ev2 P jX tX / AfTateOr.ev2 Q jX tX) P Q := ⟨hQ, rfl⟩
  have hm : Tendsto (mf hG (AfTateOr.ev2 P jX tX / AfTateOr.ev2 Q jX tX)) (𝓝[≠] (τ : ℂ)) (𝓝 c) :=
    (tendsto_hol τ hlim).congr' (mf_eq hN hG τ hrep).symm
  exact ⟨⟨c, hm⟩, lim_unique hN hG τ (placeEv_spec hN hG τ ⟨_, ⟨c, hm⟩⟩) hm⟩

/-! ## 8. The three inputs of the Hecke dictionary, discharged -/

/-- **`X1TauPoints` holds** (it is glue, not a leaf). -/
theorem x1TauPoints : X1TauPoints := x1TauPoints_of_tauPlace tauPlace

/-- **`ConstOnTauPoints` holds.** -/
theorem constOnTauPoints : ConstOnTauPoints := constOnTauPoints_of_x1TauPoints x1TauPoints

/-- **`IsHeckeT` pins `T_p`**, with no remaining hypothesis. -/
theorem isHeckeT_unique' {N : ℕ} (hN : 2 ≤ N) {X : Over SpecQ} [IsIntegral X.left] {J : AbVar ℚ}
    {jX tX : X.left.functionField} (hC : IsCurve X) (hG : IsX1Gen N X jX tX) {P₀ : RatPt X}
    {aj : X ⟶ J.X} (hJ : IsJacobian X P₀ J aj) (p : Nat.Primes) {t t' : AbVar.End J}
    (ht : IsHeckeT N jX tX aj (p : ℕ) t) (ht' : IsHeckeT N jX tX aj (p : ℕ) t') : t = t' :=
  isHeckeT_unique x1TauPoints constOnTauPoints hN hC hG hJ p ht ht'

/-- **`IsDiamond` pins `⟨d⟩`**, with no remaining hypothesis. -/
theorem isDiamond_unique' {N : ℕ} (hN : 2 ≤ N) {X : Over SpecQ} [IsIntegral X.left] {J : AbVar ℚ}
    {jX tX : X.left.functionField} (hC : IsCurve X) (hG : IsX1Gen N X jX tX) {P₀ : RatPt X}
    {aj : X ⟶ J.X} (hJ : IsJacobian X P₀ J aj) (d : (ZMod N)ˣ) {t t' : AbVar.End J}
    (ht : IsDiamond N jX tX aj d t) (ht' : IsDiamond N jX tX aj d t') : t = t' :=
  isDiamond_unique x1TauPoints constOnTauPoints hN hC hG hJ d ht ht'

/-- **`ker(heckeJ) ⊆ ker(evF)`, from the leaf candidate `AbelJacobiX1` alone.** -/
theorem evF_eq_zero_of_heckeJ_eq_zero_of_abelJacobi (hAJ : AbelJacobiX1) {N : ℕ} (hN : 2 ≤ N)
    {χ : DirichletCharacter ℂ N} {f : PkgI4.CF N 2} (hf : PkgI4.IsNormalizedEigenform f χ)
    {X : Over SpecQ} [IsIntegral X.left] {J : AbVar ℚ} {jX tX : X.left.functionField}
    (hC : IsCurve X) (hG : IsX1Gen N X jX tX) {P₀ : RatPt X} {aj : X ⟶ J.X}
    (hJ : IsJacobian X P₀ J aj) {tp : Nat.Primes → AbVar.End J} {δ : (ZMod N)ˣ → AbVar.End J}
    (htp : ∀ p : Nat.Primes, IsHeckeT N jX tX aj (p : ℕ) (tp p))
    (hδ : ∀ d : (ZMod N)ˣ, IsDiamond N jX tX aj d (δ d)) (h : HeckeFree N)
    (h0 : heckeJ tp δ h = 0) : evF χ f h = 0 :=
  evF_eq_zero_of_heckeJ_eq_zero_of_leaves x1TauPoints hAJ hN hf hC hG hJ htp hδ h h0

/-- **`KillsIf φ` iff `φ` kills DS's `I_f J`, from the leaf candidate `AbelJacobiX1` alone.** -/
theorem killsIf_iff_IfDS_of_abelJacobi (hAJ : AbelJacobiX1) {N : ℕ} (hN : 2 ≤ N)
    {χ : DirichletCharacter ℂ N} {f : PkgI4.CF N 2} (hf : PkgI4.IsNormalizedEigenform f χ)
    {X : Over SpecQ} [IsIntegral X.left] {J : AbVar ℚ} {jX tX : X.left.functionField}
    (hC : IsCurve X) (hG : IsX1Gen N X jX tX) {P₀ : RatPt X} {aj : X ⟶ J.X}
    (hJ : IsJacobian X P₀ J aj) {tp : Nat.Primes → AbVar.End J} {δ : (ZMod N)ˣ → AbVar.End J}
    (htp : ∀ p : Nat.Primes, IsHeckeT N jX tX aj (p : ℕ) (tp p))
    (hδ : ∀ d : (ZMod N)ˣ, IsDiamond N jX tX aj d (δ d)) {B : AbVar ℚ} (φ : AbVar.Hom J B) :
    KillsIf χ f tp δ φ ↔ ∀ T ∈ IfDS χ f tp δ, T.hom ≫ φ.hom = (0 : AbVar.Hom J B).hom :=
  killsIf_iff_IfDS_of_leaves x1TauPoints hAJ hN hf hC hG hJ htp hδ φ

end AfTateLam.HeckeGlue
