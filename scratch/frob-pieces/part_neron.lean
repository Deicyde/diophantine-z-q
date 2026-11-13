
/-! # frob-pieces: `GoodRedCofinite` from neron-lg's glue N1-g1 `AbVarSpreadsOut` and Zariski's
connectedness theorem (task frob-pieces)

`HasAbelianSchemeAway` and `AbVarSpreadsOut` below are verbatim copies (docstring and `def`) of
the declarations of the same names in `scratch/neron-lg/NeronLG.lean` (namespace
`ZInQ.NeronLG`), under the same `open`s (checked by `scratch/frob-pieces/py/verbatim_check.py`). -/

noncomputable section

namespace FrobPiecesNeron

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open NumberField
open PkgI3 (AbVar)
open scoped Obj

/-- `B` extends to an abelian scheme over `𝓞_L[1/f]`: a smooth proper group scheme whose generic
fibre is identified with `B` as a group scheme (over every presentation of `𝓞_L[1/f]`). -/
def HasAbelianSchemeAway (L : Type) [Field L] [NumberField L] (B : AbVar L) (f : 𝓞 L) : Prop :=
  ∀ (R : Type) [CommRing R] [Algebra (𝓞 L) R] [IsLocalization.Away f R] [Algebra R L]
    [IsScalarTower (𝓞 L) R L],
    ∃ (G : Over (Spec (CommRingCat.of R))) (_ : GrpObj G) (_ : Smooth G.hom) (_ : IsProper G.hom)
      (gen : (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap R L)))).obj G ≅ B.X),
      letI : GrpObj ((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap R L)))).obj G) :=
        Functor.grpObjObj
      IsMonHom gen.hom

/-- **Glue N1-g1 (spreading out an abelian variety).** An abelian variety `B` over a number field
`L` extends to an abelian scheme over `𝓞_L[1/f]` for some nonzero `f ∈ 𝓞_L`. Textbook (a
candidate for a textbook leaf): `L = colim 𝓞_L[1/f]`, so `B`, its group law, unit and inverse
and the group axioms (equalities of morphisms) descend to some `𝓞_L[1/f]` (EGA IV₃ 8.8.2), as do
properness (EGA IV₃ 8.10.5 (xii)) and smoothness (EGA IV₄ 17.7.8 (ii)); all locators UNVERIFIED.
Mathlib v4.35 has the descent of morphisms for affine transition maps
(`AlgebraicGeometry/.../AffineTransitionLimit.lean`, EGA IV 8.8.2) but not the descent of schemes
or of properness and smoothness. -/
def AbVarSpreadsOut : Prop :=
  ∀ (L : Type) [Field L] [NumberField L] (B : AbVar L), ∃ f : 𝓞 L, f ≠ 0 ∧ HasAbelianSchemeAway L B f

set_option synthInstance.maxHeartbeats 400000 in
/-- **`ProperSmoothGenConnected` (LEAF candidate, published: Zariski's connectedness theorem).**
A smooth proper scheme `X` over `R = 𝓞_L[1/f]` (any presentation) whose generic fibre is
geometrically connected is geometrically connected over `R`. Proof (STANDARD): `R` is normal and
`X_L` is geometrically reduced (smooth) and geometrically connected and proper, so
`H⁰(X_L, 𝒪) = L`; `f_*𝒪_X` is a finite torsion-free `R`-algebra inside `L`, integral over the
normal `R`, hence `f_*𝒪_X = 𝒪_R`, and then all fibres of the proper `f` are geometrically
connected (Zariski's connectedness theorem, EGA III₁ 4.3.1–4.3.4; Hartshorne III 11.3; locators
UNVERIFIED). Not in Mathlib v4.35 (no Stein factorization). -/
def ProperSmoothGenConnected : Prop :=
  ∀ (L : Type) [Field L] [NumberField L] (f : 𝓞 L) (R : Type) [CommRing R] [Algebra (𝓞 L) R]
    [IsLocalization.Away f R] [Algebra R L] [IsScalarTower (𝓞 L) R L]
    (X : Over (Spec (CommRingCat.of R))), Smooth X.hom → IsProper X.hom →
    GeometricallyConnected
      ((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap R L)))).obj X).hom →
    GeometricallyConnected X.hom

/-- Geometrically integral implies geometrically connected. -/
theorem geometricallyConnected_of_geometricallyIntegral {X Y : Scheme.{0}} (g : X ⟶ Y)
    [GeometricallyIntegral g] : GeometricallyConnected g := by
  refine ⟨fun K _ y Z fst snd h => ?_⟩
  have : IsIntegral Z := GeometricallyIntegral.geometrically_isIntegral y fst snd h
  infer_instance

/-- `A` has good reduction at `O` if an abelian scheme over a ring `R` mapping to `O` (compatibly
with the maps to `K`) has generic fibre `≅ A`: base change along `Spec O → Spec R`. -/
theorem hasGoodReduction_of_base {K : Type} [Field K] (O : ValuationSubring K) {R : Type}
    [CommRing R] (ιR : R →+* K) (φ : R →+* O) (hφ : (algebraMap O K).comp φ = ιR)
    (A : Grp (Over (Spec (.of K)))) (𝒜 : Grp (Over (Spec (.of R))))
    (h𝒜 : PkgI2.IsAbelianScheme 𝒜)
    (e : (Over.pullback (Spec.map (CommRingCat.ofHom ιR))).mapGrp.obj 𝒜 ≅ A) :
    PkgI2.HasGoodReduction A O := by
  let g := Spec.map (CommRingCat.ofHom φ)
  refine ⟨(Over.pullback g).mapGrp.obj 𝒜, ?_, ?_⟩
  · have := h𝒜.proper; have := h𝒜.smooth; have := h𝒜.geomConnected
    refine ⟨?_, ?_, ?_⟩
    · show IsProper (Limits.pullback.snd 𝒜.X.hom g); infer_instance
    · show Smooth (Limits.pullback.snd 𝒜.X.hom g); infer_instance
    · show GeometricallyConnected (Limits.pullback.snd 𝒜.X.hom g); infer_instance
  · have hcomp : Spec.map (CommRingCat.ofHom (algebraMap O K)) ≫ g =
        Spec.map (CommRingCat.ofHom ιR) := by
      rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, ← hφ]
    exact ⟨(Functor.mapGrpCompIso.app 𝒜).symm ≪≫
      (Functor.mapGrpNatIso (Over.pullbackComp _ _).symm).app 𝒜 ≪≫
      (FrobPiecesGood.pullbackGrp_congr hcomp 𝒜).some ≪≫ e⟩

set_option synthInstance.maxHeartbeats 400000 in
/-- **`GoodRedCofinite` from neron-lg's N1-g1 `AbVarSpreadsOut` and `ProperSmoothGenConnected`
(proved).** Spread `A` out to `G/𝓞_L[1/f]` (presentation `Localization.Away f`); `G` is
geometrically connected by `ProperSmoothGenConnected` (its generic fibre is `≅ A`, geometrically
integral). `S` is the set of prime factors of `N = |N_{L/ℚ}(f)|`: for `p ∉ S` and `w ∣ p`, `N` is a
unit of `O_w` and `N ∈ (f)`, so `f` is a unit of `O_w`, and `𝓞_L[1/f] → L` factors through `O_w`
(`IsLocalization.Away.lift`); conclude by base change (`hasGoodReduction_of_base`). -/
theorem goodRedCofinite_of_neron (hsp : AbVarSpreadsOut) (hc : ProperSmoothGenConnected) :
    AlgFrobRedRed.GoodRedCofinite := by
  intro L _ A
  letI : NumberField L := { to_charZero := inferInstance, to_finiteDimensional := inferInstance }
  obtain ⟨f, hf0, hf⟩ := hsp L A
  have hfL : IsUnit (algebraMap (𝓞 L) L f) :=
    isUnit_iff_ne_zero.2 (by simpa using hf0)
  let R := Localization.Away f
  letI : Algebra R L := (IsLocalization.Away.lift f hfL).toAlgebra
  haveI : IsScalarTower (𝓞 L) R L := IsScalarTower.of_algebraMap_eq (fun x =>
    (IsLocalization.Away.lift_eq f hfL x).symm)
  obtain ⟨G, hG, hGs, hGp, gen, hgen⟩ := hf R
  have hgc : GeometricallyConnected G.hom := by
    refine hc L f R G hGs hGp ?_
    have h1 : GeometricallyConnected A.X.hom := geometricallyConnected_of_geometricallyIntegral _
    have h2 : ((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap R L)))).obj G).hom =
        gen.hom.left ≫ A.X.hom := (Over.w gen.hom).symm
    rw [h2]
    have hR : MorphismProperty.RespectsIso (@GeometricallyConnected : MorphismProperty Scheme.{0}) :=
      MorphismProperty.IsStableUnderBaseChange.respectsIso
    exact (MorphismProperty.cancel_left_of_respectsIso (@GeometricallyConnected : MorphismProperty Scheme.{0})
      gen.hom.left A.X.hom).2 h1
  let N : ℕ := Ideal.absNorm (Ideal.span {f})
  have hN0 : N ≠ 0 := by
    simp only [N, ne_eq, Ideal.absNorm_eq_zero_iff, Ideal.span_singleton_eq_bot]
    exact hf0
  refine ⟨N.primeFactors, fun p hp hpS v hv => ?_⟩
  have hpN : ¬ p ∣ (N : ℤ).natAbs := by
    rw [Int.natAbs_natCast]
    exact fun hd => hpS (Nat.mem_primeFactors.2 ⟨hp, hd, hN0⟩)
  have hNu : IsUnit ((N : ℤ) : AlgFrobRedRed.Ow L v) :=
    FrobPiecesGood.isUnit_intCast_of_coprime (L := L) hp hv hpN
  have hfu : IsUnit (AlgFrobRedRed.toO' (AlgFrobRedRed.Ow L v) f) := by
    by_contra hnu
    have hfm : AlgFrobRedRed.toO' (AlgFrobRedRed.Ow L v) f ∈
        IsLocalRing.maximalIdeal (AlgFrobRedRed.Ow L v) := (IsLocalRing.mem_maximalIdeal _).2 hnu
    obtain ⟨c, hc'⟩ := Ideal.mem_span_singleton'.1 (Ideal.absNorm_mem (Ideal.span {f}))
    have : ((N : ℤ) : AlgFrobRedRed.Ow L v) ∈ IsLocalRing.maximalIdeal (AlgFrobRedRed.Ow L v) := by
      have := congrArg (AlgFrobRedRed.toO' (AlgFrobRedRed.Ow L v)) hc'
      rw [map_mul, map_natCast] at this
      rw [Int.cast_natCast, ← this]
      exact Ideal.mul_mem_left _ _ hfm
    exact (IsLocalRing.mem_maximalIdeal _).1 this hNu
  let φ : R →+* AlgFrobRedRed.Ow L v := IsLocalization.Away.lift f hfu
  have hφ : (algebraMap (AlgFrobRedRed.Ow L v) L).comp φ = algebraMap R L := by
    refine IsLocalization.ringHom_ext (Submonoid.powers f) (RingHom.ext fun x => ?_)
    simp only [RingHom.comp_apply, φ, IsLocalization.Away.lift_eq]
    exact (IsLocalization.Away.lift_eq f hfL x).symm
  letI : GrpObj ((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap R L)))).obj G) :=
    Functor.grpObjObj
  exact hasGoodReduction_of_base _ (algebraMap R L) φ hφ _ (Grp.mk G) ⟨hGp, hGs, hgc⟩
    (Grp.mkIso' gen)

end FrobPiecesNeron

end
