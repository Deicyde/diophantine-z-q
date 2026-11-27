import Mathlib

/-!
# Source descent of smoothness (of relative dimension `n`) along finite etale surjections

Setting: `f : X ⟶ Y` finite, etale and surjective, `q : Y ⟶ Z`, `Z` locally noetherian, and
`f ≫ q` smooth of relative dimension `n`. We want `q` smooth of relative dimension `n`.

What is proved here, with no extra hypothesis:

* `smoothOfRelativeDimension_of_comp_finite_etale`: if `q` is already known to be smooth, then
  `q` is smooth of relative dimension `n`. (The relative dimension step.)
* All of the smoothness step except one ring-theoretic input: finite presentation (Artin-Tate
  plus noetherianity), projectivity of `Ω[S/R]` (etale base change of differentials, flat descent
  along a faithfully flat map, flat plus finitely presented gives projective).

What is not proved: the vanishing of `H1Cotangent R S`. Mathlib has `Algebra.H1Cotangent` and its
flat base change along the base ring, and an extension-level etale comparison
`Algebra.Extension.tensorH1CotangentOfFormallyEtale` whose hypotheses are not available for a
general etale `S → T`; it has no algebra-level statement `T ⊗[S] H1(S/R) ≃ H1(T/R)` for etale
`S → T`. That single input is isolated as the named gap `H1CotangentDescentFiniteEtale`, and the
target statement is proved from it: `descentSmoothRelDimFiniteEtale_of_h1`.

Proof outline.
* Ring level, smoothness. For `R → S → T` with `R` noetherian, `S → T` finite, etale and
  faithfully flat, and `R → T` smooth:
  - `S` is of finite type over `R` by Artin-Tate (`fg_of_fg_of_fg`), hence finitely presented;
  - `T ⊗[S] Ω[S/R] ≃ Ω[T/R]` (`KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale`) is
    projective, hence flat, so `Ω[S/R]` is flat (`Module.Flat.of_flat_tensorProduct`), and it
    is finitely presented, hence projective (`Module.Flat.projective_of_finitePresentation`);
  - `H1Cotangent R S` is trivial by the gap;
  - `Algebra.formallySmooth_iff` assembles formal smoothness.
* Ring level, relative dimension. For `R → A` standard smooth, `A → B` formally etale with `B`
  nontrivial and `R → B` locally standard smooth of relative dimension `n`: pick `t` in the
  covering family with `B_t` nontrivial (`t` outside a maximal ideal); then
  `rank_A Ω[A/R] = rank_B Ω[B/R] = rank_{B_t} Ω[B_t/R] = n` by etale base change of
  differentials and `Module.rank_baseChange`, and
  `Algebra.IsStandardSmoothOfRelativeDimension.iff_of_isStandardSmooth` concludes.
* Scheme level. As for local finite type: `HasRingHomProperty.iff_appLE` for smoothness, and
  `smoothOfRelativeDimension_iff` together with `Smooth.exists_isStandardSmooth` for the relative
  dimension; in both cases the ring maps are `Γ(Z, U) ⟶ Γ(Y, V) ⟶ Γ(X, f ⁻¹ᵁ V)`.
-/

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry Limits

namespace Y3Buzzard.SourceDescent

/-! ## The named gap -/

/-- **Named gap.** Triviality of the first homology of the naive cotangent complex descends along
a finite, etale, faithfully flat ring map.

Mathematically this follows from `T ⊗[S] H1(L_{S/R}) ≃ H1(L_{T/R})` for etale `S → T` (the
cotangent complex of an etale map vanishes, and `S → T` is flat) and faithful flatness. Closest
printed references: Stacks, Section 10.134 (Tag 00S0, naive cotangent complex and the
Jacobi-Zariski sequence, Tag 00S2) for the comparison map, and Stacks Tag 036U (smoothness is
local on the source in the smooth topology) for the scheme-level statement it serves. Mathlib
has the flat base change version `Algebra.tensorH1CotangentOfFlat` (change of base ring), the
localization version `Algebra.tensorH1CotangentOfIsLocalization`, and the extension-level
`Algebra.Extension.tensorH1CotangentOfFormallyEtale` (which needs `J ≃ Q ⊗ I`), but not this. -/
def H1CotangentDescentFiniteEtale : Prop :=
  ∀ (R S T : Type) [CommRing R] [CommRing S] [CommRing T] [Algebra R S] [Algebra R T]
    [Algebra S T] [IsScalarTower R S T],
    Algebra.Etale S T → Module.Finite S T → Module.FaithfullyFlat S T →
      Subsingleton (Algebra.H1Cotangent R T) → Subsingleton (Algebra.H1Cotangent R S)

/-! ## Ring level: finite presentation and projectivity of differentials -/

/-- Projectivity of `Ω[S/R]` descends along a formally etale, faithfully flat `S → T`, provided
`S` is finitely presented over `R`. -/
theorem projective_kaehlerDifferential_of_formallyEtale_faithfullyFlat
    {R S T : Type} [CommRing R] [CommRing S] [CommRing T] [Algebra R S] [Algebra R T]
    [Algebra S T] [IsScalarTower R S T] [Algebra.FinitePresentation R S]
    [Algebra.FormallyEtale S T] [Module.FaithfullyFlat S T]
    [Module.Projective T (KaehlerDifferential R T)] :
    Module.Projective S (KaehlerDifferential R S) := by
  haveI : Module.Flat T (KaehlerDifferential R T) := Module.Flat.of_projective
  haveI : Module.Flat T (TensorProduct S T (KaehlerDifferential R S)) :=
    Module.Flat.of_linearEquiv (KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale R S T)
  haveI : Module.Flat S (KaehlerDifferential R S) :=
    Module.Flat.of_flat_tensorProduct S (KaehlerDifferential R S) T
  exact Module.Flat.projective_of_finitePresentation

/-- Ring-level smooth descent along a finite, etale, faithfully flat map, over a noetherian base,
assuming the named gap. -/
theorem algebra_smooth_of_comp_finite_etale (hH1 : H1CotangentDescentFiniteEtale)
    {R S T : Type} [CommRing R] [CommRing S] [CommRing T] [Algebra R S] [Algebra R T]
    [Algebra S T] [IsScalarTower R S T] [IsNoetherianRing R] [Algebra.Smooth R T]
    [Algebra.Etale S T] [Module.Finite S T] [Module.FaithfullyFlat S T]
    (hinj : Function.Injective (algebraMap S T)) : Algebra.Smooth R S := by
  -- finite presentation: Artin-Tate, then noetherianity of `R`
  have hT : Algebra.FiniteType R T := inferInstance
  have hBC : Module.Finite S T := inferInstance
  have hfg : (⊤ : Subalgebra R S).FG :=
    fg_of_fg_of_fg R S T hT.out (Module.finite_def.mp hBC) hinj
  haveI hft : Algebra.FiniteType R S := ⟨hfg⟩
  haveI hfp : Algebra.FinitePresentation R S := Algebra.FinitePresentation.of_finiteType.mp hft
  -- the two halves of formal smoothness of `T`
  have hsmT : Algebra.FormallySmooth R T := inferInstance
  obtain ⟨hprojT, hsubT⟩ := (Algebra.formallySmooth_iff R T).mp hsmT
  haveI : Module.Projective T (KaehlerDifferential R T) := hprojT
  have hproj : Module.Projective S (KaehlerDifferential R S) :=
    projective_kaehlerDifferential_of_formallyEtale_faithfullyFlat (T := T)
  have hEt : Algebra.Etale S T := inferInstance
  have hFF : Module.FaithfullyFlat S T := inferInstance
  have hsub : Subsingleton (Algebra.H1Cotangent R S) := hH1 R S T hEt hBC hFF hsubT
  have hfs : Algebra.FormallySmooth R S := (Algebra.formallySmooth_iff R S).mpr ⟨hproj, hsub⟩
  exact Algebra.Smooth.mk hfs hfp

/-- Ring-hom form of `algebra_smooth_of_comp_finite_etale`. -/
theorem ringHom_smooth_of_comp_finite_etale (hH1 : H1CotangentDescentFiniteEtale)
    {R S T : Type} [CommRing R] [CommRing S] [CommRing T] [IsNoetherianRing R]
    (φ : R →+* S) (ψ : S →+* T) (hc : (ψ.comp φ).Smooth) (hfin : ψ.Finite)
    (hff : ψ.FaithfullyFlat) (het : ψ.Etale) : φ.Smooth := by
  letI : Algebra R S := φ.toAlgebra
  letI : Algebra S T := ψ.toAlgebra
  letI : Algebra R T := (ψ.comp φ).toAlgebra
  haveI : IsScalarTower R S T := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  haveI : Algebra.Smooth R T := RingHom.Smooth.toAlgebra hc
  haveI : Algebra.Etale S T := RingHom.Etale.toAlgebra het
  haveI : Module.Finite S T := hfin
  haveI : Module.FaithfullyFlat S T := RingHom.faithfullyFlat_algebraMap_iff.mp hff
  have hS : Algebra.Smooth R S := algebra_smooth_of_comp_finite_etale hH1 hff.injective
  exact RingHom.smooth_algebraMap.mpr hS

/-! ## Ring level: relative dimension -/

/-- If `R → A` is standard smooth, `A → B` is formally etale with `B` nontrivial, and `R → B` is
locally standard smooth of relative dimension `n`, then `R → A` is standard smooth of relative
dimension `n`. -/
theorem algebra_isStandardSmoothOfRelativeDimension_of_etale (n : ℕ)
    {R A B : Type} [CommRing R] [CommRing A] [CommRing B] [Algebra R A] [Algebra A B]
    [Algebra R B] [IsScalarTower R A B] [Nontrivial B] [Algebra.IsStandardSmooth R A]
    [Algebra.FormallyEtale A B]
    (hB : RingHom.Locally (RingHom.IsStandardSmoothOfRelativeDimension n) (algebraMap R B)) :
    Algebra.IsStandardSmoothOfRelativeDimension n R A := by
  haveI : Nontrivial A := (algebraMap A B).domain_nontrivial
  haveI : Module.Free A (KaehlerDifferential R A) :=
    Algebra.IsStandardSmooth.free_kaehlerDifferential
  -- `Ω[B/R] ≃ B ⊗[A] Ω[A/R]`, so `Ω[B/R]` is free of the same rank as `Ω[A/R]`
  let e₁ : TensorProduct A B (KaehlerDifferential R A) ≃ₗ[B] KaehlerDifferential R B :=
    KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale R A B
  haveI : Module.Free B (TensorProduct A B (KaehlerDifferential R A)) :=
    Algebra.TensorProduct.instFree A B (KaehlerDifferential R A)
  haveI : Module.Free B (KaehlerDifferential R B) := Module.Free.of_equiv e₁
  have hA1 : Module.rank B (TensorProduct A B (KaehlerDifferential R A)) =
      Module.rank A (KaehlerDifferential R A) :=
    (Module.rank_baseChange (R := B) (S := A) (M' := KaehlerDifferential R A)).trans
      (Cardinal.lift_id _)
  have hA2 : Module.rank B (TensorProduct A B (KaehlerDifferential R A)) =
      Module.rank B (KaehlerDifferential R B) :=
    e₁.rank_eq
  -- a localization `B_t` from the covering family that is nontrivial
  obtain ⟨s, hs, hst⟩ := (RingHom.locally_iff_finite _ _).mp hB
  obtain ⟨m, hm⟩ := Ideal.exists_maximal B
  have hex : ∃ t ∈ s, t ∉ m := by
    by_contra hcon
    push_neg at hcon
    have hle : Ideal.span (s : Set B) ≤ m := Ideal.span_le.mpr (fun t ht => hcon t ht)
    have htop : (⊤ : Ideal B) ≤ m := by
      rw [← hs]
      exact hle
    exact hm.ne_top (top_le_iff.mp htop)
  obtain ⟨t, hts, htm⟩ := hex
  haveI : m.IsPrime := hm.isPrime
  haveI : Nontrivial (Localization.Away t) := by
    have hu : IsUnit (algebraMap B (Localization.AtPrime m) t) :=
      IsLocalization.map_units (Localization.AtPrime m) (⟨t, htm⟩ : m.primeCompl)
    exact (Localization.awayLift (algebraMap B (Localization.AtPrime m)) t hu).domain_nontrivial
  have hP := hst t hts
  haveI : Algebra.IsStandardSmoothOfRelativeDimension n R (Localization.Away t) :=
    (RingHom.isStandardSmoothOfRelativeDimension_algebraMap n).mp
      (by rw [IsScalarTower.algebraMap_eq R B (Localization.Away t)]; exact hP)
  haveI : Algebra.FormallyEtale B (Localization.Away t) :=
    Algebra.FormallyEtale.of_isLocalization (Submonoid.powers t)
  have hn : Module.rank (Localization.Away t) (KaehlerDifferential R (Localization.Away t)) =
      n :=
    Algebra.IsStandardSmoothOfRelativeDimension.rank_kaehlerDifferential n
  let e₂ : TensorProduct B (Localization.Away t) (KaehlerDifferential R B) ≃ₗ[Localization.Away t]
      KaehlerDifferential R (Localization.Away t) :=
    KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale R B (Localization.Away t)
  have hB1 : Module.rank (Localization.Away t)
        (TensorProduct B (Localization.Away t) (KaehlerDifferential R B)) =
      Module.rank B (KaehlerDifferential R B) :=
    (Module.rank_baseChange (R := Localization.Away t) (S := B)
      (M' := KaehlerDifferential R B)).trans (Cardinal.lift_id _)
  have hB2 : Module.rank (Localization.Away t)
        (TensorProduct B (Localization.Away t) (KaehlerDifferential R B)) =
      Module.rank (Localization.Away t) (KaehlerDifferential R (Localization.Away t)) :=
    e₂.rank_eq
  have hrk : Module.rank A (KaehlerDifferential R A) = n :=
    hA1.symm.trans (hA2.trans (hB1.symm.trans (hB2.trans hn)))
  exact (Algebra.IsStandardSmoothOfRelativeDimension.iff_of_isStandardSmooth n).mpr hrk

/-- Ring-hom form of `algebra_isStandardSmoothOfRelativeDimension_of_etale`. -/
theorem ringHom_isStandardSmoothOfRelativeDimension_of_etale (n : ℕ)
    {R A B : Type} [CommRing R] [CommRing A] [CommRing B] [Nontrivial B]
    (φ : R →+* A) (ψ : A →+* B) (hφ : φ.IsStandardSmooth) (hψ : ψ.Etale)
    (hc : RingHom.Locally (RingHom.IsStandardSmoothOfRelativeDimension n) (ψ.comp φ)) :
    RingHom.IsStandardSmoothOfRelativeDimension n φ := by
  letI : Algebra R A := φ.toAlgebra
  letI : Algebra A B := ψ.toAlgebra
  letI : Algebra R B := (ψ.comp φ).toAlgebra
  haveI : IsScalarTower R A B := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  haveI : Algebra.IsStandardSmooth R A := RingHom.IsStandardSmooth.toAlgebra hφ
  haveI : Algebra.Etale A B := RingHom.Etale.toAlgebra hψ
  have h : Algebra.IsStandardSmoothOfRelativeDimension n R A :=
    algebra_isStandardSmoothOfRelativeDimension_of_etale n hc
  exact (RingHom.isStandardSmoothOfRelativeDimension_algebraMap n).mpr h

/-! ## Faithful flatness of `Γ(Y, V) ⟶ Γ(X, f ⁻¹ᵁ V)` -/

/-- For `f` flat and surjective and `V` an affine open of `Y` with affine preimage, the ring
map `Γ(Y, V) ⟶ Γ(X, f ⁻¹ᵁ V)` is faithfully flat. -/
theorem faithfullyFlat_appLE_preimage_of_flat_surj {X Y : Scheme.{0}} (f : X ⟶ Y)
    (hf : AlgebraicGeometry.Flat f) (hfs : AlgebraicGeometry.Surjective f)
    {V : Y.Opens} (hV : IsAffineOpen V) (hW : IsAffineOpen (f ⁻¹ᵁ V)) :
    (f.appLE V (f ⁻¹ᵁ V) le_rfl).hom.FaithfullyFlat := by
  have hflat : (f.appLE V (f ⁻¹ᵁ V) le_rfl).hom.Flat :=
    HasRingHomProperty.appLE (P := @AlgebraicGeometry.Flat) f hf ⟨V, hV⟩ ⟨f ⁻¹ᵁ V, hW⟩ le_rfl
  have hsq : Spec.map (f.appLE V (f ⁻¹ᵁ V) le_rfl) ≫ hV.fromSpec = hW.fromSpec ≫ f :=
    IsAffineOpen.SpecMap_appLE_fromSpec f hV hW le_rfl
  have hsurj : Function.Surjective (Spec.map (f.appLE V (f ⁻¹ᵁ V) le_rfl)) := by
    intro p
    obtain ⟨x, hx⟩ := hfs.1 (hV.fromSpec p)
    have h1 : hV.fromSpec p ∈ (V : Set Y) :=
      (Set.ext_iff.mp hV.range_fromSpec _).mp ⟨p, rfl⟩
    have hxW : x ∈ ((f ⁻¹ᵁ V : X.Opens) : Set X) :=
      Eq.subst (motive := fun y => y ∈ (V : Set Y)) hx.symm h1
    obtain ⟨p', hp'⟩ := (Set.ext_iff.mp hW.range_fromSpec x).mpr hxW
    refine ⟨p', hV.fromSpec.isOpenEmbedding.toIsEmbedding.injective ?_⟩
    exact (Scheme.Hom.comp_apply (Spec.map (f.appLE V (f ⁻¹ᵁ V) le_rfl)) hV.fromSpec
      p').symm.trans
      ((congrArg (fun g : Spec Γ(X, f ⁻¹ᵁ V) ⟶ Y => g p') hsq).trans
        ((Scheme.Hom.comp_apply hW.fromSpec f p').trans
          ((congrArg (fun y => f y) hp').trans hx)))
  have hflatSpec : AlgebraicGeometry.Flat (Spec.map (f.appLE V (f ⁻¹ᵁ V) le_rfl)) :=
    (HasRingHomProperty.Spec_iff (P := @AlgebraicGeometry.Flat)).mpr hflat
  exact (flat_and_surjective_SpecMap_iff (f.appLE V (f ⁻¹ᵁ V) le_rfl)).mp
    ⟨hflatSpec, ⟨hsurj⟩⟩

/-! ## Scheme level: smoothness -/

/-- Source descent of smoothness along a finite, etale, surjective morphism, over a locally
noetherian base, assuming the named gap. -/
theorem smooth_of_comp_finite_etale (hH1 : H1CotangentDescentFiniteEtale)
    {X Y Z : Scheme.{0}} (f : X ⟶ Y) (q : Y ⟶ Z) [IsLocallyNoetherian Z]
    (hfin : AlgebraicGeometry.IsFinite f) (het : AlgebraicGeometry.Etale f)
    (hsurj : AlgebraicGeometry.Surjective f) (hfq : AlgebraicGeometry.Smooth (f ≫ q)) :
    AlgebraicGeometry.Smooth q := by
  haveI : AlgebraicGeometry.IsFinite f := hfin
  have hflat : AlgebraicGeometry.Flat f :=
    (AlgebraicGeometry.Etale.iff_flat_and_formallyUnramified.mp het).1
  refine (HasRingHomProperty.iff_appLE (P := @AlgebraicGeometry.Smooth)).mpr ?_
  rintro ⟨U, hU⟩ ⟨V, hV⟩ e
  have hU' : IsAffineOpen U := hU
  have hV' : IsAffineOpen V := hV
  have hW : IsAffineOpen (f ⁻¹ᵁ V) := IsAffineOpen.preimage hV' f
  haveI : IsNoetherianRing Γ(Z, U) := IsLocallyNoetherian.component_noetherian ⟨U, hU'⟩
  -- the inclusion `f ⁻¹ᵁ V ≤ (f ≫ q) ⁻¹ᵁ U`, as the image of `e` under pulling back along `f`
  have e' : f ⁻¹ᵁ V ≤ (f ≫ q) ⁻¹ᵁ U :=
    CategoryTheory.leOfHom ((TopologicalSpace.Opens.map f.base).map (CategoryTheory.homOfLE e))
  have hcomp := Scheme.Hom.appLE_comp_appLE f q U V (f ⁻¹ᵁ V) e le_rfl
  have h1 : RingHom.Smooth (q.appLE U V e ≫ f.appLE V (f ⁻¹ᵁ V) le_rfl).hom :=
    (congrArg (fun g : Γ(Z, U) ⟶ Γ(X, f ⁻¹ᵁ V) => RingHom.Smooth g.hom) hcomp).mpr
      (HasRingHomProperty.appLE (P := @AlgebraicGeometry.Smooth) (f ≫ q) hfq ⟨U, hU'⟩
        ⟨f ⁻¹ᵁ V, hW⟩ e')
  have h2 : (f.appLE V (f ⁻¹ᵁ V) le_rfl).hom.Finite :=
    (congrArg (fun g : Γ(Y, V) ⟶ Γ(X, f ⁻¹ᵁ V) => g.hom.Finite)
      (Scheme.Hom.app_eq_appLE f (U := V))).mp (IsFinite.finite_app f V hV')
  have h3 : (f.appLE V (f ⁻¹ᵁ V) le_rfl).hom.FaithfullyFlat :=
    faithfullyFlat_appLE_preimage_of_flat_surj f hflat hsurj hV' hW
  have h4 : (f.appLE V (f ⁻¹ᵁ V) le_rfl).hom.Etale :=
    HasRingHomProperty.appLE (P := @AlgebraicGeometry.Etale) f het ⟨V, hV'⟩ ⟨f ⁻¹ᵁ V, hW⟩
      le_rfl
  exact ringHom_smooth_of_comp_finite_etale hH1 (q.appLE U V e).hom
    (f.appLE V (f ⁻¹ᵁ V) le_rfl).hom h1 h2 h3 h4

/-! ## Scheme level: relative dimension -/

/-- If `f` is finite, etale and surjective, `q` is smooth and `f ≫ q` is smooth of relative
dimension `n`, then `q` is smooth of relative dimension `n`. No noetherian hypothesis and no
gap. -/
theorem smoothOfRelativeDimension_of_comp_finite_etale (n : ℕ) {X Y Z : Scheme.{0}}
    (f : X ⟶ Y) (q : Y ⟶ Z) (hfin : AlgebraicGeometry.IsFinite f)
    (het : AlgebraicGeometry.Etale f) (hsurj : AlgebraicGeometry.Surjective f)
    (hsm : AlgebraicGeometry.Smooth q)
    (hfq : AlgebraicGeometry.SmoothOfRelativeDimension n (f ≫ q)) :
    AlgebraicGeometry.SmoothOfRelativeDimension n q := by
  haveI : AlgebraicGeometry.Smooth q := hsm
  haveI : AlgebraicGeometry.IsFinite f := hfin
  refine (AlgebraicGeometry.smoothOfRelativeDimension_iff n q).mpr ?_
  intro y
  obtain ⟨U, hU, V, hV, hyV, e, hst⟩ := AlgebraicGeometry.Smooth.exists_isStandardSmooth q y
  refine ⟨U, hU, V, hV, hyV, e, ?_⟩
  have hW : IsAffineOpen (f ⁻¹ᵁ V) := IsAffineOpen.preimage hV f
  have e' : f ⁻¹ᵁ V ≤ (f ≫ q) ⁻¹ᵁ U :=
    CategoryTheory.leOfHom ((TopologicalSpace.Opens.map f.base).map (CategoryTheory.homOfLE e))
  have hcomp := Scheme.Hom.appLE_comp_appLE f q U V (f ⁻¹ᵁ V) e le_rfl
  have h1 : RingHom.Locally (RingHom.IsStandardSmoothOfRelativeDimension n)
      (q.appLE U V e ≫ f.appLE V (f ⁻¹ᵁ V) le_rfl).hom :=
    (congrArg (fun g : Γ(Z, U) ⟶ Γ(X, f ⁻¹ᵁ V) =>
        RingHom.Locally (RingHom.IsStandardSmoothOfRelativeDimension n) g.hom) hcomp).mpr
      (HasRingHomProperty.appLE (P := @AlgebraicGeometry.SmoothOfRelativeDimension n) (f ≫ q)
        hfq ⟨U, hU⟩ ⟨f ⁻¹ᵁ V, hW⟩ e')
  have h4 : (f.appLE V (f ⁻¹ᵁ V) le_rfl).hom.Etale :=
    HasRingHomProperty.appLE (P := @AlgebraicGeometry.Etale) f het ⟨V, hV⟩ ⟨f ⁻¹ᵁ V, hW⟩
      le_rfl
  -- `Γ(X, f ⁻¹ᵁ V)` is nontrivial: a point of `X` over `y` lies in `f ⁻¹ᵁ V`
  obtain ⟨x, hx⟩ := hsurj.1 y
  have hxW : x ∈ ((f ⁻¹ᵁ V : X.Opens) : Set X) :=
    Eq.subst (motive := fun z => z ∈ (V : Set Y)) hx.symm hyV
  haveI : Nontrivial Γ(X, f ⁻¹ᵁ V) :=
    PrimeSpectrum.nonempty_iff_nontrivial.mp ⟨hW.primeIdealOf ⟨x, hxW⟩⟩
  exact ringHom_isStandardSmoothOfRelativeDimension_of_etale n (q.appLE U V e).hom
    (f.appLE V (f ⁻¹ᵁ V) le_rfl).hom hst h4 h1

/-! ## The target statements -/

/-- Smoothness descends along finite etale surjections of the source, over a locally noetherian
base. -/
def DescentSmoothFiniteEtale : Prop :=
  ∀ (X Y Z : Scheme.{0}) (f : X ⟶ Y) (q : Y ⟶ Z), IsLocallyNoetherian Z →
    AlgebraicGeometry.IsFinite f → AlgebraicGeometry.Etale f → AlgebraicGeometry.Surjective f →
      AlgebraicGeometry.Smooth (f ≫ q) → AlgebraicGeometry.Smooth q

/-- Smoothness of relative dimension `n` descends along finite etale surjections of the source,
over a locally noetherian base. -/
def DescentSmoothRelDimFiniteEtale : Prop :=
  ∀ (n : ℕ) (X Y Z : Scheme.{0}) (f : X ⟶ Y) (q : Y ⟶ Z), IsLocallyNoetherian Z →
    AlgebraicGeometry.IsFinite f → AlgebraicGeometry.Etale f → AlgebraicGeometry.Surjective f →
      AlgebraicGeometry.SmoothOfRelativeDimension n (f ≫ q) →
        AlgebraicGeometry.SmoothOfRelativeDimension n q

theorem descentSmoothFiniteEtale_of_h1 (hH1 : H1CotangentDescentFiniteEtale) :
    DescentSmoothFiniteEtale := by
  intro X Y Z f q hZ hfin het hsurj hfq
  haveI : IsLocallyNoetherian Z := hZ
  exact smooth_of_comp_finite_etale hH1 f q hfin het hsurj hfq

/-- The target statement, from the single named gap `H1CotangentDescentFiniteEtale`. -/
theorem descentSmoothRelDimFiniteEtale_of_h1 (hH1 : H1CotangentDescentFiniteEtale) :
    DescentSmoothRelDimFiniteEtale := by
  intro n X Y Z f q hZ hfin het hsurj hfq
  haveI : IsLocallyNoetherian Z := hZ
  have hsm' : AlgebraicGeometry.Smooth (f ≫ q) := by
    haveI : AlgebraicGeometry.SmoothOfRelativeDimension n (f ≫ q) := hfq
    exact AlgebraicGeometry.SmoothOfRelativeDimension.smooth n (f ≫ q)
  have hsq : AlgebraicGeometry.Smooth q :=
    smooth_of_comp_finite_etale hH1 f q hfin het hsurj hsm'
  exact smoothOfRelativeDimension_of_comp_finite_etale n f q hfin het hsurj hsq hfq

/-- The relative dimension step on its own, in the shape of the target statement: once `q` is
known to be smooth, nothing else is needed. -/
theorem descentSmoothRelDimFiniteEtale_of_smooth :
    ∀ (n : ℕ) (X Y Z : Scheme.{0}) (f : X ⟶ Y) (q : Y ⟶ Z),
      AlgebraicGeometry.IsFinite f → AlgebraicGeometry.Etale f →
        AlgebraicGeometry.Surjective f → AlgebraicGeometry.Smooth q →
          AlgebraicGeometry.SmoothOfRelativeDimension n (f ≫ q) →
            AlgebraicGeometry.SmoothOfRelativeDimension n q := by
  intro n X Y Z f q hfin het hsurj hsm hfq
  exact smoothOfRelativeDimension_of_comp_finite_etale n f q hfin het hsurj hsm hfq

end Y3Buzzard.SourceDescent

end
