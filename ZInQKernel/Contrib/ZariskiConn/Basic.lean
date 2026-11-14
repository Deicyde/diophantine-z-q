import Mathlib.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.Topology.Sheaves.SheafCondition.Sites
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.RingTheory.DedekindDomain.Dvr
import ZInQKernel.Contrib.TauCeti.AlgebraicGeometry.Geometrically.GlobalSections
import ZInQKernel.Contrib.TauCeti.AlgebraicGeometry.Morphisms.Smooth.GeometricallyIntegral

/-!
# zariski-conn: `ProperSmoothGenConnected` from Zariski's connectedness theorem

Task zariski-conn. `ProperSmoothGenConnected` below is a verbatim copy (docstring and `def`) of
the declaration of the same name in `scratch/frob-pieces/part_neron.lean` (namespace
`FrobPiecesNeron`), under the `open`s it needs (checked by `scratch/zariski-conn/py/verbatim_check.py`).

Main result: `ZariskiConn.properSmoothGenConnected_of_zariskiConnectedness :
ZariskiConnectedness.{0} → ProperSmoothGenConnected`, where `ZariskiConnectedness` is Zariski's
connectedness theorem (EGA III₁ 4.3.1 with 4.3.4), stated in its published form: a proper
morphism `f` to a locally noetherian scheme with `𝒪_Y ≅ f_*𝒪_X` has non-empty, geometrically
connected fibres.

The rest is proved here from Mathlib and Tau Ceti. For `R ≅ 𝓞_L[1/f]` and `X/R` smooth and
proper with geometrically connected generic fibre:
* `R` is a Dedekind domain with fraction field `L` (`f ≠ 0`, else `R = 0` has no map to `L`);
* `Γ(X, 𝒪_X)` is integral over `R` (Mathlib, `isIntegral_appTop_of_universallyClosed`);
* `Γ(X, 𝒪_X) → Γ(X_L, 𝒪)` is injective (`Spec L → Spec R` is scheme-theoretically dominant and
  `X → Spec R` is flat; Mathlib, `IsSchemeTheoreticallyDominant.pullbackFst`);
* `L → Γ(X_L, 𝒪)` is bijective (`X_L` is geometrically integral, being smooth and geometrically
  connected, Tau Ceti `Smooth.geometricallyIntegral`, and universally closed; Tau Ceti
  `Scheme.baseRingToGlobalSections_bijective_of_geometricallyIntegral`);
* so every global function is an element of `L` integral over the integrally closed `R`:
  `R → Γ(X, 𝒪_X)` is bijective (`appTop_bijective_of_generic`), with no finiteness of `f_*𝒪_X`
  (EGA III₁ 3.2.1 is not needed);
* `f_*𝒪_X = 𝒪_{Spec R}` follows by the qcqs lemma on basic opens and the basis criterion for
  isomorphisms of sheaves (`app_bijective_of_appTop_bijective`).
-/

noncomputable section

namespace ZariskiConn

open CategoryTheory AlgebraicGeometry Limits Opposite
open NumberField


/-- `Spec K → Spec R` is scheme-theoretically dominant for an injective `R → K`, `R` a domain. -/
theorem isSchemeTheoreticallyDominant_Spec_map {R K : Type} [CommRing R] [IsDomain R]
    [CommRing K] [Algebra R K] (h : Function.Injective (algebraMap R K)) :
    IsSchemeTheoreticallyDominant (Spec.map (CommRingCat.ofHom (algebraMap R K))) := by
  have : IsDominant (Spec.map (CommRingCat.ofHom (algebraMap R K))) := by
    rw [isDominant_iff]
    refine (PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical (f := algebraMap R K)).2 ?_
    rw [(RingHom.injective_iff_ker_eq_bot _).1 h]
    exact bot_le
  exact .of_isDominant _

/-- **Global sections of a flat universally closed scheme over an integrally closed domain.**
Let `R` be an integrally closed domain with fraction field `K` and `p : X ⟶ Spec R` flat and
universally closed, with geometrically integral generic fibre. Then `R → Γ(X, 𝒪_X)` is
bijective. -/
theorem appTop_bijective_of_generic {R K : Type} [CommRing R] [IsDomain R] [IsIntegrallyClosed R]
    [Field K] [Algebra R K] [IsFractionRing R K] {X : Scheme.{0}} (p : X ⟶ Spec (.of R))
    [Flat p] [UniversallyClosed p]
    [GeometricallyIntegral (pullback.snd p (Spec.map (CommRingCat.ofHom (algebraMap R K))))] :
    Function.Bijective ((Scheme.ΓSpecIso (.of R)).inv ≫ p.appTop) := by
  set ι := Spec.map (CommRingCat.ofHom (algebraMap R K))
  have hinj : Function.Injective (algebraMap R K) := IsFractionRing.injective R K
  have := isSchemeTheoreticallyDominant_Spec_map hinj
  let P : Scheme := pullback p ι
  let _ : P.Over (Spec (.of K)) := ⟨pullback.snd p ι⟩
  have : UniversallyClosed (P ↘ Spec (.of K)) := by
    change UniversallyClosed (pullback.snd p ι); infer_instance
  have : GeometricallyIntegral (P ↘ Spec (.of K)) := by
    change GeometricallyIntegral (pullback.snd p ι); infer_instance
  have hK := Scheme.baseRingToGlobalSections_bijective_of_geometricallyIntegral P K
  -- the injection `Γ(X) → Γ(X_K)`
  have hj : Function.Injective (pullback.fst p ι).appTop :=
    (pullback.fst p ι).app_injective ⊤
  set φ := ((Scheme.ΓSpecIso (.of R)).inv ≫ p.appTop).hom with hφ
  set ψ := Scheme.Modules.baseRingToGlobalSections K P with hψ
  set j := (pullback.fst p ι).appTop.hom with hjdef
  have hcomm : ∀ r : R, j (φ r) = ψ (algebraMap R K r) := by
    intro r
    have h1 : (Scheme.ΓSpecIso (.of R)).inv ≫ p.appTop ≫ (pullback.fst p ι).appTop =
        CommRingCat.ofHom (algebraMap R K) ≫ (Scheme.ΓSpecIso (.of K)).inv ≫
          (pullback.snd p ι).appTop := by
      rw [← Scheme.Hom.comp_appTop, pullback.condition, Scheme.Hom.comp_appTop,
        ← Category.assoc, ← Category.assoc, Scheme.ΓSpecIso_inv_naturality]
    exact congrArg (fun g => g.hom r) h1
  have hφint : φ.IsIntegral := by
    rw [hφ, CommRingCat.hom_comp]
    exact RingHom.IsIntegral.trans _ _ (RingHom.isIntegral_of_surjective _
      (Scheme.ΓSpecIso (.of R)).commRingCatIsoToRingEquiv.symm.surjective)
      (isIntegral_appTop_of_universallyClosed p)
  refine ⟨fun a b hab => ?_, fun b => ?_⟩
  · apply hinj; apply hK.1
    rw [← hcomm, ← hcomm, hab]
  · obtain ⟨c, hc⟩ := hK.2 (j b)
    -- `c` is integral over `R`
    obtain ⟨q, hqm, hq⟩ := hφint b
    have hcint : IsIntegral R c := by
      refine ⟨q, hqm, hK.1 ?_⟩
      rw [map_zero, Polynomial.hom_eval₂, hc]
      have : (ψ.comp (algebraMap R K)) = j.comp φ := by ext r; exact (hcomm r).symm
      rw [this, ← Polynomial.hom_eval₂, hq, map_zero]
    obtain ⟨r, hr⟩ := IsIntegrallyClosed.algebraMap_eq_of_integral hcint
    refine ⟨r, hj ?_⟩
    change j (φ r) = j b
    rw [hcomm, hr, hc]


/-- A ring map between localizations `A_a → B_{φ a}` compatible with a bijection `φ : A → B` is
bijective. -/
theorem bijective_of_isLocalization_away {A B S T : Type*} [CommRing A] [CommRing B]
    [CommRing S] [CommRing T] [Algebra A S] [Algebra B T] (φ : A →+* B)
    (hφ : Function.Bijective φ) (a : A) [IsLocalization.Away a S]
    [IsLocalization.Away (φ a) T] (ψ : S →+* T)
    (hψ : ψ.comp (algebraMap A S) = (algebraMap B T).comp φ) : Function.Bijective ψ := by
  let e : A ≃+* B := RingEquiv.ofBijective φ hφ
  have H : (Submonoid.powers a).map e.toMonoidHom = Submonoid.powers (φ a) :=
    Submonoid.map_powers _ _
  let e' : S ≃+* T := IsLocalization.ringEquivOfRingEquiv S T e H
  have : ψ = e'.toRingHom := by
    refine IsLocalization.ringHom_ext (Submonoid.powers a) ?_
    ext x
    rw [hψ]
    simp only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom, e']
    rw [IsLocalization.ringEquivOfRingEquiv_eq]
    rfl
  rw [this]
  exact e'.bijective

/-- The qcqs lemma for an open written as a basic open. -/
theorem isLocalization_of_eq_basicOpen {X : Scheme} [CompactSpace X] [QuasiSeparatedSpace X]
    (s : Γ(X, ⊤)) (V : X.Opens) (hV : X.basicOpen s = V) :
    letI := (X.presheaf.map (homOfLE le_top : V ⟶ ⊤).op).hom.toAlgebra
    IsLocalization.Away s Γ(X, V) := by
  subst hV
  exact isLocalization_basicOpen_of_qcqs isCompact_univ isQuasiSeparated_univ s

/-- `f.app` is bijective on basic opens of an affine target when `f` is qcqs and bijective on
global sections. -/
theorem app_basicOpen_bijective {X Y : Scheme} (f : X ⟶ Y) [IsAffine Y] [QuasiCompact f]
    [QuasiSeparated f] (hf : Function.Bijective f.appTop) (r : Γ(Y, ⊤)) :
    Function.Bijective (f.app (Y.basicOpen r)) := by
  have : CompactSpace X := (quasiCompact_iff_compactSpace f).mp inferInstance
  have : QuasiSeparatedSpace X := (quasiSeparated_iff_quasiSeparatedSpace f).mp inferInstance
  have hS : IsLocalization.Away r Γ(Y, Y.basicOpen r) :=
    (isAffineOpen_top Y).isLocalization_basicOpen r
  let _ : Algebra Γ(X, ⊤) Γ(X, f ⁻¹ᵁ Y.basicOpen r) :=
    (X.presheaf.map (homOfLE le_top : f ⁻¹ᵁ Y.basicOpen r ⟶ ⊤).op).hom.toAlgebra
  have hT : IsLocalization.Away (f.appTop.hom r) Γ(X, f ⁻¹ᵁ Y.basicOpen r) :=
    isLocalization_of_eq_basicOpen _ _ (f.preimage_basicOpen_top r).symm
  refine bijective_of_isLocalization_away f.appTop.hom hf r (f.app (Y.basicOpen r)).hom ?_
  have := f.naturality (homOfLE (le_top : Y.basicOpen r ≤ ⊤)).op
  ext x
  exact congrArg (fun g => g.hom x) this

/-- **`f_*𝒪_X = 𝒪_Y` from global sections.** For `f : X ⟶ Y` qcqs with `Y` affine, if `f` is
bijective on global sections then it is bijective on the sections over every open of `Y`. -/
theorem app_bijective_of_appTop_bijective {X Y : Scheme} (f : X ⟶ Y) [IsAffine Y]
    [QuasiCompact f] [QuasiSeparated f] (hf : Function.Bijective f.appTop) (U : Y.Opens) :
    Function.Bijective (f.app U) := by
  let φ : Y.sheaf ⟶ (TopCat.Sheaf.pushforward CommRingCat f.base).obj X.sheaf := ⟨f.c⟩
  have hφ : IsIso φ := by
    refine TopCat.Sheaf.isIso_iff_isIso_basis (B := Y.basicOpen) (isBasis_basicOpen Y) ?_
    intro r
    exact (ConcreteCategory.isIso_iff_bijective _).2 (app_basicOpen_bijective f hf r)
  have : IsIso ((TopCat.Sheaf.forget CommRingCat Y).map φ) := inferInstance
  have : IsIso (((TopCat.Sheaf.forget CommRingCat Y).map φ).app (op U)) := inferInstance
  exact (ConcreteCategory.isIso_iff_bijective (f.app U)).1 this


universe u

/-- **Zariski's connectedness theorem (LEAF; published: EGA III₁ 4.3.1 with 4.3.4; locators
UNVERIFIED).** Let `Y` be a locally noetherian scheme and `f : X ⟶ Y` a proper morphism with
`f_*𝒪_X = 𝒪_Y`, i.e. the canonical map `𝒪_Y(U) → 𝒪_X(f⁻¹U)` is bijective for every open
`U ⊆ Y`. Then every fibre of `f` is non-empty and geometrically connected (EGA III₁ 4.3.1: the
fibres are connected and non-empty; 4.3.4: geometrically connected). Proved in EGA from the
theorem on formal functions (EGA III₁ 4.1.5) and the coherence of `f_*` (EGA III₁ 3.2.1); see
also Hartshorne III 11.3 for projective `f`. Not in Mathlib v4.35 (no coherent cohomology, no
formal functions). -/
def ZariskiConnectedness : Prop :=
  ∀ ⦃X Y : Scheme.{u}⦄ (f : X ⟶ Y), IsProper f → IsLocallyNoetherian Y →
    (∀ U : Y.Opens, Function.Bijective (f.app U)) → GeometricallyConnected f

set_option synthInstance.maxHeartbeats 400000 in
/-- **`ProperSmoothGenConnected` (LEAF candidate, published: Zariski's connectedness theorem).**
A smooth proper scheme `X` over `R = 𝓞_L[1/f]` (any presentation) whose generic fibre is
geometrically connected is geometrically connected over `R`. Proof (STANDARD): `R ≅ 𝓞_L[1/f]`
is normal with fraction field `L` (the case `f = 0` is vacuous: no ring map from the zero ring to
`L`), and `X_L` is geometrically reduced (smooth) and geometrically connected and proper, so
`H⁰(X_L, 𝒪) = L`; `f_*𝒪_X` is a finite `R`-algebra, torsion-free since `X` is flat (smooth), so
it lies inside `H⁰(X_L, 𝒪) = L` and is integral over the normal `R`, hence
`f_*𝒪_X = 𝒪_{Spec R}`; then all fibres of the proper `f` are geometrically connected (Zariski's
connectedness theorem, EGA III₁ 4.3.1–4.3.4; locators UNVERIFIED). The fibres are nonempty since
`X → Spec R` is open (smooth), closed (proper), `X ≠ ∅` and `Spec R` is connected. Not in Mathlib
v4.35 (no Stein factorization). -/
def ProperSmoothGenConnected : Prop :=
  ∀ (L : Type) [Field L] [NumberField L] (f : 𝓞 L) (R : Type) [CommRing R] [Algebra (𝓞 L) R]
    [IsLocalization.Away f R] [Algebra R L] [IsScalarTower (𝓞 L) R L]
    (X : Over (Spec (CommRingCat.of R))), Smooth X.hom → IsProper X.hom →
    GeometricallyConnected
      ((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap R L)))).obj X).hom →
    GeometricallyConnected X.hom

/-- A presentation `R` of `𝓞_L[1/f]` with a compatible map to `L` is a Dedekind domain with
fraction field `L`. -/
theorem dedekind_fractionRing_of_away (L : Type) [Field L] [NumberField L] (f : 𝓞 L)
    (R : Type) [CommRing R] [Algebra (𝓞 L) R] [IsLocalization.Away f R] [Algebra R L]
    [IsScalarTower (𝓞 L) R L] :
    ∃ (_ : IsDomain R), IsDedekindDomain R ∧ IsFractionRing R L := by
  have hf0 : f ≠ 0 := by
    rintro rfl
    have : Subsingleton R := IsLocalization.subsingleton (M := Submonoid.powers (0 : 𝓞 L))
      (Submonoid.mem_powers 0)
    have h1 : algebraMap R L 1 = algebraMap R L 0 := by rw [Subsingleton.elim (1 : R) 0]
    simp at h1
  have hM := powers_le_nonZeroDivisors_of_noZeroDivisors hf0
  have : IsDomain R := IsLocalization.isDomain_of_le_nonZeroDivisors (S := R) hM
  exact ⟨this, IsLocalization.isDedekindDomain (𝓞 L) hM R,
    IsFractionRing.isFractionRing_of_isDomain_of_isLocalization (Submonoid.powers f) R L⟩

set_option synthInstance.maxHeartbeats 400000 in
/-- **`ProperSmoothGenConnected` from Zariski's connectedness theorem (proved).** -/
theorem properSmoothGenConnected_of_zariskiConnectedness (hZ : ZariskiConnectedness.{0}) :
    ProperSmoothGenConnected := by
  intro L _ _ f R _ _ _ _ _ X hS hP hG
  obtain ⟨_, _, _⟩ := dedekind_fractionRing_of_away L f R
  have : GeometricallyConnected
      (pullback.snd X.hom (Spec.map (CommRingCat.ofHom (algebraMap R L)))) := hG
  have h1 := appTop_bijective_of_generic (K := L) X.hom
  have h2 : Function.Bijective X.hom.appTop := by
    have := (Scheme.ΓSpecIso (.of R)).commRingCatIsoToRingEquiv.symm.bijective
    have h3 : (X.hom.appTop).hom = ((Scheme.ΓSpecIso (.of R)).inv ≫ X.hom.appTop).hom.comp
        (Scheme.ΓSpecIso (.of R)).hom.hom := by
      rw [← CommRingCat.hom_comp, ← Category.assoc, Iso.hom_inv_id, Category.id_comp]
    rw [show (⇑X.hom.appTop : _ → _) = ⇑(X.hom.appTop).hom from rfl, h3, RingHom.coe_comp]
    exact h1.comp (Scheme.ΓSpecIso (.of R)).commRingCatIsoToRingEquiv.bijective
  exact hZ X.hom hP inferInstance (app_bijective_of_appTop_bijective X.hom h2)

end ZariskiConn
