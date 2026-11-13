import ZInQKernel.HDecomp.Faltings.Models

namespace ZInQ.DefFaltings.HodgeLattice
open NumberField CategoryTheory AlgebraicGeometry Limits MonoidalCategory MonObj
open PkgI3 (AbVar)

variable {K : Type} [Field K] {A : AbVar K} {L : Type} [Field L] [NumberField L] [Algebra K L]
variable (𝒢 : GroupModel A L)

local notation "S" => Spec (CommRingCat.of (𝓞 L))

theorem unitSection_comp : 𝒢.unitSection ≫ 𝒢.G.hom = 𝟙 _ := by
  unfold GroupModel.unitSection
  rw [Over.w]
  rfl

/-- `ε(π^* c) = c`, at the level of stalks. -/
theorem stalkMap_structGerm (s : S) (c : 𝓞 L) :
    𝒢.unitSection.stalkMap s (𝒢.G.left.presheaf.germ ⊤ (𝒢.unitSection s) (TopologicalSpace.Opens.mem_top _)
      (𝒢.G.hom.appTop ((Scheme.ΓSpecIso (CommRingCat.of (𝓞 L))).inv c))) =
    (S).presheaf.germ ⊤ s (TopologicalSpace.Opens.mem_top _) ((Scheme.ΓSpecIso (CommRingCat.of (𝓞 L))).inv c) := by
  rw [Scheme.Hom.germ_stalkMap_apply]
  have h : 𝒢.unitSection.appTop (𝒢.G.hom.appTop
      ((Scheme.ΓSpecIso (CommRingCat.of (𝓞 L))).inv c)) =
      (Scheme.ΓSpecIso (CommRingCat.of (𝓞 L))).inv c := by
    have h1 : (Scheme.Hom.appTop (𝒢.unitSection ≫ 𝒢.G.hom)).hom
        ((Scheme.ΓSpecIso (CommRingCat.of (𝓞 L))).inv c) =
        (Scheme.Hom.appTop (𝟙 (S))).hom ((Scheme.ΓSpecIso (CommRingCat.of (𝓞 L))).inv c) := by
      rw [unitSection_comp]
    rw [Scheme.Hom.comp_appTop, Scheme.Hom.id_appTop] at h1
    exact h1
  exact congrArg _ h

theorem structMap_eq (c : 𝓞 L) : 𝒢.structMap c = 𝒢.G.left.presheaf.germ ⊤ 𝒢.genericUnit
      (TopologicalSpace.Opens.mem_top _)
      (𝒢.G.hom.appTop ((Scheme.ΓSpecIso (CommRingCat.of (𝓞 L))).inv c)) := rfl

theorem isUnit_germ_iff (s : S) (t : 𝓞 L) :
    IsUnit ((S).presheaf.germ ⊤ s (TopologicalSpace.Opens.mem_top _) ((Scheme.ΓSpecIso (CommRingCat.of (𝓞 L))).inv t)) ↔
      t ∉ (s : PrimeSpectrum (𝓞 L)).asIdeal := by
  rw [← Scheme.mem_basicOpen _ _ _ (TopologicalSpace.Opens.mem_top _),
    AlgebraicGeometry.basicOpen_eq_of_affine]
  rfl

omit [NumberField L] in
/-- On an affine open, every element of a stalk is a fraction of sections. -/
theorem exists_germ_frac {X : Scheme} {U : X.Opens} (hU : IsAffineOpen U) (x : X) (hx : x ∈ U)
    (f : X.presheaf.stalk x) : ∃ b u : Γ(X, U), IsUnit (X.presheaf.germ U x hx u) ∧
      f * X.presheaf.germ U x hx u = X.presheaf.germ U x hx b := by
  let := X.presheaf.algebra_section_stalk ⟨x, hx⟩
  have hl := hU.isLocalization_stalk ⟨x, hx⟩
  obtain ⟨⟨b, u⟩, h⟩ := IsLocalization.surj (hU.primeIdealOf ⟨x, hx⟩).asIdeal.primeCompl f
  exact ⟨b, u, IsLocalization.map_units _ u, h⟩

/-- The specialization `𝒪_{𝒢,e(s')} → 𝒪_{𝒢,ξ}`. -/
noncomputable abbrev spec (s' : S) : 𝒢.G.left.presheaf.stalk (𝒢.unitSection s') →+* 𝒢.genStalk :=
  (𝒢.G.left.presheaf.stalkSpecializes (𝒢.specializes_genericUnit s')).hom

theorem genericPt_specializes (s' : S) : genericPt L ⤳ s' :=
  (PrimeSpectrum.le_iff_specializes (genericPt L) s').mp bot_le

/-- **Residue lemma.** Every germ at `e(s')`, specialized to `ξ`, is congruent modulo `𝔪_ξ` to a
fraction `c/t` with `c, t ∈ 𝓞_L`, `t ∉ s'`. -/
theorem residue (s' : S) (w : 𝒢.G.left.presheaf.stalk (𝒢.unitSection s')) :
    ∃ c t : 𝓞 L, t ∉ (s' : PrimeSpectrum (𝓞 L)).asIdeal ∧
      𝒢.structMap t * spec 𝒢 s' w - 𝒢.structMap c ∈ IsLocalRing.maximalIdeal 𝒢.genStalk := by
  set z := 𝒢.unitSection.stalkMap s' w
  obtain ⟨r, u, hu, hru⟩ := exists_germ_frac (isAffineOpen_top (S)) s'
    (TopologicalSpace.Opens.mem_top _) z
  set iso := Scheme.ΓSpecIso (CommRingCat.of (𝓞 L))
  have hr : iso.inv (iso.hom r) = r := iso.hom_inv_id_apply r
  have hu' : iso.inv (iso.hom u) = u := iso.hom_inv_id_apply u
  refine ⟨iso.hom r, iso.hom u, ?_, ?_⟩
  · rw [← isUnit_germ_iff, hu']; exact hu
  by_contra hnot
  have hunit : IsUnit (𝒢.structMap (iso.hom u) * spec 𝒢 s' w - 𝒢.structMap (iso.hom r)) := by
    by_contra h'
    exact hnot ((IsLocalRing.mem_maximalIdeal _).mpr h')
  let φ : 𝒢.genStalk →+* (S).presheaf.stalk (genericPt L) :=
    (𝒢.unitSection.stalkMap (genericPt L)).hom
  have himg := hunit.map φ
  have hη := genericPt_specializes (L := L) s'
  have hspec : φ (spec 𝒢 s' w) =
      (S).presheaf.stalkSpecializes hη z :=
    Scheme.Hom.stalkSpecializes_stalkMap_apply 𝒢.unitSection (genericPt L) s' hη w
  have hst : ∀ c : 𝓞 L, φ (𝒢.structMap c) =
      (S).presheaf.germ ⊤ (genericPt L) (TopologicalSpace.Opens.mem_top _) (iso.inv c) :=
    fun c => stalkMap_structGerm 𝒢 (genericPt L) c
  rw [map_sub, map_mul, hspec, hst, hst, hr, hu'] at himg
  have hz : (S).presheaf.stalkSpecializes hη z *
      (S).presheaf.germ ⊤ (genericPt L) (TopologicalSpace.Opens.mem_top _) u =
      (S).presheaf.germ ⊤ (genericPt L) (TopologicalSpace.Opens.mem_top _) r := by
    have := congrArg ((S).presheaf.stalkSpecializes hη).hom hru
    rw [map_mul, TopCat.Presheaf.germ_stalkSpecializes_apply,
      TopCat.Presheaf.germ_stalkSpecializes_apply] at this
    exact this
  rw [mul_comm, hz, sub_self] at himg
  exact not_isUnit_zero himg

end ZInQ.DefFaltings.HodgeLattice
