import ZInQKernel.Contrib.CloudW07JacobiansCurves.Jacobian.AlgebraicGeometry.Morphisms.SmoothSourceDescent

universe u

open AlgebraicGeometry CategoryTheory Limits

namespace ZInQ.Contrib.SmoothRegular

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Over a perfect field, a point with regular local ring is in the smooth locus. -/
theorem mem_smoothLocus_of_isRegularLocalRing {K : Type u} [Field K] [PerfectField K]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of K)) [LocallyOfFiniteType f] {x : X}
    [IsRegularLocalRing (X.presheaf.stalk x)] : x ∈ f.smoothLocus := by
  obtain ⟨_, ⟨V, hV, rfl⟩, hxV, -⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
  have hU : IsAffineOpen (⊤ : (Spec (.of K)).Opens) := isAffineOpen_top _
  have hVU : V ≤ f ⁻¹ᵁ ⊤ := le_top
  have hft := f.finiteType_appLE hU hV hVU
  algebraize [(f.appLE ⊤ V hVU).hom]
  rw [Scheme.Hom.mem_smoothLocus, formallySmooth_stalkMap_iff ⊤ hU V hV hVU hxV]
  set q := (hV.primeIdealOf ⟨x, hxV⟩).asIdeal
  have : IsRegularLocalRing (Localization.AtPrime q) := by
    let := TopCat.Presheaf.algebra_section_stalk X.presheaf ⟨x, hxV⟩
    have := hV.isLocalization_stalk ⟨x, hxV⟩
    exact .of_ringEquiv (IsLocalization.algEquiv q.primeCompl (X.presheaf.stalk x)
      (Localization.AtPrime q)).toRingEquiv
  let e : K ≃+* Γ(Spec (.of K), ⊤) := (Scheme.ΓSpecIso (.of K)).symm.commRingCatIsoToRingEquiv
  let : Algebra K Γ(X, V) := ((f.appLE ⊤ V hVU).hom.comp e.toRingHom).toAlgebra
  have : Algebra.FiniteType K Γ(X, V) :=
    RingHom.FiniteType.comp hft (RingHom.FiniteType.of_surjective _ e.surjective)
  have : Algebra.EssFiniteType K (IsLocalRing.ResidueField (Localization.AtPrime q)) :=
    inferInstanceAs (Algebra.EssFiniteType K (Localization.AtPrime q ⧸ _))
  have h : Algebra.FormallySmooth K (Localization.AtPrime q) :=
    Algebra.FormallySmooth.localization_of_isRegularLocalRing (k := K) q
  change Algebra.FormallySmooth Γ(Spec (.of K), ⊤) (Localization.AtPrime q)
  rw [← RingHom.formallySmooth_algebraMap] at h ⊢
  have heq : algebraMap K (Localization.AtPrime q) =
      (algebraMap Γ(Spec (.of K), ⊤) (Localization.AtPrime q)).comp e.toRingHom := by
    rw [IsScalarTower.algebraMap_eq K Γ(X, V), IsScalarTower.algebraMap_eq Γ(Spec (.of K), ⊤)
      Γ(X, V)]
    rfl
  rw [heq] at h
  have := RingHom.FormallySmooth.respectsIso.2 _ e.symm h
  convert this using 1
  refine RingHom.ext fun a ↦ ?_
  simp only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom,
    RingEquiv.apply_symm_apply]

/-- **Regular ⇒ smooth over a perfect field** (Stacks 00TV, scheme form). -/
theorem smooth_of_isRegularLocalRing_stalk {K : Type u} [Field K] [PerfectField K]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of K)) [LocallyOfFiniteType f]
    (h : ∀ x : X, IsRegularLocalRing (X.presheaf.stalk x)) : Smooth f := by
  rw [← f.smoothLocus_eq_top_iff]
  refine top_le_iff.mp fun x _ ↦ ?_
  have := h x
  exact mem_smoothLocus_of_isRegularLocalRing f

/-- **Smooth ⇔ regular over a perfect field** (Stacks 00TV with 00TT; scheme form). -/
theorem smooth_iff_isRegularLocalRing_stalk {K : Type u} [Field K] [PerfectField K]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of K)) [LocallyOfFiniteType f] :
    Smooth f ↔ ∀ x : X, IsRegularLocalRing (X.presheaf.stalk x) :=
  ⟨fun _ x ↦ Smooth.isRegularLocalRing_stalk f x, smooth_of_isRegularLocalRing_stalk f⟩

/-- The structure map `Spec L → Spec K` of a field extension. -/
noncomputable abbrev specMap (K L : Type u) [Field K] [Field L] [Algebra K L] :
    Spec (.of L) ⟶ Spec (.of K) :=
  Spec.map (CommRingCat.ofHom (algebraMap K L))

/-- `X_L := X ×_K L` is **regular** (all its local rings are regular local rings). -/
def RegularAfter {K : Type u} [Field K] {X : Scheme.{u}} (f : X ⟶ Spec (.of K))
    (L : Type u) [Field L] [Algebra K L] : Prop :=
  ∀ x : ↥(pullback f (specMap K L)), IsRegularLocalRing ((pullback f (specMap K L)).presheaf.stalk x)

/-- `X` is **geometrically regular** over `K`: `X_L` is regular for every field extension `L/K`
(Stacks 038U asks this for finitely generated `L/K`; every `L` here, a priori stronger). -/
def GeometricallyRegular {K : Type u} [Field K] {X : Scheme.{u}} (f : X ⟶ Spec (.of K)) : Prop :=
  ∀ (L : Type u) [Field L] [Algebra K L], RegularAfter f L

theorem regularAfter_of_smooth {K : Type u} [Field K] {X : Scheme.{u}} (f : X ⟶ Spec (.of K))
    [Smooth f] (L : Type u) [Field L] [Algebra K L] : RegularAfter f L := by
  unfold RegularAfter
  intro x
  have : Smooth (pullback.snd f (specMap K L)) := inferInstance
  exact Smooth.isRegularLocalRing_stalk (pullback.snd f (specMap K L)) x

theorem geometricallyRegular_of_smooth {K : Type u} [Field K] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of K)) [Smooth f] : GeometricallyRegular f :=
  fun L _ _ ↦ regularAfter_of_smooth f L

/-- **Regular over an algebraic closure ⇒ smooth**, over any field: `X_{K̄}` is smooth over the
perfect field `K̄` by 00TV, and smoothness descends along the fpqc cover `Spec K̄ → Spec K`. -/
theorem smooth_of_regularAfter_algebraicClosure {K : Type u} [Field K] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of K)) [LocallyOfFiniteType f]
    (h : RegularAfter f (AlgebraicClosure K)) : Smooth f := by
  let g := specMap K (AlgebraicClosure K)
  have hsnd : Smooth (pullback.snd f g) := smooth_of_isRegularLocalRing_stalk _ h
  have : Surjective g := ⟨fun _ ↦ ⟨⟨⊥, Ideal.isPrime_bot⟩, Subsingleton.elim _ _⟩⟩
  have : Flat g := by
    rw [HasRingHomProperty.Spec_iff (P := @Flat)]
    exact RingHom.flat_algebraMap_iff.2 inferInstance
  exact MorphismProperty.of_pullback_snd_of_descendsAlong
    (Q := @Surjective ⊓ @Flat ⊓ @QuasiCompact) ⟨⟨‹_›, ‹_›⟩, inferInstance⟩ hsnd

/-- **Smooth ⇔ geometrically regular**, over any field (Stacks 038V / 00TT; UNVERIFIED tags). -/
theorem smooth_iff_geometricallyRegular {K : Type u} [Field K] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of K)) [LocallyOfFiniteType f] : Smooth f ↔ GeometricallyRegular f :=
  ⟨fun _ ↦ geometricallyRegular_of_smooth f,
    fun h ↦ smooth_of_regularAfter_algebraicClosure f (h _)⟩

/-- **Smooth ⇔ regular over `K̄`**, over any field. -/
theorem smooth_iff_regularAfter_algebraicClosure {K : Type u} [Field K] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of K)) [LocallyOfFiniteType f] :
    Smooth f ↔ RegularAfter f (AlgebraicClosure K) :=
  ⟨fun _ ↦ regularAfter_of_smooth f _, smooth_of_regularAfter_algebraicClosure f⟩

/-- **Over a perfect field: smooth ⇔ regular ⇔ geometrically regular.** -/
theorem smooth_tfae_perfect {K : Type u} [Field K] [PerfectField K] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of K)) [LocallyOfFiniteType f] :
    List.TFAE [Smooth f, ∀ x : X, IsRegularLocalRing (X.presheaf.stalk x),
      GeometricallyRegular f] := by
  tfae_have 1 ↔ 2 := smooth_iff_isRegularLocalRing_stalk f
  tfae_have 1 ↔ 3 := smooth_iff_geometricallyRegular f
  tfae_finish

end ZInQ.Contrib.SmoothRegular

#print axioms ZInQ.Contrib.SmoothRegular.smooth_tfae_perfect
#print axioms ZInQ.Contrib.SmoothRegular.smooth_iff_regularAfter_algebraicClosure
