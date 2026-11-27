import ZInQKernel.Contrib.HeightBC.H5GlueOpen

/-! # Detecting the generic isomorphism of an open group insertion by its actual image -/

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace ZInQ.Contrib.IsogenyDegree

/-- An open insertion becomes an isomorphism after pulling back along a map whose
image lies only under points contained in the insertion. This uses the actual
pullback and thus applies to the original generic markings. -/
theorem pullback_isIso_of_openImmersion_of_range {S T : Scheme.{0}} (g : T ⟶ S)
    {X Y : Over S} (j : X ⟶ Y) [IsOpenImmersion j.left]
    (h : ∀ y : Y.left, Y.hom y ∈ Set.range g → y ∈ Set.range j.left) :
    IsIso ((Over.pullback g).map j) := by
  let f := ((Over.pullback g).map j).left
  have hm : f = pullback.map X.hom g Y.hom g j.left (𝟙 _) (𝟙 _)
      (by simp) (by simp) := by
    apply pullback.hom_ext <;> simp [f, Over.pullback_map_left]
  have hIso : IsIso f := by
    rw [isIso_iff_isOpenImmersion_and_surjective]
    refine ⟨ZInQ.H5Glue.isOpenImmersion_pullback_map g j, ⟨fun z => ?_⟩⟩
    change z ∈ Set.range f
    rw [hm, Scheme.Pullback.range_map]
    refine ⟨h (pullback.fst Y.hom g z) ?_, ?_⟩
    · have hz := congrArg (fun a : pullback Y.hom g ⟶ S => a z) (pullback.condition (f := Y.hom) (g := g))
      exact ⟨pullback.snd Y.hom g z, hz.symm⟩
    · exact ⟨pullback.snd Y.hom g z, rfl⟩
  have : IsIso ((Over.forget T).map ((Over.pullback g).map j)) := hIso
  exact isIso_of_reflects_iso _ (Over.forget T)

open ZInQ.DefFaltings ZInQ.H5Glue
open NumberField

/-- Over the ring of integers, it suffices that the insertion contain every point
of the original model over the generic prime. -/
theorem generic_isIso_of_openImmersion_of_generic_points {K L : Type} [Field K] [Field L]
    [NumberField L] [Algebra K L] {A : PkgI3.AbVar K}
    (G N : GroupModel A L) (j : G.G ⟶ N.G) [IsOpenImmersion j.left]
    (h : ∀ y : N.G.left, (N.G.hom y).asIdeal = ⊥ → y ∈ Set.range j.left) :
    IsIso ((Over.pullback (jL L)).map j) := by
  apply pullback_isIso_of_openImmersion_of_range
  intro y hy
  obtain ⟨z, hz⟩ := hy
  apply h y
  rw [← hz]
  have hz0 : z.asIdeal = ⊥ := (Ideal.eq_bot_or_top z.asIdeal).resolve_right z.isPrime.ne_top
  change Ideal.comap (algebraMap (𝓞 L) L) z.asIdeal = ⊥
  rw [hz0]
  exact Ideal.comap_bot_of_injective _ (FaithfulSMul.algebraMap_injective (𝓞 L) L)

#print axioms pullback_isIso_of_openImmersion_of_range
#print axioms generic_isIso_of_openImmersion_of_generic_points

end ZInQ.Contrib.IsogenyDegree
