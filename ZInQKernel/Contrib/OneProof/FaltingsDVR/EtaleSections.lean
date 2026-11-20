import ZInQKernel.Contrib.OneProof.NeronDVR.GroupAmple
import Mathlib.AlgebraicGeometry.Morphisms.FlatMono
import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite
import Mathlib.RingTheory.Unramified.LocalStructure

noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace SmoothGroup

private theorem locallyQuasiFinite_of_etale {X Y : Scheme.{0}} (f : X ⟶ Y) [Etale f] :
    LocallyQuasiFinite f := by
  constructor
  intro U hU V hV e
  have he := f.etale_appLE hU hV e
  let g : Γ(Y, U) →+* Γ(X, V) := (f.appLE U V e).hom
  change g.QuasiFinite
  letI : Algebra Γ(Y, U) Γ(X, V) := g.toAlgebra
  have : Algebra.Etale Γ(Y, U) Γ(X, V) := RingHom.etale_algebraMap.mp he
  exact RingHom.quasiFinite_algebraMap.mpr inferInstance

/-- A special-fibre point of an étale scheme over a strictly henselian DVR
lifts to a section through that point. -/
theorem exists_section_over_closed_of_etale
    {R : Type} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [HenselianLocalRing R] [IsSepClosed (IsLocalRing.ResidueField R)]
    {X : Scheme.{0}} (f : X ⟶ Spec (.of R)) [Etale f] (x : X)
    (hx : f x = IsLocalRing.closedPoint R) :
    ∃ a : Spec (.of R) ⟶ X, a ≫ f = 𝟙 _ ∧ a (IsLocalRing.closedPoint R) = x := by
  have : LocallyQuasiFinite f := locallyQuasiFinite_of_etale f
  let s : Spec (.of R) := IsLocalRing.closedPoint R
  obtain ⟨U, hU, hUx⟩ := isDiscrete_iff_forall_mem_exists_isOpen.mp
    (f.isDiscrete_preimage_singleton s) x hx
  have hxU : x ∈ U := by
    have : x ∈ U ∩ f ⁻¹' {s} := hUx ▸ Set.mem_singleton x
    exact this.1
  obtain ⟨a, ha, hm⟩ := NeronDVR.exists_section_in_open_of_strictHenselianDVR f ⟨U, hU⟩ hx hxU
  refine ⟨a, ha, ?_⟩
  have hs : f (a s) = s := by
    change (a ≫ f) s = s
    rw [ha]
    rfl
  have hi : a s ∈ U ∩ f ⁻¹' {s} := ⟨hm, hs⟩
  simpa only [hUx, Set.mem_singleton_iff] using hi

/-- A section of an étale morphism into the spectrum of a local ring is
determined by its image at the closed point. -/
theorem section_eq_of_closed_eq {R : Type} [CommRing R] [IsLocalRing R]
    {X : Scheme.{0}} (f : X ⟶ Spec (.of R)) [Etale f]
    {a b : Spec (.of R) ⟶ X} (ha : a ≫ f = 𝟙 _) (hb : b ≫ f = 𝟙 _)
    (h : a (IsLocalRing.closedPoint R) = b (IsLocalRing.closedPoint R)) : a = b := by
  have : Mono a := by
    constructor
    intro Z α β e
    simpa only [Category.assoc, ha, Category.comp_id] using
      congrArg (fun γ : Z ⟶ X => γ ≫ f) e
  have : Etale (a ≫ f) := by rw [ha]; infer_instance
  have : Etale a := Etale.of_comp a f
  have : IsOpenImmersion a := IsOpenImmersion.of_flat_of_mono a
  have hall : b ⁻¹ᵁ a.opensRange = ⊤ := by
    apply (IsLocalRing.closedPoint_mem_iff _).mp
    exact ⟨_, h⟩
  have hba : Set.range b ⊆ Set.range a := by
    rintro _ ⟨y, rfl⟩
    have : y ∈ b ⁻¹ᵁ a.opensRange := by simp [hall]
    exact this
  let w := IsOpenImmersion.lift a b hba
  have hw : w ≫ a = b := IsOpenImmersion.lift_fac _ _ _
  have hwId : w = 𝟙 _ := by
    simpa only [Category.assoc, ha, Category.comp_id, hb] using
      congrArg (fun γ : Spec (.of R) ⟶ X => γ ≫ f) hw
  simpa only [hwId, Category.id_comp] using hw

end SmoothGroup
