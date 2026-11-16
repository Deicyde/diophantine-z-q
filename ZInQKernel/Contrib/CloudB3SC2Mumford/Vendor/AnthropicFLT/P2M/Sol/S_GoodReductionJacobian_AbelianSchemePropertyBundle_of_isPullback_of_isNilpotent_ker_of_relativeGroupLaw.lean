/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: P2M.Sol.S_GoodReductionJacobian_AbelianSchemePropertyBundle_of_isPullback_of_isNilpotent_ker_of_relativeGroupLaw
Modified for the Z-in-Q kernel (2026-11-16, CloudB3SC2Mumford): local import paths are relocated
(modules already vendored in this repository are imported from their existing copies; `P2M.Util`
is the copy published under CloudW02Connectedness) and the upstream lakefile options are set as
`set_option` lines after the imports; any other change is marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import ZInQKernel.Contrib.CloudB3SC2Mumford.Vendor.AnthropicFLT.Definitions.Def_JacJ1Iface
import ZInQKernel.Contrib.CloudB3SC2Mumford.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_RelativeGroupLaw
import ZInQKernel.Contrib.CloudB3SC2Mumford.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_isHomeomorph_of_isPullback_of_surjective_of_isNilpotent_ker
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.P2M.Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

namespace P2MW.S_GoodReductionJacobian_AbelianSchemePropertyBundle_of_isPullback_of_isNilpotent_ker_of_relativeGroupLaw

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian IsLocalRing

universe u

namespace E160K5

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem preimage_singleton_eq_image {T' T : Type u} [CommRing T'] [CommRing T]
    (π : T' →+* T) (hπ : Function.Surjective π) (hker : IsNilpotent (RingHom.ker π))
    {A₀ : Scheme.{u}} (f₀ : A₀ ⟶ Spec (CommRingCat.of T))
    {A : Scheme.{u}} (f : A ⟶ Spec (CommRingCat.of T'))
    (g : A₀ ⟶ A) (hg : IsPullback g f₀ f (Spec.map (CommRingCat.ofHom π)))
    (s : Spec (CommRingCat.of T)) :
    f.base ⁻¹' {Spec.map (CommRingCat.ofHom π) s} = g.base '' (f₀.base ⁻¹' {s}) := by
  have hgH := AlgebraicGeometry.isHomeomorph_of_isPullback_of_surjective_of_isNilpotent_ker
    π hπ hker f f₀ g hg
  obtain ⟨_, hgsurj, _⟩ := hgH
  have hbH := AlgebraicGeometry.isHomeomorph_of_isPullback_of_surjective_of_isNilpotent_ker
    π hπ hker (𝟙 _) (𝟙 _) (Spec.map (CommRingCat.ofHom π)) IsPullback.of_id_snd
  obtain ⟨_, _, hbhomeo⟩ := hbH
  have hw : ∀ x₀ : A₀, f.base (g.base x₀) = (Spec.map (CommRingCat.ofHom π)).base (f₀.base x₀) := by
    intro x₀
    have := congrArg (fun k => k.base x₀) hg.w
    simpa using this
  ext x
  constructor
  · intro hx
    obtain ⟨x₀, rfl⟩ := g.surjective x
    refine ⟨x₀, ?_, rfl⟩
    have h1 : (Spec.map (CommRingCat.ofHom π)).base (f₀.base x₀) =
        (Spec.map (CommRingCat.ofHom π)).base s := by
      rw [← hw]; simpa using hx
    exact hbhomeo.injective h1
  · rintro ⟨x₀, hx₀, rfl⟩
    have hx₀' : f₀.base x₀ = s := by simpa using hx₀
    rw [Set.mem_preimage, Set.mem_singleton_iff, hw, hx₀']

theorem isConnected_fibre {T' T : Type u} [CommRing T'] [CommRing T]
    (π : T' →+* T) (hπ : Function.Surjective π) (hker : IsNilpotent (RingHom.ker π))
    {A₀ : Scheme.{u}} (f₀ : A₀ ⟶ Spec (CommRingCat.of T))
    (hconn₀ : ∀ s : Spec (CommRingCat.of T), _root_.IsConnected (f₀.base ⁻¹' {s}))
    {A : Scheme.{u}} (f : A ⟶ Spec (CommRingCat.of T'))
    (g : A₀ ⟶ A) (hg : IsPullback g f₀ f (Spec.map (CommRingCat.ofHom π)))
    (s' : Spec (CommRingCat.of T')) : _root_.IsConnected (f.base ⁻¹' {s'}) := by
  have hbH := AlgebraicGeometry.isHomeomorph_of_isPullback_of_surjective_of_isNilpotent_ker
    π hπ hker (𝟙 _) (𝟙 _) (Spec.map (CommRingCat.ofHom π)) IsPullback.of_id_snd
  obtain ⟨_, hbsurj, _⟩ := hbH
  obtain ⟨s, rfl⟩ := (Spec.map (CommRingCat.ofHom π)).surjective s'
  rw [preimage_singleton_eq_image π hπ hker f₀ f g hg s]
  exact (hconn₀ s).image _ g.base.hom.continuous.continuousOn

end E160K5

theorem solution
    (T' T : Type u) [CommRing T'] [IsLocalRing T'] [CommRing T] (π : T' →+* T) (hπ : Function.Surjective π)
    (hker : IsNilpotent (RingHom.ker π))
    {A₀ : Scheme.{u}} (f₀ : A₀ ⟶ Spec (CommRingCat.of T)) (h₀ : AbelianSchemePropertyBundle T f₀)
    {A : Scheme.{u}} (f : A ⟶ Spec (CommRingCat.of T')) (hs : Smooth f) (hp : IsProper f)
    (g : A₀ ⟶ A) (hg : IsPullback g f₀ f (Spec.map (CommRingCat.ofHom π)))
    (L : RelativeGroupLaw T' f) :
    AbelianSchemePropertyBundle T' f := by
  exact
    { smooth := hs
      proper := hp
      connectedFibres :=
        E160K5.isConnected_fibre π hπ hker f₀ h₀.connectedFibres f g hg
      hasGroupLaw := ⟨L⟩ }
