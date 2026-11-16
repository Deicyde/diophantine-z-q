import ZInQKernel.Contrib.CloudB3SC2Mumford.Vendor.AnthropicFLT.Definitions.Def_JacJ1Iface
import ZInQKernel.Contrib.CloudB3SC2Mumford.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_AdicThickening

/-!
# Internal interfaces of the proof of `MumfordGroupLaw`

These two propositions split the proof into independent parts. Neither is an assumption of the
final theorem: each is proved in this directory.

* `ProperAlgebraization`: a compatible family of morphisms between the adic thickenings of two
  proper schemes over a complete noetherian adic ring comes from a unique morphism of the schemes
  (EGA III₁ 5.4.1 for proper schemes). Proved in `Algebraize.lean` from the proper-scheme
  existence theorems of the vendored Fermat development (finite covers, closed immersions and
  isomorphisms over a proper scheme), by the graph construction.
* `AffineGroupLaw`: over a noetherian ring, a smooth proper family with topologically connected
  fibres, a section and abelian geometric fibres has a unique group law with the given identity,
  and it is commutative. Proved in `Pipeline/Affine.lean` from `ProperAlgebraization`, following the
  vendored projective-case proof with the projective algebraization step replaced.
-/

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry GoodReductionJacobian NeronModelInfra

universe u

namespace ZInQ.Contrib.CloudB3SC2Mumford

/-- Morphism algebraization over a complete noetherian adic ring, for proper schemes. -/
def ProperAlgebraization : Prop :=
  ∀ {R : Type u} [CommRing R] [IsNoetherianRing R] (I : Ideal R) [IsAdicComplete I R]
    {X Y : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R)) (g : Y ⟶ Spec (CommRingCat.of R)),
    IsProper f → IsProper g →
    ∀ (φ : ∀ n : ℕ, adicThickening f I n ⟶ adicThickening g I n),
      (∀ n : ℕ, φ n ≫ adicThickeningToBase g I n = adicThickeningToBase f I n) →
      (∀ n : ℕ, adicThickeningTransition f I n ≫ φ (n + 1) = φ n ≫ adicThickeningTransition g I n) →
      ∃! ψ : X ⟶ Y, ψ ≫ g = f ∧ ∀ n : ℕ, adicThickeningι f I n ≫ ψ = φ n ≫ adicThickeningι g I n

/-- The group law on a smooth proper family with abelian geometric fibres over a noetherian ring. -/
def AffineGroupLaw : Prop :=
  ∀ {R : Type u} [CommRing R] [IsNoetherianRing R] {A : Scheme.{u}} (f : A ⟶ Spec (CommRingCat.of R)),
    Smooth f → IsProper f → (∀ s : Spec (CommRingCat.of R), _root_.IsConnected (f.base ⁻¹' {s})) →
    ∀ (e : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) f),
      (∀ (k : Type u) [Field k] [IsAlgClosed k] (s : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of R)),
        AbelianSchemePropertyBundle k (pullback.snd f s)) →
      ∃ L : RelativeGroupLaw R f, L.one (𝟙 _) = e ∧ L.IsCommutative ∧
        ∀ L' : RelativeGroupLaw R f, L'.one (𝟙 _) = e → L' = L

end ZInQ.Contrib.CloudB3SC2Mumford
