import RaynaudWild.GeometricFormBindV001
import Mathlib.AlgebraicGeometry.Morphisms.Smooth

/-!
# Finite presentation of the actual special fibre and of its identity component

The spreading-out step needs the target to be locally of finite presentation over the residue
field.  For the special fibre of a smooth group model over the valuation ring this is a
consequence of smoothness (stable under base change), and an open subscheme (the identity
component) inherits it.

* `lfp_baseChange_of_smooth`: the base change of a smooth `O`-scheme along `Spec k → Spec O` is
  locally of finite presentation;
* `lfp_of_openImmersion`: an open subscheme of a `k`-scheme locally of finite presentation is
  locally of finite presentation;
* `frob_pow_specialFibre_grp`: the group form of the residue Frobenius power action for a
  multiplicative torus presentation of an open subgroup scheme `U` of the special fibre of a
  smooth group model.
-/

open CategoryTheory AlgebraicGeometry MonObj Limits

noncomputable section

namespace RaynaudWild.FrobDescent

/-- The special fibre of a smooth `O`-scheme is locally of finite presentation over `k`. -/
theorem lfp_baseChange_of_smooth {O k : Type} [CommRing O] [Field k] [Algebra O k]
    (G : Over (Spec (CommRingCat.of O))) [Smooth G.hom] :
    LocallyOfFinitePresentation
      ((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap O k)))).obj G).hom := by
  change LocallyOfFinitePresentation (pullback.snd G.hom _)
  infer_instance

/-- An open subscheme of a `k`-scheme locally of finite presentation is locally of finite
presentation. -/
theorem lfp_of_openImmersion {k : Type} [Field k] {U G : Over (Spec (CommRingCat.of k))}
    (inc : U ⟶ G) [IsOpenImmersion inc.left] [LocallyOfFinitePresentation G.hom] :
    LocallyOfFinitePresentation U.hom := by
  rw [← Over.w inc]
  infer_instance

/-- **Special fibre, group form.** Let `𝒢` be a smooth `O`-scheme, `G` its special fibre over the
finite residue field `k` (base change along `O → k`), `U ⊆ G` an open subgroup scheme, and `e` a
multiplicative torus presentation of `U` over `Ω`, natural in `Ω`-algebra maps.  Then a power
`σ ^ N` (`N ≥ 1`) of the residue Frobenius acts on the torus points by `P ↦ P ^ (q ^ N)`. -/
theorem frob_pow_specialFibre_grp {O k Ω : Type} [CommRing O] [Field k] [Finite k] [Algebra O k]
    [Field Ω] [Algebra k Ω] [Algebra.IsAlgebraic k Ω] (σ : Ω ≃ₐ[k] Ω)
    (hσ : ∀ x : Ω, σ x = x ^ Nat.card k) (𝒢 : Over (Spec (CommRingCat.of O))) [Smooth 𝒢.hom]
    (U : Over (Spec (CommRingCat.of k))) [GrpObj U]
    (inc : U ⟶ (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap O k)))).obj 𝒢)
    [IsOpenImmersion inc.left] (r : ℕ)
    (e : ∀ (R : Type) [CommRing R] [Algebra Ω R],
      (Fin r → Rˣ) → (kPt (k := k) (Ω := Ω) R ⟶ U))
    (he : ∀ (R S : Type) [CommRing R] [Algebra Ω R] [CommRing S] [Algebra Ω S]
      (f : R →ₐ[Ω] S) (t : Fin r → Rˣ),
      e S (fun i => Units.map (f : R →* S) (t i)) = kPtMap f ≫ e R t)
    (hmul : ∀ t s : Fin r → Ωˣ, e Ω (t * s) = e Ω t * e Ω s) :
    ∃ N : ℕ, 0 < N ∧ ∀ t : Fin r → Ωˣ,
      galK (σ ^ N) ≫ e Ω t = (e Ω t) ^ (Nat.card k ^ N) := by
  haveI := lfp_baseChange_of_smooth (k := k) 𝒢
  haveI := lfp_of_openImmersion inc
  exact frob_pow_torus_point_grp U σ hσ r e he hmul

end RaynaudWild.FrobDescent

#print axioms RaynaudWild.FrobDescent.lfp_baseChange_of_smooth
#print axioms RaynaudWild.FrobDescent.lfp_of_openImmersion
#print axioms RaynaudWild.FrobDescent.frob_pow_specialFibre_grp
