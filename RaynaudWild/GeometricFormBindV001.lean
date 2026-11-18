import RaynaudWild.TorusFrobeniusBindV003

/-!
# The geometric form: torus data over the algebraic closure, action on native special-fibre points

In the geometric form of semistability the identity component, its torus and the quotient are
given over `Ω` (an algebraic closure of the finite residue field `k`): a family of
`Ω`-morphisms `Spec R → G_Ω` (`G_Ω` the base change of the special fibre `G` along
`Spec Ω → Spec k`; compose the torus presentation with the open immersion of the identity
component), natural in `Ω`-algebra maps.

* `toNative`: through the base-change adjunction each such `Ω`-morphism is a native `k`-morphism
  `Spec R → G` (`Spec R` a `k`-scheme through `k → Ω → R`); `toNative_natural`;
* `frob_pow_geometric`: there is `N ≥ 1` such that `Spec(σ ^ N)` acts on the native points of the
  torus by `t ↦ t ^ (q ^ N)`.  The chosen subobject and maps need no separate descent: the
  composite family is a family of `k`-morphisms into `G`, and the spreading-out step is applied to
  its universal point.
-/

open CategoryTheory AlgebraicGeometry

noncomputable section

namespace RaynaudWild.FrobDescent

variable {k Ω : Type} [Field k] [Finite k] [Field Ω] [Algebra k Ω]

variable (k Ω) in
/-- `Spec Ω → Spec k`. -/
abbrev sΩ : Spec (CommRingCat.of Ω) ⟶ Spec (CommRingCat.of k) :=
  Spec.map (CommRingCat.ofHom (algebraMap k Ω))

/-- `Spec R` as an `Ω`-scheme. -/
def ΩPt (R : Type) [CommRing R] [Algebra Ω R] : Over (Spec (CommRingCat.of Ω)) :=
  Over.mk (Spec.map (CommRingCat.ofHom (algebraMap Ω R)))

/-- An `Ω`-algebra map as an `Ω`-morphism of spectra. -/
def ΩPtMap {R S : Type} [CommRing R] [Algebra Ω R] [CommRing S] [Algebra Ω S] (f : R →ₐ[Ω] S) :
    ΩPt (Ω := Ω) S ⟶ ΩPt (Ω := Ω) R :=
  Over.homMk (Spec.map (CommRingCat.ofHom f.toRingHom)) (by
    change Spec.map (CommRingCat.ofHom f.toRingHom) ≫
        Spec.map (CommRingCat.ofHom (algebraMap Ω R)) =
      Spec.map (CommRingCat.ofHom (algebraMap Ω S))
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    congr 2
    ext a
    simp)

/-- `Spec R → Spec Ω → Spec k` is the `k`-scheme `kPt R`. -/
def isoK (R : Type) [CommRing R] [Algebra Ω R] :
    (Over.map (sΩ k Ω)).obj (ΩPt (Ω := Ω) R) ≅ kPt (k := k) (Ω := Ω) R :=
  Over.isoMk (Iso.refl _) (by
    change 𝟙 _ ≫ Spec.map (CommRingCat.ofHom ((algebraMap Ω R).comp (algebraMap k Ω))) =
      Spec.map (CommRingCat.ofHom (algebraMap Ω R)) ≫
        Spec.map (CommRingCat.ofHom (algebraMap k Ω))
    rw [Category.id_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp])

/-- An `Ω`-morphism `Spec R → G_Ω` as a native `k`-morphism `Spec R → G`. -/
def toNative (G : Over (Spec (CommRingCat.of k))) {R : Type} [CommRing R] [Algebra Ω R]
    (p : ΩPt (Ω := Ω) R ⟶ (Over.pullback (sΩ k Ω)).obj G) : kPt (k := k) (Ω := Ω) R ⟶ G :=
  (isoK R).inv ≫ ((Over.mapPullbackAdj (sΩ k Ω)).homEquiv _ _).symm p

/-- The transport is natural in `Ω`-algebra maps. -/
theorem toNative_natural (G : Over (Spec (CommRingCat.of k))) {R S : Type} [CommRing R]
    [Algebra Ω R] [CommRing S] [Algebra Ω S] (f : R →ₐ[Ω] S)
    (p : ΩPt (Ω := Ω) R ⟶ (Over.pullback (sΩ k Ω)).obj G) :
    toNative G (ΩPtMap f ≫ p) = kPtMap f ≫ toNative G p := by
  change (isoK S).inv ≫ ((Over.mapPullbackAdj (sΩ k Ω)).homEquiv _ _).symm (ΩPtMap f ≫ p) =
    kPtMap f ≫ (isoK R).inv ≫ ((Over.mapPullbackAdj (sΩ k Ω)).homEquiv _ _).symm p
  rw [Adjunction.homEquiv_naturality_left_symm, ← Category.assoc, ← Category.assoc]
  congr 1
  all_goals
    apply Over.OverMorphism.ext
    change 𝟙 _ ≫ Spec.map (CommRingCat.ofHom f.toRingHom) =
      Spec.map (CommRingCat.ofHom f.toRingHom) ≫ 𝟙 _
    rw [Category.id_comp, Category.comp_id]

/-- **Geometric form.** For a torus presentation over `Ω` of the base change `G_Ω` of a `k`-scheme
`G` locally of finite presentation, natural in `Ω`-algebra maps, there is `N ≥ 1` such that
`Spec(σ ^ N)` acts on the native `k`-points of the torus by `t ↦ t ^ (q ^ N)`. -/
theorem frob_pow_geometric [Algebra.IsAlgebraic k Ω] (σ : Ω ≃ₐ[k] Ω)
    (hσ : ∀ x : Ω, σ x = x ^ Nat.card k) (G : Over (Spec (CommRingCat.of k)))
    [LocallyOfFinitePresentation G.hom] (r : ℕ)
    (e : ∀ (R : Type) [CommRing R] [Algebra Ω R],
      (Fin r → Rˣ) → (ΩPt (Ω := Ω) R ⟶ (Over.pullback (sΩ k Ω)).obj G))
    (he : ∀ (R S : Type) [CommRing R] [Algebra Ω R] [CommRing S] [Algebra Ω S]
      (f : R →ₐ[Ω] S) (t : Fin r → Rˣ),
      e S (fun i => Units.map (f : R →* S) (t i)) = ΩPtMap f ≫ e R t) :
    ∃ N : ℕ, 0 < N ∧ ∀ t : Fin r → Ωˣ,
      galK (σ ^ N) ≫ toNative G (e Ω t) =
        toNative G (e Ω (fun i => t i ^ (Nat.card k ^ N))) :=
  frob_pow_torus_point_fin G σ hσ r (fun R _ _ t => toNative G (e R t))
    (fun R S _ _ _ _ f t => by
      show toNative G (e S (fun i => Units.map (f : R →* S) (t i))) = kPtMap f ≫ toNative G (e R t)
      rw [he, toNative_natural])

end RaynaudWild.FrobDescent

#print axioms RaynaudWild.FrobDescent.toNative_natural
#print axioms RaynaudWild.FrobDescent.frob_pow_geometric
