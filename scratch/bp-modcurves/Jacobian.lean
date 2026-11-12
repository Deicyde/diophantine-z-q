import Mathlib

/-!
# bp-modcurves, node MC6: the Jacobian of a pointed curve as an Albanese predicate

Over Mathlib schemes and the repository's `PkgI3.AbVar` (copied below from
`scratch/pkg-I3/I3.lean`, since scratch files cannot import each other: the structure, the
commutativity instance, and nothing else).

* `IsCurve X` : `X → Spec K` is proper, smooth of relative dimension 1, geometrically connected.
* `IsJacobian X P₀ J aj` : `aj : X → J` sends `P₀` to `0`, and every `K`-morphism `f : X → A` to an
  abelian variety with `f(P₀) = 0` factors as `φ ∘ aj` for a unique homomorphism `φ : J → A`
  (the Albanese property; for a curve the Albanese variety is the Jacobian: Milne, *Jacobian
  varieties*, in Arithmetic Geometry (1986), Prop. 6.1, UNVERIFIED number).
* `JacobianExists K` : the existence leaf (Weil 1948; Chow; Milne 1986, Thm 1.1 with Prop. 6.1,
  UNVERIFIED numbers). This is a **leaf statement** (a `Prop`), not proved here.
* `IsJacobian.unique` : any two Jacobians of `(X, P₀)` are isomorphic by a unique homomorphism
  compatible with `aj` (glue, proved). This is the acceptance test for the predicate.
-/

namespace BPModCurves

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj

universe u

/-- (Copied from `PkgI3.AbVar`.) An abelian variety over a field `K`: a group object in schemes
over `Spec K` whose structure morphism is proper, smooth and geometrically integral. -/
structure AbVar (K : Type u) [Field K] where
  X : Over (Spec (CommRingCat.of K))
  [grp : GrpObj X]
  [proper : IsProper X.hom]
  [smooth : Smooth X.hom]
  [geomInt : GeometricallyIntegral X.hom]

attribute [instance] AbVar.grp AbVar.proper AbVar.smooth AbVar.geomInt

instance {K : Type u} [Field K] (A : AbVar K) : IsCommMonObj A.X :=
  isCommMonObj_of_isProper_of_geometricallyIntegral A.X

variable {K : Type u} [Field K]

/-- A smooth proper geometrically connected curve over `K` (proper curves are projective). -/
class IsCurve (X : Over (Spec (CommRingCat.of K))) : Prop where
  proper : IsProper X.hom
  smooth : SmoothOfRelativeDimension 1 X.hom
  geomConnected : GeometricallyConnected X.hom

/-- **The Jacobian of the pointed curve `(X, P₀)`**, by the Albanese property. -/
structure IsJacobian (X : Over (Spec (CommRingCat.of K)))
    (P₀ : 𝟙_ (Over (Spec (CommRingCat.of K))) ⟶ X) (J : AbVar K) (aj : X ⟶ J.X) : Prop where
  base : P₀ ≫ aj = η[J.X]
  univ : ∀ (A : AbVar K) (f : X ⟶ A.X), P₀ ≫ f = η[A.X] →
    ∃! φ : J.X ⟶ A.X, IsMonHom φ ∧ aj ≫ φ = f

/-- **Leaf MC6' (existence of the Jacobian)**, as a statement. -/
def JacobianExists (K : Type u) [Field K] : Prop :=
  ∀ (X : Over (Spec (CommRingCat.of K))) (_ : IsCurve X)
    (P₀ : 𝟙_ (Over (Spec (CommRingCat.of K))) ⟶ X),
    ∃ (J : AbVar K) (aj : X ⟶ J.X), IsJacobian X P₀ J aj

/-- **Uniqueness of the Jacobian** (glue): two Jacobians of `(X, P₀)` are isomorphic by a
homomorphism compatible with the Abel–Jacobi maps, and that isomorphism is unique. -/
theorem IsJacobian.unique {X : Over (Spec (CommRingCat.of K))}
    {P₀ : 𝟙_ (Over (Spec (CommRingCat.of K))) ⟶ X} {J J' : AbVar K} {aj : X ⟶ J.X}
    {aj' : X ⟶ J'.X} (h : IsJacobian X P₀ J aj) (h' : IsJacobian X P₀ J' aj') :
    ∃ e : J.X ≅ J'.X, IsMonHom e.hom ∧ aj ≫ e.hom = aj' ∧
      ∀ φ : J.X ⟶ J'.X, IsMonHom φ → aj ≫ φ = aj' → φ = e.hom := by
  obtain ⟨φ, ⟨hφ, eφ⟩, uφ⟩ := h.univ J' aj' h'.base
  obtain ⟨ψ, ⟨hψ, eψ⟩, -⟩ := h'.univ J aj h.base
  have hid : φ ≫ ψ = 𝟙 _ := by
    have u := (h.univ J aj h.base).unique (y₁ := φ ≫ ψ) (y₂ := 𝟙 _)
      ⟨inferInstance, by rw [← Category.assoc, eφ, eψ]⟩ ⟨inferInstance, Category.comp_id _⟩
    exact u
  have hid' : ψ ≫ φ = 𝟙 _ := by
    have u := (h'.univ J' aj' h'.base).unique (y₁ := ψ ≫ φ) (y₂ := 𝟙 _)
      ⟨inferInstance, by rw [← Category.assoc, eψ, eφ]⟩ ⟨inferInstance, Category.comp_id _⟩
    exact u
  exact ⟨⟨φ, ψ, hid, hid'⟩, hφ, eφ, fun χ hχ eχ => uφ χ ⟨hχ, eχ⟩⟩

/-- A chosen Jacobian, given the existence leaf. -/
noncomputable def jacobian (hJ : JacobianExists K) (X : Over (Spec (CommRingCat.of K)))
    [hX : IsCurve X] (P₀ : 𝟙_ (Over (Spec (CommRingCat.of K))) ⟶ X) : AbVar K :=
  Classical.choose (hJ X hX P₀)

theorem jacobian_spec (hJ : JacobianExists K) (X : Over (Spec (CommRingCat.of K)))
    [hX : IsCurve X] (P₀ : 𝟙_ (Over (Spec (CommRingCat.of K))) ⟶ X) :
    ∃ aj : X ⟶ (jacobian hJ X P₀).X, IsJacobian X P₀ (jacobian hJ X P₀) aj :=
  Classical.choose_spec (hJ X hX P₀)

end BPModCurves

#print axioms BPModCurves.IsJacobian.unique
#print axioms BPModCurves.jacobian_spec
