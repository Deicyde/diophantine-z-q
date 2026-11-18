import NeronEtaleExtensionV001
import NeronTateLiftV001

/-!
# Points with unramified coordinate fields and sections of a Néron model

Let `O` be a discrete valuation subring of a field `K`, `Ω ⊇ K` a field with a valuation subring `w`
over `O`, `A / K` an abelian variety and `(N, e)` an `O`-model of `A` with the Néron mapping property
(smooth test schemes), separated over `O`, a group scheme with `e` a homomorphism.

Say that `x ∈ A(Ω)` has an unramified descent if it comes from `y ∈ A(M)` for a finite separable
subextension `M ⊆ Ω` whose integral closure over `O` is unramified at the centre of `w`.

* `exists_unique_section_of_unramifiedDescent`: such an `x` is the generic fibre of a unique
  `w`-section of `N`.
* `torsion_section_of_unramifiedDescent`: if moreover `x ^ m = 1`, the section is the unique
  `m`-torsion `w`-section with generic fibre `x`.
* `exists_unique_compatible_sections_of_unramifiedDescent`: an element of `T_ℓ(A)` all of whose
  components have unramified descents lifts to a unique compatible system of `w`-sections.
* `inertia_fixed_sections`: the same statements for every inertia-fixed point, conditional on the
  explicit arithmetic input `InertiaFixedUnramified` (inertia-fixed points have unramified descents),
  which is not proved here.
-/

noncomputable section
set_option autoImplicit false

open CategoryTheory AlgebraicGeometry Limits MonObj

namespace NeronInvariantTorsion

variable {K : Type} [Field K] {Ω : Type} [Field Ω] [Algebra K Ω]
variable (O : ValuationSubring K) [IsDiscreteValuationRing O]
variable (w : ValuationSubring Ω) (hw : w.comap (algebraMap K Ω) = O)

/-- `x ∈ A(Ω)` comes from a point over a finite separable coordinate field `M ⊆ Ω` whose integral
closure over `O` is unramified at the centre of `w`. -/
def HasUnramifiedDescent {A : PkgI3.AbVar K} (x : A.Pt Ω) : Prop :=
  ∃ (M : IntermediateField K Ω) (_ : FiniteDimensional K M) (_ : Algebra.IsSeparable K M)
    (_ : Algebra O M) (_ : IsScalarTower O K M)
    (_ : Algebra.IsUnramifiedAt O (center O w hw M)) (y : A.Pt M),
    Spec.map (CommRingCat.ofHom M.val.toRingHom) ≫ y.left = x.left

variable {A : PkgI3.AbVar K} {N : Over (Spec (CommRingCat.of O))}
  (e : (Over.pullback (jO O)).obj N ≅ A.X)

/-- **Existence and uniqueness of the integral section.** -/
theorem exists_unique_section_of_unramifiedDescent [IsSeparated N.hom]
    (hN : ∀ (Y : Over (Spec (CommRingCat.of O))) [Smooth Y.hom],
      Function.Bijective fun f : Y ⟶ N => (Over.pullback (jO O)).map f ≫ e.hom)
    (x : A.Pt Ω) (hx : HasUnramifiedDescent O w hw x) :
    ∃! s : specW O w hw ⟶ N, genericFibre O w hw e s = x := by
  obtain ⟨M, _, _, _, _, _, y, hxy⟩ := hx
  obtain ⟨f, -, -, φ, σ, h⟩ := exists_section_of_unramified O w hw M e hN y x hxy
  exact ⟨σ ≫ φ, h, fun s hs => genericFibre_injective O w hw e (hs.trans h.symm)⟩

open scoped Obj in
/-- **Torsion.** An `m`-torsion point with an unramified descent is the generic fibre of a unique
`m`-torsion `w`-section. -/
theorem torsion_section_of_unramifiedDescent [GrpObj N] [IsSeparated N.hom]
    (hgen : letI : GrpObj ((Over.pullback (jO O)).obj N) := Functor.grpObjObj
      IsMonHom e.hom)
    (hN : ∀ (Y : Over (Spec (CommRingCat.of O))) [Smooth Y.hom],
      Function.Bijective fun f : Y ⟶ N => (Over.pullback (jO O)).map f ≫ e.hom)
    (x : A.Pt Ω) (hx : HasUnramifiedDescent O w hw x) (m : ℕ) (hxm : x ^ m = 1) :
    ∃! s : specW O w hw ⟶ N, s ^ m = 1 ∧ genericFibre O w hw e s = x := by
  obtain ⟨s, hs, huniq⟩ := exists_unique_section_of_unramifiedDescent O w hw e hN x hx
  refine ⟨s, ⟨(pow_eq_one_iff_genericFibre O w hw e hgen s m).mpr (by rw [hs]; exact hxm), hs⟩,
    fun s' hs' => huniq s' hs'.2⟩

open scoped Obj in
/-- **Tate level.** An element of `T_ℓ(A)` whose components have unramified descents lifts to a
unique compatible system of `w`-sections. -/
theorem exists_unique_compatible_sections_of_unramifiedDescent [GrpObj N] [IsSeparated N.hom]
    (hgen : letI : GrpObj ((Over.pullback (jO O)).obj N) := Functor.grpObjObj
      IsMonHom e.hom)
    (hN : ∀ (Y : Over (Spec (CommRingCat.of O))) [Smooth Y.hom],
      Function.Bijective fun f : Y ⟶ N => (Over.pullback (jO O)).map f ≫ e.hom)
    (ℓ : ℕ) [Fact ℓ.Prime] (t : PkgI3.Tate.T ℓ (Additive (A.Pt Ω)))
    (ht : ∀ n, HasUnramifiedDescent O w hw (Additive.toMul (t.1 n))) :
    ∃ s : ℕ → (specW O w hw ⟶ N), s 0 = 1 ∧ (∀ n, s (n + 1) ^ ℓ = s n) ∧
      (∀ n, genericFibre O w hw e (s n) = Additive.toMul (t.1 n)) ∧
      ∀ s' : ℕ → (specW O w hw ⟶ N),
        (∀ n, genericFibre O w hw e (s' n) = Additive.toMul (t.1 n)) → s' = s :=
  exists_unique_compatible_sections O w hw e hgen ℓ t (fun n =>
    (exists_unique_section_of_unramifiedDescent O w hw e hN _ (ht n)).exists)

/-- **The remaining arithmetic input, as a statement (not proved here).** Every point of `A(Ω)`
fixed by the inertia group of `w` has an unramified descent. -/
def InertiaFixedUnramified (A : PkgI3.AbVar K) : Prop :=
  ∀ x : A.Pt Ω, (∀ σ : Ω ≃ₐ[K] Ω, PkgI2.IsInertia w σ → A.galAct σ x = x) →
    HasUnramifiedDescent O w hw x

open scoped Obj in
/-- **Inertia-fixed torsion, conditional on `InertiaFixedUnramified`.** -/
theorem inertia_fixed_sections [GrpObj N] [IsSeparated N.hom]
    (hgen : letI : GrpObj ((Over.pullback (jO O)).obj N) := Functor.grpObjObj
      IsMonHom e.hom)
    (hN : ∀ (Y : Over (Spec (CommRingCat.of O))) [Smooth Y.hom],
      Function.Bijective fun f : Y ⟶ N => (Over.pullback (jO O)).map f ≫ e.hom)
    (hU : InertiaFixedUnramified O w hw A)
    (x : A.Pt Ω) (hfix : ∀ σ : Ω ≃ₐ[K] Ω, PkgI2.IsInertia w σ → A.galAct σ x = x)
    (m : ℕ) (hxm : x ^ m = 1) :
    ∃! s : specW O w hw ⟶ N, s ^ m = 1 ∧ genericFibre O w hw e s = x :=
  torsion_section_of_unramifiedDescent O w hw e hgen hN x (hU x hfix) m hxm

end NeronInvariantTorsion
