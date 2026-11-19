import Mathlib
import ZInQKernel.Contrib.RC53Assist.IntegralDuality.TopTraceReduction

/-!
# Pulling a top-degree trace back along a quasi-isomorphism in one degree

Let `φ : K ⟶ L` be a morphism of complexes of `R`-modules (any complex shape, any commutative
ring `R`) which is a quasi-isomorphism in degree `j`, with `c.prev j = i` and `c.next j = k`.
If a functional `tr : L^j → R` kills boundaries, a cycle of trace zero is a boundary, and some
cycle has trace one (`IsTopTraceIso`), then the same holds for `tr ∘ φ^j : K^j → R`
(`isTopTraceIso_comp_of_quasiIsoAt`).

No finiteness, freeness, duality or self-injectivity enters, and no isomorphism of `H^j(K)` with
`R` is assumed: everything comes from the given morphism `φ`.

## Proof
* Boundaries: `tr (φ (d w)) = tr (d (φ w)) = 0`.
* Trace one: let `z` be a cycle of `L` of trace one. Since `H^j(φ)` is onto,
  `z = φ x + d b` for a cycle `x` of `K` (`exists_cycle_lift_of_epi_homologyMap`); then
  `tr (φ x) = tr z - tr (d b) = 1`.
* Trace-zero cycles: if `x` is a cycle with `tr (φ x) = 0`, then the cycle `φ x` is a boundary
  `d y`. Since `H^j(φ)` is injective, `x` is a boundary
  (`exists_boundary_of_mono_homologyMap`).

The two element-level statements are extracted from Mathlib's characterisations of mono and epi
homology maps up to refinements, evaluated on the module `R` itself: a morphism `R ⟶ M` is an
element of `M`, and an epimorphism onto `R` has `1` in its image.
-/

noncomputable section

namespace ZInQ.Contrib.RC53Assist.IntegralDuality

open CategoryTheory HomologicalComplex

universe u

section Elements

variable {R : Type u} [CommRing R]

/-- An element of a module as a morphism out of the ring. -/
def eltHom (M : ModuleCat.{u} R) (m : M) : ModuleCat.of R R ⟶ M :=
  ModuleCat.ofHom (LinearMap.toSpanSingleton R M m)

@[simp]
theorem eltHom_apply (M : ModuleCat.{u} R) (m : M) (r : R) : (eltHom M m).hom r = r • m := rfl

theorem eltHom_one (M : ModuleCat.{u} R) (m : M) :
    (eltHom M m).hom (1 : (ModuleCat.of R R : Type u)) = m := one_smul R m

theorem eltHom_comp {M N : ModuleCat.{u} R} (m : M) (g : M ⟶ N) :
    eltHom M m ≫ g = eltHom N (g.hom m) := by
  ext
  simp [eltHom]

theorem eltHom_eq_zero_iff {M : ModuleCat.{u} R} (m : M) : eltHom M m = 0 ↔ m = 0 := by
  constructor
  · intro h
    have h1 := congrArg (fun g => g.hom (1 : (ModuleCat.of R R : Type u))) h
    rw [eltHom_one] at h1
    exact h1
  · rintro rfl
    ext
    simp [eltHom]

end Elements

section Neg

variable {A : Type*} [CommRing A] {X₀ X₁ X₂ : Type*}
  [AddCommGroup X₀] [Module A X₀] [AddCommGroup X₁] [Module A X₁]
  [AddCommGroup X₂] [Module A X₂]
  {d₀ : X₀ →ₗ[A] X₁} {d₁ : X₁ →ₗ[A] X₂} {tr : X₁ →ₗ[A] A}

/-- Negating both differentials preserves the concrete trace condition. -/
theorem IsTopTraceIso.neg (h : IsTopTraceIso d₀ d₁ tr) : IsTopTraceIso (-d₀) (-d₁) tr := by
  obtain ⟨hbd, hker, z₀, hz₀, htr₀⟩ := h
  refine ⟨fun x => ?_, fun z hz htz => ?_, z₀, ?_, htr₀⟩
  · rw [LinearMap.neg_apply, map_neg, hbd, neg_zero]
  · rw [LinearMap.neg_apply, neg_eq_zero] at hz
    obtain ⟨x, hx⟩ := hker z hz htz
    exact ⟨-x, by rw [LinearMap.neg_apply, map_neg, neg_neg, hx]⟩
  · rw [LinearMap.neg_apply, hz₀, neg_zero]

/-- The concrete trace condition does not see the signs of the differentials. -/
theorem isTopTraceIso_neg_iff : IsTopTraceIso (-d₀) (-d₁) tr ↔ IsTopTraceIso d₀ d₁ tr :=
  ⟨fun h => by simpa only [neg_neg] using h.neg, IsTopTraceIso.neg⟩

end Neg

variable {R : Type u} [CommRing R] {ι : Type*} {c : ComplexShape ι}
  {K L : HomologicalComplex (ModuleCat.{u} R) c} (φ : K ⟶ L)

/-- **Injectivity on cohomology, elementwise.** If `H^j(φ)` is a monomorphism and the image of a
cycle `x` is a boundary, then `x` is a boundary. -/
theorem exists_boundary_of_mono_homologyMap {i j k : ι} (hi : c.prev j = i) (hk : c.next j = k)
    (hmono : Mono (homologyMap φ j)) (x : K.X j) (hx : (K.d j k).hom x = 0) (y : L.X i)
    (hxy : (φ.f j).hom x = (L.d i j).hom y) : ∃ w : K.X i, (K.d i j).hom w = x := by
  obtain ⟨A', π, hπ, x₁, fac⟩ :=
    (mono_homologyMap_iff_up_to_refinements φ i j k hi hk).1 hmono (eltHom _ x)
      (by rw [eltHom_comp, hx, (eltHom_eq_zero_iff _).2 rfl]) (eltHom _ y)
      (by rw [eltHom_comp, eltHom_comp, hxy])
  obtain ⟨a, ha⟩ := (ModuleCat.epi_iff_surjective π).1 hπ 1
  refine ⟨x₁.hom a, ?_⟩
  have h := congrArg (fun g => g.hom a) fac
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply, ha] at h
  rw [eltHom_one] at h
  exact h.symm

/-- **Surjectivity on cohomology, elementwise.** If `H^j(φ)` is an epimorphism, every cycle of `L`
is the image of a cycle of `K` up to a boundary. -/
theorem exists_cycle_lift_of_epi_homologyMap {i j k : ι} (hi : c.prev j = i) (hk : c.next j = k)
    (hepi : Epi (homologyMap φ j)) (y : L.X j) (hy : (L.d j k).hom y = 0) :
    ∃ x : K.X j, (K.d j k).hom x = 0 ∧ ∃ b : L.X i, y = (φ.f j).hom x + (L.d i j).hom b := by
  obtain ⟨A', π, hπ, x₂, hx₂, y₁, fac⟩ :=
    (epi_homologyMap_iff_up_to_refinements φ i j k hi hk).1 hepi (eltHom _ y)
      (by rw [eltHom_comp, hy, (eltHom_eq_zero_iff _).2 rfl])
  obtain ⟨a, ha⟩ := (ModuleCat.epi_iff_surjective π).1 hπ 1
  refine ⟨x₂.hom a, ?_, y₁.hom a, ?_⟩
  · have h := congrArg (fun g => g.hom a) hx₂
    simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at h
    exact h
  · have h := congrArg (fun g => g.hom a) fac
    simp only [ModuleCat.hom_comp, ModuleCat.hom_add, LinearMap.add_apply, LinearMap.comp_apply,
      ha] at h
    rw [eltHom_one] at h
    exact h

/-- **Pullback of a top-degree trace along a quasi-isomorphism in degree `j`.** -/
theorem isTopTraceIso_comp_of_quasiIsoAt {i j k : ι} (hi : c.prev j = i) (hk : c.next j = k)
    (hf : QuasiIsoAt φ j) (tr : L.X j →ₗ[R] R)
    (htr : IsTopTraceIso (L.d i j).hom (L.d j k).hom tr) :
    IsTopTraceIso (K.d i j).hom (K.d j k).hom (tr ∘ₗ (φ.f j).hom) := by
  have hiso : IsIso (homologyMap φ j) := (quasiIsoAt_iff_isIso_homologyMap φ j).1 hf
  obtain ⟨hbd, hker, z₀, hz₀, htr₀⟩ := htr
  have hcomm : ∀ (p q : ι) (w : K.X p), (φ.f q).hom ((K.d p q).hom w) = (L.d p q).hom
      ((φ.f p).hom w) := fun p q w => by
    have h := congrArg (fun g => g.hom w) (φ.comm p q)
    simpa only [ModuleCat.hom_comp, LinearMap.comp_apply] using h.symm
  refine ⟨fun w => ?_, fun x hx htx => ?_, ?_⟩
  · rw [LinearMap.comp_apply, hcomm, hbd]
  · have hcyc : (L.d j k).hom ((φ.f j).hom x) = 0 := by rw [← hcomm, hx, map_zero]
    obtain ⟨y, hy⟩ := hker _ hcyc htx
    exact exists_boundary_of_mono_homologyMap φ hi hk inferInstance x hx y hy.symm
  · obtain ⟨x, hx, b, hb⟩ := exists_cycle_lift_of_epi_homologyMap φ hi hk inferInstance z₀ hz₀
    refine ⟨x, hx, ?_⟩
    rw [LinearMap.comp_apply]
    have h := congrArg tr hb
    rw [map_add, hbd, add_zero, htr₀] at h
    exact h.symm

/-- The same for cochain complexes indexed by `ℤ`, with the top degree `j` and `i + 1 = j`,
`j + 1 = k`. -/
theorem isTopTraceIso_comp_of_quasiIsoAt_int {K L : CochainComplex (ModuleCat.{u} R) ℤ}
    (φ : K ⟶ L) {i j k : ℤ} (hij : i + 1 = j) (hjk : j + 1 = k) (hf : QuasiIsoAt φ j)
    (tr : L.X j →ₗ[R] R) (htr : IsTopTraceIso (L.d i j).hom (L.d j k).hom tr) :
    IsTopTraceIso (K.d i j).hom (K.d j k).hom (tr ∘ₗ (φ.f j).hom) :=
  isTopTraceIso_comp_of_quasiIsoAt φ ((ComplexShape.up ℤ).prev_eq' hij)
    ((ComplexShape.up ℤ).next_eq' hjk) hf tr htr

end ZInQ.Contrib.RC53Assist.IntegralDuality
