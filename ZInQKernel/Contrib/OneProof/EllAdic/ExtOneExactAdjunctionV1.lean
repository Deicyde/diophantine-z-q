import Mathlib.Algebra.Homology.DerivedCategory.Ext.EnoughInjectives
import Mathlib.Algebra.Homology.DerivedCategory.Ext.ExactSequences
import Mathlib.Algebra.Homology.DerivedCategory.Ext.Map
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Kernels
import Mathlib.CategoryTheory.Preadditive.Injective.Basic

set_option autoImplicit false

open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits

namespace RC53.EllAdic

universe u v w u' v' w'

variable {C : Type u} [Category.{v} C] [Abelian C] [HasExt.{w} C]

/-- The connecting map from actual arrows into the last term of the short
exact sequence, with the convention of `extClass`. -/
noncomputable def homToExtOne (T : ShortComplex C) (h : T.ShortExact) (X : C)
    (a : X ⟶ T.X₃) : Ext.{w} X T.X₁ 1 :=
  (Ext.mk₀ a).comp h.extClass (zero_add 1)

theorem homToExtOne_surjective (T : ShortComplex C) (h : T.ShortExact) (X : C)
    [Injective T.X₂] : Function.Surjective (homToExtOne T h X) := by
  intro x
  have hz : x.comp (Ext.mk₀ T.f) (add_zero 1) = 0 := Ext.eq_zero_of_injective _
  obtain ⟨b, hb⟩ := Ext.covariant_sequence_exact₁ X h x hz (n₀ := 0) rfl
  refine ⟨Ext.homEquiv₀ b, ?_⟩
  exact (congrArg (fun z : Ext.{w} X T.X₃ 0 => z.comp h.extClass (zero_add 1))
    (Ext.mk₀_homEquiv₀_apply b)).trans hb

theorem homToExtOne_eq_zero_iff (T : ShortComplex C) (h : T.ShortExact) (X : C)
    (a : X ⟶ T.X₃) : homToExtOne T h X a = 0 ↔ ∃ b : X ⟶ T.X₂, b ≫ T.g = a := by
  let d (Z : C) := (Ext.mk₀ (X := X) (Y := Z))
  constructor
  · intro hzero
    obtain ⟨x, hx⟩ := Ext.covariant_sequence_exact₃ X h (d T.X₃ a) (zero_add 1) hzero
    refine ⟨Ext.homEquiv₀ x, (Ext.mk₀_bijective X T.X₃).injective ?_⟩
    exact (Ext.mk₀_comp_mk₀ (Ext.homEquiv₀ x) T.g).symm.trans
      ((congrArg (fun k : Ext.{w} X T.X₂ 0 => k.comp (Ext.mk₀ T.g) (add_zero 0))
        (Ext.mk₀_homEquiv₀_apply x)).trans hx)
  · rintro ⟨b, rfl⟩
    have ex := (ShortComplex.ab_exact_iff_function_exact _).1 (Ext.covariant_sequence_exact₃' X h 0 1 rfl)
    change Function.Exact (fun k : Ext.{w} X T.X₂ 0 => k.comp (Ext.mk₀ T.g) (add_zero 0))
      (fun k : Ext.{w} X T.X₃ 0 => k.comp h.extClass (zero_add 1)) at ex
    exact (ex (Ext.mk₀ (b ≫ T.g))).2 ⟨Ext.mk₀ b, Ext.mk₀_comp_mk₀ b T.g⟩

variable {D : Type u'} [Category.{v'} D] [Abelian D] [HasExt.{w'} D]

/-- To compare degree one in an exact adjunction it suffices to preserve
one injective cokernel sequence. The right adjoint need not be exact. -/
theorem mapExtOne_bijective_of_specific_epi
    {L : C ⥤ D} {G : D ⥤ C} (adj : L ⊣ G)
    [L.Additive] [PreservesFiniteLimits L] [PreservesFiniteColimits L]
    (X A : C) {I Q : D} [Injective I]
    (i : L.obj A ⟶ I) [Mono i] (p : I ⟶ Q)
    (hip : i ≫ p = 0) (hp : IsColimit (CokernelCofork.ofπ p hip))
    [IsIso (adj.unit.app A)] [Epi (G.map p)] :
    Function.Bijective (L.mapExtAddHom X A 1) := by
  let S := ShortComplex.mk i p hip
  have hS : S.ShortExact := ShortComplex.ShortExact.mk'
    (ShortComplex.exact_of_g_is_cokernel S hp) (inferInstance : Mono i) (Cofork.IsColimit.epi hp)
  let : PreservesLimits G := adj.rightAdjoint_preservesLimits
  let T := ShortComplex.mk (adj.unit.app A ≫ G.map i) (G.map p) (by
    rw [Category.assoc, ← G.map_comp, hip, G.map_zero, Limits.comp_zero])
  let isoA : A ≅ G.obj (L.obj A) := asIso (adj.unit.app A)
  have kS := KernelFork.mapIsLimit _ hS.fIsKernel G
  have kT : IsLimit (KernelFork.ofι T.f T.zero) :=
    IsKernel.isoKernel (G.map p) T.f kS isoA rfl
  have hT : T.ShortExact := ShortComplex.ShortExact.mk'
    (ShortComplex.exact_of_f_is_kernel T kT) (Fork.IsLimit.mono kT) (inferInstance : Epi (G.map p))
  let : Injective (G.obj I) := adj.map_injective I inferInstance
  let e (J : D) := (adj.homEquiv X J).symm
  let φ : T.map L ⟶ S := ShortComplex.homMk (𝟙 (L.obj A)) (adj.counit.app I) (adj.counit.app Q)
    (by
      change 𝟙 (L.obj A) ≫ i = L.map (adj.unit.app A ≫ G.map i) ≫ adj.counit.app I
      have hn : L.map (G.map i) ≫ adj.counit.app I = adj.counit.app (L.obj A) ≫ i :=
        adj.counit.naturality i
      have ht : L.map (adj.unit.app A) ≫ adj.counit.app (L.obj A) = 𝟙 (L.obj A) :=
        adj.left_triangle_components A
      rw [Category.id_comp, L.map_comp, Category.assoc, hn, ← Category.assoc, ht]
      exact (Category.id_comp i).symm)
    (by
      change adj.counit.app I ≫ p = L.map (G.map p) ≫ adj.counit.app Q
      exact (adj.counit.naturality p).symm)
  have hc : (hT.map_of_exact L).extClass = (Ext.mk₀ (adj.counit.app Q)).comp hS.extClass (zero_add 1) := by
    have h := (hT.map_of_exact L).extClass_naturality hS φ
    change ((hT.map_of_exact L).extClass).comp (Ext.mk₀ (𝟙 (L.obj A))) (add_zero 1) = _ at h
    exact (Ext.comp_mk₀_id (hT.map_of_exact L).extClass).symm.trans h
  have hcomm (q : X ⟶ G.obj Q) :
      L.mapExtAddHom X A 1 (homToExtOne T hT X q) = homToExtOne S hS (L.obj X) (e Q q) := by
    simp only [homToExtOne, e, Functor.mapExtAddHom_apply, Ext.mapExactFunctor_comp,
      Ext.mapExactFunctor_mk₀, Ext.mapExactFunctor_extClass, hc,
      Ext.mk₀_comp_mk₀_assoc, Adjunction.homEquiv_counit]
  have hzero (x : Ext.{w} X A 1) (hx : L.mapExtAddHom X A 1 x = 0) : x = 0 := by
    obtain ⟨q, rfl⟩ := homToExtOne_surjective T hT X x
    have hz := (hcomm q).symm.trans hx
    obtain ⟨b, hb⟩ := (homToExtOne_eq_zero_iff S hS (L.obj X) (e Q q)).1 hz
    let c := (e I).symm b
    have hcp : c ≫ G.map p = q := by
      apply (e Q).injective
      exact (adj.homEquiv_naturality_right_symm c p).trans
        ((congrArg (fun k => k ≫ p) ((e I).apply_symm_apply b)).trans hb)
    exact (homToExtOne_eq_zero_iff T hT X q).2 ⟨c, hcp⟩
  constructor
  · intro x y hxy
    have hxy' : L.mapExtAddHom X A 1 (x - y) = 0 := by rw [map_sub, hxy, sub_self]
    exact sub_eq_zero.mp (hzero (x - y) hxy')
  · intro y
    obtain ⟨q, hq⟩ := homToExtOne_surjective S hS (L.obj X) y
    obtain ⟨b, hb⟩ := (e Q).surjective q
    exact ⟨homToExtOne T hT X b, (hcomm b).trans
      ((congrArg (homToExtOne S hS (L.obj X)) hb).trans hq)⟩

end RC53.EllAdic
