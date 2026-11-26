import ZInQKernel.Contrib.OneProof.SemistablePrintedReadings
import Mathlib.AlgebraicGeometry.Artinian

noncomputable section

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ZInQ.DefFaltings

namespace ZInQ.SemistabAssembly

/-- Gaudron–Rémond, *Polarisations et isogénies*, Duke Math. J. 163 (2014), Théorème 1.4 (p. 2060; κ and α(g) = 2^10 g^3 on p. 2058, where g ≥ 1 is a standing assumption), in the same reading as `GaudronRemondThm14AnSS` (printed semistability), for g ≥ 1 as printed. -/
def GaudronRemondThm14AnSSPos : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (A B : PkgI3.AbVar K) (g : ℕ) (x : ℝ),
    1 ≤ g → A.dim = (g : WithBot ℕ∞) → IsAnStableHeightSS A x →
    (∃ φ : A.X ⟶ B.X, IsIsogeny φ) →
    (∃ φ : A.X ⟶ B.X, IsIsogeny φ ∧ (isogDeg φ : ℝ) ≤ grKappa g (Module.finrank ℚ K) x) ∧
    (∃ ψ : B.X ⟶ A.X, IsIsogeny ψ ∧ (isogDeg ψ : ℝ) ≤ grKappa g (Module.finrank ℚ K) x)

private theorem subsingleton_of_dim_zero {K : Type} [Field K] (A : PkgI3.AbVar K)
    (hA : A.dim = 0) : Subsingleton A.X.left := by
  have : IsIntegral A.X.left :=
    GeometricallyIntegral.isIntegral_of_subsingleton A.X.hom
  have : IsLocallyNoetherian A.X.left :=
    LocallyOfFiniteType.isLocallyNoetherian A.X.hom
  have : IsLocallyArtinian A.X.left :=
    IsLocallyArtinian.of_topologicalKrullDim_le_zero (by simpa [PkgI3.AbVar.dim] using hA.le)
  exact ⟨fun x y => DiscreteTopology.isDiscrete.subsingleton_of_isPreirreducible
    PreirreducibleSpace.isPreirreducible_univ (Set.mem_univ x) (Set.mem_univ y)⟩

private theorem isIso_struct_of_subsingleton {K : Type} [Field K] (A : PkgI3.AbVar K)
    [Subsingleton A.X.left] : IsIso A.X.hom := by
  have : IsIntegral A.X.left :=
    GeometricallyIntegral.isIntegral_of_subsingleton A.X.hom
  let := (isField_of_isIntegral_of_subsingleton A.X.left).toField
  let e : Spec (CommRingCat.of K) ⟶ A.X.left :=
    (η[A.X] : 𝟙_ (Over (Spec (CommRingCat.of K))) ⟶ A.X).left
  have he : e ≫ A.X.hom = 𝟙 _ := Over.w (η[A.X])
  have : Mono e.appTop := by
    constructor
    intro Z f g h
    ext z
    exact e.appTop.hom.injective
      (congrArg (fun t : Z ⟶ Γ(Spec (CommRingCat.of K), ⊤) => t z) h)
  have hr : A.X.hom ≫ e = 𝟙 _ := by
    apply ext_of_isAffine
    rw [Scheme.Hom.comp_appTop, Scheme.Hom.id_appTop]
    apply (cancel_mono e.appTop).1
    rw [Category.assoc, ← Scheme.Hom.comp_appTop, he, Scheme.Hom.id_appTop]
    simp
  exact ⟨⟨e, hr, he⟩⟩

private theorem hom_subsingleton_of_isIso {K : Type} [Field K] (A : PkgI3.AbVar K)
    [IsIso A.X.hom] (P : Over (Spec (CommRingCat.of K))) : Subsingleton (P ⟶ A.X) := by
  constructor
  intro f g
  apply Over.OverMorphism.ext
  apply (cancel_mono A.X.hom).1
  rw [Over.w f, Over.w g]

private theorem isIso_left_of_struct {K : Type} [Field K] (A B : PkgI3.AbVar K)
    [IsIso A.X.hom] [IsIso B.X.hom] (f : A.X ⟶ B.X) : IsIso f.left := by
  have hf : f.left = A.X.hom ≫ inv B.X.hom := by
    rw [← Over.w f]
    simp
  rw [hf]
  infer_instance

private theorem degree_le_one {K : Type} [Field K] (A B : PkgI3.AbVar K)
    [IsIso A.X.hom] (f : A.X ⟶ B.X) : isogDeg f ≤ 1 := by
  have : Subsingleton (ptObj K (AlgebraicClosure K) ⟶ A.X) :=
    hom_subsingleton_of_isIso A _
  unfold isogDeg
  simpa using Nat.card_le_card_of_injective
    (fun (_ : {P : ptObj K (AlgebraicClosure K) ⟶ A.X // P ≫ f = 1}) => Unit.unit)
    (fun _ _ _ => Subsingleton.elim _ _)

private theorem isogenies_of_dim_zero {K : Type} [Field K] (A B : PkgI3.AbVar K)
    (hA : A.dim = 0) (hiso : ∃ f : A.X ⟶ B.X, IsIsogeny f) :
    (∃ φ : A.X ⟶ B.X, IsIsogeny φ ∧ (isogDeg φ : ℝ) ≤ 1) ∧
    (∃ ψ : B.X ⟶ A.X, IsIsogeny ψ ∧ (isogDeg ψ : ℝ) ≤ 1) := by
  have : Subsingleton A.X.left := subsingleton_of_dim_zero A hA
  obtain ⟨f, _, _, hf⟩ := hiso
  have : Subsingleton B.X.left := hf.surj.subsingleton
  have : IsIso A.X.hom := isIso_struct_of_subsingleton A
  have : IsIso B.X.hom := isIso_struct_of_subsingleton B
  let φ : A.X ⟶ B.X := toUnit A.X ≫ η[B.X]
  let ψ : B.X ⟶ A.X := toUnit B.X ≫ η[A.X]
  have : IsIso φ.left := isIso_left_of_struct A B φ
  have : IsIso ψ.left := isIso_left_of_struct B A ψ
  have hφ : IsIsogeny φ := by
    refine ⟨?_, inferInstance, inferInstance⟩
    dsimp [φ]
    infer_instance
  have hψ : IsIsogeny ψ := by
    refine ⟨?_, inferInstance, inferInstance⟩
    dsimp [ψ]
    infer_instance
  refine ⟨⟨φ, hφ, ?_⟩, ⟨ψ, hψ, ?_⟩⟩
  · exact_mod_cast degree_le_one A B φ
  · exact_mod_cast degree_le_one B A ψ

theorem gaudronRemondThm14AnSS_of_pos (h : GaudronRemondThm14AnSSPos) :
    GaudronRemondThm14AnSS := by
  intro K _ _ A B g x hg hx hiso
  by_cases hp : 1 ≤ g
  · exact h K A B g x hp hg hx hiso
  · have hg0 : g = 0 := by omega
    subst g
    simpa [grKappa] using isogenies_of_dim_zero A B (by simpa using hg) hiso

end ZInQ.SemistabAssembly
