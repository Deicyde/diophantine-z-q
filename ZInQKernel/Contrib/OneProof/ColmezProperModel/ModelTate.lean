import ZInQKernel.Contrib.OneProof.ColmezProperModel.Colmez

/-!
# Colmez's `T_p(X) = lim 𝒳(O_{C_p})[pⁿ]` for a proper model

Fix an abelian variety `A` over a finite `F/ℚ_p` and a proper model `π : 𝒳 ⟶ Spec O_F` of `A`
(`e`, `he` as in `Colmez.lean`). Colmez (p. 638) transports the group law of `X(C_p)` to
`𝒳(O_{C_p})` along "Par construction, 𝒳(O_{C_p}) s'identifie à X(C_p)" and builds `T_p(X)` from
the points `u_n ∈ 𝒳(O_{C_p})` (p. 639). This file does the same in Lean:

* `ModelGrp A π e he`: `𝒳(O_{C_p})` with the group law transported along `modelPtsEquiv`;
  `galModelHom σ`: the geometric action `x ↦ Spec (oAct (gfToGqp σ)) ≫ x` is a group
  automorphism.
* `TModel A π e he = lim 𝒳(O_{C_p})[pⁿ]` and `galTModel`: Colmez's `T_p(X)` with its `G_F`-action.
* **`tModelEquiv`**, **`tModelEquiv_gal`**: `TModel ≃ₗ[ℤ_p] TCp p A`, `G_F`-equivariantly, where
  `TCp p A` is the tree's `T_p` built from `A(ℂ_p)` (`ColmezTorsionIso/Basic.lean`).
* `shape_transport`: the shape of the Colmez rows (values in a subset, Galois compatibility,
  non-degeneracy after base change) is invariant under an equivariant isomorphism of the
  `T_p`-side.
-/

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ZInQ.Contrib.ColmezTorsionIso (algCp cpGal TCp galTCp)
open scoped TensorProduct

set_option linter.unusedSectionVars false

noncomputable section

namespace ZInQ.Contrib.ColmezProperModel

/-! ## Transport of the row's shape along an isomorphism of the `T_p`-side -/

section Shape

variable {R B T T' : Type*} [CommRing R] [CommRing B] [Algebra R B] [AddCommGroup T] [Module R T]
  [AddCommGroup T'] [Module R T']

theorem liftBaseChange_comp_apply (l : T' →ₗ[R] B) (ψ : T →ₗ[R] T') (x : B ⊗[R] T) :
    (l ∘ₗ ψ).liftBaseChange B x = l.liftBaseChange B (ψ.baseChange B x) := by
  induction x using TensorProduct.inductionOn with
  | tmul a m => simp
  | add x y hx hy => rw [map_add, map_add, map_add, hx, hy]

/-- **The shape of the Colmez rows is invariant under an equivariant isomorphism `T ≃ T'`.** -/
theorem shape_transport {G : Type*} (ψ : T ≃ₗ[R] T') (g : G → T →ₗ[R] T) (g' : G → T' →ₗ[R] T')
    (hψ : ∀ σ u, ψ (g σ u) = g' σ (ψ u)) (Q : B → Prop) (act : G → B → B) :
    (∃ (H : Type) (P : H → (T' →ₗ[R] B)), (∀ ω u, Q (P ω u)) ∧
      (∀ ω σ u, P ω (g' σ u) = act σ (P ω u)) ∧
      (∀ x : B ⊗[R] T', (∀ ω, (P ω).liftBaseChange B x = 0) → x = 0)) ↔
    (∃ (H : Type) (P : H → (T →ₗ[R] B)), (∀ ω u, Q (P ω u)) ∧
      (∀ ω σ u, P ω (g σ u) = act σ (P ω u)) ∧
      (∀ x : B ⊗[R] T, (∀ ω, (P ω).liftBaseChange B x = 0) → x = 0)) := by
  have hψ' : ∀ σ u, ψ.symm (g' σ u) = g σ (ψ.symm u) := fun σ u => by
    apply ψ.injective
    rw [LinearEquiv.apply_symm_apply, hψ, LinearEquiv.apply_symm_apply]
  constructor
  · rintro ⟨H, P, hQ, hG, hN⟩
    refine ⟨H, fun ω => P ω ∘ₗ (ψ : T →ₗ[R] T'), fun ω u => hQ ω (ψ u), fun ω σ u => ?_,
      fun x hx => ?_⟩
    · change P ω (ψ (g σ u)) = act σ (P ω (ψ u))
      rw [hψ, hG]
    · have h0 : (ψ.baseChange R B T T') x = 0 :=
        hN _ fun ω => by rw [← hx ω, liftBaseChange_comp_apply]; rfl
      exact (ψ.baseChange R B T T').injective (h0.trans (map_zero _).symm)
  · rintro ⟨H, P, hQ, hG, hN⟩
    refine ⟨H, fun ω => P ω ∘ₗ (ψ.symm : T' →ₗ[R] T), fun ω u => hQ ω (ψ.symm u),
      fun ω σ u => ?_, fun x hx => ?_⟩
    · change P ω (ψ.symm (g' σ u)) = act σ (P ω (ψ.symm u))
      rw [hψ', hG]
    · have h0 : (ψ.symm.baseChange R B T' T) x = 0 :=
        hN _ fun ω => by rw [← hx ω, liftBaseChange_comp_apply]; rfl
      exact (ψ.symm.baseChange R B T' T).injective (h0.trans (map_zero _).symm)

end Shape

/-! ## The group `𝒳(O_{C_p})` and its Tate module -/

section ModelTate

variable {p : ℕ} [Fact p.Prime] {F : Type} [Field F] [Algebra ℚ_[p] F] [FiniteDimensional ℚ_[p] F]

attribute [local instance] algCp

variable (A : ZInQ.Contrib.G9.PkgI4.I3.AbVar F) {𝒳 : Scheme}
  (π : 𝒳 ⟶ Spec (CommRingCat.of (OF p F))) [IsProper π]
  (e : pullback π (Spec.map (CommRingCat.ofHom (algebraMap (OF p F) F))) ≅ A.X.left)
  (he : e.hom ≫ A.X.hom = pullback.snd _ _)

/-- `𝒳(O_{C_p})`, to carry the group law of `A(ℂ_p)` transported along `modelPtsEquiv`. -/
@[nolint unusedArguments]
def ModelGrp (A : ZInQ.Contrib.G9.PkgI4.I3.AbVar F) {𝒳 : Scheme}
    (π : 𝒳 ⟶ Spec (CommRingCat.of (OF p F))) [IsProper π]
    (e : pullback π (Spec.map (CommRingCat.ofHom (algebraMap (OF p F) F))) ≅ A.X.left)
    (_he : e.hom ≫ A.X.hom = pullback.snd _ _) : Type :=
  ModelPtsCp p F π

instance : CommGroup (ModelGrp A π e he) :=
  (modelPtsEquiv A π e he).commGroup

/-- `𝒳(O_{C_p}) ≃* A(ℂ_p)`. -/
def modelMulEquiv : ModelGrp A π e he ≃* A.Pt ℂ_[p] where
  toEquiv := modelPtsEquiv A π e he
  map_mul' _ _ := (modelPtsEquiv A π e he).apply_symm_apply _

theorem modelMulEquiv_apply (x : ModelGrp A π e he) :
    modelMulEquiv A π e he x = modelPtsEquiv A π e he x := rfl

/-- `σ ∈ G_F` acting on `ModelGrp`: the geometric action `galModel`. -/
def galModelGrp (σ : Field.absoluteGaloisGroup F) (x : ModelGrp A π e he) : ModelGrp A π e he :=
  galModel p F π σ x

theorem modelMulEquiv_galModelGrp (σ : Field.absoluteGaloisGroup F) (x : ModelGrp A π e he) :
    modelMulEquiv A π e he (galModelGrp A π e he σ x) =
      A.galAct (cpGal p F σ) (modelMulEquiv A π e he x) :=
  modelPtsEquiv_gal A π e he σ x

/-- **The geometric action of `σ ∈ G_F` on `𝒳(O_{C_p})` is a group automorphism.** -/
def galModelHom (σ : Field.absoluteGaloisGroup F) : ModelGrp A π e he →* ModelGrp A π e he where
  toFun := galModelGrp A π e he σ
  map_one' := by
    apply (modelMulEquiv A π e he).injective
    rw [modelMulEquiv_galModelGrp]
    simp only [map_one]
  map_mul' x y := by
    apply (modelMulEquiv A π e he).injective
    simp only [map_mul, modelMulEquiv_galModelGrp]

theorem galModelHom_apply (σ : Field.absoluteGaloisGroup F) (x : ModelGrp A π e he) :
    galModelHom A π e he σ x = galModel p F π σ x := rfl

/-- **Colmez's `T_p(X) = lim 𝒳(O_{C_p})[pⁿ]`**, a `ℤ_p`-module. -/
abbrev TModel : Type :=
  ZInQ.Contrib.G9.PkgI4.I3.Tate.T p (Additive (ModelGrp A π e he))

/-- `σ ∈ G_F` acting on `TModel`, through its geometric action on `𝒳(O_{C_p})`. -/
def galTModel (σ : Field.absoluteGaloisGroup F) : TModel A π e he →ₗ[ℤ_[p]] TModel A π e he :=
  ZInQ.Contrib.G9.PkgI4.I3.Tate.map (MonoidHom.toAdditive (galModelHom A π e he σ))

/-- `T_p(𝒳(O_{C_p})) → T_p(A(ℂ_p))`. -/
def tModelMap : TModel A π e he →ₗ[ℤ_[p]] TCp p A :=
  ZInQ.Contrib.G9.PkgI4.I3.Tate.map
    (MonoidHom.toAdditive (modelMulEquiv A π e he).toMonoidHom)

theorem tModelMap_bijective : Function.Bijective (tModelMap A π e he) :=
  ZInQ.Contrib.ColmezTorsionIso.tate_map_bijective _
    (modelMulEquiv A π e he).injective fun _ q _ =>
      ⟨Additive.ofMul ((modelMulEquiv A π e he).symm (Additive.toMul q)),
        congrArg Additive.ofMul ((modelMulEquiv A π e he).apply_symm_apply _)⟩

/-- **`T_p(X)` from `𝒳(O_{C_p})` is the tree's `T_p` from `A(ℂ_p)`.** -/
def tModelEquiv : TModel A π e he ≃ₗ[ℤ_[p]] TCp p A :=
  LinearEquiv.ofBijective (tModelMap A π e he) (tModelMap_bijective A π e he)

/-- **`tModelEquiv` is `G_F`-equivariant.** -/
theorem tModelEquiv_gal (σ : Field.absoluteGaloisGroup F) (u : TModel A π e he) :
    tModelEquiv A π e he (galTModel A π e he σ u) = galTCp p A σ (tModelEquiv A π e he u) := by
  apply Subtype.ext
  funext n
  exact congrArg Additive.ofMul (modelPtsEquiv_gal A π e he σ (Additive.toMul (u.1 n)))

end ModelTate

end ZInQ.Contrib.ColmezProperModel

end
