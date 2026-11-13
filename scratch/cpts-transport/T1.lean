import TailF

#check @HSyn.G0Split.FibreQM.CPtsTransport
#check @UnramTate.bcPt
#check @G0FibreSimple.rigidityHom
#print GlueAssembly.NF

noncomputable section

namespace HSyn

namespace G0Split

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ZInQ ZInQ.JHeight LeafQM.AV ZInQ.DefFaltings

namespace FibreQM

open ZInQ.LeafPush2 (CPts cptObj IsUniformization cDom cEvalAt)
open scoped CategoryTheory.Obj

namespace CPtsT

/-- `appLE` along a factorization `f = x ≫ T`. -/
theorem appLE_of_eq {X Y Z : Scheme} (f : X ⟶ Z) (x : X ⟶ Y) (T : Y ⟶ Z) (h : f = x ≫ T)
    (U : Z.Opens) (hf : ⊤ ≤ f ⁻¹ᵁ U) (hx : ⊤ ≤ x ⁻¹ᵁ (T ⁻¹ᵁ U)) (s : Γ(Z, U)) :
    f.appLE U ⊤ hf s = x.appLE (T ⁻¹ᵁ U) ⊤ hx (T.app U s) := by
  subst h
  rw [Scheme.Hom.comp_appLE]
  rfl

/-- Values of regular functions along a factorization of complex points. -/
theorem cEvalAt_of_eq {K K' : Type} [Field K] [Field K'] {A : PkgI3.AbVar K}
    {B : PkgI3.AbVar K'} {σ : K →+* ℂ} {τ : K' →+* ℂ} (p : CPts A σ) (x : CPts B τ)
    (T : B.X.left ⟶ A.X.left) (h : p.left = x.left ≫ T) (U : A.X.left.Opens)
    (s : Γ(A.X.left, U)) :
    (⊤ ≤ p.left ⁻¹ᵁ U ↔ ⊤ ≤ x.left ⁻¹ᵁ (T ⁻¹ᵁ U)) ∧
      (⊤ ≤ x.left ⁻¹ᵁ (T ⁻¹ᵁ U) → cEvalAt p U s = cEvalAt x (T ⁻¹ᵁ U) (T.app U s)) := by
  have hpre : p.left ⁻¹ᵁ U = x.left ⁻¹ᵁ (T ⁻¹ᵁ U) := by rw [h]; rfl
  refine ⟨⟨fun hh => le_of_le_of_eq hh hpre, fun hh => le_of_le_of_eq hh hpre.symm⟩, fun hx => ?_⟩
  have hp : ⊤ ≤ p.left ⁻¹ᵁ U := hpre ▸ hx
  simp only [cEvalAt, dif_pos hp, dif_pos hx]
  rw [appLE_of_eq p.left x.left T h U hp hx s]
  rfl

end CPtsT

namespace CPtsT

/-- **Complex points of a pullback (proved).** If `T0 : Q → A` makes `Q/ℂ` a pullback of `A/K`
along `σ : K → ℂ`, then `Q(ℂ) ≃* A(ℂ)_σ` compatibly with regular functions. The group isomorphism
is `x ↦ (x ≫ φ)` followed by the adjunction bijection `bcPt`, where `φ = E - E(0)` for the scheme
isomorphism `E : Q ≅ A_ℂ` of the two pullbacks; `φ` is a homomorphism by rigidity
(`G0FibreSimple.rigidityHom`). -/
theorem cPts_of_isPullback {K : Type} [Field K] (A : PkgI3.AbVar K) (σ : K →+* ℂ)
    (Q : PkgI3.AbVar ℂ) (T0 : Q.X.left ⟶ A.X.left)
    (S : IsPullback T0 Q.X.hom A.X.hom (Spec.map (CommRingCat.ofHom σ))) :
    ∃ ψ : CPts Q (RingHom.id ℂ) ≃* CPts A σ,
      ∀ (U : A.X.left.Opens) (s : Γ(A.X.left, U)),
        ∃ (U' : Q.X.left.Opens) (s' : Γ(Q.X.left, U')),
          ∀ x : CPts Q (RingHom.id ℂ), (⊤ ≤ (ψ x).left ⁻¹ᵁ U ↔ ⊤ ≤ x.left ⁻¹ᵁ U') ∧
            (⊤ ≤ x.left ⁻¹ᵁ U' → cEvalAt (ψ x) U s = cEvalAt x U' s') := by
  letI iC : Algebra K ℂ := σ.toAlgebra
  let B : PkgI3.AbVar ℂ := A.baseChange ℂ
  have S4 : IsPullback (pullback.fst A.X.hom (Spec.map (CommRingCat.ofHom σ)) :
      B.X.left ⟶ A.X.left) B.X.hom A.X.hom (Spec.map (CommRingCat.ofHom σ)) :=
    IsPullback.of_hasPullback _ _
  let E0 : Q.X.left ≅ B.X.left := S.isoIsPullback _ _ S4
  let E : Q.X ≅ B.X := Over.isoMk E0 (S.isoIsPullback_hom_snd _ _ S4)
  -- recentre at the identity and apply rigidity
  let b : 𝟙_ (Over (Spec (CommRingCat.of ℂ))) ⟶ B.X := η[Q.X] ≫ E.hom
  let φ : Q.X ⟶ B.X := E.hom * (toUnit Q.X ≫ b⁻¹)
  let φ' : B.X ⟶ Q.X := (𝟙 B.X * (toUnit B.X ≫ b)) ≫ E.inv
  have hu : η[Q.X] ≫ toUnit Q.X = 𝟙 _ := toUnit_unique _ _
  have h1 : φ ≫ φ' = 𝟙 Q.X := by
    simp only [φ, φ']
    rw [← Category.assoc, MonObj.comp_mul, Category.comp_id,
      ← Category.assoc, toUnit_unique ((E.hom * (toUnit Q.X ≫ b⁻¹)) ≫ toUnit B.X) (toUnit Q.X),
      _root_.mul_assoc, ← MonObj.comp_mul, inv_mul_cancel, MonObj.comp_one, _root_.mul_one,
      E.hom_inv_id]
  have h2 : φ' ≫ φ = 𝟙 B.X := by
    have k1 : φ' ≫ E.hom = 𝟙 B.X * (toUnit B.X ≫ b) := by
      simp only [φ']
      rw [Category.assoc, E.inv_hom_id, Category.comp_id]
    have k2 : φ' ≫ toUnit Q.X ≫ b⁻¹ = toUnit B.X ≫ b⁻¹ := by
      rw [← Category.assoc, toUnit_unique (φ' ≫ toUnit Q.X) (toUnit B.X)]
    simp only [φ]
    rw [MonObj.comp_mul, k1, k2, _root_.mul_assoc, ← MonObj.comp_mul, mul_inv_cancel,
      MonObj.comp_one, _root_.mul_one]
  have h3 : η[Q.X] ≫ φ = η[B.X] := by
    simp only [φ]
    rw [MonObj.comp_mul, ← Category.assoc, hu, Category.id_comp, mul_inv_cancel,
      MonObj.one_eq_one]
  haveI hφ : IsMonHom φ := G0FibreSimple.rigidityHom ℂ Q B φ h3
  let m : CPts Q (RingHom.id ℂ) ≃* CPts B (RingHom.id ℂ) :=
    { toFun := fun x => x ≫ φ
      invFun := fun y => y ≫ φ'
      left_inv := fun x => (Category.assoc x φ φ').trans (by rw [h1, Category.comp_id])
      right_inv := fun y => (Category.assoc y φ' φ).trans (by rw [h2, Category.comp_id])
      map_mul' := fun x y => MonObj.mul_comp x y φ }
  let bc : CPts B (RingHom.id ℂ) ≃* CPts A σ :=
    @UnramTate.bcPt K ℂ _ _ iC A ℂ _ (Algebra.id ℂ) iC IsScalarTower.right
  let T : Q.X.left ⟶ A.X.left := φ.left ≫ pullback.fst A.X.hom (Spec.map (CommRingCat.ofHom σ))
  have hT : ∀ x : CPts Q (RingHom.id ℂ), (bc (m x)).left = x.left ≫ T := by
    intro x
    show 𝟙 _ ≫ (x ≫ φ).left ≫ pullback.fst A.X.hom (Spec.map (CommRingCat.ofHom σ)) = _
    rw [Category.id_comp]
    rfl
  exact ⟨m.trans bc, fun U s =>
    ⟨T ⁻¹ᵁ U, T.app U s, fun x => cEvalAt_of_eq _ x T (hT x) U s⟩⟩

end CPtsT

open CPtsT in
/-- **`CPtsTransport` holds** (proved from `cPts_of_isPullback` by pasting pullback squares). -/
theorem cPtsTransport_proof : CPtsTransport := by
  intro K A emb P hiso ιe Q hQ
  obtain ⟨e⟩ := hiso
  obtain ⟨g, hpb, -, -⟩ := hQ
  letI iQ : Algebra K.K Qbar := emb.toAlgebra
  have S2 : IsPullback e.inv.left P.A.X.hom (A.baseChange Qbar).X.hom (𝟙 _) :=
    IsPullback.of_horiz_isIso ⟨by simp⟩
  have S3 : IsPullback (pullback.fst A.X.hom (Spec.map (CommRingCat.ofHom emb)) :
      (A.baseChange Qbar).X.left ⟶ A.X.left) (A.baseChange Qbar).X.hom A.X.hom
      (Spec.map (CommRingCat.ofHom emb)) :=
    IsPullback.of_hasPullback _ _
  have S := hpb.paste_horiz (S2.paste_horiz S3)
  have hσ : Spec.map (CommRingCat.ofHom ιe) ≫ 𝟙 _ ≫ Spec.map (CommRingCat.ofHom emb) =
      Spec.map (CommRingCat.ofHom (ιe.comp emb)) := by
    rw [Category.id_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  rw [hσ] at S
  exact cPts_of_isPullback (LeafAdopt.abVarEquiv K.K A) (ιe.comp emb) Q.A _ S

end FibreQM

end G0Split

end HSyn

#print axioms HSyn.G0Split.FibreQM.CPtsT.cPts_of_isPullback
#print axioms HSyn.G0Split.FibreQM.cPtsTransport_proof
