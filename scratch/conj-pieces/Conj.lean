import ZInQKernel.HDecomp.LeafPush2.T

/-! # conj-pieces §C: `ConjUniformization` (N3a)

Check with `lake env lean scratch/conj-pieces/Conj.lean` (after
`lake build ZInQKernel.HDecomp.LeafPush2.T`).

* §1 copies **verbatim** from `scratch/conj-twist/ConjTwist.lean`: `specS`, `conjVar`,
  `homEquiv_mul_conj`, `conjHom`, `conjCs`, `mapPtIso`, `twistC`, `twistC_one`, `conjL`,
  `conjL_conjL`, `conjL_I`, `ConjUniformization`, `conjHomInv`, `mapPtIsoInv`, `twistC_inj_aux`,
  `twistC_injective`, `ringHom_bijective_of_numberField`.
* §2 proves the group-theoretic clauses (`twistC_mul`, `twistC_surjective`) and reduces
  `ConjUniformization` to the analytic glue `ConjHolo` (`conjUniformization_of_conjHolo`).
* §3 proves `ConjHolo` whenever `s` is bijective (`conjHolo_of_bijective`), in particular for
  number fields, hence `ConjUniformizationNF` (`ConjUniformization` for number fields, the only
  case used by conj-twist's `conjAntiLiftLat_of`). -/

noncomputable section

namespace G0Galois

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct CategoryTheory.Obj

open ZInQ.LeafPush2 (CPts cptObj IsUniformization cDom cEvalAt)

/-! ## §1. Verbatim copies from `scratch/conj-twist/ConjTwist.lean` -/

open PkgI3 in
/-- `Spec(s) : Spec K → Spec K`. -/
abbrev specS {K : Type} [Field K] (s : K →+* K) :
    Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of K) :=
  Spec.map (CommRingCat.ofHom s)

/-- **The conjugate abelian variety** `A^s = A ×_{Spec K, Spec s} Spec K` (pullback along
`Spec(s)`; group structure transported by the monoidal functor `Over.pullback`). -/
def conjVar {K : Type} [Field K] (A : PkgI3.AbVar K) (s : K →+* K) : PkgI3.AbVar K :=
  let f := specS s
  letI : GrpObj ((Over.pullback f).obj A.X) := Functor.grpObjObj
  haveI : IsProper ((Over.pullback f).obj A.X).hom := by dsimp; infer_instance
  haveI : Smooth ((Over.pullback f).obj A.X).hom := by dsimp; infer_instance
  haveI : GeometricallyIntegral ((Over.pullback f).obj A.X).hom := by dsimp; infer_instance
  { X := (Over.pullback f).obj A.X }

section Transport

variable {K : Type} [Field K] (A : PkgI3.AbVar K) (s : K →+* K)
  (cc : AlgebraicClosure K ≃+* AlgebraicClosure K)
  (hs : ∀ k, cc (algebraMap K _ k) = algebraMap K _ (s k))

/-- The adjunction bijection for `Over.map (Spec s) ⊣ Over.pullback (Spec s)` is
multiplicative. -/
theorem homEquiv_mul_conj (X : Over (Spec (CommRingCat.of K)))
    (p q : (Over.map (specS s)).obj X ⟶ A.X) :
    (Over.mapPullbackAdj (specS s)).homEquiv X A.X (p * q) =
      (Over.mapPullbackAdj (specS s)).homEquiv X A.X p *
        (Over.mapPullbackAdj (specS s)).homEquiv X A.X q := by
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit, Adjunction.homEquiv_unit,
    Functor.map_mul, MonObj.comp_mul]

end Transport

/-- `Spec(conj) : Spec ℂ → Spec ℂ`, over `K` from `σ ∘ s` to `σ`, when `σ ∘ s = conj ∘ σ`. -/
def conjHom {K : Type} [Field K] (σ : K →+* ℂ) (s : K →+* K)
    (h : σ.comp s = (starRingEnd ℂ).comp σ) : cptObj (σ.comp s) ⟶ cptObj σ :=
  Over.homMk (Spec.map (CommRingCat.ofHom (starRingEnd ℂ))) (by
    simp only [cptObj, Over.mk_hom]
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, h])

/-- Complex conjugation `A(ℂ)_σ → A(ℂ)_{σ∘s}` when `σ ∘ s = conj ∘ σ`: `Q ↦ Q ∘ Spec(conj)`. -/
def conjCs {K : Type} [Field K] (A : PkgI3.AbVar K) (σ : K →+* ℂ) (s : K →+* K)
    (h : σ.comp s = (starRingEnd ℂ).comp σ) (Q : CPts A σ) : CPts A (σ.comp s) :=
  conjHom σ s h ≫ Q

/-- `(Over.map Spec(s)).obj (Spec ℂ via σ) ⟶ Spec ℂ via σ ∘ s` (the identity of `Spec ℂ`). -/
def mapPtIso {K : Type} [Field K] (σ : K →+* ℂ) (s : K →+* K) :
    (Over.map (specS s)).obj (cptObj σ) ⟶ cptObj (σ.comp s) :=
  Over.homMk (𝟙 _) (by
    simp only [Over.map_obj_hom, cptObj, Over.mk_hom, Category.id_comp, ← Spec.map_comp,
      ← CommRingCat.ofHom_comp])

/-- The map `A(ℂ)_σ → A^s(ℂ)_σ`, `Q ↦ Q ∘ Spec(conj)` read through `A^s(ℂ)_σ = A(ℂ)_{σ∘s}`
(adjunction `Over.map ⊣ Over.pullback`). -/
def twistC {K : Type} [Field K] (A : PkgI3.AbVar K) (σ : K →+* ℂ) (s : K →+* K)
    (h : σ.comp s = (starRingEnd ℂ).comp σ) (Q : CPts A σ) : CPts (conjVar A s) σ :=
  (Over.mapPullbackAdj (specS s)).homEquiv _ _ (mapPtIso σ s ≫ conjCs A σ s h Q)

/-- `twistC` maps `1` to `1` (proved). -/
theorem twistC_one {K : Type} [Field K] (A : PkgI3.AbVar K) (σ : K →+* ℂ) (s : K →+* K)
    (h : σ.comp s = (starRingEnd ℂ).comp σ) : twistC A σ s h 1 = 1 := by
  change (Over.mapPullbackAdj (specS s)).homEquiv _ _ (mapPtIso σ s ≫ conjHom σ s h ≫ 1) = 1
  rw [MonObj.comp_one, MonObj.comp_one, Adjunction.homEquiv_unit, Functor.map_one,
    MonObj.comp_one]
  rfl

/-- Complex conjugation on `ℂ^g`, as an `ℝ`-linear map. -/
def conjL (g : ℕ) : (Fin g → ℂ) →ₗ[ℝ] (Fin g → ℂ) where
  toFun z i := starRingEnd ℂ (z i)
  map_add' z w := by funext i; simp
  map_smul' r z := by funext i; simp

theorem conjL_conjL {g : ℕ} (z : Fin g → ℂ) : conjL g (conjL g z) = z := by
  funext i; simp [conjL]

theorem conjL_I {g : ℕ} (z : Fin g → ℂ) :
    conjL g (Complex.I • z) = -(Complex.I • conjL g z) := by
  funext i; simp [conjL]

/-- **N3a. The conjugate of a uniformization (GLUE, unproved; STANDARD).** If `σ ∘ s = conj ∘ σ`
and `Φ` uniformizes `A(ℂ)_σ` with kernel `Λ`, then `z ↦ twistC(Φ(z̄))` uniformizes `A^s(ℂ)_σ`
with kernel `Λ̄ = {z | z̄ ∈ Λ}`. (`A^s(ℂ)_σ = A(ℂ)_{σ∘s} = A(ℂ)_{conj∘σ}`, and on affine charts
`twistC` conjugates the values of regular functions, so `z ↦ s(twistC(Φ z̄)) = conj(s'(Φ z))`-type
compositions are holomorphic; the group-theoretic clauses follow from `twistC` being a bijective
homomorphism.) -/
def ConjUniformization : Prop :=
  ∀ (K : Type) [Field K] (A : PkgI3.AbVar K) (σ : K →+* ℂ) (s : K →+* K)
    (h : σ.comp s = (starRingEnd ℂ).comp σ) (g : ℕ) (Λ : Submodule ℤ (Fin g → ℂ))
    (Φ : (Fin g → ℂ) → CPts A σ),
    A.dim = (g : WithBot ℕ∞) → IsUniformization σ Λ Φ →
    IsUniformization σ (Λ.comap ((conjL g).restrictScalars ℤ))
      (fun z => twistC A σ s h (Φ (conjL g z)))

/-- `Spec(conj)` back from `σ` to `σ ∘ s`. -/
def conjHomInv {K : Type} [Field K] (σ : K →+* ℂ) (s : K →+* K)
    (h : σ.comp s = (starRingEnd ℂ).comp σ) : cptObj σ ⟶ cptObj (σ.comp s) :=
  Over.homMk (Spec.map (CommRingCat.ofHom (starRingEnd ℂ))) (by
    simp only [cptObj, Over.mk_hom]
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, h]
    congr 2
    ext x
    simp)

/-- The inverse of `mapPtIso`. -/
def mapPtIsoInv {K : Type} [Field K] (σ : K →+* ℂ) (s : K →+* K) :
    cptObj (σ.comp s) ⟶ (Over.map (specS s)).obj (cptObj σ) :=
  Over.homMk (𝟙 _) (by
    simp only [Over.map_obj_hom, cptObj, Over.mk_hom, Category.id_comp, ← Spec.map_comp,
      ← CommRingCat.ofHom_comp])

theorem twistC_inj_aux {K : Type} [Field K] (σ : K →+* ℂ) (s : K →+* K)
    (h : σ.comp s = (starRingEnd ℂ).comp σ) :
    conjHomInv σ s h ≫ mapPtIsoInv σ s ≫ mapPtIso σ s ≫ conjHom σ s h = 𝟙 _ := by
  apply Over.OverMorphism.ext
  change Spec.map (CommRingCat.ofHom (starRingEnd ℂ)) ≫ 𝟙 _ ≫ 𝟙 _ ≫
    Spec.map (CommRingCat.ofHom (starRingEnd ℂ)) = 𝟙 _
  rw [Category.id_comp, Category.id_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  rw [show (starRingEnd ℂ).comp (starRingEnd ℂ) = RingHom.id ℂ by ext x; simp,
    CommRingCat.ofHom_id, Spec.map_id]

/-- `twistC` is injective (proved). -/
theorem twistC_injective {K : Type} [Field K] (A : PkgI3.AbVar K) (σ : K →+* ℂ) (s : K →+* K)
    (h : σ.comp s = (starRingEnd ℂ).comp σ) : Function.Injective (twistC A σ s h) := by
  intro Q Q' hQ
  have h1 : mapPtIso σ s ≫ conjHom σ s h ≫ Q = mapPtIso σ s ≫ conjHom σ s h ≫ Q' :=
    ((Over.mapPullbackAdj (specS s)).homEquiv _ _).injective hQ
  calc Q = (conjHomInv σ s h ≫ mapPtIsoInv σ s ≫ mapPtIso σ s ≫ conjHom σ s h) ≫ Q := by
        rw [twistC_inj_aux, Category.id_comp]
    _ = conjHomInv σ s h ≫ mapPtIsoInv σ s ≫ (mapPtIso σ s ≫ conjHom σ s h ≫ Q) := by
        simp only [Category.assoc]
    _ = conjHomInv σ s h ≫ mapPtIsoInv σ s ≫ (mapPtIso σ s ≫ conjHom σ s h ≫ Q') := by
        rw [h1]
    _ = (conjHomInv σ s h ≫ mapPtIsoInv σ s ≫ mapPtIso σ s ≫ conjHom σ s h) ≫ Q' := by
        simp only [Category.assoc]
    _ = Q' := by rw [twistC_inj_aux, Category.id_comp]

/-- A ring endomorphism of a number field is bijective. -/
theorem ringHom_bijective_of_numberField (K : Type) [Field K] [NumberField K] (s : K →+* K) :
    Function.Bijective s := by
  have hinj : Function.Injective s := s.injective
  refine ⟨hinj, ?_⟩
  have h := (LinearMap.injective_iff_surjective (f := s.toRatAlgHom.toLinearMap)).mp hinj
  exact h

/-! ## §2. The group-theoretic clauses and the analytic glue `ConjHolo` -/

/-- `twistC` is a homomorphism (proved). -/
theorem twistC_mul {K : Type} [Field K] (A : PkgI3.AbVar K) (σ : K →+* ℂ) (s : K →+* K)
    (h : σ.comp s = (starRingEnd ℂ).comp σ) (P Q : CPts A σ) :
    twistC A σ s h (P * Q) = twistC A σ s h P * twistC A σ s h Q := by
  change (Over.mapPullbackAdj (specS s)).homEquiv _ _ (mapPtIso σ s ≫ conjHom σ s h ≫ (P * Q)) =
    (Over.mapPullbackAdj (specS s)).homEquiv _ _ (mapPtIso σ s ≫ conjHom σ s h ≫ P) *
      (Over.mapPullbackAdj (specS s)).homEquiv _ _ (mapPtIso σ s ≫ conjHom σ s h ≫ Q)
  rw [MonObj.comp_mul, MonObj.comp_mul, homEquiv_mul_conj]

theorem twistC_surj_aux {K : Type} [Field K] (σ : K →+* ℂ) (s : K →+* K)
    (h : σ.comp s = (starRingEnd ℂ).comp σ) :
    mapPtIso σ s ≫ conjHom σ s h ≫ conjHomInv σ s h ≫ mapPtIsoInv σ s = 𝟙 _ := by
  apply Over.OverMorphism.ext
  change 𝟙 _ ≫ Spec.map (CommRingCat.ofHom (starRingEnd ℂ)) ≫
    Spec.map (CommRingCat.ofHom (starRingEnd ℂ)) ≫ 𝟙 _ = 𝟙 _
  rw [Category.id_comp, Category.comp_id, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  rw [show (starRingEnd ℂ).comp (starRingEnd ℂ) = RingHom.id ℂ by ext x; simp,
    CommRingCat.ofHom_id, Spec.map_id]

/-- `twistC` is surjective (proved). -/
theorem twistC_surjective {K : Type} [Field K] (A : PkgI3.AbVar K) (σ : K →+* ℂ) (s : K →+* K)
    (h : σ.comp s = (starRingEnd ℂ).comp σ) : Function.Surjective (twistC A σ s h) := by
  intro R
  refine ⟨conjHomInv σ s h ≫ mapPtIsoInv σ s ≫
    ((Over.mapPullbackAdj (specS s)).homEquiv _ _).symm R, ?_⟩
  change (Over.mapPullbackAdj (specS s)).homEquiv _ _ (mapPtIso σ s ≫ conjHom σ s h ≫
    conjHomInv σ s h ≫ mapPtIsoInv σ s ≫ ((Over.mapPullbackAdj (specS s)).homEquiv _ _).symm R) = R
  have e : mapPtIso σ s ≫ conjHom σ s h ≫ conjHomInv σ s h ≫ mapPtIsoInv σ s ≫
      ((Over.mapPullbackAdj (specS s)).homEquiv _ _).symm R =
      (mapPtIso σ s ≫ conjHom σ s h ≫ conjHomInv σ s h ≫ mapPtIsoInv σ s) ≫
        ((Over.mapPullbackAdj (specS s)).homEquiv _ _).symm R := by
    simp only [Category.assoc]
  rw [e, twistC_surj_aux, Category.id_comp]
  exact Equiv.apply_symm_apply _ _

/-- **N3a-holo. Conjugation preserves holomorphy (GLUE; STANDARD).** If `σ ∘ s = conj ∘ σ` and
`Ψ : ℂ^g → A(ℂ)_σ` is holomorphic in the sense of `IsUniformization` (preimages of affine-chart
domains open, regular functions holomorphic there), so is `z ↦ twistC(Ψ(z̄))` into `A^s(ℂ)_σ`.
These are the two analytic clauses of `ConjUniformization`. (On the affine pieces
`W ×_{Spec K, Spec s} Spec K` of `A^s`, a regular function `Σ aᵢ ⊗ bᵢ` takes at `twistC(Ψ z̄)` the
value `conj(Σ aᵢ(Ψ z̄)·conj(σ bᵢ))`, and `z ↦ conj(f(z̄))` is holomorphic when `f` is.) Proved
below when `s` is bijective (`conjHolo_of_bijective`), e.g. for every number field. -/
def ConjHolo : Prop :=
  ∀ (K : Type) [Field K] (A : PkgI3.AbVar K) (σ : K →+* ℂ) (s : K →+* K)
    (h : σ.comp s = (starRingEnd ℂ).comp σ) (g : ℕ) (Ψ : (Fin g → ℂ) → CPts A σ),
    (∀ U, IsOpen (cDom Ψ U)) →
    (∀ U (t : Γ(A.X.left, U)), DifferentiableOn ℂ (fun z => cEvalAt (Ψ z) U t) (cDom Ψ U)) →
    (∀ V, IsOpen (cDom (fun z => twistC A σ s h (Ψ (conjL g z))) V)) ∧
    ∀ V (t : Γ((conjVar A s).X.left, V)), DifferentiableOn ℂ
      (fun z => cEvalAt (twistC A σ s h (Ψ (conjL g z))) V t)
      (cDom (fun z => twistC A σ s h (Ψ (conjL g z))) V)

/-- The conjugate of a uniformization, given the analytic clauses (proved). -/
theorem isUniformization_twist {K : Type} [Field K] (A : PkgI3.AbVar K) (σ : K →+* ℂ)
    (s : K →+* K) (h : σ.comp s = (starRingEnd ℂ).comp σ) {g : ℕ} {Λ : Submodule ℤ (Fin g → ℂ)}
    {Φ : (Fin g → ℂ) → CPts A σ} (hΦ : IsUniformization σ Λ Φ)
    (hO : ∀ V, IsOpen (cDom (fun z => twistC A σ s h (Φ (conjL g z))) V))
    (hH : ∀ V (t : Γ((conjVar A s).X.left, V)), DifferentiableOn ℂ
      (fun z => cEvalAt (twistC A σ s h (Φ (conjL g z))) V t)
      (cDom (fun z => twistC A σ s h (Φ (conjL g z))) V)) :
    IsUniformization σ (Λ.comap ((conjL g).restrictScalars ℤ))
      (fun z => twistC A σ s h (Φ (conjL g z))) := by
  refine ⟨fun z w => ?_, fun z => ?_, ?_, hO, hH⟩
  · change twistC A σ s h (Φ (conjL g (z + w))) =
      twistC A σ s h (Φ (conjL g z)) * twistC A σ s h (Φ (conjL g w))
    rw [map_add, hΦ.1, twistC_mul]
  · change twistC A σ s h (Φ (conjL g z)) = 1 ↔ conjL g z ∈ Λ
    rw [← hΦ.2.1, ← twistC_one A σ s h]
    exact (twistC_injective A σ s h).eq_iff
  · intro R
    obtain ⟨Q, rfl⟩ := twistC_surjective A σ s h R
    obtain ⟨w, rfl⟩ := hΦ.2.2.1 Q
    exact ⟨conjL g w, by simp only [conjL_conjL]⟩

/-- **`ConjUniformization` from the analytic glue `ConjHolo` (proved).** -/
theorem conjUniformization_of_conjHolo (hC : ConjHolo) : ConjUniformization := by
  intro K _ A σ s h g Λ Φ _ hΦ
  obtain ⟨hO, hH⟩ := hC K A σ s h g Φ hΦ.2.2.2.1 hΦ.2.2.2.2
  exact isUniformization_twist A σ s h hΦ hO hH

/-! ## §3. `ConjHolo` for bijective `s` (proved), hence `ConjUniformization` for number fields -/

theorem top_le_preimage_spec (f : Spec (CommRingCat.of ℂ) ⟶ Spec (CommRingCat.of ℂ))
    (W : (Spec (CommRingCat.of ℂ)).Opens) : ⊤ ≤ f ⁻¹ᵁ W ↔ ⊤ ≤ W := by
  constructor
  · intro hW x _
    have hx : f x ∈ W := hW trivial
    rwa [Subsingleton.elim (f x) x] at hx
  · intro hW x _
    exact hW trivial

theorem appLE_of_eq {X Y : Scheme} {f f' : X ⟶ Y} (e : f = f') (U : Y.Opens) (V : X.Opens)
    (hf : V ≤ f ⁻¹ᵁ U) : f.appLE U V hf = f'.appLE U V (e ▸ hf) := by
  subst e; rfl

/-- If `r ≫ fst = c ≫ q` with `c : Spec ℂ → Spec ℂ`, then `r` meets `fst⁻¹U` iff `q` meets `U`
(proved). -/
theorem top_le_of_comp_eq {P X : Scheme} (r : Spec (CommRingCat.of ℂ) ⟶ P) (fst : P ⟶ X)
    (q : Spec (CommRingCat.of ℂ) ⟶ X) (c : Spec (CommRingCat.of ℂ) ⟶ Spec (CommRingCat.of ℂ))
    (hr : r ≫ fst = c ≫ q) (U : X.Opens) : ⊤ ≤ r ⁻¹ᵁ fst ⁻¹ᵁ U ↔ ⊤ ≤ q ⁻¹ᵁ U := by
  change ⊤ ≤ (r ≫ fst) ⁻¹ᵁ U ↔ _
  rw [hr]
  exact top_le_preimage_spec c (q ⁻¹ᵁ U)

/-- If `r ≫ fst = Spec(conj) ≫ q`, the value at `r` of the pullback along `fst` of a regular
function is the conjugate of its value at `q` (proved). -/
theorem eval_of_comp_eq_conj {P X : Scheme} (r : Spec (CommRingCat.of ℂ) ⟶ P) (fst : P ⟶ X)
    (q : Spec (CommRingCat.of ℂ) ⟶ X)
    (hr : r ≫ fst = Spec.map (CommRingCat.ofHom (starRingEnd ℂ)) ≫ q) (U : X.Opens)
    (a : Γ(X, U)) (h1 : ⊤ ≤ r ⁻¹ᵁ fst ⁻¹ᵁ U) (hq : ⊤ ≤ q ⁻¹ᵁ U) :
    (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom (r.appLE (fst ⁻¹ᵁ U) ⊤ h1 (fst.app U a)) =
      starRingEnd ℂ ((Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom (q.appLE U ⊤ hq a)) := by
  have h1' : ⊤ ≤ (r ≫ fst) ⁻¹ᵁ U := by rw [Scheme.Hom.comp_preimage]; exact h1
  have e1 : r.appLE (fst ⁻¹ᵁ U) ⊤ h1 (fst.app U a) = (r ≫ fst).appLE U ⊤ h1' a := by
    rw [Scheme.Hom.comp_appLE]; rfl
  rw [e1, appLE_of_eq hr,
    ← Scheme.Hom.appLE_comp_appLE (Spec.map (CommRingCat.ofHom (starRingEnd ℂ))) q U ⊤ ⊤
      hq le_top, CommRingCat.comp_apply,
    show (Spec.map (CommRingCat.ofHom (starRingEnd ℂ))).appLE ⊤ ⊤ le_top =
      (Spec.map (CommRingCat.ofHom (starRingEnd ℂ))).appTop from Scheme.Hom.appLE_eq_app _]
  exact congrArg (fun φ => CommRingCat.Hom.hom φ (q.appLE U ⊤ hq a))
    (Scheme.ΓSpecIso_naturality (CommRingCat.ofHom (starRingEnd ℂ)))

/-- The first component of the adjunction bijection is the given map (proved). -/
theorem homEquiv_left_fst {X Y : Scheme} (f : X ⟶ Y) (x : Over X) (y : Over Y)
    (u : (Over.map f).obj x ⟶ y) :
    ((Over.mapPullbackAdj f).homEquiv x y u).left ≫ pullback.fst y.hom f = u.left := by
  simp [Adjunction.homEquiv_unit]

/-- The projection `A^s = A ×_{Spec K, Spec s} Spec K → A`. -/
def cfst {K : Type} [Field K] (A : PkgI3.AbVar K) (s : K →+* K) :
    (conjVar A s).X.left ⟶ A.X.left :=
  pullback.fst A.X.hom (specS s)

/-- `Spec(conj)` on `Spec ℂ`, typed as an endomorphism of `(cptObj σ).left`. -/
def cconj {K : Type} [Field K] (σ : K →+* ℂ) : (cptObj σ).left ⟶ (cptObj σ).left :=
  Spec.map (CommRingCat.ofHom (starRingEnd ℂ))

/-- The first component of `twistC Q` is `Spec(conj) ≫ Q` (proved). -/
theorem twistC_left_fst {K : Type} [Field K] (A : PkgI3.AbVar K) (σ : K →+* ℂ) (s : K →+* K)
    (h : σ.comp s = (starRingEnd ℂ).comp σ) (Q : CPts A σ) :
    (twistC A σ s h Q).left ≫ cfst A s = cconj σ ≫ Q.left := by
  refine (homEquiv_left_fst (specS s) (cptObj σ) A.X (mapPtIso σ s ≫ conjCs A σ s h Q)).trans ?_
  exact Category.id_comp _

/-- Evaluating a pulled-back regular function at `twistC Q` conjugates its value at `Q`
(proved). -/
theorem cEvalAt_twistC {K : Type} [Field K] (A : PkgI3.AbVar K) (σ : K →+* ℂ) (s : K →+* K)
    (h : σ.comp s = (starRingEnd ℂ).comp σ) (Q : CPts A σ) (U : A.X.left.Opens)
    (a : Γ(A.X.left, U)) :
    cEvalAt (A := conjVar A s) (twistC A σ s h Q) (cfst A s ⁻¹ᵁ U)
      ((cfst A s).app U a) = starRingEnd ℂ (cEvalAt Q U a) := by
  unfold cEvalAt
  have hiff : ⊤ ≤ (twistC A σ s h Q).left ⁻¹ᵁ (cfst A s ⁻¹ᵁ U) ↔ ⊤ ≤ Q.left ⁻¹ᵁ U :=
    top_le_of_comp_eq _ _ _ _ (twistC_left_fst A σ s h Q) U
  by_cases hQ : ⊤ ≤ Q.left ⁻¹ᵁ U
  · have h1 := hiff.mpr hQ
    rw [dif_pos h1, dif_pos hQ]
    exact eval_of_comp_eq_conj _ _ _ (twistC_left_fst A σ s h Q) U a h1 hQ
  · have h1 : ¬ ⊤ ≤ (twistC A σ s h Q).left ⁻¹ᵁ (cfst A s ⁻¹ᵁ U) := fun h' => hQ (hiff.mp h')
    rw [dif_neg h1, dif_neg hQ, map_zero]

/-- `z ↦ conj(F(z̄))` is holomorphic on `conj⁻¹ D` when `F` is holomorphic on the open set `D`
(proved). -/
theorem differentiableOn_conj_conj {g : ℕ} {F : (Fin g → ℂ) → ℂ} {D : Set (Fin g → ℂ)}
    (hF : DifferentiableOn ℂ F D) (hD : IsOpen D) :
    DifferentiableOn ℂ (fun z => starRingEnd ℂ (F (conjL g z))) (conjL g ⁻¹' D) := by
  intro z hz
  have hFz : DifferentiableAt ℂ F (conjL g z) := hF.differentiableAt (hD.mem_nhds hz)
  set L := fderiv ℂ F (conjL g z)
  have hL : HasFDerivAt F L (conjL g z) := hFz.hasFDerivAt
  let cL : (Fin g → ℂ) →L[ℝ] (Fin g → ℂ) := LinearMap.toContinuousLinearMap (conjL g)
  have hcL : HasFDerivAt (fun z => conjL g z) cL z := cL.hasFDerivAt
  have hR : HasFDerivAt (fun z => starRingEnd ℂ (F (conjL g z)))
      ((Complex.conjCLE : ℂ →L[ℝ] ℂ).comp ((L.restrictScalars ℝ).comp cL)) z :=
    (Complex.conjCLE : ℂ →L[ℝ] ℂ).hasFDerivAt.comp z ((hL.restrictScalars ℝ).comp z hcL)
  let L'l : (Fin g → ℂ) →ₗ[ℂ] ℂ :=
    { toFun := fun v => starRingEnd ℂ (L (conjL g v))
      map_add' := fun v w => by simp [map_add]
      map_smul' := fun c v => by
        have : conjL g (c • v) = starRingEnd ℂ c • conjL g v := by
          funext i; simp [conjL]
        simp [this] }
  let L' : (Fin g → ℂ) →L[ℂ] ℂ := LinearMap.toContinuousLinearMap L'l
  have hC : HasFDerivAt (fun z => starRingEnd ℂ (F (conjL g z))) L' z :=
    hasFDerivAt_of_restrictScalars ℝ hR (by ext v; rfl)
  exact hC.differentiableAt.differentiableWithinAt

/-- **`ConjHolo` for bijective `s` (proved).** `Spec(s)` is an isomorphism, so is the projection
`A^s → A`; every open of `A^s` and every regular function on it is pulled back from `A`
(`cEvalAt_twistC`). -/
theorem conjHolo_of_bijective {K : Type} [Field K] (A : PkgI3.AbVar K) (σ : K →+* ℂ)
    (s : K →+* K) (hb : Function.Bijective s) (h : σ.comp s = (starRingEnd ℂ).comp σ) {g : ℕ}
    (Ψ : (Fin g → ℂ) → CPts A σ) (hO : ∀ U, IsOpen (cDom Ψ U))
    (hH : ∀ U (t : Γ(A.X.left, U)), DifferentiableOn ℂ (fun z => cEvalAt (Ψ z) U t) (cDom Ψ U)) :
    (∀ V, IsOpen (cDom (fun z => twistC A σ s h (Ψ (conjL g z))) V)) ∧
    ∀ V (t : Γ((conjVar A s).X.left, V)), DifferentiableOn ℂ
      (fun z => cEvalAt (twistC A σ s h (Ψ (conjL g z))) V t)
      (cDom (fun z => twistC A σ s h (Ψ (conjL g z))) V) := by
  let e : K ≃+* K := RingEquiv.ofBijective s hb
  have : IsIso (CommRingCat.ofHom s) :=
    ⟨⟨CommRingCat.ofHom (e.symm : K →+* K), by ext x; exact e.symm_apply_apply x,
      by ext x; exact e.apply_symm_apply x⟩⟩
  have : IsIso (specS s) := by unfold specS; infer_instance
  have : IsIso (cfst A s) := (inferInstance : IsIso (pullback.fst A.X.hom (specS s)))
  have hV : ∀ V : (conjVar A s).X.left.Opens,
      ∃ U, cfst A s ⁻¹ᵁ U = V := fun V =>
    ⟨(inv (cfst A s)) ⁻¹ᵁ V, by
      ext x
      change (inv (cfst A s)) (cfst A s x) ∈ V ↔ x ∈ V
      rw [← Scheme.Hom.comp_apply, IsIso.hom_inv_id]
      rfl⟩
  have hdom : ∀ U, cDom (fun z => twistC A σ s h (Ψ (conjL g z)))
      (cfst A s ⁻¹ᵁ U) = conjL g ⁻¹' cDom Ψ U := by
    intro U
    ext z
    exact top_le_of_comp_eq _ _ _ _ (twistC_left_fst A σ s h (Ψ (conjL g z))) U
  have hcont : Continuous (conjL g) := LinearMap.continuous_of_finiteDimensional _
  refine ⟨fun V => ?_, fun V t => ?_⟩
  · obtain ⟨U, rfl⟩ := hV V
    rw [hdom]
    exact (hO U).preimage hcont
  · obtain ⟨U, rfl⟩ := hV V
    obtain ⟨a, rfl⟩ : ∃ a, (cfst A s).app U a = t :=
      ⟨inv ((cfst A s).app U) t, by
        rw [← CommRingCat.comp_apply, IsIso.inv_hom_id]; rfl⟩
    rw [hdom]
    refine (differentiableOn_conj_conj (hH U a) (hO U)).congr fun z _ => ?_
    exact cEvalAt_twistC A σ s h (Ψ (conjL g z)) U a

/-- **N3a for number fields** (`ConjUniformization` with `[NumberField K]`; the only case used by
conj-twist's `conjAntiLiftLat_of`). -/
def ConjUniformizationNF : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (A : PkgI3.AbVar K) (σ : K →+* ℂ) (s : K →+* K)
    (h : σ.comp s = (starRingEnd ℂ).comp σ) (g : ℕ) (Λ : Submodule ℤ (Fin g → ℂ))
    (Φ : (Fin g → ℂ) → CPts A σ),
    A.dim = (g : WithBot ℕ∞) → IsUniformization σ Λ Φ →
    IsUniformization σ (Λ.comap ((conjL g).restrictScalars ℤ))
      (fun z => twistC A σ s h (Φ (conjL g z)))

/-- **`ConjUniformizationNF` (proved, no hypotheses).** -/
theorem conjUniformizationNF : ConjUniformizationNF := by
  intro K _ _ A σ s h g Λ Φ _ hΦ
  obtain ⟨hO, hH⟩ := conjHolo_of_bijective A σ s (ringHom_bijective_of_numberField K s) h Φ
    hΦ.2.2.2.1 hΦ.2.2.2.2
  exact isUniformization_twist A σ s h hΦ hO hH

#print axioms conjUniformization_of_conjHolo
#print axioms conjUniformizationNF

end G0Galois
