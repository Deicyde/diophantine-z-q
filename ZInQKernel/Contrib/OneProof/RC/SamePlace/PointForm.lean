import ZInQKernel.Contrib.OneProof.RC.ModelGeneric5.Extension
import ZInQKernel.Contrib.OneProof.RC.ModelTarget.Read
import ZInQKernel.Contrib.OneProof.RC.SamePlace.Supersingular

/-! # The point form of special-fibre points and the point map (rc-same-place1, items 3–4)

Let `R = LocalIntegers ell`, `A = Pinned.Y0LevelAlgebra h₅ htame h₂` and `K` a field over
`ZMod ell`, made an `R`-algebra through `ModelTarget.resRing ell K = (ZMod ell → K) ∘ closed`
(`resAlgebra`, a local instance here). A geometric point of the special fibre of the pinned
model `Pinned.Y0Level` with values in `K`, i.e. a map
`residueSource ell K ⟶ (Over.pullback (Spec closed)).obj (Pinned.Y0Level h₅ htame h₂)`
(the type of the values of `SamePlaceData.point`), is the same as an `R`-algebra map `A → K`:

* `pointForm` is the composite of Mathlib's adjunction `Over.mapPullbackAdj` (`Over.map ⊣
  Over.pullback`), the repackaging of an `Over`-morphism as a commuting scheme map (through the
  tree's `ModelTarget.residue_structure`), and Mathlib's `Spec.homEquivAlgHom`;
* `spec_pointForm`: `Spec (pointForm P) = P.left ≫ pullback.fst`;
* the **φ lemma** `pointForm_comp_map`: for every `R`-algebra endomorphism `φ` of `A` and every
  endomorphism `f` of `Pinned.Y0Level` with `f.left = Spec φ`,
  `pointForm (P ≫ (Over.pullback _).map f) = (pointForm P).comp φ` (the hypothesis on `f.left` is
  stated under `ModelGeneric5.levelCommRing`, the ring instance `ModelGeneric5.Wint` is built
  with);
* the **Frobenius form** `pointForm_residueFrob`: precomposition with `residueFrob ell K` is
  postcomposition with the `#(ZMod ell)`-power Frobenius `frobAlg ell K`, whose ring map is
  `frobenius K ell` (`frobAlg_toRingHom`).

`point` (item 4) sends a supersingular pair class `x : ssPoint ell K N` to the special-fibre point
`pointForm.symm ((Pinned.Y0LevelPoints h₅ htame h₂).symm x.val)`, through the tree's actual point
reading `Pinned.Y0LevelPoints`; it is injective.

Provenance: assembly of Mathlib and tree results, on the spot (c). -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

noncomputable section

open AlgebraicGeometry CategoryTheory Limits
open WeierstrassCurve.ModelTorsion WeierstrassCurve.ModelLevels

namespace ZInQ.Manuscript.RC.SamePlace

open PMQuotient (residueSource residueFrob)

variable {ell N : ℕ} [Fact ell.Prime] [NeZero N] (h₅ : 5 ≤ ell) (htame : ¬ ell ∣ N * N.totient)
  (h₂ : 2 ≤ N) (K : Type) [Field K] [Algebra (ZMod ell) K]

/-- The `LocalIntegers ell`-algebra structure of `K` through `ModelTarget.resRing ell K`. -/
abbrev resAlgebra (ell : ℕ) [Fact ell.Prime] (K : Type) [Field K] [Algebra (ZMod ell) K] :
    Algebra (LocalIntegers ell) K :=
  (ModelTarget.resRing ell K).toAlgebra

attribute [local instance] resAlgebra

/-- An `Over`-morphism out of `Over.map (Spec closed)` of the residue point is a scheme map to
`Spec A` over `Spec R` (through `ModelTarget.residue_structure`). -/
def overHomEquiv :
    ((Over.map (Spec.map (CommRingCat.ofHom (ModelNeron.closed ell)))).obj (residueSource ell K) ⟶
        Pinned.Y0Level h₅ htame h₂) ≃
      {u : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of (Pinned.Y0LevelAlgebra h₅ htame h₂)) //
        u ≫ Spec.algebraMap (LocalIntegers ell) (Pinned.Y0LevelAlgebra h₅ htame h₂) =
          Spec.algebraMap (LocalIntegers ell) K} where
  toFun v := ⟨v.left, (Over.w v).trans (ModelTarget.residue_structure ell K)⟩
  invFun u := Over.homMk u.1 (u.2.trans (ModelTarget.residue_structure ell K).symm)
  left_inv v := rfl
  right_inv u := rfl

/-- **The point form of special-fibre points**: geometric points of the special fibre of the
pinned model with values in `K` are `LocalIntegers ell`-algebra maps `A → K`. -/
def pointForm :
    (residueSource ell K ⟶
        (Over.pullback (Spec.map (CommRingCat.ofHom (ModelNeron.closed ell)))).obj
          (Pinned.Y0Level h₅ htame h₂)) ≃
      (Pinned.Y0LevelAlgebra h₅ htame h₂ →ₐ[LocalIntegers ell] K) :=
  ((Over.mapPullbackAdj (Spec.map (CommRingCat.ofHom (ModelNeron.closed ell)))).homEquiv
      (residueSource ell K) (Pinned.Y0Level h₅ htame h₂)).symm.trans
    ((overHomEquiv h₅ htame h₂ K).trans Spec.homEquivAlgHom)

variable {h₅ htame h₂ K}

theorem spec_homEquivAlgHom {R A B : Type} [CommRing R] [CommRing A] [CommRing B] [Algebra R A]
    [Algebra R B]
    (u : {f : Spec (CommRingCat.of B) ⟶ Spec (CommRingCat.of A) //
      f ≫ Spec.algebraMap R A = Spec.algebraMap R B}) :
    Spec.map (CommRingCat.ofHom ((Spec.homEquivAlgHom u : A →ₐ[R] B) : A →+* B)) = u.1 := by
  change Spec.map (CommRingCat.ofHom (Spec.preimage u.1).hom) = u.1
  rw [CommRingCat.ofHom_hom, Spec.map_preimage]

/-- `Spec` of the point form is the special-fibre point followed by the projection to the
model. -/
theorem spec_pointForm
    (P : residueSource ell K ⟶
      (Over.pullback (Spec.map (CommRingCat.ofHom (ModelNeron.closed ell)))).obj
        (Pinned.Y0Level h₅ htame h₂)) :
    Spec.map (CommRingCat.ofHom ((pointForm h₅ htame h₂ K P :
        Pinned.Y0LevelAlgebra h₅ htame h₂ →ₐ[LocalIntegers ell] K) :
          Pinned.Y0LevelAlgebra h₅ htame h₂ →+* K)) =
      P.left ≫ pullback.fst _ _ := by
  rw [pointForm, Equiv.trans_apply, Equiv.trans_apply, spec_homEquivAlgHom]
  simp [overHomEquiv, Over.mapPullbackAdj, Adjunction.mkOfHomEquiv_homEquiv]

/-- Algebra maps are determined by their `Spec`. -/
theorem algHom_ext_spec {R A B : Type} [CommRing R] [CommRing A] [CommRing B] [Algebra R A]
    [Algebra R B] {x y : A →ₐ[R] B}
    (h : Spec.map (CommRingCat.ofHom (x : A →+* B)) = Spec.map (CommRingCat.ofHom (y : A →+* B))) :
    x = y := by
  apply AlgHom.coe_ringHom_injective
  have := congrArg CommRingCat.Hom.hom (Spec.map_injective h)
  simpa using this

/-- `Spec` of a point form. -/
def specOf (x : Pinned.Y0LevelAlgebra h₅ htame h₂ →ₐ[LocalIntegers ell] K) :
    Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of (Pinned.Y0LevelAlgebra h₅ htame h₂)) :=
  Spec.map (CommRingCat.ofHom (x : Pinned.Y0LevelAlgebra h₅ htame h₂ →+* K))

theorem specOf_injective : Function.Injective (specOf (h₅ := h₅) (htame := htame) (h₂ := h₂)
    (K := K)) :=
  fun _ _ h => algHom_ext_spec h

theorem spec_ofHom_comp {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B)
    (g : B →+* C) :
    Spec.map (CommRingCat.ofHom (g.comp f)) =
      Spec.map (CommRingCat.ofHom g) ≫ Spec.map (CommRingCat.ofHom f) := by
  rw [CommRingCat.ofHom_comp, Spec.map_comp]

/-- **The φ lemma.** For every `LocalIntegers ell`-algebra endomorphism `φ` of the pinned level
algebra and every endomorphism `f` of the pinned model with `f.left = Spec φ` (stated under
`ModelGeneric5.levelCommRing`, the instance `ModelGeneric5.Wint` is built with), the special-fibre
action of `f` is precomposition with `φ` in the point form. -/
theorem pointForm_comp_map
    (φ : Pinned.Y0LevelAlgebra h₅ htame h₂ →ₐ[LocalIntegers ell] Pinned.Y0LevelAlgebra h₅ htame h₂)
    (f : Pinned.Y0Level h₅ htame h₂ ⟶ Pinned.Y0Level h₅ htame h₂)
    (hf : letI := ModelGeneric5.levelCommRing h₅ htame h₂
      f.left = Spec.map (CommRingCat.ofHom (φ : Pinned.Y0LevelAlgebra h₅ htame h₂ →+*
        Pinned.Y0LevelAlgebra h₅ htame h₂)))
    (P : residueSource ell K ⟶
      (Over.pullback (Spec.map (CommRingCat.ofHom (ModelNeron.closed ell)))).obj
        (Pinned.Y0Level h₅ htame h₂)) :
    pointForm h₅ htame h₂ K
        (P ≫ (Over.pullback (Spec.map (CommRingCat.ofHom (ModelNeron.closed ell)))).map f) =
      (pointForm h₅ htame h₂ K P).comp φ := by
  have hf' : f.left = Spec.map (CommRingCat.ofHom (φ : Pinned.Y0LevelAlgebra h₅ htame h₂ →+*
      Pinned.Y0LevelAlgebra h₅ htame h₂)) := hf
  apply specOf_injective
  unfold specOf
  have hl : ((Over.pullback (Spec.map (CommRingCat.ofHom (ModelNeron.closed ell)))).map f).left ≫
      pullback.fst _ _ = pullback.fst _ _ ≫ f.left := by
    simp
  rw [spec_pointForm, AlgHom.comp_toRingHom, Over.comp_left, Category.assoc, hl, hf',
    ← Category.assoc, ← spec_pointForm]
  exact (spec_ofHom_comp _ _).symm

variable (ell K) in
/-- The `#(ZMod ell)`-power Frobenius of `K` (the ring map of `residueFrob ell K`) as a
`LocalIntegers ell`-algebra map: it fixes the image of `resRing`. -/
def frobAlg : K →ₐ[LocalIntegers ell] K :=
  { (FiniteField.frobeniusAlgHom (ZMod ell) K : K →+* K) with
    commutes' := fun r => (FiniteField.frobeniusAlgHom (ZMod ell) K).commutes
      (ModelNeron.closed ell r) }

/-- The ring map of `residueFrob` is the `ell`-power Frobenius `frobenius K ell`. -/
theorem frobeniusAlgHom_eq_frobenius [CharP K ell] :
    (FiniteField.frobeniusAlgHom (ZMod ell) K : K →+* K) = frobenius K ell := by
  ext x
  change (FiniteField.frobeniusAlgHom (ZMod ell) K) x = _
  rw [FiniteField.coe_frobeniusAlgHom, ZMod.card, frobenius_def]

theorem frobAlg_toRingHom [CharP K ell] : (frobAlg ell K : K →+* K) = frobenius K ell :=
  frobeniusAlgHom_eq_frobenius

/-- **The Frobenius form**: precomposition with `residueFrob ell K` is postcomposition with the
Frobenius in the point form. -/
theorem pointForm_residueFrob
    (P : residueSource ell K ⟶
      (Over.pullback (Spec.map (CommRingCat.ofHom (ModelNeron.closed ell)))).obj
        (Pinned.Y0Level h₅ htame h₂)) :
    pointForm h₅ htame h₂ K (residueFrob ell K ≫ P) = (frobAlg ell K).comp (pointForm h₅ htame h₂ K P) := by
  apply specOf_injective
  unfold specOf
  rw [spec_pointForm, AlgHom.comp_toRingHom, CommRingCat.ofHom_comp, Spec.map_comp,
    spec_pointForm]
  have hl : (residueFrob ell K ≫ P).left =
      Spec.map (CommRingCat.ofHom (FiniteField.frobeniusAlgHom (ZMod ell) K : K →+* K)) ≫
        P.left := rfl
  rw [hl, Category.assoc]
  rfl

variable [DecidableEq K] [IsAlgClosed K]

variable (h₅ htame h₂ K) in
/-- **The point map of the same-place lane** (item 4): a supersingular pair class goes to the
special-fibre point whose point form is its preimage under the pinned reading
`Pinned.Y0LevelPoints`. -/
def point (x : ssPoint K ell N) :
    residueSource ell K ⟶
      (Over.pullback (Spec.map (CommRingCat.ofHom (ModelNeron.closed ell)))).obj
        (Pinned.Y0Level h₅ htame h₂) :=
  (pointForm h₅ htame h₂ K).symm ((Pinned.Y0LevelPoints h₅ htame h₂).symm x.val)

theorem pointForm_point (x : ssPoint K ell N) :
    pointForm h₅ htame h₂ K (point h₅ htame h₂ K x) =
      (Pinned.Y0LevelPoints h₅ htame h₂).symm x.val :=
  (pointForm h₅ htame h₂ K).apply_symm_apply _

theorem Y0LevelPoints_pointForm_point (x : ssPoint K ell N) :
    Pinned.Y0LevelPoints h₅ htame h₂ (pointForm h₅ htame h₂ K (point h₅ htame h₂ K x)) = x.val := by
  rw [pointForm_point, Equiv.apply_symm_apply]

theorem point_injective : Function.Injective (point h₅ htame h₂ K) := by
  intro x y h
  apply Subtype.ext
  have := congrArg (fun P => Pinned.Y0LevelPoints h₅ htame h₂ (pointForm h₅ htame h₂ K P)) h
  simpa only [Y0LevelPoints_pointForm_point] using this

end ZInQ.Manuscript.RC.SamePlace

#print axioms ZInQ.Manuscript.RC.SamePlace.pointForm
#print axioms ZInQ.Manuscript.RC.SamePlace.spec_pointForm
#print axioms ZInQ.Manuscript.RC.SamePlace.pointForm_comp_map
#print axioms ZInQ.Manuscript.RC.SamePlace.frobeniusAlgHom_eq_frobenius
#print axioms ZInQ.Manuscript.RC.SamePlace.pointForm_residueFrob
#print axioms ZInQ.Manuscript.RC.SamePlace.point
#print axioms ZInQ.Manuscript.RC.SamePlace.point_injective
