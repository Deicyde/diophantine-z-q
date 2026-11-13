import Mathlib.AlgebraicGeometry.Geometrically.Connected
import Mathlib.AlgebraicGeometry.Group.Abelian
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.AlgebraicGeometry.Pullbacks
import Mathlib.Algebra.Quaternion
import Mathlib.CategoryTheory.Monoidal.Cartesian.Grp
import Mathlib.CategoryTheory.Monoidal.Cartesian.Over
import Mathlib.Data.ZMod.Basic
import Mathlib.FieldTheory.AbsoluteGaloisGroup
import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.NumberTheory.Padics.RingHoms
import Mathlib.RepresentationTheory.Semisimple
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Mathlib.RingTheory.Etale.Locus
import Mathlib.RingTheory.Ideal.Height
import Mathlib.RingTheory.IntegralClosure.IntegralRestrict
import Mathlib.RingTheory.QuasiFinite.Basic
import Mathlib.RingTheory.RamificationInertia.Ramification
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.Unramified.Locus
import Mathlib.RingTheory.Valuation.RamificationGroup
import Mathlib.Topology.KrullDimension

/-! Glue of `docs/research/h-decomposition.md`, adopted by task hdec-adopt from
`scratch/obj-bridge/Objects.lean`.
The literature leaves are hypotheses (`def … : Prop`); no `sorry`, no `axiom`. -/

/-
obj-bridge: the shared object layer for packages I2 and I3, and the I2/I3 leaves restated over it.

Layout.
* §A (copied verbatim from `scratch/pkg-I3/I3.lean`): the Tate module, I3's `AbVar`, `Hom`, `End`,
  `End0`, points, `T`, `V`, `galRep`, the I3 leaves (`PkgI3.*`) and the I3 glue.
* §B (copied verbatim from `scratch/pkg-I2/I2.lean`, except that the glue theorem
  `goodReduction_of_QM_rational3`, whose proof is `sorry` there, is omitted): I2's objects and
  leaves (`PkgI2.*`).
* §C (new, namespace `ObjBridge`): the shared layer. The object is I2's
  `Grp (Over (Spec K))` with `[PkgI2.IsAbelianVariety A]`, `K : Type`; `Hom`, `End`, `End0`, `T`,
  `V`, `galRep`, `dim` are I3's through `ofGrp`. The bridge `homOfGrp : (A ⟶ B) → Hom A B` is a
  bijection (`homEquiv`), compatible with composition and identities (`endMulEquiv`), and
  `ofGrp`/`toGrp` are mutually inverse on objects (both round trips `rfl`).
* §D: every I2 and I3 leaf restated over the shared layer, each with a proof that it is
  equivalent to the original (`*_iff`), and the I3 glue restated and proved over the shared layer.
No `sorry`, no `axiom`.
-/

noncomputable section

/-! ## 1. The `ℓ`-adic Tate module of an abelian group -/

namespace PkgI3.Tate

variable (ℓ : ℕ) [hℓ : Fact ℓ.Prime] (M : Type*) [AddCommGroup M]

/-- `T_ℓ(M) = lim_n M[ℓⁿ]` (transition maps: multiplication by `ℓ`), realized as the
sequences `(xₙ)` with `x₀ = 0` and `ℓ • xₙ₊₁ = xₙ`; then `xₙ ∈ M[ℓⁿ]`. -/
def T : AddSubgroup (ℕ → M) where
  carrier := {x | x 0 = 0 ∧ ∀ n, ℓ • x (n + 1) = x n}
  add_mem' := by
    rintro x y ⟨hx0, hx⟩ ⟨hy0, hy⟩
    refine ⟨by simp [hx0, hy0], fun n => ?_⟩
    simp [smul_add, hx n, hy n]
  zero_mem' := ⟨rfl, fun n => by simp⟩
  neg_mem' := by
    rintro x ⟨hx0, hx⟩
    refine ⟨by simp [hx0], fun n => ?_⟩
    simp [hx n]

variable {ℓ M}

omit hℓ in
lemma pow_smul_eq_zero {x : ℕ → M} (hx : x ∈ T ℓ M) (n : ℕ) : (ℓ ^ n) • x n = 0 := by
  induction n with
  | zero => simpa using hx.1
  | succ n ih => rw [pow_succ, mul_smul, hx.2 n, ih]

omit hℓ in
lemma nsmul_congr {y : M} {n : ℕ} (hy : (ℓ ^ n) • y = 0) {c d : ℕ}
    (h : (c : ZMod (ℓ ^ n)) = (d : ZMod (ℓ ^ n))) : c • y = d • y := by
  rw [ZMod.natCast_eq_natCast_iff'] at h
  rw [← Nat.mod_add_div' c (ℓ ^ n), ← Nat.mod_add_div' d (ℓ ^ n), add_smul, add_smul,
    mul_smul, mul_smul, hy, smul_zero, smul_zero, h]

instance (n : ℕ) : NeZero (ℓ ^ n) := ⟨pow_ne_zero n hℓ.out.ne_zero⟩

lemma val_cast (a : ℤ_[ℓ]) (n : ℕ) :
    (((PadicInt.toZModPow (n + 1) a).val : ℕ) : ZMod (ℓ ^ n)) = PadicInt.toZModPow n a := by
  rw [← PadicInt.cast_toZModPow n (n + 1) (Nat.le_succ n) a, ZMod.natCast_val]

/-- The `ℤ_ℓ`-action: `(a • x)ₙ = (a mod ℓⁿ) • xₙ`. -/
def smulSeq (a : ℤ_[ℓ]) (x : ℕ → M) : ℕ → M :=
  fun n => (PadicInt.toZModPow n a).val • x n

lemma smulSeq_mem (a : ℤ_[ℓ]) {x : ℕ → M} (hx : x ∈ T ℓ M) : smulSeq a x ∈ T ℓ M := by
  refine ⟨by simp [smulSeq, hx.1], fun n => ?_⟩
  simp only [smulSeq]
  rw [smul_comm, hx.2 n]
  apply nsmul_congr (pow_smul_eq_zero hx n)
  rw [val_cast, ZMod.natCast_zmod_val]

lemma smulSeq_congr {x : ℕ → M} (hx : x ∈ T ℓ M) (n : ℕ) {a : ℤ_[ℓ]} {c : ℕ}
    (h : (c : ZMod (ℓ ^ n)) = PadicInt.toZModPow n a) : smulSeq a x n = c • x n := by
  simp only [smulSeq]
  apply nsmul_congr (pow_smul_eq_zero hx n)
  rw [ZMod.natCast_zmod_val, h]

instance : Module ℤ_[ℓ] (T ℓ M) where
  smul a x := ⟨smulSeq a x.1, smulSeq_mem a x.2⟩
  one_smul x := Subtype.ext <| funext fun n => by
    change smulSeq 1 x.1 n = x.1 n
    rw [smulSeq_congr x.2 n (c := 1) (by simp), one_smul]
  mul_smul a b x := Subtype.ext <| funext fun n => by
    change smulSeq (a * b) x.1 n = smulSeq a (smulSeq b x.1) n
    rw [smulSeq_congr x.2 n (c := (PadicInt.toZModPow n a).val * (PadicInt.toZModPow n b).val)
      (by push_cast; simp), mul_smul]
    rfl
  smul_zero a := Subtype.ext <| funext fun n => by
    change smulSeq a 0 n = 0
    simp [smulSeq]
  smul_add a x y := Subtype.ext <| funext fun n => by
    change smulSeq a (x.1 + y.1) n = smulSeq a x.1 n + smulSeq a y.1 n
    simp [smulSeq, smul_add]
  add_smul a b x := Subtype.ext <| funext fun n => by
    change smulSeq (a + b) x.1 n = smulSeq a x.1 n + smulSeq b x.1 n
    rw [smulSeq_congr x.2 n (c := (PadicInt.toZModPow n a).val + (PadicInt.toZModPow n b).val)
      (by push_cast; simp), add_smul]
    rfl
  zero_smul x := Subtype.ext <| funext fun n => by
    change smulSeq 0 x.1 n = 0
    simp [smulSeq]

@[simp] lemma smul_apply (a : ℤ_[ℓ]) (x : T ℓ M) (n : ℕ) :
    (a • x).1 n = (PadicInt.toZModPow n a).val • x.1 n := rfl

variable {N : Type*} [AddCommGroup N]

/-- Functoriality: a group homomorphism `M → N` induces a `ℤ_ℓ`-linear map `T_ℓ M → T_ℓ N`. -/
def map (φ : M →+ N) : T ℓ M →ₗ[ℤ_[ℓ]] T ℓ N where
  toFun x := ⟨fun n => φ (x.1 n), by simp [x.2.1], fun n => by rw [← map_nsmul, x.2.2 n]⟩
  map_add' x y := Subtype.ext <| funext fun n => by simp
  map_smul' a x := Subtype.ext <| funext fun n => by simp [map_nsmul]

@[simp] lemma map_apply (φ : M →+ N) (x : T ℓ M) (n : ℕ) : (map φ x).1 n = φ (x.1 n) := rfl

end PkgI3.Tate

/-! ## 2. Abelian varieties, their Hom groups, points, Tate modules -/

namespace PkgI3

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj

universe u

/-- An abelian variety over a field `K`: a group object in schemes over `Spec K` whose structure
morphism is proper, smooth and geometrically integral (Mumford §4, Milne 1986 §1). -/
structure AbVar (K : Type u) [Field K] where
  /-- the underlying `K`-scheme -/
  X : Over (Spec (CommRingCat.of K))
  [grp : GrpObj X]
  [proper : IsProper X.hom]
  [smooth : Smooth X.hom]
  [geomInt : GeometricallyIntegral X.hom]

attribute [instance] AbVar.grp AbVar.proper AbVar.smooth AbVar.geomInt

namespace AbVar

variable {K : Type u} [Field K]

/-- Commutativity is a Mathlib theorem (Stacks 0BFD), not an assumption. -/
instance (A : AbVar K) : IsCommMonObj A.X :=
  isCommMonObj_of_isProper_of_geometricallyIntegral A.X

/-- The dimension of `A` (Krull dimension of the underlying space). -/
def dim (A : AbVar K) : WithBot ℕ∞ := topologicalKrullDim A.X.left

/-- The homomorphisms `A → B` of group schemes over `K`, as a subgroup of the commutative group
of all `K`-morphisms `A → B` (pointwise product, `Hom.commGroup`). -/
def homGroup (A B : AbVar K) : Subgroup (A.X ⟶ B.X) where
  carrier := {f | IsMonHom f}
  one_mem' := by
    change IsMonHom (toUnit A.X ≫ η[B.X])
    infer_instance
  mul_mem' := by
    rintro f g (hf : IsMonHom f) (hg : IsMonHom g)
    change IsMonHom (lift f g ≫ μ[B.X])
    infer_instance
  inv_mem' := by
    rintro f (hf : IsMonHom f)
    change IsMonHom f⁻¹
    infer_instance

/-- `Hom_K(A, B)`, written additively (a `ℤ`-module). -/
abbrev Hom (A B : AbVar K) : Type u := Additive (homGroup A B)

/-- The underlying morphism of schemes. -/
def Hom.hom {A B : AbVar K} (f : Hom A B) : A.X ⟶ B.X := (Additive.toMul f).1

instance {A B : AbVar K} (f : Hom A B) : IsMonHom f.hom := (Additive.toMul f).2

lemma Hom.ext' {A B : AbVar K} {f g : Hom A B} (h : f.hom = g.hom) : f = g :=
  Additive.toMul.injective (Subtype.ext h)

/-- Package a homomorphism. -/
def Hom.mk' {A B : AbVar K} (f : A.X ⟶ B.X) [IsMonHom f] : Hom A B :=
  Additive.ofMul ⟨f, ‹_›⟩

@[simp] lemma Hom.hom_mk' {A B : AbVar K} (f : A.X ⟶ B.X) [IsMonHom f] :
    (Hom.mk' f).hom = f := rfl
@[simp] lemma Hom.hom_add {A B : AbVar K} (f g : Hom A B) : (f + g).hom = f.hom * g.hom := rfl
@[simp] lemma Hom.hom_zero {A B : AbVar K} : (0 : Hom A B).hom = 1 := rfl

/-- The endomorphism ring `End_K(A)`, with multiplication `f * g = f ∘ g`. -/
abbrev End (A : AbVar K) : Type u := Hom A A

instance (A : AbVar K) : Ring (End A) :=
  { (inferInstance : AddCommGroup (End A)) with
    mul := fun f g => Hom.mk' (g.hom ≫ f.hom)
    one := Hom.mk' (𝟙 _)
    mul_assoc := fun f g h => Hom.ext' (by simp [HMul.hMul, Mul.mul])
    one_mul := fun f => Hom.ext' (by simp [HMul.hMul, Mul.mul, OfNat.ofNat, One.one])
    mul_one := fun f => Hom.ext' (by simp [HMul.hMul, Mul.mul, OfNat.ofNat, One.one])
    left_distrib := fun f g h => Hom.ext' (by
      change (g + h).hom ≫ f.hom = g.hom ≫ f.hom * h.hom ≫ f.hom
      simp [MonObj.mul_comp])
    right_distrib := fun f g h => Hom.ext' (by
      change h.hom ≫ (f + g).hom = h.hom ≫ f.hom * h.hom ≫ g.hom
      simp [MonObj.comp_mul])
    zero_mul := fun f => Hom.ext' (by
      change f.hom ≫ (1 : A.X ⟶ A.X) = 1
      simp)
    mul_zero := fun f => Hom.ext' (by
      change (1 : A.X ⟶ A.X) ≫ f.hom = 1
      simp) }

/-- The endomorphism algebra `End⁰_K(A) = ℚ ⊗ End_K(A)`. -/
abbrev End0 (A : AbVar K) : Type u := TensorProduct ℤ ℚ (End A)

/-- A morphism of `K`-schemes is an isogeny-type map: finite and surjective. -/
def IsIsogenyMor {X Y : Over (Spec (CommRingCat.of K))} (f : X ⟶ Y) : Prop :=
  IsFinite f.left ∧ Surjective f.left

/-! ### Points over a field extension and the Galois action -/

variable (L : Type u) [Field L] [Algebra K L]

/-- `Spec L` as a `K`-scheme. -/
def ptObj : Over (Spec (CommRingCat.of K)) :=
  Over.mk (Spec.map (CommRingCat.ofHom (algebraMap K L)))

/-- The group `A(L)` of `L`-points: `K`-morphisms `Spec L → A`. -/
abbrev Pt (A : AbVar K) : Type u := ptObj (K := K) L ⟶ A.X

variable {L}

/-- `σ ∈ Aut_K(L)` acting on `Spec L` over `K`. -/
def galHom (σ : L ≃ₐ[K] L) : ptObj (K := K) L ⟶ ptObj L :=
  Over.homMk (Spec.map (CommRingCat.ofHom (σ : L →+* L))) (by
    simp only [ptObj, Over.mk_hom, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    congr 2
    ext x
    simp)

lemma galHom_one : galHom (1 : L ≃ₐ[K] L) = 𝟙 _ := by
  apply Over.OverMorphism.ext
  change Spec.map (CommRingCat.ofHom ((1 : L ≃ₐ[K] L) : L →+* L)) = 𝟙 (Spec (CommRingCat.of L))
  rw [show CommRingCat.ofHom ((1 : L ≃ₐ[K] L) : L →+* L) = 𝟙 _ from by ext; rfl]
  exact Spec.map_id _

lemma galHom_mul (σ τ : L ≃ₐ[K] L) : galHom (σ * τ) = galHom σ ≫ galHom τ := by
  apply Over.OverMorphism.ext
  change Spec.map (CommRingCat.ofHom ((σ * τ : L ≃ₐ[K] L) : L →+* L)) =
    Spec.map (CommRingCat.ofHom (σ : L →+* L)) ≫ Spec.map (CommRingCat.ofHom (τ : L →+* L))
  rw [← Spec.map_comp]
  congr 1

/-- The Galois action on `A(L)`: `σ • P = P ∘ Spec(σ)`, i.e. `σ` applied to coordinates. -/
def galAct (A : AbVar K) (σ : L ≃ₐ[K] L) : A.Pt L →* A.Pt L where
  toFun P := galHom σ ≫ P
  map_one' := MonObj.comp_one _
  map_mul' _ _ := MonObj.comp_mul _ _ _

/-- A homomorphism `f : A → B` acting on `L`-points. -/
def ptMap {A B : AbVar K} (f : Hom A B) : A.Pt L →* B.Pt L := IsMonHom.monoidHom f.hom _

/-! ### `T_ℓ(A)`, `V_ℓ(A)` and the Galois representation -/

variable (ℓ : ℕ) [Fact ℓ.Prime]

/-- `T_ℓ(A) = lim A(K̄)[ℓⁿ]`, a `ℤ_ℓ`-module. -/
abbrev T (A : AbVar K) : Type u := Tate.T ℓ (Additive (A.Pt (AlgebraicClosure K)))

/-- `V_ℓ(A) = ℚ_ℓ ⊗_{ℤ_ℓ} T_ℓ(A)`. -/
abbrev V (A : AbVar K) : Type u := TensorProduct ℤ_[ℓ] ℚ_[ℓ] (A.T ℓ)

variable {ℓ}

/-- Galois action on `T_ℓ(A)`. -/
def galT (A : AbVar K) (σ : Field.absoluteGaloisGroup K) : A.T ℓ →ₗ[ℤ_[ℓ]] A.T ℓ :=
  Tate.map (MonoidHom.toAdditive (A.galAct σ))

/-- A homomorphism acting on Tate modules. -/
def homT {A B : AbVar K} (f : Hom A B) : A.T ℓ →ₗ[ℤ_[ℓ]] B.T ℓ :=
  Tate.map (MonoidHom.toAdditive (ptMap f))

/-- Galois-equivariance of a `ℤ_ℓ`-linear map of Tate modules. -/
def IsGalEquivariant {A B : AbVar K} (φ : A.T ℓ →ₗ[ℤ_[ℓ]] B.T ℓ) : Prop :=
  ∀ (σ : Field.absoluteGaloisGroup K) (x : A.T ℓ), φ (A.galT σ x) = B.galT σ (φ x)

variable (ℓ)

/-- The Galois representation `ρ_ℓ : G_K → GL(V_ℓ(A))`. -/
def galRep (A : AbVar K) : Representation ℚ_[ℓ] (Field.absoluteGaloisGroup K) (A.V ℓ) where
  toFun σ := (A.galT (ℓ := ℓ) σ).baseChange ℚ_[ℓ]
  map_one' := by
    have : A.galT (ℓ := ℓ) 1 = LinearMap.id := by
      apply LinearMap.ext; intro x; apply Subtype.ext; funext n
      change Additive.ofMul (galHom (1 : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K) ≫
        Additive.toMul (x.1 n)) = x.1 n
      rw [galHom_one, Category.id_comp]; rfl
    change (A.galT (ℓ := ℓ) 1).baseChange ℚ_[ℓ] = LinearMap.id
    rw [this, LinearMap.baseChange_id]
  map_mul' σ τ := by
    have : A.galT (ℓ := ℓ) (σ * τ) = A.galT σ ∘ₗ A.galT τ := by
      apply LinearMap.ext; intro x; apply Subtype.ext; funext n
      have h := galHom_mul (K := K) (L := AlgebraicClosure K) σ τ
      change Additive.ofMul (galHom (σ * τ : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K) ≫
        Additive.toMul (x.1 n)) = Additive.ofMul (galHom σ ≫ galHom τ ≫ Additive.toMul (x.1 n))
      exact (congrArg (fun g => Additive.ofMul (g ≫ Additive.toMul (x.1 n))) h).trans
        (by rw [Category.assoc])
    change (A.galT (ℓ := ℓ) (σ * τ)).baseChange ℚ_[ℓ] =
      (A.galT σ).baseChange ℚ_[ℓ] ∘ₗ (A.galT τ).baseChange ℚ_[ℓ]
    rw [this, LinearMap.baseChange_comp]

/-- The action of `Hom(A, B)` on Tate modules, as a group homomorphism. -/
def tateHom (A B : AbVar K) : Hom A B →+ (A.T ℓ →ₗ[ℤ_[ℓ]] B.T ℓ) where
  toFun f := homT f
  map_zero' := by
    apply LinearMap.ext; intro x; apply Subtype.ext; funext n
    simp [homT, ptMap, IsMonHom.monoidHom]
  map_add' f g := by
    apply LinearMap.ext; intro x; apply Subtype.ext; funext n
    simp [homT, ptMap, IsMonHom.monoidHom, MonObj.comp_mul]

/-- The `ℤ_ℓ`-linear extension `ℤ_ℓ ⊗_ℤ Hom(A, B) → Hom_{ℤ_ℓ}(T_ℓ A, T_ℓ B)`, `a ⊗ f ↦ a · T_ℓ(f)`.
  -/
def tateHomZl (A B : AbVar K) :
    TensorProduct ℤ ℤ_[ℓ] (Hom A B) →ₗ[ℤ] (A.T ℓ →ₗ[ℤ_[ℓ]] B.T ℓ) :=
  TensorProduct.lift
    (LinearMap.mk₂ ℤ (fun (a : ℤ_[ℓ]) (f : Hom A B) => a • tateHom ℓ A B f)
      (fun a b f => add_smul a b _)
      (fun n a f => by rw [smul_assoc])
      (fun a f g => by rw [map_add, smul_add])
      (fun n a f => by rw [map_zsmul, smul_comm]))

end AbVar

end PkgI3

/-! ### Base change -/

namespace PkgI3.AbVar

open CategoryTheory AlgebraicGeometry Limits

variable {K : Type} [Field K]

/-- Base change `A_L` along a field extension `L/K` (Mathlib's `Over.pullback`; the group
structure is transported by the monoidal functor `Over.pullback`). -/
def baseChange (A : AbVar K) (L : Type) [Field L] [Algebra K L] : AbVar L :=
  let f := Spec.map (CommRingCat.ofHom (algebraMap K L))
  letI : GrpObj ((Over.pullback f).obj A.X) := Functor.grpObjObj
  haveI : IsProper ((Over.pullback f).obj A.X).hom := by dsimp; infer_instance
  haveI : Smooth ((Over.pullback f).obj A.X).hom := by dsimp; infer_instance
  haveI : GeometricallyIntegral ((Over.pullback f).obj A.X).hom := by dsimp; infer_instance
  { X := (Over.pullback f).obj A.X }

instance geometricallyIntegral_id_spec (K : Type) [Field K] :
    GeometricallyIntegral (𝟙 (Spec (CommRingCat.of K))) := by
  constructor
  intro L _ y Z fst snd h
  have : IsIso snd := h.isIso_snd_of_isIso
  have : Nonempty Z := ⟨(inv snd) (IsLocalRing.closedPoint L)⟩
  exact isIntegral_of_isOpenImmersion snd

open MonoidalCategory in
/-- Sanity check: `AbVar K` is inhabited (by `Spec K`, the zero abelian variety). No
nonzero abelian variety can be constructed in Mathlib v4.35.0: it has no projective group
scheme (Weierstrass curves exist only as point sets, not as `GrpObj`s in `Over (Spec K)`). -/
def zero (K : Type) [Field K] : AbVar K :=
  haveI : IsProper (𝟙_ (Over (Spec (CommRingCat.of K)))).hom := by dsimp; infer_instance
  haveI : Smooth (𝟙_ (Over (Spec (CommRingCat.of K)))).hom := by dsimp; infer_instance
  haveI : GeometricallyIntegral (𝟙_ (Over (Spec (CommRingCat.of K)))).hom := by
    dsimp; infer_instance
  { X := 𝟙_ (Over (Spec (CommRingCat.of K))) }

end PkgI3.AbVar

/-! ## 3. The leaves of package I3

Each leaf is a `Prop` quantified over all fields (resp. number fields) and all abelian varieties
in the sense of `AbVar`; universe `0`. Locators: see `docs/research/pkg-I3.md`. -/

namespace PkgI3

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open AbVar Polynomial
open scoped Quaternion TensorProduct

/-- Every nonzero endomorphism is an isogeny (equivalently `End⁰(A)` is a division algebra);
in characteristic `0` this is equivalent to `A` being simple (Mumford §19, Thm 1 and Cor. 2). -/
def EndDivision {k : Type} [Field k] (A : AbVar k) : Prop :=
  ∀ f : End A, f ≠ 0 → IsIsogenyMor f.hom

/-- **I3.F1 — Faltings 1983, Satz 3 (semisimplicity).** For an abelian variety `A` over a number
field `K` and a prime `ℓ`, the representation of `G_K` on `V_ℓ(A)` is semisimple. -/
def FaltingsSemisimple : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (A : AbVar K) (ℓ : ℕ) [Fact ℓ.Prime],
    (A.galRep ℓ).IsSemisimpleRepresentation

/-- **I3.F2 — Faltings 1983, Satz 4 (`A = B`) and Korollar 1 (Tate's conjecture).** For abelian
varieties `A, B` over a number field `K` and a prime `ℓ`, the natural map
`Hom_K(A, B) ⊗ ℤ_ℓ → Hom_{ℤ_ℓ}(T_ℓ A, T_ℓ B)` is injective with image the `G_K`-equivariant maps. -/
def FaltingsTate : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (A B : AbVar K) (ℓ : ℕ) [Fact ℓ.Prime],
    Function.Injective (tateHomZl ℓ A B) ∧
      Set.range (tateHomZl ℓ A B) = {φ | IsGalEquivariant φ}

/-- **I3.M0 — structure of the Tate module (Mumford §4, `A[n] ≅ (ℤ/n)^{2g}` for `char k ∤ n`;
§18-19).** For `ℓ ≠ char k`, `T_ℓ(A)` is free of rank `2 dim A` over `ℤ_ℓ`. -/
def TateModuleFree : Prop :=
  ∀ (k : Type) [Field k] (A : AbVar k) (ℓ : ℕ) [Fact ℓ.Prime], (ℓ : k) ≠ 0 →
    Module.Free ℤ_[ℓ] (A.T ℓ) ∧ Module.Finite ℤ_[ℓ] (A.T ℓ) ∧
      ((Module.finrank ℤ_[ℓ] (A.T ℓ) : ℕ∞) : WithBot ℕ∞) = 2 * A.dim

/-- **I3.M1 — Mumford §19, Thm 3.** `Hom(A, B)` is a free `ℤ`-module of finite rank
`≤ 4 dim A dim B`, and for `ℓ ≠ char k` the map `Hom(A, B) ⊗ ℤ_ℓ → Hom(T_ℓ A, T_ℓ B)` is injective.
-/
def HomFreeFinite : Prop :=
  ∀ (k : Type) [Field k] (A B : AbVar k),
    Module.Free ℤ (Hom A B) ∧ Module.Finite ℤ (Hom A B) ∧
      ((Module.finrank ℤ (Hom A B) : ℕ∞) : WithBot ℕ∞) ≤ 4 * A.dim * B.dim ∧
      ∀ (ℓ : ℕ) [Fact ℓ.Prime], (ℓ : k) ≠ 0 → Function.Injective (tateHomZl ℓ A B)

/-- **I3.M2 — Mumford §19, Thm 4 (independence of `ℓ`).** For `φ ∈ End(A)` there is a monic
`P ∈ ℤ[X]` that is the characteristic polynomial of `V_ℓ(φ)` for every prime `ℓ ≠ char k`
(computed in any finite basis). -/
def CharPolyIndepOfEll : Prop :=
  ∀ (k : Type) [Field k] (A : AbVar k) (φ : End A), ∃ P : ℤ[X], P.Monic ∧
    ∀ (ℓ : ℕ) [Fact ℓ.Prime], (ℓ : k) ≠ 0 →
      ∀ (I : Type) [Fintype I] [DecidableEq I] (b : Module.Basis I ℚ_[ℓ] (A.V ℓ)),
        (LinearMap.toMatrix b b ((homT (ℓ := ℓ) φ).baseChange ℚ_[ℓ])).charpoly =
          P.map (Int.castRingHom ℚ_[ℓ])

/-- **I3.M3 — Poincaré complete reducibility (Mumford §19, Thm 1), in the form used at E1.**
Over a field of characteristic `0`, if `End⁰(A)` is a division algebra and `f : A → J` is a
nonzero homomorphism, there are an abelian variety `Z` and a homomorphism `g : Z → J` such that
`(f, g) : A × Z → J`, `(a, z) ↦ f(a) + g(z)`, is an isogeny. -/
def PoincareReducibility : Prop :=
  ∀ (k : Type) [Field k] [CharZero k] (A J : AbVar k), EndDivision A →
    ∀ f : Hom A J, f ≠ 0 → ∃ (Z : AbVar k) (g : Hom Z J),
      IsIsogenyMor (fst A.X Z.X ≫ f.hom * snd A.X Z.X ≫ g.hom)

/-- **I3.Q — the QM dichotomy (step A9).** Over an algebraically closed field of characteristic
`0`, if a quaternion division algebra `B = (a, b)_ℚ` embeds in `End⁰(A)` for an abelian surface
`A`, then `End⁰(A) ≅ B` or `End⁰(A) ≅ M₂(ℚ(√d))` with `d < 0`. (Consequence of Mumford §19
Thm 1, Cor. 2, §21 (Albert, `[D:ℚ] ∣ 2g` in characteristic `0`) and §22; see the note.) -/
def QMDichotomy : Prop :=
  ∀ (k : Type) [Field k] [IsAlgClosed k] [CharZero k] (A : AbVar k), A.dim = 2 →
    ∀ a b : ℚ, (∀ x : ℍ[ℚ, a, b], x ≠ 0 → IsUnit x) →
      Nonempty (ℍ[ℚ, a, b] →ₐ[ℚ] End0 A) →
        Nonempty (End0 A ≃ₐ[ℚ] ℍ[ℚ, a, b]) ∨
          ∃ d : ℚ, d < 0 ∧
            Nonempty (End0 A ≃ₐ[ℚ] Matrix (Fin 2) (Fin 2) (AdjoinRoot (Polynomial.X ^ 2 -
                Polynomial.C d)))

/-- The package as one hypothesis. -/
structure I3Leaves : Prop where
  faltingsSemisimple : FaltingsSemisimple
  faltingsTate : FaltingsTate
  tateModuleFree : TateModuleFree
  homFreeFinite : HomFreeFinite
  charPolyIndepOfEll : CharPolyIndepOfEll
  poincare : PoincareReducibility
  qmDichotomy : QMDichotomy

end PkgI3

/-! ## 4. Glue checks: the leaves are usable with these definitions -/

namespace PkgI3

open CategoryTheory AlgebraicGeometry MonObj AbVar
open scoped TensorProduct

/-- The easy half of Faltings' statement holds outright: the image of `Hom(A, B) ⊗ ℤ_ℓ`
consists of Galois-equivariant maps. (So `FaltingsTate` asserts injectivity and the reverse
inclusion, as in the published statement.) -/
lemma homT_galT {K : Type} [Field K] {A B : AbVar K} {ℓ : ℕ} [Fact ℓ.Prime] (f : Hom A B)
    (σ : Field.absoluteGaloisGroup K) (x : A.T ℓ) :
    homT f (A.galT σ x) = B.galT σ (homT f x) := by
  apply Subtype.ext; funext n
  change Additive.ofMul ((galHom σ ≫ Additive.toMul (x.1 n)) ≫ f.hom) =
    Additive.ofMul (galHom σ ≫ (Additive.toMul (x.1 n) ≫ f.hom))
  rw [Category.assoc]

theorem range_tateHomZl_subset {K : Type} [Field K] (A B : AbVar K) (ℓ : ℕ) [Fact ℓ.Prime] :
    Set.range (tateHomZl ℓ A B) ⊆ {φ | IsGalEquivariant φ} := by
  rintro _ ⟨z, rfl⟩
  induction z using TensorProduct.induction_on with
  | zero => intro σ x; simp
  | tmul a f =>
    intro σ x
    have e : tateHomZl ℓ A B (a ⊗ₜ f) = a • tateHom ℓ A B f := rfl
    rw [e, LinearMap.smul_apply, LinearMap.smul_apply, map_smul]
    exact congrArg (a • ·) (homT_galT f σ x)
  | add y z hy hz =>
    intro σ x
    simp only [map_add, LinearMap.add_apply, hy σ x, hz σ x]

/-- **Glue for E1.** From Faltings' theorem and the structure of `T_ℓ`: a nonzero
`G_K`-equivariant `ℚ_ℓ`-linear map `V_ℓ(A) → V_ℓ(B)` forces a nonzero homomorphism `A → B`. -/
theorem exists_hom_ne_zero_of_equivariant (hF : FaltingsTate) (hT : TateModuleFree)
    {K : Type} [Field K] [NumberField K] (A B : AbVar K) (ℓ : ℕ) [Fact ℓ.Prime]
    (φ : A.V ℓ →ₗ[ℚ_[ℓ]] B.V ℓ) (hφ : φ ≠ 0)
    (heq : ∀ σ, φ ∘ₗ A.galRep ℓ σ = B.galRep ℓ σ ∘ₗ φ) : ∃ f : Hom A B, f ≠ 0 := by
  classical
  have hℓK : (ℓ : K) ≠ 0 := Nat.cast_ne_zero.mpr (Fact.out : ℓ.Prime).ne_zero
  obtain ⟨-, hfinA, -⟩ := hT K A ℓ hℓK
  obtain ⟨hfreeB, -, -⟩ := hT K B ℓ hℓK
  have : Module.FinitePresentation ℤ_[ℓ] (A.T ℓ) := Module.finitePresentation_of_finite _ _
  let ιA : A.T ℓ →ₗ[ℤ_[ℓ]] A.V ℓ := TensorProduct.mk ℤ_[ℓ] ℚ_[ℓ] (A.T ℓ) 1
  let ιB : B.T ℓ →ₗ[ℤ_[ℓ]] B.V ℓ := TensorProduct.mk ℤ_[ℓ] ℚ_[ℓ] (B.T ℓ) 1
  have : IsLocalizedModule (nonZeroDivisors ℤ_[ℓ]) ιB := inferInstance
  obtain ⟨h, s, hs⟩ := Module.FinitePresentation.exists_lift_of_isLocalizedModule
    (nonZeroDivisors ℤ_[ℓ]) ιB ((φ.restrictScalars ℤ_[ℓ]) ∘ₗ ιA)
  have hs0 : (s : ℤ_[ℓ]) ≠ 0 := nonZeroDivisors.ne_zero s.2
  -- `ιB` is injective (`T_ℓ B` is free, hence torsion-free).
  have hιB : Function.Injective ιB := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro y hy
    obtain ⟨t, ht⟩ := (IsLocalizedModule.eq_zero_iff (nonZeroDivisors ℤ_[ℓ]) ιB).mp hy
    exact (smul_eq_zero.mp ht).resolve_left (nonZeroDivisors.ne_zero t.2)
  -- the Galois actions commute with `ι`
  have hιAσ : ∀ σ x, ιA (A.galT σ x) = A.galRep ℓ σ (ιA x) := fun σ x => by
    simp [ιA, galRep, LinearMap.baseChange_tmul]
  have hιBσ : ∀ σ x, ιB (B.galT σ x) = B.galRep ℓ σ (ιB x) := fun σ x => by
    simp [ιB, galRep, LinearMap.baseChange_tmul]
  have hsφ : ∀ x, ιB (h x) = (s : ℤ_[ℓ]) • φ (ιA x) := fun x => by
    have := congrArg (fun g => g x) hs
    simp only [LinearMap.coe_comp, Function.comp_apply, LinearMap.smul_apply,
      LinearMap.coe_restrictScalars, Submonoid.smul_def] at this
    exact this
  -- `h` is equivariant
  have hheq : IsGalEquivariant h := by
    intro σ x
    apply hιB
    rw [hsφ, hιAσ, hιBσ, hsφ]
    have := congrArg (fun g => g (ιA x)) (heq σ)
    simp only [LinearMap.coe_comp, Function.comp_apply] at this
    rw [this, LinearMap.map_smul_of_tower]
  -- `h ≠ 0`
  have hh0 : h ≠ 0 := by
    intro h0
    apply hφ
    have hφι : ∀ x, φ (ιA x) = 0 := fun x => by
      have h1 : (s : ℤ_[ℓ]) • φ (ιA x) = 0 := by rw [← hsφ, h0]; simp
      rw [← algebraMap_smul ℚ_[ℓ] (s : ℤ_[ℓ])] at h1
      exact (smul_eq_zero.mp h1).resolve_left (by
        simpa using (IsFractionRing.injective ℤ_[ℓ] ℚ_[ℓ]).ne hs0)
    apply LinearMap.ext
    intro v
    induction v using TensorProduct.induction_on with
    | zero => simp
    | tmul q x =>
      have : (q ⊗ₜ[ℤ_[ℓ]] x : A.V ℓ) = q • ιA x := by simp [ιA, TensorProduct.smul_tmul']
      rw [this, map_smul, hφι, smul_zero, LinearMap.zero_apply]
    | add v w hv hw => simp [map_add, hv, hw]
  -- conclude with Faltings
  obtain ⟨z, hz⟩ : h ∈ Set.range (tateHomZl ℓ A B) := by
    rw [(hF K A B ℓ).2]; exact hheq
  by_contra hall
  simp only [ne_eq, not_exists, not_not] at hall
  have : Subsingleton (Hom A B) := ⟨fun f g => (hall f).trans (hall g).symm⟩
  have : z = 0 := Subsingleton.elim _ _
  exact hh0 (by rw [← hz, this, map_zero])

/-- The `G_K`-equivariant `ℚ_ℓ`-linear endomorphisms of `V_ℓ(A)`. -/
def equivEnd {K : Type} [Field K] (A : AbVar K) (ℓ : ℕ) [Fact ℓ.Prime] :
    Submodule ℚ_[ℓ] (Module.End ℚ_[ℓ] (A.V ℓ)) where
  carrier := {φ | ∀ σ, φ ∘ₗ A.galRep ℓ σ = A.galRep ℓ σ ∘ₗ φ}
  add_mem' := by
    intro φ ψ hφ hψ σ
    simp only [Set.mem_setOf_eq] at *
    rw [LinearMap.add_comp, LinearMap.comp_add, hφ σ, hψ σ]
  zero_mem' := by intro σ; simp
  smul_mem' := by
    intro c φ hφ σ
    simp only [Set.mem_setOf_eq] at *
    rw [LinearMap.smul_comp, LinearMap.comp_smul, hφ σ]

/-- **Glue for C2 (GLUE, proved).** The `ℚ_ℓ`-form of Satz 4:
`dim_{ℚ_ℓ} End_{G_K}(V_ℓ A) = rank_ℤ End_K(A)`. With `FaltingsSemisimple` and
`End⁰_K(A) ≅ B` (A9, A10, and `L'` defining every geometric endomorphism), the commutant
argument of N5 L731-734 then gives absolute irreducibility of `r_ℓ`.
Proof: `T_ℓ A` is free of finite rank (`TateModuleFree`), so every `φ ∈ End(V_ℓ A)`
has `ℓᵏφ(T_ℓ A) ⊆ T_ℓ A`; equivariance passes to `T_ℓ A` because `T_ℓ A → V_ℓ A` is injective
(as in `exists_hom_ne_zero_of_equivariant`); so `End_G(V) = ℚ_ℓ ⊗ End_G(T)`, and
`End_G(T) ≅ ℤ_ℓ ⊗ End(A)` (`FaltingsTate`) is free of rank `rank_ℤ End(A)` (`HomFreeFinite`). -/
theorem finrank_equivEnd (hF : FaltingsTate) (hT : TateModuleFree) (hH : HomFreeFinite)
    {K : Type} [Field K] [NumberField K] (A : AbVar K) (ℓ : ℕ) [Fact ℓ.Prime] :
    Module.finrank ℚ_[ℓ] (equivEnd A ℓ) = Module.finrank ℤ (End A) := by
  classical
  have hℓK : (ℓ : K) ≠ 0 := Nat.cast_ne_zero.mpr (Fact.out : ℓ.Prime).ne_zero
  obtain ⟨hfree, hfin, -⟩ := hT K A ℓ hℓK
  obtain ⟨hHfree, hHfin, -, -⟩ := hH K A A
  have : Module.FinitePresentation ℤ_[ℓ] (A.T ℓ) := Module.finitePresentation_of_finite _ _
  let jT : A.T ℓ →ₗ[ℤ_[ℓ]] A.V ℓ := TensorProduct.mk ℤ_[ℓ] ℚ_[ℓ] (A.T ℓ) 1
  have : IsLocalizedModule (nonZeroDivisors ℤ_[ℓ]) jT := inferInstance
  have hj : Function.Injective jT := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro y hy
    obtain ⟨t, ht⟩ := (IsLocalizedModule.eq_zero_iff (nonZeroDivisors ℤ_[ℓ]) jT).mp hy
    exact (smul_eq_zero.mp ht).resolve_left (nonZeroDivisors.ne_zero t.2)
  have hjσ : ∀ σ x, jT (A.galT σ x) = A.galRep ℓ σ (jT x) := fun σ x => by
    simp [jT, galRep, LinearMap.baseChange_tmul]
  have hjψ : ∀ (ψ : Module.End ℤ_[ℓ] (A.T ℓ)) x, jT (ψ x) = ψ.baseChange ℚ_[ℓ] (jT x) :=
    fun ψ x => by simp [jT, LinearMap.baseChange_tmul]
  -- the equivariant endomorphisms of `T_ℓ A`
  let ET : Submodule ℤ_[ℓ] (Module.End ℤ_[ℓ] (A.T ℓ)) :=
    { carrier := {ψ | IsGalEquivariant ψ}
      add_mem' := fun {ψ χ} hψ hχ σ x => by
        simp only [LinearMap.add_apply, map_add, hψ σ x, hχ σ x]
      zero_mem' := fun σ x => by simp
      smul_mem' := fun c ψ hψ σ x => by
        simp only [LinearMap.smul_apply, map_smul, hψ σ x] }
  -- Step 1: `ET ≅ ℤ_ℓ ⊗ End A` (Faltings), so `rank ET = rank End A`.
  have hsmul : ∀ (a : ℤ_[ℓ]) z, tateHomZl ℓ A A (a • z) = a • tateHomZl ℓ A A z := by
    intro a z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul b f =>
      rw [TensorProduct.smul_tmul', smul_eq_mul,
        show tateHomZl ℓ A A ((a * b) ⊗ₜ f) = (a * b) • tateHom ℓ A A f from rfl,
        show tateHomZl ℓ A A (b ⊗ₜ f) = b • tateHom ℓ A A f from rfl, mul_smul]
    | add y z hy hz => rw [smul_add, map_add, map_add, hy, hz, smul_add]
  let L1 : TensorProduct ℤ ℤ_[ℓ] (End A) →ₗ[ℤ_[ℓ]] ET :=
    { toFun := fun z => ⟨tateHomZl ℓ A A z, range_tateHomZl_subset A A ℓ ⟨z, rfl⟩⟩
      map_add' := fun y z => Subtype.ext (map_add _ y z)
      map_smul' := fun a z => Subtype.ext (hsmul a z) }
  have hL1 : Function.Bijective L1 := by
    refine ⟨fun y z h => (hF K A A ℓ).1 (congrArg Subtype.val h), fun ψ => ?_⟩
    obtain ⟨z, hz⟩ : ψ.1 ∈ Set.range (tateHomZl ℓ A A) := by
      rw [(hF K A A ℓ).2]; exact ψ.2
    exact ⟨z, Subtype.ext hz⟩
  have h1 : Module.finrank ℤ_[ℓ] ET = Module.finrank ℤ (End A) := by
    rw [← (LinearEquiv.ofBijective L1 hL1).finrank_eq, Module.finrank_baseChange]
  -- Step 2: `equivEnd A ℓ` is the localization of `ET`.
  let Φ : ET →ₗ[ℤ_[ℓ]] equivEnd A ℓ :=
    { toFun := fun ψ => ⟨ψ.1.baseChange ℚ_[ℓ], fun σ => by
        change ψ.1.baseChange ℚ_[ℓ] ∘ₗ (A.galT σ).baseChange ℚ_[ℓ] =
          (A.galT σ).baseChange ℚ_[ℓ] ∘ₗ ψ.1.baseChange ℚ_[ℓ]
        rw [← LinearMap.baseChange_comp, ← LinearMap.baseChange_comp]
        congr 1
        exact LinearMap.ext fun x => ψ.2 σ x⟩
      map_add' := fun ψ χ => Subtype.ext (LinearMap.baseChange_add _ _)
      map_smul' := fun c ψ => Subtype.ext (LinearMap.baseChange_smul _ _) }
  have hΦ : IsLocalizedModule (nonZeroDivisors ℤ_[ℓ]) Φ := by
    constructor
    · intro s
      have hc : algebraMap ℤ_[ℓ] ℚ_[ℓ] (s : ℤ_[ℓ]) ≠ 0 := by
        simpa using (IsFractionRing.injective ℤ_[ℓ] ℚ_[ℓ]).ne (nonZeroDivisors.ne_zero s.2)
      rw [Module.End.isUnit_iff]
      constructor
      · intro x y hxy
        simp only [Module.algebraMap_end_apply] at hxy
        rw [← algebraMap_smul ℚ_[ℓ] (s : ℤ_[ℓ]) x, ← algebraMap_smul ℚ_[ℓ] (s : ℤ_[ℓ]) y] at hxy
        exact smul_right_injective _ hc hxy
      · intro y
        refine ⟨(algebraMap ℤ_[ℓ] ℚ_[ℓ] (s : ℤ_[ℓ]))⁻¹ • y, ?_⟩
        simp only [Module.algebraMap_end_apply]
        rw [← algebraMap_smul ℚ_[ℓ] (s : ℤ_[ℓ]), smul_smul, mul_inv_cancel₀ hc, one_smul]
    · intro φ
      obtain ⟨h, s, hs⟩ := Module.FinitePresentation.exists_lift_of_isLocalizedModule
        (nonZeroDivisors ℤ_[ℓ]) jT ((φ.1.restrictScalars ℤ_[ℓ]) ∘ₗ jT)
      have hsφ : ∀ x, jT (h x) = (s : ℤ_[ℓ]) • φ.1 (jT x) := fun x => by
        have := congrArg (fun g => g x) hs
        simp only [LinearMap.coe_comp, Function.comp_apply, LinearMap.smul_apply,
          LinearMap.coe_restrictScalars, Submonoid.smul_def] at this
        exact this
      have hheq : IsGalEquivariant h := by
        intro σ x
        apply hj
        rw [hsφ, hjσ, hjσ, hsφ]
        have := congrArg (fun g => g (jT x)) (φ.2 σ)
        simp only [LinearMap.coe_comp, Function.comp_apply] at this
        rw [this, LinearMap.map_smul_of_tower]
      refine ⟨⟨⟨h, hheq⟩, s⟩, Subtype.ext ?_⟩
      apply TensorProduct.AlgebraTensorModule.curry_injective
      apply LinearMap.ext_ring
      apply LinearMap.ext
      intro x
      change (s : ℤ_[ℓ]) • φ.1 ((1 : ℚ_[ℓ]) ⊗ₜ x) = h.baseChange ℚ_[ℓ] ((1 : ℚ_[ℓ]) ⊗ₜ x)
      exact (hsφ x).symm.trans (hjψ h x)
    · intro ψ χ hψχ
      refine ⟨1, ?_⟩
      rw [one_smul, one_smul]
      apply Subtype.ext
      apply LinearMap.ext
      intro x
      apply hj
      rw [hjψ, hjψ]
      exact congrArg (fun g => g (jT x)) (congrArg Subtype.val hψχ)
  have e1 := IsLocalization.finrank_eq (R := ℤ_[ℓ]) (N := equivEnd A ℓ) ℚ_[ℓ]
    (nonZeroDivisors ℤ_[ℓ]) le_rfl
  have e2 := IsLocalizedModule.finrank_eq (M := ET) (N := equivEnd A ℓ) (p := nonZeroDivisors ℤ_[ℓ])
      (f := Φ) le_rfl
  rw [e1, e2, h1]

end PkgI3

/-! # §B. Copied from scratch/pkg-I2/I2.lean (glue A6, a sorry there, omitted) -/

universe u

open CategoryTheory AlgebraicGeometry Limits
open scoped CategoryTheory.MonObj

namespace PkgI2

/-! ## 1. Purity of the branch locus (SGA 1 X 3.4; Stacks 0BMB), ring form -/

/-- **Leaf I2-P (Zariski–Nagata purity of the branch locus).**
Ring form of Stacks Tag 0BMB (SGA 1, Exp. X, Thm 3.4, numbering UNVERIFIED):
let `R → S` be of finite type with `R` Noetherian, `q` a prime of `S` over `p`, with `R_p` regular,
`S_q` a normal domain, `S` quasi-finite at `q`, `dim S_q = dim R_p ≥ 1`, and `R → S` unramified at
every prime `q' ⊆ q` of height one. Then `R → S` is étale at `q`. -/
def PurityBranchLocus : Prop :=
  ∀ (R S : Type u) [CommRing R] [CommRing S] [Algebra R S] [IsNoetherianRing R]
    [Algebra.FiniteType R S] (q : Ideal S) [q.IsPrime],
    IsRegularLocalRing (Localization.AtPrime (q.comap (algebraMap R S))) →
    IsDomain (Localization.AtPrime q) →
    IsIntegrallyClosed (Localization.AtPrime q) →
    Algebra.QuasiFiniteAt R q →
    ringKrullDim (Localization.AtPrime q) =
      ringKrullDim (Localization.AtPrime (q.comap (algebraMap R S))) →
    1 ≤ ringKrullDim (Localization.AtPrime q) →
    (∀ (q' : Ideal S) [q'.IsPrime], q' ≤ q → q'.height = 1 → Algebra.IsUnramifiedAt R q') →
    Algebra.IsEtaleAt R q

/-! ## 2. Abelian varieties, points, Galois action, inertia, good reduction -/

section AV

variable {K : Type u} [Field K]

/-- `Spec L` as a scheme over `Spec K`. -/
noncomputable def specOver (K L : Type u) [Field K] [CommRing L] [Algebra K L] :
    Over (Spec (.of K)) :=
  Over.mk (Spec.map (CommRingCat.ofHom (algebraMap K L)))

/-- An abelian variety over `K`: a group object of `Over (Spec K)` whose structure morphism is
proper, smooth and geometrically integral (Mathlib's notions). Mathlib proves that such a group
object is commutative (`isCommMonObj_of_isProper_of_geometricallyIntegral`). -/
class IsAbelianVariety (A : Grp (Over (Spec (.of K)))) : Prop where
  proper : IsProper A.X.hom
  smooth : Smooth A.X.hom
  geomIntegral : GeometricallyIntegral A.X.hom

/-- An abelian scheme over a ring `O`: a group object of `Over (Spec O)`, proper, smooth, with
geometrically connected fibres (Mumford, GIT, Def. 6.1). -/
class IsAbelianScheme {O : Type u} [CommRing O] (𝒜 : Grp (Over (Spec (.of O)))) : Prop where
  proper : IsProper 𝒜.X.hom
  smooth : Smooth 𝒜.X.hom
  geomConnected : GeometricallyConnected 𝒜.X.hom

/-- The `L`-points `A(L)` of a scheme over `K`, for a `K`-algebra `L`; for a group object this
is a group (`MonObj.Hom.group`). -/
abbrev Pts (A : Grp (Over (Spec (.of K)))) (L : Type u) [CommRing L] [Algebra K L] :=
  specOver K L ⟶ A.X

/-- The `m`-torsion `A(L)[m]`. -/
def torsion (A : Grp (Over (Spec (.of K)))) (L : Type u) [CommRing L] [Algebra K L] (m : ℕ) :
    Set (Pts A L) :=
  {x | x ^ m = 1}

/-- The automorphism of `Spec L` over `Spec K` induced by `σ ∈ Aut(L/K)`. -/
noncomputable def galHom (L : Type u) [CommRing L] [Algebra K L] (σ : L ≃ₐ[K] L) :
    specOver K L ⟶ specOver K L :=
  Over.homMk (Spec.map (CommRingCat.ofHom (σ : L →+* L))) (by
    simp only [specOver, Over.mk_hom, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    congr 2
    ext x
    simp)

/-- The Galois action on points: `(σ • x)` has coordinates `σ ∘ x^*`. -/
noncomputable def galAct (A : Grp (Over (Spec (.of K)))) {L : Type u} [CommRing L] [Algebra K L]
    (σ : L ≃ₐ[K] L) (x : Pts A L) : Pts A L :=
  galHom L σ ≫ x

/-- `σ` lies in the inertia group of the valuation subring `w` of `L` (Mathlib's
`ValuationSubring.inertiaSubgroup`). -/
def IsInertia {L : Type u} [Field L] [Algebra K L] (w : ValuationSubring L) (σ : L ≃ₐ[K] L) :
    Prop :=
  ∃ h : σ ∈ w.decompositionSubgroup K,
    (⟨σ, h⟩ : w.decompositionSubgroup K) ∈ w.inertiaSubgroup K

/-- `A` has good reduction at the valuation subring `O` of `K`: there is an abelian scheme over
`O` whose generic fibre is isomorphic to `A` as a group object over `K` (Serre–Tate 1968, §1). -/
def HasGoodReduction (A : Grp (Over (Spec (.of K)))) (O : ValuationSubring K) : Prop :=
  ∃ 𝒜 : Grp (Over (Spec (.of O))), IsAbelianScheme 𝒜 ∧
    Nonempty ((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap O K)))).mapGrp.obj 𝒜 ≅ A)

/-- The inertia group of `w` acts trivially on `A(L)[m]`. -/
def InertiaTrivialOn (A : Grp (Over (Spec (.of K)))) {L : Type u} [Field L] [Algebra K L]
    (w : ValuationSubring L) (m : ℕ) : Prop :=
  ∀ σ : L ≃ₐ[K] L, IsInertia w σ → ∀ x ∈ torsion A L m, galAct A σ x = x

/-- `(σ - 1)² x = 0`, written multiplicatively (the group of points is commutative). -/
def UnipSq (A : Grp (Over (Spec (.of K)))) {L : Type u} [CommRing L] [Algebra K L]
    (σ : L ≃ₐ[K] L) (x : Pts A L) : Prop :=
  galAct A σ (galAct A σ x) * (galAct A σ x)⁻¹ * (galAct A σ x)⁻¹ * x = 1

end AV

/-! ## 3. Néron–Ogg–Shafarevich and potential good reduction (Serre–Tate 1968) -/

/-- **Leaf I2-NOS (Serre–Tate 1968, Thm 1; criterion of Néron–Ogg–Shafarevich).**
`K` a field with a discrete valuation ring `O`, `w` a valuation ring of `K̄` over `O`, `A/K` an
abelian variety. Then (a) ⟺ (b) ⟺ (c), where (a) good reduction at `O`, (b) for every `m ≥ 1`
invertible in `O`, inertia at `w` fixes `A(K̄)[m]`, (c) the same for infinitely many such `m`. -/
def NeronOggShafarevich : Prop :=
  ∀ (K : Type u) [Field K] (O : ValuationSubring K) [IsDiscreteValuationRing O]
    (w : ValuationSubring (AlgebraicClosure K)),
    w.comap (algebraMap K (AlgebraicClosure K)) = O →
    ∀ (A : Grp (Over (Spec (.of K)))) [IsAbelianVariety A],
      (HasGoodReduction A O ↔
        ∀ m : ℕ, 0 < m → IsUnit (m : O) → InertiaTrivialOn A w m) ∧
      (HasGoodReduction A O ↔
        {m : ℕ | 0 < m ∧ IsUnit (m : O) ∧ InertiaTrivialOn A w m}.Infinite)


/-- Base change `A_{K'}` of a group object along a field extension `K → K'`. -/
noncomputable def baseChange {K : Type u} [Field K] (A : Grp (Over (Spec (.of K))))
    (K' : Type u) [Field K'] [Algebra K K'] : Grp (Over (Spec (.of K'))) :=
  (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap K K')))).mapGrp.obj A

/-- **Leaf I2-ST2 (Serre–Tate 1968, Thm 2; potential good reduction).** For a prime `ℓ`
invertible in `O`: `A` acquires good reduction over a finite extension `K' ⊆ K̄` (at `w ∩ K'`) iff
an open subgroup `I ∩ G_{K'}` of inertia acts trivially on every `A(K̄)[ℓⁿ]`, i.e. the image of
inertia in `Aut(T_ℓ A)` is finite. Used only on the h-b1 route for A6 (not on the route of §5 of
docs/research/pkg-I2.md). -/
def SerreTatePotentialGood : Prop :=
  ∀ (K : Type u) [Field K] (O : ValuationSubring K) [IsDiscreteValuationRing O]
    (w : ValuationSubring (AlgebraicClosure K)),
    w.comap (algebraMap K (AlgebraicClosure K)) = O →
    ∀ (A : Grp (Over (Spec (.of K)))) [IsAbelianVariety A] (ℓ : ℕ), ℓ.Prime → IsUnit (ℓ : O) →
      ((∃ K' : IntermediateField K (AlgebraicClosure K), FiniteDimensional K K' ∧
          HasGoodReduction (baseChange A K') (w.comap (algebraMap K' (AlgebraicClosure K)))) ↔
       (∃ K' : IntermediateField K (AlgebraicClosure K), FiniteDimensional K K' ∧
          ∀ σ : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K, IsInertia w σ →
            (∀ x ∈ K', σ x = x) →
            ∀ n : ℕ, ∀ x ∈ torsion A (AlgebraicClosure K) (ℓ ^ n), galAct A σ x = x))

/-! ## 4. Semistable reduction: Grothendieck (SGA 7 IX 3.5, 3.6) and Raynaud (SGA 7 IX 4.7) -/

/-- **Leaf I2-SS (Grothendieck's semistable reduction theorem, monodromy form).** Consequence of
SGA 7 I, Exp. IX, Thm 3.6 (`A` acquires semistable reduction over a finite extension `K'`) and
the direction "semistable ⇒ inertia acts unipotently of echelon ≤ 2" of Prop. 3.5 (numbers
UNVERIFIED): there is a finite `K' ⊆ K̄` such that every `σ` in the inertia group of `w` fixing
`K'` satisfies `(σ - 1)² = 0` on `A(K̄)[ℓⁿ]` for every prime `ℓ` invertible in `O` and every `n`.
The finite-level form is equivalent to `(σ-1)² = 0` on `T_ℓ A`, since `T_ℓ A → A[ℓⁿ]` is onto. -/
def GrothendieckMonodromy : Prop :=
  ∀ (K : Type u) [Field K] (O : ValuationSubring K) [IsDiscreteValuationRing O]
    (w : ValuationSubring (AlgebraicClosure K)),
    w.comap (algebraMap K (AlgebraicClosure K)) = O →
    ∀ (A : Grp (Over (Spec (.of K)))) [IsAbelianVariety A],
      ∃ K' : IntermediateField K (AlgebraicClosure K), FiniteDimensional K K' ∧
        ∀ σ : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K, IsInertia w σ →
          (∀ x ∈ K', σ x = x) →
          ∀ ℓ : ℕ, ℓ.Prime → IsUnit (ℓ : O) →
            ∀ n : ℕ, ∀ x ∈ torsion A (AlgebraicClosure K) (ℓ ^ n), UnipSq A σ x

/-- **Leaf I2-Ray (Raynaud's criterion, Galois form).** Consequence of SGA 7 I, Exp. IX,
Prop. 4.7 (Raynaud: if `m ≥ 3` is invertible in `O` and the points of `A[m]` are rational over
`K`, then `A` has semistable reduction; also Silverberg–Zarhin, Ann. Inst. Fourier 45 (1995),
Thm 3.5 per h-trust, ASTRA-READ there) and the direction "semistable ⇒ unipotent of echelon ≤ 2"
of SGA 7 IX Prop. 3.5 (numbers UNVERIFIED): every `σ` in the inertia group of `w` satisfies
`(σ - 1)² = 0` on `A(K̄)[ℓⁿ]` for every prime `ℓ` invertible in `O` and every `n`. -/
def RaynaudCriterion : Prop :=
  ∀ (K : Type u) [Field K] (O : ValuationSubring K) [IsDiscreteValuationRing O]
    (w : ValuationSubring (AlgebraicClosure K)),
    w.comap (algebraMap K (AlgebraicClosure K)) = O →
    ∀ (A : Grp (Over (Spec (.of K)))) [IsAbelianVariety A] (m : ℕ), 3 ≤ m → IsUnit (m : O) →
      (∀ σ : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K,
          ∀ x ∈ torsion A (AlgebraicClosure K) m, galAct A σ x = x) →
      ∀ σ : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K, IsInertia w σ →
        ∀ ℓ : ℕ, ℓ.Prime → IsUnit (ℓ : O) →
          ∀ n : ℕ, ∀ x ∈ torsion A (AlgebraicClosure K) (ℓ ^ n), UnipSq A σ x

/-! ## 5. Néron mapping property for abelian schemes, and reduction of torsion -/

/-- **Leaf I2-NMP (Néron mapping property, abelian-scheme case).** Consequence of
Bosch–Lütkebohmert–Raynaud, *Néron models* (1990), §1.2, Def. 1 and Prop. 8 (an abelian scheme
over a DVR is the Néron model of its generic fibre; numbers UNVERIFIED): for abelian schemes
`𝒜, ℬ` over the DVR `O ⊆ K`, restriction to the generic fibre is a bijection
`Hom_O(𝒜, ℬ) → Hom_K(𝒜_K, ℬ_K)` (morphisms of schemes over the base). -/
def NeronMappingAbelianScheme : Prop :=
  ∀ (K : Type u) [Field K] (O : ValuationSubring K) [IsDiscreteValuationRing O]
    (𝒜 ℬ : Grp (Over (Spec (.of O)))) [IsAbelianScheme 𝒜] [IsAbelianScheme ℬ],
    Function.Bijective (fun f : 𝒜.X ⟶ ℬ.X =>
      (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap O K)))).map f)

section Reduction

variable {K : Type u} [Field K]

/-- The ring map `O → w` for a valuation ring `w` of `L` lying over `O`. -/
def toW {L : Type u} [Field L] [Algebra K L] (O : ValuationSubring K) (w : ValuationSubring L)
    (hw : w.comap (algebraMap K L) = O) : O →+* w :=
  ((algebraMap K L).comp O.subtype).codRestrict w.toSubring (fun x => by
    have : (x : K) ∈ w.comap (algebraMap K L) := by rw [hw]; exact x.2
    exact this)

/-- `y ∈ 𝒜(κ(w))` is the reduction of `x ∈ A(L)`: some `x̃ ∈ 𝒜(w)` restricts to `x` on the
generic point (through `e : 𝒜_K ≅ A`) and to `y` on the closed point. -/
def IsReductionOf {L : Type u} [Field L] [Algebra K L] {O : ValuationSubring K}
    {A : Grp (Over (Spec (.of K)))} (𝒜 : Grp (Over (Spec (.of O))))
    (e : (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap O K)))).mapGrp.obj 𝒜 ≅ A)
    (w : ValuationSubring L) (hw : w.comap (algebraMap K L) = O) (x : Pts A L)
    (y : Over.mk (Spec.map (CommRingCat.ofHom
      ((IsLocalRing.residue w).comp (toW O w hw)))) ⟶ 𝒜.X) : Prop :=
  ∃ x' : Over.mk (Spec.map (CommRingCat.ofHom (toW O w hw))) ⟶ 𝒜.X,
    (x ≫ (e.inv.hom.hom : A.X ⟶
        (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap O K)))).obj 𝒜.X)).left ≫
        pullback.fst 𝒜.X.hom (Spec.map (CommRingCat.ofHom (algebraMap O K))) =
        Spec.map (CommRingCat.ofHom w.subtype) ≫ x'.left ∧
    y.left = Spec.map (CommRingCat.ofHom (IsLocalRing.residue w)) ≫ x'.left

end Reduction

/-- **Leaf I2-Red (reduction of prime-to-`p` torsion at good reduction).** Serre–Tate 1968, §1
(proof of Thm 1, (a) ⇒ (b); locator UNVERIFIED): if `A` has good reduction with abelian scheme
`𝒜` and `m ≥ 1` is invertible in `O`, reduction is a bijection
`A(K̄)[m] → 𝒜(κ(w))[m]`. -/
def ReductionTorsionBijective : Prop :=
  ∀ (K : Type u) [Field K] (O : ValuationSubring K) [IsDiscreteValuationRing O]
    (w : ValuationSubring (AlgebraicClosure K))
    (hw : w.comap (algebraMap K (AlgebraicClosure K)) = O)
    (A : Grp (Over (Spec (.of K)))) [IsAbelianVariety A]
    (𝒜 : Grp (Over (Spec (.of O)))) [IsAbelianScheme 𝒜]
    (e : (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap O K)))).mapGrp.obj 𝒜 ≅ A)
    (m : ℕ), 0 < m → IsUnit (m : O) →
      (∀ x ∈ torsion A (AlgebraicClosure K) m,
        ∃! y, y ^ m = 1 ∧ IsReductionOf 𝒜 e w hw x y) ∧
      (∀ y, y ^ m = 1 → ∃! x, x ∈ torsion A (AlgebraicClosure K) m ∧ IsReductionOf 𝒜 e w hw x y)

/-! ## 6. Structure of torsion (Mumford, *Abelian varieties*, §4) -/

/-- **Leaf I2-Tors (structure of `A[n]`; boundary with I3).** Mumford, *Abelian varieties*
(1970), §4, Application 2 / §6 (locator UNVERIFIED): for an abelian variety of dimension `g` over
`K` and `n ≥ 1` invertible in `K`, `A(K̄)[n] ≅ (ℤ/n)^{2g}` as groups. The dimension is the
topological Krull dimension of the underlying space. -/
def TorsionStructure : Prop :=
  ∀ (K : Type u) [Field K] (A : Grp (Over (Spec (.of K)))) [IsAbelianVariety A] (g n : ℕ),
    topologicalKrullDim A.X.left = (g : WithBot ℕ∞) → 0 < n → (n : K) ≠ 0 →
      ∃ e : torsion A (AlgebraicClosure K) n ≃ (Fin (2 * g) → ZMod n),
        ∀ x y : torsion A (AlgebraicClosure K) n,
          ∀ h : x.1 * y.1 ∈ torsion A (AlgebraicClosure K) n, e ⟨x.1 * y.1, h⟩ = e x + e y

/-! ## 7. Abhyankar's lemma for discrete valuation rings -/

/-- **Leaf I2-AbDVR (Abhyankar's lemma, DVR form).** SGA 1, Exp. X, Lemme 3.6 (number
UNVERIFIED); also Stichtenoth, *Algebraic function fields and codes*, Thm 3.9.1, and Cornell,
Gold (classical). `R` a DVR with fraction field `K`, uniformizer `π`; `L/K` finite separable, tamely
ramified over `R` (every prime `Q` of the integral closure `S` of `R` in `L` over the maximal
ideal has `e(Q)` invertible in `R` and separable residue extension); `n` invertible in `R` with
every
`e(Q) ∣ n`. Let `M = L(t)` with `tⁿ = π`. Then every prime of the integral closure of `R` in `M`
over the maximal ideal has ramification index exactly `n` and separable residue extension
(equivalently: `M/K(t)` is unramified above `R`, as `K(t)/K` is totally ramified of degree `n`). -/
def AbhyankarDVR : Prop :=
  ∀ (R K L M : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [Field K] [Algebra R K] [IsFractionRing R K]
    [Field L] [Algebra K L] [Algebra R L] [IsScalarTower R K L]
    [FiniteDimensional K L] [Algebra.IsSeparable K L]
    [Field M] [Algebra L M] [Algebra K M] [Algebra R M]
    [IsScalarTower K L M] [IsScalarTower R K M]
    (π : R), Irreducible π → ∀ (n : ℕ), 0 < n → IsUnit (n : R) →
    (∀ (Q : Ideal (integralClosure R L)) [Q.IsPrime] [Q.LiesOver (IsLocalRing.maximalIdeal R)],
      IsUnit ((Q.ramificationIdx R : ℕ) : R) ∧ Q.ramificationIdx R ∣ n ∧
      Algebra.IsSeparable (R ⧸ IsLocalRing.maximalIdeal R) (integralClosure R L ⧸ Q)) →
    ∀ t : M, t ^ n = algebraMap R M π → IntermediateField.adjoin L {t} = ⊤ →
      ∀ (Q : Ideal (integralClosure R M)) [Q.IsPrime]
        [Q.LiesOver (IsLocalRing.maximalIdeal R)],
        Q.ramificationIdx R = n ∧
        Algebra.IsSeparable (R ⧸ IsLocalRing.maximalIdeal R) (integralClosure R M ⧸ Q)


/-! ## 8. Characteristic polynomial independent of `ℓ` (Mumford §19, Thm 4; boundary with I3) -/

/-- **Leaf I2-Char (Mumford, *Abelian varieties*, §19, Thm 4; locator UNVERIFIED).** For an
endomorphism `φ` of an abelian variety `B` of dimension `g` over a field `k` there is a monic
`P ∈ ℤ[X]` of degree `2g` which, for every prime `ℓ ≠ char k`, is the characteristic polynomial of
`φ` on `T_ℓ B`; finite-level form: reduced mod `ℓⁿ` it is the characteristic polynomial of the
matrix of `φ` on `B(k̄)[ℓⁿ]` in any `ℤ/ℓⁿ`-basis. Used in C10 (the trace of `Frob ∘ μ̄_σ` is one
integer for all `ℓ`). -/
def CharpolyIndependentOfEll : Prop :=
  ∀ (k : Type u) [Field k] (B : Grp (Over (Spec (.of k)))) [IsAbelianVariety B] (g : ℕ),
    topologicalKrullDim B.X.left = (g : WithBot ℕ∞) → ∀ φ : B ⟶ B,
    ∃ P : Polynomial ℤ, P.Monic ∧ P.natDegree = 2 * g ∧
      ∀ ℓ : ℕ, ℓ.Prime → (ℓ : k) ≠ 0 → ∀ n : ℕ, 0 < n →
        ∀ e : torsion B (AlgebraicClosure k) (ℓ ^ n) ≃ (Fin (2 * g) → ZMod (ℓ ^ n)),
        (∀ x y : torsion B (AlgebraicClosure k) (ℓ ^ n),
          ∀ h : x.1 * y.1 ∈ torsion B (AlgebraicClosure k) (ℓ ^ n),
            e ⟨x.1 * y.1, h⟩ = e x + e y) →
        ∀ M : Matrix (Fin (2 * g)) (Fin (2 * g)) (ZMod (ℓ ^ n)),
        (∀ x y : torsion B (AlgebraicClosure k) (ℓ ^ n), y.1 = x.1 ≫ φ.hom.hom →
          e y = M.mulVec (e x)) →
        M.charpoly = P.map (Int.castRingHom (ZMod (ℓ ^ n)))

/-- **Leaf I2-Rank (Mumford, *Abelian varieties*, §19, Thm 3, rank part; boundary with I3;
locator UNVERIFIED).** For abelian varieties `A, B` over `k` of dimensions `g, g'`, the group of
homomorphisms `A → B` has rank at most `4gg'`: any `4gg' + 1` homomorphisms are `ℤ`-linearly
dependent in the (commutative) group `A.X ⟶ B.X`. Used in A8 (`r ≤ 16F₀²`). The instance argument
`IsCommMonObj B.X` holds for every abelian variety (Mathlib,
`isCommMonObj_of_isProper_of_geometricallyIntegral`). -/
def HomRankBound : Prop :=
  ∀ (k : Type u) [Field k] (A B : Grp (Over (Spec (.of k)))) [IsAbelianVariety A]
    [IsAbelianVariety B] [IsCommMonObj B.X] (g g' : ℕ),
    topologicalKrullDim A.X.left = (g : WithBot ℕ∞) →
    topologicalKrullDim B.X.left = (g' : WithBot ℕ∞) →
    ∀ f : Fin (4 * g * g' + 1) → (A ⟶ B),
      ∃ c : Fin (4 * g * g' + 1) → ℤ, c ≠ 0 ∧ ∏ i, (f i).hom.hom ^ c i = 1

/-! ## 9. Glue proved from the leaves -/

section Glue

variable {K : Type u} [Field K]

lemma galAct_mul (A : Grp (Over (Spec (.of K)))) {L : Type u} [CommRing L] [Algebra K L]
    (σ : L ≃ₐ[K] L) (x y : Pts A L) : galAct A σ (x * y) = galAct A σ x * galAct A σ y :=
  MonObj.comp_mul _ _ _

lemma galAct_inv (A : Grp (Over (Spec (.of K)))) {L : Type u} [CommRing L] [Algebra K L]
    (σ : L ≃ₐ[K] L) (x : Pts A L) : galAct A σ x⁻¹ = (galAct A σ x)⁻¹ :=
  GrpObj.comp_inv _ _

lemma galAct_pow (A : Grp (Over (Spec (.of K)))) {L : Type u} [CommRing L] [Algebra K L]
    (σ : L ≃ₐ[K] L) (x : Pts A L) (n : ℕ) : galAct A σ (x ^ n) = (galAct A σ x) ^ n :=
  MonObj.comp_pow _ _ _

lemma galAct_one (A : Grp (Over (Spec (.of K)))) {L : Type u} [CommRing L] [Algebra K L]
    (σ : L ≃ₐ[K] L) : galAct A σ 1 = 1 :=
  MonObj.comp_one _

/-- **Glue C6/A8 (proved).** Good reduction at `O` makes inertia act trivially on `A[ℓⁿ]` for
every prime `ℓ` invertible in `O` (NOS, (a) ⇒ (b)): `r_ℓ` is unramified at such places. -/
theorem inertiaTrivial_of_goodReduction (hNOS : NeronOggShafarevich.{u})
    (O : ValuationSubring K) [IsDiscreteValuationRing O]
    (w : ValuationSubring (AlgebraicClosure K))
    (hw : w.comap (algebraMap K (AlgebraicClosure K)) = O)
    (A : Grp (Over (Spec (.of K)))) [IsAbelianVariety A] (hA : HasGoodReduction A O)
    (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓO : IsUnit (ℓ : O)) (n : ℕ) :
    InertiaTrivialOn A w (ℓ ^ n) :=
  ((hNOS K O w hw A).1.mp hA) (ℓ ^ n) (pow_pos hℓ.pos n) (by
    rw [Nat.cast_pow]; exact hℓO.pow n)

/-- Algebraic core of D2 (proved): in a commutative group of points, if `σ` satisfies
`(σ - 1)² x = 0`, `x` has order dividing `ℓⁿ`, and `σ^{pᵃ} x = x` with `p` prime to `ℓ`,
then `σ x = x`. -/
theorem fixed_of_unipSq_of_iterate (A : Grp (Over (Spec (.of K)))) [IsCommMonObj A.X]
    {L : Type u} [CommRing L] [Algebra K L] (σ : L ≃ₐ[K] L) (x : Pts A L) (ℓ n p a : ℕ)
    (hcop : Nat.Coprime (p ^ a) (ℓ ^ n)) (hx : x ∈ torsion A L (ℓ ^ n))
    (hu : UnipSq A σ x) (hit : (galAct A σ)^[p ^ a] x = x) : galAct A σ x = x := by
  set N := galAct A σ x * x⁻¹ with hN
  have hσN : galAct A σ N = N := by
    rw [hN, galAct_mul, galAct_inv]
    unfold UnipSq at hu
    have h2 : galAct A σ (galAct A σ x) * (galAct A σ x)⁻¹ =
        ((galAct A σ x)⁻¹ * x)⁻¹ := by
      rw [eq_inv_iff_mul_eq_one, ← hu]; group
    rw [h2, mul_inv_rev, inv_inv, mul_comm]
  have hiter : ∀ k : ℕ, (galAct A σ)^[k] x = N ^ k * x := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [Function.iterate_succ_apply', ih, galAct_mul, galAct_pow, hσN, pow_succ, hN]
      group
  have h1 : N ^ (p ^ a) = 1 := by
    have := hiter (p ^ a)
    rw [hit] at this
    exact (mul_eq_right.mp this.symm)
  have h2 : N ^ (ℓ ^ n) = 1 := by
    have hx' : x ^ (ℓ ^ n) = 1 := hx
    rw [hN, mul_pow, ← galAct_pow, hx', galAct_one, inv_pow, hx']; simp
  have hN1 : N = 1 := by
    have := pow_gcd_eq_one.mpr ⟨h1, h2⟩
    rwa [Nat.Coprime.gcd_eq_one hcop, pow_one] at this
  rw [hN] at hN1
  exact mul_inv_eq_one.mp hN1

/-- **Glue D2 (proved from Raynaud).** At a place of residue characteristic `p` where `A[m]` is
rational (`m ≥ 3` prime to `p`), every inertia element `σ` that acts on a point `x ∈ A[ℓⁿ]`
(`ℓ ≠ p`) with `p`-power order fixes it. Applied to wild inertia (pro-`p`, and the action on the
finite set `A[ℓⁿ]` factors through a finite quotient), this is D2's "wild inertia acts
trivially on `V_ℓ(A)`". The two facts in parentheses are I6/glue. -/
theorem D2_fixed_of_raynaud (hRay : RaynaudCriterion.{u})
    (O : ValuationSubring K) [IsDiscreteValuationRing O]
    (w : ValuationSubring (AlgebraicClosure K))
    (hw : w.comap (algebraMap K (AlgebraicClosure K)) = O)
    (A : Grp (Over (Spec (.of K)))) [IsAbelianVariety A] (m : ℕ) (hm : 3 ≤ m)
    (hmO : IsUnit (m : O))
    (hrat : ∀ σ : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K,
      ∀ x ∈ torsion A (AlgebraicClosure K) m, galAct A σ x = x)
    (σ : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K) (hσ : IsInertia w σ)
    (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓO : IsUnit (ℓ : O)) (n p a : ℕ)
    (hcop : Nat.Coprime (p ^ a) (ℓ ^ n))
    (x : Pts A (AlgebraicClosure K)) (hx : x ∈ torsion A (AlgebraicClosure K) (ℓ ^ n))
    (hit : (galAct A σ)^[p ^ a] x = x) : galAct A σ x = x := by
  have : IsProper A.X.hom := IsAbelianVariety.proper
  have : GeometricallyIntegral A.X.hom := IsAbelianVariety.geomIntegral
  have : IsCommMonObj A.X := isCommMonObj_of_isProper_of_geometricallyIntegral A.X
  exact fixed_of_unipSq_of_iterate A σ x ℓ n p a hcop hx
    (hRay K O w hw A m hm hmO hrat σ hσ ℓ hℓ hℓO n x hx) hit

end Glue

end PkgI2

/-! # §C. The shared object layer -/

namespace ObjBridge

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open PkgI2 (IsAbelianVariety)
open scoped Quaternion TensorProduct

variable {K : Type} [Field K]

/-- The shared object: I2's group object with `[IsAbelianVariety A]`, viewed as an I3 `AbVar`
(same scheme, same group structure). -/
def ofGrp (A : Grp (Over (Spec (.of K)))) [h : IsAbelianVariety A] : PkgI3.AbVar K :=
  haveI := h.proper; haveI := h.smooth; haveI := h.geomIntegral
  { X := A.X }

/-- The inverse direction on objects. -/
@[reducible] def toGrp (A : PkgI3.AbVar K) : Grp (Over (Spec (.of K))) := Grp.mk A.X

instance (A : PkgI3.AbVar K) : IsAbelianVariety (toGrp A) := ⟨A.proper, A.smooth, A.geomInt⟩

/-- Round trip `AbVar → Grp → AbVar` is the identity (definitionally). -/
theorem ofGrp_toGrp (A : PkgI3.AbVar K) : ofGrp (toGrp A) = A := rfl

/-- Round trip `Grp → AbVar → Grp` is the identity (definitionally). -/
theorem toGrp_ofGrp (A : Grp (Over (Spec (.of K)))) [IsAbelianVariety A] :
    toGrp (ofGrp A) = A := rfl

/-- Commutativity of the shared object (Mathlib, Stacks 0BFD), stated for `A.X` so that instance
search finds it without passing through `ofGrp`. -/
instance isCommMonObj (A : Grp (Over (Spec (.of K)))) [IsAbelianVariety A] : IsCommMonObj A.X :=
  haveI := PkgI2.IsAbelianVariety.proper (A := A)
  haveI := PkgI2.IsAbelianVariety.geomIntegral (A := A)
  isCommMonObj_of_isProper_of_geometricallyIntegral A.X

section Derived

variable (A B : Grp (Over (Spec (.of K)))) [IsAbelianVariety A] [IsAbelianVariety B]

/-- `Hom_K(A, B)`, I3's ℤ-module through the bridge. -/
abbrev Hom : Type := PkgI3.AbVar.Hom (ofGrp A) (ofGrp B)
/-- `End_K(A)`, I3's ring. -/
abbrev End : Type := PkgI3.AbVar.End (ofGrp A)
/-- `End⁰_K(A) = ℚ ⊗ End_K(A)`. -/
abbrev End0 : Type := PkgI3.AbVar.End0 (ofGrp A)
/-- The dimension (topological Krull dimension of the underlying space). -/
abbrev dim : WithBot ℕ∞ := (ofGrp A).dim

variable (ℓ : ℕ) [Fact ℓ.Prime]

/-- `T_ℓ(A)`. -/
abbrev T : Type := (ofGrp A).T ℓ
/-- `V_ℓ(A)`. -/
abbrev V : Type := (ofGrp A).V ℓ
/-- `ρ_ℓ : G_K → GL(V_ℓ A)`. -/
abbrev galRep : Representation ℚ_[ℓ] (Field.absoluteGaloisGroup K) (V A ℓ) := (ofGrp A).galRep ℓ
/-- `Hom(A, B) ⊗ ℤ_ℓ → Hom_{ℤ_ℓ}(T_ℓ A, T_ℓ B)`. -/
abbrev tateHomZl : TensorProduct ℤ ℤ_[ℓ] (Hom A B) →ₗ[ℤ] (T A ℓ →ₗ[ℤ_[ℓ]] T B ℓ) :=
  PkgI3.AbVar.tateHomZl ℓ (ofGrp A) (ofGrp B)

end Derived

/-! ## The bridge on morphisms is a bijection -/

section Bridge

variable {A B C : Grp (Over (Spec (.of K)))} [IsAbelianVariety A] [IsAbelianVariety B]
  [IsAbelianVariety C]

/-- A morphism of group objects as an element of `Hom A B` (rv-leaves-b's `homOfGrp`). -/
def homOfGrp (f : A ⟶ B) : Hom A B :=
  Additive.ofMul ⟨f.hom.hom, (inferInstance : IsMonHom f.hom.hom)⟩

@[simp] theorem homOfGrp_hom (f : A ⟶ B) : (homOfGrp f).hom = f.hom.hom := rfl

/-- The inverse: an element of `Hom A B` as a morphism of group objects. -/
def grpOfHom (f : Hom A B) : A ⟶ B :=
  @Grp.homMk _ _ _ A B (Additive.toMul f).1 (Additive.toMul f).2

@[simp] theorem grpOfHom_hom_hom (f : Hom A B) : (grpOfHom f).hom.hom = f.hom := rfl

theorem homOfGrp_grpOfHom (f : Hom A B) : homOfGrp (grpOfHom f) = f :=
  PkgI3.AbVar.Hom.ext' rfl

theorem grpOfHom_homOfGrp (f : A ⟶ B) : grpOfHom (homOfGrp f) = f :=
  Grp.hom_ext _ _ rfl

/-- **The bridge is a bijection on Hom sets.** -/
def homEquiv : (A ⟶ B) ≃ Hom A B where
  toFun := homOfGrp
  invFun := grpOfHom
  left_inv := grpOfHom_homOfGrp
  right_inv := homOfGrp_grpOfHom

theorem homOfGrp_bijective : Function.Bijective (homOfGrp : (A ⟶ B) → Hom A B) :=
  homEquiv.bijective

theorem homOfGrp_injective : Function.Injective (homOfGrp : (A ⟶ B) → Hom A B) :=
  homEquiv.injective

/-- Composition goes to composition of underlying morphisms. -/
theorem homOfGrp_comp_hom (f : A ⟶ B) (g : B ⟶ C) :
    (homOfGrp (f ≫ g)).hom = (homOfGrp f).hom ≫ (homOfGrp g).hom := rfl

theorem homOfGrp_id : homOfGrp (𝟙 A) = (1 : End A) := PkgI3.AbVar.Hom.ext' rfl

/-- On endomorphisms the bridge turns composition into I3's product `f * g = f ∘ g`. -/
theorem homOfGrp_comp_end (f g : A ⟶ A) :
    (homOfGrp (f ≫ g) : End A) = (homOfGrp g : End A) * (homOfGrp f : End A) :=
  PkgI3.AbVar.Hom.ext' rfl

/-- The bridge is a monoid isomorphism `End_{Grp}(A) ≃* End_K(A)` (Mathlib's `End` is a structure
with `f * g = .of (g.asHom ≫ f.asHom)`, i.e. `f ∘ g`). -/
def endMulEquiv : CategoryTheory.End A ≃* End A where
  toEquiv := CategoryTheory.End.homEquiv.trans (homEquiv (A := A) (B := A))
  map_mul' f g := homOfGrp_comp_end (A := A) g.asHom f.asHom

/-- The zero of `Hom A B` is the trivial morphism. -/
theorem homOfGrp_eq_zero_iff (f : A ⟶ B) : homOfGrp f = 0 ↔ f.hom.hom = 1 :=
  ⟨fun h => by rw [← homOfGrp_hom, h]; rfl,
   fun h => PkgI3.AbVar.Hom.ext' (by rw [homOfGrp_hom, h]; rfl)⟩

theorem hom_eq_zero_iff (f : Hom A B) : f = 0 ↔ f.hom = 1 :=
  ⟨fun h => by rw [h]; rfl, fun h => PkgI3.AbVar.Hom.ext' (by rw [h]; rfl)⟩

/-- The additive structure of `Hom A B` is the pointwise product of morphisms. -/
theorem hom_sum_zsmul {n : ℕ} (f : Fin n → Hom A B) (c : Fin n → ℤ) :
    (∑ i, c i • f i).hom = ∏ i, (f i).hom ^ c i := by
  let φ : Hom A B →+ Additive (A.X ⟶ B.X) :=
    MonoidHom.toAdditive (PkgI3.AbVar.homGroup (ofGrp A) (ofGrp B)).subtype
  have : ∀ x : Hom A B, x.hom = Additive.toMul (φ x) := fun _ => rfl
  rw [this, map_sum, toMul_sum]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [map_zsmul, toMul_zsmul]; rfl

/-- Quantifying over the bridge's image is quantifying over `Hom A B`. -/
theorem forall_hom_iff (P : Hom A B → Prop) : (∀ f : A ⟶ B, P (homOfGrp f)) ↔ ∀ f, P f :=
  ⟨fun h f => homOfGrp_grpOfHom f ▸ h (grpOfHom f), fun h f => h _⟩

end Bridge

/-! ## Objects: quantifying over `AbVar K` is quantifying over the shared objects -/

theorem forall_abVar_iff (P : PkgI3.AbVar K → Prop) :
    (∀ A : PkgI3.AbVar K, P A) ↔
      ∀ (A : Grp (Over (Spec (.of K)))) [IsAbelianVariety A], P (ofGrp A) :=
  ⟨fun h _ _ => h _, fun h A => h (toGrp A)⟩

theorem exists_abVar_iff (P : PkgI3.AbVar K → Prop) :
    (∃ A : PkgI3.AbVar K, P A) ↔
      ∃ (A : Grp (Over (Spec (.of K)))) (_ : IsAbelianVariety A), P (ofGrp A) :=
  ⟨fun ⟨A, h⟩ => ⟨toGrp A, inferInstance, h⟩, fun ⟨_, _, h⟩ => ⟨_, h⟩⟩

/-! ## Points: one definition (I2's `Pts`, over any `K`-algebra), which is I3's `Pt` for fields -/

section Points

variable (A : Grp (Over (Spec (.of K)))) [IsAbelianVariety A] (L : Type) [Field L] [Algebra K L]

theorem pts_eq : PkgI2.Pts A L = (ofGrp A).Pt L := rfl

theorem galAct_eq (σ : L ≃ₐ[K] L) (x : PkgI2.Pts A L) :
    PkgI2.galAct A σ x = (ofGrp A).galAct σ x := rfl

theorem galHom_eq (σ : L ≃ₐ[K] L) : PkgI2.galHom L σ = PkgI3.AbVar.galHom σ := rfl

theorem mem_torsion_iff (m : ℕ) (x : PkgI2.Pts A L) : x ∈ PkgI2.torsion A L m ↔ x ^ m = 1 :=
  Iff.rfl

end Points

end ObjBridge

/-! # §D. The I2 and I3 leaves restated over the shared layer, with equivalences -/

namespace ObjBridge

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open PkgI2 (IsAbelianVariety IsAbelianScheme Pts torsion galAct IsInertia HasGoodReduction
  InertiaTrivialOn UnipSq baseChange IsReductionOf)
open Polynomial
open scoped Quaternion TensorProduct

/-! ## I2 leaves

Universe fixed to `Type`. Points, torsion, Galois action, inertia, good reduction and base change
are the shared ones (I2's single definitions; for a field `L`, `Pts A L` is I3's `Pt` by `rfl`,
`pts_eq`). The leaves that do not involve `Hom`/`End` are I2's text at `Type` with
`topologicalKrullDim A.X.left` written `dim A`; each is `Iff.rfl` to the original. I2-Char and
I2-Rank are restated with the shared `End`/`Hom` (I3's ring and ℤ-module through the bridge). -/

/-- **Leaf I2-P (Zariski–Nagata purity of the branch locus).**
Ring form of Stacks Tag 0BMB (SGA 1, Exp. X, Thm 3.4, numbering UNVERIFIED):
let `R → S` be of finite type with `R` Noetherian, `q` a prime of `S` over `p`, with `R_p` regular,
`S_q` a normal domain, `S` quasi-finite at `q`, `dim S_q = dim R_p ≥ 1`, and `R → S` unramified at
every prime `q' ⊆ q` of height one. Then `R → S` is étale at `q`. -/
def PurityBranchLocus : Prop :=
  ∀ (R S : Type) [CommRing R] [CommRing S] [Algebra R S] [IsNoetherianRing R]
    [Algebra.FiniteType R S] (q : Ideal S) [q.IsPrime],
    IsRegularLocalRing (Localization.AtPrime (q.comap (algebraMap R S))) →
    IsDomain (Localization.AtPrime q) →
    IsIntegrallyClosed (Localization.AtPrime q) →
    Algebra.QuasiFiniteAt R q →
    ringKrullDim (Localization.AtPrime q) =
      ringKrullDim (Localization.AtPrime (q.comap (algebraMap R S))) →
    1 ≤ ringKrullDim (Localization.AtPrime q) →
    (∀ (q' : Ideal S) [q'.IsPrime], q' ≤ q → q'.height = 1 → Algebra.IsUnramifiedAt R q') →
    Algebra.IsEtaleAt R q

theorem purityBranchLocus_iff : ObjBridge.PurityBranchLocus ↔ PkgI2.PurityBranchLocus.{0} := Iff.rfl

/-- **Leaf I2-NOS (Serre–Tate 1968, Thm 1; criterion of Néron–Ogg–Shafarevich).**
`K` a field with a discrete valuation ring `O`, `w` a valuation ring of `K̄` over `O`, `A/K` an
abelian variety. Then (a) ⟺ (b) ⟺ (c), where (a) good reduction at `O`, (b) for every `m ≥ 1`
invertible in `O`, inertia at `w` fixes `A(K̄)[m]`, (c) the same for infinitely many such `m`. -/
def NeronOggShafarevich : Prop :=
  ∀ (K : Type) [Field K] (O : ValuationSubring K) [IsDiscreteValuationRing O]
    (w : ValuationSubring (AlgebraicClosure K)),
    w.comap (algebraMap K (AlgebraicClosure K)) = O →
    ∀ (A : Grp (Over (Spec (.of K)))) [IsAbelianVariety A],
      (HasGoodReduction A O ↔
        ∀ m : ℕ, 0 < m → IsUnit (m : O) → InertiaTrivialOn A w m) ∧
      (HasGoodReduction A O ↔
        {m : ℕ | 0 < m ∧ IsUnit (m : O) ∧ InertiaTrivialOn A w m}.Infinite)

theorem neronOggShafarevich_iff : ObjBridge.NeronOggShafarevich ↔ PkgI2.NeronOggShafarevich.{0} :=
    Iff.rfl

/-- **Leaf I2-ST2 (Serre–Tate 1968, Thm 2; potential good reduction).** For a prime `ℓ`
invertible in `O`: `A` acquires good reduction over a finite extension `K' ⊆ K̄` (at `w ∩ K'`) iff
an open subgroup `I ∩ G_{K'}` of inertia acts trivially on every `A(K̄)[ℓⁿ]`, i.e. the image of
inertia in `Aut(T_ℓ A)` is finite. Used only on the h-b1 route for A6 (not on the route of §5 of
docs/research/pkg-I2.md). -/
def SerreTatePotentialGood : Prop :=
  ∀ (K : Type) [Field K] (O : ValuationSubring K) [IsDiscreteValuationRing O]
    (w : ValuationSubring (AlgebraicClosure K)),
    w.comap (algebraMap K (AlgebraicClosure K)) = O →
    ∀ (A : Grp (Over (Spec (.of K)))) [IsAbelianVariety A] (ℓ : ℕ), ℓ.Prime → IsUnit (ℓ : O) →
      ((∃ K' : IntermediateField K (AlgebraicClosure K), FiniteDimensional K K' ∧
          HasGoodReduction (baseChange A K') (w.comap (algebraMap K' (AlgebraicClosure K)))) ↔
       (∃ K' : IntermediateField K (AlgebraicClosure K), FiniteDimensional K K' ∧
          ∀ σ : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K, IsInertia w σ →
            (∀ x ∈ K', σ x = x) →
            ∀ n : ℕ, ∀ x ∈ torsion A (AlgebraicClosure K) (ℓ ^ n), galAct A σ x = x))

theorem serreTatePotentialGood_iff : ObjBridge.SerreTatePotentialGood ↔
    PkgI2.SerreTatePotentialGood.{0} := Iff.rfl

/-- **Leaf I2-SS (Grothendieck's semistable reduction theorem, monodromy form).** Consequence of
SGA 7 I, Exp. IX, Thm 3.6 (`A` acquires semistable reduction over a finite extension `K'`) and
the direction "semistable ⇒ inertia acts unipotently of echelon ≤ 2" of Prop. 3.5 (numbers
UNVERIFIED): there is a finite `K' ⊆ K̄` such that every `σ` in the inertia group of `w` fixing
`K'` satisfies `(σ - 1)² = 0` on `A(K̄)[ℓⁿ]` for every prime `ℓ` invertible in `O` and every `n`.
The finite-level form is equivalent to `(σ-1)² = 0` on `T_ℓ A`, since `T_ℓ A → A[ℓⁿ]` is onto. -/
def GrothendieckMonodromy : Prop :=
  ∀ (K : Type) [Field K] (O : ValuationSubring K) [IsDiscreteValuationRing O]
    (w : ValuationSubring (AlgebraicClosure K)),
    w.comap (algebraMap K (AlgebraicClosure K)) = O →
    ∀ (A : Grp (Over (Spec (.of K)))) [IsAbelianVariety A],
      ∃ K' : IntermediateField K (AlgebraicClosure K), FiniteDimensional K K' ∧
        ∀ σ : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K, IsInertia w σ →
          (∀ x ∈ K', σ x = x) →
          ∀ ℓ : ℕ, ℓ.Prime → IsUnit (ℓ : O) →
            ∀ n : ℕ, ∀ x ∈ torsion A (AlgebraicClosure K) (ℓ ^ n), UnipSq A σ x

theorem grothendieckMonodromy_iff : ObjBridge.GrothendieckMonodromy ↔
    PkgI2.GrothendieckMonodromy.{0} := Iff.rfl

/-- **Leaf I2-Ray (Raynaud's criterion, Galois form).** Consequence of SGA 7 I, Exp. IX,
Prop. 4.7 (Raynaud: if `m ≥ 3` is invertible in `O` and the points of `A[m]` are rational over
`K`, then `A` has semistable reduction; also Silverberg–Zarhin, Ann. Inst. Fourier 45 (1995),
Thm 3.5 per h-trust, ASTRA-READ there) and the direction "semistable ⇒ unipotent of echelon ≤ 2"
of SGA 7 IX Prop. 3.5 (numbers UNVERIFIED): every `σ` in the inertia group of `w` satisfies
`(σ - 1)² = 0` on `A(K̄)[ℓⁿ]` for every prime `ℓ` invertible in `O` and every `n`. -/
def RaynaudCriterion : Prop :=
  ∀ (K : Type) [Field K] (O : ValuationSubring K) [IsDiscreteValuationRing O]
    (w : ValuationSubring (AlgebraicClosure K)),
    w.comap (algebraMap K (AlgebraicClosure K)) = O →
    ∀ (A : Grp (Over (Spec (.of K)))) [IsAbelianVariety A] (m : ℕ), 3 ≤ m → IsUnit (m : O) →
      (∀ σ : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K,
          ∀ x ∈ torsion A (AlgebraicClosure K) m, galAct A σ x = x) →
      ∀ σ : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K, IsInertia w σ →
        ∀ ℓ : ℕ, ℓ.Prime → IsUnit (ℓ : O) →
          ∀ n : ℕ, ∀ x ∈ torsion A (AlgebraicClosure K) (ℓ ^ n), UnipSq A σ x

theorem raynaudCriterion_iff : ObjBridge.RaynaudCriterion ↔ PkgI2.RaynaudCriterion.{0} := Iff.rfl

/-- **Leaf I2-NMP (Néron mapping property, abelian-scheme case).** Consequence of
Bosch–Lütkebohmert–Raynaud, *Néron models* (1990), §1.2, Def. 1 and Prop. 8 (an abelian scheme
over a DVR is the Néron model of its generic fibre; numbers UNVERIFIED): for abelian schemes
`𝒜, ℬ` over the DVR `O ⊆ K`, restriction to the generic fibre is a bijection
`Hom_O(𝒜, ℬ) → Hom_K(𝒜_K, ℬ_K)` (morphisms of schemes over the base). -/
def NeronMappingAbelianScheme : Prop :=
  ∀ (K : Type) [Field K] (O : ValuationSubring K) [IsDiscreteValuationRing O]
    (𝒜 ℬ : Grp (Over (Spec (.of O)))) [IsAbelianScheme 𝒜] [IsAbelianScheme ℬ],
    Function.Bijective (fun f : 𝒜.X ⟶ ℬ.X =>
      (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap O K)))).map f)

theorem neronMappingAbelianScheme_iff : ObjBridge.NeronMappingAbelianScheme ↔
    PkgI2.NeronMappingAbelianScheme.{0} := Iff.rfl

/-- **Leaf I2-Red (reduction of prime-to-`p` torsion at good reduction).** Serre–Tate 1968, §1
(proof of Thm 1, (a) ⇒ (b); locator UNVERIFIED): if `A` has good reduction with abelian scheme
`𝒜` and `m ≥ 1` is invertible in `O`, reduction is a bijection
`A(K̄)[m] → 𝒜(κ(w))[m]`. -/
def ReductionTorsionBijective : Prop :=
  ∀ (K : Type) [Field K] (O : ValuationSubring K) [IsDiscreteValuationRing O]
    (w : ValuationSubring (AlgebraicClosure K))
    (hw : w.comap (algebraMap K (AlgebraicClosure K)) = O)
    (A : Grp (Over (Spec (.of K)))) [IsAbelianVariety A]
    (𝒜 : Grp (Over (Spec (.of O)))) [IsAbelianScheme 𝒜]
    (e : (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap O K)))).mapGrp.obj 𝒜 ≅ A)
    (m : ℕ), 0 < m → IsUnit (m : O) →
      (∀ x ∈ torsion A (AlgebraicClosure K) m,
        ∃! y, y ^ m = 1 ∧ IsReductionOf 𝒜 e w hw x y) ∧
      (∀ y, y ^ m = 1 → ∃! x, x ∈ torsion A (AlgebraicClosure K) m ∧ IsReductionOf 𝒜 e w hw x y)

theorem reductionTorsionBijective_iff : ObjBridge.ReductionTorsionBijective ↔
    PkgI2.ReductionTorsionBijective.{0} := Iff.rfl

/-- **Leaf I2-Tors (structure of `A[n]`; boundary with I3).** Mumford, *Abelian varieties*
(1970), §4, Application 2 / §6 (locator UNVERIFIED): for an abelian variety of dimension `g` over
`K` and `n ≥ 1` invertible in `K`, `A(K̄)[n] ≅ (ℤ/n)^{2g}` as groups. The dimension is the
topological Krull dimension of the underlying space. -/
def TorsionStructure : Prop :=
  ∀ (K : Type) [Field K] (A : Grp (Over (Spec (.of K)))) [IsAbelianVariety A] (g n : ℕ),
    dim A = (g : WithBot ℕ∞) → 0 < n → (n : K) ≠ 0 →
      ∃ e : torsion A (AlgebraicClosure K) n ≃ (Fin (2 * g) → ZMod n),
        ∀ x y : torsion A (AlgebraicClosure K) n,
          ∀ h : x.1 * y.1 ∈ torsion A (AlgebraicClosure K) n, e ⟨x.1 * y.1, h⟩ = e x + e y

theorem torsionStructure_iff : ObjBridge.TorsionStructure ↔ PkgI2.TorsionStructure.{0} := Iff.rfl

/-- **Leaf I2-AbDVR (Abhyankar's lemma, DVR form).** SGA 1, Exp. X, Lemme 3.6 (number
UNVERIFIED); also Stichtenoth, *Algebraic function fields and codes*, Thm 3.9.1, and Cornell,
Gold (classical). `R` a DVR with fraction field `K`, uniformizer `π`; `L/K` finite separable, tamely
ramified over `R` (every prime `Q` of the integral closure `S` of `R` in `L` over the maximal
ideal has `e(Q)` invertible in `R` and separable residue extension); `n` invertible in `R` with
every
`e(Q) ∣ n`. Let `M = L(t)` with `tⁿ = π`. Then every prime of the integral closure of `R` in `M`
over the maximal ideal has ramification index exactly `n` and separable residue extension
(equivalently: `M/K(t)` is unramified above `R`, as `K(t)/K` is totally ramified of degree `n`). -/
def AbhyankarDVR : Prop :=
  ∀ (R K L M : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [Field K] [Algebra R K] [IsFractionRing R K]
    [Field L] [Algebra K L] [Algebra R L] [IsScalarTower R K L]
    [FiniteDimensional K L] [Algebra.IsSeparable K L]
    [Field M] [Algebra L M] [Algebra K M] [Algebra R M]
    [IsScalarTower K L M] [IsScalarTower R K M]
    (π : R), Irreducible π → ∀ (n : ℕ), 0 < n → IsUnit (n : R) →
    (∀ (Q : Ideal (integralClosure R L)) [Q.IsPrime] [Q.LiesOver (IsLocalRing.maximalIdeal R)],
      IsUnit ((Q.ramificationIdx R : ℕ) : R) ∧ Q.ramificationIdx R ∣ n ∧
      Algebra.IsSeparable (R ⧸ IsLocalRing.maximalIdeal R) (integralClosure R L ⧸ Q)) →
    ∀ t : M, t ^ n = algebraMap R M π → IntermediateField.adjoin L {t} = ⊤ →
      ∀ (Q : Ideal (integralClosure R M)) [Q.IsPrime]
        [Q.LiesOver (IsLocalRing.maximalIdeal R)],
        Q.ramificationIdx R = n ∧
        Algebra.IsSeparable (R ⧸ IsLocalRing.maximalIdeal R) (integralClosure R M ⧸ Q)

theorem abhyankarDVR_iff : ObjBridge.AbhyankarDVR ↔ PkgI2.AbhyankarDVR.{0} := Iff.rfl

/-- **I2-Char over the shared layer** (Mumford §19, Thm 4; finite-level form). As
`PkgI2.CharpolyIndependentOfEll` with `φ ∈ End B` (the shared ring) instead of `φ : B ⟶ B`. -/
def CharpolyIndependentOfEll : Prop :=
  ∀ (k : Type) [Field k] (B : Grp (Over (Spec (.of k)))) [IsAbelianVariety B] (g : ℕ),
    dim B = (g : WithBot ℕ∞) → ∀ φ : End B,
    ∃ P : Polynomial ℤ, P.Monic ∧ P.natDegree = 2 * g ∧
      ∀ ℓ : ℕ, ℓ.Prime → (ℓ : k) ≠ 0 → ∀ n : ℕ, 0 < n →
        ∀ e : torsion B (AlgebraicClosure k) (ℓ ^ n) ≃ (Fin (2 * g) → ZMod (ℓ ^ n)),
        (∀ x y : torsion B (AlgebraicClosure k) (ℓ ^ n),
          ∀ h : x.1 * y.1 ∈ torsion B (AlgebraicClosure k) (ℓ ^ n),
            e ⟨x.1 * y.1, h⟩ = e x + e y) →
        ∀ M : Matrix (Fin (2 * g)) (Fin (2 * g)) (ZMod (ℓ ^ n)),
        (∀ x y : torsion B (AlgebraicClosure k) (ℓ ^ n), y.1 = x.1 ≫ φ.hom →
          e y = M.mulVec (e x)) →
        M.charpoly = P.map (Int.castRingHom (ZMod (ℓ ^ n)))

/-- Equivalent to the original, through the bridge bijection. -/
theorem charpolyIndependentOfEll_iff :
    ObjBridge.CharpolyIndependentOfEll ↔ PkgI2.CharpolyIndependentOfEll.{0} :=
  ⟨fun h k _ B _ g hg φ => h k B g hg (homOfGrp φ),
   fun h k _ B _ g hg φ => h k B g hg (grpOfHom φ)⟩

/-- **I2-Rank over the shared layer** (Mumford §19, Thm 3, rank part): any `4gg' + 1` elements
of the ℤ-module `Hom A B` are ℤ-linearly dependent. (The original's instance argument
`[IsCommMonObj B.X]` is now a global instance, `ObjBridge.isCommMonObj`.) -/
def HomRankBound : Prop :=
  ∀ (k : Type) [Field k] (A B : Grp (Over (Spec (.of k)))) [IsAbelianVariety A]
    [IsAbelianVariety B] (g g' : ℕ),
    dim A = (g : WithBot ℕ∞) → dim B = (g' : WithBot ℕ∞) →
    ∀ f : Fin (4 * g * g' + 1) → Hom A B,
      ∃ c : Fin (4 * g * g' + 1) → ℤ, c ≠ 0 ∧ ∑ i, c i • f i = 0

/-- Equivalent to the original, through the bridge bijection and `hom_sum_zsmul`. -/
theorem homRankBound_iff : ObjBridge.HomRankBound ↔ PkgI2.HomRankBound.{0} := by
  constructor
  · intro h k _ A B _ _ _ g g' hA hB f
    obtain ⟨c, hc, hs⟩ := h k A B g g' hA hB (fun i => homOfGrp (f i))
    refine ⟨c, hc, ?_⟩
    have := congrArg PkgI3.AbVar.Hom.hom hs
    rw [hom_sum_zsmul] at this
    exact this
  · intro h k _ A B _ _ g g' hA hB f
    obtain ⟨c, hc, hp⟩ := h k A B g g' hA hB (fun i => grpOfHom (f i))
    refine ⟨c, hc, ?_⟩
    rw [hom_eq_zero_iff, hom_sum_zsmul]
    exact hp

/-! ## I3 leaves

Each is I3's text with `A : AbVar k` replaced by `A : Grp (Over (Spec k))` with
`[IsAbelianVariety A]`, and `End`, `End0`, `T`, `V`, `galRep`, `dim`, `tateHomZl` the shared ones.
Equivalence with the original: `forall_abVar_iff`-style round trips (`ofGrp (toGrp A) = A` is
`rfl`). -/

/-- Every nonzero endomorphism is an isogeny. -/
def EndDivision {k : Type} [Field k] (A : Grp (Over (Spec (.of k)))) [IsAbelianVariety A] :
    Prop :=
  ∀ f : End A, f ≠ 0 → PkgI3.AbVar.IsIsogenyMor f.hom

theorem endDivision_iff {k : Type} [Field k] (A : Grp (Over (Spec (.of k))))
    [IsAbelianVariety A] : EndDivision A ↔ PkgI3.EndDivision (ofGrp A) := Iff.rfl

/-- **I3.F1 (Faltings 1983, Satz 3)** over the shared layer. -/
def FaltingsSemisimple : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (A : Grp (Over (Spec (.of K)))) [IsAbelianVariety A]
    (ℓ : ℕ) [Fact ℓ.Prime], (galRep A ℓ).IsSemisimpleRepresentation

theorem faltingsSemisimple_iff : FaltingsSemisimple ↔ PkgI3.FaltingsSemisimple :=
  ⟨fun h K _ _ A ℓ _ => h K (toGrp A) ℓ, fun h K _ _ A _ ℓ _ => h K (ofGrp A) ℓ⟩

/-- **I3.F2 (Faltings 1983, Satz 4 and Korollar 1)** over the shared layer. -/
def FaltingsTate : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (A B : Grp (Over (Spec (.of K))))
    [IsAbelianVariety A] [IsAbelianVariety B] (ℓ : ℕ) [Fact ℓ.Prime],
    Function.Injective (tateHomZl A B ℓ) ∧
      Set.range (tateHomZl A B ℓ) = {φ | PkgI3.AbVar.IsGalEquivariant φ}

/-- Two-object form of `forall_abVar_iff` (the motive is abstracted, so the round trip
`ofGrp (toGrp A) = A` is checked by structure eta, not by unfolding the motive). -/
theorem forall₂_abVar_iff {K : Type} [Field K] (P : PkgI3.AbVar K → PkgI3.AbVar K → Prop) :
    (∀ A B : PkgI3.AbVar K, P A B) ↔
      ∀ (A B : Grp (Over (Spec (.of K)))) [IsAbelianVariety A] [IsAbelianVariety B],
        P (ofGrp A) (ofGrp B) :=
  ⟨fun h _ _ _ _ => h _ _, fun h A B => h (toGrp A) (toGrp B)⟩

theorem faltingsTate_iff : FaltingsTate ↔ PkgI3.FaltingsTate := by
  constructor
  · intro h K _ _ A B ℓ _
    exact (forall₂_abVar_iff (fun A B : PkgI3.AbVar K => ∀ (ℓ : ℕ) [Fact ℓ.Prime],
      Function.Injective (PkgI3.AbVar.tateHomZl ℓ A B) ∧
        Set.range (PkgI3.AbVar.tateHomZl ℓ A B) = {φ | PkgI3.AbVar.IsGalEquivariant φ})).mpr
      (fun A B _ _ ℓ _ => h K A B ℓ) A B ℓ
  · intro h K _ _ A B _ _ ℓ _
    exact h K (ofGrp A) (ofGrp B) ℓ

/-- **I3.M0 (Mumford §4, §18-19)** over the shared layer. -/
def TateModuleFree : Prop :=
  ∀ (k : Type) [Field k] (A : Grp (Over (Spec (.of k)))) [IsAbelianVariety A] (ℓ : ℕ)
    [Fact ℓ.Prime], (ℓ : k) ≠ 0 →
    Module.Free ℤ_[ℓ] (T A ℓ) ∧ Module.Finite ℤ_[ℓ] (T A ℓ) ∧
      ((Module.finrank ℤ_[ℓ] (T A ℓ) : ℕ∞) : WithBot ℕ∞) = 2 * dim A

theorem tateModuleFree_iff : TateModuleFree ↔ PkgI3.TateModuleFree :=
  ⟨fun h k _ A ℓ _ => h k (toGrp A) ℓ, fun h k _ A _ ℓ _ => h k (ofGrp A) ℓ⟩

/-- **I3.M1 (Mumford §19, Thm 3)** over the shared layer. -/
def HomFreeFinite : Prop :=
  ∀ (k : Type) [Field k] (A B : Grp (Over (Spec (.of k)))) [IsAbelianVariety A]
    [IsAbelianVariety B],
    Module.Free ℤ (Hom A B) ∧ Module.Finite ℤ (Hom A B) ∧
      ((Module.finrank ℤ (Hom A B) : ℕ∞) : WithBot ℕ∞) ≤ 4 * dim A * dim B ∧
      ∀ (ℓ : ℕ) [Fact ℓ.Prime], (ℓ : k) ≠ 0 → Function.Injective (tateHomZl A B ℓ)

theorem homFreeFinite_iff : HomFreeFinite ↔ PkgI3.HomFreeFinite :=
  ⟨fun h k _ A B => h k (toGrp A) (toGrp B), fun h k _ A B _ _ => h k (ofGrp A) (ofGrp B)⟩

/-- **I3.M2 (Mumford §19, Thm 4)** over the shared layer. -/
def CharPolyIndepOfEll : Prop :=
  ∀ (k : Type) [Field k] (A : Grp (Over (Spec (.of k)))) [IsAbelianVariety A] (φ : End A),
    ∃ P : ℤ[X], P.Monic ∧
    ∀ (ℓ : ℕ) [Fact ℓ.Prime], (ℓ : k) ≠ 0 →
      ∀ (I : Type) [Fintype I] [DecidableEq I] (b : Module.Basis I ℚ_[ℓ] (V A ℓ)),
        (LinearMap.toMatrix b b ((PkgI3.AbVar.homT (ℓ := ℓ) φ).baseChange ℚ_[ℓ])).charpoly =
          P.map (Int.castRingHom ℚ_[ℓ])

theorem charPolyIndepOfEll_iff : CharPolyIndepOfEll ↔ PkgI3.CharPolyIndepOfEll :=
  ⟨fun h k _ A φ => h k (toGrp A) φ, fun h k _ A _ φ => h k (ofGrp A) φ⟩

/-- The same leaf quantified over morphisms of group objects `φ : A ⟶ A` (through the bridge
bijection, `forall_hom_iff`). -/
theorem charPolyIndepOfEll_iff_grp : CharPolyIndepOfEll ↔
    ∀ (k : Type) [Field k] (A : Grp (Over (Spec (.of k)))) [IsAbelianVariety A] (φ : A ⟶ A),
    ∃ P : ℤ[X], P.Monic ∧
    ∀ (ℓ : ℕ) [Fact ℓ.Prime], (ℓ : k) ≠ 0 →
      ∀ (I : Type) [Fintype I] [DecidableEq I] (b : Module.Basis I ℚ_[ℓ] (V A ℓ)),
        (LinearMap.toMatrix b b
          ((PkgI3.AbVar.homT (ℓ := ℓ) (homOfGrp φ)).baseChange ℚ_[ℓ])).charpoly =
          P.map (Int.castRingHom ℚ_[ℓ]) :=
  ⟨fun h k _ A _ φ => h k A (homOfGrp φ),
   fun h k _ A _ φ => homOfGrp_grpOfHom φ ▸ h k A (grpOfHom φ)⟩

/-- **I3.M3 (Poincaré complete reducibility, Mumford §19, Thm 1)** over the shared layer. -/
def PoincareReducibility : Prop :=
  ∀ (k : Type) [Field k] [CharZero k] (A J : Grp (Over (Spec (.of k)))) [IsAbelianVariety A]
    [IsAbelianVariety J], EndDivision A →
    ∀ f : Hom A J, f ≠ 0 → ∃ (Z : Grp (Over (Spec (.of k)))) (_ : IsAbelianVariety Z)
      (g : Hom Z J),
      PkgI3.AbVar.IsIsogenyMor (fst (ofGrp A).X (ofGrp Z).X ≫ f.hom * snd (ofGrp A).X (ofGrp Z).X ≫
          g.hom)

theorem poincareReducibility_iff : PoincareReducibility ↔ PkgI3.PoincareReducibility := by
  constructor
  · intro h k _ _ A J hE f hf
    obtain ⟨Z, _, g, hg⟩ := h k (toGrp A) (toGrp J) hE f hf
    exact ⟨ofGrp Z, g, hg⟩
  · intro h k _ _ A J _ _ hE f hf
    obtain ⟨Z, g, hg⟩ := h k (ofGrp A) (ofGrp J) hE f hf
    exact ⟨toGrp Z, inferInstance, g, hg⟩

/-- **I3.Q (QM dichotomy)** over the shared layer. -/
def QMDichotomy : Prop :=
  ∀ (k : Type) [Field k] [IsAlgClosed k] [CharZero k] (A : Grp (Over (Spec (.of k))))
    [IsAbelianVariety A], dim A = 2 →
    ∀ a b : ℚ, (∀ x : ℍ[ℚ, a, b], x ≠ 0 → IsUnit x) →
      Nonempty (ℍ[ℚ, a, b] →ₐ[ℚ] End0 A) →
        Nonempty (End0 A ≃ₐ[ℚ] ℍ[ℚ, a, b]) ∨
          ∃ d : ℚ, d < 0 ∧
            Nonempty (End0 A ≃ₐ[ℚ]
              Matrix (Fin 2) (Fin 2) (AdjoinRoot (Polynomial.X ^ 2 - Polynomial.C d)))

theorem qmDichotomy_iff : QMDichotomy ↔ PkgI3.QMDichotomy :=
  ⟨fun h k _ _ _ A => h k (toGrp A), fun h k _ _ _ A _ => h k (ofGrp A)⟩

/-- Package I3 over the shared layer. -/
structure I3Leaves : Prop where
  faltingsSemisimple : FaltingsSemisimple
  faltingsTate : FaltingsTate
  tateModuleFree : TateModuleFree
  homFreeFinite : HomFreeFinite
  charPolyIndepOfEll : CharPolyIndepOfEll
  poincare : PoincareReducibility
  qmDichotomy : QMDichotomy

theorem i3Leaves_iff : I3Leaves ↔ PkgI3.I3Leaves :=
  ⟨fun h => ⟨faltingsSemisimple_iff.mp h.1, faltingsTate_iff.mp h.2, tateModuleFree_iff.mp h.3,
      homFreeFinite_iff.mp h.4, charPolyIndepOfEll_iff.mp h.5, poincareReducibility_iff.mp h.6,
      qmDichotomy_iff.mp h.7⟩,
   fun h => ⟨faltingsSemisimple_iff.mpr h.1, faltingsTate_iff.mpr h.2, tateModuleFree_iff.mpr h.3,
      homFreeFinite_iff.mpr h.4, charPolyIndepOfEll_iff.mpr h.5, poincareReducibility_iff.mpr h.6,
      qmDichotomy_iff.mpr h.7⟩⟩

/-! ## I3 glue over the shared layer (proved) -/

theorem homT_galT {K : Type} [Field K] {A B : Grp (Over (Spec (.of K)))} [IsAbelianVariety A]
    [IsAbelianVariety B] {ℓ : ℕ} [Fact ℓ.Prime] (f : A ⟶ B) (σ : Field.absoluteGaloisGroup K)
    (x : T A ℓ) :
    PkgI3.AbVar.homT (homOfGrp f) ((ofGrp A).galT σ x) =
      (ofGrp B).galT σ (PkgI3.AbVar.homT (homOfGrp f) x) :=
  PkgI3.homT_galT _ σ x

theorem range_tateHomZl_subset {K : Type} [Field K] (A B : Grp (Over (Spec (.of K))))
    [IsAbelianVariety A] [IsAbelianVariety B] (ℓ : ℕ) [Fact ℓ.Prime] :
    Set.range (tateHomZl A B ℓ) ⊆ {φ | PkgI3.AbVar.IsGalEquivariant φ} :=
  PkgI3.range_tateHomZl_subset _ _ ℓ

/-- **Glue for E1 over the shared layer.** A nonzero `G_K`-equivariant map `V_ℓ A → V_ℓ B`
forces a nontrivial morphism of group objects `A ⟶ B`. -/
theorem exists_hom_ne_one_of_equivariant (hF : FaltingsTate) (hT : TateModuleFree)
    {K : Type} [Field K] [NumberField K] (A B : Grp (Over (Spec (.of K))))
    [IsAbelianVariety A] [IsAbelianVariety B] (ℓ : ℕ) [Fact ℓ.Prime]
    (φ : V A ℓ →ₗ[ℚ_[ℓ]] V B ℓ) (hφ : φ ≠ 0)
    (heq : ∀ σ, φ ∘ₗ galRep A ℓ σ = galRep B ℓ σ ∘ₗ φ) : ∃ f : A ⟶ B, f.hom.hom ≠ 1 := by
  obtain ⟨f, hf⟩ := PkgI3.exists_hom_ne_zero_of_equivariant (faltingsTate_iff.mp hF)
    (tateModuleFree_iff.mp hT) (ofGrp A) (ofGrp B) ℓ φ hφ heq
  refine ⟨grpOfHom f, fun h => hf ?_⟩
  rw [← homOfGrp_grpOfHom f, homOfGrp_eq_zero_iff]
  exact h

/-- The `G_K`-equivariant endomorphisms of `V_ℓ(A)`. -/
abbrev equivEnd {K : Type} [Field K] (A : Grp (Over (Spec (.of K)))) [IsAbelianVariety A]
    (ℓ : ℕ) [Fact ℓ.Prime] : Submodule ℚ_[ℓ] (Module.End ℚ_[ℓ] (V A ℓ)) :=
  PkgI3.equivEnd (ofGrp A) ℓ

/-- **Glue for C2 over the shared layer.** -/
theorem finrank_equivEnd (hF : FaltingsTate) (hT : TateModuleFree) (hH : HomFreeFinite)
    {K : Type} [Field K] [NumberField K] (A : Grp (Over (Spec (.of K)))) [IsAbelianVariety A]
    (ℓ : ℕ) [Fact ℓ.Prime] :
    Module.finrank ℚ_[ℓ] (equivEnd A ℓ) = Module.finrank ℤ (End A) :=
  PkgI3.finrank_equivEnd (faltingsTate_iff.mp hF) (tateModuleFree_iff.mp hT)
    (homFreeFinite_iff.mp hH) (ofGrp A) ℓ

end ObjBridge

/-! # §E. Base change and functoriality on the shared layer -/

namespace ObjBridge

open CategoryTheory AlgebraicGeometry Limits MonObj
open PkgI2 (IsAbelianVariety)

section BaseChange

variable {K : Type} [Field K] (A : Grp (Over (Spec (.of K)))) [IsAbelianVariety A]
  (L : Type) [Field L] [Algebra K L]

/-- I2's base change (`Functor.mapGrp` of `Over.pullback`) of an abelian variety is an abelian
variety; the three properties are those of I3's `AbVar.baseChange`. -/
instance isAbelianVariety_baseChange : IsAbelianVariety (PkgI2.baseChange A L) :=
  ⟨((ofGrp A).baseChange L).proper, ((ofGrp A).baseChange L).smooth,
    ((ofGrp A).baseChange L).geomInt⟩

/-- **I2's and I3's base changes agree** (definitionally): the bridge commutes with base change. -/
theorem ofGrp_baseChange : ofGrp (PkgI2.baseChange A L) = (ofGrp A).baseChange L := rfl

end BaseChange

section Functoriality

variable {K : Type} [Field K] {A B C : Grp (Over (Spec (.of K)))} [IsAbelianVariety A]
  [IsAbelianVariety B] [IsAbelianVariety C]

/-- A morphism of group objects acts on `L`-points by composition. -/
theorem ptMap_homOfGrp (L : Type) [Field L] [Algebra K L] (f : A ⟶ B) (x : PkgI2.Pts A L) :
    PkgI3.AbVar.ptMap (L := L) (homOfGrp f) x = x ≫ f.hom.hom := rfl

variable (ℓ : ℕ) [Fact ℓ.Prime]

/-- `T_ℓ` is a functor on the shared objects: composition. -/
theorem homT_comp (f : A ⟶ B) (g : B ⟶ C) :
    PkgI3.AbVar.homT (ℓ := ℓ) (homOfGrp (f ≫ g)) =
      PkgI3.AbVar.homT (ℓ := ℓ) (homOfGrp g) ∘ₗ PkgI3.AbVar.homT (ℓ := ℓ) (homOfGrp f) := by
  apply LinearMap.ext; intro x; apply Subtype.ext; funext n
  change Additive.ofMul (Additive.toMul (x.1 n) ≫ (f ≫ g).hom.hom) =
    Additive.ofMul ((Additive.toMul (x.1 n) ≫ f.hom.hom) ≫ g.hom.hom)
  exact congrArg Additive.ofMul (Category.assoc _ _ _).symm

/-- `T_ℓ` is a functor on the shared objects: identities. -/
theorem homT_id : PkgI3.AbVar.homT (ℓ := ℓ) (homOfGrp (𝟙 A)) = LinearMap.id := by
  apply LinearMap.ext; intro x; apply Subtype.ext; funext n
  change Additive.ofMul (Additive.toMul (x.1 n) ≫ (𝟙 A : A ⟶ A).hom.hom) = x.1 n
  exact congrArg Additive.ofMul (Category.comp_id (Additive.toMul (x.1 n)))

end Functoriality

end ObjBridge

/-! # §F. Consolidation: leaf I2-Rank is a consequence of leaf I3.M1 -/

namespace ObjBridge

open PkgI2 (IsAbelianVariety)

/-- **I2-Rank follows from I3.M1.** If `Hom A B` is a free ℤ-module of finite rank
`≤ 4 dim A dim B` (`HomFreeFinite`, Mumford §19 Thm 3), then any `4gg' + 1` elements are
ℤ-linearly dependent (`HomRankBound`). So I2-Rank need not be announced as a separate leaf. -/
theorem homRankBound_of_homFreeFinite (hH : HomFreeFinite) : ObjBridge.HomRankBound := by
  intro k _ A B _ _ g g' hA hB f
  obtain ⟨_, _, hle, -⟩ := hH k A B
  have e : 4 * dim A * dim B = (((4 * g * g' : ℕ) : ℕ∞) : WithBot ℕ∞) := by
    rw [hA, hB]; push_cast; rfl
  rw [e, WithBot.coe_le_coe, Nat.cast_le] at hle
  have hnot : ¬ LinearIndependent ℤ f := fun hli => by
    have := hli.fintype_card_le_finrank
    simp at this; omega
  obtain ⟨c, hc, i, hi⟩ := Fintype.not_linearIndependent_iff.mp hnot
  exact ⟨c, fun h => hi (by simp [h]), hc⟩

/-- The original I2-Rank, from the original I3.M1. -/
theorem pkgI2_homRankBound_of_pkgI3_homFreeFinite (hH : PkgI3.HomFreeFinite) :
    PkgI2.HomRankBound.{0} :=
  homRankBound_iff.mp (homRankBound_of_homFreeFinite (homFreeFinite_iff.mpr hH))

end ObjBridge

/-! ## Axiom audit -/
