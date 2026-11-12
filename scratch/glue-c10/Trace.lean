/-
glue-c10: pkg-I3 definitions (sections 1-2 copied verbatim from scratch/pkg-I3/I3.lean) and the ℓ-independence of traces (C10).

Scratch file (task pkg-I3). Everything here is built on Mathlib v4.35.0 definitions:
schemes over `Spec K`, group objects in `Over (Spec K)`, `AlgebraicClosure`,
`Field.absoluteGaloisGroup`, `PadicInt`, `Representation`, `QuaternionAlgebra`.
No abstract structure is invented: the only new definitions are
* `AbVar K`         : an abelian variety (proper, smooth, geometrically integral group scheme),
* `AbVar.homGroup`  : the group `Hom_K(A, B)` of homomorphisms of group schemes,
* `AbVar.Pt`        : the group `A(K̄)` of `K̄`-points, with the Galois action,
* `Tate.T ℓ M`      : the `ℓ`-adic Tate module `lim M[ℓⁿ]` of an abelian group, as a `ℤ_ℓ`-module,
* `AbVar.T`, `AbVar.V` : `T_ℓ(A)`, `V_ℓ(A) = ℚ_ℓ ⊗ T_ℓ(A)` with the Galois representation.
Leaves are `def … : Prop`.
-/
import Mathlib.AlgebraicGeometry.Group.Abelian
import Mathlib.NumberTheory.Padics.RingHoms
import Mathlib.RepresentationTheory.Semisimple
import Mathlib.FieldTheory.AbsoluteGaloisGroup
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.Algebra.Quaternion
import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
import Mathlib.RingTheory.AdjoinRoot

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

/-- The `ℤ_ℓ`-linear extension `ℤ_ℓ ⊗_ℤ Hom(A, B) → Hom_{ℤ_ℓ}(T_ℓ A, T_ℓ B)`, `a ⊗ f ↦ a · T_ℓ(f)`. -/
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

namespace PkgI3

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open AbVar Polynomial
open scoped TensorProduct

/-- **I3.M2 — Mumford §19, Thm 4 (independence of `ℓ`)** — verbatim from pkg-I3. -/
def CharPolyIndepOfEll : Prop :=
  ∀ (k : Type) [Field k] (A : AbVar k) (φ : End A), ∃ P : ℤ[X], P.Monic ∧
    ∀ (ℓ : ℕ) [Fact ℓ.Prime], (ℓ : k) ≠ 0 →
      ∀ (I : Type) [Fintype I] [DecidableEq I] (b : Module.Basis I ℚ_[ℓ] (A.V ℓ)),
        (LinearMap.toMatrix b b ((homT (ℓ := ℓ) φ).baseChange ℚ_[ℓ])).charpoly =
          P.map (Int.castRingHom ℚ_[ℓ])

/-- **C10, the characteristic-polynomial comparison (GLUE, proved from Mumford §19 Thm 4).**
For an endomorphism `φ` of an abelian variety over any field `k` there is one integer `t` that is
the trace of `V_ℓ(φ)` for every prime `ℓ ≠ char k` (N5 L788-790: "independent of the coefficient
prime"). -/
theorem trace_indep_of_ell (h : CharPolyIndepOfEll) (k : Type) [Field k] (A : AbVar k)
    (φ : End A) : ∃ t : ℤ, ∀ (ℓ : ℕ) [Fact ℓ.Prime], (ℓ : k) ≠ 0 →
      ∀ (I : Type) [Fintype I] [DecidableEq I] (b : Module.Basis I ℚ_[ℓ] (A.V ℓ)),
        LinearMap.trace ℚ_[ℓ] (A.V ℓ) ((homT (ℓ := ℓ) φ).baseChange ℚ_[ℓ]) = (t : ℚ_[ℓ]) := by
  obtain ⟨P, -, hP⟩ := h k A φ
  refine ⟨-P.nextCoeff, fun ℓ _ hℓ I _ _ b => ?_⟩
  rw [LinearMap.trace_eq_matrix_trace ℚ_[ℓ] b, Matrix.trace_eq_neg_charpoly_nextCoeff,
    hP ℓ hℓ I b, Polynomial.nextCoeff_map (Int.castRingHom ℚ_[ℓ]).injective_int]
  simp

/-- The same integer for two primes: the traces at `ℓ₁` and `ℓ₂` are images of one integer. -/
theorem trace_eq_trace_of_ell (h : CharPolyIndepOfEll) (k : Type) [Field k] (A : AbVar k)
    (φ : End A) (ℓ₁ ℓ₂ : ℕ) [Fact ℓ₁.Prime] [Fact ℓ₂.Prime] (h₁ : (ℓ₁ : k) ≠ 0) (h₂ : (ℓ₂ : k) ≠ 0)
    (I₁ I₂ : Type) [Fintype I₁] [DecidableEq I₁] [Fintype I₂] [DecidableEq I₂]
    (b₁ : Module.Basis I₁ ℚ_[ℓ₁] (A.V ℓ₁)) (b₂ : Module.Basis I₂ ℚ_[ℓ₂] (A.V ℓ₂)) :
    ∃ t : ℤ, LinearMap.trace ℚ_[ℓ₁] (A.V ℓ₁) ((homT (ℓ := ℓ₁) φ).baseChange ℚ_[ℓ₁]) = t ∧
      LinearMap.trace ℚ_[ℓ₂] (A.V ℓ₂) ((homT (ℓ := ℓ₂) φ).baseChange ℚ_[ℓ₂]) = t := by
  obtain ⟨t, ht⟩ := trace_indep_of_ell h k A φ
  exact ⟨t, ht ℓ₁ h₁ I₁ b₁, ht ℓ₂ h₂ I₂ b₂⟩

end PkgI3

#print axioms PkgI3.trace_indep_of_ell
#print axioms PkgI3.trace_eq_trace_of_ell
