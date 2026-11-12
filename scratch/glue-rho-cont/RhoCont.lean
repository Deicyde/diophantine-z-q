/-
glue-rho-cont: continuity of the ℓ-adic Galois representation of pkg-I3.

Sections 1-2 are copied verbatim from scratch/pkg-I3/I3.lean (lines 15-335: the definitions
`Tate.T`, `AbVar`, `Pt`, `galAct`, `galT`, `galRep`, unchanged), plus six imports needed for
section 3 (module topology, Krull topology, residue fields, proper morphisms, base change of
bases, matrix topology). Section 3 is new: the topology on `T_ℓ`, open stabilizers on `A(K̄)`,
continuity of `ρ_ℓ` on `T_ℓ(A)` and on `V_ℓ(A)`. No sorry; axioms propext, Classical.choice,
Quot.sound (see the `#print axioms` at the end).
-/
import Mathlib.AlgebraicGeometry.Group.Abelian
import Mathlib.NumberTheory.Padics.RingHoms
import Mathlib.RepresentationTheory.Semisimple
import Mathlib.FieldTheory.AbsoluteGaloisGroup
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.Algebra.Quaternion
import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Mathlib.FieldTheory.KrullTopology
import Mathlib.AlgebraicGeometry.ResidueField
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.LinearAlgebra.TensorProduct.Basis
import Mathlib.Topology.Instances.Matrix

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

/-! ## 3. Continuity of `ρ_ℓ` (new: task glue-rho-cont) -/

/-! ### 3a. A discrete action with open stabilizers is continuous -/

namespace PkgI3.RhoCont

theorem continuous_orbit {G X : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [TopologicalSpace X] [DiscreteTopology X] (act : G → X → X)
    (hmul : ∀ g h x, act (g * h) x = act g (act h x))
    (hstab : ∀ x, ∃ H : OpenSubgroup G, ∀ g ∈ H, act g x = x) (x : X) :
    Continuous (fun g => act g x) := by
  rw [continuous_discrete_rng]
  intro b
  rw [isOpen_iff_forall_mem_open]
  intro g₀ hg₀
  obtain ⟨H, hH⟩ := hstab x
  refine ⟨(fun g => g₀⁻¹ * g) ⁻¹' (H : Set G), ?_,
    H.isOpen.preimage (continuous_const.mul continuous_id), by simp⟩
  intro g hg
  simp only [Set.mem_preimage, Set.mem_singleton_iff, SetLike.mem_coe] at hg hg₀ ⊢
  have : g = g₀ * (g₀⁻¹ * g) := by group
  rw [this, hmul, hH _ hg, hg₀]

theorem continuous_act {G X : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [TopologicalSpace X] [DiscreteTopology X] (act : G → X → X)
    (hmul : ∀ g h x, act (g * h) x = act g (act h x))
    (hstab : ∀ x, ∃ H : OpenSubgroup G, ∀ g ∈ H, act g x = x) :
    Continuous (fun p : G × X => act p.1 p.2) :=
  continuous_prod_of_discrete_right.2 (continuous_orbit act hmul hstab)

end PkgI3.RhoCont

/-! ### 3b. The inverse-limit topology on `T_ℓ(M)` for a discrete group `M`

`T ℓ M` is a subgroup of `ℕ → M`; with `M` discrete it carries the subspace topology of the
product, i.e. the inverse-limit topology of the discrete groups `M[ℓⁿ]` (Mathlib's instances,
no new definition). -/

namespace PkgI3.Tate

variable {ℓ : ℕ} [hℓ : Fact ℓ.Prime] {M : Type*} [AddCommGroup M] [TopologicalSpace M]
  [DiscreteTopology M]

omit hℓ in
lemma isOpen_coord_eq (n : ℕ) (m : M) : IsOpen {x : T ℓ M | x.1 n = m} := by
  have hc : Continuous (fun x : T ℓ M => x.1 n) := (continuous_apply n).comp continuous_subtype_val
  exact hc.isOpen_preimage {m} (isOpen_discrete _)

omit hℓ [TopologicalSpace M] [DiscreteTopology M] in
lemma pow_smul_shift {x : ℕ → M} (hx : x ∈ T ℓ M) (n k : ℕ) : (ℓ ^ n) • x (k + n) = x k := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ, mul_smul, ← add_assoc, hx.2 (k + n), ih]

omit [TopologicalSpace M] [DiscreteTopology M] in
/-- The kernel of the `n`-th coordinate is `ℓⁿ T_ℓ(M)`. -/
lemma coord_eq_zero_iff (x : T ℓ M) (n : ℕ) :
    x.1 n = 0 ↔ ∃ y : T ℓ M, x = ((ℓ : ℤ_[ℓ]) ^ n) • y := by
  constructor
  · intro hx
    let y : T ℓ M := ⟨fun k => x.1 (n + k), by simpa using hx, fun k => by
      show ℓ • x.1 (n + (k + 1)) = x.1 (n + k)
      rw [← add_assoc]; exact x.2.2 (n + k)⟩
    refine ⟨y, ?_⟩
    apply Subtype.ext; funext k
    change x.1 k = smulSeq ((ℓ : ℤ_[ℓ]) ^ n) y.1 k
    rw [smulSeq_congr y.2 k (c := ℓ ^ n) (by rw [map_pow, map_natCast, Nat.cast_pow])]
    change x.1 k = (ℓ ^ n) • x.1 (n + k)
    rw [add_comm n k, pow_smul_shift x.2 n k]
  · rintro ⟨y, rfl⟩
    rw [smul_apply]
    have : (PadicInt.toZModPow n ((ℓ : ℤ_[ℓ]) ^ n)) = 0 := by
      rw [map_pow, map_natCast]; exact_mod_cast ZMod.natCast_self (ℓ ^ n)
    rw [this, ZMod.val_zero, zero_smul]

end PkgI3.Tate

namespace PkgI3.Tate

variable {ℓ : ℕ} [hℓ : Fact ℓ.Prime] {M : Type*} [AddCommGroup M] [TopologicalSpace M]
  [DiscreteTopology M]

/-- The inverse-limit topology on `T_ℓ(M)` is the `ℓ`-adic one: every `ℤ_ℓ`-linear functional
`T_ℓ(M) → ℤ_ℓ` is continuous. -/
theorem continuous_of_linearMap_padicInt (c : T ℓ M →ₗ[ℤ_[ℓ]] ℤ_[ℓ]) : Continuous c := by
  apply continuous_of_continuousAt_zero c
  rw [ContinuousAt, map_zero, Metric.tendsto_nhds]
  intro ε hε
  obtain ⟨n, hn⟩ := PadicInt.exists_pow_neg_lt ℓ hε
  filter_upwards [(isOpen_coord_eq (ℓ := ℓ) (M := M) n 0).mem_nhds rfl] with x hx
  obtain ⟨y, rfl⟩ := (coord_eq_zero_iff x n).1 hx
  rw [map_smul, dist_zero_right, smul_eq_mul, norm_mul, PadicInt.norm_p_pow]
  calc (ℓ : ℝ) ^ (-(n : ℤ)) * ‖c y‖ ≤ (ℓ : ℝ) ^ (-(n : ℤ)) * 1 :=
        mul_le_mul_of_nonneg_left (PadicInt.norm_le_one _) (zpow_nonneg (Nat.cast_nonneg _) _)
    _ < ε := by simpa using hn

omit hℓ [TopologicalSpace M] [DiscreteTopology M] in
lemma coord_eq_zero_of_le {x : T ℓ M} {n k : ℕ} (hx : x.1 n = 0) (hk : k ≤ n) : x.1 k = 0 := by
  rw [← pow_smul_shift x.2 (n - k) k, Nat.add_sub_cancel' hk, hx, smul_zero]

omit hℓ in
/-- **The inverse-limit topology is the `ℓ`-adic topology.** The sets `{x | xₙ = 0} = ℓⁿ T_ℓ(M)`
(`coord_eq_zero_iff`) form a basis of neighbourhoods of `0`. -/
theorem nhds_zero_hasBasis :
    (nhds (0 : T ℓ M)).HasBasis (fun _ : ℕ => True) (fun n => {x : T ℓ M | x.1 n = 0}) := by
  refine ⟨fun U => ⟨fun hU => ?_, fun ⟨n, _, hn⟩ =>
    Filter.mem_of_superset ((isOpen_coord_eq n 0).mem_nhds rfl) hn⟩⟩
  rw [nhds_subtype, Filter.mem_comap] at hU
  obtain ⟨V, hV, hVU⟩ := hU
  rw [nhds_pi, Filter.mem_pi'] at hV
  obtain ⟨I, t, ht, hIt⟩ := hV
  refine ⟨I.sup id, trivial, fun x hx => hVU (hIt fun k hk => ?_)⟩
  have hk' : k ≤ I.sup id := Finset.le_sup (f := id) hk
  show x.1 k ∈ t k
  rw [coord_eq_zero_of_le hx hk']
  exact mem_of_mem_nhds (ht k)

omit [DiscreteTopology M] in
/-- Functoriality is jointly continuous: if `G` acts continuously on the discrete group `M`, the
induced action on `T_ℓ(M)` is continuous. -/
theorem continuous_map_action {G : Type*} [TopologicalSpace G] (act : G → (M →+ M))
    (hc : Continuous (fun p : G × M => act p.1 p.2)) :
    Continuous (fun p : G × T ℓ M => map (ℓ := ℓ) (act p.1) p.2) := by
  apply continuous_induced_rng.2
  apply continuous_pi
  intro n
  exact hc.comp (continuous_fst.prodMk
    ((continuous_apply n).comp (continuous_subtype_val.comp continuous_snd)))

end PkgI3.Tate

/-! ### 3c. Open stabilizers on `A(K̄)`

Each `K̄`-point `P` of a scheme locally of finite type over `K` is fixed by the open subgroup
`Gal(K̄/E)` for a finite extension `E/K`: the stalk map `κ = 𝒪_{A,x} → K̄` of `P` is determined
by finitely many values (`𝒪_{A,x}` is essentially of finite type over `K`), and these generate
a finite extension `E` because `K̄/K` is algebraic. -/

namespace PkgI3.RhoCont

open CategoryTheory AlgebraicGeometry Limits AbVar

universe u

variable {K : Type u} [Field K]

local notation "Kbar" => AlgebraicClosure K

lemma stalkClosedPointTo_comp_galois
    (g : Spec (CommRingCat.of Kbar) ⟶ Spec (CommRingCat.of K))
    (hg : g = Spec.map (CommRingCat.ofHom (algebraMap K Kbar))) (σ : Kbar ≃ₐ[K] Kbar) :
    Scheme.stalkClosedPointTo g ≫ CommRingCat.ofHom (σ : Kbar →+* Kbar) =
      Scheme.stalkClosedPointTo g := by
  subst hg
  ext y
  obtain ⟨U, hU, s, rfl⟩ := TopCat.Presheaf.exists_germ_eq _ y
  have hUtop : U = ⊤ := by
    ext z
    simp only [TopologicalSpace.Opens.coe_top, Set.mem_univ, iff_true]
    have : z = (Spec.map (CommRingCat.ofHom (algebraMap K Kbar)))
        (IsLocalRing.closedPoint Kbar) := Subsingleton.elim _ _
    rw [this]; exact hU
  subst hUtop
  have h := Scheme.germ_stalkClosedPointTo_Spec (CommRingCat.ofHom (algebraMap K Kbar))
  have h2 : (Spec (CommRingCat.of K)).presheaf.germ ⊤ _ trivial ≫
      Scheme.stalkClosedPointTo (Spec.map (CommRingCat.ofHom (algebraMap K Kbar))) ≫
        CommRingCat.ofHom (σ : Kbar →+* Kbar) =
      (Spec (CommRingCat.of K)).presheaf.germ ⊤ _ trivial ≫
        Scheme.stalkClosedPointTo (Spec.map (CommRingCat.ofHom (algebraMap K Kbar))) := by
    rw [← Category.assoc, h, Category.assoc, ← CommRingCat.ofHom_comp]
    congr 2
    ext c
    exact σ.commutes c
  exact congrArg (fun φ => φ.hom s) h2

/-- **Open stabilizers.** Every `K̄`-point of an abelian variety (indeed of any `K`-scheme locally
of finite type) is fixed by an open subgroup of `G_K`. -/
theorem exists_openSubgroup_galAct_eq (A : AbVar K) (P : A.Pt Kbar) :
    ∃ H : OpenSubgroup (Field.absoluteGaloisGroup K), ∀ σ ∈ H, A.galAct σ P = P := by
  set p : Spec (CommRingCat.of Kbar) ⟶ A.X.left := P.left with hp
  set x := p (IsLocalRing.closedPoint Kbar)
  set s := Scheme.stalkClosedPointTo p
  have hfin : (A.X.hom.stalkMap x).hom.EssFiniteType := LocallyOfFiniteType.stalkMap (f := A.X.hom) x
  let S : Set Kbar := s.hom '' (hfin.finset : Set _)
  have : Finite S := ((hfin.finset.finite_toSet).image _).to_subtype
  let E := IntermediateField.adjoin K S
  have : FiniteDimensional K E :=
    IntermediateField.finiteDimensional_adjoin (fun z _ => Algebra.IsIntegral.isIntegral z)
  refine ⟨⟨E.fixingSubgroup, E.fixingSubgroup_isOpen⟩, fun (σ : Kbar ≃ₐ[K] Kbar) hσ => ?_⟩
  have key : s ≫ CommRingCat.ofHom (σ : Kbar →+* Kbar) = s := by
    apply CommRingCat.hom_ext
    refine RingHom.EssFiniteType.ext hfin ?_ ?_
    · have hw : p ≫ A.X.hom = Spec.map (CommRingCat.ofHom (algebraMap K Kbar)) := by
        simpa [ptObj] using Over.w P
      have h := stalkClosedPointTo_comp_galois (p ≫ A.X.hom) hw σ
      rw [Scheme.stalkClosedPointTo_comp] at h
      have := congrArg CommRingCat.Hom.hom h
      simp only [CommRingCat.hom_comp, RingHom.comp_assoc] at this ⊢
      exact this
    · intro y hy
      exact (IntermediateField.mem_fixingSubgroup_iff E σ).1 hσ _
        (IntermediateField.subset_adjoin K S ⟨y, hy, rfl⟩)
  apply Over.OverMorphism.ext
  change Spec.map (CommRingCat.ofHom (σ : Kbar →+* Kbar)) ≫ p = p
  conv_lhs => rw [← Scheme.Spec_stalkClosedPointTo_fromSpecStalk p]
  rw [← Spec.map_comp_assoc, key, Scheme.Spec_stalkClosedPointTo_fromSpecStalk]

end PkgI3.RhoCont

/-! ### 3d. Continuity of `ρ_ℓ` on `T_ℓ(A)` and on `V_ℓ(A)` -/

namespace PkgI3.RhoCont

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj AbVar
open scoped TensorProduct

universe u

variable {K : Type u} [Field K]

local notation "Kbar" => AlgebraicClosure K

/-- `A(K̄)` with the discrete topology (so `A[ℓⁿ](K̄)` is discrete and `T_ℓ(A)` carries the
inverse-limit topology of section 3b). -/
instance instTopologicalSpacePt (A : AbVar K) : TopologicalSpace (Additive (A.Pt Kbar)) := ⊥

instance (A : AbVar K) : DiscreteTopology (Additive (A.Pt Kbar)) := ⟨rfl⟩

lemma galAct_mul (A : AbVar K) (σ τ : Field.absoluteGaloisGroup K) (P : A.Pt Kbar) :
    A.galAct (σ * τ) P = A.galAct σ (A.galAct τ P) := by
  have h := galHom_mul (K := K) (L := Kbar) σ τ
  exact (congrArg (· ≫ P) h).trans (Category.assoc _ _ _)

variable (ℓ : ℕ) [Fact ℓ.Prime]

/-- **`ρ_ℓ` is continuous on `T_ℓ(A)`**: the action map `G_K × T_ℓ(A) → T_ℓ(A)` is continuous
for the Krull topology on `G_K` and the inverse-limit topology on `T_ℓ(A)`. Unconditional. -/
theorem continuous_galT (A : AbVar K) :
    Continuous (fun p : Field.absoluteGaloisGroup K × A.T ℓ => A.galT p.1 p.2) := by
  apply Tate.continuous_map_action (act := fun σ => MonoidHom.toAdditive (A.galAct (L := Kbar) σ))
  exact continuous_act (fun σ (m : Additive (A.Pt Kbar)) => MonoidHom.toAdditive (A.galAct (L := Kbar) σ) m)
    (fun σ τ m => galAct_mul A σ τ (Additive.toMul m))
    (fun m => exists_openSubgroup_galAct_eq A (Additive.toMul m))

/-- The `ℓ`-adic topology on `V_ℓ(A)`: the module topology over `ℚ_ℓ` (when `T_ℓ(A) ≅ ℤ_ℓ^r`,
this is the product topology of `ℚ_ℓ^r`, see `continuous_galRep`). -/
instance instTopologicalSpaceV (A : AbVar K) : TopologicalSpace (A.V ℓ) :=
  moduleTopology ℚ_[ℓ] (A.V ℓ)

instance (A : AbVar K) : IsModuleTopology ℚ_[ℓ] (A.V ℓ) := ⟨rfl⟩

/-- `T_ℓ(A) → V_ℓ(A)`, `x ↦ 1 ⊗ x`, is continuous when `T_ℓ(A)` is free of finite rank. -/
theorem continuous_one_tmul (A : AbVar K) [Module.Free ℤ_[ℓ] (A.T ℓ)]
    [Module.Finite ℤ_[ℓ] (A.T ℓ)] :
    Continuous (fun x : A.T ℓ => (1 : ℚ_[ℓ]) ⊗ₜ[ℤ_[ℓ]] x) := by
  have := IsModuleTopology.toContinuousAdd ℚ_[ℓ] (A.V ℓ)
  let b := Module.Free.chooseBasis ℤ_[ℓ] (A.T ℓ)
  have h : (fun x : A.T ℓ => (1 : ℚ_[ℓ]) ⊗ₜ[ℤ_[ℓ]] x) = fun x =>
      ∑ i, ((b.coord i x : ℤ_[ℓ]) : ℚ_[ℓ]) • (b.baseChange ℚ_[ℓ] i) := by
    funext x
    conv_lhs => rw [← b.sum_repr x]
    rw [TensorProduct.tmul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [TensorProduct.tmul_smul, Module.Basis.baseChange_apply, Module.Basis.coord_apply,
      ← algebraMap_smul ℚ_[ℓ] (b.repr x i)]
    rfl
  rw [h]
  refine continuous_finsetSum _ fun i _ => ?_
  exact continuous_smul.comp ((continuous_subtype_val.comp
    (Tate.continuous_of_linearMap_padicInt (b.coord i))).prodMk continuous_const)

/-- **`ρ_ℓ` is continuous on `V_ℓ(A)`**: if `T_ℓ(A)` is free of finite rank over `ℤ_ℓ` (Mumford,
leaf I3.M0 `TateModuleFree`), the action map `G_K × V_ℓ(A) → V_ℓ(A)` is continuous for the Krull
topology and the `ℓ`-adic topology. -/
theorem continuous_galRep (A : AbVar K) [Module.Free ℤ_[ℓ] (A.T ℓ)]
    [Module.Finite ℤ_[ℓ] (A.T ℓ)] :
    Continuous (fun p : Field.absoluteGaloisGroup K × A.V ℓ => A.galRep ℓ p.1 p.2) := by
  have := IsModuleTopology.toContinuousAdd ℚ_[ℓ] (A.V ℓ)
  let b := Module.Free.chooseBasis ℤ_[ℓ] (A.T ℓ)
  let bV := b.baseChange ℚ_[ℓ]
  have h : (fun p : Field.absoluteGaloisGroup K × A.V ℓ => A.galRep ℓ p.1 p.2) = fun p =>
      ∑ j, bV.coord j p.2 • ((1 : ℚ_[ℓ]) ⊗ₜ[ℤ_[ℓ]] A.galT p.1 (b j)) := by
    funext ⟨σ, v⟩
    conv_lhs => rw [← bV.sum_repr v]
    rw [map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_smul, Module.Basis.coord_apply]
    congr 1
    change (A.galT σ).baseChange ℚ_[ℓ] (bV j) = _
    rw [Module.Basis.baseChange_apply, LinearMap.baseChange_tmul]
  rw [h]
  refine continuous_finsetSum _ fun j _ => ?_
  exact continuous_smul.comp
    (((IsModuleTopology.continuous_of_linearMap (bV.coord j)).comp continuous_snd).prodMk
      ((continuous_one_tmul ℓ A).comp
        ((continuous_galT ℓ A).comp (continuous_fst.prodMk continuous_const))))

/-- **Continuous traces** (the input C10 needs: Chebotarev density with Brauer–Nesbitt):
`σ ↦ tr ρ_ℓ(σ)` is continuous `G_K → ℚ_ℓ`. -/
theorem continuous_trace_galRep (A : AbVar K) [Module.Free ℤ_[ℓ] (A.T ℓ)]
    [Module.Finite ℤ_[ℓ] (A.T ℓ)] :
    Continuous (fun σ : Field.absoluteGaloisGroup K =>
      LinearMap.trace ℚ_[ℓ] (A.V ℓ) (A.galRep ℓ σ)) := by
  have := IsModuleTopology.toContinuousAdd ℚ_[ℓ] (A.V ℓ)
  let bV := (Module.Free.chooseBasis ℤ_[ℓ] (A.T ℓ)).baseChange ℚ_[ℓ]
  have h : (fun σ : Field.absoluteGaloisGroup K =>
      LinearMap.trace ℚ_[ℓ] (A.V ℓ) (A.galRep ℓ σ)) =
      fun σ => ∑ i, bV.coord i (A.galRep ℓ σ (bV i)) := by
    funext σ
    classical
    rw [LinearMap.trace_eq_matrix_trace ℚ_[ℓ] bV]
    simp only [Matrix.trace, Matrix.diag_apply, LinearMap.toMatrix_apply,
      Module.Basis.coord_apply]
  have hρ : ∀ v : A.V ℓ, Continuous (fun σ : Field.absoluteGaloisGroup K => A.galRep ℓ σ v) := by
    intro v
    have h1 : Continuous (fun σ : Field.absoluteGaloisGroup K => (σ, v)) :=
      continuous_id.prodMk continuous_const
    have h2 := (continuous_galRep ℓ A).comp h1
    refine h2.congr fun σ => ?_
    simp only [Function.comp_apply]
  have hc : ∀ i, Continuous (bV.coord i) := fun i =>
    IsModuleTopology.continuous_of_linearMap (bV.coord i)
  rw [h]
  refine continuous_finsetSum _ fun i _ => ?_
  refine ((hc i).comp (hρ (bV i))).congr fun σ => ?_
  simp only [Function.comp_apply]

/-- **Matrix form (`ρ_ℓ : G_K → GL_r(ℚ_ℓ)` continuous).** In any finite `ℚ_ℓ`-basis `b` of
`V_ℓ(A)`, the matrix of `ρ_ℓ(σ)` depends continuously on `σ` (entrywise topology). -/
theorem continuous_toMatrix_galRep (A : AbVar K) [Module.Free ℤ_[ℓ] (A.T ℓ)]
    [Module.Finite ℤ_[ℓ] (A.T ℓ)] {I : Type*} [Fintype I] [DecidableEq I]
    (b : Module.Basis I ℚ_[ℓ] (A.V ℓ)) :
    Continuous (fun σ : Field.absoluteGaloisGroup K => LinearMap.toMatrix b b (A.galRep ℓ σ)) := by
  have := IsModuleTopology.toContinuousAdd ℚ_[ℓ] (A.V ℓ)
  have hρ : ∀ v : A.V ℓ, Continuous (fun σ : Field.absoluteGaloisGroup K => A.galRep ℓ σ v) := by
    intro v
    have h1 : Continuous (fun σ : Field.absoluteGaloisGroup K => (σ, v)) :=
      continuous_id.prodMk continuous_const
    refine ((continuous_galRep ℓ A).comp h1).congr fun σ => ?_
    simp only [Function.comp_apply]
  refine continuous_pi fun i => continuous_pi fun j => ?_
  refine ((IsModuleTopology.continuous_of_linearMap (b.coord i)).comp (hρ (b j))).congr
    fun σ => ?_
  simp only [Function.comp_apply, LinearMap.toMatrix_apply, Module.Basis.coord_apply]

end PkgI3.RhoCont

/-! ### 3e. With pkg-I3's leaf I3.M0 -/

namespace PkgI3

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj AbVar

/-- Copied verbatim from scratch/pkg-I3/I3.lean (leaf I3.M0, Mumford §4, §18-19). -/
def TateModuleFree : Prop :=
  ∀ (k : Type) [Field k] (A : AbVar k) (ℓ : ℕ) [Fact ℓ.Prime], (ℓ : k) ≠ 0 →
    Module.Free ℤ_[ℓ] (A.T ℓ) ∧ Module.Finite ℤ_[ℓ] (A.T ℓ) ∧
      ((Module.finrank ℤ_[ℓ] (A.T ℓ) : ℕ∞) : WithBot ℕ∞) = 2 * A.dim

/-- **Continuity of `ρ_ℓ` from leaf I3.M0.** For `ℓ ≠ char K` (every `ℓ` for a number field),
`ρ_ℓ : G_K × V_ℓ(A) → V_ℓ(A)` is continuous and `σ ↦ tr ρ_ℓ(σ)` is continuous. -/
theorem continuous_galRep_of_tateModuleFree (hT : TateModuleFree) {K : Type} [Field K]
    (A : AbVar K) (ℓ : ℕ) [Fact ℓ.Prime] (hℓ : (ℓ : K) ≠ 0) :
    Continuous (fun p : Field.absoluteGaloisGroup K × A.V ℓ => A.galRep ℓ p.1 p.2) ∧
      Continuous (fun σ : Field.absoluteGaloisGroup K =>
        LinearMap.trace ℚ_[ℓ] (A.V ℓ) (A.galRep ℓ σ)) := by
  obtain ⟨h1, h2, -⟩ := hT K A ℓ hℓ
  exact ⟨RhoCont.continuous_galRep ℓ A, RhoCont.continuous_trace_galRep ℓ A⟩

end PkgI3

#print axioms PkgI3.RhoCont.exists_openSubgroup_galAct_eq
#print axioms PkgI3.RhoCont.continuous_galT
#print axioms PkgI3.Tate.continuous_of_linearMap_padicInt
#print axioms PkgI3.Tate.nhds_zero_hasBasis
#print axioms PkgI3.continuous_galRep_of_tateModuleFree
#print axioms PkgI3.RhoCont.continuous_toMatrix_galRep
