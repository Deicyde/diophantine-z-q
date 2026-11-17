/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Definitions.Def_Mathlib_Algebra_Algebra_Hom (git blob 220a40b58b82d942ae40a876b0000453d2c30387, sha256 e3ba314e4a0ef5e89409b310c12a99070e46bf57bb2ac3f4a4c3d24cad2c1ded).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

section

section semialghom

/-- Let `φ : R →+* S` be a ring homomorphism, let `A` be an `R`-algebra and let `B` be
an `S`-algebra. Then `SemialgHom φ A B` is the ring homomorphisms `ψ : A →+* B`
making lying above `φ` (i.e. such that `ψ (r • a) = φ r • ψ a`).
-/
structure SemialgHom {R S : Type*} [CommSemiring R] [CommSemiring S] (φ : R →+* S)
    (A B : Type*)  [Semiring A] [Semiring B] [Algebra R A] [Algebra S B]
    extends A →ₛₗ[φ] B, RingHom A B

/-- Reinterpret a `SemialgHom` as a `RingHom`. -/
add_decl_doc SemialgHom.toRingHom



variable {R S : Type*} [CommSemiring R] [CommSemiring S] (φ : R →+* S)
    (A B : Type*) [Semiring A] [Semiring B] [Algebra R A] [Algebra S B]

instance instFunLike : FunLike (SemialgHom φ A B) A B where
  coe f := f.toFun
  coe_injective f g h := by
    cases f
    cases g
    congr
    exact DFunLike.coe_injective h

variable {φ} {A} {B} in
lemma SemialgHom.map_smul (ψ : SemialgHom φ A B) (m : R) (x : A) : ψ (m • x) = φ m • ψ x :=
  LinearMap.map_smul' ψ.toLinearMap m x

@[simp]
theorem coe_mk (f : A →ₛₗ[φ] B) (h₁ h₂ h₃) : ((⟨f, h₁, h₂, h₃⟩ : SemialgHom φ A B) : A → B) = f :=
  rfl

end semialghom

section semialghomclass

class SemialgHomClass (F : Type*) {R S : outParam Type*}
  [CommSemiring R] [CommSemiring S] (φ : outParam (R →+* S)) (A B : outParam Type*)
  [Semiring A] [Semiring B] [Algebra R A] [Algebra S B]
  [FunLike F A B] extends SemilinearMapClass F φ A B, RingHomClass F A B

variable (F : Type*) {R S : Type*}
  [CommSemiring R] [CommSemiring S] (φ : R →+* S) (A B : outParam Type*)
  [Semiring A] [Semiring B] [Algebra R A] [Algebra S B]
  [FunLike F A B] [SemialgHomClass F φ A B]

instance SemialgHomClass.instSemialgHom : SemialgHomClass (SemialgHom φ A B) φ A B where
  map_add ψ := ψ.map_add
  map_smulₛₗ ψ := ψ.map_smulₛₗ
  map_mul ψ := ψ.map_mul
  map_one ψ := ψ.map_one
  map_zero ψ := ψ.map_zero

variable {F} {φ} {A} {B} in

def SemialgHomClass.toSemialgHom (f : F) : SemialgHom φ A B :=
  { (f : A →ₛₗ[φ] B), (f : A →+* B) with }

instance : CoeTC F (SemialgHom φ A B) :=
  ⟨SemialgHomClass.toSemialgHom⟩

@[simp]
theorem SemialgHom.coe_coe (f : F) : ⇑(f : SemialgHom φ A B) = f :=
  rfl

end semialghomclass

section semialghom

variable {R S : Type*} [CommSemiring R] [CommSemiring S] {φ : R →+* S}
    {A B : Type*} [Semiring A] [Semiring B] [Algebra R A] [Algebra S B]

lemma SemialgHom.commutes (ψ : SemialgHom φ A B) (r : R) :
    ψ (algebraMap R A r) = algebraMap S B (φ r) := by
  have := ψ.map_smul r 1
  rw [Algebra.smul_def, mul_one, map_one] at this
  rw [this, Algebra.smul_def, mul_one]

theorem SemialgHom.toLinearMap_eq_coe (f : SemialgHom φ A B) : f.toLinearMap = f :=
  rfl

theorem SemialgHom.toRingHom_eq_coe (f : SemialgHom φ A B) : f.toRingHom = f :=
  rfl

theorem SemialgHom.algebraMap_apply {A B : Type*} [CommSemiring A] [CommSemiring B]
    [Algebra R A] [Algebra S B] (f : SemialgHom φ A B) (a : A) :
    letI := f.toAlgebra
    algebraMap A B a = f a := rfl

def SemialgHom.comp {T : Type*} [CommSemiring T] {C : Type*} [Semiring C]
    [Algebra T C] {ψ : S →+* T} {ξ : R →+* T} [RingHomCompTriple φ ψ ξ]
    (g : SemialgHom ψ B C) (f : SemialgHom φ A B) :
    SemialgHom ξ A C where
  __ := LinearMap.comp (SemialgHom.toLinearMap g) (SemialgHom.toLinearMap f)
  __ := RingHom.comp g.toRingHom f.toRingHom

def AlgHom.toSemialgHom {R : Type*} [CommSemiring R] {A B : Type*} [Semiring A] [Semiring B]
    [Algebra R A] [Algebra R B] (f : A →ₐ[R] B) :
    SemialgHom (RingHom.id R) A B where
  __ := f
  map_smul' _ _ := by simp

def SemialgHom.compAlgHom {T : Type*} [CommSemiring T] {C : Type*} [Semiring C]
    [Algebra T C] {ψ : S →+* T} [Algebra S A] (g : SemialgHom ψ B C) (f : A →ₐ[S] B) :
    SemialgHom ψ A C :=
  g.comp f.toSemialgHom

def SemialgHom.prod {C : Type*} [Semiring C] [Algebra S C] (f : SemialgHom φ A B)
    (g : SemialgHom φ A C) :
    SemialgHom φ A (B × C) where
  __ := RingHom.prod f.toRingHom g.toRingHom
  map_smul' r x := by simp

def SemialgHom.prodMap {C D : Type*} [Semiring C] [Semiring D]
    [Algebra S C] [Algebra S D] [Algebra R B] (f : SemialgHom φ A C) (g : SemialgHom φ B D) :
    SemialgHom φ (A × B) (C × D) :=
  (f.compAlgHom (AlgHom.fst R A B)).prod (g.compAlgHom (AlgHom.snd R A B))

@[simps!]
def SemialgHom.restrictScalars {R S R' S' : Type*} [CommSemiring R] [CommSemiring S]
    [CommSemiring R'] [CommSemiring S'] [Algebra R R'] [Algebra S S'] {φ : R →+* S}
    (ψ : SemialgHom φ R' S') {A B : Type*} [Semiring A] [Semiring B] [Algebra R A] [Algebra S B]
    [Algebra R' A] [Algebra S' B] [IsScalarTower R R' A] [IsScalarTower S S' B]
    (f : SemialgHom ψ.toRingHom A B) : SemialgHom φ A B where
  __ := f.toRingHom
  map_smul' r a := by
    have := f.map_smul (algebraMap R R' r) a
    simp_all [SemialgHom.toLinearMap_eq_coe, Algebra.algebraMap_eq_smul_one, ψ.map_smul]

end semialghom
