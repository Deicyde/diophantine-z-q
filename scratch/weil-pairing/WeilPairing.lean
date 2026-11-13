import ZInQKernel.HDecomp.Objects
import Mathlib.NumberTheory.Cyclotomic.CyclotomicCharacter
import Mathlib.LinearAlgebra.Matrix.BilinearForm
import ZInQKernel.HDecomp.Assembly.C8

/-!
# weil-pairing: polarizations and the Weil pairing over `PkgI3.AbVar`

Task weil-pairing (2026-11-12). Over the project's abelian-variety layer
(`ZInQKernel/HDecomp/Objects.lean`, `PkgI3.AbVar`):

* §1 torsion `A[n] ⊆ A(K̄)`, `μ_n ⊆ K̄ˣ`, the Galois actions on both;
* §2 pairings `A[n] × B[n] → μ_n` (bilinear and `μ_n`-valued by construction), perfect,
  alternating, Galois-equivariant; pull-back along homomorphisms; the basic API (proved);
* §3 the dual abelian variety *as seen by its Weil pairings* (`WeilDual`), dual morphisms,
  the Weil pairing `e^λ_n(x, y) = e_n(x, λ y)` of a homomorphism `λ : A → Â`, symmetric
  isogenies, polarizations (with Rosati positivity), principal polarizations;
* §4 leaves (`def … : Prop`, with references) and the restated T9;
* §5 the old consequence-form leaf `LeafPush.T09_WeilPairing` (copied verbatim, universe `0`)
  derived from the new T9 and the isogeny leaf;
* §6 the G12 input: `det² = χ^{rank}` for a perfect pairing with multiplier.

No `sorry`, no `axiom`.
-/

noncomputable section

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace WeilPairing

open PkgI3 PkgI3.AbVar

variable {K : Type} [Field K]

/-! ## §1. Torsion, roots of unity, Galois actions -/

/-- The group `A(K̄)`, written additively. -/
abbrev P (A : AbVar K) : Type := Additive (A.Pt (AlgebraicClosure K))

/-- `A[n] = A(K̄)[n]`, the `n`-torsion of `A(K̄)`. -/
def tors (A : AbVar K) (n : ℕ) : AddSubgroup (P A) where
  carrier := {x | n • x = 0}
  add_mem' {x y} hx hy := by
    change n • x = 0 at hx
    change n • y = 0 at hy
    change n • (x + y) = 0
    rw [smul_add, hx, hy, add_zero]
  zero_mem' := smul_zero n
  neg_mem' {x} hx := by
    change n • x = 0 at hx
    change n • (-x) = 0
    rw [smul_neg, hx, neg_zero]

lemma mem_tors {A : AbVar K} {n : ℕ} {x : P A} : x ∈ tors A n ↔ n • x = 0 := Iff.rfl

lemma nsmul_tors {A : AbVar K} {n : ℕ} (x : tors A n) : n • (x : P A) = 0 := x.2

/-- A group homomorphism `A(K̄) → B(K̄)` restricted to `n`-torsion. -/
def torsHom {A B : AbVar K} (φ : P A →+ P B) (n : ℕ) : tors A n →+ tors B n where
  toFun x := ⟨φ x, by rw [mem_tors, ← map_nsmul, nsmul_tors x, map_zero]⟩
  map_zero' := Subtype.ext (map_zero φ)
  map_add' x y := Subtype.ext (map_add φ _ _)

@[simp] lemma torsHom_coe {A B : AbVar K} (φ : P A →+ P B) (n : ℕ) (x : tors A n) :
    (torsHom φ n x : P B) = φ x := rfl

/-- The inclusion `A[n] ⊆ A[k]` for `n ∣ k`. -/
def torsIncl (A : AbVar K) {n k : ℕ} (h : n ∣ k) : tors A n →+ tors A k where
  toFun x := ⟨x, by
    obtain ⟨c, rfl⟩ := h
    rw [mem_tors, mul_comm, mul_smul, nsmul_tors x, smul_zero]⟩
  map_zero' := rfl
  map_add' _ _ := rfl

/-- Multiplication by `m`, `A[m n] → A[n]`. -/
def torsSmul (A : AbVar K) (m n : ℕ) : tors A (m * n) →+ tors A n where
  toFun x := ⟨m • (x : P A), by
    rw [mem_tors, ← mul_smul, mul_comm, nsmul_tors x]⟩
  map_zero' := Subtype.ext (smul_zero m)
  map_add' x y := Subtype.ext (smul_add m (x : P A) y)

/-- `μ_n = μ_n(K̄)`, written additively. -/
abbrev Mu (K : Type) [Field K] (n : ℕ) : Type := Additive (rootsOfUnity n (AlgebraicClosure K))

/-- The underlying unit of `K̄` of an element of `μ_n`. -/
def Mu.val {n : ℕ} (z : Mu K n) : (AlgebraicClosure K)ˣ :=
  ((Additive.toMul z : rootsOfUnity n (AlgebraicClosure K)) : (AlgebraicClosure K)ˣ)

@[simp] lemma Mu.val_add {n : ℕ} (z w : Mu K n) : (z + w).val = z.val * w.val := rfl
@[simp] lemma Mu.val_zero {n : ℕ} : (0 : Mu K n).val = 1 := rfl
@[simp] lemma Mu.val_nsmul {n : ℕ} (m : ℕ) (z : Mu K n) : (m • z).val = z.val ^ m := rfl
@[simp] lemma Mu.val_neg {n : ℕ} (z : Mu K n) : (-z).val = z.val⁻¹ := rfl

lemma Mu.val_injective {n : ℕ} : Function.Injective (Mu.val : Mu K n → _) := by
  intro z w h
  exact Additive.toMul.injective (Subtype.ext h)

lemma Mu.val_pow {n : ℕ} (z : Mu K n) : z.val ^ n = 1 :=
  (mem_rootsOfUnity n _).1 (Additive.toMul z).2

/-- Every element of `μ_n` is killed by `n`. -/
lemma Mu.nsmul_eq_zero {n : ℕ} (z : Mu K n) : n • z = 0 :=
  Mu.val_injective (by rw [Mu.val_nsmul, Mu.val_pow, Mu.val_zero])

/-- The absolute Galois group `G_K = Aut(K̄/K)` (definitionally `Field.absoluteGaloisGroup K`). -/
abbrev Gal (K : Type) [Field K] : Type := AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K

/-- `G_K` acting on `A(K̄)` (Objects' `galAct`: `σ` applied to coordinates). -/
def galP (A : AbVar K) (σ : Gal K) : P A →+ P A := MonoidHom.toAdditive (A.galAct σ)

/-- `G_K` acting on `A[n]`. -/
def galTors (A : AbVar K) (n : ℕ) (σ : Gal K) : tors A n →+ tors A n := torsHom (galP A σ) n

/-- `G_K` acting on `μ_n`. -/
def galMu (n : ℕ) (σ : Gal K) : Mu K n →+ Mu K n :=
  MonoidHom.toAdditive
    (restrictRootsOfUnity σ n)

@[simp] lemma galMu_val (n : ℕ) (σ : Gal K) (z : Mu K n) :
    ((galMu n σ z).val : AlgebraicClosure K) =
      σ (z.val : AlgebraicClosure K) := rfl

/-- A homomorphism `f : A → B` acting on `K̄`-points. -/
def homP {A B : AbVar K} (f : Hom A B) : P A →+ P B := MonoidHom.toAdditive (ptMap f)

/-- `f` acting on `n`-torsion. -/
def torsMap {A B : AbVar K} (f : Hom A B) (n : ℕ) : tors A n →+ tors B n := torsHom (homP f) n

/-- Homomorphisms of abelian varieties over `K` commute with `G_K` on `K̄`-points. -/
lemma homP_galP {A B : AbVar K} (f : Hom A B) (σ : Gal K) (x : P A) :
    homP f (galP A σ x) = galP B σ (homP f x) := by
  change Additive.ofMul ((galHom _ ≫ Additive.toMul x) ≫ f.hom) =
    Additive.ofMul (galHom _ ≫ (Additive.toMul x ≫ f.hom))
  rw [Category.assoc]

lemma torsMap_galTors {A B : AbVar K} (f : Hom A B) (n : ℕ) (σ : Gal K) (x : tors A n) :
    torsMap f n (galTors A n σ x) = galTors B n σ (torsMap f n x) :=
  Subtype.ext (homP_galP f σ x)

/-! ## §2. Pairings with values in `μ_n` -/

/-- A pairing `A[n] × B[n] → μ_n`. It is bi-additive (bimultiplicative in `μ_n`) and takes values
in `μ_n` by construction. -/
abbrev Pairing (A B : AbVar K) (n : ℕ) : Type := tors A n →+ tors B n →+ Mu K n

variable {A B A' B' : AbVar K} {n : ℕ}

/-- Perfect (both kernels trivial; for finite groups of the same order this is perfectness). -/
def IsPerfect (e : Pairing A B n) : Prop :=
  (∀ x, (∀ y, e x y = 0) → x = 0) ∧ (∀ y, (∀ x, e x y = 0) → y = 0)

/-- Alternating: `e(x, x) = 1` (written additively: `0`). -/
def IsAlternating (e : Pairing A A n) : Prop := ∀ x, e x x = 0

/-- Galois-equivariant: `e(σx, σy) = σ(e(x, y))`. -/
def IsGalEquivariant (e : Pairing A B n) : Prop :=
  ∀ (σ : Gal K) x y, e (galTors A n σ x) (galTors B n σ y) = galMu n σ (e x y)

/-- Pull-back of a pairing on `A'[n] × B'[n]` along `f : A(K̄) → A'(K̄)`, `g : B(K̄) → B'(K̄)`. -/
def pull (e : Pairing A' B' n) (f : P A →+ P A') (g : P B →+ P B') : Pairing A B n where
  toFun x := (e (torsHom f n x)).comp (torsHom g n)
  map_zero' := by ext y; simp
  map_add' x x' := by ext y; simp

@[simp] lemma pull_apply (e : Pairing A' B' n) (f : P A →+ P A') (g : P B →+ P B') (x y) :
    pull e f g x y = e (torsHom f n x) (torsHom g n y) := rfl

/-! ### Basic API -/

lemma add_left (e : Pairing A B n) (x x' y) : e (x + x') y = e x y + e x' y := by
  rw [map_add, AddMonoidHom.add_apply]

lemma add_right (e : Pairing A B n) (x y y') : e x (y + y') = e x y + e x y' := map_add _ _ _

/-- Bimultiplicativity, in `K̄ˣ`. -/
lemma val_mul_left (e : Pairing A B n) (x x' y) :
    (e (x + x') y).val = (e x y).val * (e x' y).val := by rw [add_left, Mu.val_add]

lemma val_mul_right (e : Pairing A B n) (x y y') :
    (e x (y + y')).val = (e x y).val * (e x y').val := by rw [add_right, Mu.val_add]

lemma nsmul_left (e : Pairing A B n) (m : ℕ) (x y) : e (m • x) y = m • e x y := by
  rw [map_nsmul, AddMonoidHom.nsmul_apply]

lemma nsmul_right (e : Pairing A B n) (m : ℕ) (x y) : e x (m • y) = m • e x y := map_nsmul _ _ _

/-- Values in `μ_n`: `e(x, y)ⁿ = 1`. -/
lemma val_pow_eq_one (e : Pairing A B n) (x y) : (e x y).val ^ n = 1 := Mu.val_pow _

/-- An alternating pairing is skew-symmetric: `e(x, y) = e(y, x)⁻¹`. -/
lemma IsAlternating.skew {e : Pairing A A n} (h : IsAlternating e) (x y) : e x y = -e y x := by
  have h1 := h (x + y)
  rw [add_left, add_right, add_right, h x, h y, zero_add, add_zero] at h1
  exact eq_neg_of_add_eq_zero_left h1

lemma IsAlternating.pull {e : Pairing A' A' n} (h : IsAlternating e) (f : P A →+ P A') :
    IsAlternating (pull e f f) := fun _ => h _

/-- Pull-back along `G_K`-equivariant maps preserves Galois equivariance. -/
lemma IsGalEquivariant.pull {e : Pairing A' B' n} (h : IsGalEquivariant e)
    {f : P A →+ P A'} {g : P B →+ P B'}
    (hf : ∀ σ x, f (galP A σ x) = galP A' σ (f x)) (hg : ∀ σ y, g (galP B σ y) = galP B' σ (g y)) :
    IsGalEquivariant (pull e f g) := by
  intro σ x y
  have h1 : torsHom f n (galTors A n σ x) = galTors A' n σ (torsHom f n x) := Subtype.ext (hf σ x)
  have h2 : torsHom g n (galTors B n σ y) = galTors B' n σ (torsHom g n y) := Subtype.ext (hg σ y)
  rw [pull_apply, pull_apply, h1, h2, h σ]

/-- In particular along homomorphisms of abelian varieties over `K` (compatibility with
isogenies). -/
lemma IsGalEquivariant.pull_hom {e : Pairing A' B' n} (h : IsGalEquivariant e)
    (f : Hom A A') (g : Hom B B') : IsGalEquivariant (WeilPairing.pull e (homP f) (homP g)) :=
  h.pull (homP_galP f) (homP_galP g)

/-- Perfectness forces nontrivial torsion on the right: if `e` is perfect and `B[n] = 0` then
`A[n] = 0` (a non-vacuity check on `WeilDual`). -/
lemma IsPerfect.left_trivial {e : Pairing A B n} (h : IsPerfect e)
    (hB : ∀ y : tors B n, y = 0) (x : tors A n) : x = 0 :=
  h.1 x fun y => by rw [hB y, map_zero]

/-- The zero pairing is perfect only when both torsion groups are trivial. -/
lemma isPerfect_zero_iff :
    IsPerfect (0 : Pairing A B n) ↔ (∀ x : tors A n, x = 0) ∧ (∀ y : tors B n, y = 0) :=
  ⟨fun h => ⟨fun x => h.1 x fun _ => rfl, fun y => h.2 y fun _ => rfl⟩,
   fun h => ⟨fun x _ => h.1 x, fun y _ => h.2 y⟩⟩

/-! ## §3. Duals (as seen by their Weil pairings), polarizations, the Weil pairing -/

/-- Composition of homomorphisms, `g ∘ f`. -/
def comp {A B C : AbVar K} (f : Hom A B) (g : Hom B C) : Hom A C := Hom.mk' (f.hom ≫ g.hom)

lemma homP_comp {A B C : AbVar K} (f : Hom A B) (g : Hom B C) (x : P A) :
    homP (comp f g) x = homP g (homP f x) := by
  change Additive.ofMul (Additive.toMul x ≫ (f.hom ≫ g.hom)) =
    Additive.ofMul ((Additive.toMul x ≫ f.hom) ≫ g.hom)
  rw [Category.assoc]

lemma torsMap_comp {A B C : AbVar K} (f : Hom A B) (g : Hom B C) (n : ℕ) (x : tors A n) :
    torsMap (comp f g) n x = torsMap g n (torsMap f n x) := Subtype.ext (homP_comp f g x)

/-- **The dual of `A`, as seen by its Weil pairings.** An abelian variety `Â` over `K` with a
family of pairings `e_n : A[n] × Â[n] → μ_n` which, for every `n ≥ 1` invertible in `K`, is
perfect and `G_K`-equivariant, and compatible: `e_{mn}(x, y) = e_n(m x, y)` for `x ∈ A[mn]`,
`y ∈ Â[n]` (Mumford, *Abelian varieties*, §20, properties of `e_n`; UNVERIFIED numbering).
The genuine dual `Â = Pic⁰_{A/K}` with Mumford's `e_n` is one (STANDARD; Mumford §§8, 13, 20 over
`K̄`, and the pairing is defined over `K`). Mathlib has no Picard scheme (no line bundles on
schemes), so `Pic⁰` cannot be defined here. CAUTION: a `WeilDual` is not unique; over an
algebraically closed `K` any `Â` with `Â[n] ≅ A[n]` for all `n` carries one. Hence leaves over
`WeilDual` must be *existential* (`∃ D : WeilDual A, …`, witnessed by `Pic⁰`); a leaf of the form
`∀ D : WeilDual A, …` need not be a consequence of the literature (see the report). -/
structure WeilDual (A : AbVar K) where
  /-- the dual abelian variety -/
  dual : AbVar K
  /-- the Weil pairings `e_n : A[n] × Â[n] → μ_n` -/
  e : ∀ n : ℕ, Pairing A dual n
  perfect : ∀ n : ℕ, 0 < n → (n : K) ≠ 0 → IsPerfect (e n)
  galois : ∀ n : ℕ, 0 < n → (n : K) ≠ 0 → IsGalEquivariant (e n)
  compat : ∀ m n : ℕ, 0 < m → 0 < n → ((m * n : ℕ) : K) ≠ 0 →
    ∀ (x : tors A (m * n)) (y : tors dual n),
      (e (m * n) x (torsIncl dual (dvd_mul_left n m) y)).val = (e n (torsSmul A m n x) y).val

/-- `g : B̂ → Â` is dual to `f : A → B`: `e_n(x, g y) = e_n(f x, y)` for all `n` invertible in `K`
(Mumford §20, (5); UNVERIFIED numbering). -/
def IsDualHom {A B : AbVar K} (DA : WeilDual A) (DB : WeilDual B) (f : Hom A B)
    (g : Hom DB.dual DA.dual) : Prop :=
  ∀ n : ℕ, 0 < n → (n : K) ≠ 0 → ∀ x y, DA.e n x (torsMap g n y) = DB.e n (torsMap f n x) y

/-- The dual morphism is unique on all torsion of order invertible in `K` (perfectness). -/
lemma IsDualHom.unique {A B : AbVar K} {DA : WeilDual A} {DB : WeilDual B} {f : Hom A B}
    {g g' : Hom DB.dual DA.dual} (hg : IsDualHom DA DB f g) (hg' : IsDualHom DA DB f g')
    {n : ℕ} (hn : 0 < n) (hnK : (n : K) ≠ 0) (y : tors DB.dual n) :
    torsMap g n y = torsMap g' n y := by
  have h := (DA.perfect n hn hnK).2 (torsMap g n y - torsMap g' n y) fun x => by
    rw [map_sub, hg n hn hnK, hg' n hn hnK, sub_self]
  exact sub_eq_zero.1 h

/-- Duals compose contravariantly: `(g ∘ f)^∨ = f^∨ ∘ g^∨`. -/
lemma IsDualHom.comp {A B C : AbVar K} {DA : WeilDual A} {DB : WeilDual B} {DC : WeilDual C}
    {f : Hom A B} {g : Hom B C} {fv : Hom DB.dual DA.dual} {gv : Hom DC.dual DB.dual}
    (hf : IsDualHom DA DB f fv) (hg : IsDualHom DB DC g gv) :
    IsDualHom DA DC (WeilPairing.comp f g) (WeilPairing.comp gv fv) := by
  intro n hn hnK x y
  rw [torsMap_comp, torsMap_comp, hf n hn hnK, hg n hn hnK]

/-- **The Weil pairing of `λ : A → Â`**: `e^λ_n(x, y) = e_n(x, λ y)` on `A[n]`
(Mumford §20, §23; UNVERIFIED numbering). -/
def weil {A : AbVar K} (D : WeilDual A) (lam : Hom A D.dual) (n : ℕ) : Pairing A A n :=
  pull (D.e n) (AddMonoidHom.id _) (homP lam)

@[simp] lemma weil_apply {A : AbVar K} (D : WeilDual A) (lam : Hom A D.dual) (n : ℕ) (x y) :
    weil D lam n x y = D.e n x (torsMap lam n y) := by
  simp only [weil, pull_apply]
  rfl

/-- `e^λ_n` is `G_K`-equivariant (`λ` is defined over `K`). -/
lemma weil_galois {A : AbVar K} (D : WeilDual A) (lam : Hom A D.dual) {n : ℕ} (hn : 0 < n)
    (hnK : (n : K) ≠ 0) : IsGalEquivariant (weil D lam n) :=
  (D.galois n hn hnK).pull (fun _ _ => rfl) (homP_galP lam)

/-- `λ` is symmetric: every `e^λ_n` (`n` invertible in `K`) is alternating. For `λ = φ_L` this
is Mumford §23 ("`e^L` is skew-symmetric, `e^L(x, x) = 1`"); conversely a homomorphism with
skew-symmetric `e^λ` is symmetric, `λ^∨ = λ` (Mumford §20, §23; UNVERIFIED numbering). -/
def IsSymmetric {A : AbVar K} (D : WeilDual A) (lam : Hom A D.dual) : Prop :=
  ∀ n : ℕ, 0 < n → (n : K) ≠ 0 → IsAlternating (weil D lam n)

/-- **A symmetric isogeny** `λ : A → Â` (a polarization without the positivity condition). -/
structure SymmIsogeny (A : AbVar K) where
  /-- the dual -/
  D : WeilDual A
  /-- the isogeny `λ : A → Â` -/
  lam : Hom A D.dual
  isogeny : IsIsogenyMor lam.hom
  symm : IsSymmetric D lam

/-- `ψ : Â → A` is a quasi-inverse of `λ` of exponent `d`: `λ ψ = [d]` on `Â(K̄)` and
`ψ λ = [d]` on `A(K̄)`. -/
def IsQuasiInverse {A B : AbVar K} (f : Hom A B) (g : Hom B A) (d : ℕ) : Prop :=
  (∀ z : P B, homP f (homP g z) = d • z) ∧ ∀ x : P A, homP g (homP f x) = d • x

/-- **Rosati positivity** of `λ`: for every nonzero `φ ∈ End(A)` with dual `φ^∨` and every
quasi-inverse `ψ` of `λ` of exponent `d ≥ 1` (so that `d·φ† = ψ φ^∨ λ`, `φ†` the Rosati
involution), the trace of `φ ∘ (d φ†)` on `T_ℓ A` is a positive integer, for every prime `ℓ`
invertible in `K` (Mumford §21, Thm 1: `Tr(φ φ†) > 0` for `φ ≠ 0`; Tr the trace of the
`2g`-dimensional `ℓ`-adic representation, Mumford §19; UNVERIFIED numbering). -/
def RosatiPositive {A : AbVar K} (S : SymmIsogeny A) : Prop :=
  ∀ (ℓ : ℕ) [Fact ℓ.Prime], (ℓ : K) ≠ 0 →
    ∀ (d : ℕ) (ψ : Hom S.D.dual A), 0 < d → IsQuasiInverse S.lam ψ d →
      ∀ (φ : End A) (φv : End S.D.dual), IsDualHom S.D S.D φ φv → φ ≠ 0 →
        ∃ t : ℕ, 0 < t ∧
          LinearMap.trace ℤ_[ℓ] (A.T ℓ)
            (homT (ℓ := ℓ) (WeilPairing.comp (WeilPairing.comp (WeilPairing.comp S.lam φv) ψ) φ))
            = (t : ℤ_[ℓ])

/-- **A polarization**: a symmetric isogeny with Rosati positivity. -/
structure Polarization (A : AbVar K) extends SymmIsogeny A where
  pos : RosatiPositive toSymmIsogeny

/-- **Principal**: `λ` is an isomorphism. -/
def SymmIsogeny.IsPrincipal {A : AbVar K} (S : SymmIsogeny A) : Prop :=
  ∃ g : Hom S.D.dual A, (WeilPairing.comp S.lam g).hom = 𝟙 _ ∧ (WeilPairing.comp g S.lam).hom = 𝟙 _

/-- **Nondegeneracy of `e^λ` up to `d`** (proved): if `λ ψ = [d]` on `Â(K̄)` and
`e^λ_n(x, y) = 1` for all `y ∈ A[n]`, then `d x = 0`. -/
lemma weil_nondeg {A : AbVar K} (D : WeilDual A) (lam : Hom A D.dual) {ψ : Hom D.dual A} {d : ℕ}
    (hψ : ∀ z : P D.dual, homP lam (homP ψ z) = d • z) {n : ℕ} (hn : 0 < n) (hnK : (n : K) ≠ 0)
    (x : tors A n) (hx : ∀ y, weil D lam n x y = 0) : d • x = 0 := by
  apply (D.perfect n hn hnK).1
  intro z
  have hz : torsMap lam n (torsMap ψ n z) = d • z := Subtype.ext (hψ z)
  rw [nsmul_left, ← nsmul_right, ← hz, ← weil_apply, hx]

/-- With a principal `λ`, `e^λ_n` is perfect. -/
lemma weil_perfect_of_principal {A : AbVar K} (S : SymmIsogeny A) (hS : S.IsPrincipal) {n : ℕ}
    (hn : 0 < n) (hnK : (n : K) ≠ 0) : IsPerfect (weil S.D S.lam n) := by
  obtain ⟨g, h1, h2⟩ := hS
  have hP : ∀ z : P S.D.dual, homP S.lam (homP g z) = (1 : ℕ) • z := fun z => by
    rw [one_smul, ← homP_comp]
    change Additive.ofMul (Additive.toMul z ≫ (WeilPairing.comp g S.lam).hom) = z
    rw [h2, Category.comp_id]; rfl
  refine ⟨fun x hx => by simpa using weil_nondeg S.D S.lam hP hn hnK x hx, fun y hy => ?_⟩
  -- skew-symmetry turns the right kernel into the left kernel
  have hy' : ∀ x, weil S.D S.lam n y x = 0 := fun x => by
    rw [(S.symm n hn hnK).skew, hy x, neg_zero]
  simpa using weil_nondeg S.D S.lam hP hn hnK y hy'

/-- **Pull-back of a symmetric `λ_B` along `f : A → B`** (compatibility with isogenies, proved):
if `f^∨` is dual to `f` then `f^∨ λ_B f : A → Â` is symmetric. -/
lemma isSymmetric_pullback {A B : AbVar K} {DA : WeilDual A} {DB : WeilDual B} {f : Hom A B}
    {fv : Hom DB.dual DA.dual} (hf : IsDualHom DA DB f fv) {lamB : Hom B DB.dual}
    (hB : IsSymmetric DB lamB) :
    IsSymmetric DA (WeilPairing.comp (WeilPairing.comp f lamB) fv) := by
  intro n hn hnK x
  rw [weil_apply, torsMap_comp, hf n hn hnK, torsMap_comp, ← weil_apply]
  exact hB n hn hnK _

/-- The Weil pairing of the pulled-back `λ` is the pull-back of the Weil pairing:
`e^{f^∨ λ f}_n(x, y) = e^λ_n(f x, f y)`. -/
lemma weil_pullback {A B : AbVar K} {DA : WeilDual A} {DB : WeilDual B} {f : Hom A B}
    {fv : Hom DB.dual DA.dual} (hf : IsDualHom DA DB f fv) (lamB : Hom B DB.dual) {n : ℕ}
    (hn : 0 < n) (hnK : (n : K) ≠ 0) (x y : tors A n) :
    weil DA (WeilPairing.comp (WeilPairing.comp f lamB) fv) n x y =
      weil DB lamB n (torsMap f n x) (torsMap f n y) := by
  rw [weil_apply, torsMap_comp, hf n hn hnK, torsMap_comp, ← weil_apply]

/-! ## §4. Leaves (`def … : Prop`) and the restated T9 -/

/-- **T9 (restated over the definitions of §3).** Every abelian variety over a field carries a
symmetric isogeny `λ : A → Â` to its dual, with Galois-equivariant perfect compatible Weil
pairings. Published: Mumford §6 (Application 1: `A` is projective, so an ample `L` exists over
`K`), §8 (`Â`), §13, §20 (the pairing `e_n`: bilinear, perfect, Galois-equivariant,
`e_{mn}(x, y) = e_n(m x, y)`), §23 (`e^L_n(x, x) = 1`, so `λ = φ_L` is symmetric), and `φ_L` is an
isogeny for ample `L` (§6, Application 1); Milne, *Abelian varieties* (Cornell–Silverman 1986)
§§8-13, 16 (UNVERIFIED numbering). Take `D = (Pic⁰, e_n)`, `λ = φ_L`. Existential in `D`, hence a
consequence, never stronger. -/
def T09_SymmIsogenyExists : Prop :=
  ∀ (K : Type) [Field K] (A : AbVar K), Nonempty (SymmIsogeny A)

/-- **T9⁺ (polarization).** Every abelian variety over a field has a polarization in the sense of
§3 (`λ = φ_L`, `L` ample over `K`; Rosati positivity is Mumford §21, Thm 1; UNVERIFIED
numbering). Not needed by G12 (which uses only T9). -/
def T09plus_PolarizationExists : Prop :=
  ∀ (K : Type) [Field K] (A : AbVar K), Nonempty (Polarization A)

/-- **Quasi-inverse of an isogeny.** For an isogeny `f : A → B` (finite and surjective) there are
`d ≥ 1` and `g : B → A` with `f g = [d]`, `g f = [d]` (take `d = deg f`, which kills `ker f`;
Mumford §7, Remark after Thm 4, and §8 Thm 1 (UNVERIFIED numbering); Milne 1986, Prop. 7.1 /
Rem. 8.4 (UNVERIFIED)). Stated on `K̄`-points, a consequence. -/
def IsogenyQuasiInverse : Prop :=
  ∀ (K : Type) [Field K] (A B : AbVar K) (f : Hom A B), IsIsogenyMor f.hom →
    ∃ d : ℕ, 0 < d ∧ ∃ g : Hom B A, IsQuasiInverse f g d

/-! ### Non-vacuity: the definitions are satisfiable (at `A = 0`) -/

lemma pt_zero_subsingleton (x y : (AbVar.zero K).Pt (AlgebraicClosure K)) : x = y :=
  CartesianMonoidalCategory.toUnit_unique x y

lemma tors_zero_eq (n : ℕ) (x : tors (AbVar.zero K) n) : x = 0 :=
  Subtype.ext (Additive.toMul.injective (pt_zero_subsingleton _ _))

/-- The zero abelian variety has a `WeilDual` (itself, zero pairings). -/
def weilDualZero (K : Type) [Field K] : WeilDual (AbVar.zero K) where
  dual := AbVar.zero K
  e _ := 0
  perfect _ _ _ := isPerfect_zero_iff.2 ⟨tors_zero_eq _, tors_zero_eq _⟩
  galois _ _ _ σ x y := by simp
  compat _ _ _ _ _ _ _ := rfl

lemma isIsogenyMor_id (X : Over (Spec (CommRingCat.of K))) : IsIsogenyMor (𝟙 X) := by
  unfold IsIsogenyMor
  rw [Over.id_left]
  exact ⟨inferInstance, inferInstance⟩

/-- `T09_SymmIsogenyExists` holds at `A = 0`: the hypotheses are consistent. -/
theorem symmIsogeny_zero (K : Type) [Field K] : Nonempty (SymmIsogeny (AbVar.zero K)) :=
  ⟨{ D := weilDualZero K, lam := (1 : End (AbVar.zero K)), isogeny := isIsogenyMor_id _,
     symm := fun _ _ _ _ => rfl }⟩

/-! ## §5. The old consequence-form T9 (`LeafPush.T09_WeilPairing`), derived -/

namespace OldT9

universe u

open PkgI2

/-- Copied verbatim from `scratch/h-decomposition/Leaves.lean` (`LeafPush.T09_WeilPairing`, from
leaf-push), with `Type u` replaced by `Type` (the build uses universe `0`). -/
def T09_WeilPairing : Prop :=
  ∀ (K : Type) [Field K] (A : Grp (Over (Spec (.of K)))) [IsAbelianVariety A],
    ∃ d : ℕ, 0 < d ∧ ∃ e : ℕ → Pts A (AlgebraicClosure K) → Pts A (AlgebraicClosure K) →
        AlgebraicClosure K,
      ∀ n : ℕ, 0 < n → (n : K) ≠ 0 →
        (∀ x ∈ torsion A (AlgebraicClosure K) n, ∀ y ∈ torsion A (AlgebraicClosure K) n,
          e n x y ^ n = 1) ∧
        (∀ x ∈ torsion A (AlgebraicClosure K) n, ∀ x' ∈ torsion A (AlgebraicClosure K) n,
          ∀ y ∈ torsion A (AlgebraicClosure K) n,
            e n (x * x') y = e n x y * e n x' y ∧ e n y (x * x') = e n y x * e n y x') ∧
        (∀ x ∈ torsion A (AlgebraicClosure K) n, e n x x = 1) ∧
        (∀ x ∈ torsion A (AlgebraicClosure K) n,
          (∀ y ∈ torsion A (AlgebraicClosure K) n, e n x y = 1) → x ^ d = 1) ∧
        (∀ σ : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K,
          ∀ x ∈ torsion A (AlgebraicClosure K) n, ∀ y ∈ torsion A (AlgebraicClosure K) n,
            e n (galAct A σ x) (galAct A σ y) = σ (e n x y)) ∧
        (∀ m : ℕ, 0 < m → (m : K) ≠ 0 →
          ∀ x ∈ torsion A (AlgebraicClosure K) (m * n),
          ∀ y ∈ torsion A (AlgebraicClosure K) (m * n),
            e n (x ^ m) (y ^ m) = e (m * n) x y ^ m)

end OldT9

section Old

variable (A : Grp (Over (Spec (.of K)))) [PkgI2.IsAbelianVariety A]

/-- A torsion point of `A` (I2's multiplicative points) as an element of `tors (ofGrp A) n`. -/
def toT {n : ℕ} {x : PkgI2.Pts A (AlgebraicClosure K)} (hx : x ^ n = 1) :
    tors (ObjBridge.ofGrp A) n :=
  ⟨Additive.ofMul x, by rw [mem_tors]; change Additive.ofMul (x ^ n) = 0; rw [hx]; rfl⟩

open Classical in
/-- The old leaf's `e`, read off `e^λ`. -/
def oldE (S : SymmIsogeny (ObjBridge.ofGrp A)) (n : ℕ) (x y : PkgI2.Pts A (AlgebraicClosure K)) :
    AlgebraicClosure K :=
  if h : x ^ n = 1 ∧ y ^ n = 1 then ((weil S.D S.lam n (toT A h.1) (toT A h.2)).val : _) else 1

lemma oldE_eq (S : SymmIsogeny (ObjBridge.ofGrp A)) {n : ℕ} {x y : PkgI2.Pts A (AlgebraicClosure K)}
    (hx : x ^ n = 1) (hy : y ^ n = 1) :
    oldE A S n x y = ((weil S.D S.lam n (toT A hx) (toT A hy)).val : _) := by
  classical
  exact dite_eq_left_of_eq_true (eq_true ⟨hx, hy⟩)

end Old

/-- **The new T9 implies the old one.** `T09_SymmIsogenyExists` (over the definitions of §3)
together with `IsogenyQuasiInverse` implies the consequence-form leaf
`LeafPush.T09_WeilPairing` used by `scratch/h-decomposition/Leaves.lean` (`HSyn` bundle field
`t9`). So the old leaf can be replaced by the two leaves of §4. -/
theorem oldT9_of_symmIsogeny (h9 : T09_SymmIsogenyExists) (hQ : IsogenyQuasiInverse) :
    OldT9.T09_WeilPairing := by
  intro K _ A _
  obtain ⟨S⟩ := h9 K (ObjBridge.ofGrp A)
  obtain ⟨d, hd, ψ, hψ, -⟩ := hQ K _ _ S.lam S.isogeny
  refine ⟨d, hd, oldE A S, fun n hn hnK => ⟨?_, ?_, ?_, ?_, ?_, ?_⟩⟩
  · -- values in `μ_n`
    intro x hx y hy
    rw [oldE_eq A S hx hy, ← Units.val_pow_eq_pow_val, val_pow_eq_one, Units.val_one]
  · -- bimultiplicative
    intro x hx x' hx' y hy
    have hxx' : (x * x') ^ n = 1 := by
      change x ^ n = 1 at hx
      change x' ^ n = 1 at hx'
      rw [mul_pow, hx, hx', one_mul]
    have e1 : toT A hxx' = toT A hx + toT A hx' := rfl
    refine ⟨?_, ?_⟩
    · rw [oldE_eq A S hxx' hy, oldE_eq A S hx hy, oldE_eq A S hx' hy, e1, val_mul_left,
        Units.val_mul]
    · rw [oldE_eq A S hy hxx', oldE_eq A S hy hx, oldE_eq A S hy hx', e1, val_mul_right,
        Units.val_mul]
  · -- alternating
    intro x hx
    rw [oldE_eq A S hx hx, S.symm n hn hnK, Mu.val_zero, Units.val_one]
  · -- nondegenerate up to `d`
    intro x hx H
    have h0 : ∀ t : tors (ObjBridge.ofGrp A) n, weil S.D S.lam n (toT A hx) t = 0 := by
      intro t
      have ht : (Additive.toMul (t : P (ObjBridge.ofGrp A))) ^ n = 1 :=
        Additive.ofMul.injective (nsmul_tors t)
      have h1 := H _ ht
      rw [oldE_eq A S hx ht] at h1
      have h2 : toT A ht = t := rfl
      rw [h2] at h1
      exact Mu.val_injective (Units.val_eq_one.1 h1)
    have h3 := weil_nondeg S.D S.lam hψ hn hnK (toT A hx) h0
    exact Additive.ofMul.injective (congrArg Subtype.val h3)
  · -- Galois-equivariant
    intro σ x hx y hy
    have hσx : (PkgI2.galAct A σ x) ^ n = 1 := by
      change x ^ n = 1 at hx
      rw [← PkgI2.galAct_pow, hx]
      exact MonObj.comp_one _
    have hσy : (PkgI2.galAct A σ y) ^ n = 1 := by
      change y ^ n = 1 at hy
      rw [← PkgI2.galAct_pow, hy]
      exact MonObj.comp_one _
    have ex : toT A hσx = galTors _ n σ (toT A hx) := rfl
    have ey : toT A hσy = galTors _ n σ (toT A hy) := rfl
    rw [oldE_eq A S hσx hσy, oldE_eq A S hx hy, ex, ey, weil_galois S.D S.lam hn hnK, galMu_val]
  · -- compatibility
    intro m hm hmK x hx y hy
    have hmn : 0 < m * n := Nat.mul_pos hm hn
    have hmnK : ((m * n : ℕ) : K) ≠ 0 := by rw [Nat.cast_mul]; exact mul_ne_zero hmK hnK
    change x ^ (m * n) = 1 at hx
    change y ^ (m * n) = 1 at hy
    have hxm : (x ^ m) ^ n = 1 := by rw [← pow_mul, hx]
    have hym : (y ^ m) ^ n = 1 := by rw [← pow_mul, hy]
    have ex : toT A hxm = torsSmul _ m n (toT A hx) := rfl
    have ey : torsIncl _ (dvd_mul_left n m) (torsMap S.lam n (toT A hym)) =
        m • torsMap S.lam (m * n) (toT A hy) := by
      apply Subtype.ext
      change homP S.lam (Additive.ofMul (y ^ m)) = m • homP S.lam (Additive.ofMul y)
      rw [← map_nsmul]
      rfl
    rw [oldE_eq A S hxm hym, oldE_eq A S hx hy, weil_apply, ex,
      ← S.D.compat m n hm hn hmnK, ey, nsmul_right, Mu.val_nsmul, ← weil_apply,
      Units.val_pow_eq_pow_val]

/-! ## §6. The G12 input: the multiplier is cyclotomic; `det² = χ^{rank}` -/

/-- `G_K` acts on `μ_n` through the mod-`n` cyclotomic character (Mathlib's
`modularCyclotomicCharacter'`). -/
lemma galMu_eq_nsmul (n : ℕ) [NeZero n] (σ : Gal K) (z : Mu K n) :
    galMu n σ z =
      (Units.val (modularCyclotomicCharacter' (AlgebraicClosure K) n σ.toRingEquiv)).val • z := by
  apply Mu.val_injective
  apply Units.ext
  rw [galMu_val, Mu.val_nsmul, Units.val_pow_eq_pow_val]
  have := modularCyclotomicCharacter'.spec' (AlgebraicClosure K) n σ.toRingEquiv
    (Additive.toMul z).2
  exact this

/-- **Finite-level G12 input (proved).** For `n` invertible in `K`, `e^λ_n` has cyclotomic
multiplier: `e^λ_n(σx, σy) = χ_n(σ) · e^λ_n(x, y)` (additively), `χ_n` the mod-`n` cyclotomic
character. Hence `G_K` acts on `A[n]` through `GSp(e^λ_n)` with multiplier `χ_n`. -/
theorem weil_cyclotomic {A : AbVar K} (D : WeilDual A) (lam : Hom A D.dual) {n : ℕ} [NeZero n]
    (hnK : (n : K) ≠ 0) (σ : Gal K) (x y : tors A n) :
    weil D lam n (galTors A n σ x) (galTors A n σ y) =
      (Units.val (modularCyclotomicCharacter' (AlgebraicClosure K) n σ.toRingEquiv)).val •
        weil D lam n x y := by
  rw [weil_galois D lam (Nat.pos_of_ne_zero (NeZero.ne n)) hnK, galMu_eq_nsmul]

/-- **The determinant identity (proved, linear algebra).** Let `B` be a bilinear form on a free
module with basis `b` over a commutative ring, with Gram determinant a unit (a perfect
pairing), and `f` a similitude with multiplier `c`: `B(f x, f y) = c B(x, y)`. Then
`det(f)² = c^{rank}`. For `M = V_ℓ(A)`, `B` the `ℓ`-adic Weil pairing of `λ` (perfect on
`V_ℓ`) and `f = ρ_ℓ(σ)`, `c = χ_ℓ(σ)`: `det ρ_ℓ(σ)² = χ_ℓ(σ)^{2g}`, the input
`(det r₅)⁴ = χ⁴` on `G_F` (for `g = 2`) of C8's determinant argument. -/
theorem det_sq_of_similitude {R M idx : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    [Fintype idx] [DecidableEq idx] (b : Module.Basis idx R M) (B : LinearMap.BilinForm R M)
    (hB : IsUnit (LinearMap.BilinForm.toMatrix b B).det) (f : M →ₗ[R] M) (c : R)
    (hf : ∀ x y, B (f x) (f y) = c * B x y) :
    LinearMap.det f ^ 2 = c ^ Fintype.card idx := by
  have hc : B.comp f f = c • B := by
    ext x y
    simp [hf]
  have h1 := LinearMap.BilinForm.toMatrix_comp b b B f f
  rw [hc, map_smul] at h1
  have h2 := congrArg Matrix.det h1
  rw [Matrix.det_smul, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose,
    LinearMap.det_toMatrix] at h2
  exact hB.mul_left_cancel (by linear_combination -h2)

/-- Over a field: a nondegenerate `B` with multiplier `c` for `f` gives `det(f)² = c^{dim}`. -/
theorem det_sq_of_similitude_field {F M : Type*} [Field F] [AddCommGroup M] [Module F M]
    [FiniteDimensional F M] (B : LinearMap.BilinForm F M) (hB : B.Nondegenerate)
    (f : M →ₗ[F] M) (c : F) (hf : ∀ x y, B (f x) (f y) = c * B x y) :
    LinearMap.det f ^ 2 = c ^ Module.finrank F M := by
  classical
  let b := Module.finBasis F M
  have hdet := (LinearMap.BilinForm.nondegenerate_iff_det_ne_zero b).1 hB
  rw [det_sq_of_similitude b B (Ne.isUnit hdet) f c hf, Fintype.card_fin]

/-- **The determinant argument with `det²` (proved).** C8's group-theoretic step from
`(det r)⁴ = χ⁴` on a finite-index subgroup (what `det_sq_of_similitude` gives for `g = 2` and
`V ⊗ E ≅ r ⊕ r`), instead of `GlueAssembly.twist_finite`'s `(det r)² = χ²` (which needs
`det = χ^g`, i.e. the Pfaffian). -/
theorem twist_finite_four {G E : Type*} [Group G] [Field E] (H : Subgroup G) [H.FiniteIndex]
    (r ε χ ψ : G →* Eˣ) (hdet : ∀ g, r g = ε g * χ g * ψ g ^ 2)
    (hH : ∀ h ∈ H, r h ^ 4 = χ h ^ 4) (hε : (Set.range ε).Finite) : (Set.range ψ).Finite := by
  classical
  let α : G →* Eˣ := r * χ⁻¹
  have hαH : (α '' H).Finite := by
    refine Set.Finite.subset ((Polynomial.nthRoots 4 (1 : E)).toFinset.finite_toSet.preimage
      Units.val_injective.injOn) ?_
    rintro _ ⟨h, hh, rfl⟩
    simp only [Set.mem_preimage, Finset.mem_coe, Multiset.mem_toFinset]
    rw [Polynomial.mem_nthRoots (by norm_num)]
    have e : (α h) ^ 4 = 1 := by
      simp only [α, MonoidHom.mul_apply, MonoidHom.inv_apply, mul_pow, inv_pow, hH h hh,
        mul_inv_cancel]
    have := congrArg Units.val e
    simpa using this
  have hα := GlueAssembly.finite_range_of_finiteIndex α H hαH
  have hsq : (Set.range fun g => ψ g ^ 2) ⊆ (fun p : Eˣ × Eˣ => p.1 * p.2⁻¹) '' (Set.range α ×ˢ
      Set.range ε) := by
    rintro _ ⟨g, rfl⟩
    refine ⟨(α g, ε g), ⟨⟨g, rfl⟩, ⟨g, rfl⟩⟩, ?_⟩
    simp only [α, MonoidHom.mul_apply, MonoidHom.inv_apply, hdet]
    apply Units.ext
    simp only [Units.val_mul, Units.val_inv_eq_inv_val, Units.val_pow_eq_pow_val]
    have h1 := (ε g).ne_zero
    have h2 := (χ g).ne_zero
    field_simp
  exact GlueAssembly.finite_range_of_sq ψ (((hα.prod hε).image _).subset hsq)


/-! ## §7. The `ℓ`-adic Weil pairing on `T_ℓ A`, with cyclotomic multiplier -/

section Adic

variable {A : AbVar K} (D : WeilDual A) (lam : Hom A D.dual)

open Classical in
/-- `e^λ_n` on all of `A(K̄)`, as a unit of `K̄` (junk value `1` off `A[n]`); a non-dependent
form used to pass to the limit. -/
def wv (n : ℕ) (x y : P A) : (AlgebraicClosure K)ˣ :=
  if h : n • x = 0 ∧ n • y = 0 then (weil D lam n ⟨x, h.1⟩ ⟨y, h.2⟩).val else 1

variable {D lam}

lemma wv_eq {n : ℕ} {x y : P A} (hx : n • x = 0) (hy : n • y = 0) :
    wv D lam n x y = (weil D lam n ⟨x, hx⟩ ⟨y, hy⟩).val := by
  classical
  exact dite_eq_left_of_eq_true (eq_true ⟨hx, hy⟩)

lemma wv_pow (n : ℕ) (x y : P A) : wv D lam n x y ^ n = 1 := by
  classical
  unfold wv
  split_ifs
  · exact val_pow_eq_one _ _ _
  · exact one_pow n

lemma wv_one (x y : P A) : wv D lam 1 x y = 1 := by
  simpa using wv_pow (D := D) (lam := lam) 1 x y

lemma wv_add_left {n : ℕ} {x x' y : P A} (hx : n • x = 0) (hx' : n • x' = 0) (hy : n • y = 0) :
    wv D lam n (x + x') y = wv D lam n x y * wv D lam n x' y := by
  have hxx' : n • (x + x') = 0 := by rw [smul_add, hx, hx', add_zero]
  rw [wv_eq hxx' hy, wv_eq hx hy, wv_eq hx' hy]
  exact val_mul_left _ ⟨x, hx⟩ ⟨x', hx'⟩ _

lemma wv_add_right {n : ℕ} {x y y' : P A} (hx : n • x = 0) (hy : n • y = 0) (hy' : n • y' = 0) :
    wv D lam n x (y + y') = wv D lam n x y * wv D lam n x y' := by
  have hyy' : n • (y + y') = 0 := by rw [smul_add, hy, hy', add_zero]
  rw [wv_eq hx hyy', wv_eq hx hy, wv_eq hx hy']
  exact val_mul_right _ _ ⟨y, hy⟩ ⟨y', hy'⟩

lemma wv_nsmul_left {n : ℕ} (c : ℕ) {x y : P A} (hx : n • x = 0) (hy : n • y = 0) :
    wv D lam n (c • x) y = wv D lam n x y ^ c := by
  have hcx : n • (c • x) = 0 := by rw [smul_comm, hx, smul_zero]
  rw [wv_eq hcx hy, wv_eq hx hy, ← Mu.val_nsmul, ← nsmul_left]
  rfl

lemma wv_nsmul_right {n : ℕ} (c : ℕ) {x y : P A} (hx : n • x = 0) (hy : n • y = 0) :
    wv D lam n x (c • y) = wv D lam n x y ^ c := by
  have hcy : n • (c • y) = 0 := by rw [smul_comm, hy, smul_zero]
  rw [wv_eq hx hcy, wv_eq hx hy, ← Mu.val_nsmul, ← nsmul_right]
  rfl

/-- Compatibility: `e^λ_n(m x, m y) = e^λ_{mn}(x, y)^m`. -/
lemma wv_compat {m n : ℕ} (hm : 0 < m) (hn : 0 < n) (hK : ((m * n : ℕ) : K) ≠ 0) {x y : P A}
    (hx : (m * n) • x = 0) (hy : (m * n) • y = 0) :
    wv D lam n (m • x) (m • y) = wv D lam (m * n) x y ^ m := by
  have hmx : n • (m • x) = 0 := by rw [← mul_smul, mul_comm, hx]
  have hmy : n • (m • y) = 0 := by rw [← mul_smul, mul_comm, hy]
  have ex : (⟨m • x, hmx⟩ : tors A n) = torsSmul A m n ⟨x, hx⟩ := rfl
  have ey : torsIncl _ (dvd_mul_left n m) (torsMap lam n ⟨m • y, hmy⟩) =
      m • torsMap lam (m * n) ⟨y, hy⟩ := by
    apply Subtype.ext
    change homP lam (m • y) = m • homP lam y
    rw [map_nsmul]
  rw [wv_eq hmx hmy, wv_eq hx hy, weil_apply, ex, ← D.compat m n hm hn hK, ey, nsmul_right,
    Mu.val_nsmul, ← weil_apply]

/-- `G_K`-equivariance: `e^λ_n(σx, σy) = σ(e^λ_n(x, y))`. -/
lemma wv_galois {n : ℕ} (hn : 0 < n) (hnK : (n : K) ≠ 0) (σ : Gal K) {x y : P A}
    (hx : n • x = 0) (hy : n • y = 0) :
    wv D lam n (galP A σ x) (galP A σ y) =
      Units.map (σ : AlgebraicClosure K →* AlgebraicClosure K) (wv D lam n x y) := by
  have hσx : n • galP A σ x = 0 := by rw [← map_nsmul, hx, map_zero]
  have hσy : n • galP A σ y = 0 := by rw [← map_nsmul, hy, map_zero]
  have ex : (⟨galP A σ x, hσx⟩ : tors A n) = galTors A n σ ⟨x, hx⟩ := rfl
  have ey : (⟨galP A σ y, hσy⟩ : tors A n) = galTors A n σ ⟨y, hy⟩ := rfl
  rw [wv_eq hσx hσy, wv_eq hx hy, ex, ey, weil_galois D lam hn hnK]
  rfl

variable (D lam)
variable (ℓ : ℕ) [Fact ℓ.Prime]

/-- `T_ℓ(μ) = lim μ_{ℓᵏ}(K̄)`, as Objects' `Tate.T` of `K̄ˣ`. -/
abbrev TMu (K : Type) [Field K] (ℓ : ℕ) [Fact ℓ.Prime] : Type :=
  Tate.T ℓ (Additive (AlgebraicClosure K)ˣ)

/-- `G_K` acting on `T_ℓ(μ)`. -/
def galTMu (σ : Gal K) : TMu K ℓ →ₗ[ℤ_[ℓ]] TMu K ℓ :=
  Tate.map (MonoidHom.toAdditive (Units.map (σ : AlgebraicClosure K →* AlgebraicClosure K)))

omit [Fact ℓ.Prime] in
lemma tors_pow {x : A.T ℓ} (k : ℕ) : (ℓ ^ k) • x.1 k = 0 := Tate.pow_smul_eq_zero x.2 k

/-- The components `e^λ_{ℓᵏ}(x_k, y_k)`. -/
def tateSeq (x y : A.T ℓ) : ℕ → Additive (AlgebraicClosure K)ˣ :=
  fun k => Additive.ofMul (wv D lam (ℓ ^ k) (x.1 k) (y.1 k))

variable {ℓ}

lemma tateSeq_mem (hℓ : (ℓ : K) ≠ 0) (x y : A.T ℓ) : tateSeq D lam ℓ x y ∈ Tate.T ℓ _ := by
  refine ⟨?_, fun k => ?_⟩
  · change Additive.ofMul (wv D lam (ℓ ^ 0) _ _) = 0
    rw [pow_zero, wv_one]
    rfl
  · change Additive.ofMul (wv D lam (ℓ ^ (k + 1)) (x.1 (k + 1)) (y.1 (k + 1)) ^ ℓ) =
      Additive.ofMul (wv D lam (ℓ ^ k) (x.1 k) (y.1 k))
    congr 1
    have hl : 0 < ℓ := (Fact.out : ℓ.Prime).pos
    have hK : ((ℓ * ℓ ^ k : ℕ) : K) ≠ 0 := by
      rw [Nat.cast_mul, Nat.cast_pow]; exact mul_ne_zero hℓ (pow_ne_zero _ hℓ)
    have hx : (ℓ * ℓ ^ k) • x.1 (k + 1) = 0 := by rw [← pow_succ']; exact tors_pow ℓ (k + 1)
    have hy : (ℓ * ℓ ^ k) • y.1 (k + 1) = 0 := by rw [← pow_succ']; exact tors_pow ℓ (k + 1)
    rw [← x.2.2 k, ← y.2.2 k, wv_compat hl (pow_pos hl k) hK hx hy, pow_succ']

/-- **The `ℓ`-adic Weil pairing** `E^λ : T_ℓ A × T_ℓ A → T_ℓ(μ)`, `ℤ_ℓ`-bilinear, with
components `e^λ_{ℓᵏ}(x_k, y_k)`. -/
def tatePairing (hℓ : (ℓ : K) ≠ 0) : A.T ℓ →ₗ[ℤ_[ℓ]] A.T ℓ →ₗ[ℤ_[ℓ]] TMu K ℓ :=
  LinearMap.mk₂ ℤ_[ℓ] (fun x y => ⟨tateSeq D lam ℓ x y, tateSeq_mem D lam hℓ x y⟩)
    (fun x x' y => Subtype.ext <| funext fun k => by
      change Additive.ofMul (wv D lam (ℓ ^ k) (x.1 k + x'.1 k) (y.1 k)) =
        Additive.ofMul (wv D lam (ℓ ^ k) (x.1 k) (y.1 k) * wv D lam (ℓ ^ k) (x'.1 k) (y.1 k))
      rw [wv_add_left (tors_pow ℓ k) (tors_pow ℓ k) (tors_pow ℓ k)])
    (fun a x y => Subtype.ext <| funext fun k => by
      change Additive.ofMul (wv D lam (ℓ ^ k) ((PadicInt.toZModPow k a).val • x.1 k) (y.1 k)) =
        Additive.ofMul (wv D lam (ℓ ^ k) (x.1 k) (y.1 k) ^ (PadicInt.toZModPow k a).val)
      rw [wv_nsmul_left _ (tors_pow ℓ k) (tors_pow ℓ k)])
    (fun x y y' => Subtype.ext <| funext fun k => by
      change Additive.ofMul (wv D lam (ℓ ^ k) (x.1 k) (y.1 k + y'.1 k)) =
        Additive.ofMul (wv D lam (ℓ ^ k) (x.1 k) (y.1 k) * wv D lam (ℓ ^ k) (x.1 k) (y'.1 k))
      rw [wv_add_right (tors_pow ℓ k) (tors_pow ℓ k) (tors_pow ℓ k)])
    (fun a x y => Subtype.ext <| funext fun k => by
      change Additive.ofMul (wv D lam (ℓ ^ k) (x.1 k) ((PadicInt.toZModPow k a).val • y.1 k)) =
        Additive.ofMul (wv D lam (ℓ ^ k) (x.1 k) (y.1 k) ^ (PadicInt.toZModPow k a).val)
      rw [wv_nsmul_right _ (tors_pow ℓ k) (tors_pow ℓ k)])

lemma tatePairing_apply (hℓ : (ℓ : K) ≠ 0) (x y : A.T ℓ) (k : ℕ) :
    (tatePairing D lam hℓ x y).1 k = Additive.ofMul (wv D lam (ℓ ^ k) (x.1 k) (y.1 k)) := rfl

/-- `E^λ` is alternating when `λ` is symmetric. -/
theorem tatePairing_self (hS : IsSymmetric D lam) (hℓ : (ℓ : K) ≠ 0) (x : A.T ℓ) :
    tatePairing D lam hℓ x x = 0 := by
  have hl : 0 < ℓ := (Fact.out : ℓ.Prime).pos
  apply Subtype.ext; funext k
  rw [tatePairing_apply, wv_eq (tors_pow ℓ k) (tors_pow ℓ k),
    hS (ℓ ^ k) (pow_pos hl k) (by rw [Nat.cast_pow]; exact pow_ne_zero _ hℓ)]
  rfl

/-- `E^λ` is `G_K`-equivariant: `E^λ(σx, σy) = σ E^λ(x, y)`. -/
theorem tatePairing_galois (hℓ : (ℓ : K) ≠ 0) (σ : Gal K) (x y : A.T ℓ) :
    tatePairing D lam hℓ (A.galT σ x) (A.galT σ y) = galTMu ℓ σ (tatePairing D lam hℓ x y) := by
  have hl : 0 < ℓ := (Fact.out : ℓ.Prime).pos
  apply Subtype.ext; funext k
  change Additive.ofMul (wv D lam (ℓ ^ k) (galP A σ (x.1 k)) (galP A σ (y.1 k))) =
    Additive.ofMul (Units.map (σ : AlgebraicClosure K →* AlgebraicClosure K)
      (wv D lam (ℓ ^ k) (x.1 k) (y.1 k)))
  rw [wv_galois (pow_pos hl k) (by rw [Nat.cast_pow]; exact pow_ne_zero _ hℓ) σ (tors_pow ℓ k)
    (tors_pow ℓ k)]

/-- `G_K` acts on `T_ℓ(μ)` through the `ℓ`-adic cyclotomic character (Mathlib's
`cyclotomicCharacter`). -/
theorem galTMu_eq_cyclotomic [NeZero (ℓ : K)] (σ : Gal K) (z : TMu K ℓ) :
    galTMu ℓ σ z = ((cyclotomicCharacter (AlgebraicClosure K) ℓ σ.toRingEquiv : ℤ_[ℓ]ˣ) : ℤ_[ℓ]) • z := by
  apply Subtype.ext; funext k
  have hz : ((Additive.toMul (z.1 k) : (AlgebraicClosure K)ˣ) : AlgebraicClosure K) ^ ℓ ^ k = 1 := by
    have h := Tate.pow_smul_eq_zero z.2 k
    have h' : (Additive.toMul (z.1 k)) ^ ℓ ^ k = 1 := Additive.ofMul.injective h
    rw [← Units.val_pow_eq_pow_val, h', Units.val_one]
  have := cyclotomicCharacter.spec ℓ (n := k) σ.toRingEquiv _ hz
  change Additive.ofMul (Units.map (σ : AlgebraicClosure K →* AlgebraicClosure K)
      (Additive.toMul (z.1 k))) = Additive.ofMul ((Additive.toMul (z.1 k)) ^ _)
  congr 1
  apply Units.ext
  rw [Units.coe_map, Units.val_pow_eq_pow_val]
  exact this

/-- **The `ℓ`-adic G12 input (proved):** `E^λ(σx, σy) = χ_ℓ(σ) · E^λ(x, y)`, i.e. `G_K` acts on
`T_ℓ A` through `GSp(E^λ)` with the cyclotomic multiplier (C8 item 1). -/
theorem tatePairing_cyclotomic [NeZero (ℓ : K)] (σ : Gal K) (x y : A.T ℓ) :
    tatePairing D lam (NeZero.ne _) (A.galT σ x) (A.galT σ y) =
      ((cyclotomicCharacter (AlgebraicClosure K) ℓ σ.toRingEquiv : ℤ_[ℓ]ˣ) : ℤ_[ℓ]) •
        tatePairing D lam (NeZero.ne _) x y := by
  rw [tatePairing_galois, galTMu_eq_cyclotomic]

end Adic


/-! ## §8. Nondegeneracy of `E^λ` and `det ρ_ℓ(σ)² = χ_ℓ(σ)^{2g}` -/

section Det

/-- Iterating `ℓ • u(i+1) = u i`. -/
lemma iterate_smul {M : Type*} [AddCommGroup M] {ℓ : ℕ} {u : ℕ → M}
    (hu : ∀ i, ℓ • u (i + 1) = u i) (k a : ℕ) : ℓ ^ a • u (k + a) = u k := by
  induction a with
  | zero => simp
  | succ a ih => rw [pow_succ, mul_smul, ← Nat.add_assoc, hu, ih]

/-- If `a • x = 0` and `b • x = 0` with `a, b` coprime then `x = 0`. -/
lemma eq_zero_of_coprime {M : Type*} [AddCommGroup M] {x : M} {a b : ℕ} (hab : a.Coprime b)
    (ha : a • x = 0) (hb : b • x = 0) : x = 0 := by
  have h1 := addOrderOf_dvd_of_nsmul_eq_zero ha
  have h2 := addOrderOf_dvd_of_nsmul_eq_zero hb
  have h3 : addOrderOf x ∣ 1 := by
    rw [← hab.gcd_eq_one]; exact Nat.dvd_gcd h1 h2
  exact AddMonoid.addOrderOf_eq_one_iff.1 (Nat.dvd_one.1 h3)

/-- **Leaf (divisibility of `A(K̄)`).** For `n ≥ 1`, `[n] : A → A` is an isogeny (of degree
`n^{2g}`), hence surjective, hence surjective on `K̄`-points (Mumford §4, Application 2, and §6;
UNVERIFIED numbering). -/
def DivisiblePoints : Prop :=
  ∀ (K : Type) [Field K] (A : AbVar K) (n : ℕ), 0 < n → ∀ z : P A, ∃ w : P A, n • w = z

variable {A : AbVar K} {ℓ : ℕ} [Fact ℓ.Prime]

/-- A sequence of successive `ℓ`-th roots starting at `t`. -/
def rootSeq {M : Type*} [AddCommGroup M] (hdiv : ∀ z : M, ∃ w : M, ℓ • w = z) (t : M) : ℕ → M
  | 0 => t
  | i + 1 => Classical.choose (hdiv (rootSeq hdiv t i))

omit [Fact ℓ.Prime] in
lemma rootSeq_succ {M : Type*} [AddCommGroup M] (hdiv : ∀ z : M, ∃ w : M, ℓ • w = z) (t : M)
    (i : ℕ) : ℓ • rootSeq hdiv t (i + 1) = rootSeq hdiv t i :=
  Classical.choose_spec (hdiv (rootSeq hdiv t i))

omit [Fact ℓ.Prime] in
/-- `T_ℓ M → M[ℓᵏ]` is onto when `M` is `ℓ`-divisible (glue; for `M = A(K̄)` from
`DivisiblePoints`). -/
theorem tate_surj {M : Type*} [AddCommGroup M] (hdiv : ∀ z : M, ∃ w : M, ℓ • w = z) (k : ℕ)
    (t : M) (ht : ℓ ^ k • t = 0) : ∃ y : Tate.T ℓ M, y.1 k = t := by
  refine ⟨⟨fun j => ℓ ^ k • rootSeq hdiv t j, ?_, fun j => ?_⟩, ?_⟩
  · change ℓ ^ k • t = 0; exact ht
  · change ℓ • ℓ ^ k • rootSeq hdiv t (j + 1) = ℓ ^ k • rootSeq hdiv t j
    rw [smul_comm, rootSeq_succ]
  · change ℓ ^ k • rootSeq hdiv t k = t
    have := iterate_smul (rootSeq_succ hdiv t) 0 k
    rwa [Nat.zero_add] at this

variable (D : WeilDual A) (lam : Hom A D.dual)

/-- **`E^λ` has trivial left kernel (proved)**, given a quasi-inverse `ψ` of `λ` (`λψ = [d]`)
and the surjectivity of `T_ℓ A → A[ℓᵏ]`. -/
theorem tatePairing_left_ker {ψ : Hom D.dual A} {d : ℕ} (hd : 0 < d)
    (hψ : ∀ z : P D.dual, homP lam (homP ψ z) = d • z) (hℓ : (ℓ : K) ≠ 0)
    (hsurj : ∀ (k : ℕ) (t : P A), ℓ ^ k • t = 0 → ∃ y : A.T ℓ, y.1 k = t)
    (x : A.T ℓ) (hx : ∀ y, tatePairing D lam hℓ x y = 0) : x = 0 := by
  have hl : 0 < ℓ := (Fact.out : ℓ.Prime).pos
  -- `d • x_k = 0` for every `k`
  have hdk : ∀ k, d • x.1 k = 0 := by
    intro k
    have hkK : ((ℓ ^ k : ℕ) : K) ≠ 0 := by rw [Nat.cast_pow]; exact pow_ne_zero _ hℓ
    have h := weil_nondeg D lam hψ (pow_pos hl k) hkK ⟨x.1 k, tors_pow ℓ k⟩ (fun t => by
      obtain ⟨y, hy⟩ := hsurj k t (nsmul_tors t)
      have h1 := congrArg (fun z : TMu K ℓ => z.1 k) (hx y)
      simp only [tatePairing_apply] at h1
      have h2 : wv D lam (ℓ ^ k) (x.1 k) (y.1 k) = 1 := Additive.ofMul.injective h1
      have h3 : (⟨y.1 k, tors_pow ℓ k⟩ : tors A (ℓ ^ k)) = t := Subtype.ext hy
      rw [wv_eq (tors_pow ℓ k) (tors_pow ℓ k), h3] at h2
      exact Mu.val_injective h2)
    exact congrArg Subtype.val h
  obtain ⟨a, d', hd', rfl⟩ := Nat.exists_eq_pow_mul_and_not_dvd hd.ne' ℓ
    (Fact.out : ℓ.Prime).one_lt.ne'
  apply Subtype.ext; funext k
  have hcop : d'.Coprime (ℓ ^ k) :=
    Nat.Coprime.pow_right k ((Nat.coprime_comm.1 ((Fact.out : ℓ.Prime).coprime_iff_not_dvd.2 hd')))
  refine eq_zero_of_coprime hcop ?_ (tors_pow ℓ k)
  have h := hdk (k + a)
  rw [mul_comm, mul_smul, iterate_smul x.2.2 k a] at h
  exact h

/-- `det(f)² = c^{rank}` over a domain, for a bilinear form with nonzero Gram determinant. -/
theorem det_sq_of_similitude_domain {R M idx : Type*} [CommRing R] [IsDomain R] [AddCommGroup M]
    [Module R M] [Fintype idx] [DecidableEq idx] (b : Module.Basis idx R M)
    (B : LinearMap.BilinForm R M) (hB : (LinearMap.BilinForm.toMatrix b B).det ≠ 0)
    (f : M →ₗ[R] M) (c : R) (hf : ∀ x y, B (f x) (f y) = c * B x y) :
    LinearMap.det f ^ 2 = c ^ Fintype.card idx := by
  have hc : B.comp f f = c • B := by
    ext x y
    simp [hf]
  have h1 := LinearMap.BilinForm.toMatrix_comp b b B f f
  rw [hc, map_smul] at h1
  have h2 := congrArg Matrix.det h1
  rw [Matrix.det_smul, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose,
    LinearMap.det_toMatrix] at h2
  exact mul_left_cancel₀ hB (by linear_combination -h2)

/-- **G12 input on `V_ℓ A` (proved from the hypotheses).** Let `λ : A → Â` be symmetric with a
quasi-inverse (`λψ = [d]`), `ℓ` invertible in `K`, `T_ℓ A` free of finite rank (leaf
`PkgI3.TateModuleFree`), `T_ℓ A → A[ℓᵏ]` onto (from `DivisiblePoints`), and `iota : T_ℓ(μ) → ℤ_ℓ` an
injective `ℤ_ℓ`-linear map (glue target `TateMuEmbeds`). Then for every `σ ∈ G_K`,
`det ρ_ℓ(σ)² = χ_ℓ(σ)^{rank T_ℓ A}` on `V_ℓ A` (`= χ^{4}` for an abelian surface): C8 item 1. -/
theorem det_galRep_sq {ψ : Hom D.dual A} {d : ℕ} (hd : 0 < d)
    (hψ : ∀ z : P D.dual, homP lam (homP ψ z) = d • z) [NeZero (ℓ : K)]
    [Module.Free ℤ_[ℓ] (A.T ℓ)] [Module.Finite ℤ_[ℓ] (A.T ℓ)]
    (hsurj : ∀ (k : ℕ) (t : P A), ℓ ^ k • t = 0 → ∃ y : A.T ℓ, y.1 k = t)
    (iota : TMu K ℓ →ₗ[ℤ_[ℓ]] ℤ_[ℓ]) (hiota : Function.Injective iota) (σ : Gal K) :
    LinearMap.det (A.galRep ℓ σ) ^ 2 =
      algebraMap ℤ_[ℓ] ℚ_[ℓ] ((cyclotomicCharacter (AlgebraicClosure K) ℓ σ.toRingEquiv : ℤ_[ℓ]ˣ) :
        ℤ_[ℓ]) ^ Module.finrank ℤ_[ℓ] (A.T ℓ) := by
  classical
  set hℓ : (ℓ : K) ≠ 0 := NeZero.ne _
  let B : LinearMap.BilinForm ℤ_[ℓ] (A.T ℓ) := (tatePairing D lam hℓ).compr₂ iota
  have hB : ∀ x y, B (A.galT σ x) (A.galT σ y) =
      ((cyclotomicCharacter (AlgebraicClosure K) ℓ σ.toRingEquiv : ℤ_[ℓ]ˣ) : ℤ_[ℓ]) * B x y := by
    intro x y
    simp only [B, LinearMap.compr₂_apply]
    rw [tatePairing_cyclotomic, map_smul, smul_eq_mul]
  have hsep : B.SeparatingLeft := by
    intro x hx
    exact tatePairing_left_ker D lam hd hψ hℓ hsurj x fun y => hiota (by
      rw [map_zero]; exact hx y)
  have hnd : B.Nondegenerate := LinearMap.BilinForm.Nondegenerate.ofSeparatingLeft hsep
  let b := Module.Free.chooseBasis ℤ_[ℓ] (A.T ℓ)
  have hdet := (LinearMap.BilinForm.nondegenerate_iff_det_ne_zero b).1 hnd
  have key := det_sq_of_similitude_domain b B hdet (A.galT σ) _ hB
  rw [← Module.finrank_eq_card_chooseBasisIndex] at key
  change LinearMap.det ((A.galT σ).baseChange ℚ_[ℓ]) ^ 2 = _
  rw [LinearMap.det_baseChange, ← map_pow, key, map_pow]

end Det


/-! ## §9. `T_ℓ(μ) ↪ ℤ_ℓ` (proved), and the G12 determinant input from leaves alone -/

section TMuEmbed

variable {ℓ : ℕ} [Fact ℓ.Prime]

/-- `K̄ˣ` is divisible. -/
lemma units_divisible {n : ℕ} (hn : 0 < n) (z : Additive (AlgebraicClosure K)ˣ) :
    ∃ w : Additive (AlgebraicClosure K)ˣ, n • w = z := by
  obtain ⟨w, hw⟩ := IsAlgClosed.exists_pow_nat_eq ((Additive.toMul z : (AlgebraicClosure K)ˣ) :
    AlgebraicClosure K) hn
  have hw0 : w ≠ 0 := by
    rintro rfl
    rw [zero_pow hn.ne'] at hw
    exact (Additive.toMul z).ne_zero hw.symm
  refine ⟨Additive.ofMul (Units.mk0 w hw0), ?_⟩
  apply Additive.toMul.injective
  apply Units.ext
  change ((Units.mk0 w hw0 ^ n : (AlgebraicClosure K)ˣ) : AlgebraicClosure K) = _
  rw [Units.val_pow_eq_pow_val, Units.val_mk0, hw]

variable (K ℓ) in
/-- A generator of `T_ℓ(μ)`: a compatible system `(ζ_n)` with `ζ_n` of exact order `ℓⁿ`. -/
lemma exists_tmu_gen [NeZero (ℓ : K)] :
    ∃ g : TMu K ℓ, ∀ n, addOrderOf (g.1 n) = ℓ ^ n := by
  have hl1 : 1 < ℓ := (Fact.out : ℓ.Prime).one_lt
  have hl : 0 < ℓ := (Fact.out : ℓ.Prime).pos
  obtain ⟨ξ, hξ⟩ := HasEnoughRootsOfUnity.exists_isPrimitiveRoot (AlgebraicClosure K) ℓ
  let u : (AlgebraicClosure K)ˣ := Units.mk0 ξ (hξ.ne_zero hl.ne')
  have ht : ℓ ^ 1 • Additive.ofMul u = 0 := by
    apply Additive.toMul.injective
    apply Units.ext
    change ((u ^ ℓ ^ 1 : (AlgebraicClosure K)ˣ) : AlgebraicClosure K) = 1
    rw [pow_one, Units.val_pow_eq_pow_val, Units.val_mk0, hξ.pow_eq_one]
  have ht0 : Additive.ofMul u ≠ 0 := by
    intro h
    have h' : (u : AlgebraicClosure K) = 1 := by
      rw [show u = 1 from Additive.ofMul.injective h, Units.val_one]
    exact hξ.ne_one hl1 h'
  obtain ⟨y, hy⟩ := tate_surj (units_divisible hl) 1 _ ht
  refine ⟨y, fun n => ?_⟩
  cases n with
  | zero => rw [y.2.1, addOrderOf_zero, pow_zero]
  | succ m =>
    refine addOrderOf_eq_prime_pow ?_ (Tate.pow_smul_eq_zero y.2 (m + 1))
    intro h
    have h1 := iterate_smul y.2.2 1 m
    rw [Nat.add_comm 1 m, h, hy] at h1
    exact ht0 h1.symm

/-- Discrete logarithms to a base of exact order `ℓⁿ` in `K̄ˣ`. -/
lemma exists_dlog {g w : Additive (AlgebraicClosure K)ˣ} {n : ℕ} (hg : addOrderOf g = ℓ ^ n)
    (hw : ℓ ^ n • w = 0) : ∃ c : ℕ, c • g = w := by
  have hord : orderOf (Additive.toMul g) = ℓ ^ n := (addOrderOf_ofMul_eq_orderOf _).symm.trans hg
  have h : IsPrimitiveRoot (Additive.toMul g) (ℓ ^ n) := IsPrimitiveRoot.iff_orderOf.2 hord
  have hw' : Additive.toMul w ∈ rootsOfUnity (ℓ ^ n) (AlgebraicClosure K) := by
    rw [mem_rootsOfUnity]
    exact Additive.ofMul.injective hw
  obtain ⟨i, -, hi⟩ := h.eq_pow_of_mem_rootsOfUnity hw'
  exact ⟨i, congrArg Additive.ofMul hi⟩

variable {g : TMu K ℓ} (hg : ∀ n, addOrderOf (g.1 n) = ℓ ^ n)

/-- `dlog z n`: the exponent `c` with `z_n = c · ζ_n`. -/
def dlog (z : TMu K ℓ) (n : ℕ) : ℕ :=
  Classical.choose (exists_dlog (hg n) (Tate.pow_smul_eq_zero z.2 n))

lemma dlog_spec (z : TMu K ℓ) (n : ℕ) : dlog hg z n • g.1 n = z.1 n :=
  Classical.choose_spec (exists_dlog (hg n) (Tate.pow_smul_eq_zero z.2 n))

include hg in
lemma modEq_of_smul_eq {n a b : ℕ} (h : a • g.1 n = b • g.1 n) : (a : ZMod (ℓ ^ n)) = b := by
  rw [ZMod.natCast_eq_natCast_iff, ← hg n]
  exact (nsmul_eq_nsmul_iff_modEq).1 h

lemma dlog_compat (z : TMu K ℓ) (n : ℕ) :
    ((ℓ : ℤ) ^ n) ∣ ((dlog hg z (n + 1) : ℕ) : ℤ) - ((dlog hg z n : ℕ) : ℤ) := by
  have h : dlog hg z (n + 1) • g.1 n = dlog hg z n • g.1 n := by
    calc dlog hg z (n + 1) • g.1 n = dlog hg z (n + 1) • (ℓ • g.1 (n + 1)) := by rw [g.2.2 n]
      _ = ℓ • (dlog hg z (n + 1) • g.1 (n + 1)) := smul_comm _ _ _
      _ = ℓ • z.1 (n + 1) := by rw [dlog_spec]
      _ = z.1 n := z.2.2 n
      _ = dlog hg z n • g.1 n := (dlog_spec hg z n).symm
  have h2 := modEq_of_smul_eq hg h
  rw [ZMod.natCast_eq_natCast_iff] at h2
  have h3 := (Nat.modEq_iff_dvd.1 h2.symm)
  simpa using h3

/-- The coordinate `T_ℓ(μ) → ℤ_ℓ`, `z ↦ lim dlog z n`. -/
def tmuCoord (z : TMu K ℓ) : ℤ_[ℓ] :=
  PadicInt.ofIntSeq _ (PadicInt.isCauSeq_padicNorm_of_pow_dvd_sub
    (fun n => ((dlog hg z n : ℕ) : ℤ)) ℓ (dlog_compat hg z))

lemma toZModPow_tmuCoord (z : TMu K ℓ) (n : ℕ) :
    PadicInt.toZModPow n (tmuCoord hg z) = (dlog hg z n : ZMod (ℓ ^ n)) := by
  unfold tmuCoord
  rw [PadicInt.toZModPow_ofIntSeq_of_pow_dvd_sub _ _ (dlog_compat hg z)]
  simp

/-- **`T_ℓ(μ) ↪ ℤ_ℓ` (proved):** the coordinate is `ℤ_ℓ`-linear and injective. -/
def tmuCoordLin : TMu K ℓ →ₗ[ℤ_[ℓ]] ℤ_[ℓ] where
  toFun := tmuCoord hg
  map_add' z z' := by
    refine PadicInt.ext_of_toZModPow.1 fun n => ?_
    rw [map_add, toZModPow_tmuCoord, toZModPow_tmuCoord, toZModPow_tmuCoord, ← Nat.cast_add]
    apply modEq_of_smul_eq hg
    rw [add_smul, dlog_spec, dlog_spec, dlog_spec]
    rfl
  map_smul' a z := by
    refine PadicInt.ext_of_toZModPow.1 fun n => ?_
    rw [RingHom.id_apply, smul_eq_mul, map_mul, toZModPow_tmuCoord, toZModPow_tmuCoord,
      ← ZMod.natCast_zmod_val (PadicInt.toZModPow n a), ← Nat.cast_mul]
    apply modEq_of_smul_eq hg
    rw [dlog_spec, mul_smul, dlog_spec]
    rfl

lemma tmuCoordLin_injective : Function.Injective (tmuCoordLin hg) := by
  intro z z' h
  apply Subtype.ext; funext n
  have h1 := congrArg (PadicInt.toZModPow n) h
  change PadicInt.toZModPow n (tmuCoord hg z) = PadicInt.toZModPow n (tmuCoord hg z') at h1
  rw [toZModPow_tmuCoord, toZModPow_tmuCoord, ZMod.natCast_eq_natCast_iff, ← hg n] at h1
  rw [← dlog_spec hg z n, ← dlog_spec hg z' n]
  exact (nsmul_eq_nsmul_iff_modEq).2 h1

end TMuEmbed

/-- **G12 determinant input (glue target, stated over Objects' `galRep`).** For an abelian
variety `A/K`, a prime `ℓ` invertible in `K` and `σ ∈ G_K`: `det ρ_ℓ(σ)² = χ_ℓ(σ)^{rank T_ℓ A}`
(`rank = 2g`). C8 item 1 in `det²` form (with `twist_finite_four`). -/
def G12_DetInput : Prop :=
  ∀ (K : Type) [Field K] (A : AbVar K) (ℓ : ℕ) [Fact ℓ.Prime] [NeZero (ℓ : K)] (σ : Gal K),
    LinearMap.det (A.galRep ℓ σ) ^ 2 =
      algebraMap ℤ_[ℓ] ℚ_[ℓ] ((cyclotomicCharacter (AlgebraicClosure K) ℓ σ.toRingEquiv :
        ℤ_[ℓ]ˣ) : ℤ_[ℓ]) ^ Module.finrank ℤ_[ℓ] (A.T ℓ)

/-- **The G12 input from four leaves (proved).** T9 (restated), the isogeny quasi-inverse, the
freeness of `T_ℓ A` (`PkgI3.TateModuleFree`, Objects) and the divisibility of `A(K̄)` imply
`G12_DetInput`. -/
theorem g12_detInput_of_leaves (h9 : T09_SymmIsogenyExists) (hQ : IsogenyQuasiInverse)
    (hT : PkgI3.TateModuleFree) (hD : DivisiblePoints) : G12_DetInput := by
  intro K _ A ℓ _ _ σ
  obtain ⟨S⟩ := h9 K A
  obtain ⟨d, hd, ψ, hψ, -⟩ := hQ K _ _ S.lam S.isogeny
  obtain ⟨hfree, hfin, -⟩ := hT K A ℓ (NeZero.ne _)
  obtain ⟨g, hg⟩ := exists_tmu_gen K ℓ
  exact det_galRep_sq S.D S.lam hd hψ
    (fun k t ht => tate_surj (hD K A ℓ (Fact.out : ℓ.Prime).pos) k t ht)
    (tmuCoordLin hg) (tmuCoordLin_injective hg) σ


/-! ## §10. Further non-vacuity checks -/

/-- `T09plus_PolarizationExists` holds at `A = 0` (Rosati positivity is vacuous there:
`End(0) = 0`). With `symmIsogeny_zero`, the leaves of §4 are consistent. -/
theorem polarization_zero (K : Type) [Field K] : Nonempty (Polarization (AbVar.zero K)) := by
  obtain ⟨S⟩ := symmIsogeny_zero K
  refine ⟨{ toSymmIsogeny := S, pos := ?_ }⟩
  intro ℓ _ _ d ψ _ _ φ φv _ hφ
  exact absurd (Hom.ext' (CartesianMonoidalCategory.toUnit_unique _ _)) hφ

/-- The Weil pairing of a symmetric isogeny is not forced to vanish: on any `A`, if some
`e^λ_n` (`n` invertible) is identically zero then `d • A[n] = 0` for every quasi-inverse
exponent `d` of `λ`. (Hence, granted `A[n] ≅ (ℤ/n)^{2g}` with `g ≥ 1` and `n ∤ d`, `e^λ_n ≠ 0`.) -/
theorem weil_ne_zero_of {A : AbVar K} (S : SymmIsogeny A) {ψ : Hom S.D.dual A} {d : ℕ}
    (hψ : ∀ z : P S.D.dual, homP S.lam (homP ψ z) = d • z) {n : ℕ} (hn : 0 < n)
    (hnK : (n : K) ≠ 0) (h0 : weil S.D S.lam n = 0) (x : tors A n) : d • x = 0 :=
  weil_nondeg S.D S.lam hψ hn hnK x fun y => by rw [h0]; rfl

end WeilPairing

#print axioms WeilPairing.oldT9_of_symmIsogeny
#print axioms WeilPairing.symmIsogeny_zero
#print axioms WeilPairing.weil_cyclotomic
#print axioms WeilPairing.det_sq_of_similitude_field
#print axioms WeilPairing.twist_finite_four
#print axioms WeilPairing.weil_perfect_of_principal
#print axioms WeilPairing.isSymmetric_pullback
#print axioms WeilPairing.tatePairing_cyclotomic
#print axioms WeilPairing.tatePairing_left_ker
#print axioms WeilPairing.det_galRep_sq
#print axioms WeilPairing.tmuCoordLin_injective
#print axioms WeilPairing.g12_detInput_of_leaves
