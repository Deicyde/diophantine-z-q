/-! ## g0-assemble2: g12-det (its new parts, assembled as in scratch/g12-det/build_int.py, minus ResQ and part_integrate) -/
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
algebraically closed `K` any `Â` with compatible isomorphisms `Â[n] ≅ A[n]` (all `n` invertible
in `K`) carries one, even `Â = A`. Hence leaves over
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
  /-- every endomorphism has a dual (for `Pic⁰`: `f ↦ f^∨`, Mumford §8, §20 (5); UNVERIFIED);
  added after review so that Rosati conditions are never vacuous for lack of duals -/
  dualEnd : ∀ f : End A, ∃ fv : End dual, ∀ n : ℕ, 0 < n → (n : K) ≠ 0 →
    ∀ x y, e n x (torsMap fv n y) = e n (torsMap f n x) y

/-- `g : B̂ → Â` is dual to `f : A → B`: `e_n(x, g y) = e_n(f x, y)` for all `n` invertible in `K`
(Mumford §20, (5); UNVERIFIED numbering). -/
def IsDualHom {A B : AbVar K} (DA : WeilDual A) (DB : WeilDual B) (f : Hom A B)
    (g : Hom DB.dual DA.dual) : Prop :=
  ∀ n : ℕ, 0 < n → (n : K) ≠ 0 → ∀ x y, DA.e n x (torsMap g n y) = DB.e n (torsMap f n x) y

/-- Every endomorphism has a dual (field `dualEnd`). -/
lemma WeilDual.exists_dualEnd {A : AbVar K} (D : WeilDual A) (f : End A) :
    ∃ fv : End D.dual, IsDualHom D D f fv :=
  D.dualEnd f

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

/-- (With `WeilDual.dualEnd`, every `φ` has some `φv`, so this is not vacuous.)
**Rosati positivity** of `λ`: for every nonzero `φ ∈ End(A)` with dual `φ^∨` and every
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

/-- **A polarization (up to sign)**: a symmetric isogeny with Rosati positivity. CAUTION: `-λ` has
the same Rosati involution, so `-φ_L` also qualifies (and on a product, `λ₁ × (-λ₂)`); the
genuine notion (ampleness) is not expressible without line bundles. Safe only in existential
leaves; a leaf `∀ S : Polarization A, …` would be unsafe. -/
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
  dualEnd _ := ⟨0, fun _ _ _ _ _ => rfl⟩

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

-- (twist_finite_four, WeilPairing.lean L644-675, omitted: it uses GlueAssembly)


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


end WeilPairing

end


section G12DetDetSec
noncomputable section
namespace G0Galois
open scoped Matrix

/-! ## The named pieces -/

/-- **Symplectic (Darboux) bases (GLUE, pure linear algebra; STANDARD: Bourbaki, Algèbre IX §5
no. 1, Artin, *Geometric algebra*, Thm 3.7; numbering UNVERIFIED).** A nondegenerate alternating
bilinear form on a space of dimension `2n` over a field has a basis, indexed by `Fin n ⊕ Fin n`,
in which its Gram matrix is Mathlib's `Matrix.J`. -/
def Darboux : Prop :=
  ∀ (F V : Type) [Field F] [AddCommGroup V] [Module F V] [FiniteDimensional F V]
    (B : LinearMap.BilinForm F V) (n : ℕ), B.Nondegenerate → (∀ x, B x x = 0) →
    Module.finrank F V = 2 * n →
    ∃ b : Module.Basis (Fin n ⊕ Fin n) F V, LinearMap.BilinForm.toMatrix b B = Matrix.J (Fin n) F

/-- **Determinant of a symplectic similitude (GLUE, pure linear algebra; STANDARD: the Pfaffian
identity `Pf(MᵀGM) = det M · Pf G`, Bourbaki, Algèbre IX §5 no. 2; numbering UNVERIFIED).** If `f`
multiplies a nondegenerate alternating form on a `2n`-dimensional space by `c ≠ 0`, then
`det f = cⁿ`. Proved below from `Darboux` (`sympSimDet_of_darboux`). -/
def SympSimDet : Prop :=
  ∀ (F V : Type) [Field F] [AddCommGroup V] [Module F V] [FiniteDimensional F V]
    (B : LinearMap.BilinForm F V) (f : V →ₗ[F] V) (c : F) (n : ℕ), B.Nondegenerate →
    (∀ x, B x x = 0) → Module.finrank F V = 2 * n → c ≠ 0 →
    (∀ x y, B (f x) (f y) = c * B x y) → LinearMap.det f = c ^ n

/-- **The `ℓ`-adic Weil pairing on `V_ℓ(A)` (GLUE; from T9 = Mumford §20, §23 and T26 =
Mumford §18-19, as restated in scratch/weil-pairing).** For an abelian variety `A` of dimension
`g` over a number field `K` and a prime `ℓ`: `V_ℓ(A)` has dimension `2g` and carries a
nondegenerate alternating `ℚ_ℓ`-bilinear form `B` with `B(σx, σy) = χ_ℓ(σ) B(x, y)` for
`σ ∈ G_K`, `χ_ℓ` the cyclotomic character of `G_K` on `K̄`. (`B = E^λ` for a polarization `λ`
over `K`, composed with a coordinate `T_ℓ(μ) ≅ ℤ_ℓ`.) scratch/weil-pairing proves, from the leaves
`T09_SymmIsogenyExists`, `IsogenyQuasiInverse`, `TateModuleFree`, `DivisiblePoints`, the
`ℤ_ℓ`-level pairing `tatePairing` on `T_ℓ A` (alternating `tatePairing_self`, multiplier
`tatePairing_cyclotomic`, trivial left kernel `tatePairing_left_ker`) and the coordinate
`tmuCoordLin`; what is left is the extension of scalars to `V_ℓ = ℚ_ℓ ⊗ T_ℓ` (nondegeneracy over
the fraction field from the trivial kernel on a free module of finite rank) and
`dim V_ℓ = rank T_ℓ = 2g` (T26). -/
def TateGSp : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (A : PkgI3.AbVar K) (ℓ : ℕ) [Fact ℓ.Prime] (g : ℕ),
    A.dim = g →
    ∃ (_ : FiniteDimensional ℚ_[ℓ] (A.V ℓ)) (B : LinearMap.BilinForm ℚ_[ℓ] (A.V ℓ)),
      Module.finrank ℚ_[ℓ] (A.V ℓ) = 2 * g ∧ B.Nondegenerate ∧ (∀ x, B x x = 0) ∧
      ∀ (σ : Field.absoluteGaloisGroup K) (x y : A.V ℓ),
        B (A.galRep ℓ σ x) (A.galRep ℓ σ y) =
          (((cyclotomicCharacter (AlgebraicClosure K) ℓ σ.toRingEquiv : ℤ_[ℓ]ˣ) : ℤ_[ℓ]) :
            ℚ_[ℓ]) * B x y

/-! ## Proofs -/

/-- `Dᵀ J D = c⁻¹ J` for `D = diag(1, c⁻¹)`. -/
lemma J_conj_diag {F : Type*} [Field F] (n : ℕ) (c : F) :
    (Matrix.fromBlocks 1 0 0 (c⁻¹ • 1) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F)ᵀ *
        Matrix.J (Fin n) F * Matrix.fromBlocks 1 0 0 (c⁻¹ • 1) = c⁻¹ • Matrix.J (Fin n) F := by
  simp [Matrix.J, Matrix.fromBlocks_transpose, Matrix.fromBlocks_multiply, Matrix.fromBlocks_smul]

/-- **`SympSimDet` from `Darboux`** (and Mathlib's `Matrix.symplecticGroup.det_eq_one`). -/
theorem sympSimDet_of_darboux (hD : Darboux) : SympSimDet := by
  intro F V _ _ _ _ B f c n hB halt hdim hc hf
  classical
  obtain ⟨b, hb⟩ := hD F V B n hB halt hdim
  set M := LinearMap.toMatrix b b f with hM
  have hcomp : B.comp f f = c • B := by
    ext x y
    simp [hf]
  have h1 := LinearMap.BilinForm.toMatrix_comp b b B f f
  rw [hcomp, map_smul, hb] at h1
  -- `h1 : c • J = Mᵀ * J * M`
  set D : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F := Matrix.fromBlocks 1 0 0 (c⁻¹ • 1) with hDdef
  have hsymp : M * D ∈ Matrix.symplecticGroup (Fin n) F := by
    rw [SymplecticGroup.mem_iff']
    calc (M * D)ᵀ * Matrix.J (Fin n) F * (M * D)
        = Dᵀ * (Mᵀ * Matrix.J (Fin n) F * M) * D := by
          rw [Matrix.transpose_mul]; simp only [Matrix.mul_assoc]
      _ = c • (Dᵀ * Matrix.J (Fin n) F * D) := by
          rw [← h1, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_assoc]
      _ = Matrix.J (Fin n) F := by
          rw [hDdef, J_conj_diag, smul_smul, mul_inv_cancel₀ hc, one_smul]
  have hdet1 := SymplecticGroup.det_eq_one hsymp
  have hDdet : D.det = c⁻¹ ^ n := by
    rw [hDdef, Matrix.det_fromBlocks_zero₂₁, Matrix.det_one, Matrix.det_smul, Matrix.det_one,
      Fintype.card_fin]
    ring
  rw [Matrix.det_mul, hDdet] at hdet1
  rw [← LinearMap.det_toMatrix b f, ← hM]
  have hcn : c ^ n ≠ 0 := pow_ne_zero n hc
  rw [inv_pow] at hdet1
  exact (mul_inv_eq_one₀ hcn).1 hdet1

/-- The cyclotomic characters of two fields agree on automorphisms intertwined by a ring
homomorphism (both fields containing all `ℓ`-power roots of unity). -/
lemma cyc_eq_of_intertwines {L L' : Type*} [Field L] [Field L'] (ℓ : ℕ) [Fact ℓ.Prime]
    [∀ k, HasEnoughRootsOfUnity L (ℓ ^ k)] [∀ k, HasEnoughRootsOfUnity L' (ℓ ^ k)]
    (i : L →+* L') (g : L ≃+* L) (g' : L' ≃+* L') (h : ∀ x, i (g x) = g' (i x)) :
    cyclotomicCharacter L ℓ g = cyclotomicCharacter L' ℓ g' := by
  apply Units.ext
  refine PadicInt.ext_of_toZModPow.mp fun n => ?_
  rw [cyclotomicCharacter.toZModPow, cyclotomicCharacter.toZModPow]
  symm
  apply modularCyclotomicCharacter.unique
  intro t ht
  have ht' : Units.map i.toMonoidHom t ∈ rootsOfUnity (ℓ ^ n) L' := by
    rw [mem_rootsOfUnity] at ht ⊢
    rw [← map_pow, ht, map_one]
  have := modularCyclotomicCharacter.spec L'
    (HasEnoughRootsOfUnity.natCard_rootsOfUnity L' (ℓ ^ n)) g' ht'
  apply i.injective
  rw [h, map_pow]
  simpa using this

/-- `χ_ℓ(resQ σ)` on `ℚ̄` is `χ_ℓ(σ)` on `K̄`. -/
lemma cycQ_resQ (K : Type) [Field K] [NumberField K] (ℓ : ℕ) [Fact ℓ.Prime]
    (σ : Field.absoluteGaloisGroup K) :
    cyclotomicCharacter PkgI4.Qbar ℓ (toRingEquivQ (resQ K σ)) =
      cyclotomicCharacter (AlgebraicClosure K) ℓ σ.toRingEquiv :=
  cyc_eq_of_intertwines ℓ (qEmbRing K) _ _ (fun x => resQ_spec K σ x)

/-- **`DetTate` from `TateGSp` and `SympSimDet`.** -/
theorem detTate_of (hW : TateGSp) (hS : SympSimDet) : DetTate := by
  intro K _ _ A ℓ _ g hdim σ
  obtain ⟨hfd, B, hrank, hB, halt, hmult⟩ := hW K A ℓ g hdim
  set c : ℚ_[ℓ] := (((cyclotomicCharacter (AlgebraicClosure K) ℓ σ.toRingEquiv : ℤ_[ℓ]ˣ) :
    ℤ_[ℓ]) : ℚ_[ℓ]) with hc
  have hc0 : c ≠ 0 := by
    rw [hc, PadicInt.coe_ne_zero]
    exact Units.ne_zero _
  have hdet : LinearMap.det (A.galRep ℓ σ) = c ^ g :=
    hS ℚ_[ℓ] (A.V ℓ) B (A.galRep ℓ σ) c g hB halt hrank hc0 (hmult σ)
  change LinearMap.det ((A.galRep ℓ σ).baseChange (PadicAlgCl ℓ)) = _
  rw [LinearMap.det_baseChange, hdet, map_pow]
  congr 1
  simp only [cycQ, MonoidHom.coe_comp, Function.comp_apply, Units.coe_map,
    RingHom.toMonoidHom_eq_coe, MonoidHom.coe_ofClass, RingHom.coe_comp]
  rw [cycQ_resQ]
  rfl

/-- **`DetTate` from `TateGSp` and `Darboux`.** -/
theorem detTate_of_darboux (hW : TateGSp) (hD : Darboux) : DetTate :=
  detTate_of hW (sympSimDet_of_darboux hD)


/-! ## `Darboux`, proved (same proof as scratch/g12-det/Darboux.lean) -/

section DarbouxProof

open Module LinearMap LinearMap.BilinForm

variable {F : Type} [Field F]

lemma skew_of_alt {V : Type} [AddCommGroup V] [Module F V] (B : LinearMap.BilinForm F V)
    (halt : ∀ x, B x x = 0) (x y : V) : B y x = - B x y := by
  have h := halt (x + y)
  simp only [map_add, LinearMap.add_apply, halt x, halt y, zero_add, add_zero] at h
  linear_combination h

lemma isRefl_of_alt {V : Type} [AddCommGroup V] [Module F V] (B : LinearMap.BilinForm F V)
    (halt : ∀ x, B x x = 0) : B.IsRefl := by
  intro x y h
  rw [skew_of_alt B halt x y, h, neg_zero]

/-- A family with Gram matrix `J` is linearly independent. -/
lemma linearIndependent_of_gram {V : Type} [AddCommGroup V] [Module F V]
    (B : LinearMap.BilinForm F V) (n : ℕ) (v : Fin n ⊕ Fin n → V)
    (hv : ∀ i j, B (v i) (v j) = Matrix.J (Fin n) F i j) : LinearIndependent F v := by
  classical
  rw [Fintype.linearIndependent_iff]
  intro g hg
  have h1 : Matrix.vecMul g (Matrix.J (Fin n) F) = 0 := by
    funext j
    have := congrArg (fun x => B x (v j)) hg
    simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, hv, smul_eq_mul,
      map_zero, LinearMap.zero_apply] at this
    simpa [Matrix.vecMul, dotProduct] using this
  have h2 := congrArg (fun w => Matrix.vecMul w (Matrix.J (Fin n) F)) h1
  simp only [Matrix.vecMul_vecMul, Matrix.J_squared, Matrix.zero_vecMul] at h2
  intro i
  have := congrFun h2 i
  simpa [Matrix.vecMul_neg] using this

/-- The family version of Darboux, by induction. -/
lemma exists_gram_J : ∀ (n : ℕ) (V : Type) [AddCommGroup V] [Module F V] [FiniteDimensional F V]
    (B : LinearMap.BilinForm F V), B.Nondegenerate → (∀ x, B x x = 0) → finrank F V = 2 * n →
    ∃ v : Fin n ⊕ Fin n → V, ∀ i j, B (v i) (v j) = Matrix.J (Fin n) F i j := by
  intro n
  induction n with
  | zero =>
    intro V _ _ _ B _ _ _
    exact ⟨fun i => by rcases i with i | i <;> exact i.elim0, fun i => by
      rcases i with i | i <;> exact i.elim0⟩
  | succ n ih =>
    intro V _ _ _ B hB halt hdim
    have hrefl := isRefl_of_alt B halt
    have hpos : 0 < finrank F V := by rw [hdim]; omega
    haveI : Nontrivial V := Module.finrank_pos_iff.mp hpos
    obtain ⟨e, he⟩ := exists_ne (0 : V)
    have : ∃ y, B e y ≠ 0 := by
      by_contra h
      push Not at h
      exact he (hB.1 e h)
    obtain ⟨y, hy⟩ := this
    set f := (B e y)⁻¹ • y with hfdef
    have hef : B e f = 1 := by
      rw [hfdef, map_smul, smul_eq_mul, inv_mul_cancel₀ hy]
    have hfe : B f e = -1 := by rw [skew_of_alt B halt, hef]
    have hee : B e e = 0 := halt e
    have hff : B f f = 0 := halt f
    set H : Submodule F V := Submodule.span F {e, f} with hH
    set W : Submodule F V := B.orthogonal H with hW
    -- elements of `H`
    have hmemH : ∀ x ∈ H, ∃ a b : F, a • e + b • f = x := fun x hx =>
      Submodule.mem_span_pair.mp hx
    have heH : e ∈ H := Submodule.subset_span (by simp)
    have hfH : f ∈ H := Submodule.subset_span (by simp)
    -- `H ∩ H^⊥ = 0`
    have hdisj : Disjoint H W := by
      rw [Submodule.disjoint_def]
      intro x hx hxW
      obtain ⟨a, b, rfl⟩ := hmemH x hx
      have h1 : B e (a • e + b • f) = 0 := hxW e heH
      have h2 : B f (a • e + b • f) = 0 := hxW f hfH
      simp only [map_add, map_smul, smul_eq_mul, hee, hef, hfe, hff] at h1 h2
      have ha : a = 0 := by linear_combination -h2
      have hb : b = 0 := by linear_combination h1
      simp [ha, hb]
    have hcompl : IsCompl H W :=
      isCompl_orthogonal_of_restrict_nondegenerate hrefl
        (B.nondegenerate_restrict_of_disjoint_orthogonal hrefl hdisj)
    -- `finrank H = 2`
    have hli : LinearIndependent F ![e, f] := by
      rw [LinearIndependent.pair_iff]
      intro s t hst
      have h1 := congrArg (B e) hst
      have h2 := congrArg (B f) hst
      simp only [map_add, map_smul, smul_eq_mul, hee, hef, hfe, hff, map_zero] at h1 h2
      constructor
      · linear_combination -h2
      · linear_combination h1
    have hH2 : finrank F H = 2 := by
      have := finrank_span_eq_card hli
      rw [Matrix.range_cons_cons_empty, Fintype.card_fin] at this
      exact this
    have hW2 : finrank F W = 2 * n := by
      rw [hW, finrank_orthogonal hB, hdim, hH2]; omega
    -- the restriction to `W` is nondegenerate and alternating
    have hBW : (B.restrict W).Nondegenerate := by
      have hsplit : ∀ z : V, ∃ h ∈ H, ∃ w ∈ W, h + w = z := fun z =>
        Submodule.mem_sup.mp (hcompl.sup_eq_top ▸ Submodule.mem_top)
      constructor
      · intro m hm
        apply Subtype.ext
        apply hB.1
        intro z
        obtain ⟨h, hh, w, hw, rfl⟩ := hsplit z
        rw [map_add, hrefl _ _ (m.2 h hh)]
        have := hm ⟨w, hw⟩
        simpa using this
      · intro m hm
        apply Subtype.ext
        apply hB.2
        intro z
        obtain ⟨h, hh, w, hw, rfl⟩ := hsplit z
        rw [LinearMap.map_add₂, m.2 h hh]
        have := hm ⟨w, hw⟩
        simpa using this
    have haltW : ∀ x, B.restrict W x x = 0 := fun x => halt x
    obtain ⟨w, hw⟩ := ih W (B.restrict W) hBW haltW hW2
    have hfw : ∀ x : W, B f x = 0 := fun x => x.2 f hfH
    have hew : ∀ x : W, B e x = 0 := fun x => x.2 e heH
    have hwf : ∀ x : W, B x f = 0 := fun x => hrefl _ _ (hfw x)
    have hwe : ∀ x : W, B x e = 0 := fun x => hrefl _ _ (hew x)
    have hww : ∀ i j, B (w i) (w j) = Matrix.J (Fin n) F i j := hw
    let v : Fin (n + 1) ⊕ Fin (n + 1) → V :=
      Sum.elim (Fin.cons f fun j => (w (Sum.inl j) : V))
        (Fin.cons e fun j => (w (Sum.inr j) : V))
    refine ⟨v, ?_⟩
    intro i j
    rcases i with i | i <;> rcases j with j | j <;>
      induction i using Fin.cases <;> induction j using Fin.cases <;>
      simp [v, Matrix.J, hef, hfe, hee, hff, hfw, hew, hwf, hwe, hww, Matrix.one_apply,
        Fin.succ_ne_zero, Fin.succ_inj]
    all_goals exact (Fin.succ_ne_zero _).symm

/-- **`Darboux`, proved.** -/
theorem darboux : Darboux := by
  intro F V _ _ _ _ B n hB halt hdim
  classical
  obtain ⟨v, hv⟩ := exists_gram_J n V B hB halt hdim
  have hli := linearIndependent_of_gram B n v hv
  have hcard : Fintype.card (Fin n ⊕ Fin n) = finrank F V := by
    rw [Fintype.card_sum, Fintype.card_fin, hdim]; ring
  refine ⟨basisOfLinearIndependentOfCardEqFinrank' v hli hcard, ?_⟩
  refine Matrix.ext fun i j => ?_
  rw [LinearMap.BilinForm.toMatrix_apply, coe_basisOfLinearIndependentOfCardEqFinrank', hv]

end DarbouxProof

/-- **`DetTate` from `TateGSp` alone** (`Darboux` and `SympSimDet` are proved). -/
theorem detTate_of_tateGSp (hW : TateGSp) : DetTate :=
  detTate_of_darboux hW darboux


/-! ## `TateGSp` from the `ℤ_ℓ`-level Weil pairing (scratch/weil-pairing) and T26 -/

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj

/-- **The `ℓ`-adic Weil pairing on `T_ℓ(A)`, `ℤ_ℓ`-valued (GLUE, proved in scratch/weil-pairing
from leaves, up to restatement).** There is an alternating `ℤ_ℓ`-bilinear form on `T_ℓ(A)` with
trivial left kernel and multiplier the cyclotomic character of `G_K` on `K̄`. In
scratch/weil-pairing this is `B = (tatePairing D lam hℓ).compr₂ (tmuCoordLin hg)` for a
polarization `S.lam` (leaf `T09_SymmIsogenyExists`), with `tatePairing_self` (alternating),
`tatePairing_cyclotomic` (multiplier), and `tatePairing_left_ker` + `tmuCoordLin_injective`
(trivial left kernel; leaves `IsogenyQuasiInverse`, `DivisiblePoints`), exactly as in the proof
of `det_galRep_sq` / `g12_detInput_of_leaves` there (VERIFIED by reading WeilPairing.lean
L969-1148). The statement below is not compiled against that file (scratch files cannot import
each other); its `B` is theirs. -/
def TatePairingZl : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (A : PkgI3.AbVar K) (ℓ : ℕ) [Fact ℓ.Prime],
    ∃ B : LinearMap.BilinForm ℤ_[ℓ] (A.T ℓ), B.SeparatingLeft ∧ (∀ x, B x x = 0) ∧
      ∀ (σ : Field.absoluteGaloisGroup K) (x y : A.T ℓ),
        B (A.galT σ x) (A.galT σ y) =
          ((cyclotomicCharacter (AlgebraicClosure K) ℓ σ.toRingEquiv : ℤ_[ℓ]ˣ) : ℤ_[ℓ]) * B x y

lemma skew_of_alt' {R V : Type*} [CommRing R] [AddCommGroup V] [Module R V]
    (B : LinearMap.BilinForm R V) (halt : ∀ x, B x x = 0) (x y : V) : B y x = - B x y := by
  have h := halt (x + y)
  simp only [map_add, LinearMap.add_apply, halt x, halt y, zero_add, add_zero] at h
  linear_combination h

/-- **`TateGSp` from `TatePairingZl` and T26 (`PkgI3.TateModuleFree`, leaf I3 of Objects).** The
form on `V_ℓ = ℚ_ℓ ⊗ T_ℓ` is the one with the same Gram matrix in the base-changed basis. -/
theorem tateGSp_of_zl (hZ : TatePairingZl) (hT : PkgI3.TateModuleFree) : TateGSp := by
  intro K _ _ A ℓ _ g hdim
  classical
  obtain ⟨B0, hsep, halt0, hmult⟩ := hZ K A ℓ
  have hℓ : (ℓ : K) ≠ 0 := by exact_mod_cast (Fact.out : ℓ.Prime).ne_zero
  obtain ⟨hfree, hfin, hrk⟩ := hT K A ℓ hℓ
  have hrank : Module.finrank ℤ_[ℓ] (A.T ℓ) = 2 * g := by
    rw [hdim] at hrk
    have h3 : (((Module.finrank ℤ_[ℓ] (A.T ℓ) : ℕ) : ℕ∞) : WithBot ℕ∞) =
        (((2 * g : ℕ) : ℕ∞) : WithBot ℕ∞) := by
      rw [hrk]; push_cast; rfl
    exact_mod_cast WithBot.coe_injective h3
  let b := Module.Free.chooseBasis ℤ_[ℓ] (A.T ℓ)
  let bV : Module.Basis _ ℚ_[ℓ] (A.V ℓ) := Algebra.TensorProduct.basis ℚ_[ℓ] b
  have hnd0 : B0.Nondegenerate := LinearMap.BilinForm.Nondegenerate.ofSeparatingLeft hsep
  have hdet0 := (LinearMap.BilinForm.nondegenerate_iff_det_ne_zero b).1 hnd0
  set G := LinearMap.BilinForm.toMatrix b B0 with hG
  let φ := algebraMap ℤ_[ℓ] ℚ_[ℓ]
  have hφ : Function.Injective φ := IsFractionRing.injective ℤ_[ℓ] ℚ_[ℓ]
  set G' := G.map φ with hG'
  let B : LinearMap.BilinForm ℚ_[ℓ] (A.V ℓ) := Matrix.toBilin bV G'
  have hBG : LinearMap.BilinForm.toMatrix bV B = G' := LinearMap.BilinForm.toMatrix_toBilin _ _
  haveI : FiniteDimensional ℚ_[ℓ] (A.V ℓ) := Module.Finite.of_basis bV
  refine ⟨inferInstance, B, ?_, ?_, ?_, ?_⟩
  · rw [Module.finrank_baseChange, hrank]
  · rw [LinearMap.BilinForm.nondegenerate_iff_det_ne_zero bV, hBG, hG', show G.map φ = φ.mapMatrix G from rfl, ← RingHom.map_det]
    exact fun h => hdet0 (hφ (by rw [h, map_zero]))
  · -- alternating: the Gram matrix is alternating, and `2 ≠ 0`
    have hskew : ∀ i j, G' j i = - G' i j := by
      intro i j
      simp only [hG', hG, Matrix.map_apply, LinearMap.BilinForm.toMatrix_apply]
      rw [skew_of_alt' B0 halt0, map_neg]
    intro x
    have hsum : B x x = ∑ i, ∑ j, bV.repr x i * G' i j * bV.repr x j := Matrix.toBilin_apply bV G' x x
    have hsum' : B x x = - B x x := by
      conv_rhs => rw [hsum, Finset.sum_comm]
      rw [hsum, ← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [hskew j i]
      ring
    have h2 : (2 : ℚ_[ℓ]) * B x x = 0 := by linear_combination hsum'
    exact (mul_eq_zero.1 h2).resolve_left two_ne_zero
  · intro σ
    set c0 := ((cyclotomicCharacter (AlgebraicClosure K) ℓ σ.toRingEquiv : ℤ_[ℓ]ˣ) : ℤ_[ℓ])
    have hc0 : B0.comp (A.galT σ) (A.galT σ) = c0 • B0 := by
      refine LinearMap.ext fun x => LinearMap.ext fun y => ?_
      change B0 (A.galT σ x) (A.galT σ y) = c0 * B0 x y
      rw [hmult σ x y]
    set M := LinearMap.toMatrix b b (A.galT σ) with hM
    have h1 := LinearMap.BilinForm.toMatrix_comp b b B0 (A.galT σ) (A.galT σ)
    rw [hc0, map_smul] at h1
    -- `h1 : c0 • G = Mᵀ * G * M`
    have hfM : LinearMap.toMatrix bV bV (A.galRep ℓ σ) = M.map φ :=
      LinearMap.toMatrix_baseChange ℚ_[ℓ] (A.galT σ) b b
    have hcomp : B.comp (A.galRep ℓ σ) (A.galRep ℓ σ) = (φ c0) • B := by
      apply (LinearMap.BilinForm.toMatrix bV).injective
      rw [LinearMap.BilinForm.toMatrix_comp bV bV, hfM, hBG, map_smul, hBG, hG']
      have h2 := congrArg (fun X => X.map φ) h1
      simp only [Matrix.map_mul, Matrix.transpose_map] at h2
      rw [← hG] at h2
      exact h2.symm
    intro x y
    have := congrArg (fun C : LinearMap.BilinForm ℚ_[ℓ] (A.V ℓ) => C x y) hcomp
    simpa [φ] using this

/-- **`DetTate` from the `ℤ_ℓ`-level Weil pairing and T26.** -/
theorem detTate_of_zl (hZ : TatePairingZl) (hT : PkgI3.TateModuleFree) : DetTate :=
  detTate_of_tateGSp (tateGSp_of_zl hZ hT)

end G0Galois
end
end G12DetDetSec


/-! ## Part 3: `TatePairingZl` from the leaves of scratch/weil-pairing -/

namespace G0Galois

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj

/-- **`TatePairingZl` from T9 (restated), the isogeny quasi-inverse and divisibility** (as in
weil-pairing's `det_galRep_sq` / `g12_detInput_of_leaves`). -/
theorem tatePairingZl_of_leaves (h9 : WeilPairing.T09_SymmIsogenyExists)
    (hQ : WeilPairing.IsogenyQuasiInverse) (hD : WeilPairing.DivisiblePoints) : TatePairingZl := by
  intro K _ _ A ℓ _
  haveI : NeZero (ℓ : K) := ⟨by exact_mod_cast (Fact.out : ℓ.Prime).ne_zero⟩
  obtain ⟨S⟩ := h9 K A
  obtain ⟨d, hd, ψ, hψ, -⟩ := hQ K _ _ S.lam S.isogeny
  obtain ⟨g, hg⟩ := WeilPairing.exists_tmu_gen K ℓ
  refine ⟨(WeilPairing.tatePairing S.D S.lam (NeZero.ne _)).compr₂ (WeilPairing.tmuCoordLin hg),
    ?_, ?_, ?_⟩
  · intro x hx
    exact WeilPairing.tatePairing_left_ker S.D S.lam hd hψ (NeZero.ne _)
      (fun k t ht => WeilPairing.tate_surj (hD K A ℓ (Fact.out : ℓ.Prime).pos) k t ht) x
      fun y => WeilPairing.tmuCoordLin_injective hg (by rw [map_zero]; exact hx y)
  · intro x
    simp only [LinearMap.compr₂_apply]
    rw [WeilPairing.tatePairing_self S.D S.lam S.symm (NeZero.ne _) x, map_zero]
  · intro σ x y
    simp only [LinearMap.compr₂_apply]
    have h := congrArg (WeilPairing.tmuCoordLin hg)
      (WeilPairing.tatePairing_cyclotomic S.D S.lam σ x y)
    rw [map_smul, smul_eq_mul] at h
    exact h

/-- **`DetTate` from leaves**: T9 restated (`T09_SymmIsogenyExists`), `IsogenyQuasiInverse`,
`DivisiblePoints` (scratch/weil-pairing §4, §8) and T26 (`PkgI3.TateModuleFree`, Objects). -/
theorem detTate_of_leaves (h9 : WeilPairing.T09_SymmIsogenyExists)
    (hQ : WeilPairing.IsogenyQuasiInverse) (hD : WeilPairing.DivisiblePoints)
    (hT : PkgI3.TateModuleFree) : DetTate :=
  detTate_of_zl (tatePairingZl_of_leaves h9 hQ hD) hT

end G0Galois



section G12DetWeightSec
namespace G0Galois
open PkgI4 (GaloisRep GaloisChar)

/-! ### Named pieces -/

/-- `ρ'` is the twist `ψ ⊗ ρ`: `ρ'(σ) = ψ(σ) ρ(σ)`. -/
def IsTwist {ℓ : ℕ} [Fact ℓ.Prime] {n : ℕ} (ρ' : GaloisRep ℓ n) (ψ : GaloisChar ℓ)
    (ρ : GaloisRep ℓ n) : Prop :=
  ∀ σ, ρ'.mat σ = (ψ.toHom σ : PadicAlgCl ℓ) • ρ.mat σ

/-- `r` and `ρ'` are conjugate by a fixed matrix: `r(σ) = P ρ'(σ) P⁻¹`. -/
def IsConj {ℓ : ℕ} [Fact ℓ.Prime] {n : ℕ} (r ρ' : GaloisRep ℓ n) : Prop :=
  ∃ P : GL (Fin n) (PadicAlgCl ℓ), ∀ σ, r.toHom σ = P * ρ'.toHom σ * P⁻¹

/-- **The twist exists (GLUE, elementary).** `σ ↦ ψ(σ) ρ(σ)` is a continuous representation:
a homomorphism because scalars are central, continuous because `GL_n(ℚ̄_ℓ)` carries the topology
induced from `M_n × M_nᵐᵒᵖ` and `ψ`, `ψ⁻¹`, `ρ`, `ρ⁻¹` are continuous. -/
def TwistExists : Prop :=
  ∀ (ℓ : ℕ) [Fact ℓ.Prime] (n : ℕ) (ρ : GaloisRep ℓ n) (ψ : GaloisChar ℓ),
    ∃ ρ' : GaloisRep ℓ n, IsTwist ρ' ψ ρ

/-- **`r ≅ ψ ⊗ ρ_g` (GLUE, from T18 Chebotarev and T19 Brauer–Nesbitt).** If `r` is
irreducible, `ρ` semisimple and attached to `g`, `r` attached to `g` up to the twist `ψ` outside
`S`, and `ρ' = ψ ⊗ ρ`, then `r` and `ρ'` are conjugate. Argument (as in `g12Det_of`,
scratch/g0-mod-galois): `tr r = tr ρ'` at arithmetic Frobenius outside `S ∪ {p ∣ 5N}` (`ιC`
injective identifies the two `α`), hence everywhere (`eq_of_eq_on_arithFrob`, T18); `r` is
semisimple (Burnside-irreducible: an invariant subspace is invariant under `M₂(ℚ̄₅)`), `ρ'` is
semisimple (same invariant subspaces as `ρ`); Brauer–Nesbitt (T19, `G = G_ℚ`, `E = ℚ̄₅`). -/
def TwistConj : Prop :=
  ∀ (ℓ : ℕ) [Fact ℓ.Prime] (r ρ ρ' : GaloisRep ℓ 2) (ψ : GaloisChar ℓ)
    (ιC : PkgI4.Qbar →ₐ[ℚ] ℂ) (ιL : PkgI4.Qbar →ₐ[ℚ] PadicAlgCl ℓ) (N : ℕ) (k : ℤ)
    (g : PkgI4.CF N k) (S : Finset ℕ),
    0 < N → r.IsIrreducible → ρ.IsSemisimple → ρ.AttachedTo ιC ιL g →
    r.AttachedUpToTwist ψ ιC ιL g S → IsTwist ρ' ψ ρ → IsConj r ρ'

/-- **Hodge–Tate weights are invariant under conjugation (GLUE, about the definition
`PkgI4.LocalHasHTWeights`; STANDARD).** Enlarge the finite coefficient field `E` to contain the
entries of `P` and `P⁻¹` and use that `htMult` does not change under a finite extension of `E`
(`(ℂ_p(i) ⊗ V)^G` commutes with `E'/E` base change) nor under an `E'`-linear isomorphism. -/
def HTConj : Prop :=
  ∀ (ℓ : ℕ) [Fact ℓ.Prime] (n : ℕ) (r ρ' : GaloisRep ℓ n) (S : Multiset ℤ),
    IsConj r ρ' → r.HasHTWeightsAtSelf ℓ S → ρ'.HasHTWeightsAtSelf ℓ S

/-- **Sen weights of a twist (LEAF; Sen, *Continuous cohomology and p-adic Galois
representations*, Invent. Math. 62 (1980), §2 Thm 4 and Cor. (Hodge–Tate iff the Sen operator `Θ`
is semisimple with integer eigenvalues, the Hodge–Tate weights), with
`Θ_{ψ⊗V} = Θ_ψ + Θ_V` (Sen 1980 §2; Fontaine–Ouyang, *Theory of p-adic Galois representations*,
§2.4-2.5); numbering UNVERIFIED).** If `ρ` and `ρ' = ψ ⊗ ρ` (restricted to `G_{ℚ_p}`) are both
Hodge–Tate, with weight multisets `S`, `S'` of full size `n`, then `S' = S + s` for an integer
`s`. Consequence of the published theorems: the Sen operators satisfy `Θ_{ρ'} = Θ_ρ + s_ψ`, both
are semisimple with eigenvalue multisets `S`, `S'`, so `S' = S + s_ψ` in `ℂ_p`, and `s_ψ ∈ ℤ`
when `n ≥ 1` (for `n = 0`, `s = 0`). (Full size is needed: `HasHTWeights S` with `card S < n`
holds for non-Hodge–Tate `ρ`, and then the statement fails.) -/
def SenTwist : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (n : ℕ) (ρ ρ' : GaloisRep p n) (ψ : GaloisChar p)
    (S S' : Multiset ℤ),
    IsTwist ρ' ψ ρ → Multiset.card S = n → Multiset.card S' = n →
    ρ.HasHTWeightsAtSelf p S → ρ'.HasHTWeightsAtSelf p S' →
    ∃ s : ℤ, S' = S.map (· + s)

/-- **Finite image implies Hodge–Tate of weight 0 (LEAF; Tate, *p-divisible groups* (1967) §3
Thm 2 (`ℂ_p(i)^{G_L} = 0` for `i ≠ 0`) and Ax–Sen–Tate (`ℂ_p^{G_L} = L`), with Hilbert 90 for
the finite extension cut out by the image; Fontaine–Ouyang Prop. 2.15 / Sen 1980 Cor. of Thm 11;
numbering UNVERIFIED).** A representation of `G_ℚ` with finite image is Hodge–Tate at `p` with all
weights `0` (its image lies in `GL_n(E)` for a finite `E/ℚ_p`: finitely many algebraic entries).
-/
def FiniteImageHT : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (n : ℕ) (ρ : GaloisRep p n),
    (Set.range ρ.toHom).Finite → ρ.HasHTWeightsAtSelf p (Multiset.replicate n 0)

/-! ### Proof -/

/-- The conclusion of `G12Weight` is `k = 2` (for `k ≥ 1`). -/
theorem g12Weight_concl_iff (k : ℤ) (hk : 1 ≤ k) :
    (∃ n : ℤ, ({n, n + 1 - k} : Multiset ℤ) = {0, -1}) ↔ k = 2 := by
  constructor
  · rintro ⟨n, hn⟩
    have h0 : (0 : ℤ) ∈ ({n, n + 1 - k} : Multiset ℤ) := by rw [hn]; simp
    have h1 : (-1 : ℤ) ∈ ({n, n + 1 - k} : Multiset ℤ) := by rw [hn]; simp
    have hc : ((n + 1 - k : ℤ) ∈ ({0, -1} : Multiset ℤ)) := by rw [← hn]; simp
    simp only [Multiset.insert_eq_cons, Multiset.mem_cons, Multiset.mem_singleton] at h0 h1 hc
    omega
  · rintro rfl
    exact ⟨0, by norm_num⟩

/-- **`G12Weight` from the named pieces** (and the leaves R14, R13, R15 it takes). -/
theorem g12Weight_of (hTE : TwistExists) (hTC : TwistConj) (hHC : HTConj) (hSen : SenTwist)
    (hFI : FiniteImageHT) : G12Weight := by
  intro hR hHT hDS _hFD _hBN r N k χ g ψ ιC ιL S hN hk hg hirr hw hatt
  obtain ⟨ρH, hss, hρatt⟩ := hR 5 ιC ιL N k χ g hN hk hg
  let ρ : GaloisRep 5 2 := ⟨ρH.toHom, ρH.continuous_toHom⟩
  have hss' : ρ.IsSemisimple := hss
  have hatt' : ρ.AttachedTo ιC ιL g := hρatt
  obtain ⟨ρ', htw⟩ := hTE 5 2 ρ ψ
  have hconj : IsConj r ρ' := hTC 5 r ρ ρ' ψ ιC ιL N k g S hN hirr hss' hatt' hatt htw
  have hw' : ρ'.HasHTWeightsAtSelf 5 {0, -1} := hHC 5 2 r ρ' _ hconj hw
  rcases eq_or_lt_of_le hk with h1 | h2
  · -- weight one: `ρ_g` has finite image, so `ψ ⊗ ρ_g` would have equal weights
    exfalso
    subst h1
    have hfin : (Set.range ρH.toHom).Finite := hDS 5 ιC ιL ρH N χ g hN hg hss hρatt
    have h0 : ρ.HasHTWeightsAtSelf 5 (Multiset.replicate 2 0) := hFI 5 2 ρ hfin
    obtain ⟨s, hs⟩ := hSen 5 2 ρ ρ' ψ _ _ htw (by simp) (by simp) h0 hw'
    have ha : (0 : ℤ) ∈ ({0, -1} : Multiset ℤ) := by simp
    have hb : (-1 : ℤ) ∈ ({0, -1} : Multiset ℤ) := by simp
    rw [hs] at ha hb
    simp only [Multiset.mem_map, Multiset.mem_replicate] at ha hb
    obtain ⟨a, ⟨-, rfl⟩, ha⟩ := ha
    obtain ⟨b, ⟨-, rfl⟩, hb⟩ := hb
    omega
  · -- weight `k ≥ 2`: weights `{0, 1 − k} + s = {0, −1}`
    have h := hHT 5 ιC ιL N k χ g ρ hN (by omega) hg hss' hatt'
    obtain ⟨s, hs⟩ := hSen 5 2 ρ ρ' ψ _ _ htw (by simp) (by simp) h hw'
    refine ⟨s, ?_⟩
    rw [hs]
    simp only [Multiset.insert_eq_cons, Multiset.map_cons, Multiset.map_singleton]
    congr 1
    · ring
    · congr 1; ring

end G0Galois
end G12DetWeightSec


section G12DetTwistSec
noncomputable section
namespace G0Galois
open PkgI4 (GaloisRep GaloisChar)

/-! ### `TwistExists` -/

/-- Scalar matrices as units. -/
def scalarU {ℓ : ℕ} [Fact ℓ.Prime] (n : ℕ) : (PadicAlgCl ℓ)ˣ →* GL (Fin n) (PadicAlgCl ℓ) :=
  Units.map (Matrix.scalar (Fin n) : PadicAlgCl ℓ →+* Matrix (Fin n) (Fin n) (PadicAlgCl ℓ))

lemma scalarU_commute {ℓ : ℕ} [Fact ℓ.Prime] {n : ℕ} (u : (PadicAlgCl ℓ)ˣ)
    (M : GL (Fin n) (PadicAlgCl ℓ)) : Commute (scalarU n u) M := by
  apply Units.ext
  simp only [Units.val_mul, scalarU, Units.coe_map, MonoidHom.coe_coe]
  exact Matrix.scalar_commute _ (fun r => Commute.all _ r) _

/-- `σ ↦ ψ(σ) ρ(σ)`. -/
def twistHom {ℓ : ℕ} [Fact ℓ.Prime] {n : ℕ} (ρ : GaloisRep ℓ n) (ψ : GaloisChar ℓ) :
    PkgI4.GQ →* GL (Fin n) (PadicAlgCl ℓ) where
  toFun σ := scalarU n (ψ.toHom σ) * ρ.toHom σ
  map_one' := by simp
  map_mul' σ τ := by
    simp only [map_mul, mul_assoc]
    congr 1
    rw [← mul_assoc, (scalarU_commute (ψ.toHom τ) (ρ.toHom σ)).eq, mul_assoc]

lemma twistHom_val {ℓ : ℕ} [Fact ℓ.Prime] {n : ℕ} (ρ : GaloisRep ℓ n) (ψ : GaloisChar ℓ)
    (σ : PkgI4.GQ) :
    ((twistHom ρ ψ σ : GL (Fin n) (PadicAlgCl ℓ)) : Matrix (Fin n) (Fin n) (PadicAlgCl ℓ)) =
      (ψ.toHom σ : PadicAlgCl ℓ) • ρ.mat σ := by
  change ((scalarU n (ψ.toHom σ) * ρ.toHom σ : GL (Fin n) (PadicAlgCl ℓ)) :
    Matrix (Fin n) (Fin n) (PadicAlgCl ℓ)) = _
  rw [Units.val_mul]
  simp only [scalarU, Units.coe_map, MonoidHom.coe_coe, Matrix.scalar_apply,
    PkgI4.GaloisRep.mat]
  rw [Matrix.smul_eq_diagonal_mul]

/-- **`TwistExists`, proved.** -/
theorem twistExists : TwistExists := by
  intro ℓ _ n ρ ψ
  have hv : Continuous fun σ =>
      ((twistHom ρ ψ σ : GL (Fin n) (PadicAlgCl ℓ)) : Matrix (Fin n) (Fin n) (PadicAlgCl ℓ)) := by
    simp only [twistHom_val]
    exact (Units.continuous_val.comp ψ.continuous_toHom).smul (continuous_mat ρ)
  refine ⟨⟨twistHom ρ ψ, Units.continuous_iff.mpr ⟨hv, ?_⟩⟩, fun σ => twistHom_val ρ ψ σ⟩
  have : (fun σ => (((twistHom ρ ψ σ)⁻¹ : GL (Fin n) (PadicAlgCl ℓ)) :
      Matrix (Fin n) (Fin n) (PadicAlgCl ℓ))) =
      (fun σ => ((twistHom ρ ψ σ : GL (Fin n) (PadicAlgCl ℓ)) :
        Matrix (Fin n) (Fin n) (PadicAlgCl ℓ))) ∘ (fun σ => σ⁻¹) := by
    funext σ; simp [map_inv]
  rw [this]
  exact hv.comp continuous_inv

/-! ### `TwistConj` from T18 and T19 -/

/-- Invariance under all matrices of an algebra generated by the image. -/
lemma invariant_of_irreducible {ℓ : ℕ} [Fact ℓ.Prime] {n : ℕ} (r : GaloisRep ℓ n)
    (hirr : r.IsIrreducible) (W : Submodule (PadicAlgCl ℓ) (Fin n → PadicAlgCl ℓ))
    (hW : ∀ σ, W.map (Matrix.toLin' (r.mat σ)) ≤ W) :
    ∀ M : Matrix (Fin n) (Fin n) (PadicAlgCl ℓ), ∀ x ∈ W, M.mulVec x ∈ W := by
  let S : Subalgebra (PadicAlgCl ℓ) (Matrix (Fin n) (Fin n) (PadicAlgCl ℓ)) :=
    { carrier := {M | ∀ x ∈ W, M.mulVec x ∈ W}
      mul_mem' := by
        intro a b ha hb x hx
        rw [← Matrix.mulVec_mulVec]
        exact ha _ (hb x hx)
      add_mem' := by
        intro a b ha hb x hx
        rw [Matrix.add_mulVec]
        exact W.add_mem (ha x hx) (hb x hx)
      algebraMap_mem' := by
        intro c x hx
        rw [Algebra.algebraMap_eq_smul_one, Matrix.smul_mulVec, Matrix.one_mulVec]
        exact W.smul_mem c hx }
  have hle : Algebra.adjoin (PadicAlgCl ℓ) (Set.range r.mat) ≤ S := by
    rw [Algebra.adjoin_le_iff]
    rintro _ ⟨σ, rfl⟩ x hx
    exact hW σ ⟨x, hx, rfl⟩
  intro M x hx
  have hM : M ∈ S := hle (hirr ▸ Algebra.mem_top)
  exact hM x hx

/-- An irreducible (Burnside form) representation is semisimple. -/
lemma isSemisimple_of_irreducible {ℓ : ℕ} [Fact ℓ.Prime] {n : ℕ} (r : GaloisRep ℓ n)
    (hirr : r.IsIrreducible) : r.IsSemisimple := by
  intro W hW
  have hinv := invariant_of_irreducible r hirr W hW
  by_cases h : W = ⊥
  · subst h
    exact ⟨⊤, isCompl_bot_top, fun σ => le_top⟩
  · have htop : W = ⊤ := by
      obtain ⟨w, hw, hw0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot h
      obtain ⟨i, hi⟩ : ∃ i, w i ≠ 0 := by
        by_contra hc
        push Not at hc
        exact hw0 (funext hc)
      rw [eq_top_iff]
      intro v _
      let M : Matrix (Fin n) (Fin n) (PadicAlgCl ℓ) :=
        Matrix.of fun a b => if b = i then v a / w i else 0
      have hMw : M.mulVec w = v := by
        funext a
        simp [M, Matrix.mulVec, dotProduct, div_mul_cancel₀ _ hi]
      rw [← hMw]
      exact hinv M w hw
    subst htop
    exact ⟨⊥, isCompl_top_bot, fun σ => by simp⟩

/-- A twist of a semisimple representation by a character is semisimple. -/
lemma isSemisimple_twist {ℓ : ℕ} [Fact ℓ.Prime] {n : ℕ} (ρ ρ' : GaloisRep ℓ n) (ψ : GaloisChar ℓ)
    (hss : ρ.IsSemisimple) (htw : IsTwist ρ' ψ ρ) : ρ'.IsSemisimple := by
  have key : ∀ (W : Submodule (PadicAlgCl ℓ) (Fin n → PadicAlgCl ℓ)) σ,
      W.map (Matrix.toLin' (ρ'.mat σ)) ≤ W ↔ W.map (Matrix.toLin' (ρ.mat σ)) ≤ W := by
    intro W σ
    have hu : (ψ.toHom σ : PadicAlgCl ℓ) ≠ 0 := Units.ne_zero _
    simp only [Submodule.map_le_iff_le_comap, htw σ]
    constructor
    · intro h x hx
      have := W.smul_mem ((ψ.toHom σ : PadicAlgCl ℓ))⁻¹ (h hx)
      simpa [Matrix.toLin'_apply, Matrix.smul_mulVec, smul_smul, inv_mul_cancel₀ hu] using this
    · intro h x hx
      have := W.smul_mem ((ψ.toHom σ : PadicAlgCl ℓ)) (h hx)
      simpa [Matrix.toLin'_apply, Matrix.smul_mulVec] using this
  intro W hW
  obtain ⟨W', hc, hW'⟩ := hss W (fun σ => (key W σ).1 (hW σ))
  exact ⟨W', hc, fun σ => (key W' σ).2 (hW' σ)⟩

/-- **`TwistConj` from T18 (Chebotarev) and T19 (Brauer–Nesbitt), proved.** -/
theorem twistConj_of (hD : HSyn.FrobeniusDense) (hBN : HSyn.BrauerNesbitt) : TwistConj := by
  intro ℓ _ r ρ ρ' ψ ιC ιL N k g S hN hirr hss hρatt hatt htw
  have hNl : N * ℓ ≠ 0 := Nat.mul_ne_zero (by omega) (Fact.out : ℓ.Prime).ne_zero
  have htr : ∀ x, (r.mat x).trace = (ρ'.mat x).trace := by
    have h := eq_of_eq_on_arithFrob (frobeniusDenseQ_of hD) (S ∪ (N * ℓ).primeFactors)
      (fun x => (r.mat x).trace) (fun x => (ρ'.mat x).trace)
      (continuous_mat r).matrix_trace (continuous_mat ρ').matrix_trace
      (by
        intro p hp hpS v τ hv hτ
        have hpS1 : p ∉ S := fun h => hpS (Finset.mem_union_left _ h)
        have hpN : ¬ p ∣ N * ℓ := fun h =>
          hpS (Finset.mem_union_right _ (Nat.mem_primeFactors.mpr ⟨hp, h, hNl⟩))
        obtain ⟨-, α, hα, hαt⟩ := hatt p hp hpS1
        obtain ⟨-, α', hα', hα't⟩ := hρatt p hp hpN
        have hαα : α = α' := ιC.toRingHom.injective (hα.trans hα'.symm)
        rw [hαt v τ hv hτ, htw τ, Matrix.trace_smul, hα't v τ hv hτ, hαα, smul_eq_mul])
    exact fun x => congrFun h x
  have hss' : ρ'.IsSemisimple := isSemisimple_twist ρ ρ' ψ hss htw
  have hssr : r.IsSemisimple := isSemisimple_of_irreducible r hirr
  obtain ⟨P, hP⟩ := hBN PkgI4.GQ (PadicAlgCl ℓ) 2 ρ'.toHom r.toHom hss' hssr
    (fun σ => (htr σ).symm)
  exact ⟨P, hP⟩

/-- **`G12Weight` from `HTConj`, `SenTwist`, `FiniteImageHT`** (`TwistExists` proved; `TwistConj`
from the T18 and T19 that `G12Weight` itself takes). -/
theorem g12Weight_of_HT (hHC : HTConj) (hSen : SenTwist) (hFI : FiniteImageHT) : G12Weight := by
  intro hR hHT hDS hFD hBN
  exact g12Weight_of twistExists (twistConj_of hFD hBN) hHC hSen hFI hR hHT hDS hFD hBN

end G0Galois
end
end G12DetTwistSec


/-! ## g12-det: `HTConj` reduced to `HTExtend` (independence of the coefficient field) -/

section G12DetHTSec

noncomputable section

namespace G0Galois

open PkgI4 (GaloisRep GaloisChar)

/-- **Hodge–Tate multiplicities do not depend on the finite coefficient field (GLUE, about the
definition `PkgI4.LocalHasHTWeights`; STANDARD).** If a `ℚ̄_p`-valued `ρ` has a model `ρ_E` over a
finite `E ⊆ ℚ̄_p` with weights `S`, then for every finite `E' ⊇ E` the model over `E'` (the same
matrices) has weights `S`. Argument: `E' ⊗_E E^n ≅ (E^n)^{[E':E]}` as `ℚ_p[G]`-modules (`G` acts
trivially on `E'`), so `dim_{ℚ_p} H_i(ρ_{E'}) = [E':E] dim_{ℚ_p} H_i(ρ_E)` and `htMult`, which divides
by `[E':ℚ_p]`, is unchanged. (The docstring of `LocalHasHTWeights` asserts this, STANDARD.) -/
def HTExtend : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (n : ℕ) (ρ : PkgI4.GQp p →* GL (Fin n) (PadicAlgCl p))
    (S : Multiset ℤ) (E E' : IntermediateField ℚ_[p] (PadicAlgCl p))
    [FiniteDimensional ℚ_[p] E] [FiniteDimensional ℚ_[p] E'], E ≤ E' →
    ∀ ρE : PkgI4.GQp p →* GL (Fin n) E,
      (∀ σ, Matrix.GeneralLinearGroup.map (algebraMap E (PadicAlgCl p)) (ρE σ) = ρ σ) →
      PkgI4.HasHTWeights p ρE S →
      ∃ ρE' : PkgI4.GQp p →* GL (Fin n) E',
        (∀ σ, Matrix.GeneralLinearGroup.map (algebraMap E' (PadicAlgCl p)) (ρE' σ) = ρ σ) ∧
        PkgI4.HasHTWeights p ρE' S

/-- Conjugating a model by `P ∈ GL_n(E)` does not change the Hodge–Tate spaces' dimensions. -/
lemma finrank_htSpace_conj {p : ℕ} [Fact p.Prime] {n : ℕ} {E : Type*} [Field E]
    [Algebra ℚ_[p] E] [FiniteDimensional ℚ_[p] E]
    (ρ ρ' : PkgI4.GQp p →* GL (Fin n) E) (P : GL (Fin n) E)
    (h : ∀ σ, ρ' σ = P⁻¹ * ρ σ * P) (i : ℤ) :
    Module.finrank ℚ_[p] (PkgI4.htSpace p ρ' i) = Module.finrank ℚ_[p] (PkgI4.htSpace p ρ i) := by
  let A : Matrix (Fin n) (Fin n) E := (P : Matrix (Fin n) (Fin n) E)
  let B : Matrix (Fin n) (Fin n) E := ((P⁻¹ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E)
  have hAB : A * B = 1 := by simp [A, B]
  have hBA : B * A = 1 := by simp [A, B]
  have hρ' : ∀ σ, ((ρ' σ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) =
      B * (ρ σ : Matrix (Fin n) (Fin n) E) * A := by
    intro σ; rw [h σ]; simp [A, B]
  let LA : (Fin n → E) →ₗ[ℚ_[p]] (Fin n → E) := (Matrix.mulVecLin A).restrictScalars ℚ_[p]
  let LB : (Fin n → E) →ₗ[ℚ_[p]] (Fin n → E) := (Matrix.mulVecLin B).restrictScalars ℚ_[p]
  let TA := LinearMap.lcomp ℚ_[p] ℂ_[p] LA
  let TB := LinearMap.lcomp ℚ_[p] ℂ_[p] LB
  have hTA : ∀ φ ∈ PkgI4.htSpace p ρ i, TA φ ∈ PkgI4.htSpace p ρ' i := by
    intro φ hφ σ v
    have := hφ σ (A.mulVec v)
    simp only [TA, LA, LinearMap.lcomp_apply, LinearMap.coe_comp, Function.comp_apply,
      LinearMap.coe_restrictScalars, Matrix.mulVecLin_apply] at this ⊢
    rw [hρ', Matrix.mulVec_mulVec, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hAB, Matrix.one_mul,
      ← Matrix.mulVec_mulVec]
    exact this
  have hTB : ∀ φ ∈ PkgI4.htSpace p ρ' i, TB φ ∈ PkgI4.htSpace p ρ i := by
    intro φ hφ σ v
    have := hφ σ (B.mulVec v)
    simp only [TB, LB, LinearMap.lcomp_apply, LinearMap.coe_comp, Function.comp_apply,
      LinearMap.coe_restrictScalars, Matrix.mulVecLin_apply] at this ⊢
    rw [hρ', Matrix.mulVec_mulVec, Matrix.mul_assoc _ A B, hAB, Matrix.mul_one] at this
    rw [Matrix.mulVec_mulVec]
    exact this
  let f : PkgI4.htSpace p ρ i →ₗ[ℚ_[p]] PkgI4.htSpace p ρ' i := TA.restrict hTA
  let g : PkgI4.htSpace p ρ' i →ₗ[ℚ_[p]] PkgI4.htSpace p ρ i := TB.restrict hTB
  have e : PkgI4.htSpace p ρ i ≃ₗ[ℚ_[p]] PkgI4.htSpace p ρ' i := LinearEquiv.ofLinear f g
    (by
      apply LinearMap.ext; intro φ; apply Subtype.ext; apply LinearMap.ext; intro v
      simp [f, g, TA, TB, LA, LB, Matrix.mulVec_mulVec, hAB, hBA])
    (by
      apply LinearMap.ext; intro φ; apply Subtype.ext; apply LinearMap.ext; intro v
      simp [f, g, TA, TB, LA, LB, Matrix.mulVec_mulVec, hAB, hBA])
  exact e.finrank_eq.symm

/-- **`HTConj` from `HTExtend`.** -/
theorem htConj_of (hX : HTExtend) : HTConj := by
  intro ℓ _ n r ρ' S hconj hr
  obtain ⟨P, hP⟩ := hconj
  obtain ⟨E, hEfd, ρE, hmap, hHT⟩ := hr
  let T : Set (PadicAlgCl ℓ) :=
    Set.range (fun ij : Fin n × Fin n => (P : Matrix (Fin n) (Fin n) (PadicAlgCl ℓ)) ij.1 ij.2) ∪
    Set.range (fun ij : Fin n × Fin n =>
      ((P⁻¹ : GL (Fin n) (PadicAlgCl ℓ)) : Matrix (Fin n) (Fin n) (PadicAlgCl ℓ)) ij.1 ij.2)
  have hTfin : Finite T := ((Set.finite_range _).union (Set.finite_range _)).to_subtype
  have hadj : FiniteDimensional ℚ_[ℓ] (IntermediateField.adjoin ℚ_[ℓ] T) :=
    IntermediateField.finiteDimensional_adjoin fun x _ => Algebra.IsIntegral.isIntegral x
  let E' : IntermediateField ℚ_[ℓ] (PadicAlgCl ℓ) := E ⊔ IntermediateField.adjoin ℚ_[ℓ] T
  have hE'fd : FiniteDimensional ℚ_[ℓ] E' := IntermediateField.finiteDimensional_sup _ _
  obtain ⟨ρE', hmap', hHT'⟩ := hX ℓ n (r.restrictLocal ℓ) S E E' le_sup_left ρE hmap hHT
  have hmemT : ∀ x ∈ T, x ∈ E' := fun x hx =>
    (le_sup_right : IntermediateField.adjoin ℚ_[ℓ] T ≤ E') (IntermediateField.subset_adjoin _ _ hx)
  let Pm : Matrix (Fin n) (Fin n) E' := Matrix.of fun i j =>
    ⟨(P : Matrix (Fin n) (Fin n) (PadicAlgCl ℓ)) i j, hmemT _ (Or.inl ⟨(i, j), rfl⟩)⟩
  let Qm : Matrix (Fin n) (Fin n) E' := Matrix.of fun i j =>
    ⟨((P⁻¹ : GL (Fin n) (PadicAlgCl ℓ)) : Matrix (Fin n) (Fin n) (PadicAlgCl ℓ)) i j,
      hmemT _ (Or.inr ⟨(i, j), rfl⟩)⟩
  let φ := algebraMap E' (PadicAlgCl ℓ)
  have hinj : Function.Injective (φ.mapMatrix : Matrix (Fin n) (Fin n) E' → _) := by
    intro M N hMN
    exact Matrix.ext fun i j => Subtype.ext (congrFun (congrFun hMN i) j)
  have hPm : φ.mapMatrix Pm = (P : Matrix (Fin n) (Fin n) (PadicAlgCl ℓ)) := by
    ext i j; rfl
  have hQm : φ.mapMatrix Qm =
      ((P⁻¹ : GL (Fin n) (PadicAlgCl ℓ)) : Matrix (Fin n) (Fin n) (PadicAlgCl ℓ)) := by
    ext i j; rfl
  have hPQ : Pm * Qm = 1 := hinj (by rw [map_mul, map_one, hPm, hQm]; simp)
  have hQP : Qm * Pm = 1 := hinj (by rw [map_mul, map_one, hPm, hQm]; simp)
  let P' : GL (Fin n) E' := ⟨Pm, Qm, hPQ, hQP⟩
  have hP' : Matrix.GeneralLinearGroup.map φ P' = P := by
    apply Units.ext
    exact hPm
  let ρ'E : PkgI4.GQp ℓ →* GL (Fin n) E' :=
    { toFun := fun σ => P'⁻¹ * ρE' σ * P'
      map_one' := by simp
      map_mul' := fun σ τ => by simp [mul_assoc] }
  refine ⟨E', hE'fd, ρ'E, ?_, ?_⟩
  · intro σ
    change Matrix.GeneralLinearGroup.map φ (P'⁻¹ * ρE' σ * P') = _
    rw [map_mul, map_mul, map_inv, hP', hmap' σ]
    change P⁻¹ * r.toHom (PkgI4.decomp ℓ σ) * P = ρ'.toHom (PkgI4.decomp ℓ σ)
    rw [hP]
    group
  · intro w
    unfold PkgI4.htMult
    rw [finrank_htSpace_conj ρE' ρ'E P' (fun σ => rfl) (-w)]
    exact hHT' w

end G0Galois

end

end G12DetHTSec



/-! ## g12-det: `HTExtend` proved (Hodge–Tate multiplicities do not depend on the coefficient
field) -/

section G12DetHTExtSec

noncomputable section

namespace G0Galois

section Extend

variable {p : ℕ} [Fact p.Prime] {n : ℕ} {E E' : Type} [Field E] [Field E'] [Algebra ℚ_[p] E]
  [Algebra ℚ_[p] E'] [Algebra E E'] [IsScalarTower ℚ_[p] E E'] [FiniteDimensional ℚ_[p] E]
  [FiniteDimensional ℚ_[p] E'] {m : ℕ} (b : Module.Basis (Fin m) E E')

/-- `v ↦ (v_a • b_k)_a`. -/
def jk (k : Fin m) : (Fin n → E) →ₗ[ℚ_[p]] (Fin n → E') :=
  (LinearMap.pi fun a => (LinearMap.toSpanSingleton E E' (b k)).comp (LinearMap.proj a) :
    (Fin n → E) →ₗ[E] (Fin n → E')).restrictScalars ℚ_[p]

/-- `w ↦ (b.coord k (w_a))_a`. -/
def ck (k : Fin m) : (Fin n → E') →ₗ[ℚ_[p]] (Fin n → E) :=
  (LinearMap.pi fun a => (b.coord k).comp (LinearMap.proj a) :
    (Fin n → E') →ₗ[E] (Fin n → E)).restrictScalars ℚ_[p]

omit [FiniteDimensional ℚ_[p] E] [FiniteDimensional ℚ_[p] E'] in
lemma jk_apply (k : Fin m) (v : Fin n → E) (a : Fin n) : jk (p := p) b k v a = v a • b k := rfl

omit [FiniteDimensional ℚ_[p] E] [FiniteDimensional ℚ_[p] E'] in
lemma ck_apply (k : Fin m) (w : Fin n → E') (a : Fin n) :
    ck (p := p) b k w a = b.repr (w a) k := rfl

omit [FiniteDimensional ℚ_[p] E] [FiniteDimensional ℚ_[p] E'] in
lemma jk_mulVec (k : Fin m) (M : Matrix (Fin n) (Fin n) E) (v : Fin n → E) :
    jk (p := p) b k (M.mulVec v) = (M.map (algebraMap E E')).mulVec (jk (p := p) b k v) := by
  funext a
  simp only [jk_apply, Matrix.mulVec, dotProduct, Matrix.map_apply, Finset.sum_smul]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [Algebra.smul_def, Algebra.smul_def, map_mul]
  ring

omit [FiniteDimensional ℚ_[p] E] [FiniteDimensional ℚ_[p] E'] in
lemma ck_mulVec (k : Fin m) (M : Matrix (Fin n) (Fin n) E) (w : Fin n → E') :
    ck (p := p) b k ((M.map (algebraMap E E')).mulVec w) = M.mulVec (ck (p := p) b k w) := by
  funext a
  simp only [ck_apply, Matrix.mulVec, dotProduct, Matrix.map_apply, map_sum,
    Finsupp.coe_finset_sum, Finset.sum_apply]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [← Algebra.smul_def, map_smul, Finsupp.smul_apply, smul_eq_mul]

omit [FiniteDimensional ℚ_[p] E] [FiniteDimensional ℚ_[p] E'] in
lemma ck_jk (k l : Fin m) (v : Fin n → E) :
    ck (p := p) b l (jk (p := p) b k v) = if k = l then v else 0 := by
  funext a
  rw [ck_apply, jk_apply, map_smul, Finsupp.smul_apply, Module.Basis.repr_self,
    Finsupp.single_apply, smul_eq_mul]
  split_ifs <;> simp

omit [FiniteDimensional ℚ_[p] E] [FiniteDimensional ℚ_[p] E'] in
lemma sum_jk_ck (w : Fin n → E') : ∑ k, jk (p := p) b k (ck (p := p) b k w) = w := by
  funext a
  simp only [Finset.sum_apply, jk_apply, ck_apply]
  exact b.sum_repr (w a)

/-- `htSpace` of the extended model is `htSpace` of the model, `m` times. -/
def htSpaceExtendEquiv (ρE : PkgI4.GQp p →* GL (Fin n) E) (i : ℤ) :
    PkgI4.htSpace p ((Matrix.GeneralLinearGroup.map (algebraMap E E')).comp ρE) i ≃ₗ[ℚ_[p]]
      (Fin m → PkgI4.htSpace p ρE i) where
  toFun φ k := ⟨φ.1.comp (jk (p := p) b k), by
    intro σ v
    have := φ.2 σ (jk (p := p) b k v)
    simp only [LinearMap.coe_comp, Function.comp_apply]
    rw [jk_mulVec]
    exact this⟩
  invFun ψ := ⟨∑ k, (ψ k).1.comp (ck (p := p) b k), by
    intro σ w
    simp only [LinearMap.sum_apply, LinearMap.coe_comp, Function.comp_apply,
      map_sum, Finset.smul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    have h := (ψ k).2 σ (ck (p := p) b k w)
    have hm : ((((Matrix.GeneralLinearGroup.map (algebraMap E E')).comp ρE) σ :
        GL (Fin n) E') : Matrix (Fin n) (Fin n) E') =
        ((ρE σ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E).map (algebraMap E E') := rfl
    rw [hm, ck_mulVec]
    exact h⟩
  left_inv φ := by
    apply Subtype.ext
    apply LinearMap.ext
    intro w
    simp only [LinearMap.sum_apply, LinearMap.coe_comp, Function.comp_apply]
    rw [← map_sum, sum_jk_ck]
  right_inv ψ := by
    funext k
    apply Subtype.ext
    apply LinearMap.ext
    intro v
    simp only [LinearMap.sum_apply, LinearMap.coe_comp, Function.comp_apply]
    rw [Finset.sum_eq_single k]
    · rw [ck_jk, if_pos rfl]
    · intro l _ hl
      rw [ck_jk, if_neg (Ne.symm hl), map_zero]
    · intro h; exact absurd (Finset.mem_univ k) h
  map_add' φ ψ := by
    funext k; apply Subtype.ext; rfl
  map_smul' c φ := by
    funext k; apply Subtype.ext; rfl

include b in
lemma htMult_extend (ρE : PkgI4.GQp p →* GL (Fin n) E) (w : ℤ) :
    PkgI4.htMult p ((Matrix.GeneralLinearGroup.map (algebraMap E E')).comp ρE) w =
      PkgI4.htMult p ρE w := by
  have hm : 0 < m := by
    by_contra h
    have h0 : m = 0 := by omega
    subst h0
    have := b.index_nonempty
    exact (IsEmpty.false this.some)
  unfold PkgI4.htMult
  rw [(htSpaceExtendEquiv b ρE (-w)).finrank_eq,
    ← (Finsupp.linearEquivFunOnFinite ℚ_[p] (PkgI4.htSpace p ρE (-w)) (Fin m)).finrank_eq,
    Module.finrank_finsupp, Fintype.card_fin, ← Module.finrank_mul_finrank ℚ_[p] E E',
    Module.finrank_eq_card_basis b, Fintype.card_fin, mul_comm (Module.finrank ℚ_[p] E) m]
  exact Nat.mul_div_mul_left _ _ hm

end Extend

/-- **`HTExtend`, proved.** -/
theorem htExtend : HTExtend := by
  intro p _ n ρ S E E' _ _ hle ρE hmap hHT
  letI : Algebra E E' := (IntermediateField.inclusion hle).toRingHom.toAlgebra
  haveI : IsScalarTower ℚ_[p] E E' := IsScalarTower.of_algebraMap_eq fun x => rfl
  haveI : Module.Finite E E' := Module.Finite.of_restrictScalars_finite ℚ_[p] E E'
  haveI : Module.Free E E' := Module.Free.of_divisionRing E E'
  let b := Module.finBasis E E'
  refine ⟨(Matrix.GeneralLinearGroup.map (algebraMap E E')).comp ρE, ?_, ?_⟩
  · intro σ
    rw [← hmap σ]
    apply Units.ext
    ext i j
    rfl
  · intro w
    rw [htMult_extend b ρE w]
    exact hHT w

end G0Galois

end

end G12DetHTExtSec



/-! ## g12-det: `G12Weight` from `HTExtend` and the two new leaves -/

namespace G0Galois

/-- **`G12Weight` from `HTExtend` (glue) and the leaves `SenTwist`, `FiniteImageHT`.** -/
theorem g12Weight_of_htExtend (hX : HTExtend) (hSen : SenTwist) (hFI : FiniteImageHT) :
    G12Weight :=
  g12Weight_of_HT (htConj_of hX) hSen hFI

/-- **`G12Weight` from the two new leaves `SenTwist` and `FiniteImageHT`** (with the leaves R13,
R14, R15, T18, T19 that `G12Weight` itself takes as hypotheses); all glue proved. -/
theorem g12Weight_of_senTwist (hSen : SenTwist) (hFI : FiniteImageHT) : G12Weight :=
  g12Weight_of_htExtend htExtend hSen hFI

end G0Galois

