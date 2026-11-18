import Mathlib
import ZInQKernel.Contrib.OneProof.RC.SelmerComplex.Cochains

/-!
# Lane RC26: corestriction as a cochain map

For a subgroup `U ≤ G` of finite index, a `G`-module `M` and a right transversal
`x ↦ x̂` of `U` in `G` (representatives of the right cosets `Ux`), corestriction on inhomogeneous
cochains is
```
(cor c)(g₁,…,gₙ) = ∑_{α ∈ U\G} α̂⁻¹ • c(α̂ g₁ (α̂g₁)^⁻¹, (α̂g₁)^ g₂ ((α̂g₁g₂)^)⁻¹, …,
                                     (α̂g₁⋯g_{n−1})^ gₙ ((α̂g₁⋯gₙ)^)⁻¹)
```
(Nekovář, *Selmer complexes*, Astérisque 310, 8.1.4; Brown, *Cohomology of Groups*, III.9).
Each argument lies in `U`.

Main results:

* `RightTransversal U`: a finite right transversal (with `RightTransversal.ofFiniteIndex`, one
  exists for every subgroup of finite index; `RightTransversal.card_T_eq_index`: it has `[G : U]`
  elements).
* `RightTransversal.corFun`: corestriction on plain functions `((Fin n → U) → M) → ((Fin n → G) → M)`.
* `RightTransversal.corFun_dFormula`, `RightTransversal.corFun_d`: **the chain-map identity**
  `cor (d c) = d (cor c)`, for Mathlib's inhomogeneous differentials (`U` acting on `M` by
  restriction, `G` acting on `M`). PROVED.
* `RightTransversal.corInhom`: corestriction as a cochain map of Mathlib's inhomogeneous cochain
  complexes. PROVED.
* `RightTransversal.corCochains`: for an open subgroup `U` of a topological group `G`, the cochain
  map `C^•_cont(U, M) → C^•_cont(G, M)` of continuous cochains (`U` acting on `M` through the
  inclusion, `ResMod`), with `RightTransversal.corCochains_ι` (compatibility with the inclusions
  into Mathlib's inhomogeneous cochains) and `RightTransversal.corCohomology`, the induced map on
  `Hⁿ_cont`. PROVED. (No discreteness of `M` is needed: the standing hypotheses of
  `contCochains`, which hold for a discrete `M` with continuous action, suffice.)
* `RightTransversal.corFun_zero`, `RightTransversal.corFun_const_zero`: in degree zero corestriction
  is the norm (trace) `m ↦ ∑_α α̂⁻¹ • m`; on `G`-invariant `m` it is `[G : U] • m`
  (`RightTransversal.corFun_const_zero_of_invariant_index`). PROVED.

Route: the arguments of `cor c` are written as `w(x_{i})⁻¹ w(x_{i+1})` with
`x_i = α̂ g₁⋯g_i` (partial products) and `w(x) = x (x̂)⁻¹ ∈ U`. Contracting two adjacent entries
of `g` deletes one partial product (`Fin.partialProd_contractNth`), so the face terms match
termwise; the leading term matches after the reindexing `α ↦ α g₀` of `U\G`.

Kinds: all declarations are genuine definitions or PROVED.
-/

noncomputable section

namespace ZInQ.Manuscript.RC.SelmerComplex

open CategoryTheory

universe u

section Transversal

variable {G : Type u} [Group G]

/-- **A finite right transversal** of a subgroup `U ≤ G`: a finite set `T` of representatives of
the right cosets `Ux` together with the representative map `x ↦ x̂ = hat x`, with `x̂ ∈ T`,
`x̂ ∈ Ux`, `x̂` depending only on `Ux`, and `t̂ = t` for `t ∈ T` (the data used to define
corestriction in Nekovář, *Selmer complexes*, 8.1.4, and Brown, *Cohomology of Groups*, III.9).
It exists exactly when `U` has finite index (`RightTransversal.ofFiniteIndex`). -/
structure RightTransversal (U : Subgroup G) where
  /-- The finite set of representatives of the right cosets of `U`. -/
  T : Finset G
  /-- The representative map `x ↦ x̂`. -/
  hat : G → G
  /-- Representatives lie in `T`. -/
  hat_mem : ∀ x, hat x ∈ T
  /-- `x̂ ∈ U x`. -/
  hat_mul_inv_mem : ∀ x, hat x * x⁻¹ ∈ U
  /-- `x̂` depends only on the right coset `U x`. -/
  hat_eq : ∀ x y, y * x⁻¹ ∈ U → hat y = hat x
  /-- Elements of `T` are their own representatives. -/
  hat_self : ∀ t ∈ T, hat t = t

namespace RightTransversal

variable {U : Subgroup G} (R : RightTransversal U)

/-- `(x̂ y)^ = (x y)^`: the representative of `x̂ y` only depends on the coset `U x y`
(Brown III.9). -/
theorem hat_hat_mul (x y : G) : R.hat (R.hat x * y) = R.hat (x * y) := by
  apply R.hat_eq
  have e : R.hat x * y * (x * y)⁻¹ = R.hat x * x⁻¹ := by group
  rw [e]
  exact R.hat_mul_inv_mem x

/-- The representative map is idempotent. -/
theorem hat_hat (x : G) : R.hat (R.hat x) = R.hat x :=
  R.hat_self _ (R.hat_mem x)

/-- **Reindexing over `U\G`.** Right multiplication by `g` permutes the right cosets, so
`∑_{t ∈ T} F((t g)^) = ∑_{t ∈ T} F(t)` (Brown III.9). -/
theorem sum_hat_mul {A : Type*} [AddCommMonoid A] (F : G → A) (g : G) :
    ∑ t ∈ R.T, F (R.hat (t * g)) = ∑ t ∈ R.T, F t := by
  refine Finset.sum_nbij' (fun t => R.hat (t * g)) (fun t => R.hat (t * g⁻¹)) ?_ ?_ ?_ ?_ ?_
  · intro t _
    exact R.hat_mem _
  · intro t _
    exact R.hat_mem _
  · intro t ht
    rw [R.hat_hat_mul, mul_inv_cancel_right, R.hat_self t ht]
  · intro t ht
    rw [R.hat_hat_mul, inv_mul_cancel_right, R.hat_self t ht]
  · intro t _
    rfl

/-- The `U`-component `w(x) = x (x̂)⁻¹ ∈ U` of `x ∈ G = ⋃ U t`. -/
def uPart (x : G) : U :=
  ⟨x * (R.hat x)⁻¹, by simpa [mul_inv_rev] using U.inv_mem (R.hat_mul_inv_mem x)⟩

/-- The `U`-component of `x` is `x (x̂)⁻¹`. -/
@[simp]
theorem coe_uPart (x : G) : (R.uPart x : G) = x * (R.hat x)⁻¹ :=
  rfl

/-- **The arguments of corestriction** (Nekovář 8.1.4, Brown III.9): for `t ∈ G` and
`g = (g₁,…,gₙ)`, the `i`-th argument `w(x_i)⁻¹ w(x_{i+1}) ∈ U`, where `x_i = t g₁⋯g_i` (a partial
product) and `w(x) = x (x̂)⁻¹`. By `coe_corArg` it is `x̂_i g_{i+1} (x̂_{i+1})⁻¹`. -/
def corArg {n : ℕ} (t : G) (g : Fin n → G) (i : Fin n) : U :=
  (R.uPart (t * Fin.partialProd g i.castSucc))⁻¹ * R.uPart (t * Fin.partialProd g i.succ)

/-- The arguments of corestriction in the form of Nekovář 8.1.4:
`(t g₁⋯g_i)^ g_{i+1} ((t g₁⋯g_{i+1})^)⁻¹`. -/
theorem coe_corArg {n : ℕ} (t : G) (g : Fin n → G) (i : Fin n) :
    (R.corArg t g i : G) =
      R.hat (t * Fin.partialProd g i.castSucc) * g i * (R.hat (t * Fin.partialProd g i.succ))⁻¹ := by
  simp only [corArg, Subgroup.coe_mul, Subgroup.coe_inv, coe_uPart, Fin.partialProd_succ]
  group

/-- **Corestriction on cochains** (Nekovář, *Selmer complexes*, 8.1.4; Brown, *Cohomology of
Groups*, III.9): for a function `c : Uⁿ → M`,
`(cor c)(g₁,…,gₙ) = ∑_{t ∈ T} t⁻¹ • c(t g₁ (t g₁)^⁻¹, …, (t g₁⋯g_{n−1})^ gₙ ((t g₁⋯gₙ)^)⁻¹)`,
the sum over the representatives `t = α̂` of the right cosets `α ∈ U\G`. -/
def corFun {M : Type*} [AddCommMonoid M] [DistribMulAction G M] {n : ℕ}
    (c : (Fin n → U) → M) : (Fin n → G) → M :=
  fun g => ∑ t ∈ R.T, t⁻¹ • c (R.corArg t g)

/-- Unfolding `corFun`. -/
theorem corFun_apply {M : Type*} [AddCommMonoid M] [DistribMulAction G M] {n : ℕ}
    (c : (Fin n → U) → M) (g : Fin n → G) :
    R.corFun c g = ∑ t ∈ R.T, t⁻¹ • c (R.corArg t g) :=
  rfl

/-! ### The chain-map identity -/

/-- Contracting two adjacent entries of a sequence of quotients `s_i⁻¹ s_{i+1}` deletes one
entry of `s`: the combinatorial identity behind the face terms of the chain-map identity. -/
theorem contractNth_inv_mul {H : Type*} [Group H] {m : ℕ} (s : Fin (m + 2) → H)
    (j : Fin (m + 1)) (k : Fin m) :
    Fin.contractNth j (· * ·) (fun i : Fin (m + 1) => (s i.castSucc)⁻¹ * s i.succ) k =
      (s (j.succ.succAbove k.castSucc))⁻¹ * s (j.succ.succAbove k.succ) := by
  rcases lt_trichotomy (k : ℕ) j with h | h | h
  · have h1 : (k.castSucc.castSucc : Fin (m + 2)) < j.succ := by
      simp only [Fin.lt_def, Fin.val_castSucc, Fin.val_succ]; omega
    have h2 : (k.succ.castSucc : Fin (m + 2)) < j.succ := by
      simp only [Fin.lt_def, Fin.val_castSucc, Fin.val_succ]; omega
    rw [Fin.contractNth_apply_of_lt _ _ _ _ h, Fin.succAbove_of_castSucc_lt _ _ h1,
      Fin.succAbove_of_castSucc_lt _ _ h2]
    rfl
  · have h1 : (k.castSucc.castSucc : Fin (m + 2)) < j.succ := by
      simp only [Fin.lt_def, Fin.val_castSucc, Fin.val_succ]; omega
    have h2 : j.succ ≤ (k.succ.castSucc : Fin (m + 2)) := by
      simp only [Fin.le_def, Fin.val_castSucc, Fin.val_succ]; omega
    rw [Fin.contractNth_apply_of_eq _ _ _ _ h, Fin.succAbove_of_castSucc_lt _ _ h1,
      Fin.succAbove_of_le_castSucc _ _ h2]
    have e : (k.castSucc.succ : Fin (m + 2)) = k.succ.castSucc := rfl
    rw [e, mul_assoc, mul_inv_cancel_left]
  · have h1 : j.succ ≤ (k.castSucc.castSucc : Fin (m + 2)) := by
      simp only [Fin.le_def, Fin.val_castSucc, Fin.val_succ]; omega
    have h2 : j.succ ≤ (k.succ.castSucc : Fin (m + 2)) := by
      simp only [Fin.le_def, Fin.val_castSucc, Fin.val_succ]; omega
    rw [Fin.contractNth_apply_of_gt _ _ _ _ h, Fin.succAbove_of_le_castSucc _ _ h1,
      Fin.succAbove_of_le_castSucc _ _ h2]
    rfl

/-- **Face terms.** The arguments of corestriction commute with contraction:
`corArg t (… , g_j g_{j+1}, …) = (… , corArg_j · corArg_{j+1}, …)`. -/
theorem corArg_contractNth {n : ℕ} (t : G) (g : Fin (n + 1) → G) (j : Fin (n + 1)) :
    R.corArg t (Fin.contractNth j (· * ·) g) = Fin.contractNth j (· * ·) (R.corArg t g) := by
  funext k
  have e : R.corArg t g = fun i => (R.uPart (t * Fin.partialProd g i.castSucc))⁻¹ *
      R.uPart (t * Fin.partialProd g i.succ) := rfl
  rw [e, contractNth_inv_mul (fun i => R.uPart (t * Fin.partialProd g i)) j k]
  simp only [corArg, Fin.partialProd_contractNth, Function.comp_apply]

/-- **Leading term, arguments.** Dropping the first argument of `corArg t g` gives the
arguments for the representative `(t g₀)^` and the tail `(g₁,…,gₙ)`. -/
theorem corArg_succ {n : ℕ} (t : G) (g : Fin (n + 1) → G) (i : Fin n) :
    R.corArg t g i.succ = R.corArg (R.hat (t * g 0)) (fun i => g i.succ) i := by
  apply Subtype.ext
  simp only [coe_corArg, R.hat_hat_mul]
  have e : (i.succ.castSucc : Fin (n + 2)) = i.castSucc.succ := rfl
  rw [e, Fin.partialProd_succ' g, Fin.partialProd_succ' g]
  simp only [mul_assoc]
  rfl

/-- **Leading term, coefficient.** For `t ∈ T`, `t⁻¹ · corArg t g 0 = g₀ ((t g₀)^)⁻¹`. -/
theorem inv_mul_coe_corArg_zero {n : ℕ} {t : G} (ht : t ∈ R.T) (g : Fin (n + 1) → G) :
    t⁻¹ * (R.corArg t g 0 : G) = g 0 * (R.hat (t * g 0))⁻¹ := by
  rw [coe_corArg]
  have e1 : Fin.partialProd g (Fin.castSucc 0) = 1 := Fin.partialProd_zero g
  have e2 : Fin.partialProd g (Fin.succ 0) = g 0 := by
    rw [Fin.partialProd_succ, e1, one_mul]
  rw [e1, e2, mul_one, R.hat_self t ht]
  group

variable {k : Type*} [CommRing k] {M : Type*} [AddCommGroup M] [Module k M]
  [DistribMulAction G M] [SMulCommClass G k M]

/-- **The chain-map identity `cor (d c) = d (cor c)`** (Nekovář, *Selmer complexes*, 8.1.4;
Brown, *Cohomology of Groups*, III.9), written out with Mathlib's inhomogeneous differential
`(df)(g₀,…,gₙ) = g₀ • f(g₁,…,gₙ) + ∑_j (−1)^{j+1} f(…, g_j g_{j+1}, …)`, with `U` acting on `M`
through `U ≤ G` on the left-hand side and `G` acting on `M` on the right-hand side. PROVED. -/
theorem corFun_dFormula {n : ℕ} (c : (Fin n → U) → M) (g : Fin (n + 1) → G) :
    R.corFun (fun x : Fin (n + 1) → U => ((x 0 : U) : G) • c (fun i => x i.succ) +
        ∑ j : Fin (n + 1), (-1 : k) ^ ((j : ℕ) + 1) • c (Fin.contractNth j (· * ·) x)) g =
      g 0 • R.corFun c (fun i => g i.succ) +
        ∑ j : Fin (n + 1), (-1 : k) ^ ((j : ℕ) + 1) • R.corFun c (Fin.contractNth j (· * ·) g) := by
  simp only [corFun, smul_add, Finset.sum_add_distrib, Finset.smul_sum]
  congr 1
  · refine Eq.trans ?_
      (R.sum_hat_mul (fun s => g 0 • s⁻¹ • c (R.corArg s fun i => g i.succ)) (g 0))
    refine Finset.sum_congr rfl fun t ht => ?_
    rw [smul_smul, smul_smul, R.inv_mul_coe_corArg_zero ht g,
      show (fun i => R.corArg t g i.succ) = R.corArg (R.hat (t * g 0)) (fun i => g i.succ) from
        funext (R.corArg_succ t g)]
  · rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => ?_
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [smul_comm, R.corArg_contractNth]

/-! ### Degree zero: the norm -/

section DegreeZero

variable {A : Type*} [AddCommMonoid A] [DistribMulAction G A]

/-- **Degree zero** (Nekovář 8.1.4, Brown III.9): on `0`-cochains (functions on the one-point
set `U⁰`) corestriction is the norm `∑_{α ∈ U\G} α̂⁻¹ • c()`. PROVED. -/
theorem corFun_zero (c : (Fin 0 → U) → A) (g : Fin 0 → G) :
    R.corFun c g = ∑ t ∈ R.T, t⁻¹ • c Fin.elim0 := by
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [Subsingleton.elim (R.corArg t g) Fin.elim0]

/-- **Degree zero, constant cochains:** corestriction of the `0`-cochain with value `m` is the
norm (trace) `∑_{α ∈ U\G} α̂⁻¹ • m` (Nekovář 8.1.4, Brown III.9). PROVED. -/
theorem corFun_const_zero (m : A) (g : Fin 0 → G) :
    R.corFun (fun _ : Fin 0 → U => m) g = ∑ t ∈ R.T, t⁻¹ • m :=
  rfl

/-- **Degree zero, `G`-invariant values:** for `m` fixed by `G`, corestriction of the constant
`0`-cochain `m` is `|U\G| • m = [G : U] • m` (cor ∘ res is multiplication by the index on `H⁰`;
Brown III.9). PROVED. -/
theorem corFun_const_zero_of_invariant (m : A) (hm : ∀ x : G, x • m = m) (g : Fin 0 → G) :
    R.corFun (fun _ : Fin 0 → U => m) g = R.T.card • m := by
  rw [corFun_const_zero]
  simp [hm]

/-- **`T` has `[G : U]` elements**: `t ↦ U t` is a bijection from `T` onto `U\G`. PROVED. -/
theorem card_T_eq_index : R.T.card = U.index := by
  classical
  show R.T.card = Nat.card (G ⧸ U)
  rw [← Nat.card_congr (QuotientGroup.quotientRightRelEquivQuotientLeftRel U),
    ← Nat.card_eq_finsetCard]
  refine Nat.card_congr (Equiv.ofBijective
    (fun t : R.T => (Quotient.mk'' (t : G) : Quotient (QuotientGroup.rightRel U))) ⟨?_, ?_⟩)
  · rintro ⟨t, ht⟩ ⟨t', ht'⟩ h
    have h' := QuotientGroup.rightRel_apply.mp (Quotient.exact' h)
    apply Subtype.ext
    change t = t'
    rw [← R.hat_self t ht, ← R.hat_self t' ht']
    exact (R.hat_eq t t' h').symm
  · intro q
    induction q using Quotient.inductionOn' with
    | h x =>
      refine ⟨⟨R.hat x, R.hat_mem x⟩, ?_⟩
      apply Quotient.sound'
      rw [QuotientGroup.rightRel_apply]
      simpa [mul_inv_rev] using U.inv_mem (R.hat_mul_inv_mem x)

/-- **Degree zero, `G`-invariant values, with the index:** for `m` fixed by `G`, corestriction of
the constant `0`-cochain `m` is `[G : U] • m` (Brown III.9: `cor ∘ res = [G : U]` on `H⁰`).
PROVED. -/
theorem corFun_const_zero_of_invariant_index (m : A) (hm : ∀ x : G, x • m = m) (g : Fin 0 → G) :
    R.corFun (fun _ : Fin 0 → U => m) g = U.index • m := by
  rw [corFun_const_zero_of_invariant R m hm g, card_T_eq_index]

end DegreeZero

/-- **Existence of finite right transversals** for a subgroup of finite index: the representative
of `x` is a chosen element (`Quotient.out`) of its right coset `U x`, and `T` is the (finite) set of
these choices. -/
def ofFiniteIndex (U : Subgroup G) [U.FiniteIndex] : RightTransversal U := by
  classical
  haveI : Finite (Quotient (QuotientGroup.rightRel U)) :=
    Finite.of_equiv _ (QuotientGroup.quotientRightRelEquivQuotientLeftRel U).symm
  haveI := Fintype.ofFinite (Quotient (QuotientGroup.rightRel U))
  exact
    { T := Finset.univ.image (fun q : Quotient (QuotientGroup.rightRel U) => q.out)
      hat := fun x => (Quotient.mk'' x : Quotient (QuotientGroup.rightRel U)).out
      hat_mem := fun x => Finset.mem_image_of_mem _ (Finset.mem_univ _)
      hat_mul_inv_mem := fun x => by
        have h := QuotientGroup.rightRel_apply.mp (Quotient.mk_out' (s₁ := QuotientGroup.rightRel U) x)
        simpa [mul_inv_rev] using U.inv_mem h
      hat_eq := fun x y h => by
        have e : (Quotient.mk'' y : Quotient (QuotientGroup.rightRel U)) = Quotient.mk'' x :=
          Quotient.sound' (QuotientGroup.rightRel_apply.mpr (by simpa [mul_inv_rev] using U.inv_mem h))
        rw [e]
      hat_self := fun t ht => by
        obtain ⟨q, -, rfl⟩ := Finset.mem_image.mp ht
        rw [Quotient.out_eq'] }

end RightTransversal

end Transversal

/-! ### Corestriction as a cochain map of Mathlib's inhomogeneous cochains -/

section Linear

variable {k : Type u} [CommRing k] {G : Type u} [Group G] {U : Subgroup G}
  {M : Type u} [AddCommGroup M] [Module k M] [DistribMulAction G M] [SMulCommClass G k M]

namespace RightTransversal

variable (R : RightTransversal U)

/-- **Corestriction as a `k`-linear map** `Map(Uⁿ, M) → Map(Gⁿ, M)` (Nekovář 8.1.4, Brown III.9);
linearity uses that the `G`-action commutes with the `k`-action. -/
def corLin (n : ℕ) : ((Fin n → U) → M) →ₗ[k] ((Fin n → G) → M) where
  toFun := R.corFun
  map_add' c c' := by
    funext g
    simp only [corFun, Pi.add_apply, smul_add, Finset.sum_add_distrib]
  map_smul' r c := by
    funext g
    simp only [corFun, Pi.smul_apply, RingHom.id_apply, Finset.smul_sum]
    exact Finset.sum_congr rfl fun t _ => smul_comm _ _ _

/-- The `k`-linear corestriction is `corFun`. -/
theorem corLin_apply (n : ℕ) (c : (Fin n → U) → M) : R.corLin (k := k) n c = R.corFun c :=
  rfl

/-- **The chain-map identity for Mathlib's differentials** (Nekovář 8.1.4, Brown III.9):
`cor ∘ d_U = d_G ∘ cor`, where `d_U` is the inhomogeneous differential of the restriction
`Rep.res U.subtype (Rep.ofDistribMulAction k G M)` of `M` to `U` and `d_G` that of
`Rep.ofDistribMulAction k G M`. PROVED. -/
theorem corFun_d (n : ℕ) (c : (Fin n → U) → M) :
    R.corFun (M := M) (((groupCohomology.inhomogeneousCochains
        (Rep.res U.subtype (rep k G M))).d n (n + 1)).hom c) =
      ((groupCohomology.inhomogeneousCochains (rep k G M)).d n (n + 1)).hom (R.corFun (M := M) c) := by
  funext g
  rw [groupCohomology.inhomogeneousCochains.d_def, groupCohomology.inhomogeneousCochains.d_def]
  exact R.corFun_dFormula (k := k) c g

/-- **Corestriction as a cochain map** `C^•(U, M) → C^•(G, M)` of Mathlib's complexes of
inhomogeneous cochains (Nekovář, *Selmer complexes*, 8.1.4; Brown, *Cohomology of Groups*, III.9),
for `U` acting on `M` by restriction. PROVED (a cochain map by `corFun_d`). -/
def corInhom : groupCohomology.inhomogeneousCochains (Rep.res U.subtype (rep k G M)) ⟶
    groupCohomology.inhomogeneousCochains (rep k G M) where
  f n := ModuleCat.ofHom (R.corLin (k := k) (M := M) n :)
  comm' i j hij := by
    obtain rfl : j = i + 1 := hij.symm
    refine ModuleCat.hom_ext (LinearMap.ext fun c => ?_)
    exact (R.corFun_d (M := M) i c).symm

/-- In each degree, the cochain map `corInhom` is the corestriction formula `corFun`. -/
theorem corInhom_f_apply (n : ℕ) (c : (Fin n → U) → M) :
    ((R.corInhom (k := k)).f n).hom c = R.corFun (M := M) c :=
  rfl

end RightTransversal

end Linear

/-! ### Continuous cochains -/

section Continuous

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-- The inclusion `U →ₜ* G` of a subgroup (with the subspace topology). -/
def subgroupIncl (U : Subgroup G) : U →ₜ* G where
  toMonoidHom := U.subtype
  continuous_toFun := continuous_subtype_val

omit [IsTopologicalGroup G] in
/-- The inclusion `U →ₜ* G` sends `u` to `u`. -/
@[simp]
theorem subgroupIncl_apply (U : Subgroup G) (u : U) : subgroupIncl U u = (u : G) :=
  rfl

/-- Partial products `(g₁,…,gₙ) ↦ g₁⋯g_i` are continuous on `Gⁿ`. -/
theorem continuous_partialProd {n : ℕ} (i : Fin (n + 1)) :
    Continuous fun g : Fin n → G => Fin.partialProd g i := by
  induction i using Fin.induction with
  | zero =>
    simp only [Fin.partialProd_zero]
    exact continuous_const
  | succ i ih =>
    simp only [Fin.partialProd_succ]
    exact ih.mul (continuous_apply i)

variable {U : Subgroup G}

namespace RightTransversal

variable (R : RightTransversal U)

/-- For an **open** subgroup `U`, the representative map `x ↦ x̂` is locally constant (constant on
the open cosets `U x`), hence continuous. -/
theorem continuous_hat (hU : IsOpen (U : Set G)) : Continuous R.hat := by
  refine continuous_iff_continuousAt.2 fun x => ?_
  have hV : IsOpen ((fun y => y * x⁻¹) ⁻¹' (U : Set G)) := hU.preimage (continuous_id.mul continuous_const)
  have hx : x ∈ (fun y => y * x⁻¹) ⁻¹' (U : Set G) := by
    simp only [Set.mem_preimage, mul_inv_cancel, SetLike.mem_coe]
    exact U.one_mem
  refine ContinuousAt.congr (f := fun _ => R.hat x) continuousAt_const ?_
  filter_upwards [hV.mem_nhds hx] with y hy
  exact (R.hat_eq x y hy).symm

/-- For an open subgroup `U`, the arguments of corestriction depend continuously on
`(g₁,…,gₙ) ∈ Gⁿ`. -/
theorem continuous_corArg (hU : IsOpen (U : Set G)) {n : ℕ} (t : G) :
    Continuous fun g : Fin n → G => R.corArg t g := by
  refine continuous_pi fun i => ?_
  refine continuous_induced_rng.2 ?_
  have h : (Subtype.val ∘ fun g : Fin n → G => R.corArg t g i) = fun g =>
      R.hat (t * Fin.partialProd g i.castSucc) * g i *
        (R.hat (t * Fin.partialProd g i.succ))⁻¹ := by
    funext g
    exact R.coe_corArg t g i
  rw [h]
  have hr := R.continuous_hat hU
  exact ((hr.comp (continuous_const.mul (continuous_partialProd _))).mul (continuous_apply i)).mul
    (hr.comp (continuous_const.mul (continuous_partialProd _))).inv

variable {k : Type u} [CommRing k]
  {M : Type u} [AddCommGroup M] [Module k M] [DistribMulAction G M] [SMulCommClass G k M]

omit [IsTopologicalGroup G] in
/-- **The chain-map identity for `ResMod`** (`M` with `U` acting through the inclusion
`U →ₜ* G`): `cor ∘ d_U = d_G ∘ cor` for Mathlib's inhomogeneous differentials (Nekovář 8.1.4,
Brown III.9). PROVED. -/
theorem corFun_d_resMod (n : ℕ) (c : (Fin n → U) → M) :
    R.corFun (M := M) (((groupCohomology.inhomogeneousCochains
        (rep k U (ResMod (subgroupIncl U) M))).d n (n + 1)).hom c) =
      ((groupCohomology.inhomogeneousCochains (rep k G M)).d n (n + 1)).hom (R.corFun (M := M) c) := by
  funext g
  rw [groupCohomology.inhomogeneousCochains.d_def, groupCohomology.inhomogeneousCochains.d_def]
  exact R.corFun_dFormula (k := k) c g

/-- **Corestriction as a cochain map** `C^•(U, M) → C^•(G, M)` of Mathlib's inhomogeneous
cochains, for `U` acting on `M` through the inclusion `U →ₜ* G` (`ResMod`) (Nekovář 8.1.4,
Brown III.9). PROVED. -/
def corInhomResMod : groupCohomology.inhomogeneousCochains (rep k U (ResMod (subgroupIncl U) M)) ⟶
    groupCohomology.inhomogeneousCochains (rep k G M) where
  f n := ModuleCat.ofHom (R.corLin (k := k) (M := M) n :)
  comm' i j hij := by
    obtain rfl : j = i + 1 := hij.symm
    refine ModuleCat.hom_ext (LinearMap.ext fun c => ?_)
    exact (R.corFun_d_resMod (M := M) i c).symm

variable [TopologicalSpace M] [ContinuousAdd M] [ContinuousConstSMul k M] [ContinuousSMul G M]

/-- **Corestriction on continuous cochains** `cor : C^•_cont(U, M) → C^•_cont(G, M)` for an open
subgroup `U` (of finite index, through the finite transversal `R`) of a topological group `G`
(Nekovář, *Selmer complexes*, 8.1.4; Brown, *Cohomology of Groups*, III.9): the restriction of
`corInhomResMod` to continuous cochains (continuity is preserved because the representative map is
locally constant). PROVED (a cochain map). -/
def corCochains (hU : IsOpen (U : Set G)) :
    contCochains k U (ResMod (subgroupIncl U) M) ⟶ contCochains k G M :=
  (contSubCx k U (ResMod (subgroupIncl U) M)).map (contSubCx k G M) R.corInhomResMod
    (fun n c hc => by
      have hc' : Continuous (fun x : Fin n → U =>
          (show M from asFun k U (ResMod (subgroupIncl U) M) c x)) := hc
      change Continuous (fun g : Fin n → G => ∑ t ∈ R.T,
        t⁻¹ • (show M from asFun k U (ResMod (subgroupIncl U) M) c (R.corArg t g)))
      exact continuous_finsetSum _ fun t _ => (hc'.comp (R.continuous_corArg hU t)).const_smul t⁻¹)

/-- `corCochains` is given by the corestriction formula `corFun`. -/
theorem corCochains_apply (hU : IsOpen (U : Set G)) (n : ℕ)
    (c : (contCochains k U (ResMod (subgroupIncl U) M)).X n) (g : Fin n → G) :
    asFun k G M (((contSubCx k G M).el (((R.corCochains hU).f n).hom c) : contCochain k G M n) :
      (groupCohomology.inhomogeneousCochains (rep k G M)).X n) g =
      R.corFun (M := M) (asFun k U (ResMod (subgroupIncl U) M)
        ((contSubCx k U (ResMod (subgroupIncl U) M)).el c :
          contCochain k U (ResMod (subgroupIncl U) M) n)) g :=
  rfl

/-- Corestriction on continuous cochains commutes with the inclusions into Mathlib's
inhomogeneous cochains. PROVED. -/
theorem corCochains_ι (hU : IsOpen (U : Set G)) :
    R.corCochains hU ≫ contCochainsι k G M =
      contCochainsι k U (ResMod (subgroupIncl U) M) ≫ R.corInhomResMod :=
  SubCx.map_ι _ _ _ _

/-- The map `Hⁿ_cont(U, M) → Hⁿ_cont(G, M)` induced by corestriction. -/
abbrev corCohomology (hU : IsOpen (U : Set G)) (n : ℕ) :
    contCohomology k U (ResMod (subgroupIncl U) M) n ⟶ contCohomology k G M n :=
  HomologicalComplex.homologyMap (R.corCochains hU) n

end RightTransversal

end Continuous

end ZInQ.Manuscript.RC.SelmerComplex
