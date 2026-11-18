import Mathlib

/-!
# Cup products of inhomogeneous cochains

This file constructs the cup product on the (continuous) inhomogeneous cochain complexes used in
this lane, in all degrees, and proves its basic properties.

Let `G` be a group and let `A`, `B`, `T` be `k`-modules with compatible `G`-actions, together with
a `k`-bilinear pairing `β : A →ₗ[k] B →ₗ[k] T`. For `p + q = n`, an inhomogeneous `p`-cochain
`a : Gᵖ → A` and an inhomogeneous `q`-cochain `b : G^q → B`, the cup product is the `n`-cochain
$$(a ∪ b)(g_0, …, g_{n-1}) = β\bigl(a(g_0, …, g_{p-1}),\ (g_0 ⋯ g_{p-1}) • b(g_p, …, g_{n-1})\bigr)$$
(Brown, *Cohomology of Groups*, Ch. V §3; Neukirch–Schmidt–Wingberg, *Cohomology of Number
Fields*, Ch. I §4).

## Main definitions

* `headProd p n hp g`: the ordered product `g₀ g₁ ⋯ g_{p-1}` of the first `p` entries of
  `g : Fin n → G`.
* `cupFun β p q n h a b`: the cup product of two inhomogeneous cochains, as a function.
* `cup β p q n h`: the cup product as a `k`-bilinear map.

## Main results

* `cupFun_leibniz`: the Leibniz rule `d (a ∪ b) = (d a) ∪ b + (-1)ᵖ a ∪ (d b)` for Mathlib's
  inhomogeneous differential `inhomogeneousCochains.d`, whenever `β` is `G`-equivariant.
* `cupFun_isCocycle`, `cupFun_coboundary_left`, `cupFun_coboundary_right`: consequences for
  cocycles and coboundaries.
* `continuous_cupFun`: the cup product of continuous cochains is continuous (for a topological
  group `G`, a continuous action on `B` and a jointly continuous pairing), with the special case
  `continuous_cupFun_of_discrete` of discrete modules.
* `cupFun_comp`: compatibility with restriction (pullback) along a group homomorphism `H →* G`.

At the end, examples show that the construction is not vacuous.
-/

namespace ZInQ.Manuscript.RC.SelmerComplex

noncomputable section

universe u

section Def

variable {k G : Type u} [CommRing k] [Monoid G]
  {A B T : Type u} [AddCommGroup A] [Module k A] [AddCommGroup B] [Module k B] [MulAction G B]
  [AddCommGroup T] [Module k T]

/-- The ordered product `g₀ g₁ ⋯ g_{p-1}` of the first `p` entries of `g : Fin n → G`
(for `p = 0` this is `1`). It is defined as the partial product `Fin.partialProd g p`; see
`headProd_eq_prod_ofFn` for the description as the product of the list `[g₀, …, g_{p-1}]`.
This is the group element by which the second factor is translated in the cup product formula
(Brown, *Cohomology of Groups*, Ch. V §3). -/
def headProd (p n : ℕ) (hp : p ≤ n) (g : Fin n → G) : G := Fin.partialProd g ⟨p, by omega⟩

/-- The cup product of inhomogeneous cochains with respect to a bilinear pairing `β`:
`(a ∪ b)(g₀,…,g_{n−1}) = β (a(g₀,…,g_{p−1})) ((g₀⋯g_{p−1}) • b(g_p,…,g_{n−1}))`, for `p + q = n`
(Brown, *Cohomology of Groups*, Ch. V §3; for continuous cochains,
Neukirch–Schmidt–Wingberg, *Cohomology of Number Fields*, Ch. I §4). Only the action of `G` on
the second module `B` enters the formula. -/
def cupFun (β : A →ₗ[k] B →ₗ[k] T) (p q n : ℕ) (h : p + q = n)
    (a : (Fin p → G) → A) (b : (Fin q → G) → B) : (Fin n → G) → T :=
  fun g => β (a fun i => g (Fin.castLE (by omega) i))
    (headProd p n (by omega) g • b fun j => g ⟨p + j, by omega⟩)

/-- Unfolding lemma for `cupFun` (Brown, *Cohomology of Groups*, Ch. V §3). -/
theorem cupFun_apply (β : A →ₗ[k] B →ₗ[k] T) (p q n : ℕ) (h : p + q = n)
    (a : (Fin p → G) → A) (b : (Fin q → G) → B) (g : Fin n → G) :
    cupFun β p q n h a b g = β (a fun i => g (Fin.castLE (by omega) i))
      (headProd p n (by omega) g • b fun j => g ⟨p + j, by omega⟩) := rfl

end Def

section HeadProd

variable {G : Type u} [Monoid G]

/-- The empty head product is `1`. -/
theorem headProd_zero (n : ℕ) (hp : 0 ≤ n) (g : Fin n → G) : headProd 0 n hp g = 1 :=
  Fin.partialProd_zero g

/-- Peeling off the last factor: `g₀ ⋯ g_p = (g₀ ⋯ g_{p-1}) g_p`. -/
theorem headProd_succ (p n : ℕ) (hp : p + 1 ≤ n) (g : Fin n → G) :
    headProd (p + 1) n hp g = headProd p n (by omega) g * g ⟨p, by omega⟩ :=
  Fin.partialProd_succ g ⟨p, by omega⟩

/-- Peeling off the first factor: `g₀ ⋯ g_p = g₀ (g₁ ⋯ g_p)`. -/
theorem headProd_succ' (p n : ℕ) (hp : p + 1 ≤ n + 1) (g : Fin (n + 1) → G) :
    headProd (p + 1) (n + 1) hp g = g 0 * headProd p n (by omega) (fun i => g i.succ) :=
  Fin.partialProd_succ' g ⟨p, by omega⟩

/-- The head product is the product of the list `[g₀, …, g_{p-1}]` of the first `p` entries. -/
theorem headProd_eq_prod_ofFn (p n : ℕ) (hp : p ≤ n) (g : Fin n → G) :
    headProd p n hp g = (List.ofFn fun i : Fin p => g (Fin.castLE hp i)).prod := by
  induction p with
  | zero => rw [headProd_zero, List.ofFn_zero, List.prod_nil]
  | succ p ih =>
    rw [headProd_succ, ih (by omega), List.ofFn_succ', List.concat_eq_append, List.prod_append,
      List.prod_singleton]
    rfl

/-- The head product is compatible with monoid homomorphisms. -/
theorem map_headProd {H : Type u} [Monoid H] (φ : H →* G) (p n : ℕ) (hp : p ≤ n)
    (g : Fin n → H) : φ (headProd p n hp g) = headProd p n hp (φ ∘ g) := by
  induction p with
  | zero => rw [headProd_zero, headProd_zero, map_one]
  | succ p ih => rw [headProd_succ, headProd_succ, map_mul, ih]; rfl

/-- Contracting two adjacent entries `g_j, g_{j+1}` with `j < p` inside the first `p + 1`
entries does not change the product of the first `p` entries of the contracted tuple, which is
`g₀ ⋯ g_p`. -/
theorem headProd_contractNth_of_lt (p n : ℕ) (hp : p ≤ n) (g : Fin (n + 1) → G)
    (j : Fin (n + 1)) (hj : (j : ℕ) < p) :
    headProd p n hp (Fin.contractNth j (· * ·) g) = headProd (p + 1) (n + 1) (by omega) g := by
  unfold headProd
  rw [Fin.partialProd_contractNth, Function.comp_apply, Fin.succAbove_of_le_castSucc]
  · rfl
  · simp only [Fin.le_def, Fin.val_castSucc, Fin.val_succ]; omega

/-- Contracting at a position `j ≥ p` does not touch the first `p` entries, hence does not change
their product. -/
theorem headProd_contractNth_of_le (p n : ℕ) (hp : p ≤ n) (g : Fin (n + 1) → G)
    (j : Fin (n + 1)) (hj : p ≤ (j : ℕ)) :
    headProd p n hp (Fin.contractNth j (· * ·) g) = headProd p (n + 1) (by omega) g := by
  unfold headProd
  rw [Fin.partialProd_contractNth, Function.comp_apply, Fin.succAbove_of_castSucc_lt]
  · rfl
  · simp only [Fin.lt_def, Fin.val_castSucc, Fin.val_succ]; omega

/-- For `j < p`, the first `p` entries of the contraction of `g` at `j` are the contraction at `j`
of the first `p + 1` entries of `g`. -/
theorem head_contractNth_of_lt {p n : ℕ} (hp : p ≤ n) (g : Fin (n + 1) → G) (j : Fin (n + 1))
    (i : Fin (p + 1)) (hji : (j : ℕ) = i) :
    (fun l : Fin p => Fin.contractNth j (· * ·) g (Fin.castLE hp l)) =
      Fin.contractNth i (· * ·) (fun l : Fin (p + 1) => g (Fin.castLE (by omega) l)) := by
  funext l
  simp only [Fin.contractNth, Fin.val_castLE, hji]
  split_ifs <;> rfl

/-- For `j < p`, the entries of the contraction of `g` at `j` from position `p` on are the
entries of `g` from position `p + 1` on. -/
theorem tail_contractNth_of_lt {p q n : ℕ} (h : p + q = n) (g : Fin (n + 1) → G)
    (j : Fin (n + 1)) (hj : (j : ℕ) < p) :
    (fun t : Fin q => Fin.contractNth j (· * ·) g ⟨p + t, by omega⟩) =
      fun t : Fin q => g ⟨p + 1 + t, by omega⟩ := by
  funext t
  rw [Fin.contractNth_apply_of_gt _ _ _ _ (by simp only; omega)]
  congr 1
  ext
  simp only [Fin.val_succ]
  omega

/-- For `j ≥ p`, the first `p` entries of the contraction of `g` at `j` are the first `p`
entries of `g`. -/
theorem head_contractNth_of_le {p n : ℕ} (hp : p ≤ n) (g : Fin (n + 1) → G) (j : Fin (n + 1))
    (hj : p ≤ (j : ℕ)) :
    (fun l : Fin p => Fin.contractNth j (· * ·) g (Fin.castLE hp l)) =
      fun l : Fin p => g (Fin.castLE (by omega) l) := by
  funext l
  rw [Fin.contractNth_apply_of_lt _ _ _ _ (by simp only [Fin.val_castLE]; omega)]
  rfl

/-- The entries from position `p` on of the contraction of `g` at `p + j` are the contraction
at `j` of the entries of `g` from position `p` on. -/
theorem tail_contractNth_of_le {p q n : ℕ} (h : p + q = n) (g : Fin (n + 1) → G)
    (j : Fin (q + 1)) :
    (fun t : Fin q => Fin.contractNth ⟨p + j, by omega⟩ (· * ·) g ⟨p + t, by omega⟩) =
      Fin.contractNth j (· * ·) (fun t : Fin (q + 1) => g ⟨p + t, by omega⟩) := by
  funext t
  simp only [Fin.contractNth, Fin.val_castSucc, Fin.val_succ]
  split_ifs <;> first | rfl | omega

/-- Contracting the first `p + 1` entries at the last position drops the entry `g_p`. -/
theorem contractNth_last_head {p n : ℕ} (hp : p + 1 ≤ n) (g : Fin n → G) :
    Fin.contractNth (Fin.last p) (· * ·) (fun i : Fin (p + 1) => g (Fin.castLE hp i)) =
      fun i : Fin p => g (Fin.castLE (by omega) i) := by
  funext i
  rw [Fin.contractNth_apply_of_lt _ _ _ _ (by simp only [Fin.val_last]; omega)]
  rfl

omit [Monoid G] in
/-- Reindexing the entries of a tuple from position `p + 1` on. -/
theorem tail_succ_eq {p q n : ℕ} (h : p + q + 1 = n) (g : Fin n → G) :
    (fun t : Fin q => g ⟨p + (t.succ : ℕ), by omega⟩) =
      fun t : Fin q => g ⟨p + 1 + t, by omega⟩ := by
  funext t
  congr 1
  ext
  simp only [Fin.val_succ]
  omega

omit [Monoid G] in
/-- Reindexing the entries of a tuple from position `p + 1` on, seen through `Fin.succ`. -/
theorem tail_succ_eq' {p q n : ℕ} (h : p + q = n) (g : Fin (n + 1) → G) :
    (fun t : Fin q => g (⟨p + t, by omega⟩ : Fin n).succ) =
      fun t : Fin q => g ⟨p + 1 + t, by omega⟩ := by
  funext t
  congr 1
  ext
  simp only [Fin.val_succ]
  omega

end HeadProd

section Group

variable {k G : Type u} [CommRing k] [Group G]
  {A B T : Type u} [AddCommGroup A] [Module k A] [DistribMulAction G A] [SMulCommClass G k A]
  [AddCommGroup B] [Module k B] [DistribMulAction G B] [SMulCommClass G k B]
  [AddCommGroup T] [Module k T] [DistribMulAction G T] [SMulCommClass G k T]

/-- The cup product of inhomogeneous cochains as a `k`-bilinear map
(Brown, *Cohomology of Groups*, Ch. V §3). -/
def cup (β : A →ₗ[k] B →ₗ[k] T) (p q n : ℕ) (h : p + q = n) :
    ((Fin p → G) → A) →ₗ[k] ((Fin q → G) → B) →ₗ[k] ((Fin n → G) → T) :=
  LinearMap.mk₂ k (cupFun β p q n h)
    (fun a₁ a₂ b => by funext g; simp [cupFun])
    (fun c a b => by funext g; simp [cupFun])
    (fun a b₁ b₂ => by funext g; simp [cupFun, smul_add])
    (fun c a b => by funext g; simp [cupFun, smul_comm _ c])

omit [DistribMulAction G A] [SMulCommClass G k A] [DistribMulAction G T] [SMulCommClass G k T] in
/-- The bilinear map `cup` evaluates to `cupFun`. -/
@[simp]
theorem cup_apply (β : A →ₗ[k] B →ₗ[k] T) (p q n : ℕ) (h : p + q = n)
    (a : (Fin p → G) → A) (b : (Fin q → G) → B) :
    cup β p q n h a b = cupFun β p q n h a b := rfl

variable (k) in
/-- The inhomogeneous differential written out for a `k`-module `M` with a compatible
`G`-action: `(d f)(g₀,…,g_n) = g₀ • f(g₁,…,g_n) + ∑ⱼ (-1)^(j+1) f(…, g_j g_{j+1}, …)`,
where the `j = n` term drops the last entry. This is Mathlib's `inhomogeneousCochains.d`
written out on the underlying types (see `d_hom_eq`). -/
def dFun {M : Type u} [AddCommGroup M] [Module k M] [DistribMulAction G M] (n : ℕ)
    (f : (Fin n → G) → M) : (Fin (n + 1) → G) → M :=
  fun g => g 0 • f (fun i => g i.succ) + ∑ j : Fin (n + 1),
    (-1 : k) ^ ((j : ℕ) + 1) • f (Fin.contractNth j (· * ·) g)

/-- Mathlib's inhomogeneous differential for `Rep.ofDistribMulAction k G M` is `dFun`. -/
theorem d_hom_eq {M : Type u} [AddCommGroup M] [Module k M] [DistribMulAction G M]
    [SMulCommClass G k M] (n : ℕ) (f : (Fin n → G) → M) :
    (inhomogeneousCochains.d (Rep.ofDistribMulAction k G M) n).hom f = dFun k n f := rfl

/-- Splitting a sum over `Fin (p + q + 1)` into the indices `< p` and the indices `p + j`,
`j ≤ q`. -/
theorem sum_fin_split {M : Type*} [AddCommMonoid M] (p q : ℕ) (F : Fin (p + q + 1) → M) :
    ∑ j, F j = ∑ i : Fin p, F ⟨i, by omega⟩ + ∑ j : Fin (q + 1), F ⟨p + j, by omega⟩ :=
  Fin.sum_univ_add (a := p) (b := q + 1) F

omit [SMulCommClass G k A] [SMulCommClass G k B] [DistribMulAction G T] [SMulCommClass G k T] in
/-- Expansion of `(d a) ∪ b` at `g`: the `ρ`-term, the face terms `j < p`, and the last face
term `j = p`, which drops `g_p` (Brown, *Cohomology of Groups*, Ch. V §3). -/
theorem cupFun_dFun_left_apply (β : A →ₗ[k] B →ₗ[k] T) (p q : ℕ) (a : (Fin p → G) → A)
    (b : (Fin q → G) → B) (g : Fin (p + q + 1) → G) :
    cupFun β (p + 1) q (p + q + 1) (by omega) (dFun k p a) b g =
      β (g 0 • a (fun i : Fin p => g (Fin.castLE (by omega) i.succ)))
          (headProd (p + 1) (p + q + 1) (by omega) g •
            b (fun t : Fin q => g ⟨p + 1 + t, by omega⟩)) +
        (∑ i : Fin p, (-1 : k) ^ ((i : ℕ) + 1) •
          β (a (Fin.contractNth (Fin.castSucc i) (· * ·)
              (fun l : Fin (p + 1) => g (Fin.castLE (by omega) l))))
            (headProd (p + 1) (p + q + 1) (by omega) g •
              b (fun t : Fin q => g ⟨p + 1 + t, by omega⟩)) +
        (-1 : k) ^ (p + 1) • β (a (fun i : Fin p => g (Fin.castLE (by omega) i)))
            (headProd (p + 1) (p + q + 1) (by omega) g •
              b (fun t : Fin q => g ⟨p + 1 + t, by omega⟩))) := by
  simp only [cupFun, dFun, Fin.sum_univ_castSucc, map_add, LinearMap.add_apply, map_sum,
    LinearMap.sum_apply, map_smul, LinearMap.smul_apply, Fin.val_castSucc,
    Fin.val_last, contractNth_last_head, Fin.castLE_zero]

omit [DistribMulAction G A] [SMulCommClass G k A] [DistribMulAction G T]
  [SMulCommClass G k T] in
/-- Expansion of `a ∪ (d b)` at `g`: the `ρ`-term and the face terms
(Brown, *Cohomology of Groups*, Ch. V §3). -/
theorem cupFun_dFun_right_apply (β : A →ₗ[k] B →ₗ[k] T) (p q : ℕ) (a : (Fin p → G) → A)
    (b : (Fin q → G) → B) (g : Fin (p + q + 1) → G) :
    cupFun β p (q + 1) (p + q + 1) (by omega) a (dFun k q b) g =
      β (a (fun i : Fin p => g (Fin.castLE (by omega) i)))
          (headProd p (p + q + 1) (by omega) g • g ⟨p, by omega⟩ •
            b (fun t : Fin q => g ⟨p + 1 + t, by omega⟩)) +
        ∑ j : Fin (q + 1), (-1 : k) ^ ((j : ℕ) + 1) •
          β (a (fun i : Fin p => g (Fin.castLE (by omega) i)))
            (headProd p (p + q + 1) (by omega) g •
              b (Fin.contractNth j (· * ·) (fun t : Fin (q + 1) => g ⟨p + t, by omega⟩))) := by
  simp only [cupFun, dFun, smul_add, Finset.smul_sum, smul_comm _ ((-1 : k) ^ _), map_add,
    map_sum, map_smul, Fin.val_zero, add_zero, tail_succ_eq]

omit [SMulCommClass G k A] [SMulCommClass G k B] [SMulCommClass G k T] in
/-- Expansion of `d (a ∪ b)` at `g`, for a `G`-equivariant pairing `β`: the `ρ`-term is the
`ρ`-term of `(d a) ∪ b`, the face terms `j < p` are the face terms `j < p` of `(d a) ∪ b`, and
the face terms `j = p + j'` are `(-1)ᵖ` times the face terms of `a ∪ (d b)`
(Brown, *Cohomology of Groups*, Ch. V §3). -/
theorem dFun_cupFun_expand (β : A →ₗ[k] B →ₗ[k] T)
    (hβ : ∀ (g : G) (a : A) (b : B), β (g • a) (g • b) = g • β a b) (p q : ℕ)
    (a : (Fin p → G) → A) (b : (Fin q → G) → B) (g : Fin (p + q + 1) → G) :
    dFun k (p + q) (cupFun β p q (p + q) rfl a b) g =
      β (g 0 • a (fun i : Fin p => g (Fin.castLE (by omega) i.succ)))
          (headProd (p + 1) (p + q + 1) (by omega) g •
            b (fun t : Fin q => g ⟨p + 1 + t, by omega⟩)) +
        (∑ i : Fin p, (-1 : k) ^ ((i : ℕ) + 1) •
          β (a (Fin.contractNth (Fin.castSucc i) (· * ·)
              (fun l : Fin (p + 1) => g (Fin.castLE (by omega) l))))
            (headProd (p + 1) (p + q + 1) (by omega) g •
              b (fun t : Fin q => g ⟨p + 1 + t, by omega⟩)) +
        ∑ j : Fin (q + 1), (-1 : k) ^ p • (-1 : k) ^ ((j : ℕ) + 1) •
          β (a (fun i : Fin p => g (Fin.castLE (by omega) i)))
            (headProd p (p + q + 1) (by omega) g •
              b (Fin.contractNth j (· * ·) (fun t : Fin (q + 1) => g ⟨p + t, by omega⟩)))) := by
  simp only [dFun]
  rw [sum_fin_split]
  congr 1
  · simp only [cupFun]
    rw [← hβ, ← mul_smul, ← headProd_succ', tail_succ_eq' rfl g]
    rfl
  congr 1
  · refine Finset.sum_congr rfl fun i _ => ?_
    simp only [cupFun]
    rw [head_contractNth_of_lt _ g _ (Fin.castSucc i) rfl, tail_contractNth_of_lt rfl g _ (by simp),
      headProd_contractNth_of_lt _ _ _ g _ (by simp)]
  · refine Finset.sum_congr rfl fun j _ => ?_
    simp only [cupFun]
    rw [head_contractNth_of_le _ g _ (by simp), tail_contractNth_of_le rfl g j,
      headProd_contractNth_of_le _ _ _ g _ (by simp), ← mul_smul, ← pow_add]
    rfl

omit [SMulCommClass G k A] [SMulCommClass G k T] in
/-- The Leibniz rule for `dFun`, evaluated at a point (Brown, *Cohomology of Groups*,
Ch. V §3). The last face term of `(d a) ∪ b` cancels `(-1)ᵖ` times the `ρ`-term of
`a ∪ (d b)`. -/
theorem dFun_cupFun_apply (β : A →ₗ[k] B →ₗ[k] T)
    (hβ : ∀ (g : G) (a : A) (b : B), β (g • a) (g • b) = g • β a b) (p q : ℕ)
    (a : (Fin p → G) → A) (b : (Fin q → G) → B) (g : Fin (p + q + 1) → G) :
    dFun k (p + q) (cupFun β p q (p + q) rfl a b) g =
      cupFun β (p + 1) q (p + q + 1) (by omega) (dFun k p a) b g +
        (-1 : k) ^ p • cupFun β p (q + 1) (p + q + 1) (by omega) a (dFun k q b) g := by
  rw [dFun_cupFun_expand β hβ, cupFun_dFun_left_apply, cupFun_dFun_right_apply, smul_add,
    Finset.smul_sum]
  have hL : (-1 : k) ^ (p + 1) • β (a (fun i : Fin p => g (Fin.castLE (by omega) i)))
            (headProd (p + 1) (p + q + 1) (by omega) g •
              b (fun t : Fin q => g ⟨p + 1 + t, by omega⟩)) =
      -((-1 : k) ^ p • β (a (fun i : Fin p => g (Fin.castLE (by omega) i)))
          (headProd p (p + q + 1) (by omega) g • g ⟨p, by omega⟩ •
            b (fun t : Fin q => g ⟨p + 1 + t, by omega⟩))) := by
    rw [headProd_succ, mul_smul, pow_succ, mul_neg_one, neg_smul]
  rw [hL]
  abel

/-- **Leibniz rule** for the cup product of inhomogeneous cochains: for a `G`-equivariant
pairing `β`, `d (a ∪ b) = (d a) ∪ b + (-1)ᵖ a ∪ (d b)`, where `d` is Mathlib's inhomogeneous
differential (Brown, *Cohomology of Groups*, Ch. V §3; Neukirch–Schmidt–Wingberg,
*Cohomology of Number Fields*, Ch. I §4). -/
theorem cupFun_leibniz (β : A →ₗ[k] B →ₗ[k] T)
    (hβ : ∀ (g : G) (a : A) (b : B), β (g • a) (g • b) = g • β a b)
    (p q n : ℕ) (h : p + q = n) (a : (Fin p → G) → A) (b : (Fin q → G) → B) :
    (inhomogeneousCochains.d (Rep.ofDistribMulAction k G T) n).hom (cupFun β p q n h a b) =
      cupFun β (p + 1) q (n + 1) (by omega)
          ((inhomogeneousCochains.d (Rep.ofDistribMulAction k G A) p).hom a) b +
        (-1 : k) ^ p • cupFun β p (q + 1) (n + 1) (by omega) a
          ((inhomogeneousCochains.d (Rep.ofDistribMulAction k G B) q).hom b) := by
  subst h
  rw [d_hom_eq, d_hom_eq, d_hom_eq]
  funext g
  exact dFun_cupFun_apply β hβ p q a b g

/-- The Leibniz rule in terms of the explicit differential `dFun`
(Brown, *Cohomology of Groups*, Ch. V §3). -/
theorem dFun_cupFun (β : A →ₗ[k] B →ₗ[k] T)
    (hβ : ∀ (g : G) (a : A) (b : B), β (g • a) (g • b) = g • β a b)
    (p q n : ℕ) (h : p + q = n) (a : (Fin p → G) → A) (b : (Fin q → G) → B) :
    dFun k n (cupFun β p q n h a b) =
      cupFun β (p + 1) q (n + 1) (by omega) (dFun k p a) b +
        (-1 : k) ^ p • cupFun β p (q + 1) (n + 1) (by omega) a (dFun k q b) :=
  cupFun_leibniz β hβ p q n h a b

/-- The Leibniz rule stated for the bilinear map `cup` (Brown, *Cohomology of Groups*,
Ch. V §3). -/
theorem cup_leibniz (β : A →ₗ[k] B →ₗ[k] T)
    (hβ : ∀ (g : G) (a : A) (b : B), β (g • a) (g • b) = g • β a b)
    (p q n : ℕ) (h : p + q = n) (a : (Fin p → G) → A) (b : (Fin q → G) → B) :
    (inhomogeneousCochains.d (Rep.ofDistribMulAction k G T) n).hom (cup β p q n h a b) =
      cup β (p + 1) q (n + 1) (by omega)
          ((inhomogeneousCochains.d (Rep.ofDistribMulAction k G A) p).hom a) b +
        (-1 : k) ^ p • cup β p (q + 1) (n + 1) (by omega) a
          ((inhomogeneousCochains.d (Rep.ofDistribMulAction k G B) q).hom b) :=
  cupFun_leibniz β hβ p q n h a b

omit [DistribMulAction G A] [SMulCommClass G k A] [SMulCommClass G k B] [DistribMulAction G T]
  [SMulCommClass G k T] in
/-- The cup product with the zero cochain on the left vanishes. -/
@[simp]
theorem cupFun_zero_left (β : A →ₗ[k] B →ₗ[k] T) (p q n : ℕ) (h : p + q = n)
    (b : (Fin q → G) → B) : cupFun β p q n h (0 : (Fin p → G) → A) b = 0 := by
  funext g
  simp [cupFun]

omit [DistribMulAction G A] [SMulCommClass G k A] [SMulCommClass G k B] [DistribMulAction G T]
  [SMulCommClass G k T] in
/-- The cup product with the zero cochain on the right vanishes. -/
@[simp]
theorem cupFun_zero_right (β : A →ₗ[k] B →ₗ[k] T) (p q n : ℕ) (h : p + q = n)
    (a : (Fin p → G) → A) : cupFun β p q n h a (0 : (Fin q → G) → B) = 0 := by
  funext g
  simp [cupFun]

/-- The cup product of two cocycles is a cocycle (Brown, *Cohomology of Groups*, Ch. V §3). -/
theorem cupFun_isCocycle (β : A →ₗ[k] B →ₗ[k] T)
    (hβ : ∀ (g : G) (a : A) (b : B), β (g • a) (g • b) = g • β a b)
    (p q n : ℕ) (h : p + q = n) {a : (Fin p → G) → A} {b : (Fin q → G) → B}
    (ha : (inhomogeneousCochains.d (Rep.ofDistribMulAction k G A) p).hom a = 0)
    (hb : (inhomogeneousCochains.d (Rep.ofDistribMulAction k G B) q).hom b = 0) :
    (inhomogeneousCochains.d (Rep.ofDistribMulAction k G T) n).hom (cupFun β p q n h a b) = 0 := by
  have ha' : dFun k p a = 0 := ha
  have hb' : dFun k q b = 0 := hb
  have e := dFun_cupFun β hβ p q n h a b
  rw [ha', hb', cupFun_zero_left, cupFun_zero_right, smul_zero, add_zero] at e
  exact e

/-- A coboundary cupped with a cocycle is a coboundary: `(d c) ∪ b = d (c ∪ b)` if `d b = 0`
(Brown, *Cohomology of Groups*, Ch. V §3). -/
theorem cupFun_coboundary_left (β : A →ₗ[k] B →ₗ[k] T)
    (hβ : ∀ (g : G) (a : A) (b : B), β (g • a) (g • b) = g • β a b)
    (p q n : ℕ) (h : p + q = n) (c : (Fin p → G) → A) {b : (Fin q → G) → B}
    (hb : (inhomogeneousCochains.d (Rep.ofDistribMulAction k G B) q).hom b = 0) :
    cupFun β (p + 1) q (n + 1) (by omega)
        ((inhomogeneousCochains.d (Rep.ofDistribMulAction k G A) p).hom c) b =
      (inhomogeneousCochains.d (Rep.ofDistribMulAction k G T) n).hom (cupFun β p q n h c b) := by
  have hb' : dFun k q b = 0 := hb
  have e := dFun_cupFun β hβ p q n h c b
  rw [hb', cupFun_zero_right, smul_zero, add_zero] at e
  exact e.symm

/-- A cocycle cupped with a coboundary is a coboundary:
`a ∪ (d c) = (-1)ᵖ d (a ∪ c)` if `d a = 0` (Brown, *Cohomology of Groups*, Ch. V §3). -/
theorem cupFun_coboundary_right (β : A →ₗ[k] B →ₗ[k] T)
    (hβ : ∀ (g : G) (a : A) (b : B), β (g • a) (g • b) = g • β a b)
    (p q n : ℕ) (h : p + q = n) {a : (Fin p → G) → A} (c : (Fin q → G) → B)
    (ha : (inhomogeneousCochains.d (Rep.ofDistribMulAction k G A) p).hom a = 0) :
    cupFun β p (q + 1) (n + 1) (by omega) a
        ((inhomogeneousCochains.d (Rep.ofDistribMulAction k G B) q).hom c) =
      (-1 : k) ^ p •
        (inhomogeneousCochains.d (Rep.ofDistribMulAction k G T) n).hom (cupFun β p q n h a c) := by
  have ha' : dFun k p a = 0 := ha
  have e := dFun_cupFun β hβ p q n h a c
  rw [ha', cupFun_zero_left, zero_add] at e
  show cupFun β p (q + 1) (n + 1) _ a (dFun k q c) = (-1 : k) ^ p • dFun k n (cupFun β p q n h a c)
  rw [e, smul_smul, ← pow_add, ← two_mul, pow_mul, neg_one_sq, one_pow, one_smul]

section Continuity

omit [Group G] in
/-- The head product `g ↦ g₀ ⋯ g_{p-1}` is continuous on `Gⁿ` for a topological monoid `G`. -/
theorem continuous_headProd {G : Type u} [Monoid G] [TopologicalSpace G] [ContinuousMul G]
    (p n : ℕ) (hp : p ≤ n) : Continuous (headProd p n hp : (Fin n → G) → G) := by
  induction p with
  | zero =>
    have e : (headProd 0 n hp : (Fin n → G) → G) = fun _ => 1 :=
      funext fun g => headProd_zero n hp g
    rw [e]
    exact continuous_const
  | succ p ih =>
    have e : (headProd (p + 1) n hp : (Fin n → G) → G) =
        fun g => headProd p n (by omega) g * g ⟨p, by omega⟩ :=
      funext fun g => headProd_succ p n hp g
    rw [e]
    exact (ih _).mul (continuous_apply _)

omit [DistribMulAction G A] [SMulCommClass G k A] [SMulCommClass G k B] [DistribMulAction G T]
  [SMulCommClass G k T] in
/-- The cup product of continuous cochains is continuous, for a topological group `G` acting
continuously on `B` and a jointly continuous pairing `β`
(Neukirch–Schmidt–Wingberg, *Cohomology of Number Fields*, Ch. I §4). -/
theorem continuous_cupFun [TopologicalSpace G] [IsTopologicalGroup G] [TopologicalSpace A]
    [TopologicalSpace B] [TopologicalSpace T] [ContinuousSMul G B] (β : A →ₗ[k] B →ₗ[k] T)
    (hβc : Continuous fun x : A × B => β x.1 x.2) (p q n : ℕ) (h : p + q = n)
    {a : (Fin p → G) → A} {b : (Fin q → G) → B} (ha : Continuous a) (hb : Continuous b) :
    Continuous (cupFun β p q n h a b) := by
  have h1 : Continuous fun g : Fin n → G => a fun i => g (Fin.castLE (by omega) i) :=
    ha.comp (continuous_pi fun i => continuous_apply _)
  have h2 : Continuous fun g : Fin n → G => b fun j => g ⟨p + j, by omega⟩ :=
    hb.comp (continuous_pi fun j => continuous_apply _)
  have h3 : Continuous fun g : Fin n → G =>
      headProd p n (by omega) g • b fun j => g ⟨p + j, by omega⟩ :=
    (continuous_headProd p n (by omega)).smul h2
  exact hβc.comp (h1.prodMk h3)

omit [DistribMulAction G A] [SMulCommClass G k A] [SMulCommClass G k B] [DistribMulAction G T]
  [SMulCommClass G k T] in
/-- For discrete modules `A` and `B` every pairing is jointly continuous, so the cup product of
continuous cochains is continuous (Neukirch–Schmidt–Wingberg, *Cohomology of Number Fields*,
Ch. I §4). -/
theorem continuous_cupFun_of_discrete [TopologicalSpace G] [IsTopologicalGroup G]
    [TopologicalSpace A] [DiscreteTopology A] [TopologicalSpace B] [DiscreteTopology B]
    [TopologicalSpace T] [ContinuousSMul G B] (β : A →ₗ[k] B →ₗ[k] T) (p q n : ℕ)
    (h : p + q = n) {a : (Fin p → G) → A} {b : (Fin q → G) → B} (ha : Continuous a)
    (hb : Continuous b) : Continuous (cupFun β p q n h a b) :=
  continuous_cupFun β continuous_of_discreteTopology p q n h ha hb

end Continuity

omit [DistribMulAction G A] [SMulCommClass G k A] [SMulCommClass G k B] [DistribMulAction G T]
  [SMulCommClass G k T] in
/-- **Restriction compatibility.** For a group homomorphism `φ : H →* G` and an `H`-action on
`B` obtained by restriction along `φ`, the cup product commutes with pulling cochains back along
`φ` (Brown, *Cohomology of Groups*, Ch. V §3; Neukirch–Schmidt–Wingberg, *Cohomology of
Number Fields*, Ch. I §4). -/
theorem cupFun_comp {H : Type u} [Group H] [DistribMulAction H B] (β : A →ₗ[k] B →ₗ[k] T)
    (φ : H →* G) (hB : ∀ (x : H) (b : B), x • b = φ x • b)
    (p q n : ℕ) (h : p + q = n) (a : (Fin p → G) → A) (b : (Fin q → G) → B) :
    (cupFun (G := H) β p q n h (fun x => a (φ ∘ x)) (fun x => b (φ ∘ x))) =
      fun x => cupFun β p q n h a b (φ ∘ x) := by
  funext x
  simp only [cupFun]
  rw [hB, map_headProd]
  rfl

end Group

section Examples

/-- The multiplication pairing on a commutative `R`-algebra `S` is equivariant for the action
of the automorphism group `S ≃ₐ[R] S` (the Galois-type action), so the Leibniz rule applies. -/
theorem mul_pairing_equivariant {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
    (g : S ≃ₐ[R] S) (a b : S) :
    LinearMap.mul R S (g • a) (g • b) = g • LinearMap.mul R S a b := by
  simp [AlgEquiv.smul_def]

/-- The Leibniz rule instantiated for the Galois-type action of `S ≃ₐ[R] S` on `S` with the
multiplication pairing (Brown, *Cohomology of Groups*, Ch. V §3). -/
theorem cupFun_leibniz_mul {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
    (p q n : ℕ) (h : p + q = n) (a : (Fin p → (S ≃ₐ[R] S)) → S)
    (b : (Fin q → (S ≃ₐ[R] S)) → S) :
    (inhomogeneousCochains.d (Rep.ofDistribMulAction R (S ≃ₐ[R] S) S) n).hom
        (cupFun (LinearMap.mul R S) p q n h a b) =
      cupFun (LinearMap.mul R S) (p + 1) q (n + 1) (by omega)
          ((inhomogeneousCochains.d (Rep.ofDistribMulAction R (S ≃ₐ[R] S) S) p).hom a) b +
        (-1 : R) ^ p • cupFun (LinearMap.mul R S) p (q + 1) (n + 1) (by omega) a
          ((inhomogeneousCochains.d (Rep.ofDistribMulAction R (S ≃ₐ[R] S) S) q).hom b) :=
  cupFun_leibniz _ mul_pairing_equivariant p q n h a b

/-- Degree zero: `1 ∪ 1 = 1` for the multiplication pairing. -/
example {R S : Type u} [CommRing R] [CommRing S] [Algebra R S] :
    cupFun (G := S ≃ₐ[R] S) (LinearMap.mul R S) 0 0 0 rfl (fun _ => (1 : S)) (fun _ => (1 : S)) =
      fun _ => 1 := by
  funext g
  simp [cupFun, headProd_zero]

/-- In every bidegree `(p, q)`, the cup product of the constant cochains with value `1` (for the
Galois-type action of `S ≃ₐ[R] S` on `S` and the multiplication pairing) is the constant cochain
with value `1`, because automorphisms fix `1`. -/
theorem cupFun_one_one {R S : Type u} [CommRing R] [CommRing S] [Algebra R S] (p q n : ℕ)
    (h : p + q = n) :
    cupFun (G := S ≃ₐ[R] S) (LinearMap.mul R S) p q n h (fun _ => (1 : S)) (fun _ => (1 : S)) =
      fun _ => 1 := by
  funext g
  simp [cupFun]

/-- Degree one: the cup product of the two nonzero constant `1`-cochains with value `1` is the
nonzero `2`-cochain `(g₀, g₁) ↦ g₀(1) = 1`. -/
example : cupFun (G := ℚ ≃ₐ[ℚ] ℚ) (LinearMap.mul ℚ ℚ) 1 1 2 rfl (fun _ => (1 : ℚ))
    (fun _ => (1 : ℚ)) ≠ 0 := by
  intro h0
  have h1 := congrFun h0 (fun _ => 1)
  simp [cupFun] at h1

/-- The constant `1`-cochain with value `1` used above is nonzero. -/
example : (fun _ => (1 : ℚ) : (Fin 1 → (ℚ ≃ₐ[ℚ] ℚ)) → ℚ) ≠ 0 := by
  intro h0
  have h1 := congrFun h0 (fun _ => 1)
  simp at h1

end Examples

end

end ZInQ.Manuscript.RC.SelmerComplex
