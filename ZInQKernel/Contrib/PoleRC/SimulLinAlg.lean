import Mathlib

/-!
# The `𝔽₂` linear algebra of the simultaneous construction (S12, lines 585–688)

S12 is Elliot Glazer's retained source (upstream repository,
`research/version14/retained-sources/parity-frozen-4eaee875.tex`; Lemma
`par:simultaneous-matrices`, lines 543–703). Vectors are functions `α → 𝔽₂`, a support is
a `Finset α`, and the manuscript's matrix (`diophantine_zq.tex` line 1038, S12 `(par:matrices)`)
is the operator

  `(Kv)_i = Σ_{j ∈ P, j ≠ i} L j i (v_j + v_i)`,   `L j i = [q_j/q_i]`.

* `sharp`: `K♯ = K + λaᵗ` with `a = e_{q₀} + e_{b*}` (S12 lines 585–598).
* `target_of_sharp_ker`: `K = K♯T` with `T = Id − 1_B aᵗ`, and `ker K♯ = ⟨1⟩` gives
  `ker K = ⟨1, 1_B⟩` and `λ ∉ im K` (S12 lines 599–616).
* `sharp_ker_of_deleted`: nonsingularity of `K♯` with the `q₀` row and column deleted gives
  `ker K♯ = ⟨1⟩` (S12 lines 618–625).
* `block_nonsing`: the deleted matrix `[[A, C], [Cᵗ, 0]]` on `B ∪ I` is nonsingular, where `C`
  has columns `e_b + e_{b_d}` (S12 lines 627–672; the column choice is the manuscript's "columns
  `e_i + e_d`", line 1045). It is stated on any support `P' ⊇ B ∪ I` whose extra symbols have zero
  `B`-row sums, so it also gives the principal `B ∪ I` block on the larger support (S12 674–677).
* `toggle`: if the principal block on `S` is nonsingular, toggling the diagonal entries of
  `R` (disjoint from `S`) by suitable bits makes the matrix on `S ∪ R` nonsingular (S12 677–688).

`NonsingOn F U` says that `F` kills no nonzero vector supported on `U` (equations on `U`).
-/

namespace ZInQ.Manuscript.PoleRC.Simul

open Finset

theorem sim_add_self (x : ZMod 2) : x + x = 0 := by fin_cases x <;> decide

theorem sim_eq_of_add_eq_zero {x y : ZMod 2} (h : x + y = 0) : x = y := by
  revert h; revert x y; decide

theorem sim_cases (x : ZMod 2) : x = 0 ∨ x = 1 := by revert x; decide

theorem sim_solve : ∀ x y z w : ZMod 2, x + (y + z) * w = y → x = y + (y + z) * w := by decide

variable {α : Type*} [DecidableEq α]

/-- The manuscript's matrix `K` as an operator (line 1038, S12 `(par:matrices)`):
`(Kv)_i = Σ_{j ∈ P, j ≠ i} L j i (v_j + v_i)`, with `L j i = [q_j/q_i]`. -/
def kOp (L : α → α → ZMod 2) (P : Finset α) (v : α → ZMod 2) (i : α) : ZMod 2 :=
  ∑ j ∈ P.erase i, L j i * (v j + v i)

section kOp

variable (L : α → α → ZMod 2) (P : Finset α)

theorem kOp_add (v w : α → ZMod 2) (i : α) :
    kOp L P (fun j => v j + w j) i = kOp L P v i + kOp L P w i := by
  unfold kOp; rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun j _ => by ring

theorem kOp_smul (c : ZMod 2) (v : α → ZMod 2) (i : α) :
    kOp L P (fun j => c * v j) i = c * kOp L P v i := by
  unfold kOp; rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun j _ => by ring

/-- `K1 = 0`. -/
theorem kOp_const (c : ZMod 2) (i : α) : kOp L P (fun _ => c) i = 0 :=
  Finset.sum_eq_zero fun j _ => by rw [sim_add_self, mul_zero]

theorem kOp_add_const (v : α → ZMod 2) (c : ZMod 2) (i : α) :
    kOp L P (fun j => v j + c) i = kOp L P v i := by
  rw [kOp_add, kOp_const, add_zero]

theorem kOp_congr {v w : α → ZMod 2} {i : α} (hi : i ∈ P) (h : ∀ j ∈ P, v j = w j) :
    kOp L P v i = kOp L P w i :=
  Finset.sum_congr rfl fun j hj => by rw [h j (Finset.mem_of_mem_erase hj), h i hi]

theorem kOp_insert {q0 : α} (hq0 : q0 ∉ P) (v : α → ZMod 2) {i : α} (hi : i ∈ P) :
    kOp L (insert q0 P) v i = L q0 i * (v q0 + v i) + kOp L P v i := by
  unfold kOp
  have hne : q0 ≠ i := fun h => hq0 (h ▸ hi)
  rw [Finset.erase_insert_of_ne hne,
    Finset.sum_insert (fun h => hq0 (Finset.mem_of_mem_erase h))]

/-- `K1_B` (the indicator of `B ⊆ P`): at `i ∉ B` the sum of the `B`-symbols, at `i ∈ B` the
sum of the symbols from outside `B`. -/
theorem kOp_ind {Bs : Finset α} (hB : Bs ⊆ P) (i : α) :
    kOp L P (fun j => if j ∈ Bs then 1 else 0) i =
      if i ∈ Bs then ∑ j ∈ P \ Bs, L j i else ∑ j ∈ Bs, L j i := by
  unfold kOp
  by_cases hiB : i ∈ Bs
  · rw [if_pos hiB]
    have h : ∀ j ∈ P.erase i, L j i * ((if j ∈ Bs then 1 else 0) + if i ∈ Bs then 1 else 0) =
        if j ∈ P \ Bs then L j i else 0 := by
      intro j hj
      have hjP := Finset.mem_of_mem_erase hj
      by_cases hjB : j ∈ Bs
      · simp [hjB, hiB, sim_add_self]
      · simp [hjB, hiB, hjP]
    rw [Finset.sum_congr rfl h, Finset.sum_ite_mem]
    congr 1
    ext j; simp only [Finset.mem_inter, Finset.mem_erase, Finset.mem_sdiff]
    constructor
    · rintro ⟨⟨_, h1⟩, h2⟩; exact h2
    · rintro ⟨h1, h2⟩; exact ⟨⟨fun h => h2 (h ▸ hiB), h1⟩, h1, h2⟩
  · rw [if_neg hiB]
    have h : ∀ j ∈ P.erase i, L j i * ((if j ∈ Bs then 1 else 0) + if i ∈ Bs then 1 else 0) =
        if j ∈ Bs then L j i else 0 := by
      intro j _
      by_cases hjB : j ∈ Bs <;> simp [hjB, hiB]
    rw [Finset.sum_congr rfl h, Finset.sum_ite_mem]
    congr 1
    ext j; simp only [Finset.mem_inter, Finset.mem_erase]
    constructor
    · rintro ⟨_, h⟩; exact h
    · intro h; exact ⟨⟨fun h' => hiB (h' ▸ h), hB h⟩, h⟩

end kOp

/-! ### The rank-one correction (S12 lines 585–625) -/

/-- `K♯ = K + λaᵗ` with `a = e_{q₀} + e_{b*}` (S12 lines 585–598). -/
def sharp (L : α → α → ZMod 2) (P : Finset α) (lam : α → ZMod 2) (q0 bs : α)
    (v : α → ZMod 2) (i : α) : ZMod 2 :=
  kOp L P v i + lam i * (v q0 + v bs)

/-- **`K = K♯T`** (S12 `(par:projection-factorization)`): with `T v = v + (aᵗv)1_B`,
`K♯(Tv) = Kv`, given `K1_B = 0` and `aᵗ1_B = 1`. -/
theorem sharp_T (L : α → α → ZMod 2) (P : Finset α) (lam e : α → ZMod 2) (q0 bs : α)
    (he0 : e q0 = 0) (heb : e bs = 1) (v : α → ZMod 2) {i : α} (hKe : kOp L P e i = 0) :
    sharp L P lam q0 bs (fun j => v j + (v q0 + v bs) * e j) i = kOp L P v i := by
  unfold sharp
  rw [kOp_add, kOp_smul, hKe]
  dsimp only
  rw [he0, heb]
  have h4 : ∀ x z : ZMod 2, x + (x + z) * 0 + (z + (x + z) * 1) = 0 := by decide
  rw [h4]; ring

/-- **S12 lines 599–616.** If `ker K♯ = ⟨1⟩`, `K1_B = 0`, `aᵗ1_B = 1` (`1_B(q₀) = 0`,
`1_B(b*) = 1`), then `ker K = ⟨1, 1_B⟩` (every kernel vector is `c1 + d1_B` on `P`) and
`λ ∉ im K`. -/
theorem target_of_sharp_ker (L : α → α → ZMod 2) (P : Finset α) (lam e : α → ZMod 2)
    (q0 bs : α) (hbs : bs ∈ P) (he0 : e q0 = 0) (heb : e bs = 1)
    (hKe : ∀ i ∈ P, kOp L P e i = 0)
    (hker : ∀ x : α → ZMod 2, (∀ i ∈ P, sharp L P lam q0 bs x i = 0) → ∀ i ∈ P, x i = x q0) :
    (∀ v : α → ZMod 2, (∀ i ∈ P, kOp L P v i = 0) →
      ∀ i ∈ P, v i = v q0 + (v q0 + v bs) * e i) ∧
    (∀ u : α → ZMod 2, ¬ ∀ i ∈ P, kOp L P u i = lam i) := by
  constructor
  · -- If `Kx = 0`, then `Tx ∈ ker K♯ = ⟨1⟩`, so `x = c1 + (aᵗx)1_B`.
    intro v hv i hi
    have h := hker (fun j => v j + (v q0 + v bs) * e j)
      (fun j hj => by rw [sharp_T L P lam e q0 bs he0 heb v (hKe j hj)]; exact hv j hj) i hi
    simp only [he0, mul_zero, add_zero] at h
    exact sim_solve _ _ _ _ h
  · -- If `Kx = λ`, put `y = Tx`; then `K♯(y − 1_B) = 0`, and applying `aᵗ` gives `−1 = 0`.
    intro u hu
    set a := u q0 + u bs with ha
    have h := hker (fun j => u j + a * e j + e j) (fun j hj => by
      unfold sharp
      rw [kOp_add, kOp_add, kOp_smul, hKe j hj, hu j hj]
      dsimp only
      rw [he0, heb]
      have : u q0 + a * 0 + 0 + (u bs + a * 1 + 1) = 1 := by
        rw [ha]; ring_nf; rw [show (2 : ZMod 2) = 0 from rfl]; ring
      rw [this, mul_zero, add_zero, add_zero, mul_one, sim_add_self]) bs hbs
    simp only [he0, heb, mul_zero, mul_one, add_zero] at h
    rw [ha] at h
    generalize u q0 = x at h; generalize u bs = z at h
    revert x z h; decide

/-- **S12 lines 618–625.** If the matrix `K♯` with the `q₀` row and column deleted is
nonsingular, then `ker K♯ = ⟨1⟩`: subtract `x_{q₀}1` and use `K♯1 = 0`. -/
theorem sharp_ker_of_deleted (L : α → α → ZMod 2) (P : Finset α) (lam : α → ZMod 2)
    (q0 bs : α)
    (hM : ∀ v : α → ZMod 2, v q0 = 0 →
      (∀ i ∈ P, i ≠ q0 → sharp L P lam q0 bs v i = 0) → ∀ i ∈ P, v i = 0)
    (x : α → ZMod 2) (hx : ∀ i ∈ P, sharp L P lam q0 bs x i = 0) : ∀ i ∈ P, x i = x q0 := by
  have h := hM (fun i => x i + x q0) (sim_add_self _) (fun i hi _ => by
    have hxi := hx i hi
    unfold sharp at hxi ⊢
    rw [kOp_add_const]
    have : x q0 + x q0 + (x bs + x q0) = x q0 + x bs := by
      rw [sim_add_self, zero_add, add_comm]
    rw [this]; exact hxi)
  intro i hi
  exact sim_eq_of_add_eq_zero (h i hi)

/-! ### The deleted matrix -/

/-- **The matrix `K♯` with the `q₀` row and column deleted**, on a support `P'` with
`q₀ ∉ P'`: the `q₀`-symbols `y i = [q₀/q_i]` survive only on the diagonal. -/
def dOp (L : α → α → ZMod 2) (P' : Finset α) (y lam : α → ZMod 2) (bs : α)
    (v : α → ZMod 2) (i : α) : ZMod 2 :=
  kOp L P' v i + y i * v i + lam i * v bs

theorem dOp_add (L : α → α → ZMod 2) (P' : Finset α) (y lam : α → ZMod 2) (bs : α)
    (v w : α → ZMod 2) : dOp L P' y lam bs (v + w) = dOp L P' y lam bs v + dOp L P' y lam bs w := by
  funext i
  simp only [dOp, Pi.add_apply]
  rw [show (v + w) = fun j => v j + w j from rfl, kOp_add]; ring

theorem sharp_eq_dOp (L : α → α → ZMod 2) (P' : Finset α) {q0 : α} (hq0 : q0 ∉ P')
    (lam : α → ZMod 2) (bs : α) (v : α → ZMod 2) (hv : v q0 = 0) {i : α} (hi : i ∈ P') :
    sharp L (insert q0 P') lam q0 bs v i = dOp L P' (fun j => L q0 j) lam bs v i := by
  unfold sharp dOp; rw [kOp_insert L P' hq0 v hi, hv]; ring

/-- `F` kills no nonzero vector supported on `U` (equations on `U`): the principal submatrix
on `U` is nonsingular. -/
def NonsingOn (F : (α → ZMod 2) → α → ZMod 2) (U : Finset α) : Prop :=
  ∀ v : α → ZMod 2, (∀ i ∉ U, v i = 0) → (∀ i ∈ U, F v i = 0) → ∀ i, v i = 0

omit [DecidableEq α] in
theorem NonsingOn.congr {F G : (α → ZMod 2) → α → ZMod 2} {U : Finset α} (hF : NonsingOn F U)
    (h : ∀ v, ∀ i ∈ U, G v i = F v i) : NonsingOn G U :=
  fun v hout hker => hF v hout fun i hi => by rw [← h v i hi]; exact hker i hi

/-- Deleted nonsingularity in the form used by `sharp_ker_of_deleted`. -/
theorem deleted_of_nonsing (L : α → α → ZMod 2) (P' : Finset α) {q0 : α} (hq0 : q0 ∉ P')
    (lam : α → ZMod 2) {bs : α} (hbs : bs ∈ P')
    (hN : NonsingOn (dOp L P' (fun j => L q0 j) lam bs) P') :
    ∀ v : α → ZMod 2, v q0 = 0 → (∀ i ∈ insert q0 P', i ≠ q0 →
      sharp L (insert q0 P') lam q0 bs v i = 0) → ∀ i ∈ insert q0 P', v i = 0 := by
  intro v hv0 hv
  have h := hN (fun i => if i ∈ P' then v i else 0) (fun i hi => if_neg hi) (fun i hi => by
    have hne : i ≠ q0 := fun h => hq0 (h ▸ hi)
    have := hv i (Finset.mem_insert_of_mem hi) hne
    rw [sharp_eq_dOp L P' hq0 lam bs v hv0 hi] at this
    unfold dOp at this ⊢
    rw [kOp_congr L P' hi (fun j hj => if_pos hj)]
    dsimp only
    rw [if_pos hi, if_pos hbs]
    exact this)
  intro i hi
  rcases Finset.mem_insert.mp hi with rfl | hi'
  · exact hv0
  · have := h i; rwa [if_pos hi'] at this

/-! ### Toggling diagonal entries (S12 lines 677–688) -/

/-- **One toggle.** If the principal block on `U` is nonsingular and `r ∉ U`, one of the two
values of the `r`-th diagonal toggle makes the block on `U ∪ {r}` nonsingular. (Kernel form of
`det(M + X E_rr) = det M_{U∪r} + X det M_U` with `det M_U = 1`: the step `f = f₀ + X f₁` of
S12's induction, lines 684–686.) -/
theorem toggle_one (F : (α → ZMod 2) → α → ZMod 2) (hF : ∀ v w, F (v + w) = F v + F w)
    {U : Finset α} (hU : NonsingOn F U) {r : α} (hr : r ∉ U) :
    ∃ c : ZMod 2, NonsingOn (fun v i => F v i + (if i = r then c else 0) * v i) (insert r U) := by
  -- a kernel vector vanishing at `r` vanishes
  have key : ∀ (c : ZMod 2) (v : α → ZMod 2), (∀ i ∉ insert r U, v i = 0) →
      (∀ i ∈ insert r U, F v i + (if i = r then c else 0) * v i = 0) → v r = 0 →
      ∀ i, v i = 0 := by
    intro c v hout hker hvr
    refine hU v (fun i hi => ?_) (fun i hi => ?_)
    · by_cases hir : i = r
      · rw [hir]; exact hvr
      · exact hout i (by simp [hir, hi])
    · have h := hker i (Finset.mem_insert_of_mem hi)
      have hir : i ≠ r := fun h => hr (h ▸ hi)
      simpa [hir] using h
  by_contra hcon
  push Not at hcon
  have e0 := hcon 0
  have e1 := hcon 1
  unfold NonsingOn at e0 e1
  push Not at e0 e1
  obtain ⟨v0, hv0out, hv0, i0, hi0⟩ := e0
  obtain ⟨v1, hv1out, hv1, i1, hi1⟩ := e1
  have hv0r : v0 r = 1 := by
    rcases sim_cases (v0 r) with h | h
    · exact absurd (key 0 v0 hv0out hv0 h i0) hi0
    · exact h
  have hv1r : v1 r = 1 := by
    rcases sim_cases (v1 r) with h | h
    · exact absurd (key 1 v1 hv1out hv1 h i1) hi1
    · exact h
  -- `v₀ = v₁`
  have hw : ∀ i, (v0 + v1) i = 0 := by
    refine hU (v0 + v1) (fun i hi => ?_) (fun i hi => ?_)
    · by_cases hir : i = r
      · rw [hir, Pi.add_apply, hv0r, hv1r]; rfl
      · rw [Pi.add_apply, hv0out i (by simp [hir, hi]), hv1out i (by simp [hir, hi]), add_zero]
    · rw [hF, Pi.add_apply]
      have a0 := hv0 i (Finset.mem_insert_of_mem hi)
      have a1 := hv1 i (Finset.mem_insert_of_mem hi)
      have hir : i ≠ r := fun h => hr (h ▸ hi)
      simp only [hir, if_false, zero_mul, add_zero] at a0 a1
      rw [a0, a1, add_zero]
  have heq : v1 = v0 := funext fun i => (sim_eq_of_add_eq_zero (hw i)).symm
  have a0 := hv0 r (Finset.mem_insert_self _ _)
  have a1 := hv1 r (Finset.mem_insert_self _ _)
  simp only [if_true, zero_mul, add_zero, one_mul] at a0 a1
  rw [heq, a0, hv0r] at a1
  exact absurd a1 (by decide)

/-- **The toggles** (S12 lines 677–688). If the principal block on `S` is nonsingular, there are
diagonal toggles `t`, supported on `R` (disjoint from `S`), making the block on `S ∪ R`
nonsingular. S12 argues with the determinant: it is multilinear in the toggles with
full-product coefficient `det M₀ = 1`, and a nonzero multilinear polynomial over `𝔽₂` has a
nonzero value (induction on the number of variables, `f = f₀ + X f₁`). The same induction is
done here on `R`, with `toggle_one` as the step. -/
theorem toggle (F : (α → ZMod 2) → α → ZMod 2) (hF : ∀ v w, F (v + w) = F v + F w)
    {S : Finset α} (hS : NonsingOn F S) (R : Finset α) (hSR : Disjoint S R) :
    ∃ t : α → ZMod 2, (∀ i ∉ R, t i = 0) ∧
      NonsingOn (fun v i => F v i + t i * v i) (S ∪ R) := by
  induction R using Finset.induction_on with
  | empty =>
    refine ⟨fun _ => 0, fun _ _ => rfl, ?_⟩
    rw [Finset.union_empty]
    exact hS.congr fun v i _ => by simp
  | insert r R hrR ih =>
    have hS' : Disjoint S R := Finset.disjoint_of_subset_right (Finset.subset_insert _ _) hSR
    have hrS : r ∉ S := fun h => Finset.disjoint_left.mp hSR h (Finset.mem_insert_self _ _)
    obtain ⟨t, ht, hnt⟩ := ih hS'
    have hFt : ∀ v w, (fun v i => F v i + t i * v i) (v + w) =
        (fun v i => F v i + t i * v i) v + (fun v i => F v i + t i * v i) w := by
      intro v w; funext i; simp only [hF, Pi.add_apply]; ring
    have hrU : r ∉ S ∪ R := by simp [hrS, hrR]
    obtain ⟨c, hc⟩ := toggle_one _ hFt hnt hrU
    refine ⟨fun i => t i + if i = r then c else 0, fun i hi => ?_, ?_⟩
    · have h1 : i ∉ R := fun h => hi (Finset.mem_insert_of_mem h)
      have h2 : i ≠ r := fun h => hi (h ▸ Finset.mem_insert_self _ _)
      simp [ht i h1, h2]
    · have hU : S ∪ insert r R = insert r (S ∪ R) := by
        ext x; simp only [Finset.mem_union, Finset.mem_insert]; tauto
      rw [hU]
      exact hc.congr fun v i _ => by ring

/-! ### The block `[[A, C], [Cᵗ, 0]]` (S12 lines 627–672) -/

section block

variable (L : α → α → ZMod 2) (P' Bs : Finset α) (bd bs : α) (pI : α → α) (y lam : α → ZMod 2)

/-- **The deleted matrix on `B ∪ I` is nonsingular** (S12 lines 651–672). Here `I` is the image
of `B ∖ {b_d}` under `pI`, the `I`-slot `pI b` has `C`-column `e_b + e_{b_d}` (`hcol`, `hrow`;
all other symbols incident with `I` vanish), `y = [q₀/·]` is zero on `I` and is the `C`-row sum
on `B` (S12 lines 636–639), `λ = 0` on `I`, `Σ_B λ = 1`, and the symbols from `P' ∖ (B ∪ I)` (the
support of `θ`) have zero `B`-row sums (S12 `(par:cross-symbol-sums)`). The proof is S12's:
`Cᵗx = 0` makes `x` constant on `B`, the `1_Bᵗ`-sum of the first block equation makes the
constant zero, and the injectivity of `C` makes the `I`-part zero. -/
theorem block_nonsing (Is : Finset α) (hIs : Is = (Bs.erase bd).image pI)
    (hBP : Bs ⊆ P') (hbd : bd ∈ Bs) (hbs : bs ∈ Bs)
    (hIP : ∀ b ∈ Bs.erase bd, pI b ∈ P') (hIB : ∀ b ∈ Bs.erase bd, pI b ∉ Bs)
    (hinj : ∀ b ∈ Bs.erase bd, ∀ b' ∈ Bs.erase bd, pI b = pI b' → b = b')
    (hcol : ∀ b ∈ Bs.erase bd, ∀ j ∈ P', j ≠ pI b →
      L j (pI b) = (if j = b then 1 else 0) + (if j = bd then 1 else 0))
    (hrow : ∀ b ∈ Bs.erase bd, ∀ j ∈ Bs,
      L (pI b) j = (if j = b then 1 else 0) + (if j = bd then 1 else 0))
    (hyI : ∀ b ∈ Bs.erase bd, y (pI b) = 0) (hlamI : ∀ b ∈ Bs.erase bd, lam (pI b) = 0)
    (hyB : ∀ i ∈ Bs, y i = ∑ b ∈ Bs.erase bd, L (pI b) i)
    (hcross : ∀ i ∈ Bs, ∑ j ∈ P' \ (Bs ∪ Is), L j i = 0)
    (hlam : ∑ i ∈ Bs, lam i = 1) :
    NonsingOn (dOp L P' y lam bs) (Bs ∪ Is) := by
  intro v hout hker
  have hbdP : bd ∈ P' := hBP hbd
  -- the sum over `I`, reindexed by `B ∖ {b_d}`
  have hsumI : ∀ f : α → ZMod 2, ∑ j ∈ Is, f j = ∑ b ∈ Bs.erase bd, f (pI b) := fun f => by
    rw [hIs]; exact Finset.sum_image fun b hb b' hb' h => hinj b hb b' hb' h
  have hmemI : ∀ j, j ∈ Is ↔ ∃ b ∈ Bs.erase bd, pI b = j := fun j => by
    rw [hIs, Finset.mem_image]
  -- Step 1 (`Cᵗx = 0`): `v` is constant on `B`.
  have hconst : ∀ b ∈ Bs, v b = v bd := by
    intro b hb
    by_cases hbb : b = bd
    · rw [hbb]
    have hbe : b ∈ Bs.erase bd := Finset.mem_erase.mpr ⟨hbb, hb⟩
    have hk := hker (pI b) (Finset.mem_union_right _ ((hmemI _).mpr ⟨b, hbe, rfl⟩))
    unfold dOp kOp at hk
    rw [hyI b hbe, hlamI b hbe, zero_mul, add_zero, zero_mul, add_zero] at hk
    have h2 : ∀ j ∈ P'.erase (pI b), L j (pI b) * (v j + v (pI b)) =
        (if j = b then v b + v (pI b) else 0) + (if j = bd then v bd + v (pI b) else 0) := by
      intro j hj
      rw [hcol b hbe j (Finset.mem_of_mem_erase hj) (Finset.ne_of_mem_erase hj)]
      by_cases h1 : j = b
      · rw [h1]; simp [hbb]
      · by_cases h3 : j = bd
        · have hne : ¬ bd = b := fun h => hbb h.symm
          rw [h3, if_neg hne, if_neg hne, if_pos rfl, if_pos rfl, zero_add, one_mul, zero_add]
        · simp [h1, h3]
    have hbI : pI b ≠ b := fun h => hIB b hbe (by rw [h]; exact hb)
    have hbdI : pI b ≠ bd := fun h => hIB b hbe (by rw [h]; exact hbd)
    rw [Finset.sum_congr rfl h2, Finset.sum_add_distrib, Finset.sum_ite_eq',
      Finset.sum_ite_eq', if_pos (Finset.mem_erase.mpr ⟨hbI.symm, hBP hb⟩),
      if_pos (Finset.mem_erase.mpr ⟨hbdI.symm, hbdP⟩)] at hk
    have : v b + v (pI b) + (v bd + v (pI b)) = v b + v bd := by
      ring_nf; rw [show (2 : ZMod 2) = 0 from rfl]; ring
    rw [this] at hk
    exact sim_eq_of_add_eq_zero hk
  -- the decomposition `v = c 1_B + w`, `w` supported on `I`
  set c := v bd with hc
  set e : α → ZMod 2 := fun j => if j ∈ Bs then 1 else 0 with he
  set w : α → ZMod 2 := fun j => if j ∈ Bs then 0 else v j with hw
  have hvdec : v = fun j => c * e j + w j := by
    funext j
    by_cases hj : j ∈ Bs
    · simp [he, hw, hj, hconst j hj]
    · simp [he, hw, hj]
  have hwB : ∀ j ∈ Bs, w j = 0 := fun j hj => by simp [hw, hj]
  have hwsupp : ∀ j, w j ≠ 0 → j ∈ Is := by
    intro j hj
    by_cases hjB : j ∈ Bs
    · exact absurd (hwB j hjB) hj
    · have hvj : v j ≠ 0 := by simpa [hw, hjB] using hj
      by_contra hjI
      exact hvj (hout j (by simp [hjB, hjI]))
  -- `K♯ 1_B = λ` on the `B` rows (S12 `(par:sharp-B)`)
  have hsplit : ∀ i ∈ Bs, ∑ j ∈ P' \ Bs, L j i = y i := by
    intro i hi
    have hsub : Is ⊆ P' \ Bs := by
      intro j hj
      obtain ⟨b, hb, rfl⟩ := (hmemI j).mp hj
      exact Finset.mem_sdiff.mpr ⟨hIP b hb, hIB b hb⟩
    rw [← Finset.sum_sdiff hsub]
    have hdiff : (P' \ Bs) \ Is = P' \ (Bs ∪ Is) := by
      ext j; simp only [Finset.mem_sdiff, Finset.mem_union]; tauto
    rw [hdiff, hcross i hi, zero_add, hsumI, hyB i hi]
  have hde : ∀ i ∈ Bs, dOp L P' y lam bs e i = lam i := by
    intro i hi
    unfold dOp
    rw [kOp_ind L P' hBP i, if_pos hi, hsplit i hi]
    simp only [he, if_pos hi, if_pos hbs, mul_one]
    rw [sim_add_self, zero_add]
  -- `1_Bᵗ` applied to the `B`-part of `K♯ w` vanishes (the column sums of `C`)
  have hdw : ∀ i ∈ Bs, dOp L P' y lam bs w i = ∑ j ∈ P', L j i * w j := by
    intro i hi
    unfold dOp kOp
    rw [hwB i hi, hwB bs hbs, mul_zero, add_zero, mul_zero, add_zero]
    simp only [add_zero]
    exact Finset.sum_erase P' (by rw [hwB i hi, mul_zero])
  have hcolsum : ∀ j ∈ P', w j * ∑ i ∈ Bs, L j i = 0 := by
    intro j _
    by_cases hj : w j = 0
    · rw [hj, zero_mul]
    · obtain ⟨b, hb, rfl⟩ := (hmemI j).mp (hwsupp j hj)
      have hb' := Finset.mem_of_mem_erase hb
      rw [Finset.sum_congr rfl (hrow b hb), Finset.sum_add_distrib, Finset.sum_ite_eq',
        Finset.sum_ite_eq', if_pos hb', if_pos hbd, sim_add_self, mul_zero]
  have hsumw : ∑ i ∈ Bs, dOp L P' y lam bs w i = 0 := by
    rw [Finset.sum_congr rfl hdw, Finset.sum_comm]
    refine Finset.sum_eq_zero fun j hj => ?_
    rw [← hcolsum j hj, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by ring
  -- Step 2 (`1_Bᵗ` of the first block equation): `c = 0`.
  have hdv : ∀ i, dOp L P' y lam bs v i = c * dOp L P' y lam bs e i + dOp L P' y lam bs w i := by
    intro i
    rw [hvdec]
    unfold dOp
    rw [kOp_add, kOp_smul]; ring
  have hc0 : c = 0 := by
    have h1 : ∑ i ∈ Bs, dOp L P' y lam bs v i = 0 :=
      Finset.sum_eq_zero fun i hi => hker i (Finset.mem_union_left _ hi)
    rw [Finset.sum_congr rfl fun i _ => hdv i, Finset.sum_add_distrib, hsumw, add_zero,
      ← Finset.mul_sum, Finset.sum_congr rfl hde, hlam, mul_one] at h1
    exact h1
  -- Step 3 (injectivity of `C`): `v = 0` on `I`.
  have hvI : ∀ b ∈ Bs.erase bd, v (pI b) = 0 := by
    intro b hb
    have hbB := Finset.mem_of_mem_erase hb
    have hbbd : b ≠ bd := Finset.ne_of_mem_erase hb
    have hk := hker b (Finset.mem_union_left _ hbB)
    rw [hdv, hc0, zero_mul, zero_add, hdw b hbB] at hk
    have h2 : ∀ j ∈ P', L j b * w j = if j = pI b then v (pI b) else 0 := by
      intro j _
      by_cases hjb : j = pI b
      · rw [if_pos hjb, hjb, hrow b hb b hbB, if_pos rfl, if_neg hbbd, add_zero, one_mul]
        simp [hw, hIB b hb]
      · rw [if_neg hjb]
        by_cases hwj : w j = 0
        · rw [hwj, mul_zero]
        · obtain ⟨b', hb', rfl⟩ := (hmemI j).mp (hwsupp j hwj)
          have hbb' : b ≠ b' := fun h => hjb (h ▸ rfl)
          rw [hrow b' hb' b hbB, if_neg hbb', if_neg hbbd, add_zero, zero_mul]
    rw [Finset.sum_congr rfl h2, Finset.sum_ite_eq', if_pos (hIP b hb)] at hk
    exact hk
  -- conclusion
  intro i
  by_cases hiB : i ∈ Bs
  · rw [hconst i hiB]; exact hc0
  · by_cases hiI : i ∈ Is
    · obtain ⟨b, hb, rfl⟩ := (hmemI i).mp hiI
      exact hvI b hb
    · exact hout i (by simp [hiB, hiI])

end block

end ZInQ.Manuscript.PoleRC.Simul
