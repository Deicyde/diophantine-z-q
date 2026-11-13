import ZInQKernel.RouteK.Rank5b.Sec3.Forest

/-!
# Rédei's formulas: `κ` as a forest count, Lemma 2.2, and the consequences (2.1), (2.2)

`docs/research/tyz-5b.md` §2.1–2.2.

* `kappa_eq_forests`: `κ_ρ(B)` is the number mod 2 of spanning arborescences of `B` rooted at `ρ`
  (Lemma 2.1 with `F = W = {ρ}`);
* `pmin_lapl_offdiag`: `det L_B[B∖i, B∖j] = κ_i(B)` (Lemma 2.2(2));
* `kappa_add_kappa` (**Lemma 2.2(3)**, `κ`-difference): `κ_i(B) + κ_j(B) = Σ_φ wt(φ) c(T_i(φ))` over the
  forests of `B` rooted at `{i, j}`, with `c` the column sums of `L_B`;
* `colSum_lapl`: under reciprocity, `c_v = y_v (1 + y(B))` (Lemma 2.2, first sentence);
* `kappa_eq_kappa` (**Lemma 2.2(1)**): if `y(B) = 1`, `κ_i(B) = κ_j(B)`;
* `redeiG_eq_kappa`, `sum_y_kappa`, `sum_z_kappa` (**(2.1)**), `sum_z_kappa_of_y_zero` (**(2.2)**).
-/

namespace ZInQ.RouteK.Rank5b.Sec3

open Finset Matrix

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Quadratic reciprocity for bits: `a_ij + a_ji = y_i y_j` for `i ≠ j`. -/
def Recip (a : ι → ι → ZMod 2) (y : ι → ZMod 2) : Prop :=
  ∀ i j, i ≠ j → a i j + a j i = y i * y j

theorem zmod2_mul_self (x : ZMod 2) : x * x = x := by revert x; decide

theorem kappa_eq_pmin (a : ι → ι → ZMod 2) (B : Finset ι) (ρ : ι) :
    kappa a B ρ = pmin (lapl a B) (B \ {ρ}) (B \ {ρ}) := by
  rw [kappa, det_submatrix_eq_pmin, Finset.sdiff_singleton_eq_erase]

theorem root_eq_of_not_mem {f : ι → ι} {U F : Finset ι} (hf : f ∈ mapsOn U (U \ F)) {x : ι}
    (hx : x ∉ U \ F) : root f x = x := root_of_fixed ((mem_mapsOn.1 hf).1 x hx)

/-- `κ_ρ(B)` counts the spanning arborescences of `B` rooted at `ρ` (tyz-5b §2.1, Consequences). -/
theorem kappa_eq_forests (a : ι → ι → ZMod 2) {B : Finset ι} {ρ : ι} (hρ : ρ ∈ B) :
    kappa a B ρ = ∑ f ∈ forests B {ρ}, wt a (B \ {ρ}) f := by
  rw [kappa_eq_pmin, pmin_lapl_eq_forests a (by simpa using hρ) (by simpa using hρ) rfl]
  refine Finset.sum_congr rfl fun f hf => ?_
  rw [if_pos]
  intro σ hσ
  rw [Finset.mem_singleton.1 hσ, Finset.card_eq_one]
  refine ⟨σ, ?_⟩
  rw [Finset.mem_singleton.1 hσ]
  ext x
  simp only [Finset.mem_filter, Finset.mem_singleton]
  constructor
  · exact fun h => h.1
  · rintro rfl
    exact ⟨rfl, root_eq_of_not_mem (mem_forests.1 hf).1 (by simp)⟩

/-- In a forest of `B` rooted at `F`, every point of `B` has its root in `F`. -/
theorem root_mem_of_forests {B F : Finset ι} {f : ι → ι} (hf : f ∈ forests B F) {x : ι}
    (hx : x ∈ B) : root f x ∈ F :=
  root_mem_F (mem_forests.1 hf).1 (mem_forests.1 hf).2 hx

/-- **Lemma 2.2(2)**: `det L_B[B∖i, B∖j] = κ_i(B)` for `i, j ∈ B`. -/
theorem pmin_lapl_offdiag (a : ι → ι → ZMod 2) {B : Finset ι} {i j : ι} (hi : i ∈ B)
    (hj : j ∈ B) : pmin (lapl a B) (B \ {i}) (B \ {j}) = kappa a B i := by
  rw [kappa_eq_forests a hi, pmin_lapl_eq_forests a (F := {i}) (W := {j}) (by simpa using hi)
    (by simpa using hj) rfl]
  refine Finset.sum_congr rfl fun f hf => ?_
  rw [if_pos]
  intro σ hσ
  rw [Finset.mem_singleton.1 hσ, Finset.card_eq_one]
  refine ⟨j, ?_⟩
  ext x
  simp only [Finset.mem_filter, Finset.mem_singleton]
  constructor
  · exact fun h => h.1
  · rintro rfl
    exact ⟨rfl, Finset.mem_singleton.1 (root_mem_of_forests hf hj)⟩

/-- The column sums of `L_B` over `B`. -/
def colSum (a : ι → ι → ZMod 2) (B : Finset ι) (v : ι) : ZMod 2 := ∑ u ∈ B, lapl a B u v

/-- `{j, v}` is a transversal of a forest of `B` rooted at `{i, j}` iff `v` lies in the tree of `i`. -/
theorem isTransv_pair {B : Finset ι} {i j v : ι} (hij : i ≠ j) (hvj : v ≠ j) {f : ι → ι}
    (hf : f ∈ forests B {i, j}) (hv : v ∈ B) : IsTransv f {i, j} {j, v} ↔ root f v = i := by
  have hjj : root f j = j :=
    root_eq_of_not_mem (mem_forests.1 hf).1 (by simp)
  have hrv0 := root_mem_of_forests hf hv
  simp only [Finset.mem_insert, Finset.mem_singleton] at hrv0
  unfold IsTransv
  constructor
  · intro h
    rcases hrv0 with hrv | hrv
    · exact hrv
    · exfalso
      have := h j (by simp)
      have hsub : ({j, v} : Finset ι) ⊆ ({j, v} : Finset ι).filter (fun w => root f w = j) := by
        intro w hw
        simp only [Finset.mem_insert, Finset.mem_singleton] at hw
        rcases hw with rfl | rfl
        · simp [hjj]
        · simp [hrv]
      have := (Finset.card_le_card hsub).trans_eq this
      rw [Finset.card_pair hvj.symm] at this
      omega
  · intro hvi ρ hρ
    simp only [Finset.mem_insert, Finset.mem_singleton] at hρ
    rw [Finset.card_eq_one]
    rcases hρ with rfl | rfl
    · refine ⟨v, ?_⟩
      ext w
      simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton]
      constructor
      · rintro ⟨rfl | rfl, h⟩
        · rw [hjj] at h; exact absurd h.symm hij
        · rfl
      · rintro rfl; exact ⟨Or.inr rfl, hvi⟩
    · refine ⟨ρ, ?_⟩
      ext w
      simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton]
      constructor
      · rintro ⟨rfl | rfl, h⟩
        · rfl
        · rw [hvi] at h; exact absurd h hij
      · rintro rfl; exact ⟨Or.inl rfl, hjj⟩

theorem pmin_updateRow_add (M : Matrix ι ι (ZMod 2)) {R C : Finset ι} {i : ι} (hi : i ∈ R)
    (r s : ι → ZMod 2) :
    pmin (M.updateRow i (r + s)) R C = pmin (M.updateRow i r) R C + pmin (M.updateRow i s) R C := by
  have := pmin_updateRow_sum M hi (C := C) (Finset.univ : Finset Bool)
    (fun b => if b then r else s)
  simpa [add_comm] using this

/-- **Lemma 2.2(3)** (`κ`-difference): for `i ≠ j` in `B`, `κ_i(B) + κ_j(B) = Σ_φ wt(φ) c(T_i(φ))`,
over the forests `φ` of `B` rooted at `{i, j}`, with `T_i(φ)` the tree of `i` and `c` the column sums. -/
theorem kappa_add_kappa (a : ι → ι → ZMod 2) {B : Finset ι} {i j : ι} (hi : i ∈ B) (hj : j ∈ B)
    (hij : i ≠ j) :
    kappa a B i + kappa a B j = ∑ f ∈ forests B {i, j},
      wt a (B \ {i, j}) f * ∑ v ∈ B.filter (fun v => root f v = i), colSum a B v := by
  set R := B \ {j} with hR
  have hiR : i ∈ R := by simp [hR, hi, hij]
  -- adding all other rows to row `i` does not change `κ_j`
  have h1 : pmin ((lapl a B).updateRow i (∑ u ∈ R, fun v => lapl a B u v)) R R = kappa a B j := by
    rw [pmin_updateRow_sum (lapl a B) hiR, ← Finset.add_sum_erase R _ hiR,
      show (fun v => lapl a B i v) = lapl a B i from rfl, updateRow_eq_self, ← kappa_eq_pmin]
    rw [Finset.sum_eq_zero, add_zero]
    intro u hu
    refine pmin_eq_zero_of_row_eq _ hiR (Finset.mem_of_mem_erase hu) (Finset.ne_of_mem_erase hu).symm ?_
    rw [updateRow_self, updateRow_ne (Finset.ne_of_mem_erase hu)]
  -- the sum of the rows of `R` is `c + L_j`
  have hsumrow : (∑ u ∈ R, fun v => lapl a B u v) = colSum a B + lapl a B j := by
    funext v
    rw [Finset.sum_apply, Pi.add_apply, colSum, hR, Finset.sdiff_singleton_eq_erase,
      ← Finset.sum_erase_add B _ hj, add_assoc, CharTwo.add_self_eq_zero, add_zero]
  rw [hsumrow, pmin_updateRow_add (lapl a B) hiR] at h1
  -- the row `L_j` in place of row `i` gives `κ_i`
  have h2 : pmin ((lapl a B).updateRow i (lapl a B j)) R R = kappa a B i := by
    rw [pmin_expand_row _ hiR, ← pmin_lapl_offdiag a hi hj]
    have hjR' : j ∈ B \ {i} := by simp [hj, Ne.symm hij]
    rw [pmin_expand_row _ hjR']
    refine Finset.sum_congr rfl fun v _ => ?_
    rw [updateRow_self]
    congr 1
    have hE : (B \ {i}).erase j = R.erase i := by
      ext x; simp [hR]; tauto
    rw [hE]
    refine pmin_congr fun k hk => ?_
    rw [updateRow_ne (Finset.ne_of_mem_erase hk)]
  -- the row `c` in place of row `i`: expand along it and use the forest lemma
  have h3 : pmin ((lapl a B).updateRow i (colSum a B)) R R = ∑ f ∈ forests B {i, j},
      wt a (B \ {i, j}) f * ∑ v ∈ B.filter (fun v => root f v = i), colSum a B v := by
    rw [pmin_expand_row _ hiR]
    have hRi : R.erase i = B \ {i, j} := by
      ext x; simp [hR]; tauto
    have hterm : ∀ v ∈ R, ((lapl a B).updateRow i (colSum a B)) i v *
        pmin ((lapl a B).updateRow i (colSum a B)) (R.erase i) (R.erase v) =
        colSum a B v * ∑ f ∈ forests B {i, j}, if root f v = i then wt a (B \ {i, j}) f else 0 := by
      intro v hv
      have hvB : v ∈ B := (Finset.mem_sdiff.1 hv).1
      have hvj : v ≠ j := by simpa using (Finset.mem_sdiff.1 hv).2
      rw [updateRow_self]
      congr 1
      rw [pmin_congr (M' := lapl a B) fun k hk => updateRow_ne (Finset.ne_of_mem_erase hk), hRi]
      have hRv : R.erase v = B \ {j, v} := by
        ext x; simp [hR]; tauto
      rw [hRv, pmin_lapl_eq_forests a (by simp [Finset.insert_subset_iff, hi, hj])
        (by simp [Finset.insert_subset_iff, hj, hvB])
        (by rw [Finset.card_pair hij, Finset.card_pair hvj.symm])]
      refine Finset.sum_congr rfl fun f hf => ?_
      exact if_congr (isTransv_pair hij hvj hf hvB) rfl rfl
    rw [Finset.sum_congr rfl hterm]
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun f hf => ?_
    have hjroot : root f j = j :=
      root_eq_of_not_mem (mem_forests.1 hf).1 (by simp)
    rw [Finset.sum_filter, hR, Finset.sdiff_singleton_eq_erase, ← Finset.sum_erase_add B _ hj]
    rw [if_neg (by rw [hjroot]; exact hij.symm), add_zero]
    refine Finset.sum_congr rfl fun v _ => ?_
    split_ifs <;> ring
  rw [h2, h3] at h1
  rw [← h1, add_comm _ (kappa a B i), ← add_assoc, CharTwo.add_self_eq_zero, zero_add]

/-- Lemma 2.2, first sentence: under reciprocity the column sums of `L_B` are `c_v = y_v (1 + y(B))`. -/
theorem colSum_lapl {a : ι → ι → ZMod 2} {y : ι → ZMod 2} (hrec : Recip a y) {B : Finset ι}
    {v : ι} (hv : v ∈ B) : colSum a B v = y v * (∑ u ∈ B, y u + 1) := by
  rw [colSum, ← Finset.add_sum_erase B _ hv]
  have : lapl a B v v = ∑ k ∈ B.erase v, a v k := by simp [lapl]
  rw [this, ← Finset.sum_add_distrib]
  have h2 : ∀ u ∈ B.erase v, a v u + lapl a B u v = y v * y u := fun u hu => by
    have huv := Finset.ne_of_mem_erase hu
    simp only [lapl, huv, if_false]
    exact hrec v u (Ne.symm huv)
  rw [Finset.sum_congr rfl h2, ← Finset.mul_sum, ← Finset.add_sum_erase B y hv]
  ring_nf
  rw [show y v ^ 2 = y v from (sq (y v)).trans (zmod2_mul_self _)]
  ring_nf
  rw [show (2 : ZMod 2) = 0 from rfl]
  ring

/-- **Lemma 2.2(1)**: if `y(B) = 1`, all `κ_ρ(B)`, `ρ ∈ B`, are equal. -/
theorem kappa_eq_kappa {a : ι → ι → ZMod 2} {y : ι → ZMod 2} (hrec : Recip a y) {B : Finset ι}
    (hy : ∑ u ∈ B, y u = 1) {i j : ι} (hi : i ∈ B) (hj : j ∈ B) : kappa a B i = kappa a B j := by
  rcases eq_or_ne i j with rfl | hij
  · rfl
  have := kappa_add_kappa a hi hj hij
  rw [Finset.sum_eq_zero] at this
  · exact (eq_of_sub_eq_zero (by rw [sub_eq_add_neg, ZMod.neg_eq_self_mod_two]; exact this))
  intro f _
  rw [Finset.sum_eq_zero, mul_zero]
  intro v hv
  rw [colSum_lapl hrec (Finset.mem_filter.1 hv).1, hy, CharTwo.add_self_eq_zero, mul_zero]

/-- If `y(B) = 1`, `g(B) = κ_ρ(B)` for every `ρ ∈ B` (tyz-5b Proposition 2.3(1) as stated). -/
theorem redeiG_eq_kappa {a : ι → ι → ZMod 2} {y z : ι → ZMod 2} (hrec : Recip a y)
    {B : Finset ι} (hy : ∑ u ∈ B, y u = 1) {ρ : ι} (hρ : ρ ∈ B) :
    redeiG a y z B = kappa a B ρ := by
  rw [redeiG, if_pos hy, Finset.sum_congr rfl fun r hr => by rw [kappa_eq_kappa hrec hy hr hρ],
    ← Finset.sum_mul, hy, one_mul]

/-- **(2.1)**, first half: if `y(B) = 1`, `Σ_ρ y_ρ κ_ρ(B) = g(B)`. -/
theorem sum_y_kappa {a : ι → ι → ZMod 2} {y z : ι → ZMod 2} {B : Finset ι}
    (hy : ∑ u ∈ B, y u = 1) : ∑ ρ ∈ B, y ρ * kappa a B ρ = redeiG a y z B := by
  rw [redeiG, if_pos hy]

/-- **(2.1)**, second half: if `y(B) = 1`, `Σ_ρ z_ρ κ_ρ(B) = z(B) g(B)`. -/
theorem sum_z_kappa {a : ι → ι → ZMod 2} {y z : ι → ZMod 2} (hrec : Recip a y) {B : Finset ι}
    (hy : ∑ u ∈ B, y u = 1) : ∑ ρ ∈ B, z ρ * kappa a B ρ = (∑ u ∈ B, z u) * redeiG a y z B := by
  rcases B.eq_empty_or_nonempty with rfl | ⟨ρ, hρ⟩
  · simp at hy
  rw [redeiG_eq_kappa hrec hy hρ, Finset.sum_mul]
  exact Finset.sum_congr rfl fun r hr => by rw [kappa_eq_kappa hrec hy hr hρ]

/-- **(2.2)**: if `y(B) = 0`, `Σ_ρ z_ρ κ_ρ(B) = g(B)` (the definition). -/
theorem sum_z_kappa_of_y_zero {a : ι → ι → ZMod 2} {y z : ι → ZMod 2} {B : Finset ι}
    (hy : ∑ u ∈ B, y u = 0) : ∑ ρ ∈ B, z ρ * kappa a B ρ = redeiG a y z B := by
  rw [redeiG, if_neg (by rw [hy]; exact zero_ne_one)]

end ZInQ.RouteK.Rank5b.Sec3
