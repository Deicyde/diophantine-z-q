import ZInQKernel.Contrib.CloudB3RC53.EvenUpper.Realize
import ZInQKernel.Contrib.CloudB3RC53.CoefficientDictionary.NonVacuity

/-!
# EvenUpper, part 5: a nonzero symbol at `ε ≠ 0` — non-vacuity of `realized_cubes`

Consistency check, not part of the manuscript. Lane RC2's only witness for the coefficient rules
(`forestSymbol`, `Witness.lean`) has zero sign coordinate `ε = 0`, which no `TypeData` admits (its
`sign` field forces `ε(typ p) = (p − 1)/2`); the dictionary's witnesses at `ε ≠ 0` are the zero
symbol, which has no unit seed. Here (all `PROVED`):

* `redei φ Γ` — **the Rédei symbol**: the determinant over `𝔽₂` of the Rédei matrix of the typed
  graph, with off-diagonal entries the residue bits `z_{ab}` and diagonal entries
  `φ(t_a) + ∑_{c ≠ a} z_{ac}` (for additive `φ : L →+ 𝔽₂`).
* `coefficientRules_redei` — it satisfies RC2's coefficient rules for **every** `ε`:
  * graph dependence: `redei_iso`, by simultaneous permutation of rows and columns;
  * primary isolation: `redei_isolation`, a zero row;
  * contraction: `redei_contraction`. Flipping the pair bit adds `δδᵀ`, `δ = e_v + e_w`; by row
    multilinearity, a row swap, a column transvection and a block expansion
    (`det_add_det_flip`), `det M + det M' = det` of the contracted Rédei matrix. Compatibility is
    not used, so the contraction rule is consistent at `ε ≠ 0` and negative-vertex pairs cause no
    obstruction.
* `coefficientRules_primeReading`, `fixedU_primeReading` — an isomorphism-invariant symbol with the
  rules, read on prime sets (`R W = A(primeConfig W typ)`), gives a reading with the fixed-`U`
  factorization whose dictionary symbol `symb T R` satisfies the rules (`symb T R = A` on
  compatible graphs, `symb_primeReading`).
* `redei_partitionable_three` — for the sign type data (`ε = id`, `typ p = (p − 1)/2 mod 2`), the
  typed graph of `3` (one negative vertex) is partitionable for the Rédei reading.
* `realized_cubes_redei` — **every hypothesis of `realized_cubes` holds** (with `d = 3`, `N₀ = 1`,
  and the unit predicate "Rédei reading one at a set of good primes"), so for every `b ≥ 1` there
  is a binary family based at `3` whose nonzero addresses carry Rédei reading one.
-/

namespace ZInQ.Contrib.CloudB3RC53.EvenUpper

open ZInQ.Manuscript.RC.Symbols ZInQ.Contrib.CloudB3RC53.CoefficientDictionary Finset Matrix

section Abstract

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- In `𝔽₂`, `a + a = 0`. -/
theorem zmod2_add_self (a : ZMod 2) : a + a = 0 := by revert a; decide

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **The abstract contraction identity** (`PROVED`): over `𝔽₂`, with `w = inl ()` and
`v = inr v`, adding `δδᵀ` (`δ = e_w + e_v`) changes the determinant by the determinant of the
matrix obtained by adding row `w` to row `v` and column `w` to column `v` and deleting `w`. -/
theorem det_add_det_flip (N : Matrix (Unit ⊕ ι) (Unit ⊕ ι) (ZMod 2)) (v : ι) :
    N.det + (Matrix.of fun i j => N i j +
        (if i = Sum.inl () ∨ i = Sum.inr v then 1 else 0) *
          (if j = Sum.inl () ∨ j = Sum.inr v then 1 else 0)).det =
      (Matrix.of fun a b : ι => N (Sum.inr a) (Sum.inr b) +
        (if a = v then N (Sum.inl ()) (Sum.inr b) else 0) +
        (if b = v then N (Sum.inr a) (Sum.inl ()) else 0) +
        (if a = v ∧ b = v then N (Sum.inl ()) (Sum.inl ()) else 0)).det := by
  set w : Unit ⊕ ι := Sum.inl () with hw
  set v' : Unit ⊕ ι := Sum.inr v with hv'
  have hwv : w ≠ v' := Sum.inl_ne_inr
  set δ : Unit ⊕ ι → ZMod 2 := fun i => if i = w ∨ i = v' then 1 else 0 with hδ
  have hδw : δ w = 1 := by simp [hδ]
  have hδv : δ v' = 1 := by simp [hδ]
  have hN' : (Matrix.of fun i j => N i j + δ i * δ j) =
      updateRow (updateRow N v' (N v' + δ)) w (N w + δ) := by
    ext i j
    by_cases hi : i = w
    · subst hi; simp [updateRow_apply, hδw]
    · by_cases hi' : i = v'
      · subst hi'; simp [updateRow_apply, hδv, hi]
      · have : δ i = 0 := by simp [hδ, hi, hi']
        simp [updateRow_apply, hi, hi', this]
  set X := updateRow N w δ with hX
  -- (a)
  have ha : (updateRow (updateRow N v' (N v' + δ)) w (N w + δ)).det =
      N.det + (updateRow N v' δ).det + X.det := by
    have hU : (updateRow N v' (N v' + δ)) w = N w := updateRow_ne hwv
    have e1 : (updateRow N v' (N v' + δ)).updateRow w (N w) = updateRow N v' (N v' + δ) := by
      conv_lhs => rw [← hU]
      exact updateRow_eq_self _ _
    have e2 : (updateRow N v' (N v')) = N := updateRow_eq_self _ _
    rw [det_updateRow_add, e1, det_updateRow_add, e2, updateRow_comm _ hwv.symm,
      det_updateRow_add]
    have h0 : (updateRow (updateRow N w δ) v' δ).det = 0 :=
      det_zero_of_row_eq hwv (by rw [updateRow_ne hwv, updateRow_self, updateRow_self])
    have hX' : (updateRow N w δ) v' = N v' := updateRow_ne hwv.symm
    have e3 : (updateRow N w δ).updateRow v' (N v') = updateRow N w δ := by
      conv_lhs => rw [← hX']
      exact updateRow_eq_self _ _
    rw [h0, add_zero, e3]
  -- (b) swap rows
  have hb : (updateRow N v' δ).det = (updateRow X v' (N w)).det := by
    have hperm : (updateRow X v' (N w)).submatrix (Equiv.swap w v') id = updateRow N v' δ := by
      ext i j
      simp only [submatrix_apply, id]
      by_cases hi : i = w
      · subst hi; rw [Equiv.swap_apply_left, updateRow_self, updateRow_ne hwv]
      · by_cases hi' : i = v'
        · subst hi'; rw [Equiv.swap_apply_right, updateRow_self, updateRow_ne hwv, hX,
            updateRow_self]
        · rw [Equiv.swap_apply_of_ne_of_ne hi hi', updateRow_ne hi', updateRow_ne hi', hX,
            updateRow_ne hi]
    rw [← hperm, det_permute, Equiv.Perm.sign_swap hwv]
    simp
  -- (c)
  set K := updateRow X v' (N v' + N w) with hK
  have hc : X.det + (updateRow X v' (N w)).det = K.det := by
    have hX' : X v' = N v' := updateRow_ne hwv.symm
    have e3 : X.updateRow v' (N v') = X := by
      conv_lhs => rw [← hX']
      exact updateRow_eq_self _ _
    rw [hK, det_updateRow_add, e3]
  -- (d) column operation and block expansion
  have hd : K.det = (Matrix.of fun a b : ι => N (Sum.inr a) (Sum.inr b) +
        (if a = v then N (Sum.inl ()) (Sum.inr b) else 0) +
        (if b = v then N (Sum.inr a) (Sum.inl ()) else 0) +
        (if a = v ∧ b = v then N (Sum.inl ()) (Sum.inl ()) else 0)).det := by
    set K' := K * transvection w v' 1 with hK'
    have hdet : K'.det = K.det := by rw [hK', det_mul]; simp [hwv]
    have hKw : K w = δ := by rw [hK, updateRow_ne hwv, hX, updateRow_self]
    have hKv : K v' = N v' + N w := by rw [hK, updateRow_self]
    have hKo : ∀ i, i ≠ v' → i ≠ w → K i = N i := fun i h1 h2 => by
      rw [hK, updateRow_ne h1, hX, updateRow_ne h2]
    have hK'e : ∀ i j, K' i j = K i j + (if j = v' then K i w else 0) := by
      intro i j
      by_cases hj : j = v'
      · subst hj; rw [hK', mul_transvection_apply_same]; simp
      · rw [hK']; simp [hj]
    have h12 : K'.toBlocks₁₂ = 0 := by
      ext u b
      simp only [toBlocks₁₂, of_apply, Matrix.zero_apply]
      rw [hK'e, hKw]
      by_cases hb : b = v
      · subst hb; simp [hδ, hw, hv']; exact zmod2_add_self 1
      · simp [hδ, hw, hv', hb]
    have h11 : K'.toBlocks₁₁.det = 1 := by
      rw [det_unique]
      simp only [toBlocks₁₁, of_apply]
      rw [hK'e, hKw]
      simp [hδ, hw, hv']
    rw [← hdet, ← fromBlocks_toBlocks K', h12, det_fromBlocks_zero₁₂, h11, one_mul]
    congr 1
    ext a b
    simp only [toBlocks₂₂, of_apply]
    rw [hK'e]
    by_cases ha : a = v
    · subst ha
      rw [hKv]
      by_cases hb : b = a
      · subst hb; simp [hw, hv']; ring
      · simp [hw, hv', hb]
    · rw [hKo _ (by simpa [hv'] using ha) (by simp [hw])]
      by_cases hb : b = v
      · subst hb; simp [hw, hv', ha]
      · simp [hv', ha, hb]
  have key : N.det + (updateRow (updateRow N v' (N v' + δ)) w (N w + δ)).det = K.det := by
    rw [ha, hb, ← hc]
    have := zmod2_add_self N.det
    linear_combination this
  rw [← hd, ← key, ← hN']


end Abstract

section Redei

variable {L : Type*} [AddCommGroup L]

/-- The row sum of the residue bits of `a` (diagonal of the Rédei matrix). -/
def rowBits (Γ : Config L) (a : ℕ) : ZMod 2 := ∑ c ∈ Γ.V, if c = a then 0 else Γ.z a c

/-- The entries of the Rédei matrix, on vertex names. -/
def redeiEntry (φ : L →+ ZMod 2) (Γ : Config L) (x y : ℕ) : ZMod 2 :=
  if x = y then φ (Γ.t x) + rowBits Γ x else Γ.z x y

/-- **The Rédei matrix** of a typed graph: off-diagonal entries the residue bits `z_{ab}`, diagonal
`φ(t_a) + ∑_{c ≠ a} z_{ac}`. -/
def redeiMatrix (φ : L →+ ZMod 2) (Γ : Config L) : Matrix Γ.V Γ.V (ZMod 2) :=
  Matrix.of fun a b => redeiEntry φ Γ a b

/-- **The Rédei symbol**: the determinant of the Rédei matrix over `𝔽₂`. -/
def redei (φ : L →+ ZMod 2) (Γ : Config L) : ZMod 2 := (redeiMatrix φ Γ).det

/-- The Rédei symbol is invariant under isomorphisms (no compatibility needed). -/
theorem redei_iso (φ : L →+ ZMod 2) {Γ Δ : Config L} (h : Γ.IsIso Δ) : redei φ Γ = redei φ Δ := by
  obtain ⟨e, ht, hz⟩ := h
  unfold redei
  rw [← det_submatrix_equiv_self e (redeiMatrix φ Δ)]
  congr 1
  ext a b
  simp only [submatrix_apply, redeiMatrix, of_apply, redeiEntry]
  by_cases hab : a = b
  · subst hab
    simp only [↓reduceIte, ht]
    congr 1
    unfold rowBits
    rw [← Finset.sum_coe_sort Δ.V, ← Finset.sum_coe_sort Γ.V, ← e.sum_comp]
    refine Finset.sum_congr rfl fun c _ => ?_
    by_cases hca : c = a
    · subst hca; simp
    · have h1 : ((e c : Δ.V) : ℕ) ≠ ((e a : Δ.V) : ℕ) := fun h =>
        hca (e.injective (Subtype.ext h))
      have h2 : (c : ℕ) ≠ (a : ℕ) := fun h => hca (Subtype.ext h)
      simp only [h1, h2, ↓reduceIte, hz a c (Ne.symm hca)]
  · have h1 : ((e a : Δ.V) : ℕ) ≠ ((e b : Δ.V) : ℕ) := fun h =>
      hab (e.injective (Subtype.ext h))
    have h2 : (a : ℕ) ≠ (b : ℕ) := fun h => hab (Subtype.ext h)
    simp only [h1, h2, ↓reduceIte, hz a b hab]

/-- Primary isolation for the Rédei symbol: a zero row. -/
theorem redei_isolation (φ : L →+ ZMod 2) {Γ : Config L} {v : ℕ} (hv : v ∈ Γ.V)
    (ht : Γ.t v = 0) (hz : ∀ w ∈ Γ.V, w ≠ v → Γ.z v w = 0) : redei φ Γ = 0 := by
  refine det_eq_zero_of_row_eq_zero ⟨v, hv⟩ fun j => ?_
  simp only [redeiMatrix, of_apply, redeiEntry]
  split_ifs with h
  · rw [ht, map_zero, zero_add]
    refine Finset.sum_eq_zero fun c hc => ?_
    split_ifs with hcv
    · rfl
    · exact hz c hc hcv
  · exact hz j j.2 fun h' => h h'.symm

end Redei

section Contraction

variable {L : Type*} [AddCommGroup L]

/-- `Γ.V = {w} ⊔ (Γ.V \ {w})`. -/
def splitEquiv (Γ : Config L) {w : ℕ} (hw : w ∈ Γ.V) : Unit ⊕ (Γ.V.erase w) ≃ Γ.V where
  toFun := Sum.elim (fun _ => ⟨w, hw⟩) (fun b => ⟨b, Finset.mem_of_mem_erase b.2⟩)
  invFun x := if h : (x : ℕ) = w then Sum.inl () else Sum.inr ⟨x, Finset.mem_erase.2 ⟨h, x.2⟩⟩
  left_inv := by
    rintro (u | b)
    · simp
    · have : (b : ℕ) ≠ w := (Finset.mem_erase.1 b.2).1
      simp [this]
  right_inv := by
    intro x
    by_cases h : (x : ℕ) = w
    · simp only [h, ↓reduceDIte, Sum.elim_inl]; exact Subtype.ext h.symm
    · simp [h]

omit [AddCommGroup L] in
/-- Flipping the bit of `vw` changes the row sums of `v` and `w` by one. -/
theorem rowBits_flip (Γ : Config L) {v w : ℕ} (hv : v ∈ Γ.V) (hw : w ∈ Γ.V) (hvw : v ≠ w)
    (a : ℕ) : rowBits (Γ.flip v w) a = rowBits Γ a + (if a = v ∨ a = w then 1 else 0) := by
  unfold rowBits
  simp only [Config.flip, Config.flipBy, Finset.mem_singleton, Sym2.eq_iff]
  have hsplit : ∀ c, (if c = a then (0 : ZMod 2) else Γ.z a c +
      if a ≠ c ∧ (a = v ∧ c = w ∨ a = w ∧ c = v) then 1 else 0) =
      (if c = a then 0 else Γ.z a c) +
        (if (a = v ∧ c = w) ∨ (a = w ∧ c = v) then 1 else 0) := by
    intro c
    by_cases hca : c = a
    · subst hca
      have : ¬ ((c = v ∧ c = w) ∨ (c = w ∧ c = v)) := by
        rintro (⟨h1, h2⟩ | ⟨h1, h2⟩) <;> exact hvw (h1 ▸ h2 ▸ rfl)
      simp [this]
    · have hac : a ≠ c := Ne.symm hca
      simp [hca, hac]
  rw [Finset.sum_congr rfl fun c _ => hsplit c, Finset.sum_add_distrib]
  congr 1
  by_cases hav : a = v
  · subst hav
    rw [Finset.sum_eq_single w (fun c _ hc => by simp [hc, hvw]) (fun h => absurd hw h)]
    simp
  · by_cases haw : a = w
    · subst haw
      rw [Finset.sum_eq_single v (fun c _ hc => by simp [hc, hav]) (fun h => absurd hv h)]
      simp [hav]
    · simp [hav, haw]


/-- Split off one term of a sum. -/
theorem sum_split (s : Finset ℕ) (g : ℕ → ZMod 2) {v : ℕ} (hv : v ∈ s) :
    ∑ c ∈ s, g c = g v + ∑ c ∈ s, (if c = v then 0 else g c) := by
  rw [← Finset.add_sum_erase s g hv, ← Finset.add_sum_erase s _ hv]
  simp only [↓reduceIte, zero_add]
  congr 1
  exact Finset.sum_congr rfl fun c hc => by simp [Finset.ne_of_mem_erase hc]

/-- The Rédei entries after flipping a pair bit. -/
theorem redeiEntry_flip (φ : L →+ ZMod 2) (Γ : Config L) {v w : ℕ} (hv : v ∈ Γ.V) (hw : w ∈ Γ.V)
    (hvw : v ≠ w) (x y : ℕ) :
    redeiEntry φ (Γ.flip v w) x y = redeiEntry φ Γ x y +
      (if x = v ∨ x = w then 1 else 0) * (if y = v ∨ y = w then 1 else 0) := by
  unfold redeiEntry
  by_cases hxy : x = y
  · subst hxy
    simp only [↓reduceIte, rowBits_flip Γ hv hw hvw]
    have : (Γ.flip v w).t = Γ.t := rfl
    rw [this]
    split_ifs <;> ring
  · simp only [hxy, ↓reduceIte, Config.flip, Config.flipBy, Finset.mem_singleton, Sym2.eq_iff]
    congr 1
    by_cases hx : x = v <;> by_cases hy : y = w <;> by_cases hx' : x = w <;> by_cases hy' : y = v <;>
      simp_all

/-- The Rédei entries of a contraction. -/
theorem redeiEntry_contract (φ : L →+ ZMod 2) (Γ : Config L) {v w : ℕ} (hv : v ∈ Γ.V)
    (hw : w ∈ Γ.V) (hvw : v ≠ w) {a b : ℕ} (ha : a ∈ Γ.V.erase w) (hb : b ∈ Γ.V.erase w) :
    redeiEntry φ (Γ.contract v w) a b = redeiEntry φ Γ a b +
      (if a = v then redeiEntry φ Γ w b else 0) + (if b = v then redeiEntry φ Γ a w else 0) +
      (if a = v ∧ b = v then redeiEntry φ Γ w w else 0) := by
  have haw : a ≠ w := Finset.ne_of_mem_erase ha
  have hbw : b ≠ w := Finset.ne_of_mem_erase hb
  have hvE : v ∈ Γ.V.erase w := Finset.mem_erase.2 ⟨hvw, hv⟩
  have h2 : (2 : ZMod 2) = 0 := rfl
  have hct : ∀ x, (Γ.contract v w).t x = Function.update Γ.t v (Γ.t v + Γ.t w) x := fun _ => rfl
  have hcz : ∀ x y, (Γ.contract v w).z x y = if x = v then Γ.z v y + Γ.z w y else
      if y = v then Γ.z x v + Γ.z x w else Γ.z x y := fun _ _ => rfl
  unfold redeiEntry
  by_cases hab : a = b
  · subst hab
    by_cases hav : a = v
    · subst hav
      have hwa : w ≠ a := Ne.symm hvw
      have hrv : rowBits Γ a = Γ.z a w + ∑ c ∈ Γ.V.erase w, (if c = a then 0 else Γ.z a c) := by
        unfold rowBits
        rw [← Finset.add_sum_erase _ _ hw]
        simp only [hwa, ↓reduceIte]
      have hrw : rowBits Γ w = Γ.z w a + ∑ c ∈ Γ.V.erase w, (if c = a then 0 else Γ.z w c) := by
        unfold rowBits
        rw [← Finset.add_sum_erase _ _ hw]
        simp only [↓reduceIte, zero_add]
        rw [Finset.sum_congr rfl fun c hc => (by simp only [Finset.ne_of_mem_erase hc, ↓reduceIte] :
          (if c = w then (0 : ZMod 2) else Γ.z w c) = Γ.z w c), sum_split _ _ hvE]
      have hrc : rowBits (Γ.contract a w) a = ∑ c ∈ Γ.V.erase w, (if c = a then 0 else Γ.z a c) +
          ∑ c ∈ Γ.V.erase w, (if c = a then 0 else Γ.z w c) := by
        unfold rowBits
        rw [← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl fun c _ => by rw [hcz]; split_ifs <;> simp_all
      simp only [↓reduceIte, and_self, hwa, haw, hct, Function.update_self, map_add]
      rw [hrc, hrv, hrw]
      linear_combination (-(Γ.z a w + Γ.z w a)) * h2
    · have hrc : rowBits (Γ.contract v w) a = rowBits Γ a := by
        unfold rowBits
        simp only [hcz, hav, ↓reduceIte]
        rw [← Finset.add_sum_erase Γ.V _ hw]
        simp only [Ne.symm haw, ↓reduceIte]
        have : ∀ c ∈ Γ.V.erase w, (if c = a then (0 : ZMod 2) else
            if c = v then Γ.z a v + Γ.z a w else Γ.z a c) =
            (if c = a then 0 else Γ.z a c) + (if c = v then Γ.z a w else 0) := by
          intro c _
          by_cases hca : c = a
          · subst hca; simp [hav]
          · by_cases hcv : c = v
            · subst hcv; simp [hca]
            · simp [hca, hcv]
        show (∑ c ∈ Γ.V.erase w, (if c = a then (0 : ZMod 2) else
            if c = v then Γ.z a v + Γ.z a w else Γ.z a c)) = _
        rw [Finset.sum_congr rfl this, Finset.sum_add_distrib, Finset.sum_ite_eq' _ v]
        simp only [hvE, ↓reduceIte]
        rw [add_comm]
      simp only [↓reduceIte, hav, hct, Function.update_of_ne hav, hrc, false_and]
      ring
  · by_cases hav : a = v
    · subst hav
      have hbv : b ≠ a := Ne.symm hab
      simp only [hab, ↓reduceIte, hbv, Ne.symm hbw, and_false, add_zero, hcz]
    · by_cases hbv : b = v
      · subst hbv
        simp only [hab, ↓reduceIte, haw, false_and, add_zero, hcz]
      · simp [hab, hav, hbv, hcz]

/-- **The contraction rule for the Rédei symbol** (PROVED, no compatibility needed). -/
theorem redei_contraction (φ : L →+ ZMod 2) (Γ : Config L) {v w : ℕ} (hv : v ∈ Γ.V)
    (hw : w ∈ Γ.V) (hvw : v ≠ w) :
    redei φ Γ + redei φ (Γ.flip v w) = redei φ (Γ.contract v w) := by
  classical
  set τ := splitEquiv Γ hw with hτ
  have hvE : v ∈ Γ.V.erase w := Finset.mem_erase.2 ⟨hvw, hv⟩
  set v₀ : Γ.V.erase w := ⟨v, hvE⟩
  set N := reindex τ.symm τ.symm (redeiMatrix φ Γ) with hN
  have hdetN : redei φ Γ = N.det := by rw [hN, det_reindex_self]; rfl
  have htl : ((τ (Sum.inl ()) : Γ.V) : ℕ) = w := rfl
  have htr : ∀ a : Γ.V.erase w, ((τ (Sum.inr a) : Γ.V) : ℕ) = a := fun _ => rfl
  have hv₀ : ∀ a : Γ.V.erase w, a = v₀ ↔ (a : ℕ) = v := fun a => by
    constructor
    · rintro rfl; rfl
    · intro h; exact Subtype.ext h
  have hind : ∀ i, (((τ i : Γ.V) : ℕ) = v ∨ ((τ i : Γ.V) : ℕ) = w) ↔
      (i = Sum.inl () ∨ i = Sum.inr v₀) := by
    rintro (u | a)
    · simp [htl]
    · have haw : (a : ℕ) ≠ w := Finset.ne_of_mem_erase a.2
      simp only [htr, haw, or_false, reduceCtorEq, false_or, Sum.inr.injEq, hv₀]
  have hNe : ∀ i j, N i j = redeiEntry φ Γ (τ i) (τ j) := fun _ _ => rfl
  have hdetF : redei φ (Γ.flip v w) = (Matrix.of fun i j => N i j +
      (if i = Sum.inl () ∨ i = Sum.inr v₀ then 1 else 0) *
        (if j = Sum.inl () ∨ j = Sum.inr v₀ then 1 else 0)).det := by
    let MF : Matrix Γ.V Γ.V (ZMod 2) := Matrix.of fun a b => redeiEntry φ (Γ.flip v w) a b
    have e : redei φ (Γ.flip v w) = (reindex τ.symm τ.symm MF).det := by
      rw [det_reindex_self]; rfl
    rw [e]
    congr 1
    ext i j
    simp only [reindex_apply, submatrix_apply, Equiv.symm_symm, of_apply, MF, hNe]
    rw [redeiEntry_flip φ Γ hv hw hvw]
    simp only [hind]
  have hdetC : redei φ (Γ.contract v w) = (Matrix.of fun a b : Γ.V.erase w =>
      N (Sum.inr a) (Sum.inr b) +
        (if a = v₀ then N (Sum.inl ()) (Sum.inr b) else 0) +
        (if b = v₀ then N (Sum.inr a) (Sum.inl ()) else 0) +
        (if a = v₀ ∧ b = v₀ then N (Sum.inl ()) (Sum.inl ()) else 0)).det := by
    unfold redei
    congr 1
    ext a b
    simp only [redeiMatrix, of_apply, hNe, htl, htr, hv₀]
    exact redeiEntry_contract φ Γ hv hw hvw a.2 b.2
  rw [hdetN, hdetF, hdetC]
  exact det_add_det_flip N v₀

end Contraction

section Rules

variable {L : Type*} [AddCommGroup L]

/-- **The Rédei symbol satisfies RC2's coefficient rules** (`PROVED`), for every sign map `ε`
(compatibility is not even needed). -/
theorem coefficientRules_redei (ε φ : L →+ ZMod 2) : CoefficientRules ε (redei φ) where
  graph_dependence _ _ _ hiso := redei_iso φ hiso
  contraction Γ _ _ hv _ hw hvw := redei_contraction φ Γ hv hw hvw
  primary_isolation _ _ _ hv ht hz := redei_isolation φ hv ht fun w hw hwv => (hz w hw hwv).1

omit [AddCommGroup L] in
/-- An isomorphism from an injective renaming of the vertices. -/
theorem isIso_of_map {Γ Δ : Config L} (f : ℕ → ℕ) (hinj : Set.InjOn f Γ.V)
    (hV : Δ.V = Γ.V.image f) (ht : ∀ x ∈ Γ.V, Δ.t (f x) = Γ.t x)
    (hz : ∀ x ∈ Γ.V, ∀ y ∈ Γ.V, x ≠ y → Δ.z (f x) (f y) = Γ.z x y) : Γ.IsIso Δ := by
  classical
  have hmem : ∀ x ∈ Γ.V, f x ∈ Δ.V := fun x hx => by rw [hV]; exact Finset.mem_image_of_mem f hx
  let g : Γ.V → Δ.V := fun x => ⟨f x, hmem x x.2⟩
  have hg : Function.Bijective g := by
    refine ⟨fun x y h => Subtype.ext (hinj x.2 y.2 (congrArg Subtype.val h)), fun y => ?_⟩
    have hy : (y : ℕ) ∈ Γ.V.image f := by rw [← hV]; exact y.2
    obtain ⟨x, hx, hxy⟩ := Finset.mem_image.1 hy
    exact ⟨⟨x, hx⟩, Subtype.ext hxy⟩
  exact ⟨Equiv.ofBijective g hg, fun x => ht x x.2,
    fun x y hxy => hz x x.2 y y.2 fun h => hxy (Subtype.ext h)⟩

/-- Compatibility is carried along isomorphisms. -/
theorem compatible_of_iso {ε : L →+ ZMod 2} {Γ Δ : Config L} (hΓ : Γ.Compatible ε)
    (h : Γ.IsIso Δ) : Δ.Compatible ε := by
  obtain ⟨e, ht, hz⟩ := h
  intro a ha b hb hab
  set x := e.symm ⟨a, ha⟩
  set y := e.symm ⟨b, hb⟩
  have hxy : x ≠ y := fun h => hab (congrArg Subtype.val (e.symm.injective h))
  have hea : ((e x : Δ.V) : ℕ) = a := by simp [x]
  have heb : ((e y : Δ.V) : ℕ) = b := by simp [y]
  have h1 := hz x y hxy
  have h2 := hz y x (Ne.symm hxy)
  rw [hea, heb] at h1 h2
  have h3 := ht x
  have h4 := ht y
  rw [hea] at h3
  rw [heb] at h4
  rw [h1, h2, h3, h4]
  exact hΓ x x.2 y y.2 fun h => hxy (Subtype.ext h)

variable {ε : L →+ ZMod 2}

/-- The symbol of the prime readings of an isomorphism-invariant `A` is `A` on compatible graphs. -/
theorem symb_primeReading (T : TypeData L ε) (A : Config L → ZMod 2)
    (hiso : ∀ Γ Δ : Config L, Γ.IsIso Δ → A Γ = A Δ) {Γ : Config L} (hΓ : Γ.Compatible ε) :
    symb T (fun W => A (primeConfig W T.typ)) Γ = A Γ := by
  classical
  have h : ∃ f, IsReal T Γ f := exists_real T hΓ
  rw [symb, dif_pos' h]
  have hf := h.choose_spec
  symm
  exact hiso _ _ (isIso_of_map h.choose hf.1 rfl (fun x hx => (hf.2.1 x hx).2)
    (fun x hx y hy hxy => hf.2.2 x hx y hy hxy))

/-- The coefficient rules pass to the symbol of the prime readings. -/
theorem coefficientRules_primeReading (T : TypeData L ε) (A : Config L → ZMod 2)
    (hA : CoefficientRules ε A) (hiso : ∀ Γ Δ : Config L, Γ.IsIso Δ → A Γ = A Δ) :
    CoefficientRules ε (symb T (fun W => A (primeConfig W T.typ))) where
  graph_dependence Γ Δ hΓ h := by
    rw [symb_primeReading T A hiso hΓ, symb_primeReading T A hiso (compatible_of_iso hΓ h)]
    exact hiso _ _ h
  contraction Γ hΓ v hv w hw hvw := by
    rw [symb_primeReading T A hiso hΓ, symb_primeReading T A hiso (flip_compatible hΓ v w),
      symb_primeReading T A hiso (ForestAux.contract_compatible hΓ hv hw)]
    exact hA.contraction Γ hΓ v hv w hw hvw
  primary_isolation Γ hΓ v hv ht hz := by
    rw [symb_primeReading T A hiso hΓ]
    exact hA.primary_isolation Γ hΓ v hv ht hz

/-- The fixed-`U` factorization holds for the prime readings of an isomorphism-invariant `A`. -/
theorem fixedU_primeReading (T : TypeData L ε) (A : Config L → ZMod 2)
    (hiso : ∀ Γ Δ : Config L, Γ.IsIso Δ → A Γ = A Δ) (B : ℕ) :
    FixedUFactorization T (fun W => A (primeConfig W T.typ)) B := by
  classical
  intro W p p' _ hW hp hp' hpW hp'W htyp hbits
  have hfix : ∀ x ∈ W, Equiv.swap p p' x = x := fun x hx =>
    Equiv.swap_apply_of_ne_of_ne (fun h => hpW (h ▸ hx)) (fun h => hp'W (h ▸ hx))
  apply hiso
  refine isIso_of_map (Equiv.swap p p') (Equiv.swap p p').injective.injOn ?_ ?_ ?_
  · show insert p' W = (insert p W).image (Equiv.swap p p')
    rw [Finset.image_insert, Equiv.swap_apply_left, Finset.image_congr (g := id) hfix,
      Finset.image_id]
  · intro x hx
    rcases Finset.mem_insert.1 hx with rfl | hx
    · show T.typ (Equiv.swap x p' x) = T.typ x
      rw [Equiv.swap_apply_left, htyp]
    · show T.typ (Equiv.swap p p' x) = T.typ x
      rw [hfix x hx]
  · intro x hx y hy hxy
    show legBit (Equiv.swap p p' x) (Equiv.swap p p' y) = legBit x y
    rcases Finset.mem_insert.1 hx with hxp | hxW <;> rcases Finset.mem_insert.1 hy with hyp | hyW
    · exact absurd (hxp.trans hyp.symm) hxy
    · rw [hxp, Equiv.swap_apply_left, hfix y hyW, hbits y hyW]
    · rw [hyp, Equiv.swap_apply_left, hfix x hxW]
      have hxp : x ≠ p := fun h => hpW (h ▸ hxW)
      have hxp' : x ≠ p' := fun h => hp'W (h ▸ hxW)
      rw [T.legBit_rev (hW x hxW) hp' hxp', T.legBit_rev (hW x hxW) hp hxp, hbits x hxW, htyp]
    · rw [hfix x hxW, hfix y hyW]

end Rules

section Witness

/-- A singleton configuration: the Rédei symbol is the type value. -/
theorem redei_singleton {L : Type*} [AddCommGroup L] (φ : L →+ ZMod 2) {Γ : Config L} {r : ℕ}
    (hV : Γ.V = {r}) : redei φ Γ = φ (Γ.t r) := by
  have hr : r ∈ Γ.V := by rw [hV]; exact Finset.mem_singleton_self r
  have : Subsingleton Γ.V := ⟨fun a b => Subtype.ext (by
    have ha : (a : ℕ) ∈ ({r} : Finset ℕ) := hV ▸ a.2
    have hb : (b : ℕ) ∈ ({r} : Finset ℕ) := hV ▸ b.2
    rw [Finset.mem_singleton.1 ha, Finset.mem_singleton.1 hb])⟩
  unfold redei
  rw [det_eq_elem_of_subsingleton _ ⟨r, hr⟩]
  simp only [redeiMatrix, of_apply, redeiEntry, ↓reduceIte, rowBits, hV, Finset.sum_singleton,
    add_zero]

/-- The Rédei reading on sets of primes (sign type data, `φ = id`). -/
noncomputable def redeiReading (W : Finset ℕ) : ZMod 2 :=
  redei (AddMonoidHom.id (ZMod 2)) (primeConfig W signTypeData.typ)

/-- The dictionary symbol of the Rédei reading satisfies the rules. -/
theorem redeiReading_rules :
    CoefficientRules (AddMonoidHom.id (ZMod 2)) (symb signTypeData redeiReading) :=
  coefficientRules_primeReading signTypeData _ (coefficientRules_redei _ _)
    (fun _ _ h => redei_iso _ h)

/-- The Rédei reading has the fixed-`U` factorization. -/
theorem redeiReading_fixedU (B : ℕ) : FixedUFactorization signTypeData redeiReading B :=
  fixedU_primeReading signTypeData _ (fun _ _ h => redei_iso _ h) B

/-- A prime `≡ 1 (mod 4)` has sign type zero. -/
theorem signTypeData_typ_one (q : ℕ) (hq : ((q : ℕ) : ZMod signTypeData.m) = 1) :
    signTypeData.typ q = 0 := by
  change ((q : ℕ) : ZMod 4) = 1 at hq
  change ((q / 2 : ℕ) : ZMod 2) = 0
  rw [show (1 : ZMod 4) = ((1 : ℕ) : ZMod 4) by simp, ZMod.natCast_eq_natCast_iff'] at hq
  rw [ZMod.natCast_eq_zero_iff_even]
  exact ⟨q / 4, by omega⟩

/-- `3` is a good prime for the sign type data. -/
theorem good_three : signTypeData.Good 3 := ⟨Nat.prime_three, by decide⟩

/-- The primes of `3`. -/
theorem primeFactors_three : (3 : ℤ).natAbs.primeFactors = {3} := Nat.prime_three.primeFactors

/-- **`3` is partitionable for the Rédei symbol** (`PROVED`): a single negative vertex
(`3 ≡ 3 mod 4`, type one) is a unit seed, certified by the empty forest. -/
theorem redei_partitionable_three :
    IsPartitionable (AddMonoidHom.id (ZMod 2)) (symb signTypeData redeiReading)
      (primeConfig (3 : ℤ).natAbs.primeFactors signTypeData.typ) := by
  classical
  rw [primeFactors_three]
  set Γ := primeConfig ({3} : Finset ℕ) signTypeData.typ with hΓ
  have hf0 : IsReal signTypeData Γ id :=
    ⟨Set.injOn_id _, fun v hv => ⟨by rw [Finset.mem_singleton.1 hv]; exact good_three, rfl⟩,
      fun v _ w _ _ => rfl⟩
  have hc : Γ.Compatible (AddMonoidHom.id (ZMod 2)) := compatible_of_real signTypeData hf0
  refine ⟨by simp [hΓ, primeConfig], ∅, ⟨Finset.empty_subset _, ?_⟩, ?_⟩
  · simp [ncomp, hΓ, primeConfig]
  · rw [show symb signTypeData redeiReading = symb signTypeData
        (fun W => redei (AddMonoidHom.id (ZMod 2)) (primeConfig W signTypeData.typ)) from rfl,
      symb_primeReading signTypeData _ (fun _ _ h => redei_iso _ h) (hc.contractBy ∅)]
    set r := rep Γ.V ∅ 3
    have hV : (Γ.contractBy ∅).V = {r} := by
      simp [Config.contractBy, hΓ, primeConfig, r]
    rw [redei_singleton _ hV]
    have ht : (Γ.contractBy ∅).t r = signTypeData.typ 3 := by
      simp [Config.contractBy, hΓ, primeConfig, r, Finset.filter_singleton]
    rw [ht]
    rfl

/-- **Non-vacuity of `realized_cubes` with a nonzero symbol at `ε ≠ 0`** (`PROVED`): for the sign
type data (`ε(typ p) = (p − 1)/2`, `ε = id`) and the Rédei reading, every hypothesis of
`realized_cubes` holds at `d = 3`, `N₀ = 1`, with the unit predicate "a Rédei reading one at a set
of good primes"; so for every `b ≥ 1` there is a binary family based at `3` whose nonzero addresses
are products of good primes with Rédei reading one. -/
theorem realized_cubes_redei (b : ℕ) (hb : 1 ≤ b) :
    ∃ fam : ZInQ.Manuscript.RC.Even.BinaryFamily 1, fam.b = b ∧ fam.h 0 = 3 ∧
      ∀ x, x ≠ 0 → ∃ V : Finset ℕ, (∀ p ∈ V, signTypeData.Good p) ∧ redeiReading V = 1 ∧
        fam.h x = ∏ p ∈ V, (p : ℤ) := by
  have hsq : Squarefree (3 : ℤ) := Int.squarefree_natAbs.mp Nat.prime_three.squarefree
  have hgood : ∀ p ∈ (3 : ℤ).natAbs.primeFactors, signTypeData.Good p ∧ Nat.Coprime p 1 := by
    rw [primeFactors_three]
    intro p hp
    rw [Finset.mem_singleton.1 hp]
    exact ⟨good_three, Nat.coprime_one_right 3⟩
  obtain ⟨fam, hb', h0, hu⟩ := realized_cubes signTypeData redeiReading redeiReading_fixedU
    redeiReading_rules (fun q _ hq => signTypeData_typ_one q hq) one_pos
    (fun h => ∃ V : Finset ℕ, (∀ p ∈ V, signTypeData.Good p) ∧ redeiReading V = 1 ∧
      h = ∏ p ∈ V, (p : ℤ)) 3 hsq hgood redei_partitionable_three
    (fun V hV h1 => ⟨V, hV, h1, by rw [show (3 : ℤ).sign = 1 from rfl, one_mul]⟩) b hb
  exact ⟨fam, hb', h0, hu⟩

end Witness

end ZInQ.Contrib.CloudB3RC53.EvenUpper
