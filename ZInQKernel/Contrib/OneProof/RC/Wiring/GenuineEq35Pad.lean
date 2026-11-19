import ZInQKernel.Contrib.OneProof.RC.Wiring.GenuineEq35A

/-!
**Theorem 5.3, Lane RC0 round 9: padding the models of the (3.5) leaf to the cap of (5.1)**

Proposition `ex:limits-uniform-lower-bound` (tex 4909–5202). The leaf `Eq35InputsGenuineA W`
(`GenuineEq35A.lean`) asks, for each `A`, for a model family whose sizes EQUAL the cap of (5.1),
`nOf l = eq51Cap ℓ A |l|`, while the text only bounds them by the cap (tex 4453–4460, 4936–4938,
4954–4956). The leaf's docstring justifies the equality by padding each model with contractible
blocks. This file formalizes that padding argument.

**Finding (sign of the blocks).** Padding by `k` blocks `[𝒪 --1--> 𝒪]` multiplies the
class-functional coordinate by `(-1)^k`, for every admissible complement (`Pad.coord_padOne`): the
valuation is unchanged, the coordinate itself is not when `k` is odd. Padding by `k` blocks
`[𝒪 --(-1)--> 𝒪]`, equally contractible, leaves the coordinate unchanged (`Pad.coord_padNegOne`).
The sign occurs: over `ℚ`, `[ℚ --0--> ℚ]` with class and functional `1` has coordinate `1`, and
`-1` after one block `[ℚ --1--> ℚ]` (`Pad.coord_padOne_example`).
The construction below uses the blocks `-1`; with them the coordinates, the outer dimensions and
hence the switch steps are exactly preserved. (With the blocks `1` the valuation clause of the leaf
would survive, but the switch steps, which relate the coordinates themselves, would have to absorb
the signs.)

Results (all PROVED):
1. `InstanceModel.padN X k N h` (`n + k = N`), `InstanceModel.pad X k : InstanceModel ϖ K (n + k)`,
   `InstanceModel.padTo X N hle`: the model `M' = diag(M, -1, …, -1)`, class `(zR, 0)`,
   functional `(lamR, 0)`, complement `w' = ((w_i, 0))_i, ((0, e_t))_t`, `y' = (y, 0)`. The
   denominator is unchanged (`Pad.detCols_colsDWY_pad`: the new block contributes `(-1)^k` twice),
   so `hden` is inherited; `hprim` is inherited. `pad_coordOf`, `padN_coordOf`: the coordinate is
   unchanged.
2. `isGenuineInstanceModel_pad`, `isGenuineInstanceModel_padN`: `IsGenuineInstanceModel` is
   preserved, through the homotopy equivalence `integralTwoTerm_padEquiv` between
   `[𝒪^{n+1} --M--> 𝒪^{n+1}]` and `[𝒪^{N+1} --M'--> 𝒪^{N+1}]` (inclusion `ι`, projection `π`,
   `π ι = 1`, and the homotopy `1 − ι π` onto the contractible summand; general form
   `twoTermHomotopyEquiv`).
3. `GenuineOuterModels.padTo G cap hle` for `nOf ≤ cap`, with `nOf = cap`: the coordinate clause
   (`padTo_coordOf`) and `IsGenuineInstanceModel` are preserved; every configuration stage has the
   same coordinates (`padTo_stage_coord`) and the same outer dimension (`padTo_stage_outerDim`: the
   genuine outer matrix of the padded models is the padded outer matrix, `outerMatrix_padMat`, and
   the kernel of `diag(D, -1, …, -1)` is isomorphic to that of `D`, `Pad.finrank_ker_mat`). An
   `OuterSwitchStep` depends on its two stages only through their outer dimensions and coordinates
   (`OuterSwitchStep.transfer`), so `GenuineOuterSwitchData.padTo`: the switching data of `G` are
   switching data of `G.padTo cap hle`, with the same derivative-prime labels.
4. `eq35InputsGenuineA_of_bounded`: the leaf from `Eq35InputsGenuineABounded W`, the same statement
   with `nOf l ≤ eq51Cap ℓ A |l|`; `eq35InputsGenuineA_iff_bounded`: the two are equivalent. The
   bound is on the matrix index `nOf`; each free term has rank `nOf + 1`. The text's total-rank
   estimate `2 * (nOf + 1) ≤ eq51Cap` implies this weaker bound. The exact-size auxiliary form
   pads the index to the cap and may exceed the text's literal total-rank cap, while retaining a
   bound depending only on `E`, `A` and `j`.
-/

noncomputable section

namespace ZInQ.Manuscript.RC.Wiring

namespace Pad

open Matrix ZInQ.Manuscript.RC.Uniform

variable {n k N : ℕ}

/-! **Block decomposition of the padded index** -/

/-- The block decomposition `Fin (n + 1) ⊕ Fin k ≃ Fin (N + 1)` of the padded index (for
`n + k = N`): the old coordinates first, then the `k` new ones. Kind: definition. -/
def eqv (h : n + k = N) : Fin (n + 1) ⊕ Fin k ≃ Fin (N + 1) :=
  finSumFinEquiv.trans (finCongr (by omega))

/-- The block decomposition `Fin n ⊕ Fin k ≃ Fin N` of the index of the padded complement.
Kind: definition. -/
def eqv' (h : n + k = N) : Fin n ⊕ Fin k ≃ Fin N :=
  finSumFinEquiv.trans (finCongr h)

/-- Kind: PROVED. -/
theorem eqv_inl_zero (h : n + k = N) : eqv h (Sum.inl 0) = 0 :=
  Fin.ext (by simp [eqv])

/-- Kind: PROVED. -/
theorem eqv_inl_succ (h : n + k = N) (a : Fin n) :
    eqv h (Sum.inl a.succ) = (eqv' h (Sum.inl a)).succ :=
  Fin.ext (by simp [eqv, eqv'])

/-- Kind: PROVED. -/
theorem eqv_inr (h : n + k = N) (t : Fin k) :
    eqv h (Sum.inr t) = (eqv' h (Sum.inr t)).succ :=
  Fin.ext (by simp [eqv, eqv']; omega)

section Ring

variable {S : Type*} [CommRing S]

/-- The padded vector `(x, 0)`. Kind: definition. -/
def vec (h : n + k = N) (x : Fin (n + 1) → S) : Fin (N + 1) → S :=
  fun r => Sum.elim x 0 ((eqv h).symm r)

/-- The vector `(0, b)` of the new block. Kind: definition. -/
def vec' (h : n + k = N) (b : Fin k → S) : Fin (N + 1) → S :=
  fun r => Sum.elim 0 b ((eqv h).symm r)

/-- The old block `x` of a vector `(x, b)`. Kind: definition. -/
def restrA (h : n + k = N) (v : Fin (N + 1) → S) : Fin (n + 1) → S :=
  fun a => v (eqv h (Sum.inl a))

/-- The new block `b` of a vector `(x, b)`. Kind: definition. -/
def restrB (h : n + k = N) (v : Fin (N + 1) → S) : Fin k → S :=
  fun t => v (eqv h (Sum.inr t))

/-- The padded matrix `diag(M, c, …, c)` (`k` new diagonal entries `c`; the model of `M` padded by
`k` blocks `[R --c--> R]`). Kind: definition. -/
def mat (h : n + k = N) (M : Matrix (Fin (n + 1)) (Fin (n + 1)) S) (c : S) :
    Matrix (Fin (N + 1)) (Fin (N + 1)) S :=
  (fromBlocks M 0 0 (diagonal fun _ => c)).submatrix (eqv h).symm (eqv h).symm

@[simp] theorem vec_inl (h : n + k = N) (x : Fin (n + 1) → S) (a : Fin (n + 1)) :
    vec h x (eqv h (Sum.inl a)) = x a := by simp [vec]

@[simp] theorem vec_inr (h : n + k = N) (x : Fin (n + 1) → S) (t : Fin k) :
    vec h x (eqv h (Sum.inr t)) = 0 := by simp [vec]

@[simp] theorem vec'_inl (h : n + k = N) (b : Fin k → S) (a : Fin (n + 1)) :
    vec' h b (eqv h (Sum.inl a)) = 0 := by simp [vec']

@[simp] theorem vec'_inr (h : n + k = N) (b : Fin k → S) (t : Fin k) :
    vec' h b (eqv h (Sum.inr t)) = b t := by simp [vec']

@[simp] theorem mat_apply (h : n + k = N) (M : Matrix (Fin (n + 1)) (Fin (n + 1)) S) (c : S)
    (p q : Fin (n + 1) ⊕ Fin k) :
    mat h M c (eqv h p) (eqv h q) = fromBlocks M 0 0 (diagonal fun _ => c) p q := by
  simp [mat]

/-- Functions on the padded index are determined by their two blocks. Kind: PROVED. -/
theorem funext_eqv (h : n + k = N) {T : Type*} {f g : Fin (N + 1) → T}
    (h1 : ∀ a, f (eqv h (Sum.inl a)) = g (eqv h (Sum.inl a)))
    (h2 : ∀ t, f (eqv h (Sum.inr t)) = g (eqv h (Sum.inr t))) : f = g := by
  funext r
  obtain ⟨p, rfl⟩ := (eqv h).surjective r
  rcases p with a | t
  · exact h1 a
  · exact h2 t

@[simp] theorem restrA_vec (h : n + k = N) (x : Fin (n + 1) → S) : restrA h (vec h x) = x := by
  funext a; simp [restrA]

@[simp] theorem restrB_vec (h : n + k = N) (x : Fin (n + 1) → S) : restrB h (vec h x) = 0 := by
  funext t; simp [restrB]

@[simp] theorem restrA_vec' (h : n + k = N) (b : Fin k → S) : restrA h (vec' h b) = 0 := by
  funext a; simp [restrA]

@[simp] theorem restrB_vec' (h : n + k = N) (b : Fin k → S) : restrB h (vec' h b) = b := by
  funext t; simp [restrB]

/-- `v = (restrA v, 0) + (0, restrB v)`. Kind: PROVED. -/
theorem vec_add_vec' (h : n + k = N) (v : Fin (N + 1) → S) :
    vec h (restrA h v) + vec' h (restrB h v) = v :=
  funext_eqv h (fun a => by simp [restrA]) (fun t => by simp [restrB])

theorem vec_zero (h : n + k = N) : vec h (0 : Fin (n + 1) → S) = 0 :=
  funext_eqv h (fun a => by simp) (fun t => by simp)

theorem vec'_zero (h : n + k = N) : vec' h (0 : Fin k → S) = 0 :=
  funext_eqv h (fun a => by simp) (fun t => by simp)

theorem vec_add (h : n + k = N) (x y : Fin (n + 1) → S) : vec h (x + y) = vec h x + vec h y :=
  funext_eqv h (fun a => by simp) (fun t => by simp)

theorem vec_smul (h : n + k = N) (s : S) (x : Fin (n + 1) → S) : vec h (s • x) = s • vec h x :=
  funext_eqv h (fun a => by simp) (fun t => by simp)

theorem vec'_add (h : n + k = N) (b b' : Fin k → S) : vec' h (b + b') = vec' h b + vec' h b' :=
  funext_eqv h (fun a => by simp) (fun t => by simp)

theorem vec'_neg (h : n + k = N) (b : Fin k → S) : vec' h (-b) = -vec' h b :=
  funext_eqv h (fun a => by simp) (fun t => by simp)

/-- The old block of `diag(M, c, …, c) v` is `M` applied to the old block of `v`. Kind: PROVED. -/
theorem mat_mulVec_inl (h : n + k = N) (M : Matrix (Fin (n + 1)) (Fin (n + 1)) S) (c : S)
    (v : Fin (N + 1) → S) (a : Fin (n + 1)) :
    (mat h M c *ᵥ v) (eqv h (Sum.inl a)) = (M *ᵥ restrA h v) a := by
  simp only [mulVec, dotProduct]
  rw [← (eqv h).sum_comp, Fintype.sum_sum_type]
  simp [restrA]

/-- The new block of `diag(M, c, …, c) v` is `c` times the new block of `v`. Kind: PROVED. -/
theorem mat_mulVec_inr (h : n + k = N) (M : Matrix (Fin (n + 1)) (Fin (n + 1)) S) (c : S)
    (v : Fin (N + 1) → S) (t : Fin k) :
    (mat h M c *ᵥ v) (eqv h (Sum.inr t)) = c * v (eqv h (Sum.inr t)) := by
  simp only [mulVec, dotProduct]
  rw [← (eqv h).sum_comp, Fintype.sum_sum_type]
  simp [diagonal_apply]

/-- `diag(M, c, …, c) (x, 0) = (M x, 0)`. Kind: PROVED. -/
theorem mat_mulVec_vec (h : n + k = N) (M : Matrix (Fin (n + 1)) (Fin (n + 1)) S) (c : S)
    (x : Fin (n + 1) → S) : mat h M c *ᵥ vec h x = vec h (M *ᵥ x) :=
  funext_eqv h (fun a => by rw [mat_mulVec_inl, restrA_vec, vec_inl])
    (fun t => by rw [mat_mulVec_inr, vec_inr, vec_inr, mul_zero])

/-- `diag(M, c, …, c) (0, b) = (0, c b)`. Kind: PROVED. -/
theorem mat_mulVec_vec' (h : n + k = N) (M : Matrix (Fin (n + 1)) (Fin (n + 1)) S) (c : S)
    (b : Fin k → S) : mat h M c *ᵥ vec' h b = vec' h (c • b) :=
  funext_eqv h (fun a => by rw [mat_mulVec_inl, restrA_vec', mulVec_zero, vec'_inl]; rfl)
    (fun t => by rw [mat_mulVec_inr, vec'_inr, vec'_inr]; rfl)

/-- Kind: PROVED. -/
theorem mat_transpose (h : n + k = N) (M : Matrix (Fin (n + 1)) (Fin (n + 1)) S) (c : S) :
    (mat h M c)ᵀ = mat h Mᵀ c := by
  ext r s
  obtain ⟨p, rfl⟩ := (eqv h).surjective r
  obtain ⟨q, rfl⟩ := (eqv h).surjective s
  rw [transpose_apply, mat_apply, mat_apply]
  rcases p with a | t <;> rcases q with b | u
  · simp
  · simp
  · simp
  · by_cases htu : t = u
    · subst htu; simp
    · simp [diagonal_apply_ne _ htu, diagonal_apply_ne _ (Ne.symm htu)]

/-- `(x, 0) diag(M, c, …, c) = (x M, 0)`. Kind: PROVED. -/
theorem vec_vecMul_mat (h : n + k = N) (M : Matrix (Fin (n + 1)) (Fin (n + 1)) S) (c : S)
    (x : Fin (n + 1) → S) : vec h x ᵥ* mat h M c = vec h (x ᵥ* M) := by
  rw [← mulVec_transpose, mat_transpose, mat_mulVec_vec, mulVec_transpose]

/-- `(x, 0) · (y, 0) = x · y`. Kind: PROVED. -/
theorem vec_dotProduct (h : n + k = N) (x y : Fin (n + 1) → S) :
    vec h x ⬝ᵥ vec h y = x ⬝ᵥ y := by
  simp only [dotProduct]
  rw [← (eqv h).sum_comp, Fintype.sum_sum_type]
  simp

/-- Padding commutes with ring homomorphisms. Kind: PROVED. -/
theorem mat_map {T : Type*} [CommRing T] (f : S →+* T) (h : n + k = N)
    (M : Matrix (Fin (n + 1)) (Fin (n + 1)) S) (c : S) :
    (mat h M c).map f = mat h (M.map f) (f c) := by
  ext r s
  obtain ⟨p, rfl⟩ := (eqv h).surjective r
  obtain ⟨q, rfl⟩ := (eqv h).surjective s
  rw [map_apply, mat_apply, mat_apply]
  rcases p with a | t <;> rcases q with b | u
  · simp
  · simp
  · simp
  · by_cases htu : t = u
    · subst htu; simp
    · simp [diagonal_apply_ne _ htu]

/-- Kind: PROVED. -/
theorem mat_map_neg_one {T : Type*} [CommRing T] (f : S →+* T) (h : n + k = N)
    (M : Matrix (Fin (n + 1)) (Fin (n + 1)) S) :
    (mat h M (-1)).map f = mat h (M.map f) (-1) := by
  rw [mat_map, map_neg, map_one]

/-- Kind: PROVED. -/
theorem vec_map {T : Type*} [CommRing T] (f : S →+* T) (h : n + k = N) (x : Fin (n + 1) → S) :
    (fun r => f (vec h x r)) = vec h (fun a => f (x a)) :=
  funext_eqv h (fun a => by simp) (fun t => by simp)

end Ring

/-! **Determinants of padded column lists** -/

section Field

variable {K : Type*} [Field K]

/-- The padded complement `((w_i, 0))_i, ((0, b_t))_t`. Kind: definition. -/
def cvec (h : n + k = N) (u : Fin n → Fin (n + 1) → K) (b : Fin k → Fin k → K) :
    Fin N → Fin (N + 1) → K :=
  fun i => Sum.elim (fun a => vec h (u a)) (fun t => vec' h (b t)) ((eqv' h).symm i)

/-- Kind: PROVED. -/
theorem cvec_inl (h : n + k = N) (u : Fin n → Fin (n + 1) → K) (b : Fin k → Fin k → K)
    (a : Fin n) : cvec h u b (eqv' h (Sum.inl a)) = vec h (u a) := by
  simp [cvec]

/-- Kind: PROVED. -/
theorem cvec_inr (h : n + k = N) (u : Fin n → Fin (n + 1) → K) (b : Fin k → Fin k → K)
    (t : Fin k) : cvec h u b (eqv' h (Sum.inr t)) = vec' h (b t) := by
  simp [cvec]

/-- **Block determinant**: `det[(v, 0) | (u_i, 0) | (0, b_t)] = det[v | u] · det[b]`.
Kind: PROVED. -/
theorem detCols_colsZW_pad (h : n + k = N) (v : Fin (n + 1) → K) (u : Fin n → Fin (n + 1) → K)
    (b : Fin k → Fin k → K) :
    detCols (colsZW (vec h v) (cvec h u b)) = detCols (colsZW v u) * (colsMat b).det := by
  have hm : colsMat (colsZW (vec h v) (cvec h u b)) =
      (fromBlocks (colsMat (colsZW v u)) 0 0 (colsMat b)).submatrix (eqv h).symm (eqv h).symm := by
    ext r s
    obtain ⟨p, rfl⟩ := (eqv h).surjective r
    obtain ⟨q, rfl⟩ := (eqv h).surjective s
    simp only [submatrix_apply, Equiv.symm_apply_apply]
    rcases q with c | t
    · refine Fin.cases ?_ (fun a => ?_) c
      · rw [eqv_inl_zero]
        rcases p with a | t <;> simp [colsMat, colsZW]
      · rw [eqv_inl_succ]
        rcases p with a' | t <;> simp [colsMat, colsZW, cvec_inl]
    · rw [eqv_inr]
      rcases p with a | t' <;> simp [colsMat, colsZW, cvec_inr]
  unfold detCols
  rw [hm, det_submatrix_equiv_self, det_fromBlocks_zero₂₁]

/-- Kind: PROVED. -/
theorem colsMat_smul_single (c : K) :
    colsMat (fun t : Fin k => c • (Pi.single t 1 : Fin k → K)) =
      c • (1 : Matrix (Fin k) (Fin k) K) := by
  ext i j
  by_cases hij : i = j
  · subst hij; simp [colsMat]
  · simp [colsMat, Pi.single_apply, hij, one_apply_ne hij]

/-- Kind: PROVED. -/
theorem det_colsMat_smul_single (c : K) :
    (colsMat (fun t : Fin k => c • (Pi.single t 1 : Fin k → K))).det = c ^ k := by
  rw [colsMat_smul_single, det_smul, det_one, mul_one, Fintype.card_fin]

/-- Kind: PROVED. -/
theorem det_colsMat_single :
    (colsMat (fun t : Fin k => (Pi.single t 1 : Fin k → K))).det = 1 := by
  have := det_colsMat_smul_single (k := k) (1 : K)
  simpa using this

/-- Kind: PROVED. -/
theorem mat_mulVec_cvec (h : n + k = N) (D : Matrix (Fin (n + 1)) (Fin (n + 1)) K) (c : K)
    (w : Fin n → Fin (n + 1) → K) (b : Fin k → Fin k → K) :
    (fun i => mat h D c *ᵥ cvec h w b i) = cvec h (fun a => D *ᵥ w a) (fun t => c • b t) := by
  funext i
  obtain ⟨p, rfl⟩ := (eqv' h).surjective i
  rcases p with a | t
  · rw [cvec_inl, cvec_inl, mat_mulVec_vec]
  · rw [cvec_inr, cvec_inr, mat_mulVec_vec']

/-- **The denominator of the padded data**: `det[D' w' | y'] = (-c)^k · det[D w | y]` for the
padded matrix `D' = diag(D, c, …, c)` and the padded complement (the new block contributes
`(-1)^k` from moving `y'` past the `k` new columns and `c^k` from the new block). Kind: PROVED. -/
theorem detCols_colsDWY_pad (h : n + k = N) (D : Matrix (Fin (n + 1)) (Fin (n + 1)) K) (c : K)
    (w : Fin n → Fin (n + 1) → K) (y : Fin (n + 1) → K) :
    detCols (colsDWY (mat h D c) (cvec h w fun t => Pi.single t 1) (vec h y)) =
      (-c) ^ k * detCols (colsDWY D w y) := by
  rw [detCols_colsDWY_eq, detCols_colsDWY_eq, mat_mulVec_cvec, detCols_colsZW_pad,
    det_colsMat_smul_single, ← h, pow_add, neg_pow c k]
  ring

/-- **The coordinate of the padded data**: `u' = u / (-c)^k`. Kind: PROVED. -/
theorem classFunctionalCoordWith_pad (h : n + k = N) (D : Matrix (Fin (n + 1)) (Fin (n + 1)) K)
    (c : K) (z lam : Fin (n + 1) → K) (w : Fin n → Fin (n + 1) → K) (y : Fin (n + 1) → K) :
    classFunctionalCoordWith (mat h D c) (vec h z) (vec h lam) (cvec h w fun t => Pi.single t 1)
        (vec h y) =
      classFunctionalCoordWith D z lam w y / (-c) ^ k := by
  unfold classFunctionalCoordWith
  rw [detCols_colsZW_pad, det_colsMat_single, mul_one, vec_dotProduct, detCols_colsDWY_pad,
    mul_comm ((-c) ^ k), div_div]

end Field

end Pad

namespace Pad

open Matrix ZInQ.Manuscript.RC.Uniform Module

variable {n k N : ℕ}

/-! **The padding as linear maps, and the kernel of the padded matrix** -/

section Lin

variable {S : Type*} [CommRing S]

/-- The inclusion `x ↦ (x, 0)` as an `S`-linear map. Kind: definition. -/
def vecLin (h : n + k = N) : (Fin (n + 1) → S) →ₗ[S] (Fin (N + 1) → S) where
  toFun := vec h
  map_add' := vec_add h
  map_smul' := vec_smul h

/-- The projection `(x, b) ↦ x` as an `S`-linear map. Kind: definition. -/
def restrALin (h : n + k = N) : (Fin (N + 1) → S) →ₗ[S] (Fin (n + 1) → S) where
  toFun := restrA h
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- The old block of `diag(M, c, …, c) v` is `M` applied to the old block of `v`. Kind: PROVED. -/
theorem restrA_mat_mulVec (h : n + k = N) (M : Matrix (Fin (n + 1)) (Fin (n + 1)) S) (c : S)
    (v : Fin (N + 1) → S) : restrA h (mat h M c *ᵥ v) = M *ᵥ restrA h v := by
  funext a
  exact mat_mulVec_inl h M c v a

end Lin

section Ker

variable {F : Type*} [Field F]

/-- **The kernel of the padded matrix** (`c ≠ 0`): `x ↦ (x, 0)` is an isomorphism
`ker M ≅ ker diag(M, c, …, c)`. Kind: definition (PROVED). -/
def kerEquiv (h : n + k = N) (D : Matrix (Fin (n + 1)) (Fin (n + 1)) F) {c : F} (hc : c ≠ 0) :
    LinearMap.ker D.mulVecLin ≃ₗ[F] LinearMap.ker (mat h D c).mulVecLin where
  toFun x := ⟨vec h x.1, by
    have hx := x.2
    rw [LinearMap.mem_ker, mulVecLin_apply] at hx ⊢
    rw [mat_mulVec_vec, hx, vec_zero]⟩
  invFun v := ⟨restrA h v.1, by
    have hv := v.2
    rw [LinearMap.mem_ker, mulVecLin_apply] at hv ⊢
    rw [← restrA_mat_mulVec h D c, hv]
    rfl⟩
  map_add' x y := Subtype.ext (vec_add h x.1 y.1)
  map_smul' a x := Subtype.ext (vec_smul h a x.1)
  left_inv x := Subtype.ext (restrA_vec h x.1)
  right_inv v := by
    have hv := v.2
    rw [LinearMap.mem_ker, mulVecLin_apply] at hv
    refine Subtype.ext (funext_eqv h (fun a => by simp [restrA]) (fun t => ?_))
    have ht := congrFun hv (eqv h (Sum.inr t))
    rw [mat_mulVec_inr, Pi.zero_apply] at ht
    simp only [vec_inr]
    exact ((mul_eq_zero.mp ht).resolve_left hc).symm

/-- **The outer dimension is unchanged by padding**: `dim ker diag(D, c, …, c) = dim ker D` for
`c ≠ 0`. Kind: PROVED. -/
theorem finrank_ker_mat (h : n + k = N) (D : Matrix (Fin (n + 1)) (Fin (n + 1)) F) {c : F}
    (hc : c ≠ 0) :
    finrank F (LinearMap.ker (mat h D c).mulVecLin) = finrank F (LinearMap.ker D.mulVecLin) :=
  (kerEquiv h D hc).finrank_eq.symm

/-- **The coordinate of the `(-1)`-padded data, for every admissible complement**: it is the
coordinate of the original data. Kind: PROVED (from `classFunctionalCoordWith_indep`). -/
theorem coord_padNegOne (h : n + k = N) (D : Matrix (Fin (n + 1)) (Fin (n + 1)) F)
    (z lam : Fin (n + 1) → F) (hz : D *ᵥ z = 0) (hlam : lam ᵥ* D = 0)
    (w : Fin n → Fin (n + 1) → F) (y : Fin (n + 1) → F) (hden : detCols (colsDWY D w y) ≠ 0)
    (w' : Fin N → Fin (N + 1) → F) (y' : Fin (N + 1) → F)
    (hden' : detCols (colsDWY (mat h D (-1)) w' y') ≠ 0) :
    classFunctionalCoordWith (mat h D (-1)) (vec h z) (vec h lam) w' y' =
      classFunctionalCoordWith D z lam w y := by
  rw [classFunctionalCoordWith_indep (mat h D (-1)) (vec h z) (vec h lam)
    (by rw [mat_mulVec_vec, hz, vec_zero]) (by rw [vec_vecMul_mat, hlam, vec_zero])
    w' (cvec h w fun t => Pi.single t 1) y' (vec h y) hden'
    (by rw [detCols_colsDWY_pad, neg_neg, one_pow, one_mul]; exact hden),
    classFunctionalCoordWith_pad, neg_neg, one_pow, div_one]

/-- **Finding: the `(+1)`-padded data have coordinate `(-1)^k u`, for every admissible
complement** (`k` blocks `[𝒪 --1--> 𝒪]`): the valuation is unchanged, the coordinate is not when
`k` is odd and `u ≠ 0`. Kind: PROVED (from `classFunctionalCoordWith_indep`). -/
theorem coord_padOne (h : n + k = N) (D : Matrix (Fin (n + 1)) (Fin (n + 1)) F)
    (z lam : Fin (n + 1) → F) (hz : D *ᵥ z = 0) (hlam : lam ᵥ* D = 0)
    (w : Fin n → Fin (n + 1) → F) (y : Fin (n + 1) → F) (hden : detCols (colsDWY D w y) ≠ 0)
    (w' : Fin N → Fin (N + 1) → F) (y' : Fin (N + 1) → F)
    (hden' : detCols (colsDWY (mat h D 1) w' y') ≠ 0) :
    classFunctionalCoordWith (mat h D 1) (vec h z) (vec h lam) w' y' =
      (-1) ^ k * classFunctionalCoordWith D z lam w y := by
  rw [classFunctionalCoordWith_indep (mat h D 1) (vec h z) (vec h lam)
    (by rw [mat_mulVec_vec, hz, vec_zero]) (by rw [vec_vecMul_mat, hlam, vec_zero])
    w' (cvec h w fun t => Pi.single t 1) y' (vec h y) hden'
    (by
      rw [detCols_colsDWY_pad]
      exact mul_ne_zero (pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero)) hden),
    classFunctionalCoordWith_pad, div_eq_mul_inv, ← inv_pow, inv_neg_one, mul_comm]

end Ker

/-- **The sign is real** (non-vacuity of the finding): over `ℚ`, the model `[ℚ --0--> ℚ]` with
class and functional `1` and complement `y = 1` has coordinate `1`; padded by one block
`[ℚ --1--> ℚ]` it has an admissible complement, and its coordinate is `-1` for every admissible
complement. Kind: PROVED. -/
theorem coord_padOne_example :
    classFunctionalCoordWith (0 : Matrix (Fin 1) (Fin 1) ℚ) (fun _ => 1) (fun _ => 1) Fin.elim0
        (fun _ => 1) = 1 ∧
      detCols (colsDWY (mat (rfl : 0 + 1 = 1) (0 : Matrix (Fin 1) (Fin 1) ℚ) 1)
        (cvec (rfl : 0 + 1 = 1) Fin.elim0 fun t => Pi.single t 1)
        (vec (rfl : 0 + 1 = 1) fun _ => 1)) ≠ 0 ∧
      ∀ (w' : Fin 1 → Fin 2 → ℚ) (y' : Fin 2 → ℚ),
        detCols (colsDWY (mat (rfl : 0 + 1 = 1) (0 : Matrix (Fin 1) (Fin 1) ℚ) 1) w' y') ≠ 0 →
        classFunctionalCoordWith (mat (rfl : 0 + 1 = 1) (0 : Matrix (Fin 1) (Fin 1) ℚ) 1)
          (vec (rfl : 0 + 1 = 1) fun _ => 1) (vec (rfl : 0 + 1 = 1) fun _ => 1) w' y' = -1 := by
  have hZ : detCols (colsZW (fun _ => (1 : ℚ)) (Fin.elim0 : Fin 0 → Fin 1 → ℚ)) = 1 := by
    have : colsZW (fun _ => (1 : ℚ)) (Fin.elim0 : Fin 0 → Fin 1 → ℚ) = fun _ _ => 1 := by
      funext i r
      obtain rfl : i = 0 := Fin.eq_of_val_eq (by omega)
      rfl
    rw [this]
    change Matrix.det (Matrix.of fun _ _ : Fin 1 => (1 : ℚ)) = 1
    rw [Matrix.det_fin_one]; rfl
  have hD : detCols (colsDWY (0 : Matrix (Fin 1) (Fin 1) ℚ) Fin.elim0 (fun _ => 1)) = 1 := by
    have : colsDWY (0 : Matrix (Fin 1) (Fin 1) ℚ) Fin.elim0 (fun _ => 1) = fun _ _ => 1 := by
      funext i r
      obtain rfl : i = Fin.last 0 := Fin.eq_of_val_eq (by omega)
      rw [colsDWY, Fin.snoc_last]
    rw [this]
    change Matrix.det (Matrix.of fun _ _ : Fin 1 => (1 : ℚ)) = 1
    rw [Matrix.det_fin_one]; rfl
  have h1 : classFunctionalCoordWith (0 : Matrix (Fin 1) (Fin 1) ℚ) (fun _ => 1) (fun _ => 1)
      Fin.elim0 (fun _ => 1) = 1 := by
    unfold classFunctionalCoordWith
    rw [hZ, hD]
    simp [dotProduct]
  refine ⟨h1, ?_, fun w' y' hden' => ?_⟩
  · rw [detCols_colsDWY_pad, hD]
    norm_num
  · have key := coord_padOne (rfl : 0 + 1 = 1) (0 : Matrix (Fin 1) (Fin 1) ℚ) (fun _ => 1)
      (fun _ => 1) (zero_mulVec _) (vecMul_zero _) Fin.elim0 (fun _ => 1)
      (by rw [hD]; exact one_ne_zero) w' y' hden'
    rw [key, h1]
    norm_num

end Pad

/-! **A two-term complex padded by a contractible summand** -/

section TwoTerm

open CategoryTheory CategoryTheory.Limits ZInQ.Contrib.CloudB3RC53.PairedFunctional

variable {S : Type} [CommRing S] {N₁ N₂ : Type} [AddCommGroup N₁] [Module S N₁]
  [AddCommGroup N₂] [Module S N₂]

/-- The components of a map of two-term complexes `[N₁ → N₁] → [N₂ → N₂]` (degree zero `0`).
Kind: definition. -/
def twoTermF (φ : N₁ →ₗ[S] N₂) :
    ∀ i : ℤ, threeTermX S PUnit N₁ N₁ i ⟶ threeTermX S PUnit N₂ N₂ i
  | .ofNat 1 => ModuleCat.ofHom φ
  | .ofNat 2 => ModuleCat.ofHom φ
  | _ => 0

/-- A map of two-term complexes `[N₁ --d₁--> N₁] → [N₂ --d₂--> N₂]` (degrees one and two) given by
`φ` in both degrees, for `φ d₁ = d₂ φ`. Kind: definition (PROVED). -/
def twoTermHom (d₁ : N₁ →ₗ[S] N₁) (d₂ : N₂ →ₗ[S] N₂) (φ : N₁ →ₗ[S] N₂) (hφ : φ ∘ₗ d₁ = d₂ ∘ₗ φ) :
    threeTermComplex (0 : PUnit →ₗ[S] N₁) d₁ (LinearMap.comp_zero _) ⟶
      threeTermComplex (0 : PUnit →ₗ[S] N₂) d₂ (LinearMap.comp_zero _) where
  f := twoTermF φ
  comm' i j hij := by
    simp only [ComplexShape.up_Rel] at hij
    subst hij
    by_cases h0 : i = 0
    · subst h0
      have e1 : (threeTermComplex (0 : PUnit →ₗ[S] N₁) d₁ (LinearMap.comp_zero _)).d 0 (0 + 1) =
          0 := (threeTermComplex_d_zero_one _ _ _).trans ModuleCat.ofHom_zero
      have e0 : twoTermF φ 0 = 0 := rfl
      rw [e0, e1]
      exact zero_comp.trans zero_comp.symm
    by_cases h1 : i = 1
    · subst h1
      refine ModuleCat.hom_ext (LinearMap.ext fun x => ?_)
      change d₂ (φ x) = φ (d₁ x)
      exact (LinearMap.congr_fun hφ x).symm
    · have e₁ : (threeTermComplex (0 : PUnit →ₗ[S] N₁) d₁ (LinearMap.comp_zero _)).d i (i + 1) =
          0 := threeTermD_eq_zero _ _ _ _ (fun h => h0 h.1) (fun h => h1 h.1)
      have e₂ : (threeTermComplex (0 : PUnit →ₗ[S] N₂) d₂ (LinearMap.comp_zero _)).d i (i + 1) =
          0 := threeTermD_eq_zero _ _ _ _ (fun h => h0 h.1) (fun h => h1 h.1)
      rw [e₁, e₂]
      exact comp_zero.trans zero_comp.symm

/-- **A homotopy equivalence of two-term complexes** `[N₁ --d₁--> N₁] ≃ [N₂ --d₂--> N₂]` from maps
`φ : N₁ → N₂`, `ψ : N₂ → N₁` of complexes with `ψ φ = 1` and a homotopy `s : N₂ → N₂` (degree two
to one) with `φ ψ = s d₂ + 1` on degree one and `φ ψ = d₂ s + 1` on degree two. Kind: definition
(PROVED). -/
def twoTermHomotopyEquiv (d₁ : N₁ →ₗ[S] N₁) (d₂ : N₂ →ₗ[S] N₂) (φ : N₁ →ₗ[S] N₂)
    (ψ : N₂ →ₗ[S] N₁) (s : N₂ →ₗ[S] N₂) (hφ : φ ∘ₗ d₁ = d₂ ∘ₗ φ) (hψ : ψ ∘ₗ d₂ = d₁ ∘ₗ ψ)
    (hψφ : ψ ∘ₗ φ = LinearMap.id) (hs1 : φ ∘ₗ ψ = s ∘ₗ d₂ + LinearMap.id)
    (hs2 : φ ∘ₗ ψ = d₂ ∘ₗ s + LinearMap.id) :
    HomotopyEquiv (threeTermComplex (0 : PUnit →ₗ[S] N₁) d₁ (LinearMap.comp_zero _))
      (threeTermComplex (0 : PUnit →ₗ[S] N₂) d₂ (LinearMap.comp_zero _)) where
  hom := twoTermHom d₁ d₂ φ hφ
  inv := twoTermHom d₂ d₁ ψ hψ
  homotopyHomInvId := Homotopy.ofEq (by
    ext i : 1
    rcases i with (_ | _ | _ | n) | n
    · ext x
      exact Subsingleton.elim (α := PUnit) _ _
    · refine ModuleCat.hom_ext (LinearMap.ext fun x => ?_)
      change ψ (φ x) = x
      exact LinearMap.congr_fun hψφ x
    · refine ModuleCat.hom_ext (LinearMap.ext fun x => ?_)
      change ψ (φ x) = x
      exact LinearMap.congr_fun hψφ x
    · ext x
      exact Subsingleton.elim (α := PUnit) _ _
    · ext x
      exact Subsingleton.elim (α := PUnit) _ _)
  homotopyInvHomId :=
    { hom := fun i j =>
          (show (threeTermComplex (0 : PUnit →ₗ[S] N₂) d₂ (LinearMap.comp_zero _)).X i ⟶
            (threeTermComplex (0 : PUnit →ₗ[S] N₂) d₂ (LinearMap.comp_zero _)).X j from
            threeTermH (0 : N₂ →ₗ[S] PUnit) s i j)
      zero := fun i j hij => by
        simp only [ComplexShape.up_Rel] at hij
        apply threeTermH_eq_zero
        · rintro ⟨rfl, rfl⟩; exact hij rfl
        · rintro ⟨rfl, rfl⟩; exact hij rfl
      comm := fun i => by
        rw [dNext_eq _ (show (ComplexShape.up ℤ).Rel i (i + 1) from rfl),
          prevD_eq _ (show (ComplexShape.up ℤ).Rel (i - 1) i from by simp)]
        rcases i with (_ | _ | _ | n) | n
        · ext x
          exact Subsingleton.elim (α := PUnit) _ _
        · refine ModuleCat.hom_ext (LinearMap.ext fun (x : N₂) => ?_)
          change φ (ψ x) = s (d₂ x) + (0 : PUnit →ₗ[S] N₂) ((0 : N₂ →ₗ[S] PUnit) x) + x
          have := LinearMap.congr_fun hs1 x
          simp only [LinearMap.comp_apply, LinearMap.add_apply, LinearMap.id_apply] at this
          simp [this]
        · refine ModuleCat.hom_ext (LinearMap.ext fun (x : N₂) => ?_)
          change φ (ψ x) = (0 : N₂) + d₂ (s x) + x
          have := LinearMap.congr_fun hs2 x
          simp only [LinearMap.comp_apply, LinearMap.add_apply, LinearMap.id_apply] at this
          simp [this]
        · ext x
          exact Subsingleton.elim (α := PUnit) _ _
        · ext x
          exact Subsingleton.elim (α := PUnit) _ _ }

end TwoTerm

open Matrix in
/-- **Padding by contractible blocks is a homotopy equivalence** (part 2 of the padding
argument): `[R^{n+1} --M--> R^{n+1}] ≃ [R^{N+1} --diag(M, -1, …, -1)--> R^{N+1}]`, by the inclusion
`x ↦ (x, 0)`, the projection `(x, b) ↦ x` and the homotopy `1 − ιπ` (the projection onto the new
block, which is the contractible summand `[R^k --(-1)--> R^k]`). Kind: definition (PROVED). -/
def integralTwoTerm_padEquiv {R : Type} [CommRing R] {n k N : ℕ} (h : n + k = N)
    (M : Matrix (Fin (n + 1)) (Fin (n + 1)) R) :
    HomotopyEquiv (integralTwoTerm M) (integralTwoTerm (Pad.mat h M (-1))) :=
  twoTermHomotopyEquiv M.mulVecLin (Pad.mat h M (-1)).mulVecLin (Pad.vecLin h) (Pad.restrALin h)
    (LinearMap.id - Pad.vecLin h ∘ₗ Pad.restrALin h)
    (LinearMap.ext fun x => by
      change Pad.vec h (M *ᵥ x) = Pad.mat h M (-1) *ᵥ Pad.vec h x
      rw [Pad.mat_mulVec_vec])
    (LinearMap.ext fun v => by
      change Pad.restrA h (Pad.mat h M (-1) *ᵥ v) = M *ᵥ Pad.restrA h v
      exact Pad.restrA_mat_mulVec h M (-1) v)
    (LinearMap.ext fun x => by
      change Pad.restrA h (Pad.vec h x) = x
      exact Pad.restrA_vec h x)
    (LinearMap.ext fun v => by
      change Pad.vec h (Pad.restrA h v) =
        (Pad.mat h M (-1) *ᵥ v - Pad.vec h (Pad.restrA h (Pad.mat h M (-1) *ᵥ v))) + v
      refine Pad.funext_eqv h (fun a => ?_) (fun t => ?_)
      · simp [Pad.restrA]
      · simp [Pad.mat_mulVec_inr])
    (LinearMap.ext fun v => by
      change Pad.vec h (Pad.restrA h v) =
        Pad.mat h M (-1) *ᵥ (v - Pad.vec h (Pad.restrA h v)) + v
      refine Pad.funext_eqv h (fun a => ?_) (fun t => ?_)
      · rw [Pi.add_apply, Pad.mat_mulVec_inl]
        have : Pad.restrA h (v - Pad.vec h (Pad.restrA h v)) = 0 := by
          funext b; simp [Pad.restrA]
        rw [this, Matrix.mulVec_zero]
        simp [Pad.restrA]
      · rw [Pi.add_apply, Pad.mat_mulVec_inr]
        simp)

end ZInQ.Manuscript.RC.Wiring

/-! **The padded instance models and model families** -/

namespace ZInQ.Contrib.CloudB3RC53.SwitchInputs

open Matrix Module Filter ZInQ.Manuscript.RC.Uniform ZInQ.Manuscript.RC.Limits
  ZInQ.Contrib.CloudB3RC53.UniformSwitch

section PadModel

variable {R : Type} [CommRing R] {ϖ : R} {K : Type} [Field K] [Algebra R K]

/-- **The padded instance model** (part 1 of the padding argument), for `n + k = N`: the model
`M' = diag(M, -1, …, -1)` (`k` contractible blocks `[R --(-1)--> R]`), the class `(zR, 0)`, the
functional `(lamR, 0)`, the complement `w' = ((w_i, 0))_i, ((0, e_t))_t`, `y' = (y, 0)`. The new
block contributes the unit factor `(-1)^k` twice to the denominator (`detCols_colsDWY_pad`), so
`hden` is inherited; `hprim` is inherited. Kind: definition (PROVED). -/
def InstanceModel.padN {n : ℕ} (X : InstanceModel ϖ K n) (k N : ℕ) (h : n + k = N) :
    InstanceModel ϖ K N where
  M := ZInQ.Manuscript.RC.Wiring.Pad.mat h X.M (-1)
  zR := ZInQ.Manuscript.RC.Wiring.Pad.vec h X.zR
  lamR := ZInQ.Manuscript.RC.Wiring.Pad.vec h X.lamR
  hz := by
    rw [ZInQ.Manuscript.RC.Wiring.Pad.mat_mulVec_vec, X.hz, ZInQ.Manuscript.RC.Wiring.Pad.vec_zero]
  hlam := by
    rw [ZInQ.Manuscript.RC.Wiring.Pad.vec_vecMul_mat, X.hlam,
      ZInQ.Manuscript.RC.Wiring.Pad.vec_zero]
  w := ZInQ.Manuscript.RC.Wiring.Pad.cvec h X.w fun t => Pi.single t 1
  y := ZInQ.Manuscript.RC.Wiring.Pad.vec h X.y
  hden := by
    rw [ZInQ.Manuscript.RC.Wiring.Pad.mat_map, map_neg, map_one,
      ZInQ.Manuscript.RC.Wiring.Pad.detCols_colsDWY_pad, neg_neg, one_pow, one_mul]
    exact X.hden
  hprim := by
    obtain ⟨i, hi⟩ := X.hprim
    exact ⟨ZInQ.Manuscript.RC.Wiring.Pad.eqv h (Sum.inl i), by
      rw [ZInQ.Manuscript.RC.Wiring.Pad.vec_inl]; exact hi⟩

/-- **The coordinate is unchanged by padding** (part 1). Kind: PROVED. -/
theorem InstanceModel.padN_coordOf {n : ℕ} (X : InstanceModel ϖ K n) (k N : ℕ) (h : n + k = N) :
    (X.padN k N h).coordOf = X.coordOf := by
  change classFunctionalCoordWith
      ((ZInQ.Manuscript.RC.Wiring.Pad.mat h X.M (-1)).map (algebraMap R K))
      (fun i => algebraMap R K (ZInQ.Manuscript.RC.Wiring.Pad.vec h X.zR i))
      (fun i => algebraMap R K (ZInQ.Manuscript.RC.Wiring.Pad.vec h X.lamR i))
      (ZInQ.Manuscript.RC.Wiring.Pad.cvec h X.w fun t => Pi.single t 1)
      (ZInQ.Manuscript.RC.Wiring.Pad.vec h X.y) = X.coordOf
  rw [ZInQ.Manuscript.RC.Wiring.Pad.mat_map, map_neg, map_one,
    ZInQ.Manuscript.RC.Wiring.Pad.vec_map, ZInQ.Manuscript.RC.Wiring.Pad.vec_map,
    ZInQ.Manuscript.RC.Wiring.Pad.classFunctionalCoordWith_pad, neg_neg, one_pow, div_one]
  rfl

/-- **The padding by `k` blocks**: `InstanceModel ϖ K n → InstanceModel ϖ K (n + k)`.
Kind: definition. -/
def InstanceModel.pad {n : ℕ} (X : InstanceModel ϖ K n) (k : ℕ) : InstanceModel ϖ K (n + k) :=
  X.padN k (n + k) rfl

/-- `(X.pad k).coordOf = X.coordOf`. Kind: PROVED. -/
theorem InstanceModel.pad_coordOf {n : ℕ} (X : InstanceModel ϖ K n) (k : ℕ) :
    (X.pad k).coordOf = X.coordOf :=
  X.padN_coordOf k (n + k) rfl

/-- The padding to a size `N ≥ n` (by `N - n` blocks). Kind: definition. -/
def InstanceModel.padTo {n : ℕ} (X : InstanceModel ϖ K n) (N : ℕ) (hle : n ≤ N) :
    InstanceModel ϖ K N :=
  X.padN (N - n) N (by omega)

/-- Kind: PROVED. -/
theorem InstanceModel.padTo_coordOf {n : ℕ} (X : InstanceModel ϖ K n) (N : ℕ) (hle : n ≤ N) :
    (X.padTo N hle).coordOf = X.coordOf :=
  X.padN_coordOf _ _ _

end PadModel

section PadFamilyBasic

variable {R : Type} [CommRing R] {ϖ : R} {K : Type} [Field K] [Algebra R K] {J : Type}

/-- **The genuine outer matrix of padded models is the padded outer matrix**: `outerMatrix` is
entrywise, and the new blocks are constant. Kind: PROVED. -/
theorem outerMatrix_padMat (U : Ultrafilter J) (ϖ : R) {n k N : ℕ} (h : n + k = N)
    (M : J → Matrix (Fin (n + 1)) (Fin (n + 1)) R) (c : R) :
    outerMatrix U ϖ (fun j => ZInQ.Manuscript.RC.Wiring.Pad.mat h (M j) c) =
      ZInQ.Manuscript.RC.Wiring.Pad.mat h (outerMatrix U ϖ M) (algebraMap R (OInf U ϖ) c) := by
  ext r s
  obtain ⟨p, rfl⟩ := (ZInQ.Manuscript.RC.Wiring.Pad.eqv h).surjective r
  obtain ⟨q, rfl⟩ := (ZInQ.Manuscript.RC.Wiring.Pad.eqv h).surjective s
  rw [ZInQ.Manuscript.RC.Wiring.Pad.mat_apply]
  simp only [outerMatrix, Matrix.of_apply, ZInQ.Manuscript.RC.Wiring.Pad.mat_apply]
  rcases p with a | t <;> rcases q with b | u
  · rfl
  · exact map_zero (toOInf U ϖ)
  · exact map_zero (toOInf U ϖ)
  · by_cases htu : t = u
    · subst htu
      simp only [fromBlocks_apply₂₂, diagonal_apply_eq]
      rfl
    · simp only [fromBlocks_apply₂₂, diagonal_apply_ne _ htu]
      exact map_zero (toOInf U ϖ)

/-- The case `c = -1` of `outerMatrix_padMat`. Kind: PROVED. -/
theorem outerMatrix_padMat_neg_one (U : Ultrafilter J) (ϖ : R) {n k N : ℕ} (h : n + k = N)
    (M : J → Matrix (Fin (n + 1)) (Fin (n + 1)) R) :
    outerMatrix U ϖ (fun j => ZInQ.Manuscript.RC.Wiring.Pad.mat h (M j) (-1)) =
      ZInQ.Manuscript.RC.Wiring.Pad.mat h (outerMatrix U ϖ M) (-1) := by
  rw [outerMatrix_padMat, map_neg, map_one]

/-- **The family padded to a size function `cap ≥ nOf`** (part 3): `nOf = cap`, every model padded
by `cap l - nOf l` contractible blocks. Kind: definition. -/
def GenuineOuterModels.padTo {Inst P : Type} (G : GenuineOuterModels ϖ K Inst P)
    (cap : List P → ℕ) (hle : ∀ l, G.nOf l ≤ cap l) : GenuineOuterModels ϖ K Inst P where
  nOf := cap
  model i l := (G.model i l).padTo (cap l) (hle l)

/-- Kind: PROVED. -/
theorem GenuineOuterModels.padTo_coordOf {Inst P : Type} (G : GenuineOuterModels ϖ K Inst P)
    (cap : List P → ℕ) (hle : ∀ l, G.nOf l ≤ cap l) (i : Inst) (l : List P) :
    ((G.padTo cap hle).model i l).coordOf = (G.model i l).coordOf :=
  InstanceModel.padTo_coordOf (G.model i l) (cap l) (hle l)

end PadFamilyBasic

section PadFamily

variable {R : Type} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] {ϖ : R}
  [Fact (Irreducible ϖ)] {K : Type} [Field K] [Algebra R K] {J : Type} {𝒰 : Ultrafilter J}

/-- **The stages of the padded family have the same coordinates.** Kind: PROVED. -/
theorem GenuineOuterModels.padTo_stage_coord {Inst P : Type} (G : GenuineOuterModels ϖ K Inst P)
    (cap : List P → ℕ) (hle : ∀ l, G.nOf l ≤ cap l) (inst : J → Inst) (l : List P) (j : J) :
    ((G.padTo cap hle).stage 𝒰 inst l).base.toOuterStage.coord j =
      (G.stage 𝒰 inst l).base.toOuterStage.coord j :=
  InstanceModel.padTo_coordOf (G.model (inst j) l) (cap l) (hle l)

/-- **The stages of the padded family have the same outer dimension**: the genuine outer matrix of
the padded models is the padded outer matrix (`outerMatrix_padMat`), whose kernel has the same
dimension (`finrank_ker_mat`). Kind: PROVED. -/
theorem GenuineOuterModels.padTo_stage_outerDim {Inst P : Type}
    (G : GenuineOuterModels ϖ K Inst P) (cap : List P → ℕ) (hle : ∀ l, G.nOf l ≤ cap l)
    (inst : J → Inst) (l : List P) :
    ((G.padTo cap hle).stage 𝒰 inst l).base.toOuterStage.outerDim =
      (G.stage 𝒰 inst l).base.toOuterStage.outerDim := by
  change finrank (FractionRing (OInf 𝒰 ϖ)) (LinearMap.ker ((outerMatrix 𝒰 ϖ
      (fun j => ZInQ.Manuscript.RC.Wiring.Pad.mat (_ : G.nOf l + (cap l - G.nOf l) = cap l)
        (G.model (inst j) l).M (-1))).map
      (algebraMap (OInf 𝒰 ϖ) (FractionRing (OInf 𝒰 ϖ)))).mulVecLin) =
    finrank (FractionRing (OInf 𝒰 ϖ)) (LinearMap.ker ((outerMatrix 𝒰 ϖ
      (fun j => (G.model (inst j) l).M)).map
      (algebraMap (OInf 𝒰 ϖ) (FractionRing (OInf 𝒰 ϖ)))).mulVecLin)
  rw [outerMatrix_padMat_neg_one, ZInQ.Manuscript.RC.Wiring.Pad.mat_map_neg_one]
  exact ZInQ.Manuscript.RC.Wiring.Pad.finrank_ker_mat _ _ (neg_ne_zero.mpr one_ne_zero)

/-- **A switch step depends on its stages only through their outer dimensions and coordinates**:
an `OuterSwitchStep S S'` transfers to stages `T, T'` with the same outer dimensions and the same
coordinates. Kind: definition (PROVED). -/
def OuterSwitchStep.transfer {S S' T T' : OuterStage (FractionRing (OInf 𝒰 ϖ)) K J}
    (X : OuterSwitchStep S S') (h1 : S.outerDim = T.outerDim) (h2 : S'.outerDim = T'.outerDim)
    (h3 : ∀ j, S.coord j = T.coord j) (h4 : ∀ j, S'.coord j = T'.coord j) :
    OuterSwitchStep T T' where
  X := X.X
  hs := h1.symm.trans X.hs
  hs' := h2.symm.trans X.hs'
  coords := X.coords.mono fun j ⟨Y, mF, mS, hF, hS, hYF, hYS, e1, e2⟩ =>
    ⟨Y, mF, mS, hF, hS, hYF, hYS, (h3 j).symm.trans e1, (h4 j).symm.trans e2⟩

/-- **The switching data transfer to the padded family** (part 3): a configuration of the padded
family has the same outer dimension and coordinates as the original one, so the switch steps of
`G` are switch steps of `G.padTo cap hle`. Kind: PROVED. -/
theorem GenuineOuterSwitchData.padTo {Inst P : Type} {G : GenuineOuterModels ϖ K Inst P}
    {inst : J → Inst} (H : GenuineOuterSwitchData 𝒰 G inst) (cap : List P → ℕ)
    (hle : ∀ l, G.nOf l ≤ cap l) : GenuineOuterSwitchData 𝒰 (G.padTo cap hle) inst where
  step l hl := by
    rw [G.padTo_stage_outerDim] at hl
    obtain ⟨p, ⟨T⟩⟩ := H.step l hl
    exact ⟨p, ⟨T.transfer (G.padTo_stage_outerDim cap hle inst l).symm
      (G.padTo_stage_outerDim cap hle inst (l ++ [p])).symm
      (fun j => (G.padTo_stage_coord cap hle inst l j).symm)
      (fun j => (G.padTo_stage_coord cap hle inst (l ++ [p]) j).symm)⟩⟩

end PadFamily

end ZInQ.Contrib.CloudB3RC53.SwitchInputs

/-! **The leaf from bounded sizes** -/

namespace ZInQ.Manuscript.RC.Wiring

open ZInQ.Manuscript ZInQ.Manuscript.SelmerTwoPower ZInQ.Contrib.CloudB3RC53
  ZInQ.Manuscript.RC.Uniform ZInQ.Manuscript.RC.Rings Module CategoryTheory Filter
open ZInQ.Manuscript.RC.Determinant (OO)

attribute [local instance] Nat.fact_prime_two

/-- **`IsGenuineInstanceModel` is preserved by padding** (part 2): compose the given homotopy
equivalence with `integralTwoTerm_padEquiv`. Kind: PROVED. -/
theorem isGenuineInstanceModel_padN {n : ℕ}
    {X : SwitchInputs.InstanceModel (2 : OO) (FractionRing OO) n} (k N : ℕ) (h : n + k = N)
    (hX : IsGenuineInstanceModel X) : IsGenuineInstanceModel (X.padN k N h) := by
  obtain ⟨D, hD, ⟨e⟩⟩ := hX
  exact ⟨D, hD, ⟨e.trans (integralTwoTerm_padEquiv h X.M)⟩⟩

/-- Kind: PROVED. -/
theorem isGenuineInstanceModel_pad {n : ℕ}
    {X : SwitchInputs.InstanceModel (2 : OO) (FractionRing OO) n} (k : ℕ)
    (hX : IsGenuineInstanceModel X) : IsGenuineInstanceModel (X.pad k) :=
  isGenuineInstanceModel_padN k (n + k) rfl hX

variable {ℓ : ℕ} (W : WData ℓ)

/-- **The inputs of (3.5) with the text's size bound** (tex 4453–4460, 4936–4938, 4954–4956): the
leaf `Eq35InputsGenuineA W` with `nOf l ≤ eq51Cap ℓ A |l|` in place of `nOf l = eq51Cap ℓ A |l|`;
all other conjuncts verbatim. Kind: definition. The bound is on the matrix index `nOf`; each free
term has rank `nOf + 1`. The text's total-rank estimate `2 * (nOf + 1) ≤ eq51Cap` implies this
weaker bound. The exact-size auxiliary form pads the index to the cap and may exceed the text's
literal total-rank cap, while retaining a bound depending only on `E`, `A` and `j`. -/
def Eq35InputsGenuineABounded : Prop :=
  ∃ (uprim : ℤ → ℤ → FractionRing Lambda) (C₀ : ℤ),
    (∀ h k' : ℤ, W.prepared h → AnalyticRank (Etw ℓ h) 1 → W.IsRoughCompanion h k' →
      RegularityInputsGPK (uprim h k')) ∧
    (∀ h k' : ℤ, W.prepared h → AnalyticRank (Etw ℓ h) 1 → W.IsRoughCompanion h k' →
      ∀ uh : LambdaHalf, lambdaHalfToFrac uh = uprim h k' →
        ∃ (t : ℕ → ℕ) (err : ℤ), (∀ p, t p ≤ 2) ∧ |err| ≤ C₀ ∧
          v2 (centralSpecialization uh) =
            ((2 * W.jrc h k' - 4 * (omega h : ℤ) - sFun ℓ h - sFun ℓ (h * k') -
              ∑ p ∈ k'.natAbs.primeFactors, (t p : ℤ) + err : ℤ) : WithTop ℤ)) ∧
    ∀ A : ℕ, ∃ (Pl : Type)
      (G : SwitchInputs.GenuineOuterModels (2 : OO) (FractionRing OO) (CompanionPair W A) Pl),
      (∀ l, G.nOf l ≤ eq51Cap ℓ A l.length) ∧
      (∀ i l, IsGenuineInstanceModel (G.model i l)) ∧
      (∀ i : CompanionPair W A, vO (G.model i []).coordOf = vO (iotaO (uprim i.h i.k))) ∧
      ∀ inst : ℕ → CompanionPair W A,
        SwitchInputs.GenuineOuterSwitchData (Filter.hyperfilter ℕ) G inst

/-- **The leaf from the bounded sizes** (part 4 of the padding argument): pad every family to the
cap of (5.1) (`GenuineOuterModels.padTo`); the coordinate clause, `IsGenuineInstanceModel` and the
switching data are preserved. Kind: PROVED. -/
theorem eq35InputsGenuineA_of_bounded (hin : Eq35InputsGenuineABounded W) :
    Eq35InputsGenuineA W := by
  obtain ⟨uprim, C₀, hreg, h46, hout⟩ := hin
  refine ⟨uprim, C₀, hreg, h46, fun A => ?_⟩
  obtain ⟨Pl, G, hle, hgen, hcoord, hsw⟩ := hout A
  refine ⟨Pl, G.padTo (fun l => eq51Cap ℓ A l.length) hle, fun l => rfl,
    fun i l => isGenuineInstanceModel_padN _ _ _ (hgen i l), fun i => ?_,
    fun inst => (hsw inst).padTo _ hle⟩
  rw [SwitchInputs.GenuineOuterModels.padTo_coordOf]
  exact hcoord i

/-- **The two forms of the leaf are equivalent.** Kind: PROVED. -/
theorem eq35InputsGenuineA_iff_bounded : Eq35InputsGenuineA W ↔ Eq35InputsGenuineABounded W := by
  refine ⟨fun hin => ?_, eq35InputsGenuineA_of_bounded W⟩
  obtain ⟨uprim, C₀, hreg, h46, hout⟩ := hin
  refine ⟨uprim, C₀, hreg, h46, fun A => ?_⟩
  obtain ⟨Pl, G, hn, hgen, hcoord, hsw⟩ := hout A
  exact ⟨Pl, G, fun l => (hn l).le, hgen, hcoord, hsw⟩

/-- **`Eq35InputsGenuineABounded W` is satisfiable** in the degenerate case (no ring instances),
through `eq35InputsGenuineA_of_not_prepared`. Kind: PROVED. -/
theorem eq35InputsGenuineABounded_of_not_prepared (hW : ∀ h, ¬ W.prepared h) :
    Eq35InputsGenuineABounded W :=
  (eq35InputsGenuineA_iff_bounded W).mp (eq35InputsGenuineA_of_not_prepared W hW)

end ZInQ.Manuscript.RC.Wiring
