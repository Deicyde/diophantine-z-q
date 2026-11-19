import ZInQKernel.Contrib.OneProof.RC.Wiring.CommonCoordinate14Model
import ZInQKernel.Contrib.OneProof.RC.Wiring.CommonCoordinate12Cob

/-!
# The field part of a chain of relaxations: models, coordinates, steps and (4.7)

Manuscript `diophantine_zq.tex`, Lemma `ex:arith-common-coordinate` (tex 4157–4194) in the
iterated mapping-cone bases (tex 4185–4193).

Over a field `F`, the matrix data `c : ChainMat F m₀ m₁ m₂` of a chain of relaxations whose
identities hold exactly for the first `n` steps (`c.Holds ⊥ f n`) give:

* `ChainMat.cx_of_holds`, `ChainMat.blockAt`: the models of the supports `T_i` (`i ≤ n`) are
  block complexes; `ChainMat.coneAt`: the cone model of step `i < n` is a pre-cancellation
  complex with the new block `B_i`;
* `blk1_mulVec_zP`, `lP_vecMul_blk1`, `blockAt_cycle`, `blockAt_closed`, `coneAt_cycle`,
  `coneAt_closed`: the primitive and the relaxed classes are cycles, the primitive and the relaxed
  functionals are closed;
* `ChainMat.vRel`, `ChainMat.vPrim`: the Knudsen–Mumford coordinates of the cone model of step `i`
  and of the model of the support `T_i`;
* `fourCx_eq_of`, `kmCoord_cx_congr`, `ChainMat.B_eq`, `ChainMat.coneAt_cancel_toFour`, and
  **`ChainMat.kmStep`**: each step is a `KmStep` when its two-place block is invertible;
* `linkOrient`, `linkSign`, **`ChainMat.vPrim_succ`**: the primitive coordinate of step `i + 1`
  is the relaxed coordinate of step `i` times an explicit sign;
* `chainSign`, `ChainMat.chainV`, `ChainMat.vPrim_eq_chainV`, **`ChainMat.chain_h47`**,
  **`ChainMat.exists_chain_h47`**: the values and signs along the chain, with (4.7) at each step.

Kinds: definitions and PROVED.
-/

noncomputable section

namespace ZInQ.Manuscript.RC.Wiring

open Matrix ZInQ.Contrib.CloudB3RC53.ClearingComplex ZInQ.Contrib.CloudB3RC53.Torsion
open ZInQ.Contrib.CloudB3RC53.CommonCoordinate (twoPlaceBlock)
open ZInQ.Manuscript.RC.Central (pointFactor quotientFactor)

/-! ### Congruence of the coordinate -/

/-- Two four-term complexes with the same differentials are equal (tex 4185–4193).
Kind: PROVED. -/
theorem fourCx_eq_of {K : Type} [Field K] {ι0 ι1 ι2 ι3 : Type} [Fintype ι1] [Fintype ι2]
    {C C' : FourCx K ι0 ι1 ι2 ι3} (h0 : C.d0 = C'.d0) (h1 : C.d1 = C'.d1)
    (h2 : C.d2 = C'.d2) : C = C' := by
  cases C
  cases C'
  simp only at h0 h1 h2
  subst h0 h1 h2
  rfl

/-- The coordinate on equal four-term complexes, at the same cycle and functional
(tex 3877–3892, 4185–4193). Kind: PROVED. -/
theorem kmCoord_cx_congr {K : Type} [Field K] {ι0 ι1 ι2 ι3 : Type} [Fintype ι0] [Fintype ι1]
    [Fintype ι2] [Fintype ι3] [DecidableEq ι0] [DecidableEq ι1] [DecidableEq ι2]
    [DecidableEq ι3] {C C' : FourCx K ι0 ι1 ι2 ι3} (h : C = C') {z : ι1 → K} {lam : ι2 → K}
    (hz : C.d1 *ᵥ z = 0) (hz' : C'.d1 *ᵥ z = 0) (hlam : lam ᵥ* C.d1 = 0)
    (hlam' : lam ᵥ* C'.d1 = 0) (σ : (ι0 ⊕ Unit) ⊕ ι2 ≃ ι1 ⊕ (ι3 ⊕ Unit)) :
    kmCoord C z lam hz hlam σ = kmCoord C' z lam hz' hlam' σ := by
  subst h
  rfl

/-! ### The orientations and signs of the links -/

/-- **The orientation of the model of `T_{i+1}` transported from the cone model of step `i`**
along the re-indexings `chE1`, `chE2` (tex 4185–4193). Kind: definition. -/
def linkOrient (m0 m1 m2 i : ℕ) :
    (Fin m0 ⊕ Unit) ⊕ cD2 m1 m2 (i + 1) ≃ cD1 m0 m1 (i + 1) ⊕ (Fin m2 ⊕ Unit) :=
  (Equiv.sumCongr (Equiv.sumCongr (Equiv.refl (Fin m0)) (Equiv.refl Unit))
      (chE2 m1 m2 i)).symm.trans
    ((σFull m0 (m1 + 4 * i) m2 NS).trans
      (Equiv.sumCongr (chE1 m0 m1 i) (Equiv.sumCongr (Equiv.refl (Fin m2)) (Equiv.refl Unit))))

/-- **The sign of the comparison of the cone bases at step `i`** (tex 4185–4193: "their
comparison is a sign"): the sign of the permutation comparing the block orientation of the model
of `T_{i+1}` with the transported orientation. Kind: definition. -/
def linkSign (m0 m1 m2 i : ℕ) : ℤˣ :=
  Equiv.Perm.sign ((σBlock m0 (m1 + 4 * (i + 1)) m2).trans (linkOrient m0 m1 m2 i).symm)

/-- **The signs along the chain** (tex 4185–4193): `σ₀ = 1` and `σ_{i+1} = linkSign i`.
Kind: definition. -/
def chainSign (m0 m1 m2 : ℕ) : ℕ → ℤˣ
  | 0 => 1
  | i + 1 => linkSign m0 m1 m2 i

namespace ChainMat

variable {F : Type} [Field F] {m0 m1 m2 : ℕ} (c : ChainMat F m0 m1 m2) {f : FrobSeq F} {n : ℕ}

/-! ### The models of the supports and the cone models -/

/-- **The models of the supports are complexes** (tex 4185–4193): for `i ≤ n`, `d¹ d⁰ = 0` and
`d² d¹ = 0` for the model of `C_{T_i}`, by induction from the model of `C_∅` and the identities
of the cone models (`blk1 (i+1) blk0 (i+1)` is the re-indexed `[[P, Q], [0, B]] (d⁰; 0)`,
`blk2 (i+1) blk1 (i+1)` the re-indexed `(U V) [[P, Q], [0, B]]`). Kind: PROVED. -/
theorem cx_of_holds (H : c.Holds ⊥ f n) :
    ∀ i ≤ n, c.blk1 i * c.blk0 i = 0 ∧ c.blk2 i * c.blk1 i = 0 := by
  intro i
  induction i with
  | zero =>
    intro _
    exact ⟨Matrix.ext fun a b => Ideal.mem_bot.mp (H.h10 a b),
      Matrix.ext fun a b => Ideal.mem_bot.mp (H.h21 a b)⟩
  | succ i ih =>
    intro hi
    obtain ⟨h10, h21⟩ := ih (Nat.le_of_succ_le hi)
    have hQVB : c.blk2 i * c.Q i + c.V i * c.B i = 0 :=
      Matrix.ext fun a b => Ideal.mem_bot.mp (H.hQVB i hi a b)
    constructor
    · change (fromBlocks (c.blk1 i) (c.Q i) 0 (c.B i)).submatrix (chE2 m1 m2 i).symm
          (chE1 m0 m1 i).symm * (fromRows (c.blk0 i) (0 : Matrix NS (Fin m0) F)).submatrix
          (chE1 m0 m1 i).symm id = 0
      rw [submatrix_mul_equiv, fromBlocks_mul_fromRows, h10]
      simp
    · change (fromCols (c.blk2 i) (c.V i)).submatrix id (chE2 m1 m2 i).symm *
          (fromBlocks (c.blk1 i) (c.Q i) 0 (c.B i)).submatrix (chE2 m1 m2 i).symm
            (chE1 m0 m1 i).symm = 0
      rw [submatrix_mul_equiv, fromCols_mul_fromBlocks, h21, hQVB]
      simp

/-- **The model of the support `T_i`** (tex 4185–4193): the block complex
`(m₀, m₁ + 4i, m₂; blk0 i, blk1 i, blk2 i)`, for `i ≤ n`. Kind: definition. -/
def blockAt (H : c.Holds ⊥ f n) (i : ℕ) (hi : i ≤ n) : BlockComplex F where
  m0 := m0
  m1 := m1 + 4 * i
  m2 := m2
  d0 := c.blk0 i
  d1 := c.blk1 i
  d2 := c.blk2 i
  d1_d0 := (c.cx_of_holds H i hi).1
  d2_d1 := (c.cx_of_holds H i hi).2

/-- **The cone model of step `i`** (tex 4185–4193, 5398–5424): the pre-cancellation complex with
old part the model of `T_i`, new summands `N`, `Y = 0`, `T = 0` and the blocks `Q_i`, `B_i`,
`V_i`, for `i < n`. Kind: definition. -/
def coneAt (H : c.Holds ⊥ f n) (i : ℕ) (hi : i < n) : FullPreComplex F where
  m0 := m0
  m1 := m1 + 4 * i
  m2 := m2
  N := NS
  c0 := c.blk0 i
  Y := 0
  P := c.blk1 i
  Q := c.Q i
  T := 0
  B := c.B i
  U := c.blk2 i
  V := c.V i
  c1_c0 := by
    rw [fromBlocks_mul_fromRows, (c.cx_of_holds H i hi.le).1]
    simp
  c2_c1 := by
    have hQVB : c.blk2 i * c.Q i + c.V i * c.B i = 0 :=
      Matrix.ext fun a b => Ideal.mem_bot.mp (H.hQVB i hi a b)
    rw [fromCols_mul_fromBlocks, (c.cx_of_holds H i hi.le).2, hQVB]
    simp

/-! ### Cycles and closed functionals -/

/-- **The primitive class of `T_i` is a cycle of its model** (tex 4185–4193), for `i ≤ n`: for
`i = 0` by hypothesis, for `i + 1` the re-indexed relaxed class of step `i`. Kind: PROVED. -/
theorem blk1_mulVec_zP (H : c.Holds ⊥ f n) : ∀ i ≤ n, c.blk1 i *ᵥ c.zP i = 0
  | 0, _ => funext fun a => Ideal.mem_bot.mp (H.hzP0 a)
  | i + 1, hi => by
    have hz : fromBlocks (c.blk1 i) (c.Q i) 0 (c.B i) *ᵥ c.z i = 0 :=
      funext fun a => Ideal.mem_bot.mp (H.hz i hi a)
    funext x
    change ∑ j, fromBlocks (c.blk1 i) (c.Q i) 0 (c.B i) ((chE2 m1 m2 i).symm x)
      ((chE1 m0 m1 i).symm j) * c.z i ((chE1 m0 m1 i).symm j) = 0
    rw [Equiv.sum_comp (chE1 m0 m1 i).symm
      (fun j => fromBlocks (c.blk1 i) (c.Q i) 0 (c.B i) ((chE2 m1 m2 i).symm x) j * c.z i j)]
    exact congrFun hz _

/-- **The primitive functional of `T_i` is closed on its model** (tex 4185–4193), for `i ≤ n`.
Kind: PROVED. -/
theorem lP_vecMul_blk1 (H : c.Holds ⊥ f n) : ∀ i ≤ n, c.lP i ᵥ* c.blk1 i = 0
  | 0, _ => funext fun a => Ideal.mem_bot.mp (H.hlP0 a)
  | i + 1, hi => by
    have hl : c.l i ᵥ* fromBlocks (c.blk1 i) (c.Q i) 0 (c.B i) = 0 :=
      funext fun a => Ideal.mem_bot.mp (H.hl i hi a)
    funext j
    change ∑ x, c.l i ((chE2 m1 m2 i).symm x) *
      fromBlocks (c.blk1 i) (c.Q i) 0 (c.B i) ((chE2 m1 m2 i).symm x) ((chE1 m0 m1 i).symm j) = 0
    rw [Equiv.sum_comp (chE2 m1 m2 i).symm
      (fun x => c.l i x * fromBlocks (c.blk1 i) (c.Q i) 0 (c.B i) x ((chE1 m0 m1 i).symm j))]
    exact congrFun hl _

/-- The primitive class is a cycle of `blockAt i` (tex 4185–4193). Kind: PROVED. -/
theorem blockAt_cycle (H : c.Holds ⊥ f n) (i : ℕ) (hi : i ≤ n) :
    (c.blockAt H i hi).toFour.d1 *ᵥ c.zP i = 0 :=
  c.blk1_mulVec_zP H i hi

/-- The primitive functional is closed on `blockAt i` (tex 4185–4193). Kind: PROVED. -/
theorem blockAt_closed (H : c.Holds ⊥ f n) (i : ℕ) (hi : i ≤ n) :
    c.lP i ᵥ* (c.blockAt H i hi).toFour.d1 = 0 :=
  c.lP_vecMul_blk1 H i hi

/-- The relaxed class of step `i` is a cycle of `coneAt i` (tex 4185–4193). Kind: PROVED. -/
theorem coneAt_cycle (H : c.Holds ⊥ f n) (i : ℕ) (hi : i < n) :
    (c.coneAt H i hi).toFour.d1 *ᵥ c.z i = 0 :=
  funext fun a => Ideal.mem_bot.mp (H.hz i hi a)

/-- The relaxed functional of step `i` is closed on `coneAt i` (tex 4185–4193).
Kind: PROVED. -/
theorem coneAt_closed (H : c.Holds ⊥ f n) (i : ℕ) (hi : i < n) :
    c.l i ᵥ* (c.coneAt H i hi).toFour.d1 = 0 :=
  funext fun a => Ideal.mem_bot.mp (H.hl i hi a)

/-! ### The coordinates -/

/-- **The relaxed coordinate of step `i`** (tex 4157–4194, 4185–4193): the Knudsen–Mumford
coordinate of the cone model at the relaxed class and functional. Kind: definition. -/
def vRel (H : c.Holds ⊥ f n) (i : ℕ) (hi : i < n) : F :=
  kmCoord (c.coneAt H i hi).toFour (c.z i) (c.l i) (c.coneAt_cycle H i hi)
    (c.coneAt_closed H i hi) (σFull m0 (m1 + 4 * i) m2 NS)

/-- **The primitive coordinate of step `i`** (tex 4157–4194, 4185–4193): the Knudsen–Mumford
coordinate of the model of `T_i` at the primitive class and functional. Kind: definition. -/
def vPrim (H : c.Holds ⊥ f n) (i : ℕ) (hi : i ≤ n) : F :=
  kmCoord (c.blockAt H i hi).toFour (c.zP i) (c.lP i) (c.blockAt_cycle H i hi)
    (c.blockAt_closed H i hi) (σBlock m0 (m1 + 4 * i) m2)

/-! ### The step -/

/-- The new block of step `i` is the two-place block (tex 4176–4184). Kind: PROVED. -/
theorem B_eq (H : c.Holds ⊥ f n) (i : ℕ) (hi : i < n) :
    c.B i = twoPlaceBlock (f.Fr i) (f.q i) (f.z i) (f.zi i) :=
  Matrix.ext fun a b => sub_eq_zero.mp (Ideal.mem_bot.mp (H.hB i hi a b))

/-- **The cancellation of the cone model of step `i` is the model of `T_i`** (tex 4185–4193,
5424–5425): `d¹ = P − Q B⁻¹ 0 = P`. Kind: PROVED. -/
theorem coneAt_cancel_toFour (H : c.Holds ⊥ f n) (i : ℕ) (hi : i < n)
    (hB : IsUnit (c.coneAt H i hi).B.det) :
    ((c.coneAt H i hi).cancel hB).toFour = (c.blockAt H i hi.le).toFour := by
  refine fourCx_eq_of rfl ?_ rfl
  change c.blk1 i - c.Q i * (c.B i)⁻¹ * (0 : Matrix NS (cD1 m0 m1 i) F) = c.blk1 i
  rw [Matrix.mul_zero, sub_zero]

/-- **Each step of the chain is a torsion-level step** (tex 4157–4194, 4185–4193): if the
two-place block of step `i < n` is invertible, then `KmStep` holds between the relaxed and the
primitive coordinates of step `i`. The relaxed class is `e_q • (z_P, 0)` plus the retained
boundary `d⁰ w_i` (`kmCoord_add_boundary`), the relaxed functional restricts to `e_q λ_P` up to the
coboundary `ν_i d²` (`kmStep_of_cob`), and the cancelled cone model is the model of `T_i`.
Kind: PROVED. -/
theorem kmStep (H : c.Holds ⊥ f n) (i : ℕ) (hi : i < n)
    (hU : IsUnit (twoPlaceBlock (f.Fr i) (f.q i) (f.z i) (f.zi i)).det) :
    KmStep (f.Fr i) (f.q i) (f.a i) (f.z i) (f.zi i) (c.vRel H i hi) (c.vPrim H i hi.le) := by
  have hB : IsUnit (c.coneAt H i hi).B.det := by
    change IsUnit (c.B i).det
    rw [c.B_eq H i hi]
    exact hU
  have hz := c.coneAt_cycle H i hi
  have hl := c.coneAt_closed H i hi
  have hz' : (c.coneAt H i hi).toFour.d1 *ᵥ
      (pointFactor (f.a i) (f.z i) (f.zi i) • Sum.elim (c.zP i) (0 : NS → F)) = 0 := by
    have h1 := c.blk1_mulVec_zP H i hi.le
    change fromBlocks (c.blk1 i) (c.Q i) 0 (c.B i) *ᵥ
      (pointFactor (f.a i) (f.z i) (f.zi i) • Sum.elim (c.zP i) (0 : NS → F)) = 0
    rw [mulVec_smul, fromBlocks_mulVec, Sum.elim_comp_inl, Sum.elim_comp_inr, h1]
    simp
  have hd0 : (c.coneAt H i hi).toFour.d0 *ᵥ c.w i = Sum.elim (c.blk0 i *ᵥ c.w i) 0 := by
    change fromRows (c.blk0 i) (0 : Matrix NS (Fin m0) F) *ᵥ c.w i = _
    rw [fromRows_mulVec, zero_mulVec]
    rfl
  have hdec : c.z i = @HAdd.hAdd ((c.coneAt H i hi).D1 ⊕ (c.coneAt H i hi).N → F)
      ((c.coneAt H i hi).D1 ⊕ (c.coneAt H i hi).N → F)
      ((c.coneAt H i hi).D1 ⊕ (c.coneAt H i hi).N → F) _
      (pointFactor (f.a i) (f.z i) (f.zi i) • Sum.elim (c.zP i) (0 : NS → F))
      ((c.coneAt H i hi).toFour.d0 *ᵥ c.w i) := by
    rw [hd0]
    funext x
    rcases x with a | a
    · exact sub_eq_zero.mp (Ideal.mem_bot.mp (H.hnorm i hi a))
    · rw [Ideal.mem_bot.mp (H.hnormN i hi a)]
      change (0 : F) = pointFactor (f.a i) (f.z i) (f.zi i) * 0 + 0
      ring
  have hR : c.vRel H i hi = kmCoord (c.coneAt H i hi).toFour
      (pointFactor (f.a i) (f.z i) (f.zi i) • Sum.elim (c.zP i) (0 : NS → F)) (c.l i) hz' hl
      (σFull m0 (m1 + 4 * i) m2 NS) :=
    (kmCoord_congr _ hz (cycle_add_boundary _ hz' (c.w i)) hl hl hdec rfl _).trans
      (kmCoord_add_boundary _ hz' hl _ (c.w i))
  have h4 := c.coneAt_cancel_toFour H i hi hB
  have hzP : ((c.coneAt H i hi).cancel hB).toFour.d1 *ᵥ c.zP i = 0 := by
    change (c.blk1 i - c.Q i * (c.B i)⁻¹ * (0 : Matrix NS (cD1 m0 m1 i) F)) *ᵥ c.zP i = 0
    rw [Matrix.mul_zero, sub_zero]
    exact c.blk1_mulVec_zP H i hi.le
  have hlP : c.lP i ᵥ* ((c.coneAt H i hi).cancel hB).toFour.d1 = 0 := by
    change c.lP i ᵥ* (c.blk1 i - c.Q i * (c.B i)⁻¹ * (0 : Matrix NS (cD1 m0 m1 i) F)) = 0
    rw [Matrix.mul_zero, sub_zero]
    exact c.lP_vecMul_blk1 H i hi.le
  have hP : c.vPrim H i hi.le = kmCoord ((c.coneAt H i hi).cancel hB).toFour (c.zP i) (c.lP i)
      hzP hlP (σBlock m0 (m1 + 4 * i) m2) :=
    (kmCoord_cx_congr h4 hzP (c.blockAt_cycle H i hi.le) hlP (c.blockAt_closed H i hi.le)
      (σBlock m0 (m1 + 4 * i) m2)).symm
  refine kmStep_of_cob (c.coneAt H i hi) hB ⟨Equiv.refl _, ?_⟩ hz' hl hzP hlP (c.ν i) ?_
    (fun j => sub_eq_zero.mp (Ideal.mem_bot.mp (H.hfun i hi j))) hR hP
  · ext a b
    exact congrFun (congrFun (c.B_eq H i hi) a) b
  · funext a
    rfl

/-! ### The link between consecutive steps -/

/-- **The primitive coordinate of step `i + 1` is the relaxed coordinate of step `i` up to the
sign of the comparison of the cone bases** (tex 4185–4193): the model of `T_{i+1}` is the cone
model of step `i` re-indexed by `chE1`, `chE2` (definitionally), the primitive class and
functional are the re-indexed relaxed ones, and the re-indexing (`kmCoord_reindexF`) and the
change of orientation (`kmCoord_orient`) give the sign `linkSign i`. Kind: PROVED. -/
theorem vPrim_succ (H : c.Holds ⊥ f n) (i : ℕ) (hi : i < n) :
    c.vPrim H (i + 1) (Nat.succ_le_of_lt hi) =
      ((linkSign m0 m1 m2 i : ℤ) : F) * c.vRel H i hi := by
  have h1 := kmCoord_orient (c.blockAt H (i + 1) (Nat.succ_le_of_lt hi)).toFour
    (c.blockAt_cycle H (i + 1) (Nat.succ_le_of_lt hi))
    (c.blockAt_closed H (i + 1) (Nat.succ_le_of_lt hi))
    (linkOrient m0 m1 m2 i) (σBlock m0 (m1 + 4 * (i + 1)) m2)
  have h2 := kmCoord_reindexF (c.coneAt H i hi).toFour (Equiv.refl _) (chE1 m0 m1 i)
    (chE2 m1 m2 i) (Equiv.refl _) (c.coneAt_cycle H i hi) (c.coneAt_closed H i hi)
    (σFull m0 (m1 + 4 * i) m2 NS)
  exact h1.trans (congrArg (fun t => ((linkSign m0 m1 m2 i : ℤ) : F) * t) h2)

/-! ### The values along the chain and (4.7) -/

/-- **The values along the chain** (tex 4185–4193): `v₀` is the primitive coordinate of
`T₀ = ∅`, `v_{i+1}` the relaxed coordinate of step `i` (for `i < n`; `0` beyond).
Kind: definition. -/
def chainV (H : c.Holds ⊥ f n) : ℕ → F
  | 0 => c.vPrim H 0 (Nat.zero_le n)
  | i + 1 => if hi : i < n then c.vRel H i hi else 0

/-- The first value is the primitive coordinate of `T₀` (tex 4185–4193).
Kind: PROVED (definitional). -/
theorem chainV_zero (H : c.Holds ⊥ f n) : c.chainV H 0 = c.vPrim H 0 (Nat.zero_le n) :=
  rfl

/-- The value after step `i < n` is the relaxed coordinate of step `i` (tex 4185–4193); in
particular `v n` is the relaxed coordinate of the last step when `n ≥ 1`. Kind: PROVED. -/
theorem chainV_succ (H : c.Holds ⊥ f n) (i : ℕ) (hi : i < n) :
    c.chainV H (i + 1) = c.vRel H i hi :=
  dite_eq_left hi

/-- **One coordinate per support, up to sign** (tex 4185–4193): the primitive coordinate of
step `i ≤ n` is `σ_i v_i`. Kind: PROVED. -/
theorem vPrim_eq_chainV (H : c.Holds ⊥ f n) :
    ∀ (i : ℕ) (hi : i ≤ n), c.vPrim H i hi = ((chainSign m0 m1 m2 i : ℤ) : F) * c.chainV H i
  | 0, _ => by
    change c.vPrim H 0 _ = (((1 : ℤˣ) : ℤ) : F) * c.vPrim H 0 (Nat.zero_le n)
    rw [Units.val_one, Int.cast_one, one_mul]
  | i + 1, hi => by
    rw [c.chainV_succ H i (Nat.lt_of_succ_le hi)]
    exact c.vPrim_succ H i (Nat.lt_of_succ_le hi)

/-- **(4.7) at step `i` of the chain** (tex 4157–4194, 4185–4193): if `q_i q_i⁻¹ = 1`,
`tr Fr_i = a_i`, `det Fr_i = q_i` and the two-place block of step `i < n` is invertible, then
`l_i v_{i+1} = e_i² q_i⁻⁴ σ_i v_i`. Here `ε_i = q_i⁻⁴`; the text's `ε_q` also contains unit-disk
determinants (tex 4189–4193), which this normalization absorbs; this is not a proof of the text's
unit step. Kind: PROVED (from `kmStep`, `KmStep.h47` and the link). -/
theorem chain_h47 (H : c.Holds ⊥ f n) (i : ℕ) (hi : i < n) (hq : f.q i * f.qi i = 1)
    (ha : (f.Fr i).trace = f.a i) (hd : (f.Fr i).det = f.q i)
    (hU : IsUnit (twoPlaceBlock (f.Fr i) (f.q i) (f.z i) (f.zi i)).det) :
    quotientFactor (f.Fr i) (f.qi i) (f.z i) (f.zi i) * c.chainV H (i + 1) =
      pointFactor (f.a i) (f.z i) (f.zi i) ^ 2 * f.qi i ^ 4 *
        ((chainSign m0 m1 m2 i : ℤ) : F) * c.chainV H i := by
  have h := (c.kmStep H i hi hU).h47 hq ha hd
  rw [c.vPrim_eq_chainV H i hi.le] at h
  rw [c.chainV_succ H i hi, h]
  ring

/-- **(4.7) along the chain** (tex 4157–4194, 4185–4193): values `v` and signs `σ` with
`σ 0 = 1`, `v 0` the primitive coordinate of `T₀`, `v (i+1)` the relaxed coordinate of step `i`,
and `l_i v_{i+1} = e_i² q_i⁻⁴ σ_i v_i` at every step `i < n` (`v = chainV`,
`σ = chainSign`). Kind: PROVED. -/
theorem exists_chain_h47 (H : c.Holds ⊥ f n) (hq : ∀ i < n, f.q i * f.qi i = 1)
    (ha : ∀ i < n, (f.Fr i).trace = f.a i) (hd : ∀ i < n, (f.Fr i).det = f.q i)
    (hU : ∀ i < n, IsUnit (twoPlaceBlock (f.Fr i) (f.q i) (f.z i) (f.zi i)).det) :
    ∃ (v : ℕ → F) (σ : ℕ → ℤˣ), σ 0 = 1 ∧ v 0 = c.vPrim H 0 (Nat.zero_le n) ∧
      (∀ (i : ℕ) (hi : i < n), v (i + 1) = c.vRel H i hi) ∧
      ∀ i < n, quotientFactor (f.Fr i) (f.qi i) (f.z i) (f.zi i) * v (i + 1) =
        pointFactor (f.a i) (f.z i) (f.zi i) ^ 2 * f.qi i ^ 4 * ((σ i : ℤ) : F) * v i :=
  ⟨c.chainV H, chainSign m0 m1 m2, rfl, rfl, fun i hi => c.chainV_succ H i hi,
    fun i hi => c.chain_h47 H i hi (hq i hi) (ha i hi) (hd i hi) (hU i hi)⟩

end ChainMat

end ZInQ.Manuscript.RC.Wiring
