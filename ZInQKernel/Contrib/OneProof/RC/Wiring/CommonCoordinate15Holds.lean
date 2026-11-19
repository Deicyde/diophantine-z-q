import ZInQKernel.Contrib.OneProof.RC.Wiring.CommonCoordinate15Chain

/-!
# The identities of the matrix data of a chain of switches, and lifts to `Λ`

Manuscript `diophantine_zq.tex`, Lemma `ex:arith-common-coordinate` (tex 4142–4194) in the
iterated mapping-cone bases (tex 4185–4193), at a finite coefficient stage of the inner limit
(tex 4385–4451).

* `CMStepHyps`: the inputs of the steps of a chain of switches — the norm identity with its
  retained boundary `z_{R,i} = e_i · i(z_i) + d b_i` (tex 4169–4170) and the functional relation
  up to a coboundary `λ_{R,i} ∘ i = e_i λ_i + μ_i ∘ d` (tex 4171–4172), at the point factors
  `e_i = a_i − z_i − z_i⁻¹`.
* **`toChainMat_holds`**: the matrix data `CMChainData.toChainMat` of the chain satisfy every
  identity of `ChainMat.Holds` exactly (modulo `⊥`): the models of `C_∅` and the cone models are
  complexes, the new blocks are the two-place blocks (from the bases of the two places,
  `toMatrix_twoSingA`), the classes are cycles and the functionals closed, and the two relations
  hold in model coordinates.
* `ChainMat.liftAlong`, `liftAlong_map`, **`holds_liftAlong_iff`**: entrywise lifts of matrix data
  along a surjective ring homomorphism; the lifts satisfy the identities modulo the kernel exactly
  when the data satisfy them. `stageLift`, **`stageLift_holds`**: at the stage `Λ ⧸ stageIdeal s`
  the lifts satisfy the identities modulo `stageIdeal s`, the hypothesis of round ten's
  `limit_holds`.

Kinds: definitions and PROVED.
-/

noncomputable section

namespace ZInQ.Manuscript.RC.Wiring

open Matrix ZInQ.Manuscript.RC.Limits ZInQ.Contrib.CloudB3RC53.PairedFunctional
open ZInQ.Contrib.CloudB3RC53.ClearingComplex
open ZInQ.Contrib.CloudB3RC53.CommonCoordinate (twoPlaceBlock)
open ZInQ.Manuscript.RC.Central (pointFactor)
open ZInQ.Manuscript.RC.Local (twoSingCx)

section Holds

variable {A : Type} [CommRing A] {ι : Type} [DecidableEq ι] {C : Finset ι → GCx A}
  {E : ∀ (T : Finset ι) (p : ι), SplitInclusion (C T) (C (insert p T))} {m0 m1 m2 : ℕ}
  {ps : ℕ → ι} {n : ℕ} (cd : CMChainData C E m0 m1 m2 ps n)

/-- **The inputs of the steps of a chain of switches** (tex 4157–4194, 4169–4172): for the steps
`i < n`, the norm identity with its retained boundary `b_i` and the functional relation up to the
coboundary of `μ_i`, at the point factors `e_i = a_i − z_i − z_i⁻¹`. Kind: definition. -/
structure CMStepHyps (a : ℕ → A) (bw : ∀ i, (C (insert (ps i) (chainT ps i))).X 0)
    (μ : ∀ i, (C (chainT ps i)).X 3 →ₗ[A] A) : Prop where
  /-- the norm identity `z_R = e · i(z) + d b` -/
  hnorm : ∀ i (h : i < n), cd.zR i = pointFactor (a i) (cd.z i) (cd.zi i) •
      (E (chainT ps i) (ps i)).i.f 1 1 rfl (cmState cd i h.le).z +
    (C (insert (ps i) (chainT ps i))).d 0 1 rfl (bw i)
  /-- the functional relation `λ_R ∘ i = e λ + μ ∘ d` -/
  hfun : ∀ i (h : i < n), cd.lamR i ∘ₗ (E (chainT ps i) (ps i)).i.f 2 2 rfl =
    pointFactor (a i) (cd.z i) (cd.zi i) • (cmState cd i h.le).lam +
      μ i ∘ₗ (C (chainT ps i)).d 2 3 rfl

variable (bw : ∀ i, (C (insert (ps i) (chainT ps i))).X 0) (μ : ∀ i, (C (chainT ps i)).X 3 →ₗ[A] A)

/-- The cone matrix of step `i` of the matrix data is the cone model of the state
(tex 4185–4193). Kind: PROVED. -/
theorem cone1_toChainMat (i : ℕ) (h : i < n) :
    (cd.toChainMat bw μ).cone1 i = (cmCone cd i h).toFour.d1 := by
  change fromBlocks ((cd.toChainMat bw μ).blk1 i) ((cd.toChainMat bw μ).Q i) 0
    ((cd.toChainMat bw μ).B i) = _
  obtain ⟨hQ, -, hB⟩ := toChainMat_QVB cd bw μ i h
  rw [blk1_eq cd bw μ i h.le, hQ, hB]
  rfl

/-- **The norm identity in the coordinates of the cone model** (tex 4169–4170): the model of
`z_{R,i}` is `e_i` times the model of `i(z_i)` plus the model of the boundary. Kind: PROVED. -/
theorem cone_norm (a : ℕ → A) (H : CMStepHyps cd a bw μ) (i : ℕ) (hi : i < n) :
    (cmConeRetract cd i hi).p.f 1 1 rfl (cd.zR i) =
      pointFactor (a i) (cd.z i) (cd.zi i) • (cmConeRetract cd i hi).p.f 1 1 rfl
          ((E (chainT ps i) (ps i)).i.f 1 1 rfl (cmState cd i hi.le).z) +
        (cmCone cd i hi).toGCx.d 0 1 rfl ((cmConeRetract cd i hi).p.f 0 0 rfl (bw i)) := by
  have h2 : (cmConeRetract cd i hi).p.f 1 1 rfl
      ((C (insert (ps i) (chainT ps i))).d 0 1 rfl (bw i)) =
      (cmCone cd i hi).toGCx.d 0 1 rfl ((cmConeRetract cd i hi).p.f 0 0 rfl (bw i)) :=
    GRetract.p_d _ 0 1 rfl _
  rw [← h2, ← map_smul, ← map_add]
  exact congrArg _ (H.hnorm i hi)

/-- **The matrix data of a chain of switches satisfy all the identities exactly**
(tex 4142–4194, 4185–4193): given the inputs of the steps `i < n` and Frobenius data `f` agreeing
with the chain's at those steps (`Fr`, `q`, `z`, `z⁻¹`, and the traces `a`), the matrix data hold
modulo `⊥`. Kind: PROVED. -/
theorem toChainMat_holds (a : ℕ → A) (H : CMStepHyps cd a bw μ) (f : FrobSeq A)
    (hFr : ∀ i < n, f.Fr i = cd.Fr i) (hq : ∀ i < n, f.q i = (cd.q i : A))
    (hz : ∀ i < n, f.z i = cd.z i) (hzi : ∀ i < n, f.zi i = cd.zi i)
    (ha : ∀ i < n, f.a i = a i) :
    (cd.toChainMat bw μ).Holds ⊥ f n := by
  refine ⟨fun r t => ?_, fun r t => ?_, fun i hi r t => ?_, fun i hi r t => ?_, fun r => ?_,
    fun r => ?_, fun i hi r => ?_, fun i hi r => ?_, fun i hi r => ?_, fun i hi r => ?_,
    fun i hi r => ?_⟩
  · rw [Ideal.mem_bot]
    change (cd.st0.d1 * cd.st0.d0) r t = 0
    rw [cd.st0.h10]
    rfl
  · rw [Ideal.mem_bot]
    change (cd.st0.d2 * cd.st0.d1) r t = 0
    rw [cd.st0.h21]
    rfl
  · obtain ⟨hQ, hV, hB⟩ := toChainMat_QVB cd bw μ i hi
    rw [Ideal.mem_bot, blk2_eq cd bw μ i hi.le, hQ, hV, hB]
    change ((cmCone cd i hi).U * (cmCone cd i hi).Q + (cmCone cd i hi).V * (cmCone cd i hi).B)
      r t = 0
    rw [(cmCone cd i hi).UQ_VB]
    rfl
  · obtain ⟨-, -, hB⟩ := toChainMat_QVB cd bw μ i hi
    rw [Ideal.mem_bot, hFr i hi, hq i hi, hz i hi, hzi i hi, sub_eq_zero, hB]
    rw [relModelA_B, toMatrix_twoSingA]
  · exact Ideal.mem_bot.2 (congrFun (retract_p_cycle cd.st0.R (rfl : (1 : ℤ) + 1 = 2)
      cd.st0.hz) r)
  · exact Ideal.mem_bot.2 (congrFun (funVec_vecMul_eq_zero (ι := cD2 m1 m2 0) _ cd.st0.d1
      (retract_closed_comp_i cd.st0.R (rfl : (1 : ℤ) + 1 = 2) cd.st0.lam cd.st0.hlam)) r)
  · rw [Ideal.mem_bot, cone1_toChainMat cd bw μ i hi, (toChainMat_zlwν cd bw μ i hi).1]
    exact congrFun (retract_p_cycle (cmConeRetract cd i hi) (rfl : (1 : ℤ) + 1 = 2)
      (cd.hzR i)) r
  · rw [Ideal.mem_bot, cone1_toChainMat cd bw μ i hi, (toChainMat_zlwν cd bw μ i hi).2.1]
    exact congrFun (funVec_vecMul_eq_zero (ι := cD2 m1 m2 i ⊕ NS) _ (cmCone cd i hi).toFour.d1
      (retract_closed_comp_i (cmConeRetract cd i hi) (rfl : (1 : ℤ) + 1 = 2) (cd.lamR i)
        (cd.hlamR i))) r
  · have hp := cone_norm cd bw μ a H i hi
    rw [Ideal.mem_bot, sub_eq_zero, ha i hi, hz i hi, hzi i hi, zP_eq cd bw μ i hi.le,
      blk0_eq cd bw μ i hi.le, (toChainMat_zlwν cd bw μ i hi).1,
      (toChainMat_zlwν cd bw μ i hi).2.2.1]
    change (cmConeRetract cd i hi).p.f 1 1 rfl (cd.zR i) (Sum.inl r) = _
    rw [hp, relRetractA_p_i_one]
    change (pointFactor (a i) (cd.z i) (cd.zi i) •
        Sum.elim (α := cD1 m0 m1 i) ((cmState cd i hi.le).R.p.f 1 1 rfl (cmState cd i hi.le).z)
          (0 : NS → A) +
      fromRows (cmState cd i hi.le).d0 (0 : Matrix NS (Fin m0) A) *ᵥ
        ((cmConeRetract cd i hi).p.f 0 0 rfl (bw i))) (Sum.inl r) = _
    rfl
  · have hp := cone_norm cd bw μ a H i hi
    rw [Ideal.mem_bot, (toChainMat_zlwν cd bw μ i hi).1]
    change (cmConeRetract cd i hi).p.f 1 1 rfl (cd.zR i) (Sum.inr r) = 0
    rw [hp, relRetractA_p_i_one]
    change pointFactor (a i) (cd.z i) (cd.zi i) * (0 : A) +
      (0 : Fin m0 → A) ⬝ᵥ ((cmConeRetract cd i hi).p.f 0 0 rfl (bw i)) = 0
    rw [mul_zero, zero_add]
    exact zero_dotProduct _
  · rw [Ideal.mem_bot, sub_eq_zero, ha i hi, hz i hi, hzi i hi, lP_eq cd bw μ i hi.le,
      blk2_eq cd bw μ i hi.le, (toChainMat_zlwν cd bw μ i hi).2.1,
      (toChainMat_zlwν cd bw μ i hi).2.2.2]
    have h0 : funVec (ι := cD2 m1 m2 i ⊕ NS)
        (cd.lamR i ∘ₗ (cmConeRetract cd i hi).i.f 2 2 rfl) (Sum.inl r) =
        funVec (ι := cD2 m1 m2 i) ((cd.lamR i ∘ₗ (E (chainT ps i) (ps i)).i.f 2 2 rfl) ∘ₗ
          (cmState cd i hi.le).R.i.f 2 2 rfl) r :=
      congrFun (funVec_relRetractA_inl (E (chainT ps i) (ps i)) (cmState cd i hi.le).R
        (cd.RQ i hi) (twoSingB1A (cd.Fr i) (cd.q i) (cd.z i) (cd.zi i))
        (twoSingB2A (cd.Fr i) (cd.q i) (cd.z i) (cd.zi i))
        (twoSing_subsingletonA (cd.Fr i) (cd.q i) (cd.z i) (cd.zi i)) (cd.lamR i)) r
    change funVec (ι := cD2 m1 m2 i ⊕ NS) (cd.lamR i ∘ₗ (cmConeRetract cd i hi).i.f 2 2 rfl)
      (Sum.inl r) = _
    rw [h0, H.hfun i hi]
    set y : (cmState cd i hi.le).D.toGCx.X 2 :=
      (Pi.single r (1 : A) : cD2 m1 m2 i → A) with hy
    change (pointFactor (a i) (cd.z i) (cd.zi i) • (cmState cd i hi.le).lam +
        μ i ∘ₗ (C (chainT ps i)).d 2 3 rfl) ((cmState cd i hi.le).R.i.f 2 2 rfl y) =
      pointFactor (a i) (cd.z i) (cd.zi i) *
        (cmState cd i hi.le).lam ((cmState cd i hi.le).R.i.f 2 2 rfl y) + _
    rw [LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul, LinearMap.comp_apply,
      ← GRetract.i_d (cmState cd i hi.le).R 2 3 rfl y]
    congr 1
    have e1 := funVec_dotProduct (ι := Fin m2) (μ i ∘ₗ (cmState cd i hi.le).R.i.f 3 3 rfl)
      ((cmState cd i hi.le).d2 *ᵥ (Pi.single r (1 : A) : cD2 m1 m2 i → A))
    rw [dotProduct_mulVec, dotProduct_single, mul_one] at e1
    exact e1

end Holds

/-! ### Lifts along a surjective ring homomorphism -/

namespace ChainMat

variable {R A : Type} [CommRing R] [CommRing A] {m0 m1 m2 : ℕ}

/-- **The entrywise lift of matrix data along a surjective ring homomorphism** (tex 4385–4451:
the stage data lifted to `Λ`, entrywise by chosen preimages). Kind: definition. -/
def liftAlong (π : R →+* A) (hπ : Function.Surjective π) (c : ChainMat A m0 m1 m2) :
    ChainMat R m0 m1 m2 where
  d0 := c.d0.map (Function.surjInv hπ)
  d1 := c.d1.map (Function.surjInv hπ)
  d2 := c.d2.map (Function.surjInv hπ)
  Q i := (c.Q i).map (Function.surjInv hπ)
  V i := (c.V i).map (Function.surjInv hπ)
  B i := (c.B i).map (Function.surjInv hπ)
  zP0 := Function.surjInv hπ ∘ c.zP0
  lP0 := Function.surjInv hπ ∘ c.lP0
  z i := Function.surjInv hπ ∘ c.z i
  l i := Function.surjInv hπ ∘ c.l i
  w i := Function.surjInv hπ ∘ c.w i
  ν i := Function.surjInv hπ ∘ c.ν i

/-- The lift specializes to the data (tex 4385–4451). Kind: PROVED. -/
theorem liftAlong_map (π : R →+* A) (hπ : Function.Surjective π) (c : ChainMat A m0 m1 m2) :
    (c.liftAlong π hπ).map π = c := by
  have e : ∀ x, π (Function.surjInv hπ x) = x := Function.surjInv_eq hπ
  have hM : ∀ {m n : Type} (M : Matrix m n A), (M.map (Function.surjInv hπ)).map π = M :=
    fun M => by
      ext a b
      exact e (M a b)
  have hv : ∀ {m : Type} (v : m → A), (π : R → A) ∘ (Function.surjInv hπ ∘ v) = v :=
    fun v => by
      funext a
      exact e (v a)
  obtain ⟨d0, d1, d2, Q, V, B, zP0, lP0, z, l, w, ν⟩ := c
  simp only [ChainMat.map, liftAlong, hM, hv]

/-- **The lifts satisfy the identities modulo the kernel exactly when the data satisfy them**
(tex 4385–4451). Kind: PROVED. -/
theorem holds_liftAlong_iff (π : R →+* A) (hπ : Function.Surjective π)
    (c : ChainMat A m0 m1 m2) (f : FrobSeq R) (n : ℕ) :
    (c.liftAlong π hπ).Holds (RingHom.ker π) f n ↔ c.Holds ⊥ (f.map π) n := by
  have h := holds_map_iff (c.liftAlong π hπ) π ⊥ f n
  rw [liftAlong_map] at h
  rw [h, RingHom.ker_eq_comap_bot]

end ChainMat

/-- **The lift of stage matrix data to `Λ`** (tex 4385–4451): matrix data over the stage
`Λ ⧸ stageIdeal s`, lifted entrywise. Kind: definition. -/
def stageLift {m0 m1 m2 : ℕ} (s : ℕ) (c : ChainMat (LamI ⧸ stageIdeal s) m0 m1 m2) :
    ChainMat LamI m0 m1 m2 :=
  c.liftAlong (Ideal.Quotient.mk (stageIdeal s)) Ideal.Quotient.mk_surjective

/-- **Stage data satisfying the identities lift to data satisfying them modulo `stageIdeal s`**
(tex 4385–4451): the hypothesis of `limit_holds`. Kind: PROVED. -/
theorem stageLift_holds {m0 m1 m2 : ℕ} (s : ℕ) (c : ChainMat (LamI ⧸ stageIdeal s) m0 m1 m2)
    (f : FrobSeq LamI) (n : ℕ) (h : c.Holds ⊥ (f.map (Ideal.Quotient.mk (stageIdeal s))) n) :
    (stageLift s c).Holds (stageIdeal s) f n := by
  have e := (ChainMat.holds_liftAlong_iff (Ideal.Quotient.mk (stageIdeal s))
    Ideal.Quotient.mk_surjective c f n).2 h
  rwa [Ideal.mk_ker] at e

end ZInQ.Manuscript.RC.Wiring
