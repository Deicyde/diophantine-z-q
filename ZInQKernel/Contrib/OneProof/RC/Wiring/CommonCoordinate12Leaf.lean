import ZInQKernel.Contrib.OneProof.RC.Wiring.CommonCoordinate12Cob
import ZInQKernel.Contrib.OneProof.RC.Wiring.CommonCoordinate10Leaf
import ZInQKernel.Contrib.OneProof.RC.Wiring.CommonCoordinate12Values

/-!
# The common-coordinate leaf along a chain of relaxations

Manuscript `diophantine_zq.tex`, Lemma `ex:arith-common-coordinate` (tex 4142–4194): the
coordinates are taken "in the original integral determinant bases" (tex 4185–4193), which are the
iterated mapping-cone bases (round seven: minimal-model coordinates absorb `det B = q⁴ l_q`). So the
coordinate of a support is defined along a chain of relaxations `∅ = T₀ ⊂ T₁ ⊂ ⋯ ⊂ T_n = U_x`,
`T_{i+1} = T_i ∪ {p_i}`, adding the unused primes one at a time: the primitive model of each step
after the first is the re-indexed cone model of the previous relaxed complex
(`SupportTriangle.next`), and the primitive classes are the previous relaxed classes.

* `TriangleChain F` (any field: a finite coefficient stage, or `Frac Λ`): `n` support triangles,
  each after the first the next step of the previous one, each a `KmStep`; `TriangleChain.h47`:
  (4.7) between consecutive supports with the signs of the comparison of the cone bases;
  `TriangleChain.prod_h47`: the multi-prime (4.7) along the chain.
* `StepInputsAt C Fam x p S`: the inputs of one step at the leaf's values: the new block (`hBe`),
  the norm identity with its retained boundary (`hzR`), and the functional relation ON COCYCLES
  (`hnat`, what the retained pairing gives); `StepInputsAt.kmStep`, `StepInputsAt.h47`: the step
  is a `KmStep`, hence (4.7) at the step, for any model of the primitive complex
  (`SupportTriangle.kmStep_of_natural`).
* **`CommonCoordinateChainST C D Fam x`**: the leaf along one chain: an enumeration `ps` of the
  unused primes, the triangles `S i` of the steps, each step after the first the next step of the
  previous one (`hlink : S (i + 1) = nd.tri` for next data `nd`), the inputs of every step, and
  the primitive and corrected expansions at the two ends.
* `chainV`, `chainSign`: the coordinates of the supports along the chain (`chainV 0` the
  primitive coordinate, `chainV (i + 1)` the relaxed coordinate of step `i`) and the signs of the
  comparison of the cone bases; **`chain_h47`**: (4.7) between consecutive supports,
  `l_{p_i} v_{i+1} = e_{p_i}² p_i⁻⁴ σ_i v_i`; `chain_primCoord`: the primitive coordinate of step
  `i` is `σ_i v_i` (one coordinate per support, up to sign: `NextData.primCoord_tri`).
* **`CommonCoordinateChainST.toLF`**, **`commonCoordinateInputsNF_of_chain`**,
  **`commonCoordinateTarget_of_chain`**: the chain form gives the current leaf
  `CommonCoordinateInputsNF`, hence (4.7) (`CommonCoordinateTarget`), through the values of the
  chain (`ChainValues.toLF`): the leaf's coordinates of `∅` and of `U_x` are the chain's; those of
  the intermediate supports are the product-formula values (the leaf's step content is exactly
  (4.7) at the step, `supportTriangleAt_iff_h47`).

Kinds: definitions and PROVED.
-/

noncomputable section

namespace ZInQ.Manuscript.RC.Wiring

open Matrix ZInQ.Manuscript ZInQ.Manuscript.RC ZInQ.Manuscript.RC.Central
  ZInQ.Manuscript.RC.Uniform ZInQ.Contrib.CloudB3RC53 ZInQ.Contrib.CloudB3RC53.CommonCoordinate
open ZInQ.Manuscript.RC.TateWiring (FrobeniusTrace)

/-! ### Chains of support triangles over any field -/

section Generic

variable {F : Type} [Field F]

/-- **A chain of relaxations over a field** (tex 4185–4193): `n` support triangles, each after the
first the next step of the previous one, with the Frobenius data of each step and each step a
`KmStep`. At a finite coefficient stage the first step is the genuine step at the two places
(`kmStep_genuine`) and the later ones come from `kmStep_next_of_natural`. Kind: definition
(data). -/
structure TriangleChain (F : Type) [Field F] : Type 1 where
  /-- the number of steps -/
  n : ℕ
  /-- the support triangle of step `i` -/
  S : ℕ → SupportTriangle F
  /-- each later step is the next step of the previous one -/
  hlink : ∀ i, i + 1 < n → ∃ nd : NextData (S i), S (i + 1) = nd.tri
  /-- the Frobenius matrix of step `i` -/
  Fr : ℕ → Matrix (Fin 2) (Fin 2) F
  /-- the residue cardinality of step `i` and its inverse -/
  q : ℕ → F
  /-- the inverse of `q` -/
  qi : ℕ → F
  /-- the trace of Frobenius of step `i` -/
  a : ℕ → F
  /-- the point of step `i` and its inverse -/
  z : ℕ → F
  /-- the inverse point -/
  zi : ℕ → F
  /-- `q q⁻¹ = 1` -/
  hq : ∀ i < n, q i * qi i = 1
  /-- `tr Fr = a` -/
  ha : ∀ i < n, (Fr i).trace = a i
  /-- `det Fr = q` -/
  hd : ∀ i < n, (Fr i).det = q i
  /-- each step is a torsion-level step -/
  hkm : ∀ i < n, KmStep (Fr i) (q i) (a i) (z i) (zi i) (S i).relCoord (S i).primCoord

namespace TriangleChain

variable (H : TriangleChain F)

/-- **The comparison of the cone bases is a sign** along the chain (tex 4185–4193).
Kind: PROVED. -/
theorem link (i : ℕ) (hi : i + 1 < H.n) :
    ∃ ε : ℤˣ, (H.S (i + 1)).primCoord = ((ε : ℤ) : F) * (H.S i).relCoord := by
  obtain ⟨nd, hnd⟩ := H.hlink i hi
  rw [hnd]
  exact nd.primCoord_tri

/-- The signs of the comparison of the cone bases along the chain (tex 4185–4193).
Kind: definition. -/
def sign : ℕ → ℤˣ
  | 0 => 1
  | i + 1 => if hi : i + 1 < H.n then Classical.choose (H.link i hi) else 1

/-- The coordinate of the support `T_i` along the chain: the primitive coordinate of the first
step, then the relaxed coordinates (tex 4185–4193). Kind: definition. -/
def v : ℕ → F
  | 0 => (H.S 0).primCoord
  | i + 1 => (H.S i).relCoord

/-- **One coordinate per support, up to sign** (tex 4185–4193). Kind: PROVED. -/
theorem primCoord_eq (i : ℕ) (hi : i < H.n) :
    (H.S i).primCoord = ((H.sign i : ℤ) : F) * H.v i := by
  match i, hi with
  | 0, _ =>
    change (H.S 0).primCoord = (((1 : ℤˣ) : ℤ) : F) * (H.S 0).primCoord
    simp
  | j + 1, hi =>
    change (H.S (j + 1)).primCoord = (((if hj : j + 1 < H.n then
      Classical.choose (H.link j hj) else 1 : ℤˣ) : ℤ) : F) * (H.S j).relCoord
    rw [dite_eq_left hi]
    exact Classical.choose_spec (H.link j hi)

/-- **(4.7) between consecutive supports** (tex 4166–4193):
`l_i v_{i+1} = e_i² q_i⁻⁴ σ_i v_i`. Kind: PROVED. -/
theorem h47 (i : ℕ) (hi : i < H.n) :
    quotientFactor (H.Fr i) (H.qi i) (H.z i) (H.zi i) * H.v (i + 1) =
      pointFactor (H.a i) (H.z i) (H.zi i) ^ 2 * H.qi i ^ 4 * ((H.sign i : ℤ) : F) * H.v i := by
  have h := (H.hkm i hi).h47 (H.hq i hi) (H.ha i hi) (H.hd i hi)
  rw [H.primCoord_eq i hi] at h
  change _ * (H.S i).relCoord = _
  rw [h]
  ring

/-- **The multi-prime (4.7) along the chain** (tex 4166–4193, 4222):
`(∏ l_i) v_n = (∏ σ_i e_i² q_i⁻⁴) v_0`. Kind: PROVED. -/
theorem prod_h47 :
    (∏ i ∈ Finset.range H.n, quotientFactor (H.Fr i) (H.qi i) (H.z i) (H.zi i)) * H.v H.n =
      (∏ i ∈ Finset.range H.n, pointFactor (H.a i) (H.z i) (H.zi i) ^ 2 * H.qi i ^ 4 *
        ((H.sign i : ℤ) : F)) * H.v 0 := by
  suffices key : ∀ m ≤ H.n,
      (∏ i ∈ Finset.range m, quotientFactor (H.Fr i) (H.qi i) (H.z i) (H.zi i)) * H.v m =
        (∏ i ∈ Finset.range m, pointFactor (H.a i) (H.z i) (H.zi i) ^ 2 * H.qi i ^ 4 *
          ((H.sign i : ℤ) : F)) * H.v 0 from key H.n le_rfl
  intro m hm
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Finset.prod_range_succ, Finset.prod_range_succ]
    have e1 := H.h47 m (by omega)
    have e2 := ih (by omega)
    linear_combination
      (∏ i ∈ Finset.range m, quotientFactor (H.Fr i) (H.qi i) (H.z i) (H.zi i)) * e1 +
      (pointFactor (H.a m) (H.z m) (H.zi m) ^ 2 * H.qi m ^ 4 * ((H.sign m : ℤ) : F)) * e2

end TriangleChain

end Generic

section Leaf

variable {ℓ : ℕ} [(Ecurve ℓ).IsElliptic] (C : TateCoef (Ecurve ℓ)) (Fam : Family) (x : Addr Fam.b)

/-- **The inputs of one relaxation step at the leaf's values** (tex 4157–4194): for a support
triangle `S` over `F = Frac Λ` and an unused prime `p`: the new block is the two-place block of
`ρ_T(Fr_p)` at `z_p(x)` (`hBe`), the norm identity with its retained boundary (`hzR`), and the
functional relation on cocycles of `C_P` (`hnat`: `λ_R(i w) = e_p(x) λ_P(w)` for every cocycle
`w`, the retained pairing). Kind: definition. -/
def StepInputsAt (p : ℕ) (S : SupportTriangle FracLam) : Prop :=
  (∃ e : S.N ≃ Fin 2 ⊕ Fin 2, LinearMap.toMatrix S.b1 S.b2 (S.Q'.d 1 2 rfl) =
    (twoPlaceBlock ((frobMat C p).map zTwoToF) (p : FracLam) (lamToF (zAt Fam x p : Lambda))
      (lamToF ((zAt Fam x p)⁻¹ : Lambdaˣ))).submatrix e e) ∧
  (∃ b : S.CR.X 0, S.zR = eF ℓ Fam x p • S.E.i.f 1 1 rfl S.zP + S.CR.d 0 1 rfl b) ∧
  (∀ w : S.CP.X 2, S.CP.d 2 3 rfl w = 0 →
    S.lamR (S.E.i.f 2 2 rfl w) = eF ℓ Fam x p * S.lamP w)

/-- **The step from its inputs is a `KmStep`** at the coordinates of the models (tex 4157–4194),
for any model of the primitive complex; the units are PROVED. Kind: PROVED. -/
theorem StepInputsAt.kmStep {p : ℕ} {S : SupportTriangle FracLam} (hpr : p.Prime) (hp2 : p ≠ 2)
    (hgood : Nonvanishing.GoodAt (Ecurve ℓ) p) (h : StepInputsAt C Fam x p S) :
    KmStep ((frobMat C p).map zTwoToF) (p : FracLam) (apE ℓ p : FracLam)
      (lamToF (zAt Fam x p : Lambda)) (lamToF ((zAt Fam x p)⁻¹ : Lambdaˣ)) S.relCoord
      S.primCoord := by
  obtain ⟨hBe, hzR, hnat⟩ := h
  obtain ⟨ha, hd⟩ := leafFr_trace_det C hpr hp2 hgood
  have hp0 : (p : FracLam) ≠ 0 := natCast_ne_zero_F hpr.ne_zero
  rw [eF_eq_pointFactor] at hzR hnat
  exact S.kmStep_of_natural (mul_inv_cancel₀ hp0) ha hd
    (leaf_quotientFactor_ne_zero C Fam x hpr hp2 hgood) hBe hzR hnat

/-- **(4.7) at a step from its inputs** (tex 4157–4194, 4185–4188):
`l_p u_rel = e_p² p⁻⁴ u_prim`. Kind: PROVED. -/
theorem StepInputsAt.h47 {p : ℕ} {S : SupportTriangle FracLam} (hpr : p.Prime) (hp2 : p ≠ 2)
    (hgood : Nonvanishing.GoodAt (Ecurve ℓ) p) (h : StepInputsAt C Fam x p S) :
    quotientFactor ((frobMat C p).map zTwoToF) (p : FracLam)⁻¹ (lamToF (zAt Fam x p : Lambda))
        (lamToF ((zAt Fam x p)⁻¹ : Lambdaˣ)) * S.relCoord =
      pointFactor (apE ℓ p : FracLam) (lamToF (zAt Fam x p : Lambda))
        (lamToF ((zAt Fam x p)⁻¹ : Lambdaˣ)) ^ 2 * (p : FracLam)⁻¹ ^ 4 * S.primCoord := by
  obtain ⟨ha, hd⟩ := leafFr_trace_det C hpr hp2 hgood
  have hp0 : (p : FracLam) ≠ 0 := natCast_ne_zero_F hpr.ne_zero
  exact (h.kmStep C Fam x hpr hp2 hgood).h47 (mul_inv_cancel₀ hp0) ha hd

end Leaf

/-- **The common-coordinate data along one chain of relaxations** (tex 4142–4194, 4185–4193):
the graph primes are good odd primes; an enumeration `ps = [p₀, …, p_{n−1}]` of the unused primes
`U_x` (no repetition); the primitive coordinate `u0` (of the support `∅`) with its expansion; the
support triangles `S i` of the steps `T_i → T_i ∪ {p_i}` (`T_i = {p₀, …, p_{i−1}}`), the first
with primitive coordinate `u0`, each later one the next step of the previous one
(`hlink`: its primitive complex, model and classes are the previous relaxed complex, re-indexed
cone model and classes); the inputs of every step at the leaf's values; and the expansion of the
corrected coordinate at the last support `U_x`.

What still differs from the text (stated exactly): the triangles are data over `F = Frac Λ`; the
text's are the genuine Selmer complexes of the supports (lane RC32's `GenuineStepData.triangle`
at a finite coefficient stage; at `Frac Λ` after the inner limit), whose pinning needs (i) one
presentation of the Selmer data with all the places of `U_x` present from the start, the
condition at `p_i` switched from unramified to full at step `i` (so that the relaxed complex of
step `i` is literally the primitive complex of step `i + 1`); (ii) the inner limit from the finite
stages to `Frac Λ`; and, for the step inputs, (iii) the (H20) coefficient push of the norm
identity to the stage, the localization inputs of the strict lifts, lane RC30's `q`-components,
and lane RC31's literature statements `TameCochainQuasiIso`, `IwasawaGenerators`; (iv) at the
first step, a model of `C_∅` (the minimal model when `dim Hⁿ(C_∅) = (0, 1, 1, 0)`).
Kind: definition (data). -/
structure CommonCoordinateChainST {ℓ : ℕ} [(Ecurve ℓ).IsElliptic] (C : TateCoef (Ecurve ℓ))
    (D : RCData ℓ) (Fam : Family) (x : Addr Fam.b) : Type 1 where
  /-- the graph primes are odd primes (tex 2678–2680, 4143) -/
  hprime : ∀ q ∈ Fam.Q, q.Prime ∧ q ≠ 2
  /-- the graph primes are primes of good reduction of `E_ℓ` (tex 4143) -/
  hgood : ∀ q ∈ Fam.Q, Nonvanishing.GoodAt (Ecurve ℓ) q
  /-- the order in which the unused primes are relaxed -/
  ps : List ℕ
  /-- each unused prime is relaxed once -/
  hnd : ps.Nodup
  /-- the chain relaxes exactly the unused primes -/
  hps : ps.toFinset = unusedAt Fam x
  /-- the primitive coordinate (support `∅`) -/
  u0 : FracLam
  /-- the support triangle of step `i` -/
  S : ℕ → SupportTriangle FracLam
  /-- the first step starts at the primitive coordinate -/
  hS0 : 0 < ps.length → (S 0).primCoord = u0
  /-- each later step is the next step of the previous one (tex 4185–4193) -/
  hlink : ∀ i, i + 1 < ps.length → ∃ nd : NextData (S i), S (i + 1) = nd.tri
  /-- the inputs of every step at the leaf's values (tex 4157–4194) -/
  hstep : ∀ i (hi : i < ps.length), StepInputsAt C Fam x (ps.get ⟨i, hi⟩) (S i)
  /-- the primitive coordinate is regular with `t`-expansion `u_{prim,x}` (tex 4153) -/
  hprim : IsTExpansion u0 (D.uPrim Fam x)
  /-- the corrected coordinate at the last support has `t`-expansion `ũ_x` (tex 4150–4151) -/
  htilde : IsTExpansion (etaF ℓ Fam x *
    (if ps = [] then u0 else (S (ps.length - 1)).relCoord)) (D.uTilde Fam x)

namespace CommonCoordinateChainST

variable {ℓ : ℕ} [(Ecurve ℓ).IsElliptic] {C : TateCoef (Ecurve ℓ)} {D : RCData ℓ}
  {Fam : Family} {x : Addr Fam.b} (H : CommonCoordinateChainST C D Fam x)

/-- **The coordinate of the support `T_i` along the chain** (tex 4185–4193): `v 0 = u0`, and
`v (i + 1)` the relaxed coordinate of step `i`. Kind: definition. -/
def chainV : ℕ → FracLam
  | 0 => H.u0
  | i + 1 => (H.S i).relCoord

/-- **The comparison of the cone bases is a sign** (tex 4185–4193): the primitive coordinate of a
later step is `±` the relaxed coordinate of the previous step. Kind: PROVED. -/
theorem link_primCoord (i : ℕ) (hi : i + 1 < H.ps.length) :
    ∃ ε : ℤˣ, (H.S (i + 1)).primCoord = (ε : FracLam) * (H.S i).relCoord := by
  obtain ⟨nd, hnd⟩ := H.hlink i hi
  rw [hnd]
  exact nd.primCoord_tri

/-- **The signs of the chain** (tex 4185–4193): `σ 0 = 1`, `σ (i + 1)` the sign of the
comparison at step `i + 1` (`link_primCoord`). Kind: definition. -/
def chainSign : ℕ → ℤˣ
  | 0 => 1
  | i + 1 => if hi : i + 1 < H.ps.length then Classical.choose (H.link_primCoord i hi) else 1

/-- **One coordinate per support, up to sign** (tex 4185–4193): the primitive coordinate of step
`i` is `σ_i v_i`. Kind: PROVED. -/
theorem chain_primCoord (i : ℕ) (hi : i < H.ps.length) :
    (H.S i).primCoord = ((H.chainSign i : ℤ) : FracLam) * H.chainV i := by
  match i, hi with
  | 0, hi =>
    change (H.S 0).primCoord = (((1 : ℤˣ) : ℤ) : FracLam) * H.u0
    rw [H.hS0 hi]
    simp
  | j + 1, hi =>
    change (H.S (j + 1)).primCoord = (((if hj : j + 1 < H.ps.length then
      Classical.choose (H.link_primCoord j hj) else 1 : ℤˣ) : ℤ) : FracLam) * (H.S j).relCoord
    rw [dite_eq_left hi]
    exact Classical.choose_spec (H.link_primCoord j hi)

/-- **(4.7) between consecutive supports along the chain** (tex 4166–4193):
`l_{p_i} v_{i+1} = e_{p_i}² p_i⁻⁴ σ_i v_i`. Kind: PROVED. -/
theorem chain_h47 (i : ℕ) (hi : i < H.ps.length) :
    quotientFactor ((frobMat C (H.ps.get ⟨i, hi⟩)).map zTwoToF)
        ((H.ps.get ⟨i, hi⟩ : ℕ) : FracLam)⁻¹ (lamToF (zAt Fam x (H.ps.get ⟨i, hi⟩) : Lambda))
        (lamToF ((zAt Fam x (H.ps.get ⟨i, hi⟩))⁻¹ : Lambdaˣ)) * H.chainV (i + 1) =
      pointFactor (apE ℓ (H.ps.get ⟨i, hi⟩) : FracLam)
          (lamToF (zAt Fam x (H.ps.get ⟨i, hi⟩) : Lambda))
          (lamToF ((zAt Fam x (H.ps.get ⟨i, hi⟩))⁻¹ : Lambdaˣ)) ^ 2 *
        ((H.ps.get ⟨i, hi⟩ : ℕ) : FracLam)⁻¹ ^ 4 * (((H.chainSign i : ℤ) : FracLam)) *
          H.chainV i := by
  have hmem : H.ps.get ⟨i, hi⟩ ∈ unusedAt Fam x := by
    rw [← H.hps, List.mem_toFinset]
    exact List.get_mem _ _
  have hpQ : H.ps.get ⟨i, hi⟩ ∈ Fam.Q := (mem_unusedAt.mp hmem).1
  obtain ⟨hpr, hp2⟩ := H.hprime _ hpQ
  have h := (H.hstep i hi).h47 C Fam x hpr hp2 (H.hgood _ hpQ)
  rw [H.chain_primCoord i hi] at h
  change _ * (H.S i).relCoord = _
  rw [h]
  ring

/-- **The coordinate of the last support** (tex 4185–4193): `v n` is the relaxed coordinate of the
last step, or `u0` when there is no unused prime. Kind: PROVED. -/
theorem chainV_length :
    H.chainV H.ps.length = if H.ps = [] then H.u0 else (H.S (H.ps.length - 1)).relCoord := by
  by_cases h : H.ps = []
  · rw [ite_eq_left h, h]
    rfl
  · rw [ite_eq_right h]
    obtain ⟨n, hn⟩ : ∃ n, H.ps.length = n + 1 :=
      Nat.exists_eq_succ_of_ne_zero (fun h0 => h (List.length_eq_zero_iff.mp h0))
    rw [hn, Nat.add_sub_cancel]
    rfl

/-- **The chain's values** (tex 4142–4193): the coordinates `v i` and signs `σ i` of the chain
with (4.7) between consecutive supports (`chain_h47`). Kind: definition. -/
def toChainValues : ChainValues C D Fam x where
  hprime := H.hprime
  hgood := H.hgood
  ps := H.ps
  hnd := H.hnd
  hps := H.hps
  v := H.chainV
  σ := H.chainSign
  h47 := fun i hi => H.chain_h47 i hi
  hprim := H.hprim
  htilde := by
    rw [H.chainV_length]
    exact H.htilde

/-- **The current leaf's triangles from one chain of relaxations** (tex 4142–4194): through
`ChainValues.toLF`; the leaf's coordinates of `∅` and of `U_x` are the chain's primitive
coordinate and its last relaxed coordinate, those of the intermediate supports the
product-formula values (the leaf's step content is (4.7) at the step,
`supportTriangleAt_iff_h47`). Kind: definition. -/
def toLF : CommonCoordinateTrianglesLF C D Fam x :=
  H.toChainValues.toLF

end CommonCoordinateChainST

/-- **The common-coordinate inputs along chains of relaxations** (definition, tex 4142–4194):
`E_ℓ` elliptic, a coefficient datum, and at every address of every final family the data of one
chain of relaxations of the unused primes (`CommonCoordinateChainST`). -/
def CommonCoordinateInputsChain {ℓ : ℕ} (D : RCData ℓ) : Prop :=
  ∃ (hE : (Ecurve ℓ).IsElliptic) (C : TateCoef (Ecurve ℓ)),
    ∀ Co Ce : ℤ, ∀ F : Family, D.FinalFamilyAt Co Ce F → ∀ x : Addr F.b,
      Nonempty (@CommonCoordinateChainST ℓ hE C D F x)

/-- **The current leaf from chains of relaxations** (PROVED, tex 4142–4194). -/
theorem commonCoordinateInputsNF_of_chain {ℓ : ℕ} {D : RCData ℓ}
    (h : CommonCoordinateInputsChain D) : CommonCoordinateInputsNF D := by
  obtain ⟨hE, C, hT⟩ := h
  exact ⟨hE, C, fun Co Ce F hF x => (hT Co Ce F hF x).map fun t => t.toLF⟩

/-- **(4.7) from chains of relaxations** (PROVED, tex 4142–4194): `RCSteps.common_coordinate`. -/
theorem commonCoordinateTarget_of_chain {ℓ : ℕ} {D : RCData ℓ}
    (h : CommonCoordinateInputsChain D) : CommonCoordinateTarget D :=
  commonCoordinateTarget_of_NF (commonCoordinateInputsNF_of_chain h)


end ZInQ.Manuscript.RC.Wiring
