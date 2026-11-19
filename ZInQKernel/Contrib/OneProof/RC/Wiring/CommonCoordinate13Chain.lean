import ZInQKernel.Contrib.OneProof.RC.Wiring.CommonCoordinate12Leaf

/-!
# Chains of switches of one presentation

Manuscript `diophantine_zq.tex`, Lemma `ex:arith-common-coordinate` (tex 4142–4194, 4185–4193).

For a family of complexes `C T` indexed by the supports `T` (a single presentation of the support
complexes) and split inclusions `E T p : C T ⊂ C (insert p T)` (switching the condition at `p`),
and an order `p₀, p₁, …` of the primes, this file builds the chain of support triangles
`T_i → T_{i+1} = insert p_i T_i` by recursion on the STATE of the chain at `T_i`: the model of
`C T_i` with its retract, and the class and functional of `C T_i`. The state at `T_{i+1}` is the
re-indexed cone model of step `i` with the relaxed class and functional of step `i`, so each later
step is, by definition, the next step of the previous one (`chainTri_link`, `rfl`).

* `chainT ps`: `T₀ = ∅`, `T_{i+1} = insert p_i T_i`.
* `ChainState C T`, `ChainData C E ps`: the state at a support; the data of a chain (the initial
  state, the Frobenius data and quotient retractions onto the two singular blocks of every step,
  and the relaxed classes and functionals).
* `chainState`, **`chainTri`**: the states and the support triangles of the chain;
  **`chainTri_link`**: each later step is `NextData.tri` of the previous one, definitionally;
  `chainTri_CP`, `chainTri_CR`, `chainTri_E`: the complexes and the inclusions of the steps are
  `C T_i`, `C T_{i+1}`, `E T_i p_i`.
* `ChainHyps`: the arithmetic inputs of every step (the units, the norm identity, the functional
  relation on cocycles); **`chainTri_kmStep`**: every step is a `KmStep` (the new block is
  PROVED, `toMatrix_twoSing`); **`ChainData.toTriangleChain`**: the chain as a `TriangleChain`,
  hence (4.7) between consecutive supports and the multi-prime (4.7) along the chain
  (`TriangleChain.h47`, `TriangleChain.prod_h47`).

Kinds: definitions and PROVED.
-/

noncomputable section

namespace ZInQ.Manuscript.RC.Wiring

open Matrix ZInQ.Manuscript.RC.Limits ZInQ.Contrib.CloudB3RC53.PairedFunctional
open ZInQ.Contrib.CloudB3RC53.ClearingComplex ZInQ.Contrib.CloudB3RC53.CommonCoordinate
open ZInQ.Manuscript.RC.Central (pointFactor quotientFactor)
open ZInQ.Manuscript.RC.Local (twoSingCx)

variable {k : Type} [Field k] {ι : Type} [DecidableEq ι] (C : Finset ι → GCx k)
  (E : ∀ (T : Finset ι) (p : ι), SplitInclusion (C T) (C (insert p T)))

/-- **The supports of a chain** (tex 4185–4193): `T₀ = ∅`, `T_{i+1} = insert p_i T_i`.
Kind: definition. -/
def chainT (ps : ℕ → ι) : ℕ → Finset ι
  | 0 => ∅
  | i + 1 => insert (ps i) (chainT ps i)

/-- **Membership in the supports of a chain** (tex 4185–4193): `p ∈ T_i` iff `p = p_j` for some
`j < i`. Kind: PROVED. -/
theorem mem_chainT (ps : ℕ → ι) (i : ℕ) (p : ι) : p ∈ chainT ps i ↔ ∃ j < i, ps j = p := by
  induction i with
  | zero => simp [chainT]
  | succ i ih =>
    change p ∈ insert (ps i) (chainT ps i) ↔ _
    rw [Finset.mem_insert, ih]
    constructor
    · rintro (h | ⟨j, hj, h⟩)
      · exact ⟨i, Nat.lt_succ_self i, h.symm⟩
      · exact ⟨j, Nat.lt_succ_of_lt hj, h⟩
    · rintro ⟨j, hj, h⟩
      rcases Nat.lt_succ_iff_lt_or_eq.1 hj with hj | rfl
      · exact Or.inr ⟨j, hj, h⟩
      · exact Or.inl h.symm

/-- **The primes of a chain are new when they are relaxed** (tex 4185–4193): if the `p_j`,
`j ≤ i`, are distinct, then `p_i ∉ T_i`. Kind: PROVED. -/
theorem not_mem_chainT (ps : ℕ → ι) (i : ℕ) (h : ∀ j < i, ps j ≠ ps i) : ps i ∉ chainT ps i :=
  fun hm => by
    obtain ⟨j, hj, hji⟩ := (mem_chainT ps i (ps i)).1 hm
    exact h j hj hji

/-- **The state of a chain at a support** (tex 4185–4193): a block-complex model of `C T` with
its retract, and the class and functional of `C T`. Kind: definition (data). -/
structure ChainState (T : Finset ι) where
  /-- the model of `C T` -/
  D : BlockComplex k
  /-- the retract of `C T` onto its model -/
  R : GRetract (C T) D.toGCx
  /-- the class of `C T` -/
  z : (C T).X 1
  /-- `d z = 0` -/
  hz : (C T).d 1 2 rfl z = 0
  /-- the functional of `C T` -/
  lam : (C T).X 2 →ₗ[k] k
  /-- `λ ∘ d = 0` -/
  hlam : lam ∘ₗ (C T).d 1 2 rfl = 0

/-- **The data of a chain of switches** (tex 4157–4194, 4185–4193): the initial state at `∅`
(a model of `C ∅`, the primitive class and functional), and for every step `i` the Frobenius data
of `p_i`, a retraction of the quotient of `E T_i p_i` onto the two singular blocks, and the
relaxed class and functional of `C T_{i+1}`. Kind: definition (data). -/
structure ChainData (ps : ℕ → ι) where
  /-- the state at the empty support -/
  st0 : ChainState C ∅
  /-- the Frobenius matrix at step `i` -/
  Fr : ℕ → Matrix (Fin 2) (Fin 2) k
  /-- the residue cardinality at step `i` -/
  q : ℕ → ℕ
  /-- the point at step `i` -/
  z : ℕ → k
  /-- the inverse point at step `i` -/
  zi : ℕ → k
  /-- the retraction of the quotient of step `i` onto the two singular blocks -/
  RQ : ∀ i, GRetract (E (chainT ps i) (ps i)).quotientCx (twoSingCx (Fr i) (q i) (z i) (zi i))
  /-- the relaxed class of step `i` -/
  zR : ∀ i, (C (insert (ps i) (chainT ps i))).X 1
  /-- `d z_R = 0` -/
  hzR : ∀ i, (C (insert (ps i) (chainT ps i))).d 1 2 rfl (zR i) = 0
  /-- the relaxed functional of step `i` -/
  lamR : ∀ i, (C (insert (ps i) (chainT ps i))).X 2 →ₗ[k] k
  /-- `λ_R ∘ d = 0` -/
  hlamR : ∀ i, lamR i ∘ₗ (C (insert (ps i) (chainT ps i))).d 1 2 rfl = 0

variable {C E} {ps : ℕ → ι} (cd : ChainData C E ps)

/-- **The step triangle from a state** (tex 4157–4194): the support triangle of the switch
`E T_i p_i` with the state's model, class and functional as primitive data
(`SupportTriangle.ofTwoSing`). Kind: definition. -/
def stepTri (i : ℕ) (st : ChainState C (chainT ps i)) : SupportTriangle k :=
  SupportTriangle.ofTwoSing (cd.Fr i) (cd.q i) (cd.z i) (cd.zi i) (E (chainT ps i) (ps i)) st.D
    st.R (cd.RQ i) (cd.zR i) (cd.hzR i) st.z st.hz (cd.lamR i) (cd.hlamR i) st.lam st.hlam

/-- **The states of the chain** (tex 4185–4193): the initial state, then the re-indexed cone model
of each step with its relaxed class and functional. Kind: definition. -/
def chainState : (i : ℕ) → ChainState C (chainT ps i)
  | 0 => cd.st0
  | i + 1 =>
    { D := FullPreComplex.toBlock (stepTri cd i (chainState i)).model
      R := (stepTri cd i (chainState i)).nextModelRetract
      z := cd.zR i
      hz := cd.hzR i
      lam := cd.lamR i
      hlam := cd.hlamR i }

/-- **The support triangles of the chain** (tex 4157–4194, 4185–4193). Kind: definition. -/
def chainTri (i : ℕ) : SupportTriangle k :=
  stepTri cd i (chainState cd i)

/-- The primitive complex of step `i` is `C T_i` (tex 4185–4193). Kind: PROVED (definitional). -/
theorem chainTri_CP (i : ℕ) : (chainTri cd i).CP = C (chainT ps i) :=
  rfl

/-- The relaxed complex of step `i` is `C T_{i+1}` (tex 4185–4193). Kind: PROVED
(definitional). -/
theorem chainTri_CR (i : ℕ) : (chainTri cd i).CR = C (chainT ps (i + 1)) :=
  rfl

/-- The inclusion of step `i` is the switch `E T_i p_i` (tex 4185–4193). Kind: PROVED
(definitional). -/
theorem chainTri_E (i : ℕ) : HEq (chainTri cd i).E (E (chainT ps i) (ps i)) :=
  HEq.rfl

/-- **The next data of the chain** (tex 4185–4193): the switch at step `i + 1` with its quotient
retraction, bases and relaxed classes. Kind: definition. -/
def chainNext (i : ℕ) : NextData (chainTri cd i) where
  CR' := C (insert (ps (i + 1)) (chainT ps (i + 1)))
  E' := E (chainT ps (i + 1)) (ps (i + 1))
  Q'' := twoSingCx (cd.Fr (i + 1)) (cd.q (i + 1)) (cd.z (i + 1)) (cd.zi (i + 1))
  RQ' := cd.RQ (i + 1)
  hQ'' := twoSing_subsingleton (cd.Fr (i + 1)) (cd.q (i + 1)) (cd.z (i + 1)) (cd.zi (i + 1))
  N' := Fin 2 ⊕ Fin 2
  b1' := twoSingB1 (cd.Fr (i + 1)) (cd.q (i + 1)) (cd.z (i + 1)) (cd.zi (i + 1))
  b2' := twoSingB2 (cd.Fr (i + 1)) (cd.q (i + 1)) (cd.z (i + 1)) (cd.zi (i + 1))
  zR' := cd.zR (i + 1)
  hzR' := cd.hzR (i + 1)
  lamR' := cd.lamR (i + 1)
  hlamR' := cd.hlamR (i + 1)

/-- **Each later step of the chain is the next step of the previous one, definitionally**
(tex 4185–4193): its primitive complex, model, class and functional are the relaxed complex,
re-indexed cone model, class and functional of the previous step. Kind: PROVED (definitional). -/
theorem chainTri_link (i : ℕ) : chainTri cd (i + 1) = (chainNext cd i).tri :=
  rfl

/-- **The arithmetic inputs of the steps of a chain** (tex 4157–4194): for every step `i < n` the
units (`q q⁻¹ = 1`, `tr Fr = a`, `det Fr = q`, `l_q ≠ 0`), the norm identity with its retained
boundary, and the functional relation on cocycles of `C T_i` (the retained pairing).
Kind: definition (hypotheses). -/
structure ChainHyps (n : ℕ) where
  /-- the inverse of `q` at step `i` -/
  qi : ℕ → k
  /-- the trace of Frobenius at step `i` -/
  a : ℕ → k
  /-- `q q⁻¹ = 1` -/
  hq : ∀ i < n, (cd.q i : k) * qi i = 1
  /-- `tr Fr = a` -/
  ha : ∀ i < n, (cd.Fr i).trace = a i
  /-- `det Fr = q` -/
  hd : ∀ i < n, (cd.Fr i).det = cd.q i
  /-- `l_q ≠ 0` (an unused prime) -/
  hl : ∀ i < n, quotientFactor (cd.Fr i) (qi i) (cd.z i) (cd.zi i) ≠ 0
  /-- the norm identity with its retained boundary at step `i` -/
  hnorm : ∀ i < n, ∃ b : (C (insert (ps i) (chainT ps i))).X 0,
    cd.zR i = pointFactor (a i) (cd.z i) (cd.zi i) •
        (E (chainT ps i) (ps i)).i.f 1 1 rfl (chainState cd i).z +
      (C (insert (ps i) (chainT ps i))).d 0 1 rfl b
  /-- the functional relation on cocycles at step `i` (the retained pairing) -/
  hnat : ∀ i < n, ∀ w : (C (chainT ps i)).X 2, (C (chainT ps i)).d 2 3 rfl w = 0 →
    cd.lamR i ((E (chainT ps i) (ps i)).i.f 2 2 rfl w) =
      pointFactor (a i) (cd.z i) (cd.zi i) * (chainState cd i).lam w

/-- **Every step of the chain is a `KmStep`** (tex 4157–4194): the new block is the two-place
block (PROVED, `toMatrix_twoSing`), the norm identity and the functional relation on cocycles
are the inputs. Kind: PROVED. -/
theorem chainTri_kmStep {n : ℕ} (H : ChainHyps cd n) (i : ℕ) (hi : i < n) :
    KmStep (cd.Fr i) (cd.q i : k) (H.a i) (cd.z i) (cd.zi i) (chainTri cd i).relCoord
      (chainTri cd i).primCoord :=
  SupportTriangle.kmStep_of_natural (chainTri cd i) (H.hq i hi) (H.ha i hi) (H.hd i hi)
    (H.hl i hi)
    ⟨Equiv.refl _, (toMatrix_twoSing (cd.Fr i) (cd.q i) (cd.z i) (cd.zi i)).trans
      (submatrix_id_id _).symm⟩
    (H.hnorm i hi) (H.hnat i hi)

/-- **The chain as a `TriangleChain`** (tex 4166–4194): `n` steps, linked definitionally, each a
`KmStep`; hence (4.7) between consecutive supports (`TriangleChain.h47`) and along the chain
(`TriangleChain.prod_h47`). Kind: definition. -/
def ChainData.toTriangleChain {n : ℕ} (H : ChainHyps cd n) : TriangleChain k where
  n := n
  S := chainTri cd
  hlink i _ := ⟨chainNext cd i, chainTri_link cd i⟩
  Fr := cd.Fr
  q i := (cd.q i : k)
  qi := H.qi
  a := H.a
  z := cd.z
  zi := cd.zi
  hq := H.hq
  ha := H.ha
  hd := H.hd
  hkm := chainTri_kmStep cd H

/-- **(4.7) along a chain of switches of one presentation** (tex 4166–4193, 4222):
`(∏ l_i) v_n = (∏ σ_i e_i² q_i⁻⁴) v_0`, `v_0` the primitive coordinate at `∅` and `v_n` the
relaxed coordinate at `T_n`. Kind: PROVED. -/
theorem ChainData.prod_h47 {n : ℕ} (H : ChainHyps cd n) :
    (∏ i ∈ Finset.range n, quotientFactor (cd.Fr i) (H.qi i) (cd.z i) (cd.zi i)) *
        (cd.toTriangleChain H).v n =
      (∏ i ∈ Finset.range n, pointFactor (H.a i) (cd.z i) (cd.zi i) ^ 2 * H.qi i ^ 4 *
        (((cd.toTriangleChain H).sign i : ℤ) : k)) * (cd.toTriangleChain H).v 0 :=
  (cd.toTriangleChain H).prod_h47

end ZInQ.Manuscript.RC.Wiring
