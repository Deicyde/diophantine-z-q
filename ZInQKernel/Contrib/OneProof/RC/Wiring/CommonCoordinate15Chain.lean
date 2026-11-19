import ZInQKernel.Contrib.OneProof.RC.Wiring.CommonCoordinate15Ring
import ZInQKernel.Contrib.OneProof.RC.Wiring.CommonCoordinate14Leaf

/-!
# The matrix data of a chain of switches, over a coefficient ring

Manuscript `diophantine_zq.tex`, Lemma `ex:arith-common-coordinate` (tex 4142–4194) in the
iterated mapping-cone bases (tex 4185–4193), at a finite coefficient stage of the inner limit
(tex 4385–4451).

For a family of complexes `C T` over a commutative ring `A` (one presentation of the support
complexes) with switches `E T p : C T ⊂ C (insert p T)`, the chain of relaxations along an order
`p₀, p₁, …` is built by recursion on its STATE in the shapes of round ten's matrix data
`ChainMat`: the model of `C_{T_i}` is a block complex of shape `(m₀, m₁ + 4i, m₂)`, and the model
of `C_{T_{i+1}}` is the full-condition cone model of step `i` (`relModelA`) re-indexed by the
re-indexings `chE1`, `chE2` of `ChainMat`. The matrix data of the chain are then read off:

* `shapeBlock`, `CMState`: the block complex of the shape of step `i`; the state of the chain at a
  support (model, retract, class, functional).
* `coneOf`, `coneRetract`: the cone model of a switch at a state and the retract of the relaxed
  complex onto it (over the ring, with the bases of the two places).
* `cmNextD0`, `cmNextD1`, `cmNextD2`, `cmEquiv`, `cmEquiv_comm`, `cmNext`: the next state.
* `CMChainData`, `cmState`: the data of a chain of switches and its states.
* **`CMChainData.toChainMat`**: the matrix data of the chain; `blk0_eq`, `blk1_eq`, `blk2_eq`,
  `zP_eq`, `lP_eq`: the recursive models and primitive data of `ChainMat` are those of the states.
* `CMStepHyps`: the inputs of the steps — the norm identity with its retained boundary and the
  functional relation up to a coboundary, at the point factors `e_i = a_i − z_i − z_i⁻¹`;
  **`toChainMat_holds`**: the matrix data satisfy all the identities of `ChainMat.Holds` exactly
  (the cone models are complexes, the new block is the two-place block — PROVED from the bases
  of the two places, `toMatrix_twoSingA` — cycles and closed functionals, and the two relations).
* `ChainMat.liftAlong`, `liftAlong_map`, **`holds_liftAlong_iff`**: lifts of matrix data along a
  surjective ring homomorphism `Λ → A`; their identities modulo the kernel are the identities of
  the data.

Kinds: definitions and PROVED.
-/

noncomputable section

namespace ZInQ.Manuscript.RC.Wiring

open Matrix ZInQ.Manuscript.RC.Limits ZInQ.Contrib.CloudB3RC53.PairedFunctional
open ZInQ.Contrib.CloudB3RC53.ClearingComplex
open ZInQ.Contrib.CloudB3RC53.CommonCoordinate (twoPlaceBlock)
open ZInQ.Manuscript.RC.Central (pointFactor)
open ZInQ.Manuscript.RC.Local (twoSingCx)

/-! ### Shapes and states -/

section State

variable {A : Type} [CommRing A] (m0 m1 m2 : ℕ)

/-- **The block complex of the shape of step `i`** (tex 4185–4193): ranks `(m₀, m₁ + 4i, m₂)`.
Kind: definition. -/
def shapeBlock (i : ℕ) (d0 : Matrix (cD1 m0 m1 i) (Fin m0) A)
    (d1 : Matrix (cD2 m1 m2 i) (cD1 m0 m1 i) A) (d2 : Matrix (Fin m2) (cD2 m1 m2 i) A)
    (h10 : d1 * d0 = 0) (h21 : d2 * d1 = 0) : BlockComplex A where
  m0 := m0
  m1 := m1 + 4 * i
  m2 := m2
  d0 := d0
  d1 := d1
  d2 := d2
  d1_d0 := h10
  d2_d1 := h21

/-- **The state of the chain at a support** (tex 4185–4193): a model of `X = C_{T_i}` of the shape
of step `i` with its retract, and the class and functional of `X`. Kind: definition (data). -/
structure CMState (X : GCx A) (i : ℕ) where
  /-- the model in degrees `0 → 1` -/
  d0 : Matrix (cD1 m0 m1 i) (Fin m0) A
  /-- the model in degrees `1 → 2` -/
  d1 : Matrix (cD2 m1 m2 i) (cD1 m0 m1 i) A
  /-- the model in degrees `2 → 3` -/
  d2 : Matrix (Fin m2) (cD2 m1 m2 i) A
  /-- `d¹ d⁰ = 0` -/
  h10 : d1 * d0 = 0
  /-- `d² d¹ = 0` -/
  h21 : d2 * d1 = 0
  /-- the retract of `X` onto its model -/
  R : GRetract X (shapeBlock m0 m1 m2 i d0 d1 d2 h10 h21).toGCx
  /-- the class of `X` -/
  z : X.X 1
  /-- `d z = 0` -/
  hz : X.d 1 2 rfl z = 0
  /-- the functional of `X` -/
  lam : X.X 2 →ₗ[A] A
  /-- `λ ∘ d = 0` -/
  hlam : lam ∘ₗ X.d 1 2 rfl = 0

variable {m0 m1 m2}

/-- The model of a state (tex 4185–4193). Kind: definition. -/
abbrev CMState.D {X : GCx A} {i : ℕ} (s : CMState m0 m1 m2 X i) : BlockComplex A :=
  shapeBlock m0 m1 m2 i s.d0 s.d1 s.d2 s.h10 s.h21

variable {X Y : GCx A} (E : SplitInclusion X Y) {Fr : Matrix (Fin 2) (Fin 2) A} {q : ℕ}
  {z zi : A} (RQ : GRetract E.quotientCx (twoSingCx Fr q z zi)) {i : ℕ}
  (s : CMState m0 m1 m2 X i)

/-- **The cone model of a switch at a state** (tex 5398–5424): the full-condition model of the
relaxed complex on the model of the state, with the bases of the two places. Kind: definition. -/
abbrev coneOf : FullPreComplex A :=
  relModelA E s.R RQ (twoSingB1A Fr q z zi) (twoSingB2A Fr q z zi)

/-- **The retract of the relaxed complex onto the cone model** (tex 5398–5424, 4423–4437).
Kind: definition. -/
abbrev coneRetract : GRetract Y (coneOf E RQ s).toGCx :=
  relRetractA E s.R RQ (twoSingB1A Fr q z zi) (twoSingB2A Fr q z zi)
    (twoSing_subsingletonA Fr q z zi)

/-- The next model in degrees `0 → 1`: the cone model re-indexed (tex 4185–4193).
Kind: definition. -/
abbrev cmNextD0 : Matrix (cD1 m0 m1 (i + 1)) (Fin m0) A :=
  (coneOf E RQ s).toFour.d0.submatrix (chE1 m0 m1 i).symm id

/-- The next model in degrees `1 → 2` (tex 4185–4193). Kind: definition. -/
abbrev cmNextD1 : Matrix (cD2 m1 m2 (i + 1)) (cD1 m0 m1 (i + 1)) A :=
  (coneOf E RQ s).toFour.d1.submatrix (chE2 m1 m2 i).symm (chE1 m0 m1 i).symm

/-- The next model in degrees `2 → 3` (tex 4185–4193). Kind: definition. -/
abbrev cmNextD2 : Matrix (Fin m2) (cD2 m1 m2 (i + 1)) A :=
  (coneOf E RQ s).toFour.d2.submatrix id (chE2 m1 m2 i).symm

/-- The next model is a complex in degrees `0 → 2` (tex 4185–4193). Kind: PROVED. -/
theorem cmNext_h10 : cmNextD1 E RQ s * cmNextD0 E RQ s = 0 :=
  (submatrix_mul_equiv (coneOf E RQ s).toFour.d1 (coneOf E RQ s).toFour.d0
    (chE2 m1 m2 i).symm (chE1 m0 m1 i).symm id).trans
    (by rw [(coneOf E RQ s).toFour.d10]; rfl)

/-- The next model is a complex in degrees `1 → 3` (tex 4185–4193). Kind: PROVED. -/
theorem cmNext_h21 : cmNextD2 E RQ s * cmNextD1 E RQ s = 0 :=
  (submatrix_mul_equiv (coneOf E RQ s).toFour.d2 (coneOf E RQ s).toFour.d1
    id (chE2 m1 m2 i).symm (chE1 m0 m1 i).symm).trans
    (by rw [(coneOf E RQ s).toFour.d21]; rfl)

/-- **The next model is degreewise the cone model** (tex 4185–4193): `v ↦ v ∘ chE` in degrees one
and two, the identity elsewhere. Kind: definition. -/
def cmEquiv : (n : ℤ) → (shapeBlock m0 m1 m2 (i + 1) (cmNextD0 E RQ s) (cmNextD1 E RQ s)
    (cmNextD2 E RQ s) (cmNext_h10 E RQ s) (cmNext_h21 E RQ s)).toGCx.X n ≃ₗ[A]
    (coneOf E RQ s).toGCx.X n
  | 0 => LinearEquiv.refl A (Fin m0 → A)
  | 1 => LinearEquiv.funCongrLeft A A (chE1 m0 m1 i)
  | 2 => LinearEquiv.funCongrLeft A A (chE2 m1 m2 i)
  | 3 => LinearEquiv.refl A (Fin m2 → A)
  | Int.ofNat (_ + 4) => LinearEquiv.refl A (Empty → A)
  | Int.negSucc _ => LinearEquiv.refl A (Empty → A)

/-- The identification commutes with the differentials (tex 4185–4193). Kind: PROVED. -/
theorem cmEquiv_comm (a b : ℤ) (h : a + 1 = b)
    (y : (shapeBlock m0 m1 m2 (i + 1) (cmNextD0 E RQ s) (cmNextD1 E RQ s)
      (cmNextD2 E RQ s) (cmNext_h10 E RQ s) (cmNext_h21 E RQ s)).toGCx.X a) :
    (coneOf E RQ s).toGCx.d a b h (cmEquiv E RQ s a y) =
      cmEquiv E RQ s b ((shapeBlock m0 m1 m2 (i + 1) (cmNextD0 E RQ s) (cmNextD1 E RQ s)
        (cmNextD2 E RQ s) (cmNext_h10 E RQ s) (cmNext_h21 E RQ s)).toGCx.d a b h y) := by
  subst h
  match a with
  | 0 =>
    funext x
    exact (mulVec_submatrix_apply_equiv (coneOf E RQ s).toFour.d0 (chE1 m0 m1 i)
      (Equiv.refl _) (y : Fin m0 → A) x).symm
  | 1 =>
    funext x
    exact (mulVec_submatrix_apply_equiv (coneOf E RQ s).toFour.d1 (chE2 m1 m2 i)
      (chE1 m0 m1 i) (y : cD1 m0 m1 (i + 1) → A) x).symm
  | 2 =>
    funext x
    exact (mulVec_submatrix_apply_equiv (coneOf E RQ s).toFour.d2 (Equiv.refl _)
      (chE2 m1 m2 i) (y : cD2 m1 m2 (i + 1) → A) x).symm
  | 3 =>
    change (0 : Empty → A) = (0 : Empty → A)
    rfl
  | Int.ofNat (n + 4) =>
    obtain rfl : y = 0 := Subsingleton.elim (α := Empty → A) _ _
    simp only [map_zero]
  | Int.negSucc n =>
    obtain rfl : y = 0 := Subsingleton.elim (α := Empty → A) _ _
    simp only [map_zero]

/-- **The next state** (tex 4185–4193): the re-indexed cone model of the switch with the
transported retract, and the relaxed class and functional. Kind: definition. -/
def cmNext (zR : Y.X 1) (hzR : Y.d 1 2 rfl zR = 0) (lamR : Y.X 2 →ₗ[A] A)
    (hlamR : lamR ∘ₗ Y.d 1 2 rfl = 0) : CMState m0 m1 m2 Y (i + 1) where
  d0 := cmNextD0 E RQ s
  d1 := cmNextD1 E RQ s
  d2 := cmNextD2 E RQ s
  h10 := cmNext_h10 E RQ s
  h21 := cmNext_h21 E RQ s
  R := retractOfModelEquiv (coneRetract E RQ s) (cmEquiv E RQ s) (cmEquiv_comm E RQ s)
  z := zR
  hz := hzR
  lam := lamR
  hlam := hlamR

end State

/-! ### The chain -/

section Chain

variable {A : Type} [CommRing A] {ι : Type} [DecidableEq ι] {C : Finset ι → GCx A}
  {E : ∀ (T : Finset ι) (p : ι), SplitInclusion (C T) (C (insert p T))} {m0 m1 m2 : ℕ}
  {ps : ℕ → ι} {n : ℕ}

variable (C E m0 m1 m2 ps n) in
/-- **The data of a chain of `n` switches in the shapes of the matrix data** (tex 4157–4194,
4185–4193): the initial state at `∅` (a model of `C_∅` of ranks `(m₀, m₁, m₂)`, the primitive class
and functional), and for every step `i < n` the Frobenius data of `p_i`, a retraction of the
quotient of the switch onto the two singular blocks, and the relaxed class and functional of
`C_{T_{i+1}}`. Kind: definition (data). -/
structure CMChainData where
  /-- the state at the empty support -/
  st0 : CMState m0 m1 m2 (C ∅) 0
  /-- the Frobenius matrix at step `i` -/
  Fr : ℕ → Matrix (Fin 2) (Fin 2) A
  /-- the residue cardinality at step `i` -/
  q : ℕ → ℕ
  /-- the point at step `i` -/
  z : ℕ → A
  /-- the inverse point at step `i` -/
  zi : ℕ → A
  /-- the retraction of the quotient of the switch of step `i` onto the two singular blocks -/
  RQ : ∀ i, i < n →
    GRetract (E (chainT ps i) (ps i)).quotientCx (twoSingCx (Fr i) (q i) (z i) (zi i))
  /-- the relaxed class of step `i` -/
  zR : ∀ i, (C (insert (ps i) (chainT ps i))).X 1
  /-- `d z_R = 0` -/
  hzR : ∀ i, (C (insert (ps i) (chainT ps i))).d 1 2 rfl (zR i) = 0
  /-- the relaxed functional of step `i` -/
  lamR : ∀ i, (C (insert (ps i) (chainT ps i))).X 2 →ₗ[A] A
  /-- `λ_R ∘ d = 0` -/
  hlamR : ∀ i, lamR i ∘ₗ (C (insert (ps i) (chainT ps i))).d 1 2 rfl = 0

variable (cd : CMChainData C E m0 m1 m2 ps n)

/-- **The states of the chain** (tex 4185–4193). Kind: definition. -/
def cmState : ∀ i, i ≤ n → CMState m0 m1 m2 (C (chainT ps i)) i
  | 0, _ => cd.st0
  | i + 1, h => cmNext (E (chainT ps i) (ps i)) (cd.RQ i (by omega)) (cmState i (by omega))
      (cd.zR i) (cd.hzR i) (cd.lamR i) (cd.hlamR i)

/-- The cone model of step `i` (tex 5398–5424). Kind: definition. -/
abbrev cmCone (i : ℕ) (h : i < n) : FullPreComplex A :=
  coneOf (E (chainT ps i) (ps i)) (cd.RQ i h) (cmState cd i h.le)

/-- The retract of the relaxed complex of step `i` onto its cone model (tex 5398–5424).
Kind: definition. -/
abbrev cmConeRetract (i : ℕ) (h : i < n) :
    GRetract (C (insert (ps i) (chainT ps i))) (cmCone cd i h).toGCx :=
  coneRetract (E (chainT ps i) (ps i)) (cd.RQ i h) (cmState cd i h.le)

/-- **The matrix data of the chain** (tex 4142–4194, 4185–4193): the model of `C_∅`, the cone
blocks of the steps `i < n`, the classes and functionals in model coordinates, and the boundaries
`w_i` (the models of the boundaries `b_i` of the norm identity) and coboundaries `ν_i` (the models
of the coboundaries `μ_i` of the functional relation); zero beyond the chain. Kind: definition. -/
def CMChainData.toChainMat (bw : ∀ i, (C (insert (ps i) (chainT ps i))).X 0)
    (μ : ∀ i, (C (chainT ps i)).X 3 →ₗ[A] A) : ChainMat A m0 m1 m2 where
  d0 := cd.st0.d0
  d1 := cd.st0.d1
  d2 := cd.st0.d2
  Q i := if h : i < n then (cmCone cd i h).Q else 0
  V i := if h : i < n then (cmCone cd i h).V else 0
  B i := if h : i < n then (cmCone cd i h).B else 0
  zP0 := cd.st0.R.p.f 1 1 rfl cd.st0.z
  lP0 := funVec (ι := cD2 m1 m2 0) (cd.st0.lam ∘ₗ cd.st0.R.i.f 2 2 rfl)
  z i := if h : i < n then (cmConeRetract cd i h).p.f 1 1 rfl (cd.zR i) else 0
  l i := if h : i < n then funVec (ι := cD2 m1 m2 i ⊕ NS)
    (cd.lamR i ∘ₗ ((cmConeRetract cd i h).i.f 2 2 rfl : (cD2 m1 m2 i ⊕ NS → A) →ₗ[A] _))
    else 0
  w i := if h : i < n then (cmConeRetract cd i h).p.f 0 0 rfl (bw i) else 0
  ν i := if h : i < n then funVec (ι := Fin m2) (μ i ∘ₗ (cmState cd i h.le).R.i.f 3 3 rfl)
    else 0

variable (bw : ∀ i, (C (insert (ps i) (chainT ps i))).X 0) (μ : ∀ i, (C (chainT ps i)).X 3 →ₗ[A] A)

/-- The cone blocks of the matrix data at a step of the chain (tex 4185–4193).
Kind: PROVED. -/
theorem toChainMat_QVB (i : ℕ) (h : i < n) :
    (cd.toChainMat bw μ).Q i = (cmCone cd i h).Q ∧ (cd.toChainMat bw μ).V i = (cmCone cd i h).V ∧
      (cd.toChainMat bw μ).B i = (cmCone cd i h).B :=
  ⟨dite_eq_left h, dite_eq_left h, dite_eq_left h⟩

/-- The class, functional, boundary and coboundary of the matrix data at a step of the chain
(tex 4185–4193). Kind: PROVED. -/
theorem toChainMat_zlwν (i : ℕ) (h : i < n) :
    (cd.toChainMat bw μ).z i = (cmConeRetract cd i h).p.f 1 1 rfl (cd.zR i) ∧
      (cd.toChainMat bw μ).l i = funVec (ι := cD2 m1 m2 i ⊕ NS)
        (cd.lamR i ∘ₗ ((cmConeRetract cd i h).i.f 2 2 rfl : (cD2 m1 m2 i ⊕ NS → A) →ₗ[A] _)) ∧
      (cd.toChainMat bw μ).w i = (cmConeRetract cd i h).p.f 0 0 rfl (bw i) ∧
      (cd.toChainMat bw μ).ν i = funVec (ι := Fin m2) (μ i ∘ₗ (cmState cd i h.le).R.i.f 3 3 rfl) :=
  ⟨dite_eq_left h, dite_eq_left h, dite_eq_left h, dite_eq_left h⟩

/-- The models of the chain in degrees `0 → 1` are those of the states (tex 4185–4193).
Kind: PROVED. -/
theorem blk0_eq (i : ℕ) (h : i ≤ n) : (cd.toChainMat bw μ).blk0 i = (cmState cd i h).d0 := by
  induction i with
  | zero => rfl
  | succ i ih =>
    change (fromRows ((cd.toChainMat bw μ).blk0 i) (0 : Matrix NS (Fin m0) A)).submatrix
      (chE1 m0 m1 i).symm id = _
    rw [ih (by omega)]
    rfl

/-- The models of the chain in degrees `1 → 2` are those of the states (tex 4185–4193).
Kind: PROVED. -/
theorem blk1_eq (i : ℕ) (h : i ≤ n) : (cd.toChainMat bw μ).blk1 i = (cmState cd i h).d1 := by
  induction i with
  | zero => rfl
  | succ i ih =>
    change (fromBlocks ((cd.toChainMat bw μ).blk1 i) ((cd.toChainMat bw μ).Q i) 0
      ((cd.toChainMat bw μ).B i)).submatrix (chE2 m1 m2 i).symm (chE1 m0 m1 i).symm = _
    obtain ⟨hQ, -, hB⟩ := toChainMat_QVB cd bw μ i (by omega)
    rw [ih (by omega), hQ, hB]
    rfl

/-- The models of the chain in degrees `2 → 3` are those of the states (tex 4185–4193).
Kind: PROVED. -/
theorem blk2_eq (i : ℕ) (h : i ≤ n) : (cd.toChainMat bw μ).blk2 i = (cmState cd i h).d2 := by
  induction i with
  | zero => rfl
  | succ i ih =>
    change (fromCols ((cd.toChainMat bw μ).blk2 i) ((cd.toChainMat bw μ).V i)).submatrix id
      (chE2 m1 m2 i).symm = _
    obtain ⟨-, hV, -⟩ := toChainMat_QVB cd bw μ i (by omega)
    rw [ih (by omega), hV]
    rfl

/-- The primitive classes of the chain are the models of the classes of the states
(tex 4185–4193). Kind: PROVED. -/
theorem zP_eq (i : ℕ) (h : i ≤ n) :
    (cd.toChainMat bw μ).zP i = (cmState cd i h).R.p.f 1 1 rfl (cmState cd i h).z := by
  cases i with
  | zero => rfl
  | succ i =>
    change (cd.toChainMat bw μ).z i ∘ (chE1 m0 m1 i).symm = _
    rw [(toChainMat_zlwν cd bw μ i (by omega)).1]
    rfl

/-- A basis vector composed with an equivalence is a basis vector, over a ring (tex 4185–4193).
Kind: PROVED. -/
theorem single_comp_equivA {ι' κ : Type} [DecidableEq ι'] [DecidableEq κ] (e : ι' ≃ κ) (k : κ) :
    (Pi.single k (1 : A) : κ → A) ∘ e = Pi.single (e.symm k) 1 := by
  funext x
  by_cases h : e x = k
  · have h' : x = e.symm k := by rw [← h, Equiv.symm_apply_apply]
    subst h'
    simp
  · have h' : x ≠ e.symm k := fun hx => h (by rw [hx, Equiv.apply_symm_apply])
    simp [Function.comp_apply, h, h']

/-- The coordinate vector of a functional composed with a re-indexing, over a ring
(tex 4185–4193). Kind: PROVED. -/
theorem funVec_comp_funCongrLeftA {ι' κ : Type} [Fintype ι'] [DecidableEq ι'] [Fintype κ]
    [DecidableEq κ] (φ : (ι' → A) →ₗ[A] A) (e : ι' ≃ κ) :
    funVec (φ ∘ₗ (LinearEquiv.funCongrLeft A A e).toLinearMap) = funVec φ ∘ e.symm := by
  funext k
  change φ ((Pi.single k (1 : A) : κ → A) ∘ e) = φ (Pi.single (e.symm k) 1)
  rw [single_comp_equivA]

/-- The primitive functionals of the chain are the models of the functionals of the states
(tex 4185–4193). Kind: PROVED. -/
theorem lP_eq (i : ℕ) (h : i ≤ n) :
    (cd.toChainMat bw μ).lP i =
      funVec (ι := cD2 m1 m2 i) ((cmState cd i h).lam ∘ₗ (cmState cd i h).R.i.f 2 2 rfl) := by
  cases i with
  | zero => rfl
  | succ i =>
    change (cd.toChainMat bw μ).l i ∘ (chE2 m1 m2 i).symm = _
    rw [(toChainMat_zlwν cd bw μ i (by omega)).2.1]
    exact (funVec_comp_funCongrLeftA (ι' := cD2 m1 m2 i ⊕ NS) (κ := cD2 m1 m2 (i + 1))
      (cd.lamR i ∘ₗ ((cmConeRetract cd i (by omega)).i.f 2 2 rfl :
        (cD2 m1 m2 i ⊕ NS → A) →ₗ[A] _)) (chE2 m1 m2 i)).symm

end Chain

end ZInQ.Manuscript.RC.Wiring
