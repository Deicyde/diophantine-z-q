import ZInQKernel.Contrib.OneProof.RC.Wiring.CommonCoordinate13Leaf
import ZInQKernel.Contrib.OneProof.RC.Limits.Ultralimit

/-!
# The matrix data of a chain of relaxations, over any coefficient ring

Manuscript `diophantine_zq.tex`, Lemma `ex:arith-common-coordinate` (tex 4142–4194) in the
iterated mapping-cone bases (tex 4185–4193), with the inner limit of Lemma
`ex:limits-inner-limit` (tex 4385–4451) in view: "Each finite tuple of matrix entries then has a
compatible limit at every coefficient precision, giving matrices over `Λ`. Every polynomial
identity between the matrices survives" (tex 4444–4448).

The coordinates of the supports `T_0 = ∅ ⊂ T_1 ⊂ ⋯` along a chain of relaxations are computed on
the iterated cone models: the model of `C_{T_{i+1}}` is the cone model of step `i` re-indexed as
a block complex (`FullPreComplex.toBlock`, round seven). In these bases the whole chain is a
finite tuple of matrices whose shapes are fixed by the ranks `(m₀, m₁, m₂)` of the model of `C_∅`
(each step adds the four summands `N = Fin 2 ⊕ Fin 2` of the two places above the prime). This
file records that tuple over an arbitrary commutative ring, with its identities modulo an ideal,
so that it can be taken at the finite coefficient stages `A_s = Λ/(2^s, t^s)`, pushed along ring
homomorphisms, and passed to the ultralimit over `Λ`.

* `NS`, `cD1`, `cD2`, `joinF`, `chE1`, `chE2`: the index types of the models in degrees one and
  two at step `i` (`Fin m₀ ⊕ Unit ⊕ Fin (m₁ + 4i)`, `Fin (m₁ + 4i) ⊕ Unit ⊕ Fin m₂`) and the
  re-indexings `(·) ⊕ N ≃ (·)` of the cone models.
* `ChainMat R m₀ m₁ m₂`: the matrix data — the model of `C_∅`, and for every step `i` the
  off-diagonal blocks `Q_i`, `V_i`, the new block `B_i`, the relaxed class `z_i` and functional
  `λ_i`, and the boundary `w_i` and coboundary `ν_i` of the norm identity and of the functional
  relation; `blk0`, `blk1`, `blk2`, `zP`, `lP`: the models of the supports `T_i` and their
  primitive classes and functionals, by recursion (the re-indexed cone models and relaxed classes
  of the previous step).
* `FrobSeq`: the Frobenius data of the steps; `ChainMat.Holds J f n`: the identities of the first
  `n` steps modulo an ideal `J` (complex identities, the new block is the two-place block, cycles
  and closed functionals, the norm identity with its retained boundary, the functional relation
  up to a coboundary).
* `ChainMat.map`, `FrobSeq.map`: push-forward along a ring homomorphism; `blk0_map`, `blk1_map`,
  `blk2_map`, `zP_map`, `lP_map`; **`holds_map_iff`**: the identities of the push-forward modulo
  `J'` are the identities modulo the preimage `φ⁻¹(J')`; `Holds.map`.

Kinds: definitions and PROVED.
-/

noncomputable section

namespace ZInQ.Manuscript.RC.Wiring

open Matrix
open ZInQ.Contrib.CloudB3RC53.CommonCoordinate (twoPlaceBlock)
open ZInQ.Manuscript.RC.Central (pointFactor)

/-- **The new summands of a step** (tex 4176–4184): two coordinates at each of the two places
above the prime. Kind: definition. -/
abbrev NS : Type := Fin 2 ⊕ Fin 2

section Shapes

variable (m0 m1 m2 : ℕ)

/-- The degree-one index of the model at step `i` (tex 4185–4193): `Fin m₀ ⊕ Unit ⊕ Fin (m₁+4i)`.
Kind: definition. -/
abbrev cD1 (i : ℕ) : Type := Fin m0 ⊕ Unit ⊕ Fin (m1 + 4 * i)

/-- The degree-two index of the model at step `i` (tex 4185–4193): `Fin (m₁+4i) ⊕ Unit ⊕ Fin m₂`.
Kind: definition. -/
abbrev cD2 (i : ℕ) : Type := Fin (m1 + 4 * i) ⊕ Unit ⊕ Fin m2

/-- The new summands join the old ones: `Fin (m₁ + 4i) ⊕ N ≃ Fin (m₁ + 4(i+1))`
(tex 4185–4193). Kind: definition. -/
def joinF (i : ℕ) : Fin (m1 + 4 * i) ⊕ NS ≃ Fin (m1 + 4 * (i + 1)) :=
  (Equiv.sumCongr (Equiv.refl _) finSumFinEquiv).trans
    (finSumFinEquiv.trans (finCongr (by ring)))

/-- Degree one: `(B₁ ⊕ H₁ ⊕ E₁) ⊕ N ≃ B₁ ⊕ H₁ ⊕ (E₁ ⊕ N)` (tex 4185–4193). Kind: definition. -/
def chE1 (i : ℕ) : cD1 m0 m1 i ⊕ NS ≃ cD1 m0 m1 (i + 1) :=
  (Equiv.sumAssoc _ _ _).trans (Equiv.sumCongr (Equiv.refl _)
    ((Equiv.sumAssoc _ _ _).trans (Equiv.sumCongr (Equiv.refl _) (joinF m1 i))))

/-- Degree two: `(B₂ ⊕ H₂ ⊕ E₂) ⊕ N ≃ (B₂ ⊕ N) ⊕ H₂ ⊕ E₂` (tex 4185–4193). Kind: definition. -/
def chE2 (i : ℕ) : cD2 m1 m2 i ⊕ NS ≃ cD2 m1 m2 (i + 1) :=
  (Equiv.sumAssoc _ _ _).trans ((Equiv.sumCongr (Equiv.refl _) (Equiv.sumComm _ _)).trans
    ((Equiv.sumAssoc _ _ _).symm.trans (Equiv.sumCongr (joinF m1 i) (Equiv.refl _))))

end Shapes

/-- **The matrix data of a chain of relaxations** (tex 4142–4194, 4185–4193): the model of
`C_∅` (`d0`, `d1`, `d2`) with its primitive class and functional (`zP0`, `lP0`), and for every
step `i`: the off-diagonal blocks `Q_i`, `V_i` and the new block `B_i` of the cone model, the
relaxed class `z_i` and functional `λ_i`, the boundary `w_i` of the norm identity and the
coboundary `ν_i` of the functional relation. Kind: definition (data). -/
structure ChainMat (R : Type) [CommRing R] (m0 m1 m2 : ℕ) where
  /-- the model of `C_∅` in degrees `0 → 1` -/
  d0 : Matrix (cD1 m0 m1 0) (Fin m0) R
  /-- the model of `C_∅` in degrees `1 → 2` -/
  d1 : Matrix (cD2 m1 m2 0) (cD1 m0 m1 0) R
  /-- the model of `C_∅` in degrees `2 → 3` -/
  d2 : Matrix (Fin m2) (cD2 m1 m2 0) R
  /-- the block of the cone model of step `i` from the new summands in degree one -/
  Q : ∀ i, Matrix (cD2 m1 m2 i) NS R
  /-- the block of the cone model of step `i` from the new summands in degree two -/
  V : ∀ _ : ℕ, Matrix (Fin m2) NS R
  /-- the new block of step `i` -/
  B : ∀ _ : ℕ, Matrix NS NS R
  /-- the primitive class of `C_∅` -/
  zP0 : cD1 m0 m1 0 → R
  /-- the primitive functional of `C_∅` -/
  lP0 : cD2 m1 m2 0 → R
  /-- the relaxed class of step `i` -/
  z : ∀ i, cD1 m0 m1 i ⊕ NS → R
  /-- the relaxed functional of step `i` -/
  l : ∀ i, cD2 m1 m2 i ⊕ NS → R
  /-- the boundary of the norm identity at step `i` -/
  w : ∀ _ : ℕ, Fin m0 → R
  /-- the coboundary of the functional relation at step `i` -/
  ν : ∀ _ : ℕ, Fin m2 → R

/-- **The Frobenius data of the steps** (tex 4176–4184): `Fr_i`, `q_i`, `q_i⁻¹`, `a_i`, `z_i`,
`z_i⁻¹`. Kind: definition (data). -/
structure FrobSeq (R : Type) [CommRing R] where
  /-- the Frobenius matrix of step `i` -/
  Fr : ℕ → Matrix (Fin 2) (Fin 2) R
  /-- the residue cardinality of step `i` -/
  q : ℕ → R
  /-- its inverse -/
  qi : ℕ → R
  /-- the trace of Frobenius of step `i` -/
  a : ℕ → R
  /-- the point of step `i` -/
  z : ℕ → R
  /-- its inverse -/
  zi : ℕ → R

namespace ChainMat

variable {R : Type} [CommRing R] {m0 m1 m2 : ℕ} (c : ChainMat R m0 m1 m2)

/-- The model of `C_{T_i}` in degrees `0 → 1` (tex 4185–4193): the re-indexed cone models.
Kind: definition. -/
def blk0 : ∀ i, Matrix (cD1 m0 m1 i) (Fin m0) R
  | 0 => c.d0
  | i + 1 => (fromRows (blk0 i) (0 : Matrix NS (Fin m0) R)).submatrix (chE1 m0 m1 i).symm id

/-- The model of `C_{T_i}` in degrees `1 → 2` (tex 4185–4193). Kind: definition. -/
def blk1 : ∀ i, Matrix (cD2 m1 m2 i) (cD1 m0 m1 i) R
  | 0 => c.d1
  | i + 1 => (fromBlocks (blk1 i) (c.Q i) 0 (c.B i)).submatrix (chE2 m1 m2 i).symm
      (chE1 m0 m1 i).symm

/-- The model of `C_{T_i}` in degrees `2 → 3` (tex 4185–4193). Kind: definition. -/
def blk2 : ∀ i, Matrix (Fin m2) (cD2 m1 m2 i) R
  | 0 => c.d2
  | i + 1 => (fromCols (blk2 i) (c.V i)).submatrix id (chE2 m1 m2 i).symm

/-- The primitive class of step `i` (tex 4185–4193): the relaxed class of the previous step,
re-indexed. Kind: definition. -/
def zP : ∀ i, cD1 m0 m1 i → R
  | 0 => c.zP0
  | i + 1 => c.z i ∘ (chE1 m0 m1 i).symm

/-- The primitive functional of step `i` (tex 4185–4193). Kind: definition. -/
def lP : ∀ i, cD2 m1 m2 i → R
  | 0 => c.lP0
  | i + 1 => c.l i ∘ (chE2 m1 m2 i).symm

/-- The differential `1 → 2` of the cone model of step `i` (tex 5398–5424):
`[[d¹, Q], [0, B]]`. Kind: definition. -/
abbrev cone1 (i : ℕ) : Matrix (cD2 m1 m2 i ⊕ NS) (cD1 m0 m1 i ⊕ NS) R :=
  fromBlocks (c.blk1 i) (c.Q i) 0 (c.B i)

/-- **The identities of the first `n` steps modulo an ideal `J`** (tex 4142–4194, 4444–4448):
the model of `C_∅` is a complex with a cycle and a closed functional; at every step the cone model
is a complex (`d² Q + V B = 0`), its new block is the two-place block of the step, the relaxed
class and functional are a cycle and a closed functional, and the norm identity with its retained
boundary and the functional relation up to a coboundary hold. Kind: definition. -/
structure Holds (J : Ideal R) (f : FrobSeq R) (n : ℕ) : Prop where
  /-- `d¹ d⁰ = 0` for the model of `C_∅` -/
  h10 : ∀ a b, (c.d1 * c.d0) a b ∈ J
  /-- `d² d¹ = 0` for the model of `C_∅` -/
  h21 : ∀ a b, (c.d2 * c.d1) a b ∈ J
  /-- the cone models are complexes -/
  hQVB : ∀ i < n, ∀ a b, (c.blk2 i * c.Q i + c.V i * c.B i) a b ∈ J
  /-- the new block is the two-place block of the step -/
  hB : ∀ i < n, ∀ a b,
    c.B i a b - twoPlaceBlock (f.Fr i) (f.q i) (f.z i) (f.zi i) a b ∈ J
  /-- the primitive class of `C_∅` is a cycle -/
  hzP0 : ∀ a, (c.d1 *ᵥ c.zP0) a ∈ J
  /-- the primitive functional of `C_∅` is closed -/
  hlP0 : ∀ a, (c.lP0 ᵥ* c.d1) a ∈ J
  /-- the relaxed classes are cycles -/
  hz : ∀ i < n, ∀ a, (c.cone1 i *ᵥ c.z i) a ∈ J
  /-- the relaxed functionals are closed -/
  hl : ∀ i < n, ∀ a, (c.l i ᵥ* c.cone1 i) a ∈ J
  /-- the norm identity with its retained boundary, old part -/
  hnorm : ∀ i < n, ∀ a, c.z i (Sum.inl a) -
    (pointFactor (f.a i) (f.z i) (f.zi i) * c.zP i a + (c.blk0 i *ᵥ c.w i) a) ∈ J
  /-- the norm identity, new part -/
  hnormN : ∀ i < n, ∀ a, c.z i (Sum.inr a) ∈ J
  /-- the functional relation up to a coboundary -/
  hfun : ∀ i < n, ∀ a, c.l i (Sum.inl a) -
    (pointFactor (f.a i) (f.z i) (f.zi i) * c.lP i a + (c.ν i ᵥ* c.blk2 i) a) ∈ J

/-! ### Push-forward along ring homomorphisms -/

variable {R' : Type} [CommRing R'] (φ : R →+* R')

/-- **The push-forward of the matrix data along a ring homomorphism** (tex 4444–4448).
Kind: definition. -/
def map : ChainMat R' m0 m1 m2 where
  d0 := c.d0.map φ
  d1 := c.d1.map φ
  d2 := c.d2.map φ
  Q i := (c.Q i).map φ
  V i := (c.V i).map φ
  B i := (c.B i).map φ
  zP0 := φ ∘ c.zP0
  lP0 := φ ∘ c.lP0
  z i := φ ∘ c.z i
  l i := φ ∘ c.l i
  w i := φ ∘ c.w i
  ν i := φ ∘ c.ν i

/-- The pushed models in degrees `0 → 1` (tex 4444–4448). Kind: PROVED. -/
theorem blk0_map (i : ℕ) : (c.map φ).blk0 i = (c.blk0 i).map φ := by
  induction i with
  | zero => rfl
  | succ i ih =>
    change (fromRows ((c.map φ).blk0 i) (0 : Matrix NS (Fin m0) R')).submatrix _ id = _
    rw [ih]
    change _ = ((fromRows (c.blk0 i) (0 : Matrix NS (Fin m0) R)).submatrix _ id).map φ
    rw [← submatrix_map, fromRows_map, Matrix.map_zero _ (map_zero φ)]

/-- The pushed models in degrees `1 → 2` (tex 4444–4448). Kind: PROVED. -/
theorem blk1_map (i : ℕ) : (c.map φ).blk1 i = (c.blk1 i).map φ := by
  induction i with
  | zero => rfl
  | succ i ih =>
    change (fromBlocks ((c.map φ).blk1 i) ((c.Q i).map φ) 0 ((c.B i).map φ)).submatrix _ _ = _
    rw [ih]
    change _ = ((fromBlocks (c.blk1 i) (c.Q i) 0 (c.B i)).submatrix _ _).map φ
    rw [← submatrix_map, fromBlocks_map, Matrix.map_zero _ (map_zero φ)]

/-- The pushed models in degrees `2 → 3` (tex 4444–4448). Kind: PROVED. -/
theorem blk2_map (i : ℕ) : (c.map φ).blk2 i = (c.blk2 i).map φ := by
  induction i with
  | zero => rfl
  | succ i ih =>
    change (fromCols ((c.map φ).blk2 i) ((c.V i).map φ)).submatrix id _ = _
    rw [ih]
    change _ = ((fromCols (c.blk2 i) (c.V i)).submatrix id _).map φ
    rw [← submatrix_map, fromCols_map]

/-- The pushed primitive classes (tex 4444–4448). Kind: PROVED (definitional). -/
theorem zP_map (i : ℕ) : (c.map φ).zP i = φ ∘ c.zP i := by
  cases i <;> rfl

/-- The pushed primitive functionals (tex 4444–4448). Kind: PROVED (definitional). -/
theorem lP_map (i : ℕ) : (c.map φ).lP i = φ ∘ c.lP i := by
  cases i <;> rfl

/-- The pushed cone differentials (tex 4444–4448). Kind: PROVED. -/
theorem cone1_map (i : ℕ) : (c.map φ).cone1 i = (c.cone1 i).map φ := by
  change fromBlocks ((c.map φ).blk1 i) ((c.Q i).map φ) 0 ((c.B i).map φ) = _
  rw [blk1_map, fromBlocks_map, Matrix.map_zero _ (map_zero φ)]

/-- Pushing forward twice is pushing forward along the composite (tex 4444–4448).
Kind: PROVED (definitional). -/
theorem map_map {R'' : Type} [CommRing R''] (ψ : R' →+* R'') :
    (c.map φ).map ψ = c.map (ψ.comp φ) :=
  rfl

end ChainMat

namespace FrobSeq

variable {R R' : Type} [CommRing R] [CommRing R'] (f : FrobSeq R) (φ : R →+* R')

/-- The push-forward of the Frobenius data (tex 4444–4448). Kind: definition. -/
def map : FrobSeq R' where
  Fr i := (f.Fr i).map φ
  q i := φ (f.q i)
  qi i := φ (f.qi i)
  a i := φ (f.a i)
  z i := φ (f.z i)
  zi i := φ (f.zi i)

end FrobSeq

/-- The two-place block commutes with ring homomorphisms (tex 4176–4184). Kind: PROVED. -/
theorem twoPlaceBlock_map {R R' : Type} [CommRing R] [CommRing R'] (φ : R →+* R')
    (F : Matrix (Fin 2) (Fin 2) R) (q z zi : R) :
    (twoPlaceBlock F q z zi).map φ = twoPlaceBlock (F.map φ) (φ q) (φ z) (φ zi) := by
  ext (a | a) (b | b) <;> simp [twoPlaceBlock, Matrix.one_apply, apply_ite φ]

/-- The point factor commutes with ring homomorphisms (tex 4145, 4158). Kind: PROVED. -/
theorem pointFactor_map {R R' : Type} [CommRing R] [CommRing R'] (φ : R →+* R') (a z zi : R) :
    φ (pointFactor a z zi) = pointFactor (φ a) (φ z) (φ zi) := by
  simp only [pointFactor, map_sub]

namespace ChainMat

variable {R R' : Type} [CommRing R] [CommRing R'] {m0 m1 m2 : ℕ} (c : ChainMat R m0 m1 m2)
  (φ : R →+* R')

/-- **The identities of the push-forward modulo `J'` are the identities modulo `φ⁻¹(J')`**
(tex 4444–4448: "every polynomial identity between the matrices survives"). Kind: PROVED. -/
theorem holds_map_iff (J' : Ideal R') (f : FrobSeq R) (n : ℕ) :
    (c.map φ).Holds J' (f.map φ) n ↔ c.Holds (J'.comap φ) f n := by
  have eM : ∀ {m k o : Type} [Fintype k] (A : Matrix m k R) (B : Matrix k o R) a b,
      (A.map φ * B.map φ) a b = φ ((A * B) a b) := fun A B a b => by
    rw [← Matrix.map_mul]
    rfl
  have eV : ∀ {m k : Type} [Fintype k] (A : Matrix m k R) (v : k → R) a,
      (A.map φ *ᵥ (φ ∘ v)) a = φ ((A *ᵥ v) a) := fun A v a => (RingHom.map_mulVec φ A v a).symm
  have eW : ∀ {m k : Type} [Fintype m] (A : Matrix m k R) (v : m → R) a,
      ((φ ∘ v) ᵥ* A.map φ) a = φ ((v ᵥ* A) a) := fun A v a => (RingHom.map_vecMul φ A v a).symm
  constructor
  · intro h
    refine ⟨fun a b => ?_, fun a b => ?_, fun i hi a b => ?_, fun i hi a b => ?_, fun a => ?_,
      fun a => ?_, fun i hi a => ?_, fun i hi a => ?_, fun i hi a => ?_, fun i hi a => ?_,
      fun i hi a => ?_⟩
    · have := h.h10 a b
      rw [Ideal.mem_comap, ← eM]
      exact this
    · have := h.h21 a b
      rw [Ideal.mem_comap, ← eM]
      exact this
    · have := h.hQVB i hi a b
      rw [Ideal.mem_comap, Matrix.add_apply, map_add, ← eM, ← eM, ← blk2_map]
      exact this
    · have := h.hB i hi a b
      have e : twoPlaceBlock ((f.map φ).Fr i) ((f.map φ).q i) ((f.map φ).z i) ((f.map φ).zi i) =
          (twoPlaceBlock (f.Fr i) (f.q i) (f.z i) (f.zi i)).map φ :=
        (twoPlaceBlock_map φ _ _ _ _).symm
      rw [e] at this
      rw [Ideal.mem_comap, map_sub]
      exact this
    · have := h.hzP0 a
      rw [Ideal.mem_comap, ← eV]
      exact this
    · have := h.hlP0 a
      rw [Ideal.mem_comap, ← eW]
      exact this
    · have := h.hz i hi a
      rw [Ideal.mem_comap, ← eV, ← cone1_map]
      exact this
    · have := h.hl i hi a
      rw [Ideal.mem_comap, ← eW, ← cone1_map]
      exact this
    · have := h.hnorm i hi a
      rw [Ideal.mem_comap, map_sub, map_add, map_mul, pointFactor_map, ← eV, ← blk0_map]
      change _ - (_ * ((c.map φ).zP i) a + _) ∈ J' at this
      rw [zP_map] at this
      exact this
    · exact Ideal.mem_comap.2 (h.hnormN i hi a)
    · have := h.hfun i hi a
      rw [Ideal.mem_comap, map_sub, map_add, map_mul, pointFactor_map, ← eW, ← blk2_map]
      change _ - (_ * ((c.map φ).lP i) a + _) ∈ J' at this
      rw [lP_map] at this
      exact this
  · intro h
    refine ⟨fun a b => ?_, fun a b => ?_, fun i hi a b => ?_, fun i hi a b => ?_, fun a => ?_,
      fun a => ?_, fun i hi a => ?_, fun i hi a => ?_, fun i hi a => ?_, fun i hi a => ?_,
      fun i hi a => ?_⟩
    · have := Ideal.mem_comap.1 (h.h10 a b)
      change (c.d1.map φ * c.d0.map φ) a b ∈ J'
      rw [eM]
      exact this
    · have := Ideal.mem_comap.1 (h.h21 a b)
      change (c.d2.map φ * c.d1.map φ) a b ∈ J'
      rw [eM]
      exact this
    · have := Ideal.mem_comap.1 (h.hQVB i hi a b)
      change ((c.map φ).blk2 i * (c.Q i).map φ + (c.V i).map φ * (c.B i).map φ) a b ∈ J'
      rw [blk2_map, Matrix.add_apply, eM, eM, ← map_add]
      exact this
    · have := Ideal.mem_comap.1 (h.hB i hi a b)
      have e : twoPlaceBlock ((f.map φ).Fr i) ((f.map φ).q i) ((f.map φ).z i) ((f.map φ).zi i) =
          (twoPlaceBlock (f.Fr i) (f.q i) (f.z i) (f.zi i)).map φ :=
        (twoPlaceBlock_map φ _ _ _ _).symm
      rw [e]
      rw [map_sub] at this
      exact this
    · have := Ideal.mem_comap.1 (h.hzP0 a)
      change (c.d1.map φ *ᵥ (φ ∘ c.zP0)) a ∈ J'
      rw [eV]
      exact this
    · have := Ideal.mem_comap.1 (h.hlP0 a)
      change ((φ ∘ c.lP0) ᵥ* c.d1.map φ) a ∈ J'
      rw [eW]
      exact this
    · have := Ideal.mem_comap.1 (h.hz i hi a)
      change ((c.map φ).cone1 i *ᵥ (φ ∘ c.z i)) a ∈ J'
      rw [cone1_map, eV]
      exact this
    · have := Ideal.mem_comap.1 (h.hl i hi a)
      change ((φ ∘ c.l i) ᵥ* (c.map φ).cone1 i) a ∈ J'
      rw [cone1_map, eW]
      exact this
    · have := Ideal.mem_comap.1 (h.hnorm i hi a)
      change φ (c.z i (Sum.inl a)) - (pointFactor (φ (f.a i)) (φ (f.z i)) (φ (f.zi i)) *
        (c.map φ).zP i a + ((c.map φ).blk0 i *ᵥ (φ ∘ c.w i)) a) ∈ J'
      rw [zP_map, blk0_map, eV, ← pointFactor_map]
      rw [map_sub, map_add, map_mul] at this
      exact this
    · exact Ideal.mem_comap.1 (h.hnormN i hi a)
    · have := Ideal.mem_comap.1 (h.hfun i hi a)
      change φ (c.l i (Sum.inl a)) - (pointFactor (φ (f.a i)) (φ (f.z i)) (φ (f.zi i)) *
        (c.map φ).lP i a + ((φ ∘ c.ν i) ᵥ* (c.map φ).blk2 i) a) ∈ J'
      rw [lP_map, blk2_map, eW, ← pointFactor_map]
      rw [map_sub, map_add, map_mul] at this
      exact this

/-- The identities are monotone in the ideal (tex 4444–4448). Kind: PROVED. -/
theorem Holds.mono {J J' : Ideal R} {f : FrobSeq R} {n : ℕ} (h : c.Holds J f n) (hJ : J ≤ J') :
    c.Holds J' f n :=
  ⟨fun a b => hJ (h.h10 a b), fun a b => hJ (h.h21 a b), fun i hi a b => hJ (h.hQVB i hi a b),
    fun i hi a b => hJ (h.hB i hi a b), fun a => hJ (h.hzP0 a), fun a => hJ (h.hlP0 a),
    fun i hi a => hJ (h.hz i hi a), fun i hi a => hJ (h.hl i hi a),
    fun i hi a => hJ (h.hnorm i hi a), fun i hi a => hJ (h.hnormN i hi a),
    fun i hi a => hJ (h.hfun i hi a)⟩

/-- **The identities survive every ring homomorphism killing the ideal** (tex 4444–4448).
Kind: PROVED. -/
theorem Holds.map {J : Ideal R} {f : FrobSeq R} {n : ℕ} (h : c.Holds J f n) (J' : Ideal R')
    (hφ : ∀ x ∈ J, φ x ∈ J') : (c.map φ).Holds J' (f.map φ) n :=
  (c.holds_map_iff φ J' f n).2 (h.mono c fun x hx => Ideal.mem_comap.2 (hφ x hx))

end ChainMat

end ZInQ.Manuscript.RC.Wiring
