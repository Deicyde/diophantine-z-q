import ZInQKernel.Contrib.OneProof.RC.FibreDuality.LimitMatrices

/-!
# Lane RC31, round 2, part 3: the global duality of the limit diagram from retained matrices

Manuscript `diophantine_zq.tex`, tex 4385–4388: "The same retained data include the integral
duality maps, their homotopy inverses, and the homotopies expressing compatibility of duality with
localization"; Lemma `ex:limits-inner-limit` (tex 4391–4451): every polynomial identity between
the retained matrices survives the inner limit; Nekovář, *Selmer complexes*, 5.4.3 (global duality).

For the matrix presentation of the limit diagram (`LimitMatrices.lean`), this file presents the
compactly supported complex `Cone(res : G → L)[−1]`, its dual `Hom(−, k)[−3]` and the global
duality map `globalDualityMap` of `limitPair` by matrices, and proves that the global duality map
is a quasi-isomorphism as soon as retained matrices give it a homotopy inverse with homotopies.

* `cIdxOf`, `RkAtOf`, `compactDiffMatOf`, `dualDiffMatOf`, `forwardMatOf`: the coordinate matrices,
  as functions of their input matrices over any commutative ring (so that they apply equally to the
  coefficient-stage matrices); `cIdx`, `RkAt`, `compactDiffMat`, `dualDiffMat`, `forwardMat`: the
  same over `k`.
* `compactCoord`, `dualCoord`: the coordinates; `compactCoord_d`, `dualCoord_d`,
  `dualCoord_forward`: the differentials and the duality map in coordinates.
* `globalHomotopyEquiv`, **`globalDuality_quasiIso_ofMat`**: the homotopy equivalence and the
  quasi-isomorphism.

Kinds: definitions and PROVED.
-/

noncomputable section

namespace ZInQ.Manuscript.RC.FibreDuality

open CategoryTheory Matrix
open ZInQ.Contrib.CloudB3RC53.PairedFunctional ZInQ.Contrib.CloudB3RC53.SelmerDuality
open ZInQ.Contrib.RC53Assist.InnerLimit

section RingGeneric

variable {S : Type} [CommRing S] {rank : ℤ → ℕ}

/-- **The coordinate index of the compactly supported complex** `Cone(G → L)[−1]` in degree `m`,
over any ranks: `Fin (rank m) ⊕ lIdx (m − 1)` (the `G`-part and the `L`-part). Finiteness and
decidable equality are inferred from those of the summands. Locator: tex 4385–4388; Nekovář, Selmer
complexes, 5.4.3. Kind: definition. -/
abbrev cIdxOf (rank : ℤ → ℕ) (m : ℤ) : Type := Fin (rank m) ⊕ lIdx (m - 1)

/-- **The restriction matrix transported along an index equality**: `Rk m` viewed with rows indexed
by `lIdx n` when `m = n`, over any commutative ring. Locator: tex 4385–4388. Kind: definition. -/
def RkAtOf (Rk : ∀ n : ℤ, Matrix (lIdx n) (Fin (rank n)) S) (m n : ℤ) (h : m = n) :
    Matrix (lIdx n) (Fin (rank m)) S := by
  subst h
  exact Rk m

/-- **The differential matrix of `Cone(G → L)[−1]`** from degree `m` to `m' = m + 1`, over any
commutative ring: the block matrix `[[D, 0], [R, 0]]` (the split model has zero differentials),
matching `d(b, y) = (d b, res b − d y)`. Locator: tex 4385–4388; tex 4391–4451. Kind: definition. -/
def compactDiffMatOf (D : ∀ a b : ℤ, a + 1 = b → Matrix (Fin (rank b)) (Fin (rank a)) S)
    (Rk : ∀ n : ℤ, Matrix (lIdx n) (Fin (rank n)) S) (m m' : ℤ) (h : m + 1 = m') :
    Matrix (cIdxOf rank m') (cIdxOf rank m) S :=
  Matrix.fromBlocks (D m m' h) 0 (RkAtOf Rk m (m' - 1) (by omega)) 0

/-- **The differential matrix of the dual** `Hom(Cone(G → L)[−1], k)[−3]` from degree `a` to `b`, in
the dual coordinates, over any commutative ring: `−(−1)^a` times the transpose of the cone
differential from degree `3 − b` to `3 − a`. Locator: tex 4385–4388; tex 4391–4451. Kind:
definition. -/
def dualDiffMatOf (D : ∀ a b : ℤ, a + 1 = b → Matrix (Fin (rank b)) (Fin (rank a)) S)
    (Rk : ∀ n : ℤ, Matrix (lIdx n) (Fin (rank n)) S) (a b : ℤ) (h : a + 1 = b) :
    Matrix (cIdxOf rank (3 - b)) (cIdxOf rank (3 - a)) S :=
  (-(sgn a : S)) • (compactDiffMatOf D Rk (3 - b) (3 - a) (by omega))ᵀ

/-- **The matrix of the global duality map** in degree `a`, over any commutative ring: rows
`(Mbg a (3 − a))ᵀ` (the global trace pairing) stacked over `(−1)^a (Mbl a (3 − a − 1))ᵀ Rk a` (the
local pairing of the restriction), matching
`a ↦ ((b, y) ↦ B_G(a, b) + (−1)^a β(res a, y))`. Locator: tex 4385–4388; Nekovář, Selmer complexes,
5.4.3. Kind: definition. -/
def forwardMatOf (Mbg : ∀ a b : ℤ, a + b = 3 → Matrix (Fin (rank a)) (Fin (rank b)) S)
    (Mbl : ∀ a b : ℤ, Matrix (lIdx a) (lIdx b) S)
    (Rk : ∀ n : ℤ, Matrix (lIdx n) (Fin (rank n)) S) (a : ℤ) :
    Matrix (cIdxOf rank (3 - a)) (Fin (rank a)) S :=
  Matrix.fromRows (Mbg a (3 - a) (by omega))ᵀ ((sgn a : S) • ((Mbl a (3 - a - 1))ᵀ * Rk a))

end RingGeneric

section Generic

variable {k : Type} [Field k]

/-- The linear form `w ↦ v ⬝ w`. Kind: definition. -/
def dotLin {ι : Type} [Fintype ι] (v : ι → k) : (ι → k) →ₗ[k] k where
  toFun w := v ⬝ᵥ w
  map_add' w w' := dotProduct_add v w w'
  map_smul' c w := by
    rw [dotProduct_smul]
    rfl

/-- Expansion of a coordinate vector in the standard basis. Kind: PROVED. -/
theorem coord_expand {ι : Type} [Fintype ι] [DecidableEq ι] (w : ι → k) :
    w = ∑ i, w i • Pi.single i (1 : k) := by
  ext j
  simp [Finset.sum_apply, Pi.single_apply]

/-- **The dual coordinates** of a coordinate system `e : V ≃ (ι → k)`: a linear form `φ` goes to
its values on the standard basis, `φ ↦ (j ↦ φ (e⁻¹ (single j 1)))`. Locator: tex 4385–4388.
Kind: definition. -/
def dualEquivOfCoord {V ι : Type} [AddCommGroup V] [Module k V] [Fintype ι] [DecidableEq ι]
    (e : V ≃ₗ[k] (ι → k)) : Module.Dual k V ≃ₗ[k] (ι → k) where
  toFun φ j := φ (e.symm (Pi.single j 1))
  map_add' φ ψ := rfl
  map_smul' c φ := rfl
  invFun v := dotLin v ∘ₗ e.toLinearMap
  left_inv φ := by
    refine LinearMap.ext fun x => ?_
    change (fun j => φ (e.symm (Pi.single j 1))) ⬝ᵥ e x = φ x
    have h1 : φ x = φ (e.symm (∑ j, (e x) j • Pi.single j (1 : k))) := by
      rw [← coord_expand, LinearEquiv.symm_apply_apply]
    rw [h1, map_sum, map_sum]
    simp only [map_smul, smul_eq_mul, dotProduct]
    exact Finset.sum_congr rfl fun j _ => mul_comm _ _
  right_inv v := by
    funext j
    change v ⬝ᵥ e (e.symm (Pi.single j 1)) = v j
    rw [LinearEquiv.apply_symm_apply, dotProduct_single, mul_one]

/-- Evaluation of the dual coordinates. Kind: PROVED. -/
theorem dualEquivOfCoord_apply {V ι : Type} [AddCommGroup V] [Module k V] [Fintype ι]
    [DecidableEq ι] (e : V ≃ₗ[k] (ι → k)) (φ : Module.Dual k V) (j : ι) :
    dualEquivOfCoord e φ j = φ (e.symm (Pi.single j 1)) :=
  rfl

/-- A linear form is the dot product of its dual coordinates with the coordinates. Kind:
PROVED. -/
theorem dualEquivOfCoord_eval {V ι : Type} [AddCommGroup V] [Module k V] [Fintype ι]
    [DecidableEq ι] (e : V ≃ₗ[k] (ι → k)) (φ : Module.Dual k V) (x : V) :
    φ x = dualEquivOfCoord e φ ⬝ᵥ e x := by
  conv_lhs => rw [← (dualEquivOfCoord e).symm_apply_apply φ]
  rfl

/-- Characterization of the dual coordinates by evaluation. Kind: PROVED. -/
theorem dualEquivOfCoord_eq {V ι : Type} [AddCommGroup V] [Module k V] [Fintype ι]
    [DecidableEq ι] (e : V ≃ₗ[k] (ι → k)) (φ : Module.Dual k V) (v : ι → k)
    (h : ∀ x, φ x = v ⬝ᵥ e x) : dualEquivOfCoord e φ = v := by
  funext j
  rw [dualEquivOfCoord_apply, h, LinearEquiv.apply_symm_apply, dotProduct_single, mul_one]

/-- The dot product of two block vectors. Kind: PROVED. -/
theorem sumElim_dotProduct {m n : Type} [Fintype m] [Fintype n] (u x : m → k) (v y : n → k) :
    Sum.elim u v ⬝ᵥ Sum.elim x y = u ⬝ᵥ x + v ⬝ᵥ y := by
  simp [dotProduct, Fintype.sum_sum_type]

/-- Multiplying a stacked matrix by a vector. Kind: PROVED. -/
theorem fromRows_mulVec_eq {m₁ m₂ n : Type} [Fintype n] (A : Matrix m₁ n k) (B : Matrix m₂ n k)
    (x : n → k) : Matrix.fromRows A B *ᵥ x = Sum.elim (A *ᵥ x) (B *ᵥ x) := by
  funext i
  cases i <;> rfl

end Generic

section Specialized

variable {k : Type} [Field k]
variable {R : Type} [CommRing R] [TopologicalSpace R] [IsTopologicalRing R] [CompactSpace R]
  [T2Space R] {I : ℕ → Ideal R} {U : Ultrafilter ℕ}
  (hI : ZInQ.Manuscript.RC.Limits.IdealsTendToZero I)
  (hU : (U : Filter ℕ) ≤ Filter.cofinite) (ρ : R →+* k) (C : ComplexStages I U)
  (Rk : ∀ n : ℤ, Matrix (lIdx n) (Fin (C.rank n)) k)
  (hRk : ∀ n : ℤ, Rk (n + 1) * specDiff ρ C n (n + 1) rfl = 0)

/-- The coordinate index of `Cone(G → L)[−1]` for the specialized limit complex. Locator: tex
4385–4388. Kind: definition. -/
abbrev cIdx (m : ℤ) : Type := cIdxOf C.rank m

/-- The restriction matrix transported along `m = n`. Locator: tex 4385–4388. Kind: definition. -/
abbrev RkAt (m n : ℤ) (h : m = n) : Matrix (lIdx n) (Fin (C.rank m)) k := RkAtOf Rk m n h

/-- The differential matrix of `Cone(G → L)[−1]` over `k`. Locator: tex 4385–4388. Kind: definition.
-/
abbrev compactDiffMat (m m' : ℤ) (h : m + 1 = m') : Matrix (cIdx C m') (cIdx C m) k :=
  compactDiffMatOf (specDiff ρ C) Rk m m' h

/-- The differential matrix of the dual of `Cone(G → L)[−1]` over `k`. Locator: tex 4385–4388. Kind:
definition. -/
abbrev dualDiffMat (a b : ℤ) (h : a + 1 = b) : Matrix (cIdx C (3 - b)) (cIdx C (3 - a)) k :=
  dualDiffMatOf (specDiff ρ C) Rk a b h

/-- The matrix of the global duality map over `k`. Locator: tex 4385–4388; Nekovář, Selmer
complexes, 5.4.3. Kind: definition. -/
abbrev forwardMat (Mbg : ∀ a b : ℤ, a + b = 3 → Matrix (Fin (C.rank a)) (Fin (C.rank b)) k)
    (Mbl : ∀ a b : ℤ, Matrix (lIdx a) (lIdx b) k) (a : ℤ) :
    Matrix (cIdx C (3 - a)) (Fin (C.rank a)) k :=
  forwardMatOf Mbg Mbl Rk a

/-- **The compactly supported limit complex** `Cone(res : G → L)[−1]` of the relaxed limit Selmer
data (`compactCx`). Locator: tex 4385–4388; Nekovář, Selmer complexes, 5.4.3. Kind: definition. -/
abbrev limitCompact : GCx k :=
  compactCx (limitRelaxed (specializeComplex hI hU ρ C) (resOfMat hI hU ρ C Rk hRk)).D

/-- **The coordinates of the compactly supported limit complex**: the `G`-part as is, the `L`-part
through `lCoord`. Locator: tex 4385–4388. Kind: definition. -/
def compactCoord (m : ℤ) : (limitCompact hI hU ρ C Rk hRk).X m ≃ₗ[k] (cIdx C m → k) :=
  ((LinearEquiv.refl k (Fin (C.rank m) → k)).prodCongr (lCoord k (m - 1))).trans
    (LinearEquiv.sumArrowLequivProdArrow (Fin (C.rank m)) (lIdx (m - 1)) k k).symm

/-- The coordinates of a pair `(b, y)`. Kind: PROVED. -/
theorem compactCoord_mk (m : ℤ) (b : Fin (C.rank m) → k) (y : (splitLocalComplex k).X (m - 1)) :
    compactCoord hI hU ρ C Rk hRk m (b, y) = Sum.elim b (lCoord k (m - 1) y) := by
  funext s
  cases s <;> rfl

/-- **The coordinates of the dual complex** `Hom(Cone(G → L)[−1], k)[−3]` in degree `n`: the dual
of the standard basis of `cIdx (3 − n) → k`. Locator: tex 4385–4388. Kind: definition. -/
def dualCoord (n : ℤ) :
    (dualCx (limitCompact hI hU ρ C Rk hRk) 3).X n ≃ₗ[k] (cIdx C (3 - n) → k) :=
  dualEquivOfCoord (compactCoord hI hU ρ C Rk hRk (3 - n))

/-- Evaluation of the dual coordinates. Kind: PROVED. -/
theorem dualCoord_apply (n : ℤ) (φ : (dualCx (limitCompact hI hU ρ C Rk hRk) 3).X n)
    (j : cIdx C (3 - n)) :
    dualCoord hI hU ρ C Rk hRk n φ j =
      asDual φ ((compactCoord hI hU ρ C Rk hRk (3 - n)).symm (Pi.single j 1)) :=
  rfl

/-- The restriction in coordinates, along an index equality. Kind: PROVED. -/
theorem lCoord_res_at (m n : ℤ) (h : m = n) (x : Fin (C.rank m) → k) :
    lCoord k n ((resOfMat hI hU ρ C Rk hRk).f m n h x) = RkAt C Rk m n h *ᵥ x := by
  subst h
  exact lCoord_resOfMat hI hU ρ C Rk hRk m x

/-- **The differential of `Cone(G → L)[−1]` in coordinates** is `compactDiffMat`. Locator: tex
4385–4388; tex 4391–4451. Kind: PROVED. -/
theorem compactCoord_d (m m' : ℤ) (h : m + 1 = m') (z : (limitCompact hI hU ρ C Rk hRk).X m) :
    compactCoord hI hU ρ C Rk hRk m' ((limitCompact hI hU ρ C Rk hRk).d m m' h z) =
      compactDiffMat ρ C Rk m m' h *ᵥ compactCoord hI hU ρ C Rk hRk m z := by
  obtain ⟨b, y⟩ := z
  revert b y
  change ∀ (b : Fin (C.rank m) → k) (y : (splitLocalComplex k).X (m - 1)), _
  intro b y
  change compactCoord hI hU ρ C Rk hRk m'
      (specDiff ρ C m m' h *ᵥ b,
        ((resOfMat hI hU ρ C Rk hRk).f m (m' - 1) (by omega) b - 0 :
          (splitLocalComplex k).X (m' - 1))) =
    compactDiffMat ρ C Rk m m' h *ᵥ compactCoord hI hU ρ C Rk hRk m (b, y)
  rw [compactCoord_mk, compactCoord_mk, compactDiffMat, compactDiffMatOf, fromBlocks_mulVec,
    sub_zero, lCoord_res_at]
  simp only [Sum.elim_comp_inl, Sum.elim_comp_inr, zero_mulVec, add_zero]

/-- **The differential of the dual complex in coordinates** is `dualDiffMat`. Locator: tex
4385–4388; tex 4391–4451. Kind: PROVED. -/
theorem dualCoord_d (a b : ℤ) (h : a + 1 = b)
    (φ : (dualCx (limitCompact hI hU ρ C Rk hRk) 3).X a) :
    dualCoord hI hU ρ C Rk hRk b ((dualCx (limitCompact hI hU ρ C Rk hRk) 3).d a b h φ) =
      dualDiffMat ρ C Rk a b h *ᵥ dualCoord hI hU ρ C Rk hRk a φ := by
  funext j
  rw [dualCoord_apply, dualCx_d_apply]
  have e := dualEquivOfCoord_eval (compactCoord hI hU ρ C Rk hRk (3 - a)) (asDual φ)
    ((limitCompact hI hU ρ C Rk hRk).d (3 - b) (3 - a) (by omega)
      ((compactCoord hI hU ρ C Rk hRk (3 - b)).symm (Pi.single j 1)))
  rw [compactCoord_d, LinearEquiv.apply_symm_apply] at e
  rw [e]
  change (-(sgn a)) • (dualCoord hI hU ρ C Rk hRk a φ ⬝ᵥ
    (compactDiffMat ρ C Rk (3 - b) (3 - a) (by omega) *ᵥ Pi.single j 1)) = _
  rw [dualDiffMat, dualDiffMatOf]
  simp [Matrix.mulVec, dotProduct, Pi.single_apply, Finset.mul_sum, zsmul_eq_mul, mul_comm,
    compactDiffMat]
  simp only [mul_assoc]
  exact add_comm _ _

/-- The trace of the Selmer cup product of `(x, 0, 0)` and `(b, 0, y)`: the global pairing plus
`(−1)^a` times the local pairing of the restriction. Kind: PROVED. -/
theorem globalDuality_eval_clean {G : GCx k} (res : GHom G (splitLocalComplex k))
    (BG : GlobalTracePairing G) (B : SplitLocalPairing k) (a : ℤ) (h : a + (3 - a) = 3)
    (x : G.X a) (b : G.X (3 - a)) (w : (splitLocalComplex k).X (3 - a))
    (y : (splitLocalComplex k).X (3 - a - 1)) :
    limitCupGP res BG B a (3 - a) 3 h x b +
        (limitCupLP B (a - 1) (3 - a) (3 - 1) 0 w +
          sgn a • limitCupLP B a (3 - a - 1) (3 - 1) (res.f a a rfl x) y + 0) =
      BG a (3 - a) h x b + sgn a • B.bl a (3 - a - 1) (res.f a a rfl x) y := by
  rw [limitCupGP_apply_of_three res BG B h rfl, limitCupLP_apply_of_two B (by norm_num) _ y,
    map_zero, LinearMap.zero_apply, zero_add, add_zero]

/-- The matrix identity behind `forwardMat`. Kind: PROVED. -/
theorem forward_matrix_clean {m n l l' : Type} [Fintype m] [Fintype n] [Fintype l] [Fintype l']
    (Mg : Matrix m n k) (Ml : Matrix l l' k) (Rka : Matrix l m k) (s : ℤ) (x : m → k)
    (b : n → k) (w : l' → k) :
    x ⬝ᵥ (Mg *ᵥ b) + s • ((Rka *ᵥ x) ⬝ᵥ (Ml *ᵥ w)) =
      (Mgᵀ *ᵥ x) ⬝ᵥ b + (((s : k) • (Mlᵀ * Rka)) *ᵥ x) ⬝ᵥ w := by
  rw [mulVec_dotProduct_eq Mgᵀ, transpose_transpose, smul_mulVec, ← mulVec_mulVec,
    smul_dotProduct, mulVec_dotProduct_eq Mlᵀ, transpose_transpose, zsmul_eq_mul, smul_eq_mul]

/-- **The global duality map in coordinates** is `forwardMat`. Locator: tex 4385–4388; Nekovář,
Selmer complexes, 5.4.3. Kind: PROVED. -/
theorem dualCoord_forward
    (Mbg : ∀ a b : ℤ, a + b = 3 → Matrix (Fin (C.rank a)) (Fin (C.rank b)) k)
    (Mbl : ∀ a b : ℤ, Matrix (lIdx a) (lIdx b) k)
    (hrec : LimitReciprocity (resOfMat hI hU ρ C Rk hRk) (globalPairingOfMat hI hU ρ C Mbg)
      (localPairingOfMat Mbl))
    (a : ℤ) (x : Fin (C.rank a) → k) :
    dualCoord hI hU ρ C Rk hRk a
      ((globalDualityMap (limitPair (resOfMat hI hU ρ C Rk hRk) (globalPairingOfMat hI hU ρ C Mbg)
        (localPairingOfMat Mbl) hrec) (limitTrace k)
        (limitPair_htr (resOfMat hI hU ρ C Rk hRk) (globalPairingOfMat hI hU ρ C Mbg)
          (localPairingOfMat Mbl) hrec)).f a a rfl x) =
      forwardMat C Rk Mbg Mbl a *ᵥ x := by
  apply dualEquivOfCoord_eq
  intro z
  obtain ⟨b, y⟩ := z
  revert b y
  change ∀ (b : Fin (C.rank (3 - a)) → k) (y : (splitLocalComplex k).X (3 - a - 1)), _
  intro b y
  rw [compactCoord_mk, forwardMat, forwardMatOf, fromRows_mulVec_eq, sumElim_dotProduct]
  change limitCupGP (resOfMat hI hU ρ C Rk hRk) (globalPairingOfMat hI hU ρ C Mbg)
      (localPairingOfMat Mbl) a (3 - a) 3 (by omega) x b +
    (limitCupLP (localPairingOfMat Mbl) (a - 1) (3 - a) (3 - 1) 0 _ +
      sgn a • limitCupLP (localPairingOfMat Mbl) a (3 - a - 1) (3 - 1)
        ((resOfMat hI hU ρ C Rk hRk).f a a rfl x) y + 0) = _
  have h2 : (localPairingOfMat Mbl).bl a (3 - a - 1) ((resOfMat hI hU ρ C Rk hRk).f a a rfl x) y =
      (Rk a *ᵥ x) ⬝ᵥ (Mbl a (3 - a - 1) *ᵥ lCoord k (3 - a - 1) y) :=
    (localPairingOfMat_bl Mbl a (3 - a - 1) (by omega) _ y).trans
      (congrArg (fun v => v ⬝ᵥ (Mbl a (3 - a - 1) *ᵥ lCoord k (3 - a - 1) y))
        (lCoord_resOfMat hI hU ρ C Rk hRk a x))
  have h1 : globalPairingOfMat hI hU ρ C Mbg a (3 - a) (by omega) x b =
      x ⬝ᵥ (Mbg a (3 - a) (by omega) *ᵥ b) := rfl
  refine (globalDuality_eval_clean (resOfMat hI hU ρ C Rk hRk) (globalPairingOfMat hI hU ρ C Mbg)
    (localPairingOfMat Mbl) a (by omega) x b _ y).trans ?_
  rw [h1, h2]
  exact forward_matrix_clean (Mbg a (3 - a) (by omega)) (Mbl a (3 - a - 1)) (Rk a) (sgn a) x b
    (lCoord k (3 - a - 1) y)

/-- **The homotopy inverse of the global duality map** from matrices `Gm a` satisfying the chain
identity `hchain`: `φ ↦ Gm a (dualCoord a φ)`. Locator: tex 4385–4388 ("the integral duality maps,
their homotopy inverses"). Kind: definition. -/
def globalInverse (Gm : ∀ a : ℤ, Matrix (Fin (C.rank a)) (cIdx C (3 - a)) k)
    (hchain : ∀ a : ℤ, Gm (a + 1) * dualDiffMat ρ C Rk a (a + 1) rfl =
      specDiff ρ C a (a + 1) rfl * Gm a) :
    GHom (dualCx (limitCompact hI hU ρ C Rk hRk) 3) (specializeComplex hI hU ρ C) where
  f a b h := by
    subst h
    exact Matrix.toLin' (Gm a) ∘ₗ (dualCoord hI hU ρ C Rk hRk a).toLinearMap
  comm i i₁ j j₁ hij h₁ h₂ hj φ := by
    subst hij hj h₁
    change Gm (i + 1) *ᵥ dualCoord hI hU ρ C Rk hRk (i + 1)
        ((dualCx (limitCompact hI hU ρ C Rk hRk) 3).d i (i + 1) rfl φ) =
      specDiff ρ C i (i + 1) rfl *ᵥ (Gm i *ᵥ dualCoord hI hU ρ C Rk hRk i φ)
    rw [dualCoord_d, mulVec_mulVec, mulVec_mulVec, hchain]

/-- **The global duality map is a homotopy equivalence**, from retained matrices: a homotopy inverse
`Gm` (chain map by `hchain`) and homotopies `Hs` on `G` and `Ht` on the dual of `Cone(G → L)[−1]`
(in dual coordinates) with the matrix identities `hsrc`, `htgt`. Locator: tex 4385–4388 ("The same
retained data include the integral duality maps, their homotopy inverses, and the homotopies
expressing compatibility of duality with localization"); tex 4391–4451 (Lemma
`ex:limits-inner-limit`: every polynomial identity between the matrices survives); Nekovář, Selmer
complexes, 5.4.3. Kind: definition. -/
def globalHomotopyEquiv
    (Mbg : ∀ a b : ℤ, a + b = 3 → Matrix (Fin (C.rank a)) (Fin (C.rank b)) k)
    (Mbl : ∀ a b : ℤ, Matrix (lIdx a) (lIdx b) k)
    (hrec : LimitReciprocity (resOfMat hI hU ρ C Rk hRk) (globalPairingOfMat hI hU ρ C Mbg)
      (localPairingOfMat Mbl))
    (Gm : ∀ a : ℤ, Matrix (Fin (C.rank a)) (cIdx C (3 - a)) k)
    (Hs : ∀ a b : ℤ, b + 1 = a → Matrix (Fin (C.rank b)) (Fin (C.rank a)) k)
    (Ht : ∀ a b : ℤ, b + 1 = a → Matrix (cIdx C (3 - b)) (cIdx C (3 - a)) k)
    (hchain : ∀ a : ℤ, Gm (a + 1) * dualDiffMat ρ C Rk a (a + 1) rfl =
      specDiff ρ C a (a + 1) rfl * Gm a)
    (hsrc : ∀ a : ℤ, Gm a * forwardMat C Rk Mbg Mbl a =
      Hs (a + 1) a rfl * specDiff ρ C a (a + 1) rfl +
        specDiff ρ C (a - 1) a (by omega) * Hs a (a - 1) (by omega) + 1)
    (htgt : ∀ a : ℤ, forwardMat C Rk Mbg Mbl a * Gm a =
      Ht (a + 1) a rfl * dualDiffMat ρ C Rk a (a + 1) rfl +
        dualDiffMat ρ C Rk (a - 1) a (by omega) * Ht a (a - 1) (by omega) + 1) :
    HomotopyEquiv (specializeComplex hI hU ρ C).toCC
      (dualCx (limitCompact hI hU ρ C Rk hRk) 3).toCC where
  hom := GHom.toCC (globalDualityMap (limitPair (resOfMat hI hU ρ C Rk hRk)
    (globalPairingOfMat hI hU ρ C Mbg) (localPairingOfMat Mbl) hrec) (limitTrace k)
    (limitPair_htr (resOfMat hI hU ρ C Rk hRk) (globalPairingOfMat hI hU ρ C Mbg)
      (localPairingOfMat Mbl) hrec))
  inv := GHom.toCC (globalInverse hI hU ρ C Rk hRk Gm hchain)
  homotopyHomInvId := homotopyOfLinearIdentities _ _
    (fun a b hab => Matrix.toLin' (Hs a b hab)) (by
      intro a
      erw [toCC_d_linear (specializeComplex hI hU ρ C) a (a + 1) rfl,
        toCC_d_linear (specializeComplex hI hU ρ C) (a - 1) a (by omega)]
      apply LinearMap.ext
      intro x
      change (Fin (C.rank a) → k) at x
      change Gm a *ᵥ dualCoord hI hU ρ C Rk hRk a
          ((globalDualityMap (limitPair (resOfMat hI hU ρ C Rk hRk)
            (globalPairingOfMat hI hU ρ C Mbg) (localPairingOfMat Mbl) hrec) (limitTrace k)
            (limitPair_htr (resOfMat hI hU ρ C Rk hRk) (globalPairingOfMat hI hU ρ C Mbg)
              (localPairingOfMat Mbl) hrec)).f a a rfl x) =
        Hs (a + 1) a rfl *ᵥ (specDiff ρ C a (a + 1) rfl *ᵥ x) +
          specDiff ρ C (a - 1) a (by omega) *ᵥ (Hs a (a - 1) (by omega) *ᵥ x) + x
      rw [dualCoord_forward, mulVec_mulVec, hsrc]
      simp only [add_mulVec, mulVec_mulVec, one_mulVec])
  homotopyInvHomId := homotopyOfLinearIdentities _ _
    (fun a b hab => (dualCoord hI hU ρ C Rk hRk b).symm.toLinearMap ∘ₗ
      Matrix.toLin' (Ht a b hab) ∘ₗ (dualCoord hI hU ρ C Rk hRk a).toLinearMap) (by
      intro a
      erw [toCC_d_linear (dualCx (limitCompact hI hU ρ C Rk hRk) 3) a (a + 1) rfl,
        toCC_d_linear (dualCx (limitCompact hI hU ρ C Rk hRk) 3) (a - 1) a (by omega)]
      apply LinearMap.ext
      intro φ
      change (dualCx (limitCompact hI hU ρ C Rk hRk) 3).X a at φ
      apply (dualCoord hI hU ρ C Rk hRk a).injective
      change dualCoord hI hU ρ C Rk hRk a
          ((globalDualityMap (limitPair (resOfMat hI hU ρ C Rk hRk)
            (globalPairingOfMat hI hU ρ C Mbg) (localPairingOfMat Mbl) hrec) (limitTrace k)
            (limitPair_htr (resOfMat hI hU ρ C Rk hRk) (globalPairingOfMat hI hU ρ C Mbg)
              (localPairingOfMat Mbl) hrec)).f a a rfl
            (Gm a *ᵥ dualCoord hI hU ρ C Rk hRk a φ)) =
        dualCoord hI hU ρ C Rk hRk a
          ((dualCoord hI hU ρ C Rk hRk a).symm (Ht (a + 1) a rfl *ᵥ
              dualCoord hI hU ρ C Rk hRk (a + 1)
                ((dualCx (limitCompact hI hU ρ C Rk hRk) 3).d a (a + 1) rfl φ)) +
            (dualCx (limitCompact hI hU ρ C Rk hRk) 3).d (a - 1) a (by omega)
              ((dualCoord hI hU ρ C Rk hRk (a - 1)).symm
                (Ht a (a - 1) (by omega) *ᵥ dualCoord hI hU ρ C Rk hRk a φ)) + φ)
      rw [dualCoord_forward, map_add, map_add, LinearEquiv.apply_symm_apply, dualCoord_d,
        dualCoord_d, LinearEquiv.apply_symm_apply]
      simp only [mulVec_mulVec, htgt, add_mulVec, one_mulVec])

/-- **The global duality quasi-isomorphism of the limit pairing data from retained matrices**:
given the matrix presentation (`Rk`, `Mbg`, `Mbl` with matrix reciprocity `hM`), a homotopy
inverse `Gm` of the global duality matrices `forwardMat` and homotopies `Hs`, `Ht` satisfying the
retained identities `hchain`, `hsrc`, `htgt`, the global duality map `globalDualityMap` of
`limitPair` is a quasi-isomorphism (the hypothesis `hglob` of
`limitPairingCertificate_of_dualities`). Locator: tex 4385–4388; tex 4391–4451 (Lemma
`ex:limits-inner-limit`); Nekovář, Selmer complexes, 5.4.3. Kind: PROVED. -/
theorem globalDuality_quasiIso_ofMat
    (Mbg : ∀ a b : ℤ, a + b = 3 → Matrix (Fin (C.rank a)) (Fin (C.rank b)) k)
    (Mbl : ∀ a b : ℤ, Matrix (lIdx a) (lIdx b) k) (hM : MatReciprocity ρ C Rk Mbg Mbl)
    (Gm : ∀ a : ℤ, Matrix (Fin (C.rank a)) (cIdx C (3 - a)) k)
    (Hs : ∀ a b : ℤ, b + 1 = a → Matrix (Fin (C.rank b)) (Fin (C.rank a)) k)
    (Ht : ∀ a b : ℤ, b + 1 = a → Matrix (cIdx C (3 - b)) (cIdx C (3 - a)) k)
    (hchain : ∀ a : ℤ, Gm (a + 1) * dualDiffMat ρ C Rk a (a + 1) rfl =
      specDiff ρ C a (a + 1) rfl * Gm a)
    (hsrc : ∀ a : ℤ, Gm a * forwardMat C Rk Mbg Mbl a =
      Hs (a + 1) a rfl * specDiff ρ C a (a + 1) rfl +
        specDiff ρ C (a - 1) a (by omega) * Hs a (a - 1) (by omega) + 1)
    (htgt : ∀ a : ℤ, forwardMat C Rk Mbg Mbl a * Gm a =
      Ht (a + 1) a rfl * dualDiffMat ρ C Rk a (a + 1) rfl +
        dualDiffMat ρ C Rk (a - 1) a (by omega) * Ht a (a - 1) (by omega) + 1) :
    QuasiIso (GHom.toCC (globalDualityMap
      (limitPair (resOfMat hI hU ρ C Rk hRk) (globalPairingOfMat hI hU ρ C Mbg)
        (localPairingOfMat Mbl) (limitReciprocity_ofMat hI hU ρ C Rk hRk Mbg Mbl hM))
      (limitTrace k)
      (limitPair_htr (resOfMat hI hU ρ C Rk hRk) (globalPairingOfMat hI hU ρ C Mbg)
        (localPairingOfMat Mbl) (limitReciprocity_ofMat hI hU ρ C Rk hRk Mbg Mbl hM)))) :=
  (globalHomotopyEquiv hI hU ρ C Rk hRk Mbg Mbl
    (limitReciprocity_ofMat hI hU ρ C Rk hRk Mbg Mbl hM) Gm Hs Ht hchain hsrc htgt).quasiIso_hom

end Specialized

end ZInQ.Manuscript.RC.FibreDuality
