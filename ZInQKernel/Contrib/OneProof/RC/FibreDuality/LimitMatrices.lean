import ZInQKernel.Contrib.OneProof.RC.FibreDuality.LimitPairing

/-!
# Lane RC31, round 2, part 2: matrix presentation of the paired limit diagram

Manuscript `diophantine_zq.tex`, Lemma `ex:limits-inner-limit` (tex 4391–4451): "Each finite tuple
of matrix entries then has a compatible limit at every coefficient precision, giving matrices over
`Λ`. Every polynomial identity between the matrices survives." The retained limit diagram is a
finite matrix diagram; this file presents the restriction to the split local model, the retained
local pairing and the retained global trace pairing by matrices over the field `k`, in the
coordinates of the split model (`lIdx`, `lCoord`), and proves the chain-level reciprocity
`LimitReciprocity` from its matrix form.

* `lIdx n`, `lCoord k n`: coordinates of the split model `L = D⁰ ⊕ (F ⊕ S)[−1] ⊕ D²[−2]`.
* `resOfMat`: the restriction `G → L` of a matrix complex `G` from matrices `R n`.
* `localPairingOfMat`, `globalPairingOfMat`: the two pairings from matrices.
* `limitReciprocity_ofMat`: reciprocity from its matrix identity.

Kinds: definitions and PROVED.
-/

noncomputable section

namespace ZInQ.Manuscript.RC.FibreDuality

open CategoryTheory Matrix
open ZInQ.Contrib.CloudB3RC53.PairedFunctional ZInQ.Contrib.CloudB3RC53.SelmerDuality
open ZInQ.Contrib.RC53Assist.InnerLimit

/-- **The coordinate index of the split model in degree `n`**: `Fin 2` (`D⁰`), `Fin 2 ⊕ Fin 2`
(`F ⊕ S`), `Fin 2` (`D²`), empty otherwise (tex 4860). Kind: definition. -/
def lIdx : ℤ → Type
  | .ofNat 0 => Fin 2
  | .ofNat 1 => Fin 2 ⊕ Fin 2
  | .ofNat 2 => Fin 2
  | _ => Empty

/-- The coordinate index is finite. Kind: definition (instance). -/
instance lIdx_fintype : ∀ n : ℤ, Fintype (lIdx n)
  | .ofNat 0 => inferInstanceAs (Fintype (Fin 2))
  | .ofNat 1 => inferInstanceAs (Fintype (Fin 2 ⊕ Fin 2))
  | .ofNat 2 => inferInstanceAs (Fintype (Fin 2))
  | .ofNat (_ + 3) => inferInstanceAs (Fintype Empty)
  | .negSucc _ => inferInstanceAs (Fintype Empty)

/-- The coordinate index has decidable equality. Kind: definition (instance). -/
instance lIdx_decEq : ∀ n : ℤ, DecidableEq (lIdx n)
  | .ofNat 0 => inferInstanceAs (DecidableEq (Fin 2))
  | .ofNat 1 => inferInstanceAs (DecidableEq (Fin 2 ⊕ Fin 2))
  | .ofNat 2 => inferInstanceAs (DecidableEq (Fin 2))
  | .ofNat (_ + 3) => inferInstanceAs (DecidableEq Empty)
  | .negSucc _ => inferInstanceAs (DecidableEq Empty)

variable (k : Type) [Field k]

/-- **The coordinates of the split model**: `L^n ≃ (lIdx n → k)`. Kind: definition. -/
def lCoord : ∀ n : ℤ, (splitLocalComplex k).X n ≃ₗ[k] (lIdx n → k)
  | .ofNat 0 => LinearEquiv.refl k (Fin 2 → k)
  | .ofNat 1 => (LinearEquiv.sumArrowLequivProdArrow (Fin 2) (Fin 2) k k).symm
  | .ofNat 2 => LinearEquiv.refl k (Fin 2 → k)
  | .ofNat (m + 3) => by
    haveI : Subsingleton ((splitLocalComplex k).X (.ofNat (m + 3))) :=
      inferInstanceAs (Subsingleton PUnit)
    haveI : Subsingleton (lIdx (.ofNat (m + 3)) → k) := inferInstanceAs (Subsingleton (Empty → k))
    exact LinearEquiv.ofSubsingleton _ _
  | .negSucc m => by
    haveI : Subsingleton ((splitLocalComplex k).X (.negSucc m)) :=
      inferInstanceAs (Subsingleton PUnit)
    haveI : Subsingleton (lIdx (.negSucc m) → k) := inferInstanceAs (Subsingleton (Empty → k))
    exact LinearEquiv.ofSubsingleton _ _

variable {k}

/-- The bilinear form `v, w ↦ v ⬝ (M w)` of a matrix. Kind: definition. -/
def bilinOfMat {n m : Type} [Fintype n] [Fintype m]
    (M : Matrix n m k) : (n → k) →ₗ[k] (m → k) →ₗ[k] k :=
  LinearMap.mk₂ k (fun v w => v ⬝ᵥ (M *ᵥ w))
    (fun v v' w => by rw [add_dotProduct])
    (fun c v w => by rw [smul_dotProduct, smul_eq_mul])
    (fun v w w' => by rw [Matrix.mulVec_add, dotProduct_add])
    (fun c v w => by rw [Matrix.mulVec_smul, dotProduct_smul, smul_eq_mul])

/-- Evaluation of the bilinear form of a matrix. Kind: PROVED (definitional). -/
theorem bilinOfMat_apply {n m : Type} [Fintype n] [Fintype m]
    (M : Matrix n m k) (v : n → k) (w : m → k) : bilinOfMat M v w = v ⬝ᵥ (M *ᵥ w) :=
  rfl

/-! ### The matrix presentation over a specialized limit complex -/

section Specialized

variable {R : Type} [CommRing R] [TopologicalSpace R] [IsTopologicalRing R] [CompactSpace R]
  [T2Space R] {I : ℕ → Ideal R} {U : Ultrafilter ℕ}
  (hI : ZInQ.Manuscript.RC.Limits.IdealsTendToZero I)
  (hU : (U : Filter ℕ) ≤ Filter.cofinite) (ρ : R →+* k) (C : ComplexStages I U)

/-- The differential matrices of the specialized limit complex. Kind: definition. -/
abbrev specDiff (a b : ℤ) (hab : a + 1 = b) : Matrix (Fin (C.rank b)) (Fin (C.rank a)) k :=
  (ZInQ.Manuscript.RC.Limits.ulimMat U (fun i => C.d i a b hab)).map ρ

/-- **The restriction to the split model from matrices** `R n : lIdx n × rank n`, a chain map as
soon as `R (n + 1) ⋅ d = 0` (the split model has zero differentials). Kind: definition. -/
def resOfMat (Rk : ∀ n : ℤ, Matrix (lIdx n) (Fin (C.rank n)) k)
    (hRk : ∀ n : ℤ, Rk (n + 1) * specDiff ρ C n (n + 1) rfl = 0) :
    GHom (specializeComplex hI hU ρ C) (splitLocalComplex k) where
  f n m h := by
    subst h
    exact (lCoord k n).symm.toLinearMap ∘ₗ Matrix.toLin' (Rk n)
  comm i i₁ j j₁ hij h₁ h₂ hj x := by
    subst hij hj h₁
    have key : ∀ y : Fin (C.rank i) → k, Rk (i + 1) *ᵥ (specDiff ρ C i (i + 1) rfl *ᵥ y) = 0 :=
      fun y => by rw [Matrix.mulVec_mulVec, hRk i, Matrix.zero_mulVec]
    exact (congrArg (lCoord k (i + 1)).symm (key x)).trans (map_zero _)

/-- The restriction in the coordinates of the split model is its matrix. Kind: PROVED. -/
theorem lCoord_resOfMat (Rk : ∀ n : ℤ, Matrix (lIdx n) (Fin (C.rank n)) k)
    (hRk : ∀ n : ℤ, Rk (n + 1) * specDiff ρ C n (n + 1) rfl = 0) (n : ℤ)
    (x : Fin (C.rank n) → k) :
    lCoord k n ((resOfMat hI hU ρ C Rk hRk).f n n rfl x) = Rk n *ᵥ x := by
  change lCoord k n ((lCoord k n).symm (Rk n *ᵥ x)) = _
  rw [LinearEquiv.apply_symm_apply]

/-- **The retained global trace pairing from matrices** `M a b : rank a × rank b`. Kind:
definition. -/
def globalPairingOfMat (Mbg : ∀ a b : ℤ, a + b = 3 → Matrix (Fin (C.rank a)) (Fin (C.rank b)) k) :
    GlobalTracePairing (specializeComplex hI hU ρ C) :=
  fun a b h => bilinOfMat (Mbg a b h)

end Specialized

/-- **The retained local pairing from matrices** `M a b : lIdx a × lIdx b` (in the coordinates of
the split model). Kind: definition. -/
def localPairingOfMat (Mbl : ∀ a b : ℤ, Matrix (lIdx a) (lIdx b) k) : SplitLocalPairing k where
  b02 := bilinOfMat (Mbl 0 2)
  b11 := (bilinOfMat (Mbl 1 1)).compl₁₂ (lCoord k 1).toLinearMap (lCoord k 1).toLinearMap
  b20 := bilinOfMat (Mbl 2 0)

/-- Moving a matrix across the dot product. Kind: PROVED. -/
theorem mulVec_dotProduct_eq {n m : Type} [Fintype n] [Fintype m] (D : Matrix m n k) (x : n → k)
    (u : m → k) : (D *ᵥ x) ⬝ᵥ u = x ⬝ᵥ (Dᵀ *ᵥ u) := by
  rw [Matrix.dotProduct_mulVec, Matrix.vecMul_transpose]

/-- Outside degrees `0, 1, 2` the split model has no coordinates. Kind: PROVED. -/
theorem lIdx_isEmpty (a : ℤ) (h0 : a ≠ 0) (h1 : a ≠ 1) (h2 : a ≠ 2) : IsEmpty (lIdx a) := by
  rcases a with ((_ | _ | _ | a) | a)
  · exact absurd rfl h0
  · exact absurd rfl h1
  · exact absurd rfl h2
  · exact inferInstanceAs (IsEmpty Empty)
  · exact inferInstanceAs (IsEmpty Empty)

/-- Outside degrees `0, 1, 2` the local pairing vanishes. Kind: PROVED. -/
theorem SplitLocalPairing.bl_eq_zero (B : SplitLocalPairing k) (a b : ℤ) (h0 : a ≠ 0)
    (h1 : a ≠ 1) (h2 : a ≠ 2) : B.bl a b = 0 := by
  rcases a with ((_ | _ | _ | a) | a)
  · exact absurd rfl h0
  · exact absurd rfl h1
  · exact absurd rfl h2
  · rfl
  · rfl

/-- The local pairing of matrices in coordinates, in every degree of total degree two. Kind:
PROVED. -/
theorem localPairingOfMat_bl (Mbl : ∀ a b : ℤ, Matrix (lIdx a) (lIdx b) k) (a b : ℤ)
    (h : a + b = 2) (x : (splitLocalComplex k).X a) (y : (splitLocalComplex k).X b) :
    (localPairingOfMat Mbl).bl a b x y = lCoord k a x ⬝ᵥ (Mbl a b *ᵥ lCoord k b y) := by
  by_cases h0 : a = 0
  · subst h0
    have hb : b = 2 := by omega
    subst hb
    exact bilinOfMat_apply _ _ _
  · by_cases h1 : a = 1
    · subst h1
      have hb : b = 1 := by omega
      subst hb
      show bilinOfMat (Mbl 1 1) (lCoord k 1 x) (lCoord k 1 y) = _
      exact bilinOfMat_apply _ _ _
    · by_cases h2 : a = 2
      · subst h2
        have hb : b = 0 := by omega
        subst hb
        exact bilinOfMat_apply _ _ _
      · have := lIdx_isEmpty a h0 h1 h2
        rw [SplitLocalPairing.bl_eq_zero _ a b h0 h1 h2, LinearMap.zero_apply,
          LinearMap.zero_apply]
        exact (Fintype.sum_empty _).symm

/-! ### Reciprocity from its matrix identity -/

section Reciprocity

variable {R : Type} [CommRing R] [TopologicalSpace R] [IsTopologicalRing R] [CompactSpace R]
  [T2Space R] {I : ℕ → Ideal R} {U : Ultrafilter ℕ}
  (hI : ZInQ.Manuscript.RC.Limits.IdealsTendToZero I)
  (hU : (U : Filter ℕ) ≤ Filter.cofinite) (ρ : R →+* k) (C : ComplexStages I U)

/-- **The matrix form of chain-level reciprocity**: for `a + b = 2`,
`dᵀ M_{a+1,b} + (−1)^a M_{a,b+1} d + Rᵀ β R = 0`. Kind: definition (hypothesis). -/
def MatReciprocity (Rk : ∀ n : ℤ, Matrix (lIdx n) (Fin (C.rank n)) k)
    (Mbg : ∀ a b : ℤ, a + b = 3 → Matrix (Fin (C.rank a)) (Fin (C.rank b)) k)
    (Mbl : ∀ a b : ℤ, Matrix (lIdx a) (lIdx b) k) : Prop :=
  ∀ (a b : ℤ) (h : a + b = 2),
    (specDiff ρ C a (a + 1) rfl)ᵀ * Mbg (a + 1) b (by omega) +
        sgn a • (Mbg a (b + 1) (by omega) * specDiff ρ C b (b + 1) rfl) +
        (Rk a)ᵀ * Mbl a b * Rk b = 0

omit [IsTopologicalRing R] [CompactSpace R] [T2Space R] in
/-- Reciprocity from its matrix identity, on coordinate vectors. Kind: PROVED. -/
theorem recip_clean (Rk : ∀ n : ℤ, Matrix (lIdx n) (Fin (C.rank n)) k)
    (Mbg : ∀ a b : ℤ, a + b = 3 → Matrix (Fin (C.rank a)) (Fin (C.rank b)) k)
    (Mbl : ∀ a b : ℤ, Matrix (lIdx a) (lIdx b) k) (hM : MatReciprocity ρ C Rk Mbg Mbl)
    (a b : ℤ) (h : a + b = 2) (x : Fin (C.rank a) → k) (y : Fin (C.rank b) → k) :
    (specDiff ρ C a (a + 1) rfl *ᵥ x) ⬝ᵥ (Mbg (a + 1) b (by omega) *ᵥ y) +
        sgn a • (x ⬝ᵥ (Mbg a (b + 1) (by omega) *ᵥ (specDiff ρ C b (b + 1) rfl *ᵥ y))) =
      -((Rk a *ᵥ x) ⬝ᵥ (Mbl a b *ᵥ (Rk b *ᵥ y))) := by
  have e := congrArg (fun M => x ⬝ᵥ (M *ᵥ y)) (hM a b h)
  simp only [Matrix.add_mulVec, Matrix.smul_mulVec, dotProduct_add, dotProduct_smul,
    Matrix.zero_mulVec, dotProduct_zero, ← Matrix.mulVec_mulVec] at e
  rw [mulVec_dotProduct_eq, mulVec_dotProduct_eq (Rk a)]
  simp only [zsmul_eq_mul] at e ⊢
  linear_combination e

/-- **Chain-level reciprocity from its matrix identity.** Kind: PROVED. -/
theorem limitReciprocity_ofMat (Rk : ∀ n : ℤ, Matrix (lIdx n) (Fin (C.rank n)) k)
    (hRk : ∀ n : ℤ, Rk (n + 1) * specDiff ρ C n (n + 1) rfl = 0)
    (Mbg : ∀ a b : ℤ, a + b = 3 → Matrix (Fin (C.rank a)) (Fin (C.rank b)) k)
    (Mbl : ∀ a b : ℤ, Matrix (lIdx a) (lIdx b) k) (hM : MatReciprocity ρ C Rk Mbg Mbl) :
    LimitReciprocity (resOfMat hI hU ρ C Rk hRk) (globalPairingOfMat hI hU ρ C Mbg)
      (localPairingOfMat Mbl) := by
  intro a b h
  have key := recip_clean ρ C Rk Mbg Mbl hM a b h
  intro x y
  rw [localPairingOfMat_bl Mbl a b h]
  revert x y
  change ∀ (x : Fin (C.rank a) → k) (y : Fin (C.rank b) → k), _
  intro x y
  rw [lCoord_resOfMat, lCoord_resOfMat]
  exact key x y

end Reciprocity

end ZInQ.Manuscript.RC.FibreDuality
