import ZInQKernel.Contrib.CloudB3RC53.ClearingComplex.CoordTorsion
import ZInQKernel.Contrib.CloudB3RC53.ClearingComplex.NewLocalModel

/-!
# E1b: Elliot's determinant computation, PROVED for the Knudsen–Mumford coordinate

Manuscript `diophantine_zq.tex`, proof of Proposition `ex:limits-fixed-field-clearing`, tex
L5577–5617. The coordinate parameter `c` of `CoordParam.lean` is instantiated by lane Torsion's
Knudsen–Mumford coordinate `kmCoord` of the sign-evaluated remaining complex, at the transported
cycle `z` and closed functional `μ`:

* `cOf D z μ x := kmCoord(D_x, z_x, μ_x)` (in the orientation `σBlock`), and `sdOf D z μ` the
  scalar data read off `z`, `μ` and the differentials (`z_H`, `z_B`, `C`, `μ_H`, `μ_E`, `B_H`,
  tex 5577–5584);
* `coordComputation_km` (**E1b, PROVED**): `CoordComputation` for the genuine generic patterns of
  `Patterns.lean` with `ε = −1`: where `Δ_x ≠ 0`, in the rank-one pattern
  `c_x = α_x β_x T_x`, `T = ε ∏ δ_i^{(−1)^i}`; in the acyclic pattern `α_x = 0` and `c_x = 0`.
  (Rank-one forces the remaining map `H₁ → H₂` to vanish, by the Schur determinant
  `det [[A₁, u], [v, w]] = det A₁ · h`; acyclic makes `z_x` a boundary, whose `α` is zero.)
* `clearingModel_of_km` (PROVED): RC0's `ClearingModel` from the new-local model (GLUE, consistent),
  a transported cycle and closed functional over `𝒪[G]`, and E1a (`CoordLink`, GLUE) for the
  Knudsen–Mumford coordinate.
-/

noncomputable section

namespace ZInQ.Contrib.CloudB3RC53.ClearingComplex

open Matrix ZInQ.Contrib.CloudB3RC53.Torsion
open ZInQ.Manuscript.RC ZInQ.Manuscript.RC.Wiring
open ZInQ.Manuscript.RC.Determinant (Lam OO SignGroup SmithBlocks ScalarData evK uK sgnChar
  cleanT genuinePole)

namespace BlockComplex

variable {S S' : Type} [CommRing S] [CommRing S']

/-- Coefficient change of a block complex. -/
def map (D : BlockComplex S) (f : S →+* S') : BlockComplex S' where
  m0 := D.m0
  m1 := D.m1
  m2 := D.m2
  d0 := D.d0.map f
  d1 := D.d1.map f
  d2 := D.d2.map f
  d1_d0 := by rw [← Matrix.map_mul, D.d1_d0, Matrix.map_zero _ (map_zero f)]
  d2_d1 := by rw [← Matrix.map_mul, D.d2_d1, Matrix.map_zero _ (map_zero f)]

end BlockComplex

variable {b : ℕ} (D : BlockComplex (MonoidAlgebra OO (SignGroup b)))
  (z : Fin D.m0 ⊕ Unit ⊕ Fin D.m1 → MonoidAlgebra OO (SignGroup b))
  (μ : Fin D.m1 ⊕ Unit ⊕ Fin D.m2 → MonoidAlgebra OO (SignGroup b))
  (hz : D.d1 *ᵥ z = 0) (hμ : μ ᵥ* D.d1 = 0)

/-- The sign-evaluated remaining complex over `K = Frac 𝒪`. -/
abbrev Dx (x : Addr b) : BlockComplex (FractionRing OO) := D.map (evK (sgnChar x))

include hz in
theorem hzx (x : Addr b) : (Dx D x).toFour.d1 *ᵥ (evK (sgnChar x) ∘ z) = 0 := by
  have h : (D.d1.map (evK (sgnChar x))) *ᵥ (evK (sgnChar x) ∘ z) = 0 := by
    funext i; rw [← RingHom.map_mulVec, hz]; simp
  exact h

include hμ in
theorem hμx (x : Addr b) : (evK (sgnChar x) ∘ μ) ᵥ* (Dx D x).toFour.d1 = 0 := by
  have h : (evK (sgnChar x) ∘ μ) ᵥ* (D.d1.map (evK (sgnChar x))) = 0 := by
    funext i; rw [← RingHom.map_vecMul, hμ]; simp
  exact h

/-- **The coordinate**: the Knudsen–Mumford coordinate of `[z_x] ⊗ [μ_x]` of `D_x`. -/
def cOf (x : Addr b) : FractionRing OO :=
  kmCoord (Dx D x).toFour (evK (sgnChar x) ∘ z) (evK (sgnChar x) ∘ μ) (hzx D z hz x)
    (hμx D μ hμ x) (σBlock D.m0 D.m1 D.m2)

/-- **The scalar data of the transported cycle and functional** (tex 5577–5584). -/
def sdOf (A0 : (i : ℕ) → Matrix (Fin (D.mi i)) (Fin (D.mi i)) Lam)
    (s : (i : ℕ) → Fin (D.mi i) → ℤ_[2]) (s_ne : ∀ i j, s i j ≠ 0)
    (central : ∀ i, (A0 i).map PowerSeries.constantCoeff = Matrix.diagonal (s i)) :
    ScalarData (D.toSmithBlocks (O := OO) A0 s s_ne central) where
  zH := z (Sum.inr (Sum.inl ()))
  zB := fun j => z (Sum.inl j)
  C := fun j => D.d0 (Sum.inr (Sum.inl ())) j
  μH := μ (Sum.inr (Sum.inl ()))
  μE := fun e => μ (Sum.inr (Sum.inr e))
  BH := fun j => D.d2 j (Sum.inr (Sum.inl ()))

variable (A0 : (i : ℕ) → Matrix (Fin (D.mi i)) (Fin (D.mi i)) Lam)
  (s : (i : ℕ) → Fin (D.mi i) → ℤ_[2]) (s_ne : ∀ i j, s i j ≠ 0)
  (central : ∀ i, (A0 i).map PowerSeries.constantCoeff = Matrix.diagonal (s i))

theorem alphaK_eq (x : Addr b) :
    (sdOf D z μ A0 s s_ne central).αK (evK (sgnChar x)) = (Dx D x).alphaB (evK (sgnChar x) ∘ z) :=
  rfl

theorem betaK_eq (x : Addr b) :
    (sdOf D z μ A0 s s_ne central).βK (evK (sgnChar x)) = (Dx D x).betaB (evK (sgnChar x) ∘ μ) :=
  rfl

theorem evK_det_A0 (x : Addr b) : evK (sgnChar x) D.A0.det = (Dx D x).A0.det := by
  rw [RingHom.map_det]; rfl
theorem evK_det_A1 (x : Addr b) : evK (sgnChar x) D.A1.det = (Dx D x).A1.det := by
  rw [RingHom.map_det]; rfl
theorem evK_det_A2 (x : Addr b) : evK (sgnChar x) D.A2.det = (Dx D x).A2.det := by
  rw [RingHom.map_det]; rfl

theorem cleanT_eq (x : Addr b) :
    cleanT (evK (sgnChar x)) (D.toSmithBlocks (O := OO) A0 s s_ne central) (-1) =
      -((Dx D x).A0.det * ((Dx D x).A1.det)⁻¹ * (Dx D x).A2.det) := by
  unfold cleanT
  simp only [BlockComplex.toSmithBlocks, Finset.prod_range_succ, Finset.prod_range_zero,
    one_mul, SmithBlocks.δ, map_neg, map_one]
  change -1 * ((evK (sgnChar x) D.A0.det) ^ ((-1 : ℤ) ^ 0) *
    (evK (sgnChar x) D.A1.det) ^ ((-1 : ℤ) ^ 1) * (evK (sgnChar x) D.A2.det) ^ ((-1 : ℤ) ^ 2)) = _
  rw [evK_det_A0, evK_det_A1, evK_det_A2]
  norm_num

/-! ### Rank-one forces the remaining map to vanish -/

theorem schur_unit_entry {K : Type} [Field K] {n : Type} [Fintype n] [DecidableEq n]
    (w : K) (Q : Matrix Unit n K) (A : Matrix n n K) (T : Matrix n Unit K) :
    ((of fun (_ : Unit) (_ : Unit) => w) - Q * A⁻¹ * T) () () =
      w - (fun e => Q () e) ⬝ᵥ (A⁻¹ *ᵥ fun b => T b ()) := by
  rw [Matrix.sub_apply, mul_inv_mul_apply]
  rfl

/-- **The Schur determinant**: the minor on `(B₂, H₂) × (E₁, H₁)` of `d¹` is `det A₁ · h`. -/
theorem le_rank_d1_of_hRem_ne_zero {K : Type} [Field K] (E : BlockComplex K)
    (hA1 : IsUnit E.A1.det) (hh : E.hRem ≠ 0) : E.m1 + 1 ≤ E.d1.rank := by
  let f : Fin E.m1 ⊕ Unit → Fin E.m1 ⊕ Unit ⊕ Fin E.m2 := Sum.elim Sum.inl (fun _ => Sum.inr (Sum.inl ()))
  let g : Fin E.m1 ⊕ Unit → Fin E.m0 ⊕ Unit ⊕ Fin E.m1 :=
    Sum.elim (fun e => Sum.inr (Sum.inr e)) (fun _ => Sum.inr (Sum.inl ()))
  have hM : E.d1.submatrix f g = fromBlocks E.A1 (of fun b (_ : Unit) => E.d1 (Sum.inl b)
      (Sum.inr (Sum.inl ()))) (of fun (_ : Unit) e => E.d1 (Sum.inr (Sum.inl ())) (Sum.inr (Sum.inr e)))
      (of fun _ _ => E.d1 (Sum.inr (Sum.inl ())) (Sum.inr (Sum.inl ()))) := by
    ext (i | i) (j | j) <;> rfl
  let _ := Matrix.invertibleOfIsUnitDet E.A1 hA1
  have hdet : (E.d1.submatrix f g).det = E.A1.det * E.hRem := by
    rw [hM, det_fromBlocks₁₁, Matrix.det_unique (n := Unit), Matrix.invOf_eq_nonsing_inv]
    congr 1
    exact schur_unit_entry _ _ _ _
  have hne : (E.d1.submatrix f g).det ≠ 0 := by
    rw [hdet]; exact mul_ne_zero hA1.ne_zero hh
  have := Matrix.rank_of_det_ne_zero hne
  rw [Fintype.card_sum, Fintype.card_fin, Fintype.card_unit] at this
  rw [← this]
  exact Matrix.rank_submatrix_le _ f g

variable {D}

theorem hRem_eq_zero_of_rankOne (x : Addr b) (h0 : evK (sgnChar x) D.A0.det ≠ 0)
    (h1 : evK (sgnChar x) D.A1.det ≠ 0) (h2 : evK (sgnChar x) D.A2.det ≠ 0)
    (hR : D.RankOnePattern x) : (Dx D x).hRem = 0 := by
  by_contra hh
  have hA1 : IsUnit (Dx D x).A1.det := by rw [← evK_det_A1]; exact isUnit_iff_ne_zero.mpr h1
  have hr := le_rank_d1_of_hRem_ne_zero (Dx D x) hA1 hh
  obtain ⟨e0, -, -, -⟩ := D.hdim_le_central x h0 h1 h2
  obtain ⟨-, e1, -, -⟩ := hR
  change ((D.m0 : ℤ) - (D.dx0 x).rank) = 0 at e0
  change ((D.m0 + 1 + D.m1 : ℕ) : ℤ) - (D.dx1 x).rank - (D.dx0 x).rank = 1 at e1
  change D.m1 + 1 ≤ (D.dx1 x).rank at hr
  push_cast at e1
  omega

/-! ### Acyclic makes the cycle a boundary -/

theorem alphaB_of_boundary {K : Type} [Field K] (E : BlockComplex K) (hA0 : IsUnit E.A0.det)
    (y : Fin E.m0 → K) : E.alphaB (E.d0 *ᵥ y) = 0 := by
  have hB : (E.d0 *ᵥ y) ∘ Sum.inl = E.A0 *ᵥ y := by funext j; rfl
  unfold BlockComplex.alphaB
  rw [hB, Matrix.mulVec_mulVec, nonsing_inv_mul _ hA0, Matrix.one_mulVec]
  change (fun j => E.d0 (Sum.inr (Sum.inl ())) j) ⬝ᵥ y - _ = 0
  rw [sub_self]

include hz in
theorem alpha_eq_zero_of_acyclic (x : Addr b) (h0 : evK (sgnChar x) D.A0.det ≠ 0)
    (hA : D.AcyclicPattern x) : (Dx D x).alphaB (evK (sgnChar x) ∘ z) = 0 := by
  have hA0 : IsUnit (Dx D x).A0.det := by rw [← evK_det_A0]; exact isUnit_iff_ne_zero.mpr h0
  -- the range of `d⁰_x` is the kernel of `d¹_x`
  have hle : LinearMap.range (D.dx0 x).mulVecLin ≤ LinearMap.ker (D.dx1 x).mulVecLin := by
    rintro _ ⟨y, rfl⟩
    rw [LinearMap.mem_ker, Matrix.mulVecLin_apply, Matrix.mulVecLin_apply, Matrix.mulVec_mulVec,
      D.dx1_mul_dx0, Matrix.zero_mulVec]
  have hrk := (D.dx1 x).mulVecLin.finrank_range_add_finrank_ker
  have e1 := hA 1
  change ((D.m0 + 1 + D.m1 : ℕ) : ℤ) - (D.dx1 x).rank - (D.dx0 x).rank = 0 at e1
  simp only [Module.finrank_fintype_fun_eq_card, Fintype.card_sum, Fintype.card_fin,
    Fintype.card_unit] at hrk
  have heq : LinearMap.range (D.dx0 x).mulVecLin = LinearMap.ker (D.dx1 x).mulVecLin := by
    apply Submodule.eq_of_le_of_finrank_eq hle
    change (D.dx0 x).rank = _
    change (D.dx1 x).rank + _ = _ at hrk
    push_cast at e1
    omega
  have hmem : evK (sgnChar x) ∘ z ∈ LinearMap.ker (D.dx1 x).mulVecLin := by
    rw [LinearMap.mem_ker, Matrix.mulVecLin_apply]
    exact hzx D z hz x
  rw [← heq] at hmem
  obtain ⟨y, hy⟩ := hmem
  rw [Matrix.mulVecLin_apply] at hy
  have key := alphaB_of_boundary (Dx D x) hA0 y
  have hy' : (Dx D x).d0 *ᵥ y = evK (sgnChar x) ∘ z := hy
  rw [hy'] at key
  exact key

/-! ### E1b -/

variable (D)

/-- **E1b, PROVED**: Elliot's determinant computation of the Knudsen–Mumford coordinate, for the
genuine generic patterns, with `ε = −1`. -/
theorem coordComputation_km :
    CoordComputation (D.toSmithBlocks (O := OO) A0 s s_ne central)
      (sdOf D z μ A0 s s_ne central) (-1) (cOf D z μ hz hμ) D.RankOnePattern D.AcyclicPattern := by
  refine ⟨fun x hΔ hR => ?_, fun x hΔ hA => ?_⟩
  · obtain ⟨h0, h1, h2⟩ := D.dets_of_Δ A0 s s_ne central x hΔ
    have hh := hRem_eq_zero_of_rankOne x h0 h1 h2 hR
    have hk := kmCoord_block (D := Dx D x) (evK (sgnChar x) ∘ z) (evK (sgnChar x) ∘ μ)
      (hzx D z hz x) (hμx D μ hμ x) (by rw [← evK_det_A0]; exact isUnit_iff_ne_zero.mpr h0)
      (by rw [← evK_det_A1]; exact isUnit_iff_ne_zero.mpr h1)
      (by rw [← evK_det_A2]; exact isUnit_iff_ne_zero.mpr h2)
    refine (show cOf D z μ hz hμ x = _ from hk).trans ?_
    rw [if_pos hh, alphaK_eq, betaK_eq, cleanT_eq]
    ring
  · obtain ⟨h0, h1, h2⟩ := D.dets_of_Δ A0 s s_ne central x hΔ
    have hα := alpha_eq_zero_of_acyclic z hz x h0 hA
    refine ⟨by rw [alphaK_eq]; exact hα, ?_⟩
    have hk := kmCoord_block (D := Dx D x) (evK (sgnChar x) ∘ z) (evK (sgnChar x) ∘ μ)
      (hzx D z hz x) (hμx D μ hμ x) (by rw [← evK_det_A0]; exact isUnit_iff_ne_zero.mpr h0)
      (by rw [← evK_det_A1]; exact isUnit_iff_ne_zero.mpr h1)
      (by rw [← evK_det_A2]; exact isUnit_iff_ne_zero.mpr h2)
    refine (show cOf D z μ hz hμ x = _ from hk).trans ?_
    rw [hα]
    split_ifs <;> simp

/-- **RC0's `ClearingModel` from the new-local model, a transported cycle and functional, and E1a
for the Knudsen–Mumford coordinate** (PROVED; E1b and E2 are theorems). -/
theorem clearingModel_of_km {ℓ : ℕ} (Dd : RCData ℓ)
    (h : ∃ dK hK cE tK : ℕ, ∀ Co Ce : ℤ, ∀ F : Family, Dd.FinalFamilyAt Co Ce F →
      ∃ (M : Identification2 F.b dK hK cE tK)
        (z : Fin M.D.m0 ⊕ Unit ⊕ Fin M.D.m1 → MonoidAlgebra OO (SignGroup F.b))
        (μ : Fin M.D.m1 ⊕ Unit ⊕ Fin M.D.m2 → MonoidAlgebra OO (SignGroup F.b))
        (hz : M.D.d1 *ᵥ z = 0) (hμ : μ ᵥ* M.D.d1 = 0) (κ η : MonoidAlgebra OO (SignGroup F.b)),
        ∀ (e : Addr F.b → ℕ) (g : Addr F.b → Lam), UTildeRep Dd F e g →
          CoordLink M.toIdentification.B κ η 0 e g (cOf M.D z μ hz hμ)) :
    ClearingModel Dd := by
  obtain ⟨dK, hK, cE, tK, hF⟩ := h
  exact clearingModel_of_newLocal Dd ⟨dK, hK, cE, tK, fun Co Ce F hFam => by
    obtain ⟨M, z, μ, hz, hμ, κ, η, hlink⟩ := hF Co Ce F hFam
    exact ⟨M, sdOf M.D z μ M.oldC.Ai M.s M.s_ne (central_of_full _ M.s M.central_full), κ, -1, η, cOf M.D z μ hz hμ,
      coordComputation_km M.D z μ hz hμ M.oldC.Ai M.s M.s_ne (central_of_full _ M.s M.central_full), hlink⟩⟩

/-- **The inputs of RC0's `clearingTarget_of_complex`** (the body of `ClearingInputsCx`, RC/Wiring)
from the second identification, transported cycles and functionals, and E1a (PROVED): the
Selmer-phrased identification is derived (`toSelmerIdentification`), the scalar data are read off
`z, μ`, the coordinate is the Knudsen–Mumford coordinate and E1b is `coordComputation_km`. -/
theorem clearingInputsCx_of_km {ℓ : ℕ} (Dd : RCData ℓ)
    (h : ∃ dK hK cE tK : ℕ, ∀ Co Ce : ℤ, ∀ F : Family, Dd.FinalFamilyAt Co Ce F →
      ∃ (M : Identification2 F.b dK hK cE tK)
        (z : Fin M.D.m0 ⊕ Unit ⊕ Fin M.D.m1 → MonoidAlgebra OO (SignGroup F.b))
        (μ : Fin M.D.m1 ⊕ Unit ⊕ Fin M.D.m2 → MonoidAlgebra OO (SignGroup F.b))
        (hz : M.D.d1 *ᵥ z = 0) (hμ : μ ᵥ* M.D.d1 = 0) (κ η : MonoidAlgebra OO (SignGroup F.b)),
        ∀ (e : Addr F.b → ℕ) (g : Addr F.b → Lam), UTildeRep Dd F e g →
          CoordLink M.toIdentification.B κ η 0 e g (cOf M.D z μ hz hμ)) :
    ∃ dK hK cE tK : ℕ, ∀ Co Ce : ℤ, ∀ F : Family, Dd.FinalFamilyAt Co Ce F →
      ∃ (I : SelmerIdentification F.b dK hK cE tK) (sd : ScalarData I.B)
        (κ ε η : MonoidAlgebra OO (SignGroup F.b)) (c : Addr F.b → FractionRing OO),
        CoordComputation I.B sd ε c I.D.RankOnePattern I.D.AcyclicPattern ∧
        ∀ (e : Addr F.b → ℕ) (g : Addr F.b → Lam), UTildeRep Dd F e g →
          CoordLink I.B κ η 0 e g c := by
  obtain ⟨dK, hK, cE, tK, hF⟩ := h
  refine ⟨dK, hK, cE, tK, fun Co Ce F hFam => ?_⟩
  obtain ⟨M, z, μ, hz, hμ, κ, η, hlink⟩ := hF Co Ce F hFam
  exact ⟨M.toSelmerIdentification, sdOf M.D z μ M.oldC.Ai M.s M.s_ne
      (central_of_full _ M.s M.central_full), κ, -1, η, cOf M.D z μ hz hμ,
    coordComputation_km M.D z μ hz hμ M.oldC.Ai M.s M.s_ne (central_of_full _ M.s M.central_full),
    hlink⟩

end ZInQ.Contrib.CloudB3RC53.ClearingComplex
