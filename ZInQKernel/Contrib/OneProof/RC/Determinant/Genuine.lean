import ZInQKernel.Contrib.OneProof.RC.Determinant.B3Bridge
import ZInQKernel.Contrib.OneProof.RC.Determinant.OCoeff
import ZInQKernel.Contrib.OneProof.RC.Determinant.NewLocalBlock
import ZInQKernel.Contrib.OneProof.RC.Determinant.GroupRingUnits

/-!
# (5.9) over the genuine coefficient ring `𝒪` (Lane RC7)

Instantiates the interfaces of `Pole.lean` and `Output.lean` for the genuine
`𝒪 = (Λ_{(2)})^ = lim_n (ℤ/2ⁿ)((t))` of `OModel.lean`/`OCoeff.lean` (manuscript tex 2747–2748,
3728), and states the outputs of Lemma `ex:limits-fixed-field-budget` (5.8) and Proposition
`ex:limits-fixed-field-clearing` (5.9) there.

* `genuinePole : PoleData Λ 𝒪` (`t = X`, `t⁻¹ = tInv`) and `genuineLaurent : LaurentCoeffData`
  (PROVED: the Laurent coefficients `coeffZ`, their decay, the Cauchy product with `Λ`).
* `newLocal_inv_pole_genuine` (PROVED): over `𝒪` every sign-evaluated new block `B_x = A + 2V_x`
  is invertible and its inverse has pole at most `4M` modulo `2^M`, uniformly in the number of
  blocks (5.8).
* `clearing_nodes_genuine` (PROVED from the named inputs): the shared top layer's
  `ClearingIdentity`, `PoleBound` and `BaseRegular` for the actual `f = 2^a Δ⁴`, `d = η Δ Q` in
  `𝒪[G]`.
-/

namespace ZInQ.Manuscript.RC.Determinant

/-- The pole filtration of the genuine `𝒪`: `t = X ∈ Λ`, inverse `tInv`. -/
noncomputable def genuinePole : PoleData Lam OO :=
  ⟨PowerSeries.X, tInv, algebraMap_X_mul_tInv⟩

/-- **Tex 2747–2748, 5500–5503, 5637–5639 (PROVED).**  The Laurent-coefficient realization of the
genuine `𝒪`. -/
noncomputable def genuineLaurent : LaurentCoeffData genuinePole where
  coeffZ := coeffZ
  coeffZ_add := coeffZ_add
  coeffZ_intCast_mul := coeffZ_intCast_mul
  coeffZ_algebraMap := coeffZ_algebraMap
  dvd_of_mem_poleModLE := by
    intro M L y hy i hi
    obtain ⟨a, ha⟩ := genuinePole.mem_poleModLE.1 hy
    exact two_pow_dvd_coeffZ_of_mem M L y a ha i hi
  conv := hasSum_coeffZ_mul_algebraMap
  decay := coeffZ_decay

/-- **Tex 5420–5436, 5466–5481: (5.8) over the genuine `𝒪` (PROVED).**  For the augmented new local
block `A = diag(A_q)` with `det A_q = t^{d_q} v_q + 2 w_q` (`d_q ≤ 4`, `v_q ∈ Λ^×`) and any
`B_x = A + 2V_x` with `V_x` over `Λ`: `B_x` is invertible over `𝒪`, and every entry of `B_x⁻¹` has
pole at most `4M` modulo `2^M`, for every `M`, independently of the number of blocks. -/
theorem newLocal_inv_pole_genuine {Q ι : Type*} [Fintype Q] [DecidableEq Q] [Fintype ι]
    [DecidableEq ι] (A : Q → Matrix ι ι Lam) (d : Q → ℕ) (hd : ∀ q, d q ≤ 4) (v : Q → Lamˣ)
    (w : Q → Lam) (hdet : ∀ q, (A q).det = (PowerSeries.X : Lam) ^ d q * (v q : Lam) + 2 * w q)
    (V : Matrix (ι × Q) (ι × Q) Lam) (M : ℕ) :
    let Bx : Matrix (ι × Q) (ι × Q) OO :=
      (Matrix.blockDiagonal A).map (algebraMap Lam OO) + (2 : OO) • V.map (algebraMap Lam OO)
    IsUnit Bx.det ∧ ∀ i j, Bx⁻¹ i j ∈ genuinePole.poleModLE M (4 * M) := by
  intro Bx
  have hu : IsUnit Bx.det :=
    genuinePole.newLocal_isUnit_det isUnit_one_add_two_mul_OO A d v w hdet V Bx rfl
  exact ⟨hu, genuinePole.newLocal_inv_pole A d hd v w hdet V Bx rfl hu M⟩

/-- **Tex 5420–5436, 5466–5469: (5.8) at every sign character, over the genuine `𝒪` (PROVED).**
Let the lifted family block `B` (a matrix over `Λ[G]`, tex 5416–5418) augment to `diag(A_q)`, with
`det A_q = t^{d_q} v_q + 2 w_q`, `d_q ≤ 4`, `v_q ∈ Λ^×`.  Then at every sign character `x` the
evaluation `B_x` is invertible over `𝒪` and every entry of `B_x⁻¹` has pole at most `4M` modulo `2^M`,
uniformly in the number of blocks.  (Each sign is `≡ 1 (mod 2)`, so `B_x = A + 2V_x`.) -/
theorem newLocal_family_pole_genuine {G : Type*} [CommMonoid G] {Q ι : Type*} [Fintype Q]
    [DecidableEq Q] [Fintype ι] [DecidableEq ι] (A : Q → Matrix ι ι Lam) (d : Q → ℕ)
    (hd : ∀ q, d q ≤ 4) (v : Q → Lamˣ) (w : Q → Lam)
    (hdet : ∀ q, (A q).det = (PowerSeries.X : Lam) ^ d q * (v q : Lam) + 2 * w q)
    (Bfam : Matrix (ι × Q) (ι × Q) (MonoidAlgebra Lam G))
    (hB0 : Bfam.map aug = Matrix.blockDiagonal A) (x : G →* ℤˣ) (M : ℕ) :
    IsUnit ((Bfam.map (signEval x)).map (algebraMap Lam OO)).det ∧
      ∀ i j, ((Bfam.map (signEval x)).map (algebraMap Lam OO))⁻¹ i j ∈
        genuinePole.poleModLE M (4 * M) := by
  obtain ⟨V, hV⟩ := matrix_signEval_eq_aug_add_two_smul x Bfam
  have hBx : (Bfam.map (signEval x)).map (algebraMap Lam OO) =
      (Matrix.blockDiagonal A).map (algebraMap Lam OO) + (2 : OO) • V.map (algebraMap Lam OO) := by
    rw [hV, hB0]
    ext i j
    simp [Matrix.map_apply, Matrix.add_apply, Matrix.smul_apply, map_add, map_mul, map_ofNat]
  rw [hBx]
  exact newLocal_inv_pole_genuine A d hd v w hdet V M

/-- **Proposition `ex:limits-fixed-field-clearing`, (5.9), over the genuine `𝒪` (PROVED from the
named inputs; see `clearing_nodes` for their provenance).**  For the binary family over `𝔽₂^b`
there is coefficient data `C` whose coordinates are the given `ũ_x = g_x/2^{e_x}`, with the clearing
identity, the pole bound `L_T(M) = 16(d_K+5)M` for every `M`, and a regular base with
`c = a + 4h₁ ≤ c_det = a + 4(h_K + 2c_E + 2t_K)`. -/
theorem clearing_nodes_genuine {b : ℕ}
    (B : SmithBlocks (MonoidAlgebra OO (SignGroup b)) OO) (hn : 2 < B.n)
    (haug : ∀ i, (B.A i).map aug = (B.A0 i).map (algebraMap Lam OO))
    (sd : ScalarData B) (κ ε η : MonoidAlgebra OO (SignGroup b)) (a : ℕ)
    (u : Addr b → ℕ → ℚ_[2]) (e : Addr b → ℕ) (g : Addr b → Lam)
    (hu : ∀ x j, u x j = ((PowerSeries.coeff j (g x) : ℤ_[2]) : ℚ_[2]) / 2 ^ e x)
    (RankOne Acyclic : Addr b → Prop) (hpat : ∀ x, RankOne x ∨ Acyclic x)
    (hrank : ∀ x, evK (sgnChar x) B.Δ ≠ 0 → RankOne x →
      uK (e x) (g x) = evK (sgnChar x) η * evK (sgnChar x) κ * sd.αK (evK (sgnChar x)) *
        (((2 : FractionRing OO) ^ a)⁻¹ * sd.βK (evK (sgnChar x))) * cleanT (evK (sgnChar x)) B ε)
    (hacyc : ∀ x, evK (sgnChar x) B.Δ ≠ 0 → Acyclic x →
      sd.αK (evK (sgnChar x)) = 0 ∧ uK (e x) (g x) = (0 : FractionRing OO))
    (hpole : ∀ x M i, ∀ j k,
      ((B.A i).map (signEval (sgnChar x))) j k ∈ genuinePole.poleModLE M (4 * M))
    (dK hK cE tK : ℕ) (hm : B.mTot ≤ dK + 5) (hh : B.hSmith ≤ hK + 2 * cE + 2 * tK) :
    ∃ C : ZInQ.Contrib.CloudB3RC53.CoordData b, C.u = u ∧
      ZInQ.Contrib.CloudB3RC53.ClearingIdentity C ∧
      (∀ M : ℕ, ZInQ.Contrib.CloudB3RC53.PoleBound C (16 * (dK + 5) * M) M) ∧
      ZInQ.Contrib.CloudB3RC53.BaseRegular C (a + 4 * B.hSmith) ∧
      a + 4 * B.hSmith ≤ a + 4 * (hK + 2 * cE + 2 * tK) :=
  clearing_nodes genuineLaurent B hn haug sd κ ε η a u e g hu (by simpa using two_pow_ne_zero_OO 1)
    RankOne Acyclic hpat hrank hacyc hpole dK hK cE tK hm hh

end ZInQ.Manuscript.RC.Determinant
