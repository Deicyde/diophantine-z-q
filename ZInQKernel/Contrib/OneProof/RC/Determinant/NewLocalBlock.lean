import ZInQKernel.Contrib.OneProof.RC.Determinant.Pole
import Mathlib.Data.Matrix.Block
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.NumberTheory.Padics.RingHoms

/-!
# The new local blocks and the pole bound (5.8) (Lane RC7)

Manuscript `diophantine_zq.tex` (11/5; identical in Version 19), Lemma
`ex:limits-fixed-field-budget`, tex 5239–5249, 5420–5436 and 5456–5483.

After augmentation every graph prime `q` is unramified, and the block of the family differential
containing the local quotients has `B_0 = A = diag(A_q)`, `T_0 = 0`.  Here `A_q` is the direct sum of
the two rank-two singular differentials at the conjugate graph places.  This file proves:

* the residual calculation: modulo two the scalar entries of `A_q` are `t` and `-t/(1+t)`, so
  `det Ā_q = t⁴/(1+t)²` (tex 5456–5463); the Euler-factor form `ē = (1+t) + (1+t)⁻¹ = t²/(1+t)` and
  `l̄ = ē² = t⁴/(1+t)²` in characteristic two (tex 5243–5246, 4203, 4321–4322);
* the decomposition `det A_q = t^{d_q} v_q + 2 w_q` with `d_q = 4`, `v_q = (1+t)^{-2}` a power-series
  unit, as soon as `det A_q ≡ t⁴/(1+t)² (mod 2)` (tex 5428);
* with `C_q = adj(A_q)/(t^{d_q} v_q)`: `A_q C_q = 1 + 2 w_q/(t^{d_q} v_q)` (tex 5470–5472); for the
  block-diagonal `C` and any sign evaluation `B_x = A + 2 V_x` (tex 5466–5469),
  `B_x C = 1 + 2 F_x` with every entry of `C` and `F_x` of Laurent order at least `-4`
  (tex 5431, 5473–5476); hence (5.8): every entry of `B_x⁻¹`, and of the surviving Schur
  differential `P_x - Q_x B_x⁻¹ T_x`, has pole at most `4M` modulo `2^M`, uniformly in the number of
  blocks (tex 5434–5436, 5476–5481).

Everything here is PROVED, over the interface `PoleData` of `Pole.lean` (a ring map `Λ → O` in which
`t` becomes invertible).
-/

namespace ZInQ.Manuscript.RC.Determinant

open Matrix

/-! ### Residual calculations (tex 5243–5249, 5456–5465) -/

section Residual

variable {k : Type*} [CommRing k]

/-- **Tex 5456–5463 (PROVED).**  Modulo two, `A_q` is the direct sum of the two rank-two singular
differentials `z Φ̄ - 1` and `z⁻¹ Φ̄ - 1` at the conjugate graph places, where `z = 1 + t` is the
Frobenius scalar and `Φ̄ = 1` because `E[2]` is trivial.  Its scalar entries are `t` and
`z⁻¹ - 1 = -t/(1+t)`, and `det Ā_q · (1+t)² = t⁴`, i.e. `det Ā_q = t⁴/(1+t)²`. -/
theorem residual_det_newLocal (t : k) (z : kˣ) (hz : (z : k) = 1 + t) :
    (Matrix.fromBlocks ((z : k) • (1 : Matrix (Fin 2) (Fin 2) k) - 1) 0 0
        (((z⁻¹ : kˣ) : k) • (1 : Matrix (Fin 2) (Fin 2) k) - 1)).det * (z : k) ^ 2 = t ^ 4 := by
  rw [det_fromBlocks_zero₂₁]
  have h1 : ((z : k) • (1 : Matrix (Fin 2) (Fin 2) k) - 1) = Matrix.diagonal fun _ => (z : k) - 1 := by
    ext i j; by_cases h : i = j <;> simp [h]
  have h2 : (((z⁻¹ : kˣ) : k) • (1 : Matrix (Fin 2) (Fin 2) k) - 1) =
      Matrix.diagonal fun _ => ((z⁻¹ : kˣ) : k) - 1 := by
    ext i j; by_cases h : i = j <;> simp [h]
  rw [h1, h2, det_diagonal, det_diagonal]
  simp only [Fin.prod_univ_two]
  have hzz : ((z⁻¹ : kˣ) : k) * (z : k) = 1 := Units.inv_mul z
  have : (((z⁻¹ : kˣ) : k) - 1) * (z : k) = -t := by
    rw [sub_mul, hzz, one_mul, hz]; ring
  calc ((z : k) - 1) * ((z : k) - 1) * ((((z⁻¹ : kˣ) : k) - 1) * (((z⁻¹ : kˣ) : k) - 1)) * (z : k) ^ 2
      = ((z : k) - 1) ^ 2 * ((((z⁻¹ : kˣ) : k) - 1) * (z : k)) ^ 2 := by ring
    _ = t ^ 4 := by rw [this, hz]; ring

/-- **Tex 4203 and 5243–5246 (PROVED).**  In characteristic two, with `z = 1 + t` a unit, the point
factor reduces to `ē = z + z⁻¹` and `ē · (1 + t) = t²`, i.e. `ē = t²/(1+t)`; hence
`ē² · (1+t)² = t⁴`, i.e. `l̄ = ē² = t⁴/(1+t)²`. -/
theorem residual_euler_factor [CharP k 2] (t : k) (z : kˣ) (hz : (z : k) = 1 + t) :
    ((z : k) + ((z⁻¹ : kˣ) : k)) * (z : k) = t ^ 2 ∧
      ((z : k) + ((z⁻¹ : kˣ) : k)) ^ 2 * (z : k) ^ 2 = t ^ 4 := by
  have h2 : (2 : k) = 0 := CharP.cast_eq_zero k 2
  have hzz : ((z⁻¹ : kˣ) : k) * (z : k) = 1 := Units.inv_mul z
  have hmain : ((z : k) + ((z⁻¹ : kˣ) : k)) * (z : k) = t ^ 2 := by
    rw [add_mul, hzz, hz]
    have : (1 + t) * (1 + t) + 1 = t ^ 2 + 2 * (1 + t) := by ring
    rw [this, h2, zero_mul, add_zero]
  refine ⟨hmain, ?_⟩
  calc ((z : k) + ((z⁻¹ : kˣ) : k)) ^ 2 * (z : k) ^ 2
      = (((z : k) + ((z⁻¹ : kˣ) : k)) * (z : k)) ^ 2 := by ring
    _ = t ^ 4 := by rw [hmain]; ring

/-- **Tex 4214–4219 (PROVED, the residual consequence used at tex 5242–5246).**  The exact Euler
factor identity `q² l_q = e_q² + (q-1)(q-1-(z+z⁻¹)e_q)` gives `l̄_q = ē_q²` modulo two, since `q`
is odd. -/
theorem residual_l_eq_e_sq [CharP k 2] (q l e s : k) (hq : q = 1)
    (hid : q ^ 2 * l = e ^ 2 + (q - 1) * (q - 1 - s * e)) : l = e ^ 2 := by
  subst hq; simpa using hid

end Residual

/-! ### The decomposition `det A_q = t^{d_q} v_q + 2 w_q` (tex 5428) -/

/-- **Tex 5428 (PROVED).**  An element of `ℤ₂[[t]]` whose reduction modulo two is zero is twice a
power series: the kernel of `ℤ₂[[t]] → 𝔽₂[[t]]` is `2 ℤ₂[[t]]`. -/
theorem powerSeries_eq_two_mul_of_map_eq_zero (f : PowerSeries ℤ_[2])
    (hf : PowerSeries.map (PadicInt.toZMod (p := 2)) f = 0) :
    ∃ g : PowerSeries ℤ_[2], f = 2 * g := by
  have hc : ∀ n, ∃ b : ℤ_[2], PowerSeries.coeff n f = 2 * b := by
    intro n
    have h0 : PadicInt.toZMod (PowerSeries.coeff n f) = 0 := by
      have := congrArg (PowerSeries.coeff n) hf
      simpa [PowerSeries.coeff_map] using this
    have hmem : PowerSeries.coeff n f ∈ IsLocalRing.maximalIdeal ℤ_[2] := by
      rw [← PadicInt.ker_toZMod]; exact h0
    rw [PadicInt.maximalIdeal_eq_span_p, Ideal.mem_span_singleton] at hmem
    obtain ⟨b, hb⟩ := hmem
    exact ⟨b, by simpa using hb⟩
  choose b hb using hc
  refine ⟨PowerSeries.mk b, ?_⟩
  refine PowerSeries.ext fun n => ?_
  rw [hb n, two_mul (PowerSeries.mk b), map_add, PowerSeries.coeff_mk, two_mul]

/-- **Tex 5428 and 5456–5464 (PROVED).**  If the residual determinant of `A_q` is `t⁴/(1+t)²`
(that is, `det A_q · (1+t)²` reduces to `t⁴` modulo two), then `det A_q = t^{d_q} v_q + 2 w_q` with
`d_q = 4` and `v_q = (1+t)^{-2}` a unit of `ℤ₂[[t]]`: the residual `t`-order is exactly four,
uniformly in `q` and in the number of graph primes. -/
theorem det_decomposition (δ : PowerSeries ℤ_[2])
    (hres : PowerSeries.map (PadicInt.toZMod (p := 2)) (δ * (1 + PowerSeries.X) ^ 2) =
      PowerSeries.map (PadicInt.toZMod (p := 2)) (PowerSeries.X ^ 4)) :
    ∃ (v : (PowerSeries ℤ_[2])ˣ) (w : PowerSeries ℤ_[2]),
      ((v : PowerSeries ℤ_[2]) * (1 + PowerSeries.X) ^ 2 = 1) ∧
      δ = PowerSeries.X ^ 4 * (v : PowerSeries ℤ_[2]) + 2 * w := by
  have hu : IsUnit ((1 + PowerSeries.X : PowerSeries ℤ_[2]) ^ 2) := by
    refine IsUnit.pow 2 ?_
    rw [PowerSeries.isUnit_iff_constantCoeff]; simp
  set u : (PowerSeries ℤ_[2])ˣ := hu.unit with hu_def
  set vv : PowerSeries ℤ_[2] := ((u⁻¹ : (PowerSeries ℤ_[2])ˣ) : PowerSeries ℤ_[2]) with hvv
  refine ⟨u⁻¹, ?_⟩
  have hv : vv * (1 + PowerSeries.X) ^ 2 = 1 := by
    have : ((u : (PowerSeries ℤ_[2])ˣ) : PowerSeries ℤ_[2]) = (1 + PowerSeries.X) ^ 2 := rfl
    rw [hvv, ← this, Units.inv_mul]
  obtain ⟨g, hg⟩ := powerSeries_eq_two_mul_of_map_eq_zero
    ((δ * (1 + PowerSeries.X) ^ 2 - PowerSeries.X ^ 4) * vv)
    (by rw [map_mul, map_sub, hres, sub_self, zero_mul])
  refine ⟨g, hv, ?_⟩
  have h1 : δ = (δ * (1 + PowerSeries.X) ^ 2) * vv := by
    rw [mul_assoc, mul_comm ((1 + PowerSeries.X) ^ 2), hv, mul_one]
  calc δ = (δ * (1 + PowerSeries.X) ^ 2 - PowerSeries.X ^ 4) * vv + PowerSeries.X ^ 4 * vv := by
        rw [sub_mul, ← h1]; ring
    _ = _ := by rw [hg]; ring

/-! ### The approximate inverse `C` and the pole bound (5.8) -/

namespace PoleData

variable {Λ O : Type*} [CommRing Λ] [CommRing O] [Algebra Λ O] (D : PoleData Λ O)

/-- Tex 5428–5430: `C_q = adj(A_q)/(t^{d_q} v_q)`, computed in `O` where `t` is invertible. -/
noncomputable def approxInv {ι : Type*} [Fintype ι] [DecidableEq ι] (A : Matrix ι ι Λ) (d : ℕ)
    (v : Λˣ) : Matrix ι ι O :=
  (D.tinv ^ d * algebraMap Λ O ((v⁻¹ : Λˣ) : Λ)) • (A.map (algebraMap Λ O)).adjugate

/-- **Tex 5470–5472 (PROVED).**  If `det A_q = t^{d_q} v_q + 2 w_q` then
`A_q C_q = 1 + 2 w_q/(t^{d_q} v_q)`. -/
theorem mul_approxInv {ι : Type*} [Fintype ι] [DecidableEq ι] (A : Matrix ι ι Λ) (d : ℕ) (v : Λˣ)
    (w : Λ) (hdet : A.det = D.tΛ ^ d * v + 2 * w) :
    A.map (algebraMap Λ O) * D.approxInv A d v =
      1 + (2 : O) • ((D.tinv ^ d * algebraMap Λ O ((v⁻¹ : Λˣ) : Λ) * algebraMap Λ O w) •
        (1 : Matrix ι ι O)) := by
  rw [approxInv, Matrix.mul_smul, mul_adjugate, ← RingHom.mapMatrix_apply, ← RingHom.map_det, hdet,
    smul_smul]
  have ht : algebraMap Λ O D.tΛ * D.tinv = 1 := D.mul_tinv
  have hv : algebraMap Λ O (v : Λ) * algebraMap Λ O ((v⁻¹ : Λˣ) : Λ) = 1 := by
    rw [← map_mul, Units.mul_inv, map_one]
  have : D.tinv ^ d * algebraMap Λ O ((v⁻¹ : Λˣ) : Λ) *
      algebraMap Λ O (D.tΛ ^ d * (v : Λ) + 2 * w) =
      1 + 2 * (D.tinv ^ d * algebraMap Λ O ((v⁻¹ : Λˣ) : Λ) * algebraMap Λ O w) := by
    simp only [map_add, map_mul, map_pow, map_ofNat]
    calc D.tinv ^ d * algebraMap Λ O ((v⁻¹ : Λˣ) : Λ) *
          ((algebraMap Λ O D.tΛ) ^ d * algebraMap Λ O (v : Λ) + 2 * algebraMap Λ O w)
        = (algebraMap Λ O D.tΛ * D.tinv) ^ d *
            (algebraMap Λ O (v : Λ) * algebraMap Λ O ((v⁻¹ : Λˣ) : Λ)) +
          2 * (D.tinv ^ d * algebraMap Λ O ((v⁻¹ : Λˣ) : Λ) * algebraMap Λ O w) := by ring
      _ = _ := by rw [ht, hv, one_pow, one_mul]
  rw [this, add_smul, one_smul, smul_smul]

theorem approxInv_mem_poleLE {ι : Type*} [Fintype ι] [DecidableEq ι] (A : Matrix ι ι Λ) (d : ℕ)
    (v : Λˣ) : ∀ i j, D.approxInv A d v i j ∈ D.poleLE d := by
  intro i j
  rw [approxInv, Matrix.smul_apply, smul_eq_mul, ← RingHom.mapMatrix_apply, ← RingHom.map_adjugate,
    RingHom.mapMatrix_apply, Matrix.map_apply]
  have := D.mul_mem_poleLE (D.tinv_pow_mem_poleLE d)
    (D.mul_mem_poleLE (D.algebraMap_mem_poleLE ((v⁻¹ : Λˣ) : Λ))
      (D.algebraMap_mem_poleLE (A.adjugate i j)))
  simpa [mul_assoc] using this

/-- **Tex 5420–5436, 5466–5481: the pole bound (5.8) (PROVED).**  Let the augmented new local block be
`A = diag(A_q)` (`q` ranging over an arbitrary finite set `Q` of graph primes) with
`det A_q = t^{d_q} v_q + 2 w_q`, `d_q ≤ 4`, `v_q` a power-series unit.  Let `B_x = A + 2 V_x` be any
matrix of this shape with `V_x` a power-series matrix (every sign evaluation of the family block has
this shape, tex 5466–5469) and suppose `B_x` is invertible.  Then for every precision `M`, every entry
of `B_x⁻¹` has pole at most `4M` modulo `2^M`, independently of the number of blocks. -/
theorem newLocal_inv_pole {Q ι : Type*} [Fintype Q] [DecidableEq Q] [Fintype ι] [DecidableEq ι]
    (A : Q → Matrix ι ι Λ) (d : Q → ℕ) (hd : ∀ q, d q ≤ 4) (v : Q → Λˣ) (w : Q → Λ)
    (hdet : ∀ q, (A q).det = D.tΛ ^ d q * v q + 2 * w q)
    (V : Matrix (ι × Q) (ι × Q) Λ) (Bx : Matrix (ι × Q) (ι × Q) O)
    (hBx : Bx = (blockDiagonal A).map (algebraMap Λ O) + (2 : O) • V.map (algebraMap Λ O))
    (hB : IsUnit Bx.det) (M : ℕ) : ∀ i j, Bx⁻¹ i j ∈ D.poleModLE M (4 * M) := by
  classical
  set C : Matrix (ι × Q) (ι × Q) O := blockDiagonal fun q => D.approxInv (A q) (d q) (v q)
  set W : Matrix (ι × Q) (ι × Q) O := blockDiagonal fun q =>
    (D.tinv ^ d q * algebraMap Λ O (((v q)⁻¹ : Λˣ) : Λ) * algebraMap Λ O (w q)) • (1 : Matrix ι ι O)
  set F : Matrix (ι × Q) (ι × Q) O := W + V.map (algebraMap Λ O) * C
  have hAC : (blockDiagonal A).map (algebraMap Λ O) * C = 1 + (2 : O) • W := by
    simp only [C, W]
    rw [blockDiagonal_map _ _ (map_zero _), ← blockDiagonal_mul]
    simp only [D.mul_approxInv (A _) (d _) (v _) (w _) (hdet _)]
    ext ⟨i, q⟩ ⟨j, q'⟩
    by_cases h : q = q'
    · subst h; by_cases hij : i = j <;> simp [blockDiagonal_apply_eq, hij]
    · simp [blockDiagonal_apply_ne _ _ _ h, h]
  have hBC : Bx * C = 1 + (2 : O) • F := by
    rw [hBx, Matrix.add_mul, hAC, Matrix.smul_mul]
    simp only [F, smul_add]; abel
  have hC : ∀ i j, C i j ∈ D.poleLE 4 := by
    rintro ⟨i, q⟩ ⟨j, q'⟩
    simp only [C, blockDiagonal_apply]
    split_ifs with h
    · subst h; exact D.poleLE_mono (hd q) (D.approxInv_mem_poleLE _ _ _ i j)
    · exact D.zero_mem_poleLE 4
  have hW : ∀ i j, W i j ∈ D.poleLE 4 := by
    rintro ⟨i, q⟩ ⟨j, q'⟩
    simp only [W, blockDiagonal_apply]
    split_ifs with h
    · subst h
      rw [Matrix.smul_apply, smul_eq_mul]
      refine D.poleLE_mono (hd q) ?_
      have h1 : (1 : Matrix ι ι O) i j ∈ D.poleLE 0 := D.one_mem_poleLE_entries i j
      have := D.mul_mem_poleLE (D.mul_mem_poleLE (D.mul_mem_poleLE (D.tinv_pow_mem_poleLE (d q))
        (D.algebraMap_mem_poleLE (((v q)⁻¹ : Λˣ) : Λ))) (D.algebraMap_mem_poleLE (w q))) h1
      simpa using this
    · exact D.zero_mem_poleLE 4
  have hF : ∀ i j, F i j ∈ D.poleLE 4 := by
    intro i j
    refine Submodule.add_mem _ (hW i j) ?_
    have hV : ∀ i j, V.map (algebraMap Λ O) i j ∈ D.poleLE 0 := fun i j =>
      D.algebraMap_mem_poleLE (V i j)
    simpa using D.matMul_mem_poleLE _ _ hV hC i j
  have := D.inv_entry_mem_poleModLE Bx C F hB hBC hC hF M
  simpa [mul_comm] using this

/-- **Tex 5479–5481 (PROVED).**  The surviving Schur differential `P_x - Q_x B_x⁻¹ T_x` after
cancelling the new local block has every entry of pole at most `4M` modulo `2^M`, uniformly in the
number of blocks, when `P_x, Q_x, T_x` are power-series matrices. -/
theorem newLocal_schur_pole {Q ι l l' : Type*} [Fintype Q] [DecidableEq Q] [Fintype ι]
    [DecidableEq ι] [Fintype l]
    (A : Q → Matrix ι ι Λ) (d : Q → ℕ) (hd : ∀ q, d q ≤ 4) (v : Q → Λˣ) (w : Q → Λ)
    (hdet : ∀ q, (A q).det = D.tΛ ^ d q * v q + 2 * w q)
    (V : Matrix (ι × Q) (ι × Q) Λ) (Bx : Matrix (ι × Q) (ι × Q) O)
    (hBx : Bx = (blockDiagonal A).map (algebraMap Λ O) + (2 : O) • V.map (algebraMap Λ O))
    (hB : IsUnit Bx.det) (P : Matrix l' l Λ) (Qm : Matrix l' (ι × Q) Λ) (T : Matrix (ι × Q) l Λ)
    (M : ℕ) :
    ∀ i j, (P.map (algebraMap Λ O) - Qm.map (algebraMap Λ O) * Bx⁻¹ * T.map (algebraMap Λ O)) i j ∈
      D.poleModLE M (4 * M) :=
  D.schur_entry_mem_poleModLE _ _ _ Bx (fun i j => D.algebraMap_mem_poleLE (P i j))
    (fun i j => D.algebraMap_mem_poleLE (Qm i j)) (fun i j => D.algebraMap_mem_poleLE (T i j))
    (D.newLocal_inv_pole A d hd v w hdet V Bx hBx hB M)

/-- **Tex 5466–5469, 5511–5512 (PROVED).**  In a ring where every `1 + 2y` is a unit and `t` is
invertible (the genuine `𝒪`: a local ring with `2` in its maximal ideal), every matrix
`B_x = A + 2 V_x` of the shape of `newLocal_inv_pole` is invertible: `B_x C = 1 + 2F` and both
`det(1 + 2F)` and `det C` are units. -/
theorem newLocal_isUnit_det {Q ι : Type*} [Fintype Q] [DecidableEq Q] [Fintype ι] [DecidableEq ι]
    (h2 : ∀ y : O, IsUnit (1 + 2 * y))
    (A : Q → Matrix ι ι Λ) (d : Q → ℕ) (v : Q → Λˣ) (w : Q → Λ)
    (hdet : ∀ q, (A q).det = D.tΛ ^ d q * v q + 2 * w q)
    (V : Matrix (ι × Q) (ι × Q) Λ) (Bx : Matrix (ι × Q) (ι × Q) O)
    (hBx : Bx = (blockDiagonal A).map (algebraMap Λ O) + (2 : O) • V.map (algebraMap Λ O)) :
    IsUnit Bx.det := by
  classical
  -- `det (1 + 2 G)` is `1 + 2 y` for every square matrix `G`
  have hdet12 : ∀ {κ : Type _} [Fintype κ] [DecidableEq κ] (G : Matrix κ κ O),
      IsUnit (1 + (2 : O) • G).det := by
    intro κ _ _ G
    let π := Ideal.Quotient.mk (Ideal.span {(2 : O)})
    have hπ : π (1 + (2 : O) • G).det = π 1 := by
      rw [RingHom.map_det, RingHom.mapMatrix_apply]
      have : (1 + (2 : O) • G).map π = 1 := by
        ext i j
        have h2z : π 2 = 0 := Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.subset_span rfl)
        by_cases h : i = j <;> simp [Matrix.one_apply, h, h2z, π]
      rw [this, det_one, map_one]
    obtain ⟨y, hy⟩ := Ideal.mem_span_singleton'.1 (Ideal.Quotient.eq.1 hπ)
    have : (1 + (2 : O) • G).det = 1 + 2 * y := by rw [mul_comm] at hy; rw [hy]; ring
    rw [this]; exact h2 y
  set C : Matrix (ι × Q) (ι × Q) O := blockDiagonal fun q => D.approxInv (A q) (d q) (v q)
  set W : Matrix (ι × Q) (ι × Q) O := blockDiagonal fun q =>
    (D.tinv ^ d q * algebraMap Λ O (((v q)⁻¹ : Λˣ) : Λ) * algebraMap Λ O (w q)) • (1 : Matrix ι ι O)
  have hAC : (blockDiagonal A).map (algebraMap Λ O) * C = 1 + (2 : O) • W := by
    simp only [C, W]
    rw [blockDiagonal_map _ _ (map_zero _), ← blockDiagonal_mul]
    simp only [D.mul_approxInv (A _) (d _) (v _) (w _) (hdet _)]
    ext ⟨i, q⟩ ⟨j, q'⟩
    by_cases h : q = q'
    · subst h; by_cases hij : i = j <;> simp [blockDiagonal_apply_eq, hij]
    · simp [blockDiagonal_apply_ne _ _ _ h, h]
  have hBC : Bx * C = 1 + (2 : O) • (W + V.map (algebraMap Λ O) * C) := by
    rw [hBx, Matrix.add_mul, hAC, Matrix.smul_mul]; simp only [smul_add]; abel
  have hu : IsUnit (Bx * C).det := by rw [hBC]; exact hdet12 _
  rw [det_mul] at hu
  exact isUnit_of_mul_isUnit_left hu

end PoleData

end ZInQ.Manuscript.RC.Determinant
