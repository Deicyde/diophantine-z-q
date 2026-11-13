/-! ## rv-gluepieces2 check (a): g10-odd's reduction applies to g0-assemble's changed `G10Glue`.
Lines 102-239 of scratch/g10-odd/G10Odd.lean, verbatim, then the reduction. -/

section RvG10Check
namespace G0Galois
open PkgI4 (GaloisRep GaloisChar)
open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct

/-- A `2 × 2` involution over a field that is not `±1` has determinant `−1` (trace `0`). -/
theorem det_eq_neg_one_of_sq_eq_one {F : Type*} [Field F] (M : Matrix (Fin 2) (Fin 2) F)
    (h2 : M * M = 1) (h1 : M ≠ 1) (hm1 : M ≠ -1) : M.det = -1 := by
  have e00 := congrFun (congrFun h2 0) 0
  have e01 := congrFun (congrFun h2 0) 1
  have e10 := congrFun (congrFun h2 1) 0
  have e11 := congrFun (congrFun h2 1) 1
  simp [Matrix.mul_apply, Fin.sum_univ_two] at e00 e01 e10 e11
  rw [Matrix.det_fin_two]
  by_cases ht : M 0 0 + M 1 1 = 0
  · have : M 1 1 = -M 0 0 := by linear_combination ht
    rw [this]; linear_combination -e00
  · have hb : M 0 1 = 0 := by
      have : M 0 1 * (M 0 0 + M 1 1) = 0 := by linear_combination e01
      exact (mul_eq_zero.mp this).resolve_right ht
    have hc : M 1 0 = 0 := by
      have : M 1 0 * (M 0 0 + M 1 1) = 0 := by linear_combination e10
      exact (mul_eq_zero.mp this).resolve_right ht
    rw [hb, hc] at e00 e11
    have ha : M 0 0 = 1 ∨ M 0 0 = -1 := by
      have : (M 0 0 - 1) * (M 0 0 + 1) = 0 := by linear_combination e00
      rcases mul_eq_zero.mp this with h | h
      · left; linear_combination h
      · right; linear_combination h
    have hd : M 1 1 = 1 ∨ M 1 1 = -1 := by
      have : (M 1 1 - 1) * (M 1 1 + 1) = 0 := by linear_combination e11
      rcases mul_eq_zero.mp this with h | h
      · left; linear_combination h
      · right; linear_combination h
    exfalso
    rcases ha with ha | ha <;> rcases hd with hd | hd
    · exact h1 (by ext i j; fin_cases i <;> fin_cases j <;> simp [ha, hb, hc, hd])
    · exact ht (by rw [ha, hd]; ring)
    · exact ht (by rw [ha, hd]; ring)
    · exact hm1 (by ext i j; fin_cases i <;> fin_cases j <;> simp [ha, hb, hc, hd])

/-- A complex conjugation is an involution. -/
theorem isComplexConj_mul_self {c : PkgI4.GQ} (hc : PkgI4.IsComplexConj c) : c * c = 1 := by
  obtain ⟨j, hj⟩ := hc
  apply AlgEquiv.ext; intro x
  apply j.toRingHom.injective
  change j (c (c x)) = j x
  rw [hj, hj, Complex.conj_conj]

variable {ℓ : ℕ} [Fact ℓ.Prime]

theorem GaloisRep.mat_mul (r : GaloisRep ℓ 2) (g h : PkgI4.GQ) :
    r.mat (g * h) = r.mat g * r.mat h := by
  simp [PkgI4.GaloisRep.mat, map_mul, Units.val_mul]

theorem GaloisRep.mat_one (r : GaloisRep ℓ 2) : r.mat 1 = 1 := by
  simp [PkgI4.GaloisRep.mat]

/-- **Oddness from non-scalarity (proved).** If no complex conjugation acts by `±1`, then `r` is
odd. -/
theorem isOdd_of_not_pm_one (r : GaloisRep ℓ 2)
    (h : ∀ c, PkgI4.IsComplexConj c → r.mat c ≠ 1 ∧ r.mat c ≠ -1) : r.IsOdd := by
  intro c hc
  have h2 : r.mat c * r.mat c = 1 := by
    rw [← GaloisRep.mat_mul, isComplexConj_mul_self hc, GaloisRep.mat_one]
  exact det_eq_neg_one_of_sq_eq_one _ h2 (h c hc).1 (h c hc).2

/-- `v ↦ 1 ⊗ v` is injective for a field extension (flatness of vector spaces). -/
theorem one_tmul_injective (k E V : Type*) [Field k] [Field E] [Algebra k E] [AddCommGroup V]
    [Module k V] : Function.Injective (fun v : V => (1 : E) ⊗ₜ[k] v) := by
  have hinj := Module.Flat.rTensor_preserves_injective_linearMap (M := V)
    (Algebra.linearMap k E) (algebraMap k E).injective
  intro x y hxy
  apply (TensorProduct.lid k V).symm.injective
  apply hinj
  simpa using hxy

/-- Base change along a field extension is injective on linear maps. -/
theorem baseChange_injective' (k E V : Type*) [Field k] [Field E] [Algebra k E] [AddCommGroup V]
    [Module k V] {f g : V →ₗ[k] V} (h : f.baseChange E = g.baseChange E) : f = g := by
  ext v
  apply one_tmul_injective k E V
  have := LinearMap.congr_fun h ((1 : E) ⊗ₜ[k] v)
  simpa using this

/-! ## §3. The remaining glue, and `G10Glue` from it -/

/-- **G10 core: complex conjugation twists the Tate representation of `G_K` nontrivially (GLUE,
unproved; STANDARD).** For a number field `K` Galois over `ℚ`, an abelian surface `A/K`, a prime
`ℓ` and a complex conjugation `c ∈ G_ℚ`, it is not the case that `ρ_ℓ(τ) = ρ_ℓ(σ)` on `V_ℓ(A)`
whenever `τ, σ ∈ G_K` satisfy `τ = c σ c⁻¹` in `G_ℚ` (`resQ`).

Proof (STANDARD; N5 L742-751, h-trust C5): suppose it is. Let `ι : ℚ̄ → ℂ` realize `c`, `c̄ = c|_K`
(`K` normal), `A^c = A ⊗_{K,c̄} K`. The `c`-semilinear bijection `A(K̄) → A^c(K̄)` gives
`c_* : V_ℓ(A) → V_ℓ(A^c)` with `c_* ρ_A(σ) = ρ_{A^c}(cσc⁻¹) c_*`; by the assumption `c_*` is
`G_K`-equivariant, so by Faltings (`PkgI3.FaltingsTate`, R9b) `c_* ∈ Hom(A, A^c) ⊗ ℚ_ℓ`. By the
Artin comparison at `ι` (T12, through the uniformization T35 and T5), `c_* = F_* ⊗ 1` for the
antiholomorphic `F : A(ℂ) → A^c(ℂ)`, `F_* : H₁(A(ℂ),ℚ) → H₁(A^c(ℂ),ℚ)` `ℚ`-rational; since
`(W ⊗ ℚ_ℓ) ∩ Hom_ℚ(H, H') = W` for the `ℚ`-subspace `W = Hom(A, A^c) ⊗ ℚ`, `F_* ∈ W`, so `F_*` is
`ℂ`-linear by T11 (`F_* J = J' F_*`) and `ℂ`-antilinear (`F_* J = −J' F_*`), hence `F_* = 0`,
contradicting `F_*` bijective and `H ≠ 0` (`dim A = 2`). The case `c ∈ G_K` (`c̄ = id`,
`A^c = A`) is the same with `c_* = ρ_A(c)`. -/
def ConjTwistNontrivial : Prop :=
  PkgI3.FaltingsTate →
  ∀ (K : Type) [Field K] [NumberField K] [IsGalois ℚ K] (A : PkgI3.AbVar K) (ℓ : ℕ)
    [Fact ℓ.Prime], A.dim = 2 → ∀ c : PkgI4.GQ, PkgI4.IsComplexConj c →
    ¬ ∀ σ τ : Field.absoluteGaloisGroup K, resQ K τ = c * resQ K σ * c⁻¹ →
      A.galRep ℓ τ = A.galRep ℓ σ

/-- If `r(c)` is central (here `±1`), the Tate action is unchanged by the `c`-twist. -/
theorem galRep_eq_of_central {K : Type} [Field K] [NumberField K] (A : PkgI3.AbVar K)
    (r : GaloisRep ℓ 2)
    (e : Vb A ℓ ≃ₗ[PadicAlgCl ℓ] (Fin 2 → PadicAlgCl ℓ) × (Fin 2 → PadicAlgCl ℓ))
    (hI : Intertwines (tate A ℓ) (fun σ => r.mat (resQ K σ)) e) (c : PkgI4.GQ)
    (hcen : ∀ X, r.mat c * X = X * r.mat c) (σ τ : Field.absoluteGaloisGroup K)
    (hτ : resQ K τ = c * resQ K σ * c⁻¹) : A.galRep ℓ τ = A.galRep ℓ σ := by
  have hm : r.mat (resQ K τ) = r.mat (resQ K σ) := by
    rw [hτ, GaloisRep.mat_mul, GaloisRep.mat_mul, hcen, _root_.mul_assoc, ← GaloisRep.mat_mul,
      _root_.mul_inv_cancel, GaloisRep.mat_one, _root_.mul_one]
  have ht : tate A ℓ τ = tate A ℓ σ := by
    apply LinearMap.ext; intro v
    apply e.injective
    rw [hI τ v, hI σ v]
    simp only [hm]
  exact baseChange_injective' ℚ_[ℓ] (PadicAlgCl ℓ) (A.V ℓ) ht

/-- **The conclusion of `G10Glue` from `ConjTwistNontrivial` (proved),** without the opaque
hypotheses and without the rank, division and noncommutativity hypotheses. -/
theorem g10Out_of_conjTwist (h : ConjTwistNontrivial) (hF : PkgI3.FaltingsTate) (K : Type)
    [Field K] [NumberField K] [IsGalois ℚ K] (A : PkgI3.AbVar K) (ℓ : ℕ) [Fact ℓ.Prime]
    (r : GaloisRep ℓ 2)
    (e : Vb A ℓ ≃ₗ[PadicAlgCl ℓ] (Fin 2 → PadicAlgCl ℓ) × (Fin 2 → PadicAlgCl ℓ))
    (hdim : A.dim = 2) (hI : Intertwines (tate A ℓ) (fun σ => r.mat (resQ K σ)) e) :
    G10Out r := by
  apply isOdd_of_not_pm_one
  intro c hc
  have key := h hF K A ℓ hdim c hc
  constructor
  · intro h1
    exact key (galRep_eq_of_central A r e hI c (fun X => by rw [h1, _root_.one_mul, _root_.mul_one]))
  · intro h1
    exact key (galRep_eq_of_central A r e hI c (fun X => by rw [h1]; simp))

theorem g10Glue_of_conjTwist_new (h : ConjTwistNontrivial) : G10Glue := by
  intro _ _ hF K _ _ _ A ℓ _ r e hdim _ _ _ hI
  exact g10Out_of_conjTwist h hF K A ℓ r e hdim hI

end G0Galois
end RvG10Check

#print axioms G0Galois.g10Glue_of_conjTwist_new
