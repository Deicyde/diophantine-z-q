import Mathlib

/-!
# Lane RC15 (central): the class-functional coordinate of a two-term complex, and its
# specialization over a local domain

Definition `ex:arith-coordinate` of the 11/5 manuscript (`diophantine_zq.tex`, lines 3882–3892):
for a constituent whose generic cohomology has dimensions `(1,1)` in degrees one and two, the
class-functional coordinate `u` is the coordinate of `[z] ⊗ [λ]` in the determinant line
`𝒟 = det⁻¹ C ≅ H¹(C) ⊗ H²(C)^*`, in the retained integral determinant basis; for a generically
acyclic constituent `u = 0`.

**Model (DEPARTURE of form, recorded in the report).** The coordinate is computed on the two-term
finite free complex `C = [A^n --D--> A^n]` in degrees one and two, with the standard bases as the
retained basis. This is the form the manuscript's own computations reach after cancelling the
unit disks outside degrees one and two (V19 tex 20064–20067; the Schur/Cramer formula
`u = ±αβ/Δ` of `ex:limits-uniform-lower-bound`, 11/5 tex 4957–4964). On it, the canonical
isomorphism `det C¹ ⊗ (det C²)⁻¹ ≅ H¹ ⊗ (H²)^*` sends the standard basis to the coordinate
characterized by the matrix identity

  `z ⊗ λ = u · adj D`,  i.e. `z_j λ_k = u · adj(D)_{jk}` for all `j, k`,

which is the Cramer formula `u = (−1)^{j+k} z_j λ_k / M_{kj}` at every nonzero maximal minor
`M_{kj}`. A torsion disk `[A --d--> A]` contributes `d⁻¹`, i.e. `(−1)^{2+1} v(d)` to the
valuation, the sign convention of tex 4058–4060.

Every declaration in this file is `PROVED`.

* `IsClassFunctionalCoord`: the defining identity `vecMulVec z λ = u • adjugate D`.
* `isClassFunctionalCoord_unique`, `isClassFunctionalCoord_zero_of_isUnit_det` (generically
  acyclic: `u = 0`, tex 3890–3891), `exists_isClassFunctionalCoord` (in the `(1,1)` case the
  coordinate exists).
* `adjugate_ne_zero_of_rank`, `rank_eq_of_adjugate_ne_zero`: over a field, `rank D = n − 1` iff
  `det D = 0` and `adj D ≠ 0`; so "dimensions `(1,1)`" is the adjugate condition.
* `coord_specializes` (tex 4359–4364; V19 `lem:v10-determinant-specialization`, 19985–20003):
  over a local domain, if the central adjugate is nonzero, the generic coordinate of an integral
  cycle and an integral closed functional is integral (regular at the centre) and specializes to
  the coordinate of their central tensor; `coord_central_eq_zero`: if the central cycle is zero
  the central coordinate is zero.
-/

namespace ZInQ.Manuscript.RC.Central

open Matrix

section Coordinate

variable {K : Type*} [CommRing K] {n : ℕ}

/-- A nonzero matrix has a nonzero entry. PROVED. -/
theorem exists_entry_ne_zero {R : Type*} [Zero R] {m : ℕ} {M : Matrix (Fin m) (Fin m) R}
    (h : M ≠ 0) : ∃ j k, M j k ≠ 0 := by
  by_contra h'
  exact h (Matrix.ext fun j k => by
    by_contra hjk
    exact h' ⟨j, k, hjk⟩)

/-- **The class-functional coordinate** (Definition `ex:arith-coordinate`, tex 3882–3892) of a
cycle `z` (`D z = 0`) and a closed functional `λ` (`λ D = 0`) of the two-term complex
`[K^n --D--> K^n]` in degrees one and two, in the standard determinant basis: `u` with
`z ⊗ λ = u · adj D`. -/
def IsClassFunctionalCoord (D : Matrix (Fin n) (Fin n) K) (z w : Fin n → K) (u : K) : Prop :=
  vecMulVec z w = u • D.adjugate

/-- The coordinate is unique when `adj D ≠ 0` (over a domain). PROVED. -/
theorem isClassFunctionalCoord_unique [IsDomain K] {D : Matrix (Fin n) (Fin n) K}
    {z w : Fin n → K} {u u' : K} (hadj : D.adjugate ≠ 0) (hu : IsClassFunctionalCoord D z w u)
    (hu' : IsClassFunctionalCoord D z w u') : u = u' := by
  obtain ⟨j, k, hjk⟩ : ∃ j k, D.adjugate j k ≠ 0 := exists_entry_ne_zero hadj
  have h1 := congrFun (congrFun hu j) k
  have h2 := congrFun (congrFun hu' j) k
  simp only [Matrix.smul_apply, smul_eq_mul] at h1 h2
  exact mul_right_cancel₀ hjk (h1.symm.trans h2)

/-- **Generically acyclic constituents have coordinate `0`** (tex 3890–3891): if `det D` is a
unit, every cycle is zero and `u = 0` is the coordinate. PROVED. -/
theorem isClassFunctionalCoord_zero_of_isUnit_det {D : Matrix (Fin n) (Fin n) K}
    {z w : Fin n → K} (hD : IsUnit D.det) (hz : D *ᵥ z = 0) : IsClassFunctionalCoord D z w 0 := by
  have hz0 : z = 0 := by
    have hinv : D⁻¹ * D = 1 := Matrix.nonsing_inv_mul D hD
    calc z = (D⁻¹ * D) *ᵥ z := by rw [hinv, one_mulVec]
      _ = D⁻¹ *ᵥ (D *ᵥ z) := by rw [mulVec_mulVec]
      _ = 0 := by rw [hz, mulVec_zero]
  subst hz0
  ext j k
  simp [vecMulVec_apply]

/-- `det` of a product of transvections is one. PROVED. -/
theorem det_prod_transvec {m : Type*} [Fintype m] [DecidableEq m] {𝕜 : Type*} [Field 𝕜]
    (L : List (TransvectionStruct m 𝕜)) : (L.map TransvectionStruct.toMatrix).prod.det = 1 := by
  induction L with
  | nil => simp
  | cons t L ih => simp [List.prod_cons, det_mul, ih, TransvectionStruct.det]

/-- **Rank `n − 1` gives a nonzero adjugate** over a field (the converse direction of
"dimensions `(1,1)`"). Proof by Gaussian elimination to a diagonal matrix with exactly one zero
entry. PROVED. -/
theorem adjugate_ne_zero_of_rank {𝕜 : Type*} [Field 𝕜] {m : ℕ}
    (D : Matrix (Fin (m + 1)) (Fin (m + 1)) 𝕜) (hr : D.rank = m) : D.adjugate ≠ 0 := by
  classical
  obtain ⟨L, L', d, hLd⟩ := Matrix.Pivot.exists_list_transvec_mul_mul_list_transvec_eq_diagonal D
  set P := (L.map TransvectionStruct.toMatrix).prod
  set Q := (L'.map TransvectionStruct.toMatrix).prod
  have hP : IsUnit P.det := by rw [det_prod_transvec]; exact isUnit_one
  have hQ : IsUnit Q.det := by rw [det_prod_transvec]; exact isUnit_one
  have hrank : (diagonal d).rank = m := by
    rw [← hLd, rank_mul_eq_left_of_isUnit_det Q _ hQ, rank_mul_eq_right_of_isUnit_det P _ hP, hr]
  rw [rank_diagonal] at hrank
  -- exactly one index with `d i = 0`
  have hcard : Fintype.card {i // d i = 0} = 1 := by
    have h := Fintype.card_subtype_compl (fun i => d i ≠ 0)
    simp only [ne_eq, not_not, Fintype.card_fin, hrank] at h
    rw [h]; omega
  obtain ⟨⟨i0, hi0⟩, hu⟩ := Fintype.card_eq_one_iff.mp hcard
  have honly : ∀ j, d j = 0 → j = i0 := fun j hj => congrArg Subtype.val (hu ⟨j, hj⟩)
  intro hadj
  have hdiag : (diagonal d).adjugate = 0 := by
    rw [← hLd, adjugate_mul_distrib, adjugate_mul_distrib, hadj]; simp
  rw [adjugate_diagonal] at hdiag
  have := congrFun (congrFun hdiag i0) i0
  simp only [diagonal_apply_eq, Matrix.zero_apply] at this
  rw [Finset.prod_eq_zero_iff] at this
  obtain ⟨j, hj, hdj⟩ := this
  exact (Finset.mem_erase.mp hj).1 (honly j hdj)

/-- A nonzero adjugate entry gives an invertible `(n−1) × (n−1)` submatrix, so `rank D ≥ n − 1`.
PROVED. -/
theorem le_rank_of_adjugate_ne_zero {𝕜 : Type*} [Field 𝕜] {m : ℕ}
    {D : Matrix (Fin (m + 1)) (Fin (m + 1)) 𝕜} (hadj : D.adjugate ≠ 0) : m ≤ D.rank := by
  obtain ⟨j, k, hjk⟩ : ∃ j k, D.adjugate j k ≠ 0 := exists_entry_ne_zero hadj
  rw [adjugate_fin_succ_eq_det_submatrix] at hjk
  have hdet : (D.submatrix k.succAbove j.succAbove).det ≠ 0 := right_ne_zero_of_mul hjk
  have hunit : IsUnit (D.submatrix k.succAbove j.succAbove) :=
    (Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr hdet)
  have h1 := rank_of_isUnit _ hunit
  simp only [Fintype.card_fin] at h1
  exact (le_of_eq h1.symm).trans (rank_submatrix_le D _ _)

/-- **`det D = 0` and `adj D ≠ 0` give `rank D = n − 1`**: generic (or central) dimensions
`(1,1)` for the two-term complex. PROVED. -/
theorem rank_eq_of_adjugate_ne_zero {𝕜 : Type*} [Field 𝕜] {m : ℕ}
    {D : Matrix (Fin (m + 1)) (Fin (m + 1)) 𝕜} (hdet : D.det = 0) (hadj : D.adjugate ≠ 0) :
    D.rank = m := by
  refine le_antisymm ?_ (le_rank_of_adjugate_ne_zero hadj)
  by_contra hlt
  rw [not_le] at hlt
  have hle : D.rank ≤ m + 1 := by simpa using rank_le_card_width D
  have hfull : D.rank = m + 1 := by omega
  -- full rank: `mulVecLin` surjective, hence `D` invertible, contradicting `det D = 0`
  have hsurj : Function.Surjective D.mulVecLin := by
    rw [← LinearMap.range_eq_top]
    apply Submodule.eq_top_of_finrank_eq
    rw [show Module.finrank 𝕜 (LinearMap.range D.mulVecLin) = D.rank from rfl, hfull]
    simp
  obtain ⟨B, hB⟩ : ∃ B : Matrix (Fin (m + 1)) (Fin (m + 1)) 𝕜, D * B = 1 := by
    choose f hf using hsurj
    refine ⟨Matrix.of fun i j => f (Pi.single j 1) i, ?_⟩
    ext i j
    have := congrFun (hf (Pi.single j 1)) i
    rw [mulVecLin_apply] at this
    rw [mul_apply, one_apply]
    simp only [mulVec, dotProduct, of_apply] at this ⊢
    rw [this]
    by_cases hij : i = j
    · subst hij; simp
    · simp [hij]
  have := congrArg det hB
  rw [det_mul, hdet, zero_mul, det_one] at this
  exact zero_ne_one this

/-- In the kernel of a matrix of rank `≥ n − 1`, a nonzero vector spans. PROVED. -/
theorem ker_proportional {𝕜 : Type*} [Field 𝕜] {m : ℕ} (D : Matrix (Fin (m + 1)) (Fin (m + 1)) 𝕜)
    (hrank : m ≤ D.rank) {a z : Fin (m + 1) → 𝕜} (ha : D *ᵥ a = 0) (ha0 : a ≠ 0)
    (hz : D *ᵥ z = 0) : ∃ c : 𝕜, z = c • a := by
  have hrn := LinearMap.finrank_range_add_finrank_ker D.mulVecLin
  have hr : Module.finrank 𝕜 (LinearMap.range D.mulVecLin) = D.rank := rfl
  rw [hr, Module.finrank_fin_fun] at hrn
  have haV : a ∈ LinearMap.ker D.mulVecLin := by rw [LinearMap.mem_ker, mulVecLin_apply]; exact ha
  have hzV : z ∈ LinearMap.ker D.mulVecLin := by rw [LinearMap.mem_ker, mulVecLin_apply]; exact hz
  have hpos : 0 < Module.finrank 𝕜 (LinearMap.ker D.mulVecLin) :=
    Module.finrank_pos_iff_exists_ne_zero.mpr ⟨⟨a, haV⟩, fun h => ha0 (congrArg Subtype.val h)⟩
  have h1 : Module.finrank 𝕜 (LinearMap.ker D.mulVecLin) = 1 := by omega
  obtain ⟨c, hc⟩ := (finrank_eq_one_iff_of_nonzero' (⟨a, haV⟩ : LinearMap.ker D.mulVecLin)
    (fun h => ha0 (congrArg Subtype.val h))).mp h1 ⟨z, hzV⟩
  exact ⟨c, (congrArg Subtype.val hc).symm⟩

/-- **The coordinate exists in the `(1,1)` case**: over a field, if `det D = 0` and `adj D ≠ 0`,
every cycle `z` and closed functional `λ` satisfy `z ⊗ λ = u · adj D` for some `u`. PROVED. -/
theorem exists_isClassFunctionalCoord {𝕜 : Type*} [Field 𝕜] {m : ℕ}
    {D : Matrix (Fin (m + 1)) (Fin (m + 1)) 𝕜} (hdet : D.det = 0) (hadj : D.adjugate ≠ 0)
    {z w : Fin (m + 1) → 𝕜} (hz : D *ᵥ z = 0) (hw : w ᵥ* D = 0) :
    ∃ u, IsClassFunctionalCoord D z w u := by
  obtain ⟨j0, k0, hjk⟩ : ∃ j k, D.adjugate j k ≠ 0 := exists_entry_ne_zero hadj
  have hrank := le_rank_of_adjugate_ne_zero hadj
  have hrankT : m ≤ Dᵀ.rank := by rw [rank_transpose]; exact hrank
  have hDA : D * D.adjugate = 0 := by rw [mul_adjugate, hdet, zero_smul]
  have hAD : D.adjugate * D = 0 := by rw [adjugate_mul, hdet, zero_smul]
  -- columns of `adj D` are cycles
  have hcol : ∀ k, D *ᵥ (fun i => D.adjugate i k) = 0 := by
    intro k; ext i
    have := congrFun (congrFun hDA i) k
    rw [mul_apply] at this
    simpa [mulVec, dotProduct] using this
  -- rows of `adj D` are closed functionals
  have hrow : ∀ j, Dᵀ *ᵥ (fun k => D.adjugate j k) = 0 := by
    intro j; ext l
    have := congrFun (congrFun hAD j) l
    rw [mul_apply] at this
    simpa [mulVec, dotProduct, transpose_apply, mul_comm] using this
  set a : Fin (m + 1) → 𝕜 := fun i => D.adjugate i k0
  set b : Fin (m + 1) → 𝕜 := fun k => D.adjugate j0 k
  have ha0 : a ≠ 0 := fun h => hjk (congrFun h j0)
  have hb0 : b ≠ 0 := fun h => hjk (congrFun h k0)
  obtain ⟨α, hα⟩ := ker_proportional D hrank (hcol k0) ha0 hz
  have hwT : Dᵀ *ᵥ w = 0 := by rw [mulVec_transpose]; exact hw
  obtain ⟨β, hβ⟩ := ker_proportional Dᵀ hrankT (hrow j0) hb0 hwT
  have hμ : ∀ k, ∃ μ : 𝕜, (fun i => D.adjugate i k) = μ • a :=
    fun k => ker_proportional D hrank (hcol k0) ha0 (hcol k)
  choose μ hμ using hμ
  refine ⟨α * β * D.adjugate j0 k0, ?_⟩
  ext j k
  have hjk' : D.adjugate j k = μ k * a j := by
    have := congrFun (hμ k) j; simpa using this
  have hbk : b k = μ k * a j0 := by
    have := congrFun (hμ k) j0; simpa [b] using this
  simp only [vecMulVec_apply, Matrix.smul_apply, smul_eq_mul]
  rw [hα, hβ, hjk']
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [show D.adjugate j0 k = μ k * D.adjugate j0 k0 from hbk,
    show a j = D.adjugate j k0 from rfl]
  ring

end Coordinate

/-! ### Specialization of the coordinate over a local domain -/

section Specialization

variable {A F k : Type*} [CommRing A] [IsLocalRing A] [Field F] [Field k] {n : ℕ}

/-- **Regularity and specialization of the coordinate** (tex 4359–4364; V19 Lemma
`lem:v10-determinant-specialization`, 19985–20003). Let `A` be a local domain with an injection
`ι` into a field `F` (the generic point) and a reduction `ρ` to a field `k` killing the maximal
ideal (the centre). Let `D` be the integral differential, `z` an integral cycle and `λ` an
integral closed functional, and `u ∈ F` the generic coordinate. If the central adjugate is
nonzero (central dimensions `(1,1)`, no positive disk), then `u` is integral, `u = ι u₀`, and
`ρ u₀` is the coordinate of the central tensor `z̄ ⊗ λ̄` for `D̄`. PROVED. -/
theorem coord_specializes (ι : A →+* F) (hι : Function.Injective ι) (ρ : A →+* k)
    (hρ : ∀ x ∈ IsLocalRing.maximalIdeal A, ρ x = 0) (D : Matrix (Fin n) (Fin n) A)
    (z w : Fin n → A) (u : F)
    (hu : IsClassFunctionalCoord (D.map ι) (fun i => ι (z i)) (fun i => ι (w i)) u)
    (hres : (D.map ρ).adjugate ≠ 0) :
    ∃ u₀ : A, ι u₀ = u ∧
      IsClassFunctionalCoord (D.map ρ) (fun i => ρ (z i)) (fun i => ρ (w i)) (ρ u₀) := by
  obtain ⟨j, l, hjl⟩ : ∃ j l, (D.map ρ).adjugate j l ≠ 0 := exists_entry_ne_zero hres
  have hmapρ : (D.map ρ).adjugate = D.adjugate.map ρ := (RingHom.map_adjugate ρ D).symm
  have hmapι : (D.map ι).adjugate = D.adjugate.map ι := (RingHom.map_adjugate ι D).symm
  have hunit : IsUnit (D.adjugate j l) := by
    refine IsLocalRing.notMem_maximalIdeal.mp fun hm => hjl ?_
    rw [hmapρ, map_apply]; exact hρ _ hm
  obtain ⟨v, hv⟩ := hunit
  set u₀ : A := z j * w l * ↑v⁻¹
  have hentry : ∀ j' l', ι (z j' * w l') = u * ι (D.adjugate j' l') := by
    intro j' l'
    have := congrFun (congrFun hu j') l'
    simp only [vecMulVec_apply, Matrix.smul_apply, smul_eq_mul, hmapι, map_apply] at this
    rw [map_mul]; exact this
  have hu₀ : ι u₀ = u := by
    have h1 := hentry j l
    rw [← hv] at h1
    have hvι : ι ↑v * ι ↑v⁻¹ = 1 := by rw [← map_mul, Units.mul_inv, map_one]
    calc ι u₀ = ι (z j * w l) * ι ↑v⁻¹ := by simp [u₀, map_mul]
      _ = u * (ι ↑v * ι ↑v⁻¹) := by rw [h1]; ring
      _ = u := by rw [hvι, mul_one]
  refine ⟨u₀, hu₀, ?_⟩
  have hA : ∀ j' l', z j' * w l' = u₀ * D.adjugate j' l' := by
    intro j' l'
    apply hι
    rw [hentry, map_mul, hu₀]
  ext j' l'
  simp only [vecMulVec_apply, Matrix.smul_apply, smul_eq_mul, hmapρ, map_apply]
  rw [← map_mul, hA, map_mul]

/-- **The central coordinate vanishes when the central cycle does** (tex 4364–4365: "That tensor
is zero because `[z]_0 = 0`"). PROVED. -/
theorem coord_central_eq_zero {D : Matrix (Fin n) (Fin n) k} {z w : Fin n → k} {u : k}
    (hu : IsClassFunctionalCoord D z w u) (hadj : D.adjugate ≠ 0) (hz : z = 0) : u = 0 := by
  obtain ⟨j, l, hjl⟩ : ∃ j l, D.adjugate j l ≠ 0 := exists_entry_ne_zero hadj
  have := congrFun (congrFun hu j) l
  simp only [vecMulVec_apply, Matrix.smul_apply, smul_eq_mul, hz, Pi.zero_apply, zero_mul] at this
  exact (mul_eq_zero.mp this.symm).resolve_right hjl

end Specialization

end ZInQ.Manuscript.RC.Central
