
/-! ## §19. H-32 from `B_dR^{G_{ℚ_p}} = ℚ_p` alone

Fontaine's Tannakian theorem for `B_dR` (the leaf `FontaineDRTannakian` of §7) has an elementary proof
from the regularity of `B_dR` (Brinon–Conrad, Thm 5.2.1). `B_dR` is a field (bdr-kertheta, in the kernel:
`BdrKer.Cp.isField_BDeRham`), so regularity reduces to `B_dR^{G_{ℚ_p}} = ℚ_p`, the leaf
`BdRInvariants`. -/

section BdRSec

/-- **LEAF (Fontaine: `B_dR^{G_K} = K`, here `K = ℚ_p`).** Fontaine, *Le corps des périodes
p-adiques*, Astérisque 223 (1994), Exp. II, §1.5 (and §3); Brinon–Conrad, *CMI summer school notes on
p-adic Hodge theory* (2009), Thm 4.3.? / §4.4 (`(B_dR)^{G_K} = K`); numbering UNVERIFIED. Lean form: a
`G_{ℚ_p}`-invariant element of Mathlib's `B_dR(𝓞_ℂ_p)` (pkg-I4's action `bdrAct`) lies in the image
of `ℚ_p`. (It is the hypothesis `hfix` of pkg-I4's `isDeRham_trivial`.) -/
def BdRInvariants : Prop :=
  ∀ x : BdR p, (∀ σ : GQp p, bdrAct p σ x = x) → x ∈ Set.range (qpToBdR p)

theorem isField_BdR : IsField (BdR p) := BdrKer.Cp.isField_BDeRham p

/-- `B_dR` as a field (the ring structure is Mathlib's). -/
noncomputable def bdrField : Field (BdR p) := (isField_BdR p).toField

attribute [local instance] bdrField

variable {n : ℕ}

/-- The matrix of `ρ(σ)` read in `B_dR`. -/
def matB (M : Matrix (Fin n) (Fin n) ℚ_[p]) : Matrix (Fin n) (Fin n) (BdR p) :=
  M.map (algebraMap ℚ_[p] (BdR p))

/-- `σ` on `B_dRⁿ`, coordinatewise. -/
def bAct (σ : GQp p) (x : Fin n → BdR p) : Fin n → BdR p := fun k => bdrAct p σ (x k)

theorem mem_ddrStd_iff (ρ : GQp p →* GL (Fin n) ℚ_[p]) (x : Fin n → BdR p) :
    x ∈ ddrStd p ρ ↔ ∀ σ, (matB p (ρ σ : Matrix (Fin n) (Fin n) ℚ_[p])).mulVec (bAct p σ x) = x :=
  Iff.rfl

theorem matB_mul (A B : Matrix (Fin n) (Fin n) ℚ_[p]) : matB p (A * B) = matB p A * matB p B := by
  simp [matB, Matrix.map_mul]

theorem matB_one : matB p (1 : Matrix (Fin n) (Fin n) ℚ_[p]) = 1 := by
  simp [matB, Matrix.map_one]

theorem matB_inv_mul (ρ : GQp p →* GL (Fin n) ℚ_[p]) (σ : GQp p) :
    matB p (ρ σ⁻¹ : Matrix (Fin n) (Fin n) ℚ_[p]) * matB p (ρ σ : Matrix (Fin n) (Fin n) ℚ_[p]) = 1 := by
  rw [← matB_mul, gl_inv_mul, matB_one]

theorem matB_mul_inv (ρ : GQp p →* GL (Fin n) ℚ_[p]) (σ : GQp p) :
    matB p (ρ σ : Matrix (Fin n) (Fin n) ℚ_[p]) * matB p (ρ σ⁻¹ : Matrix (Fin n) (Fin n) ℚ_[p]) = 1 := by
  rw [← matB_mul, gl_mul_inv, matB_one]

theorem bAct_of_mem {ρ : GQp p →* GL (Fin n) ℚ_[p]} {x : Fin n → BdR p} (hx : x ∈ ddrStd p ρ)
    (σ : GQp p) : bAct p σ x = (matB p (ρ σ⁻¹ : Matrix (Fin n) (Fin n) ℚ_[p])).mulVec x := by
  conv_rhs => rw [← (mem_ddrStd_iff p ρ x).mp hx σ]
  rw [Matrix.mulVec_mulVec, matB_inv_mul, Matrix.one_mulVec]

theorem bAct_add (σ : GQp p) (x y : Fin n → BdR p) : bAct p σ (x + y) = bAct p σ x + bAct p σ y := by
  ext k; simp [bAct]

theorem bAct_smul (σ : GQp p) (c : BdR p) (x : Fin n → BdR p) :
    bAct p σ (c • x) = bdrAct p σ c • bAct p σ x := by
  ext k; simp [bAct]

theorem bAct_sum {ι : Type*} (s : Finset ι) (σ : GQp p) (f : ι → Fin n → BdR p) :
    bAct p σ (∑ k ∈ s, f k) = ∑ k ∈ s, bAct p σ (f k) := by
  ext m; simp [bAct, Finset.sum_apply, map_sum]

theorem bAct_zero (σ : GQp p) : bAct p σ (0 : Fin n → BdR p) = 0 := by ext; simp [bAct]

theorem algebraMap_BdR_injective : Function.Injective (algebraMap ℚ_[p] (BdR p)) :=
  (algebraMap ℚ_[p] (BdR p)).injective

/-- **(I) Regularity.** `ℚ_p`-independent elements of `D_dR(V)` are `B_dR`-independent. -/
theorem ddrStd_linearIndependent (hB : BdRInvariants p) (ρ : GQp p →* GL (Fin n) ℚ_[p])
    {ι : Type*} [Fintype ι] [DecidableEq ι] (x : ι → (Fin n → BdR p)) (hx : ∀ k, x k ∈ ddrStd p ρ)
    (hind : LinearIndependent ℚ_[p] x) : LinearIndependent (BdR p) x := by
  rw [Fintype.linearIndependent_iff]
  suffices H : ∀ (s : Finset ι) (b : ι → BdR p), (∀ k ∉ s, b k = 0) → ∑ k, b k • x k = 0 →
      ∀ k, b k = 0 from fun b hb => H Finset.univ b (by simp) hb
  intro s
  induction s using Finset.strongInduction with
  | H s ih =>
  intro b hbs hb
  by_contra hne
  push_neg at hne
  obtain ⟨k₀, hk₀⟩ := hne
  have hk₀s : k₀ ∈ s := by
    by_contra h; exact hk₀ (hbs k₀ h)
  let b' : ι → BdR p := fun k => (b k₀)⁻¹ * b k
  have hb' : ∑ k, b' k • x k = 0 := by
    simp only [b', mul_smul, ← Finset.smul_sum, hb, smul_zero]
  have hb'k₀ : b' k₀ = 1 := inv_mul_cancel₀ hk₀
  have hb's : ∀ k ∉ s, b' k = 0 := fun k hk => by simp [b', hbs k hk]
  have key : ∀ σ, ∀ k, b' k = bdrAct p σ (b' k) := by
    intro σ
    let d : ι → BdR p := fun k => b' k - bdrAct p σ (b' k)
    have h1 : (matB p (ρ σ⁻¹ : Matrix (Fin n) (Fin n) ℚ_[p])).mulVec
        (∑ k, bdrAct p σ (b' k) • x k) = 0 := by
      have h0 := congrArg (bAct p σ) hb'
      rw [bAct_sum, bAct_zero] at h0
      rw [Matrix.mulVec_sum, ← h0]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [bAct_smul, bAct_of_mem p (hx k), Matrix.mulVec_smul]
    have h2 : ∑ k, bdrAct p σ (b' k) • x k = 0 := by
      have := congrArg (matB p (ρ σ : Matrix (Fin n) (Fin n) ℚ_[p])).mulVec h1
      rwa [Matrix.mulVec_mulVec, matB_mul_inv, Matrix.one_mulVec, Matrix.mulVec_zero] at this
    have hd : ∑ k, d k • x k = 0 := by
      simp only [d, sub_smul, Finset.sum_sub_distrib, hb', h2, sub_zero]
    have hds : ∀ k ∉ s.erase k₀, d k = 0 := by
      intro k hk
      by_cases hkk : k = k₀
      · subst hkk; simp [d, hb'k₀]
      · have : k ∉ s := fun h => hk (Finset.mem_erase.mpr ⟨hkk, h⟩)
        simp [d, hb's k this]
    have := ih (s.erase k₀) (Finset.erase_ssubset hk₀s) d hds hd
    intro k
    exact sub_eq_zero.mp (this k)
  have hK : ∀ k, ∃ a : ℚ_[p], b' k = algebraMap ℚ_[p] (BdR p) a := by
    intro k
    obtain ⟨a, ha⟩ := hB (b' k) fun σ => (key σ k).symm
    exact ⟨a, ha.symm⟩
  choose a ha using hK
  have hsum : ∑ k, a k • x k = 0 := by
    rw [← hb']
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [ha k, algebraMap_smul]
  have h0 := Fintype.linearIndependent_iff.mp hind a hsum k₀
  have h1 := ha k₀
  rw [h0, map_zero, hb'k₀] at h1
  exact one_ne_zero h1

theorem ddrStd_finiteDimensional (hB : BdRInvariants p) (ρ : GQp p →* GL (Fin n) ℚ_[p]) :
    FiniteDimensional ℚ_[p] (ddrStd p ρ) := by
  classical
  refine Module.rank_lt_aleph0_iff.mp (lt_of_le_of_lt (rank_le (n := n) fun s hs => ?_)
    (Cardinal.natCast_lt_aleph0 (n := n)))
  have hli : LinearIndependent (BdR p) (fun x : s => ((x : ddrStd p ρ) : Fin n → BdR p)) :=
    ddrStd_linearIndependent p hB ρ _ (fun x => (x : ddrStd p ρ).2)
      (LinearIndependent.map' hs (ddrStd p ρ).subtype (Submodule.ker_subtype _))
  calc s.card = Fintype.card s := (Fintype.card_coe s).symm
    _ ≤ Module.finrank (BdR p) (Fin n → BdR p) := hli.fintype_card_le_finrank
    _ = n := Module.finrank_fin_fun _

theorem ddrStd_finrank_le (hB : BdRInvariants p) (ρ : GQp p →* GL (Fin n) ℚ_[p]) :
    Module.finrank ℚ_[p] (ddrStd p ρ) ≤ n := by
  haveI := ddrStd_finiteDimensional p hB ρ
  let b := Module.finBasis ℚ_[p] (ddrStd p ρ)
  have hli : LinearIndependent (BdR p) (fun k => ((b k : ddrStd p ρ) : Fin n → BdR p)) :=
    ddrStd_linearIndependent p hB ρ _ (fun k => (b k).2)
      (LinearIndependent.map' b.linearIndependent (ddrStd p ρ).subtype (Submodule.ker_subtype _))
  have := hli.fintype_card_le_finrank
  rwa [Fintype.card_fin, Module.finrank_fin_fun] at this

end BdRSec

section BdRSec2

attribute [local instance] bdrField

instance bdrDomain : IsDomain (BdR p) := (isField_BdR p).isDomain

variable {n : ℕ}

theorem mulVec_eq_sum_col (P : Matrix (Fin n) (Fin n) (BdR p)) (v : Fin n → BdR p) :
    P.mulVec v = ∑ j, v j • (fun i => P i j) := by
  ext i; simp [Matrix.mulVec, dotProduct, Finset.sum_apply, mul_comm]

theorem bAct_col (σ : GQp p) (P : Matrix (Fin n) (Fin n) (BdR p)) (j : Fin n) :
    bAct p σ (fun i => P i j) = fun i => P.map (bdrAct p σ) i j := rfl

/-- **(L5)** An invertible matrix whose columns lie in `D_dR(V)` makes `V` de Rham. -/
theorem isDeRhamStd_of_matrix (hB : BdRInvariants p) (ρ : GQp p →* GL (Fin n) ℚ_[p])
    (P : Matrix (Fin n) (Fin n) (BdR p)) (hP : P.det ≠ 0)
    (hrel : ∀ σ, matB p (ρ σ : Matrix (Fin n) (Fin n) ℚ_[p]) * P.map (bdrAct p σ) = P) :
    IsDeRhamStd p ρ := by
  haveI := ddrStd_finiteDimensional p hB ρ
  have hcol : ∀ j, (fun i => P i j) ∈ ddrStd p ρ := by
    intro j
    rw [mem_ddrStd_iff]
    intro σ
    rw [bAct_col]
    ext i
    have := congrFun (congrFun (hrel σ) i) j
    rw [Matrix.mul_apply] at this
    simp only [Matrix.mulVec, dotProduct]
    exact this
  let c : Fin n → ddrStd p ρ := fun j => ⟨fun i => P i j, hcol j⟩
  have hli : LinearIndependent ℚ_[p] c := by
    rw [Fintype.linearIndependent_iff]
    intro a ha j
    have h1 : P.mulVec (fun j => algebraMap ℚ_[p] (BdR p) (a j)) = 0 := by
      rw [mulVec_eq_sum_col]
      have := congrArg Subtype.val ha
      rw [Submodule.coe_sum, Submodule.coe_zero] at this
      rw [← this]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [algebraMap_smul]
      rfl
    by_contra hne
    exact hP ((Matrix.exists_mulVec_eq_zero_iff).mp
      ⟨_, fun h => hne (algebraMap_BdR_injective p (by simpa using congrFun h j)), h1⟩)
  have h1 := hli.fintype_card_le_finrank
  rw [Fintype.card_fin] at h1
  exact le_antisymm (ddrStd_finrank_le p hB ρ) h1

/-- **(L4)** If `V` is de Rham, a basis of `D_dR(V)` gives an invertible matrix. -/
theorem exists_matrix_of_isDeRhamStd (hB : BdRInvariants p) (ρ : GQp p →* GL (Fin n) ℚ_[p])
    (h : IsDeRhamStd p ρ) : ∃ P : Matrix (Fin n) (Fin n) (BdR p), P.det ≠ 0 ∧
      ∀ σ, matB p (ρ σ : Matrix (Fin n) (Fin n) ℚ_[p]) * P.map (bdrAct p σ) = P := by
  haveI := ddrStd_finiteDimensional p hB ρ
  let b := (Module.finBasis ℚ_[p] (ddrStd p ρ)).reindex (finCongr h)
  let P : Matrix (Fin n) (Fin n) (BdR p) := Matrix.of fun i j => (b j : Fin n → BdR p) i
  have hli : LinearIndependent (BdR p) (fun j => ((b j : ddrStd p ρ) : Fin n → BdR p)) :=
    ddrStd_linearIndependent p hB ρ _ (fun j => (b j).2)
      (LinearIndependent.map' b.linearIndependent (ddrStd p ρ).subtype (Submodule.ker_subtype _))
  refine ⟨P, fun hdet => ?_, fun σ => ?_⟩
  · obtain ⟨v, hv, hPv⟩ := (Matrix.exists_mulVec_eq_zero_iff).mpr hdet
    rw [mulVec_eq_sum_col] at hPv
    exact hv (funext fun j => Fintype.linearIndependent_iff.mp hli v hPv j)
  · ext i j
    have := congrFun ((mem_ddrStd_iff p ρ _).mp (b j).2 σ) i
    rw [Matrix.mul_apply]
    simpa [Matrix.mulVec, dotProduct, bAct, P] using this

theorem map_inv_bdr (σ : GQp p) (P : Matrix (Fin n) (Fin n) (BdR p)) (hP : P.det ≠ 0) :
    (P⁻¹).map (bdrAct p σ) = (P.map (bdrAct p σ))⁻¹ := by
  have hu : IsUnit P.det := isUnit_iff_ne_zero.mpr hP
  symm
  apply Matrix.inv_eq_left_inv
  rw [← Matrix.map_mul, Matrix.nonsing_inv_mul _ hu, Matrix.map_one _ (map_zero _) (map_one _)]

/-- **(a) Duals.** -/
theorem dual_of_bdr (hB : BdRInvariants p) (ρ ρ' : GQp p →* GL (Fin n) ℚ_[p])
    (h' : ∀ σ, (ρ' σ : Matrix (Fin n) (Fin n) ℚ_[p]) = ((ρ σ)⁻¹ : GL (Fin n) ℚ_[p]).val.transpose)
    (h : IsDeRhamStd p ρ) : IsDeRhamStd p ρ' := by
  obtain ⟨P, hP, hrel⟩ := exists_matrix_of_isDeRhamStd p hB ρ h
  have hu : IsUnit P.det := isUnit_iff_ne_zero.mpr hP
  refine isDeRhamStd_of_matrix p hB ρ' (P⁻¹).transpose ?_ fun σ => ?_
  · rw [Matrix.det_transpose]
    exact (Matrix.isUnit_nonsing_inv_det P hu).ne_zero
  · have hPσ : P.map (bdrAct p σ) = matB p (ρ σ⁻¹ : Matrix (Fin n) (Fin n) ℚ_[p]) * P := by
      conv_rhs => rw [← hrel σ]
      rw [← mul_assoc, matB_inv_mul, one_mul]
    have hPσdet : (P.map (bdrAct p σ)).det ≠ 0 := by
      rw [hPσ, Matrix.det_mul]
      refine mul_ne_zero ?_ hP
      intro h0
      have := congrArg Matrix.det (matB_inv_mul p ρ σ)
      rw [Matrix.det_mul, h0, zero_mul, Matrix.det_one] at this
      exact zero_ne_one this
    have hinv : (P.map (bdrAct p σ))⁻¹ = P⁻¹ * matB p (ρ σ : Matrix (Fin n) (Fin n) ℚ_[p]) := by
      apply Matrix.inv_eq_left_inv
      rw [hPσ, mul_assoc, ← mul_assoc (matB p _), matB_mul_inv, one_mul,
        Matrix.nonsing_inv_mul _ hu]
    have hmat' : matB p (ρ' σ : Matrix (Fin n) (Fin n) ℚ_[p]) =
        (matB p (ρ σ⁻¹ : Matrix (Fin n) (Fin n) ℚ_[p])).transpose := by
      rw [h' σ, ← map_inv, matB, matB, Matrix.transpose_map]
    rw [Matrix.transpose_map, map_inv_bdr p σ P hP, hinv, hmat', Matrix.transpose_mul,
      ← mul_assoc, ← Matrix.transpose_mul, matB_mul_inv, Matrix.transpose_one, one_mul]

end BdRSec2
