import ZInQKernel.Contrib.Dim.MvPolynomial
import ZInQKernel.Contrib.Dim.Cotangent

/-!
# Local rings of standard smooth algebras over a field

Copyright: this file is part of the fork Deicyde/diophantine-z-q (task dim-contrib, 2026-11-13,
adopting task infra-smooth-dim, `scratch/infra-smooth-dim/`). Mathlib only.

## Main result

`ZInQ.Contrib.Dim.ringKrullDim_and_spanFinrank_localization`: if `S` has a submersive
presentation `P` over a field `k` (so `S` is standard smooth of relative dimension `P.dimension`)
and `𝔪` is a maximal ideal of `S`, then `S_𝔪` has Krull dimension `P.dimension` and its maximal
ideal is spanned by `P.dimension` elements and no fewer. In particular `S_𝔪` is a regular local
ring of dimension `P.dimension`.

## Proof

Write `S = k[x_ι]/(f_σ)` with invertible Jacobian, and let `M` be the preimage of `𝔪`. Krull's
height theorem and `ht M = |ι|` give `dim S_𝔪 ≥ |ι| - |σ|`. Differentiating a relation
`∑ aᵢ fᵢ ∈ M²` and reducing the Jacobian modulo `M` shows that the `fᵢ` have linearly independent
classes in the cotangent space of `k[x]_M`; so killing them lowers the embedding dimension `|ι|` of
the regular local ring `k[x]_M` by `|σ|`. Finally `dim ≤ edim`.
-/

namespace ZInQ.Contrib.Dim

open Ideal IsLocalRing

variable {k S : Type*} [Field k] [CommRing S] [Algebra k S]
variable {ι σ : Type} [Finite ι] [Finite σ]

/-- The class of a relation in the cotangent space of `k[x]_M`. -/
noncomputable def relationCotangent (P : Algebra.SubmersivePresentation k S ι σ)
    (M : Ideal P.Ring) [M.IsMaximal] (hker : P.ker ≤ M) (i : σ) : maximalIdeal (Localization.AtPrime M) :=
  ⟨algebraMap P.Ring (Localization.AtPrime M) (P.relation i), by
    rw [← Localization.AtPrime.map_eq_maximalIdeal]
    exact Ideal.mem_map_of_mem _ (hker (P.relation_mem_ker i))⟩

/-- Every element of the residue field of `R_M` is the residue of an element of `R`. -/
theorem exists_residue_algebraMap_eq {R : Type*} [CommRing R] (M : Ideal R) [M.IsMaximal]
    (x : ResidueField (Localization.AtPrime M)) :
    ∃ a : R, residue _ (algebraMap R (Localization.AtPrime M) a) = x := by
  obtain ⟨y, hy⟩ :=
    (IsLocalization.AtPrime.equivQuotMaximalIdeal M (Localization.AtPrime M)).surjective x
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective y
  rw [IsLocalization.AtPrime.equivQuotMaximalIdeal_apply_mk] at hy
  exact ⟨a, hy⟩

omit [Finite ι] in
/-- The Jacobian determinant of a submersive presentation lies in no maximal ideal containing the
kernel of `k[x] → S`. -/
theorem jacobiMatrix_det_notMem [Fintype σ] [DecidableEq σ]
    (P : Algebra.SubmersivePresentation k S ι σ) (M : Ideal P.Ring)
    [M.IsMaximal] (hker : P.ker ≤ M) : P.jacobiMatrix.det ∉ M := by
  intro hdet
  have hu := P.jacobian_isUnit
  rw [P.jacobian_eq_jacobiMatrix_det] at hu
  obtain ⟨u, hu⟩ := hu.exists_right_inv
  obtain ⟨a', rfl⟩ := P.algebraMap_surjective u
  have h1 : P.jacobiMatrix.det * a' - 1 ∈ M := hker (by
    show _ ∈ RingHom.ker (algebraMap P.Ring S)
    rw [RingHom.mem_ker, map_sub, map_mul, hu, map_one, sub_self])
  have h2 : P.jacobiMatrix.det * a' ∈ M := M.mul_mem_right _ hdet
  have : (1 : P.Ring) ∈ M := by simpa using M.sub_mem h2 h1
  exact (Ideal.IsMaximal.ne_top inferInstance) ((Ideal.eq_top_iff_one M).mpr this)

omit [Finite ι] in
/-- If `∑ aᵢ fᵢ ∈ M²` then every `aᵢ ∈ M` (differentiate and invert the Jacobian mod `M`). -/
theorem coeffs_mem_of_sum_mem_sq [Fintype σ] [DecidableEq σ]
    (P : Algebra.SubmersivePresentation k S ι σ) (M : Ideal P.Ring) [M.IsMaximal]
    (hker : P.ker ≤ M) (a : σ → P.Ring) (hy2 : ∑ i, a i * P.relation i ∈ M ^ 2) :
    ∀ i, a i ∈ M := by
  have hrM : ∀ i, P.relation i ∈ M := fun i => hker (P.relation_mem_ker i)
  have hder : ∀ j : σ, ∑ i, a i * MvPolynomial.pderiv (P.map j) (P.relation i) ∈ M := by
    intro j
    have h1 := derivation_mem_of_mem_sq (MvPolynomial.pderiv (P.map j)) hy2
    have h2 : MvPolynomial.pderiv (P.map j) (∑ i, a i * P.relation i) =
        ∑ i, a i * MvPolynomial.pderiv (P.map j) (P.relation i)
        + ∑ i, P.relation i * MvPolynomial.pderiv (P.map j) (a i) := by
      simp only [map_sum, Derivation.leibniz, smul_eq_mul, Finset.sum_add_distrib]
    rw [h2] at h1
    have h3 : ∑ i, P.relation i * MvPolynomial.pderiv (P.map j) (a i) ∈ M :=
      Ideal.sum_mem _ fun i _ => M.mul_mem_right _ (hrM i)
    have := M.sub_mem h1 h3
    rwa [add_sub_cancel_right] at this
  let _ : Field (P.Ring ⧸ M) := Ideal.Quotient.field M
  let J := P.jacobiMatrix.map (Ideal.Quotient.mk M)
  have hJ : J.det ≠ 0 := by
    rw [show J.det = Ideal.Quotient.mk M P.jacobiMatrix.det from (RingHom.map_det _ _).symm,
      Ne, Ideal.Quotient.eq_zero_iff_mem]
    exact jacobiMatrix_det_notMem P M hker
  have hv : Matrix.mulVec J (fun i => Ideal.Quotient.mk M (a i)) = 0 := by
    ext j
    simp only [Matrix.mulVec, dotProduct, J, Matrix.map_apply, Pi.zero_apply]
    rw [← Ideal.Quotient.eq_zero_iff_mem.mpr (hder j), map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [P.jacobiMatrix_apply, map_mul, mul_comm]
  have := Matrix.eq_zero_of_mulVec_eq_zero hJ hv
  intro i
  have hi := congrFun this i
  rwa [Pi.zero_apply, Ideal.Quotient.eq_zero_iff_mem] at hi

omit [Finite ι] in
/-- A relation among the cotangent classes, with coefficients lifted to `k[x]`, gives an element
`∑ aᵢ fᵢ` of `M²`. -/
theorem sum_mem_sq_of_cotangent [Fintype σ]
    (P : Algebra.SubmersivePresentation k S ι σ) (M : Ideal P.Ring) [M.IsMaximal]
    (hker : P.ker ≤ M) (a : σ → P.Ring)
    (hc : ∑ i, algebraMap P.Ring (Localization.AtPrime M) (a i) •
      (maximalIdeal (Localization.AtPrime M)).toCotangent (relationCotangent P M hker i) = 0) :
    ∑ i, a i * P.relation i ∈ M ^ 2 := by
  rw [← IsLocalization.AtPrime.under_maximalIdeal_pow M (Localization.AtPrime M) 2,
    Ideal.mem_comap]
  simp_rw [← map_smul, ← map_sum, Ideal.toCotangent_eq_zero] at hc
  convert hc using 1
  rw [Submodule.coe_sum, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Submodule.coe_smul, smul_eq_mul, map_mul]
  rfl

omit [Finite ι] in
/-- The relations of a submersive presentation have linearly independent classes in the cotangent
space of `k[x]_M`, for any maximal ideal `M ⊇ ker (k[x] → S)`. -/
theorem linearIndependent_relationCotangent (P : Algebra.SubmersivePresentation k S ι σ)
    (M : Ideal P.Ring) [M.IsMaximal] (hker : P.ker ≤ M) :
    LinearIndependent (ResidueField (Localization.AtPrime M))
      (fun i => (maximalIdeal (Localization.AtPrime M)).toCotangent
        (relationCotangent P M hker i)) := by
  classical
  have := Fintype.ofFinite σ
  rw [Fintype.linearIndependent_iff]
  intro c hc
  choose a ha using exists_residue_algebraMap_eq M
  have hc' : ∑ i, algebraMap P.Ring (Localization.AtPrime M) (a (c i)) •
      (maximalIdeal (Localization.AtPrime M)).toCotangent (relationCotangent P M hker i) = 0 := by
    rw [← hc]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← algebraMap_smul (ResidueField (Localization.AtPrime M)), ResidueField.algebraMap_eq,
      ha (c i)]
  have hmem := coeffs_mem_of_sum_mem_sq P M hker (fun i => a (c i))
    (sum_mem_sq_of_cotangent P M hker _ hc')
  intro i
  rw [← ha (c i), residue_eq_zero_iff, ← Localization.AtPrime.map_eq_maximalIdeal]
  exact Ideal.mem_map_of_mem _ (hmem i)

/-! ## §3 Dimension and embedding dimension of `S_𝔪` -/

/-- **Main algebraic theorem.** For a submersive presentation `P` of `S` over a field `k` and a
maximal ideal `𝔪` of `S`: `dim S_𝔪 = P.dimension` and `𝔪 S_𝔪` is spanned by `P.dimension`
elements (and no fewer). -/
theorem ringKrullDim_and_spanFinrank_localization (P : Algebra.SubmersivePresentation k S ι σ)
    (m : Ideal S) [m.IsMaximal] :
    ringKrullDim (Localization.AtPrime m) = P.dimension ∧
      (maximalIdeal (Localization.AtPrime m)).spanFinrank = P.dimension := by
  classical
  have := Fintype.ofFinite σ
  have hφs : Function.Surjective (algebraMap P.Ring S) := P.algebraMap_surjective
  have hkerφ : ∀ x ∈ P.ker, algebraMap P.Ring S x = 0 := fun x hx => hx
  obtain ⟨M, hMdef⟩ : ∃ M, M = m.comap (algebraMap P.Ring S) := ⟨_, rfl⟩
  have : M.IsMaximal := hMdef ▸ Ideal.comap_isMaximal_of_surjective _ hφs
  have hker : P.ker ≤ M := fun x hx => by
    rw [hMdef, Ideal.mem_comap, hkerφ x hx]
    exact m.zero_mem
  have : IsNoetherianRing S := isNoetherianRing_of_surjective _ _ _ hφs
  -- lower bound (Krull's height theorem)
  have hM : M.height = Nat.card ι := height_eq_natCard_of_isMaximal_mvPolynomial k ι M
  have hK := Ideal.height_le_height_add_spanFinrank_of_le hker
  have hspan : P.ker.spanFinrank ≤ Nat.card σ := by
    rw [← P.span_range_relation_eq_ker]
    refine (Submodule.spanFinrank_span_le_ncard_of_finite (Set.finite_range _)).trans ?_
    rw [← Set.image_univ]
    exact (Set.ncard_image_le Set.finite_univ).trans (Set.ncard_univ _).le
  have hquot : (M.map (Ideal.Quotient.mk P.ker)).height = m.height := by
    let e : (P.Ring ⧸ P.ker) ≃+* S := RingHom.quotientKerEquivOfSurjective hφs
    refine (e.height_map _).symm.trans (congrArg Ideal.height ?_)
    change Ideal.map (e : P.Ring ⧸ P.ker →+* S) _ = m
    rw [Ideal.map_map]
    have : (e : P.Ring ⧸ P.ker →+* S).comp (Ideal.Quotient.mk P.ker) = algebraMap P.Ring S :=
      RingHom.ext fun x => RingHom.quotientKerEquivOfSurjective_apply_mk hφs x
    rw [this, hMdef, Ideal.map_comap_of_surjective _ hφs]
  rw [hquot, hM] at hK
  have hdimC : ringKrullDim (Localization.AtPrime m) = m.height :=
    IsLocalization.AtPrime.ringKrullDim_eq_height m (Localization.AtPrime m)
  -- upper bound (embedding dimension)
  let ψ := Localization.localRingHom M m (algebraMap P.Ring S) hMdef
  have hcomp : ψ.comp (algebraMap P.Ring (Localization.AtPrime M)) =
      (algebraMap S (Localization.AtPrime m)).comp (algebraMap P.Ring S) := by
    ext x
    · exact Localization.localRingHom_to_map M m _ hMdef _
    · exact Localization.localRingHom_to_map M m _ hMdef _
  have hmap : (maximalIdeal (Localization.AtPrime M)).map ψ =
      maximalIdeal (Localization.AtPrime m) := by
    rw [← Localization.AtPrime.map_eq_maximalIdeal, ← Localization.AtPrime.map_eq_maximalIdeal,
      Ideal.map_map, hcomp, ← Ideal.map_map, hMdef, Ideal.map_comap_of_surjective _ hφs]
  have hkill : ∀ i, ψ (relationCotangent P M hker i) = 0 := by
    intro i
    change ψ (algebraMap P.Ring (Localization.AtPrime M) (P.relation i)) = 0
    rw [← RingHom.comp_apply, hcomp, RingHom.comp_apply, hkerφ _ (P.relation_mem_ker i), map_zero]
  have hU := spanFinrank_maximalIdeal_add_card_le ψ hmap (relationCotangent P M hker)
    (linearIndependent_relationCotangent P M hker)
    hkill
  have hB : ((maximalIdeal (Localization.AtPrime M)).spanFinrank : WithBot ℕ∞) = Nat.card ι := by
    rw [IsRegularLocalRing.spanFinrank_maximalIdeal,
      IsLocalization.AtPrime.ringKrullDim_eq_height M (Localization.AtPrime M), hM]
    rfl
  have hB' : (maximalIdeal (Localization.AtPrime M)).spanFinrank = Nat.card ι := by
    exact_mod_cast hB
  have hle := ringKrullDim_le_spanFinrank_maximalIdeal (Localization.AtPrime m)
  rw [hdimC] at hle
  have hle' : m.height ≤ ((maximalIdeal (Localization.AtPrime m)).spanFinrank : ℕ∞) := by
    exact_mod_cast hle
  obtain ⟨h, hh⟩ := ENat.ne_top_iff_exists.mp (ne_top_of_le_ne_top (ENat.natCast_ne_top _) hle')
  rw [← hh] at hle' hK
  rw [hB', Fintype.card_eq_nat_card] at hU
  rw [hdimC, ← hh]
  simp only [Algebra.Presentation.dimension]
  have hK' : Nat.card ι ≤ h + P.ker.spanFinrank := by exact_mod_cast hK
  have hle'' : h ≤ (maximalIdeal (Localization.AtPrime m)).spanFinrank := by exact_mod_cast hle'
  constructor
  · have : h = Nat.card ι - Nat.card σ := by omega
    rw [this]; rfl
  · omega

end ZInQ.Contrib.Dim
