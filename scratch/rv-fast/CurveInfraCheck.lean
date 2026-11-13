import Mathlib
import ZInQKernel.HDecomp.LeafPush2.R18

/-! # Local rings of smooth schemes over a field (§0-§3 = StdSmoothLocal.lean verbatim)

Task infra-smooth-dim. Mathlib-only. (Lemmas from `MaxHeight.lean` and `CotQuot.lean` are copied
verbatim in §0, since scratch files cannot import each other.)

**Main result.** If `S` is a standard smooth algebra of relative dimension `n` over a field `k` and
`𝔪` is a maximal ideal of `S`, then `S_𝔪` has Krull dimension `n` and its maximal ideal is spanned by
`n` elements (so `S_𝔪` is regular, and `dim_κ 𝔪/𝔪² = n`).

Proof: write `S = k[x_ι]/(f_σ)` with invertible Jacobian, `M` the preimage of `𝔪`. Krull's height
theorem and `ht M = |ι|` give `dim S_𝔪 ≥ |ι| - |σ|`; the derivatives `∂f_i/∂x_{map j}` show that
the `f_i` have linearly independent classes in `M A_M / M² A_M`, so killing them lowers the embedding
dimension `|ι|` of the regular local ring `k[x]_M` by `|σ|`; and `dim ≤ edim`. -/

open Ideal IsLocalRing

namespace InfraSmoothDim

/-! ## §0 Copied from `MaxHeight.lean` and `CotQuot.lean` -/

theorem height_isMaximal_mvPolynomial (k : Type*) [Field k] :
    ∀ (ι : Type) [Finite ι] (M : Ideal (MvPolynomial ι k)) [M.IsMaximal],
      M.height = Nat.card ι := by
  intro ι _
  induction ι using Finite.induction_empty_option with
  | of_equiv e H =>
    intro M _
    have e' := (MvPolynomial.renameEquiv k e).toRingEquiv
    have : (M.map e'.symm).IsMaximal := map_isMaximal_of_equiv e'.symm
    rw [← e'.symm.height_map M, H, Nat.card_congr e]
  | h_empty =>
    intro M _
    have h1 := Ideal.height_le_ringKrullDim_of_ne_top (I := M) IsPrime.ne_top'
    rw [MvPolynomial.ringKrullDim_of_isNoetherianRing_of_finite, ringKrullDim_eq_zero_of_field]
      at h1
    simp only [Nat.card_of_isEmpty, CharP.cast_eq_zero, add_zero] at h1
    simp only [Nat.card_of_isEmpty, CharP.cast_eq_zero]
    exact_mod_cast nonpos_iff_eq_zero.mp (by exact_mod_cast h1)
  | @h_option α _ IH =>
    intro M _
    let e := (MvPolynomial.optionEquivLeft k α).toRingEquiv
    let P := M.map e
    have : P.IsMaximal := map_isMaximal_of_equiv e
    let p := P.comap (Polynomial.C : MvPolynomial α k →+* _)
    have : p.IsMaximal := Polynomial.isMaximal_comap_C_of_isJacobsonRing P
    have : P.LiesOver p := ⟨rfl⟩
    rw [← e.height_map M, Polynomial.height_eq_height_add_one p P, IH p]
    simp [Nat.card_eq_fintype_card, Fintype.card_option]

theorem spanFinrank_add_card_le {B C : Type*} [CommRing B] [IsLocalRing B] [IsNoetherianRing B]
    [CommRing C] [IsLocalRing C] (ψ : B →+* C)
    (hmap : (maximalIdeal B).map ψ = maximalIdeal C)
    {σ : Type*} [Fintype σ] (f : σ → maximalIdeal B)
    (hf : LinearIndependent (ResidueField B) (fun i => (maximalIdeal B).toCotangent (f i)))
    (hker : ∀ i, ψ (f i) = 0) :
    (maximalIdeal C).spanFinrank + Fintype.card σ ≤ (maximalIdeal B).spanFinrank := by
  classical
  set κ := ResidueField B
  set V := CotangentSpace B
  let v : σ → V := fun i => (maximalIdeal B).toCotangent (f i)
  let W : Submodule κ V := Submodule.span κ (Set.range v)
  have hW : Module.finrank κ W = Fintype.card σ := finrank_span_eq_card hf
  have hVW := Submodule.finrank_quotient_add_finrank W
  set d := Module.finrank κ (V ⧸ W)
  let b := Module.finBasis κ (V ⧸ W)
  have hsurj : Function.Surjective
      (fun x : maximalIdeal B => W.mkQ ((maximalIdeal B).toCotangent x)) :=
    (Submodule.mkQ_surjective W).comp (Ideal.toCotangent_surjective _)
  choose g hg using fun j : Fin d => hsurj (b j)
  -- the classes of `f` and `g` span `V`
  let s : Set (maximalIdeal B) := Set.range f ∪ Set.range g
  have hspan : Submodule.span κ ((maximalIdeal B).toCotangent '' s) = ⊤ := by
    have h1 : W ≤ Submodule.span κ ((maximalIdeal B).toCotangent '' s) := by
      refine Submodule.span_le.mpr ?_
      rintro _ ⟨i, rfl⟩
      exact Submodule.subset_span ⟨f i, Or.inl ⟨i, rfl⟩, rfl⟩
    have h2 : (Submodule.span κ ((maximalIdeal B).toCotangent '' s)).map W.mkQ = ⊤ := by
      rw [eq_top_iff, ← b.span_eq, Submodule.span_le]
      rintro _ ⟨j, rfl⟩
      rw [← hg j]
      exact Submodule.mem_map_of_mem (Submodule.subset_span ⟨g j, Or.inr ⟨j, rfl⟩, rfl⟩)
    have := Submodule.comap_map_mkQ W (Submodule.span κ ((maximalIdeal B).toCotangent '' s))
    rw [h2, Submodule.comap_top, sup_eq_right.mpr h1] at this
    exact this.symm
  have hspanB : Submodule.span B s = ⊤ := (CotangentSpace.span_image_eq_top_iff).mp hspan
  have hmB : maximalIdeal B = Ideal.span (((↑) : maximalIdeal B → B) '' s) := by
    have := congrArg (Submodule.map (maximalIdeal B).subtype) hspanB
    rw [Submodule.map_span, Submodule.map_top, Submodule.range_subtype] at this
    exact this.symm
  have hmC : maximalIdeal C = Ideal.span (Set.range fun j => ψ (g j)) := by
    rw [← hmap, congrArg (Ideal.map ψ) hmB, Ideal.map_span]
    refine le_antisymm (Ideal.span_le.mpr ?_) (Ideal.span_le.mpr ?_)
    · rintro _ ⟨_, ⟨x, hx | hx, rfl⟩, rfl⟩
      · obtain ⟨i, rfl⟩ := hx
        simp [hker i]
      · obtain ⟨j, rfl⟩ := hx
        exact Ideal.subset_span ⟨j, rfl⟩
    · rintro _ ⟨j, rfl⟩
      exact Ideal.subset_span ⟨_, ⟨g j, Or.inr ⟨j, rfl⟩, rfl⟩, rfl⟩
  have hle : (maximalIdeal C).spanFinrank ≤ d := by
    rw [hmC]
    have := Submodule.spanFinrank_span_le_ncard_of_finite (R := C)
      (Set.finite_range fun j => ψ (g j))
    refine this.trans ?_
    have h3 : (Set.range fun j => ψ (g j)).ncard ≤ Nat.card (Fin d) := by
      rw [← Set.image_univ]
      exact (Set.ncard_image_le Set.finite_univ).trans (Set.ncard_univ _).le
    rw [Nat.card_fin] at h3
    exact h3
  rw [spanFinrank_maximalIdeal_eq_finrank_cotangentSpace B]
  change _ ≤ Module.finrank κ V
  omega

/-! ## §1 Derivatives vanish modulo `M` on `M²` -/

theorem derivation_mem_of_mem_sq {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]
    (D : Derivation R A A) {M : Ideal A} {x : A} (hx : x ∈ M ^ 2) : D x ∈ M := by
  rw [pow_two] at hx
  refine Submodule.mul_induction_on hx ?_ ?_
  · intro a ha b hb
    rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul]
    exact add_mem (M.mul_mem_right _ ha) (M.mul_mem_right _ hb)
  · intro x y hx hy
    rw [map_add]
    exact add_mem hx hy

/-! ## §2 The main theorem -/

variable {k S : Type*} [Field k] [CommRing S] [Algebra k S]
variable {ι σ : Type} [Finite ι] [Finite σ]

/-- The class of a relation in the cotangent space of `k[x]_M`. -/
noncomputable def relCot (P : Algebra.SubmersivePresentation k S ι σ) (M : Ideal P.Ring)
    [M.IsMaximal] (hker : P.ker ≤ M) (i : σ) : maximalIdeal (Localization.AtPrime M) :=
  ⟨algebraMap P.Ring (Localization.AtPrime M) (P.relation i), by
    rw [← Localization.AtPrime.map_eq_maximalIdeal]
    exact Ideal.mem_map_of_mem _ (hker (P.relation_mem_ker i))⟩

theorem exists_residue_algebraMap_eq {R : Type*} [CommRing R] (M : Ideal R) [M.IsMaximal]
    (x : ResidueField (Localization.AtPrime M)) :
    ∃ a : R, residue _ (algebraMap R (Localization.AtPrime M) a) = x := by
  obtain ⟨y, hy⟩ :=
    (IsLocalization.AtPrime.equivQuotMaximalIdeal M (Localization.AtPrime M)).surjective x
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective y
  rw [IsLocalization.AtPrime.equivQuotMaximalIdeal_apply_mk] at hy
  exact ⟨a, hy⟩

omit [Finite ι] in
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
      (maximalIdeal (Localization.AtPrime M)).toCotangent (relCot P M hker i) = 0) :
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
theorem linearIndependent_relCot (P : Algebra.SubmersivePresentation k S ι σ) (M : Ideal P.Ring)
    [M.IsMaximal] (hker : P.ker ≤ M) :
    LinearIndependent (ResidueField (Localization.AtPrime M))
      (fun i => (maximalIdeal (Localization.AtPrime M)).toCotangent (relCot P M hker i)) := by
  classical
  have := Fintype.ofFinite σ
  rw [Fintype.linearIndependent_iff]
  intro c hc
  choose a ha using exists_residue_algebraMap_eq M
  have hc' : ∑ i, algebraMap P.Ring (Localization.AtPrime M) (a (c i)) •
      (maximalIdeal (Localization.AtPrime M)).toCotangent (relCot P M hker i) = 0 := by
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
  have hM : M.height = Nat.card ι := height_isMaximal_mvPolynomial k ι M
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
  have hkill : ∀ i, ψ (relCot P M hker i) = 0 := by
    intro i
    change ψ (algebraMap P.Ring (Localization.AtPrime M) (P.relation i)) = 0
    rw [← RingHom.comp_apply, hcomp, RingHom.comp_apply, hkerφ _ (P.relation_mem_ker i), map_zero]
  have hU := spanFinrank_add_card_le ψ hmap (relCot P M hker) (linearIndependent_relCot P M hker)
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

end InfraSmoothDim


/-! ## §4 Scheme stalks (task infra-smooth-dim) -/

namespace InfraSmoothDim

open CategoryTheory AlgebraicGeometry

/-- The algebraic theorem over a base ring that is a field (without a `Field` instance). -/
theorem ringKrullDim_and_spanFinrank_of_isField {R S : Type*} [CommRing R] [CommRing S]
    (hR : IsField R) (φ : R →+* S) (n : ℕ) (h : φ.IsStandardSmoothOfRelativeDimension n)
    (m : Ideal S) [m.IsMaximal] :
    ringKrullDim (Localization.AtPrime m) = n ∧
      (maximalIdeal (Localization.AtPrime m)).spanFinrank = n := by
  let _ := hR.toField
  let _ := φ.toAlgebra
  obtain ⟨ι, σ, _, _, P, hP⟩ :=
    (h : @Algebra.IsStandardSmoothOfRelativeDimension n R S _ _ φ.toAlgebra).out
  rw [← hP]
  exact ringKrullDim_and_spanFinrank_localization P m

/-- Sections of `Spec K` over a nonempty open form a field. -/
theorem isField_sections_spec (K : Type*) [Field K] (U : (Spec (CommRingCat.of K)).Opens)
    (hU : (U : Set (Spec (CommRingCat.of K))).Nonempty) :
    IsField Γ(Spec (CommRingCat.of K), U) := by
  have hUt : U = ⊤ := by
    obtain ⟨z, hz⟩ := hU
    refine eq_top_iff.mpr fun y _ => ?_
    have : Subsingleton (Spec (CommRingCat.of K)) :=
      inferInstanceAs (Subsingleton (PrimeSpectrum K))
    rwa [Subsingleton.elim y z]
  subst hUt
  exact (Scheme.ΓSpecIso (CommRingCat.of K)).commRingCatIsoToRingEquiv.toMulEquiv.isField
    (Field.toIsField K)

/-- **Local form.** If `f : X → Spec K` is standard smooth of relative dimension `n` on an affine
chart `V → U` containing a closed point `x`, then `dim 𝒪_{X,x} = n` and `𝔪_x` is spanned by `n`
elements (so `dim_{κ(x)} 𝔪_x/𝔪_x² = n`). -/
theorem stalk_dim_of_chart {K : Type*} [Field K] {X : Scheme} (f : X ⟶ Spec (CommRingCat.of K))
    {U : (Spec (CommRingCat.of K)).Opens} (hU : IsAffineOpen U) {V : X.Opens} (hV : IsAffineOpen V)
    (e : V ≤ f ⁻¹ᵁ U) (n : ℕ)
    (h : RingHom.IsStandardSmoothOfRelativeDimension n (f.appLE U V e).hom)
    (x : X) (hxV : x ∈ V) (hx : IsClosed ({x} : Set X)) :
    ringKrullDim (X.presheaf.stalk x) = n ∧
      (maximalIdeal (X.presheaf.stalk x)).spanFinrank = n := by
  have hR := isField_sections_spec K U ⟨f.base x, e hxV⟩
  have hmax := hV.primeIdealOf_isMaximal_of_isClosed ⟨x, hxV⟩ hx
  obtain ⟨h1, h2⟩ := ringKrullDim_and_spanFinrank_of_isField hR _ n h
    (hV.primeIdealOf ⟨x, hxV⟩).asIdeal
  let _ := X.presheaf.algebra_section_stalk ⟨x, hxV⟩
  have := hV.isLocalization_stalk ⟨x, hxV⟩
  let eq : Localization.AtPrime (hV.primeIdealOf ⟨x, hxV⟩).asIdeal ≃+* X.presheaf.stalk x :=
    (IsLocalization.algEquiv (hV.primeIdealOf ⟨x, hxV⟩).asIdeal.primeCompl _ _).toRingEquiv
  constructor
  · rw [← ringKrullDim_eq_of_ringEquiv eq, h1]
  · rw [← map_ringEquiv_maximalIdeal eq, Ideal.spanFinrank_map_eq_of_ringEquiv, h2]

/-- **Smooth of relative dimension `n` over a field.** At every closed point, the local ring has
Krull dimension `n` and embedding dimension `n` (it is a regular local ring of dimension `n`). -/
theorem stalk_dim_of_smoothOfRelativeDimension {K : Type*} [Field K] {X : Scheme}
    (f : X ⟶ Spec (CommRingCat.of K)) (n : ℕ) [SmoothOfRelativeDimension n f]
    (x : X) (hx : IsClosed ({x} : Set X)) :
    ringKrullDim (X.presheaf.stalk x) = n ∧
      (maximalIdeal (X.presheaf.stalk x)).spanFinrank = n := by
  obtain ⟨U, hU, V, hV, hxV, e, h⟩ :=
    SmoothOfRelativeDimension.exists_isStandardSmoothOfRelativeDimension (n := n) (f := f) x
  exact stalk_dim_of_chart f hU hV e n h x hxV hx

/-- **Smooth over a field.** At every closed point, the local ring is regular: its Krull dimension
equals its embedding dimension, and both equal the relative dimension of a standard smooth chart
around the point. -/
theorem exists_stalk_dim_of_smooth {K : Type*} [Field K] {X : Scheme}
    (f : X ⟶ Spec (CommRingCat.of K)) [Smooth f] (x : X) (hx : IsClosed ({x} : Set X)) :
    ∃ n : ℕ, ringKrullDim (X.presheaf.stalk x) = n ∧
      (maximalIdeal (X.presheaf.stalk x)).spanFinrank = n := by
  obtain ⟨U, hU, V, hV, hxV, e, h⟩ := Smooth.exists_isStandardSmooth f x
  let _ := (f.appLE U V e).hom.toAlgebra
  have h' : Algebra.IsStandardSmooth Γ(Spec (CommRingCat.of K), U) Γ(X, V) := h
  have := h'.out
  obtain ⟨ι, σ, _, _, ⟨P⟩⟩ := this
  exact ⟨P.dimension, stalk_dim_of_chart f hU hV e P.dimension
    (P.isStandardSmoothOfRelativeDimension rfl) x hxV hx⟩

/-- **Chart form.** Around every point of a smooth `K`-scheme there is an open set `V` and an
`n` such that every closed point of `V` has local ring of dimension and embedding dimension `n`. -/
theorem exists_nbhd_stalk_dim {K : Type*} [Field K] {X : Scheme}
    (f : X ⟶ Spec (CommRingCat.of K)) [Smooth f] (x : X) :
    ∃ (V : X.Opens) (n : ℕ), x ∈ V ∧ ∀ y ∈ V, IsClosed ({y} : Set X) →
      ringKrullDim (X.presheaf.stalk y) = n ∧
        (maximalIdeal (X.presheaf.stalk y)).spanFinrank = n := by
  obtain ⟨U, hU, V, hV, hxV, e, h⟩ := Smooth.exists_isStandardSmooth f x
  let _ := (f.appLE U V e).hom.toAlgebra
  have h' : Algebra.IsStandardSmooth Γ(Spec (CommRingCat.of K), U) Γ(X, V) := h
  have := h'.out
  obtain ⟨ι, σ, _, _, ⟨P⟩⟩ := this
  exact ⟨V, P.dimension, hxV, fun y hy hyc => stalk_dim_of_chart f hU hV e P.dimension
    (P.isStandardSmoothOfRelativeDimension rfl) y hy hyc⟩

/-- On an irreducible smooth `K`-scheme all closed points have local rings of the same
dimension. -/
theorem stalk_dim_eq_of_closed {K : Type*} [Field K] {X : Scheme}
    (f : X ⟶ Spec (CommRingCat.of K)) [Smooth f] [IrreducibleSpace X]
    (z w : X) (hz : IsClosed ({z} : Set X)) (hw : IsClosed ({w} : Set X)) :
    ringKrullDim (X.presheaf.stalk z) = ringKrullDim (X.presheaf.stalk w) := by
  have : JacobsonSpace X := LocallyOfFiniteType.jacobsonSpace f
  obtain ⟨Vz, nz, hzV, hz'⟩ := exists_nbhd_stalk_dim f z
  obtain ⟨Vw, nw, hwV, hw'⟩ := exists_nbhd_stalk_dim f w
  have hne : ((Vz : Set X) ∩ Vw).Nonempty :=
    nonempty_preirreducible_inter Vz.2 Vw.2 ⟨z, hzV⟩ ⟨w, hwV⟩
  obtain ⟨u, ⟨huz, huw⟩, hu⟩ :=
    nonempty_inter_closedPoints hne (Vz.2.inter Vw.2).isLocallyClosed
  rw [(hz' z hzV hz).1, (hw' w hwV hw).1, ← (hz' u huz hu).1, (hw' u huw hu).1]

/-- **Dimension of an irreducible smooth `K`-scheme.** Its dimension equals the Krull dimension of
the local ring at any closed point, which equals the embedding dimension there. -/
theorem topologicalKrullDim_eq_of_smooth {K : Type*} [Field K] {X : Scheme}
    (f : X ⟶ Spec (CommRingCat.of K)) [Smooth f] [IrreducibleSpace X]
    (x : X) (hx : IsClosed ({x} : Set X)) :
    topologicalKrullDim X = ringKrullDim (X.presheaf.stalk x) ∧
      ((maximalIdeal (X.presheaf.stalk x)).spanFinrank : WithBot ℕ∞) =
        ringKrullDim (X.presheaf.stalk x) := by
  have : JacobsonSpace X := LocallyOfFiniteType.jacobsonSpace f
  obtain ⟨n, hn1, hn2⟩ := exists_stalk_dim_of_smooth f x hx
  refine ⟨?_, by rw [hn1, hn2]⟩
  have hdim : topologicalKrullDim X = Order.krullDim X :=
    Order.krullDim_eq_of_orderIso (irreducibleSetEquivPoints (α := X))
  rw [hdim]
  refine le_antisymm ?_ ?_
  · rw [Order.krullDim_eq_iSup_coheight]
    refine iSup_le fun y => ?_
    obtain ⟨z, hz, hzc⟩ := nonempty_inter_closedPoints (Z := closure ({y} : Set X))
      ⟨y, subset_closure rfl⟩ isClosed_closure.isLocallyClosed
    have hyz : z ≤ y := specializes_iff_mem_closure.mpr hz
    calc (Order.coheight y : WithBot ℕ∞) ≤ Order.coheight z := by
          exact_mod_cast Order.coheight_anti hyz
      _ = ringKrullDim (X.presheaf.stalk z) := (ringKrullDim_stalk_eq_coheight z).symm
      _ = ringKrullDim (X.presheaf.stalk x) := stalk_dim_eq_of_closed f z x hzc hx
      _ = ringKrullDim (X.presheaf.stalk x) := rfl
  · rw [ringKrullDim_stalk_eq_coheight]
    exact Order.coheight_le_krullDim x


/-! ### Corollaries: regularity, cotangent dimension, rational points, dimension of `X` -/

/-- **Smooth over a field ⇒ regular at closed points.** -/
theorem isRegularLocalRing_stalk_of_smooth {K : Type*} [Field K] {X : Scheme}
    (f : X ⟶ Spec (CommRingCat.of K)) [Smooth f] (x : X) (hx : IsClosed ({x} : Set X)) :
    IsRegularLocalRing (X.presheaf.stalk x) := by
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  obtain ⟨n, h1, h2⟩ := exists_stalk_dim_of_smooth f x hx
  exact (isRegularLocalRing_iff _).mpr (by rw [h1, h2])

/-- **Cotangent space at a closed point.** If `X → Spec K` is smooth of relative dimension `n`
and `x` is a closed point, then `dim_{κ(x)} 𝔪_x/𝔪_x² = n`. -/
theorem finrank_cotangentSpace_of_smoothOfRelativeDimension {K : Type*} [Field K] {X : Scheme}
    (f : X ⟶ Spec (CommRingCat.of K)) (n : ℕ) [SmoothOfRelativeDimension n f]
    (x : X) (hx : IsClosed ({x} : Set X)) :
    Module.finrank (ResidueField (X.presheaf.stalk x)) (CotangentSpace (X.presheaf.stalk x)) =
      n := by
  have : Smooth f := SmoothOfRelativeDimension.smooth n f
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  rw [← spanFinrank_maximalIdeal_eq_finrank_cotangentSpace]
  exact (stalk_dim_of_smoothOfRelativeDimension f n x hx).2

/-- The image of a `K`-point (a section of `X → Spec K`) is a closed point. -/
theorem isClosed_of_section {K : Type*} [Field K] {X : Scheme}
    (f : X ⟶ Spec (CommRingCat.of K)) (s : Spec (CommRingCat.of K) ⟶ X) (hs : s ≫ f = 𝟙 _)
    (p : Spec (CommRingCat.of K)) : IsClosed ({s.base p} : Set X) := by
  have := isClosedImmersion_of_comp_eq_id (Y := Spec (CommRingCat.of K)) f s hs
  have hr : Set.range s.base = {s.base p} := by
    ext y
    constructor
    · rintro ⟨a, rfl⟩
      have : Subsingleton (PrimeSpectrum K) := inferInstance
      exact congrArg _ (Subsingleton.elim (α := PrimeSpectrum K) a p)
    · rintro rfl
      exact ⟨_, rfl⟩
  rw [← hr]
  exact s.isClosedEmbedding.isClosed_range

/-- **Cotangent space at a rational point.** If `X → Spec K` is smooth of relative dimension `n`
and `s` is a `K`-point, then the local ring at `s` has dimension `n` and its cotangent space
`𝔪/𝔪²` has dimension `n` over the residue field. -/
theorem stalk_dims_of_section {K : Type*} [Field K] {X : Scheme}
    (f : X ⟶ Spec (CommRingCat.of K)) (n : ℕ) [SmoothOfRelativeDimension n f]
    (s : Spec (CommRingCat.of K) ⟶ X) (hs : s ≫ f = 𝟙 _) (p : Spec (CommRingCat.of K)) :
    ringKrullDim (X.presheaf.stalk (s.base p)) = n ∧
      Module.finrank (ResidueField (X.presheaf.stalk (s.base p)))
        (CotangentSpace (X.presheaf.stalk (s.base p))) = n :=
  ⟨(stalk_dim_of_smoothOfRelativeDimension f n _ (isClosed_of_section f s hs p)).1,
    finrank_cotangentSpace_of_smoothOfRelativeDimension f n _ (isClosed_of_section f s hs p)⟩

/-- **Dimension of an irreducible smooth `K`-scheme of relative dimension `n`** is `n`. -/
theorem topologicalKrullDim_eq_of_smoothOfRelativeDimension {K : Type*} [Field K] {X : Scheme}
    (f : X ⟶ Spec (CommRingCat.of K)) (n : ℕ) [SmoothOfRelativeDimension n f]
    [IrreducibleSpace X] : topologicalKrullDim X = n := by
  have : Smooth f := SmoothOfRelativeDimension.smooth n f
  have : JacobsonSpace X := LocallyOfFiniteType.jacobsonSpace f
  have : Nonempty X := IrreducibleSpace.toNonempty
  obtain ⟨x, -, hx⟩ := nonempty_inter_closedPoints (Z := (Set.univ : Set X))
    Set.univ_nonempty isClosed_univ.isLocallyClosed
  rw [(topologicalKrullDim_eq_of_smooth f x hx).1,
    (stalk_dim_of_smoothOfRelativeDimension f n x hx).1]

end InfraSmoothDim


set_option linter.style.haveILetI false

open Order

universe u

namespace CurveInfra

/-- Copied verbatim from g0-dim (`scratch/g0-dim/part_dim.lean`). -/
theorem ringKrullDim_eq_of_isIntegral_of_injective {A B : Type*} [CommRing A] [CommRing B]
    [Algebra A B] [Algebra.IsIntegral A B] (hinj : Function.Injective (algebraMap A B)) :
    ringKrullDim B = ringKrullDim A := by
  apply le_antisymm
  · refine Order.krullDim_le_of_strictMono (PrimeSpectrum.comap (algebraMap A B)) ?_
    intro P Q hPQ
    have h : P.asIdeal < Q.asIdeal := hPQ
    exact Ideal.IsIntegral.under_lt_under (R := A) h
  · refine iSup_le fun l => ?_
    obtain ⟨P, -, hP, hPl⟩ := Ideal.exists_ideal_over_prime_of_isIntegral (S := B)
      l.head.asIdeal ⊥ (by
        intro x hx
        have : algebraMap A B x = 0 := by simpa using hx
        have : x = 0 := hinj (by simpa using this)
        simp [this])
    haveI : P.LiesOver l.head.asIdeal := ⟨hPl.symm⟩
    obtain ⟨L, hlen, -, -⟩ := Ideal.exists_ltSeries_of_hasGoingUp l P
    rw [← hlen]
    exact L.length_le_krullDim

theorem ringKrullDim_mvPolynomial_field (k : Type*) [Field k] (s : ℕ) :
    ringKrullDim (MvPolynomial (Fin s) k) = s := by
  rw [MvPolynomial.ringKrullDim_of_isNoetherianRing_of_finite, ringKrullDim_eq_zero_of_field]
  simp

/-- Noether normalization data for a domain of finite type: `dim R = s = trdeg_K R`. -/
theorem exists_dim_eq_trdeg (K : Type u) [Field K] (R : Type u) [CommRing R] [IsDomain R]
    [Algebra K R] [Algebra.FiniteType K R] :
    ∃ s : ℕ, ringKrullDim R = s ∧ Algebra.trdeg K R = s := by
  obtain ⟨s, g, ginj, gfin⟩ := exists_finite_inj_algHom_of_fg K R
  letI := g.toRingHom.toAlgebra
  haveI : Algebra.IsIntegral (MvPolynomial (Fin s) K) R := ⟨gfin.to_isIntegral⟩
  haveI : IsScalarTower K (MvPolynomial (Fin s) K) R :=
    IsScalarTower.of_algebraMap_eq (fun x => (g.commutes x).symm)
  haveI : FaithfulSMul (MvPolynomial (Fin s) K) R :=
    (faithfulSMul_iff_algebraMap_injective _ _).mpr ginj
  refine ⟨s, ?_, ?_⟩
  · rw [ringKrullDim_eq_of_isIntegral_of_injective (A := MvPolynomial (Fin s) K) ginj,
      ringKrullDim_mvPolynomial_field]
  · rw [← trdeg_add_eq K (MvPolynomial (Fin s) K) (A := R), MvPolynomial.trdeg_of_isDomain,
      trdeg_eq_zero (R := MvPolynomial (Fin s) K) (A := R)]
    simp

/-- Transcendence degree is unchanged by passing to a localization (e.g. the fraction field). -/
theorem trdeg_eq_of_isLocalization (K : Type*) [Field K] (R : Type u) [CommRing R] [IsDomain R]
    [Algebra K R] (F : Type u) [Field F] [Algebra R F] [Algebra K F] [IsScalarTower K R F]
    [IsFractionRing R F] : Algebra.trdeg K F = Algebra.trdeg K R := by
  haveI : Algebra.IsAlgebraic R F := IsLocalization.isAlgebraic F (nonZeroDivisors R)
  haveI : FaithfulSMul R F := (faithfulSMul_iff_algebraMap_injective _ _).mpr
    (IsFractionRing.injective R F)
  rw [← trdeg_add_eq K R (A := F), trdeg_eq_zero (R := R) (A := F), add_zero]


/-! ## §2. Schemes -/

open AlgebraicGeometry CategoryTheory TopologicalSpace Topology

/-- Copied verbatim from g0-dim (`scratch/g0-dim/part_dim.lean`). -/
theorem topologicalKrullDim_eq_iSup_of_openEmbedding {X : Type*} [TopologicalSpace X] {ι : Type*}
    {Y : ι → Type*} [∀ i, TopologicalSpace (Y i)] (f : ∀ i, Y i → X)
    (hf : ∀ i, IsOpenEmbedding (f i)) (hcov : ∀ x, ∃ i, x ∈ Set.range (f i)) :
    topologicalKrullDim X = ⨆ i, topologicalKrullDim (Y i) := by
  apply le_antisymm
  · refine iSup_le fun p => ?_
    obtain ⟨x, hx⟩ := p.head.isIrreducible.nonempty
    obtain ⟨i, y, rfl⟩ := hcov x
    let e := IrreducibleCloseds.orderIsoOfIsOpenEmbedding (f i) (hf i)
    have hmem : ∀ j, (f i ⁻¹' (p j : Set X)).Nonempty := fun j =>
      ⟨y, p.monotone (Fin.zero_le j) hx⟩
    let q : LTSeries {V : IrreducibleCloseds X | (f i ⁻¹' V).Nonempty} :=
      { length := p.length
        toFun := fun j => ⟨p j, hmem j⟩
        step := fun j => p.step j }
    calc (p.length : WithBot ℕ∞) = q.length := rfl
      _ ≤ krullDim {V : IrreducibleCloseds X | (f i ⁻¹' V).Nonempty} := q.length_le_krullDim
      _ = topologicalKrullDim (Y i) := (Order.krullDim_eq_of_orderIso e).symm
      _ ≤ ⨆ i, topologicalKrullDim (Y i) := le_iSup (fun i => topologicalKrullDim (Y i)) i
  · exact iSup_le fun i => (hf i).isInducing.topologicalKrullDim_le

/-- Copied verbatim from g0-dim (`scratch/g0-dim/part_dim.lean`). -/
theorem scheme_dim_eq_of_iso {X Y : Scheme} (e : X ≅ Y) :
    topologicalKrullDim X = topologicalKrullDim Y :=
  IsHomeomorph.topologicalKrullDim_eq _ (Scheme.homeoOfIso e).isHomeomorph

/-- Copied verbatim from g0-dim (`scratch/g0-dim/part_dim.lean`). -/
theorem spec_dim (R : CommRingCat) : topologicalKrullDim (Spec R) = ringKrullDim R :=
  PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim R

/-- The top open of a nonempty scheme is nonempty. -/
instance nonempty_top (X : Scheme.{u}) [Nonempty X] : Nonempty (⊤ : X.Opens) :=
  ⟨⟨Nonempty.some inferInstance, trivial⟩⟩

/-- The `K`-algebra structure on the function field of an integral scheme `X` over `Spec K`,
through `K ≅ Γ(Spec K, ⊤) → Γ(X, ⊤) → K(X)`. -/
noncomputable abbrev fnFieldAlgebra (K : Type u) [Field K] (X : Scheme.{u}) [IsIntegral X]
    (f : X ⟶ Spec (CommRingCat.of K)) : Algebra K X.functionField :=
  ((Scheme.ΓSpecIso (CommRingCat.of K)).inv ≫ f.appTop ≫ X.germToFunctionField ⊤).hom.toAlgebra

/-- The `K`-algebra structure on `Γ(X, U)` through `f`. -/
noncomputable abbrev secAlgebra (K : Type u) [Field K] (X : Scheme.{u})
    (f : X ⟶ Spec (CommRingCat.of K)) (U : X.Opens) : Algebra K Γ(X, U) :=
  ((Scheme.ΓSpecIso (CommRingCat.of K)).inv ≫ f.appLE ⊤ U le_top).hom.toAlgebra

/-- On a nonempty affine open `U` of an integral `X` locally of finite type over `K`:
`dim U = trdeg_K K(X)`. -/
theorem dim_affineOpen_eq_trdeg (K : Type u) [Field K] (X : Scheme.{u}) [IsIntegral X]
    (f : X ⟶ Spec (CommRingCat.of K)) [LocallyOfFiniteType f] (U : X.Opens) (hU : IsAffineOpen U)
    [Nonempty U] :
    letI := fnFieldAlgebra K X f
    topologicalKrullDim U = ((Algebra.trdeg K X.functionField).toENat : WithBot ℕ∞) := by
  letI := fnFieldAlgebra K X f
  letI := secAlgebra K X f U
  have hft : Algebra.FiniteType K Γ(X, U) := by
    have h1 : (f.appLE ⊤ U le_top).hom.FiniteType :=
      HasRingHomProperty.appLE @LocallyOfFiniteType f inferInstance
        ⟨⊤, isAffineOpen_top _⟩ ⟨U, hU⟩ le_top
    have h2 : (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom.FiniteType :=
      RingHom.FiniteType.of_surjective _
        (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of K)).inv).2
    exact h1.comp h2
  haveI : IsScalarTower K Γ(X, U) X.functionField := by
    refine IsScalarTower.of_algebraMap_eq (fun x => ?_)
    change ((Scheme.ΓSpecIso (CommRingCat.of K)).inv ≫ f.appTop ≫ X.germToFunctionField ⊤).hom x =
      (X.germToFunctionField U).hom
        (((Scheme.ΓSpecIso (CommRingCat.of K)).inv ≫ f.appLE ⊤ U le_top).hom x)
    rw [← CommRingCat.comp_apply]
    congr 2
    simp only [Category.assoc, Scheme.Hom.appLE, Scheme.Hom.appTop]
    congr 2
    exact (X.presheaf.germ_res (homOfLE le_top) _ _).symm
  haveI : IsFractionRing Γ(X, U) X.functionField :=
    functionField_isFractionRing_of_isAffineOpen X U hU
  obtain ⟨s, hdim, htr⟩ := exists_dim_eq_trdeg K Γ(X, U)
  rw [trdeg_eq_of_isLocalization K Γ(X, U) X.functionField, htr, Cardinal.toENat_nat]
  rw [show topologicalKrullDim U = topologicalKrullDim U.toScheme from rfl,
    scheme_dim_eq_of_iso hU.isoSpec, spec_dim, hdim]
  norm_cast

/-- **(AD), general form, proved.** For an integral scheme `X` locally of finite type over a
field `K`, `dim X = trdeg_K K(X)`. -/
theorem dim_eq_trdeg (K : Type u) [Field K] (X : Scheme.{u}) [IsIntegral X]
    (f : X ⟶ Spec (CommRingCat.of K)) [LocallyOfFiniteType f] :
    letI := fnFieldAlgebra K X f
    topologicalKrullDim X = ((Algebra.trdeg K X.functionField).toENat : WithBot ℕ∞) := by
  letI := fnFieldAlgebra K X f
  let ι := {U : X.Opens // IsAffineOpen U ∧ (U : Set X).Nonempty}
  have hcov : ∀ x : X, ∃ i : ι, x ∈ Set.range (fun y : (i.1 : Set X) => (y : X)) := by
    intro x
    obtain ⟨_, ⟨V, hV, rfl⟩, hxV, -⟩ :=
      X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
    exact ⟨⟨V, hV, ⟨x, hxV⟩⟩, ⟨x, hxV⟩, rfl⟩
  rw [topologicalKrullDim_eq_iSup_of_openEmbedding (Y := fun i : ι => (i.1 : Set X))
    (fun i y => (y : X)) (fun i => i.1.isOpen.isOpenEmbedding_subtypeVal) hcov]
  haveI : Nonempty ι := by
    obtain ⟨i, -⟩ := hcov (Nonempty.some inferInstance)
    exact ⟨i⟩
  have : ∀ i : ι, topologicalKrullDim (i.1 : Set X) =
      ((Algebra.trdeg K X.functionField).toENat : WithBot ℕ∞) := by
    intro i
    haveI : Nonempty i.1 := i.2.2.to_subtype
    exact dim_affineOpen_eq_trdeg K X f i.1 i.2.1
  simp only [this, ciSup_const]


/-! ## §3. The named statements and their proofs -/

/-- **(AD), general form: dimension equals transcendence degree.** Step (AD) of curve-glue's
image-plane step, in the general form cited by curve-glue §6 and §8 ("the Krull dimension of a
finitely generated `K`-domain equals the transcendence degree of its fraction field").
For an integral scheme `X` locally of finite type over a field `K`, the Krull dimension of `X`
equals the transcendence degree over `K` of its function field `K(X)` (with the `K`-algebra
structure induced by `f`). Source (STANDARD; numbering UNVERIFIED): Hartshorne, *Algebraic
Geometry*, I Prop. 1.7, Thm. 1.8A and Ex. II.3.20; the Stacks Project, *Commutative Algebra*,
section "Dimension of finite type algebras over fields". Glue: proved here from Mathlib's Noether
normalization (`exists_finite_inj_algHom_of_fg`, Stacks 00OW). -/
def DimEqTrdeg : Prop :=
  ∀ (K : Type) [Field K] (X : Scheme.{0}) [IsIntegral X] (f : X ⟶ Spec (CommRingCat.of K))
    [LocallyOfFiniteType f],
    letI := fnFieldAlgebra K X f
    topologicalKrullDim X = ((Algebra.trdeg K X.functionField).toENat : WithBot ℕ∞)

/-- **(AD), affine algebraic form.** For a domain `R` of finite type over a field `K`,
`dim R = trdeg_K Frac(R)`. Same source as `DimEqTrdeg`. Glue: proved here. -/
def DimEqTrdegAlg : Prop :=
  ∀ (K R : Type) [Field K] [CommRing R] [IsDomain R] [Algebra K R] [Algebra.FiniteType K R],
    ringKrullDim R = ((Algebra.trdeg K (FractionRing R)).toENat : WithBot ℕ∞)

/-- **Two elements of a field of transcendence degree one are algebraically dependent.** The
function-field content of curve-glue's `AlgDep` (two rational functions on a curve satisfy a
nonzero polynomial relation). Source (STANDARD): definition of transcendence degree
(Stacks 030G, as tagged in Mathlib's `Algebra.trdeg`). Glue: proved here. -/
def AlgDepOfTrdegOne : Prop :=
  ∀ (K F : Type) [Field K] [Field F] [Algebra K F], Algebra.trdeg K F = 1 →
    ∀ a b : F, ∃ P : MvPolynomial (Fin 2) K, P ≠ 0 ∧ MvPolynomial.aeval ![a, b] P = 0

theorem dimEqTrdeg : DimEqTrdeg := by
  intro K _ X _ f _
  exact dim_eq_trdeg K X f

theorem dimEqTrdegAlg : DimEqTrdegAlg := by
  intro K R _ _ _ _ _
  obtain ⟨s, hdim, htr⟩ := exists_dim_eq_trdeg K R
  rw [trdeg_eq_of_isLocalization K R (FractionRing R), htr, Cardinal.toENat_nat, hdim]
  norm_cast

theorem algDepOfTrdegOne : AlgDepOfTrdegOne := by
  intro K F _ _ _ h a b
  by_contra hne
  push Not at hne
  have hind : AlgebraicIndependent K ![a, b] := by
    rw [algebraicIndependent_iff_injective_aeval, injective_iff_map_eq_zero]
    intro P hP
    by_contra h0
    exact hne P h0 hP
  have := hind.cardinalMk_le_trdeg
  rw [h, Cardinal.mk_fin] at this
  norm_num at this

end CurveInfra


/-! ## §4. Smooth schemes and the kernel's `ffAlgebra` -/

namespace CurveInfra

open AlgebraicGeometry CategoryTheory

/-- **Transcendence degree of the function field of a smooth integral scheme.** For `X` integral
and smooth of relative dimension `n` over a field `K`, `trdeg_K K(X) = n`. Source (STANDARD;
numbering UNVERIFIED): Hartshorne I Prop. 1.7/Thm. 1.8A with II.8; Stacks, *Varieties*, section
"Smooth varieties". Glue: proved here from `dimEqTrdeg` and infra-smooth-dim's
`topologicalKrullDim_eq_of_smoothOfRelativeDimension`. -/
def SmoothTrdeg : Prop :=
  ∀ (K : Type) [Field K] (X : Scheme.{0}) [IsIntegral X] (f : X ⟶ Spec (CommRingCat.of K))
    (n : ℕ) [SmoothOfRelativeDimension n f],
    letI := fnFieldAlgebra K X f
    Algebra.trdeg K X.functionField = n

/-- **Two rational functions on a smooth integral curve are algebraically dependent.** The
general form of curve-glue's (AD) at the level of function fields. Glue: proved here from
`SmoothTrdeg` and `AlgDepOfTrdegOne`. -/
def CurveFnFieldAlgDep : Prop :=
  ∀ (K : Type) [Field K] (X : Scheme.{0}) [IsIntegral X] (f : X ⟶ Spec (CommRingCat.of K))
    [SmoothOfRelativeDimension 1 f],
    letI := fnFieldAlgebra K X f
    ∀ a b : X.functionField, ∃ P : MvPolynomial (Fin 2) K, P ≠ 0 ∧ MvPolynomial.aeval ![a, b] P = 0

/-- **`DimEqTrdeg` with the kernel's `ZInQ.LeafPush2.ffAlgebra`** (`ZInQKernel/HDecomp/LeafPush2/R18.lean`),
for `X : Over (Spec K)`. Glue: proved here. -/
def DimEqTrdegOver : Prop :=
  ∀ (K : Type) [Field K] (X : Over (Spec (CommRingCat.of K))) [IsIntegral X.left]
    [LocallyOfFiniteType X.hom],
    letI := ZInQ.LeafPush2.ffAlgebra X
    topologicalKrullDim X.left = ((Algebra.trdeg K X.left.functionField).toENat : WithBot ℕ∞)

/-- **`SmoothTrdeg` with the kernel's `ffAlgebra`**. Glue: proved here. -/
def SmoothTrdegOver : Prop :=
  ∀ (K : Type) [Field K] (X : Over (Spec (CommRingCat.of K))) [IsIntegral X.left]
    (n : ℕ) [SmoothOfRelativeDimension n X.hom],
    letI := ZInQ.LeafPush2.ffAlgebra X
    Algebra.trdeg K X.left.functionField = n

theorem smoothTrdeg : SmoothTrdeg := by
  intro K _ X _ f n _
  letI := fnFieldAlgebra K X f
  haveI : Smooth f := SmoothOfRelativeDimension.smooth n f
  have h1 := dim_eq_trdeg K X f
  have h2 := InfraSmoothDim.topologicalKrullDim_eq_of_smoothOfRelativeDimension f n
  rw [h1] at h2
  have h3 : (Algebra.trdeg K X.functionField).toENat = n := by exact_mod_cast h2
  exact Cardinal.toENat_eq_natCast.mp h3

theorem curveFnFieldAlgDep : CurveFnFieldAlgDep := by
  intro K _ X _ f _
  letI := fnFieldAlgebra K X f
  have h := smoothTrdeg K X f 1
  exact algDepOfTrdegOne K X.functionField (by exact_mod_cast h)

theorem dimEqTrdegOver : DimEqTrdegOver := by
  intro K _ X _ _
  exact dim_eq_trdeg K X.left X.hom

theorem smoothTrdegOver : SmoothTrdegOver := by
  intro K _ X _ n _
  exact smoothTrdeg K X.left X.hom n

/-- **On a smooth integral curve, the function field is algebraic over `K[x]` for every
transcendental `x`** (with the kernel's `ffAlgebra`; compare the kernel's `HasSexticModel`, which
asks for a transcendental `x`). Glue: proved here from `SmoothTrdegOver` and Mathlib's
transcendence bases. -/
def CurveAlgOverTranscendental : Prop :=
  ∀ (K : Type) [Field K] (X : Over (Spec (CommRingCat.of K))) [IsIntegral X.left]
    [SmoothOfRelativeDimension 1 X.hom],
    letI := ZInQ.LeafPush2.ffAlgebra X
    ∀ x : X.left.functionField, Transcendental K x →
      Algebra.IsAlgebraic (Algebra.adjoin K {x}) X.left.functionField

theorem curveAlgOverTranscendental : CurveAlgOverTranscendental := by
  intro K _ X _ _
  letI := ZInQ.LeafPush2.ffAlgebra X
  intro x hxt
  have h := smoothTrdegOver K X 1
  have hx : AlgebraicIndependent K ![x] := algebraicIndependent_iff_transcendental.mpr hxt
  have hb := hx.isTranscendenceBasis_of_trdeg_le_of_finite (by rw [h]; simp)
  have := hb.isAlgebraic
  rwa [show Set.range ![x] = {x} by simp] at this

end CurveInfra


/-! ## rv-fast checks (appended to a copy of scratch/curve-infra/CurveInfraAll.lean) -/
namespace RvFastCurveInfra
open AlgebraicGeometry CategoryTheory

-- (c) the kernel's `ZInQ.LeafPush2.ffAlgebra` is definitionally curve-infra's `fnFieldAlgebra`
example (K : Type) [Field K] (X : Over (Spec (CommRingCat.of K))) [IsIntegral X.left] :
    ZInQ.LeafPush2.ffAlgebra X = CurveInfra.fnFieldAlgebra K X.left X.hom := rfl

-- (c) `DimEqTrdegOver` is `DimEqTrdeg` restricted to `Over` objects, by unfolding
example : CurveInfra.DimEqTrdegOver ↔ ∀ (K : Type) [Field K] (X : Over (Spec (CommRingCat.of K)))
    [IsIntegral X.left] [LocallyOfFiniteType X.hom],
    letI := CurveInfra.fnFieldAlgebra K X.left X.hom
    topologicalKrullDim X.left = ((Algebra.trdeg K X.left.functionField).toENat : WithBot ℕ∞) :=
  Iff.rfl

-- (b) non-vacuity on a concrete instance: `DimEqTrdegAlg` at `R = K[X]` gives `trdeg_K K(X) = 1`
-- (from Mathlib's `dim K[X] = 1`), the expected value.
example (K : Type) [Field K] :
    (Algebra.trdeg K (FractionRing (Polynomial K))).toENat = 1 := by
  have h := CurveInfra.dimEqTrdegAlg K (Polynomial K)
  rw [Polynomial.ringKrullDim_of_isNoetherianRing, ringKrullDim_eq_zero_of_field, zero_add] at h
  exact_mod_cast h.symm

-- and at `R = K` (dimension 0)
example (K : Type) [Field K] : (Algebra.trdeg K (FractionRing K)).toENat = 0 := by
  have h := CurveInfra.dimEqTrdegAlg K K
  rw [ringKrullDim_eq_zero_of_field] at h
  exact_mod_cast h.symm

end RvFastCurveInfra

#print axioms CurveInfra.dimEqTrdeg
#print axioms CurveInfra.dimEqTrdegAlg
#print axioms CurveInfra.algDepOfTrdegOne
#print axioms CurveInfra.smoothTrdeg
#print axioms CurveInfra.curveFnFieldAlgDep
#print axioms CurveInfra.dimEqTrdegOver
#print axioms CurveInfra.smoothTrdegOver
#print axioms CurveInfra.curveAlgOverTranscendental
