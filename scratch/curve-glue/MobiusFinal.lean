import Mathlib
import ZInQKernel.HDecomp.QM.Pin
import ZInQKernel.HDecomp.Textbook.SkolemNoether
import Mathlib.LinearAlgebra.Lagrange
import Mathlib.RingTheory.Polynomial.Resultant.Basic
import Mathlib.RingTheory.Polynomial.GaussLemma
import Mathlib.FieldTheory.Separable
import Mathlib.FieldTheory.IsAlgClosed.Basic

/-!
# mobius-glue: the `π`-half of qm-pin's comparison of two triples

Task mobius-glue (2026-11-13). See `docs/research/mobius-glue.md`.

**Main result** (`mobiusGlue_of_curves`): `LeafQM.AV.Pin.MobiusGlue` (qm-pin §3.2, copied
verbatim from `scratch/qm-pin/QMPin.lean` together with the definitions it uses) follows from

* `CurveRatFactor` (curves): on a proper smooth curve over `ℚ`, a morphism `ρ` to `P¹` that is
  constant on the fibres of a morphism `σ` to `P¹` is a rational function of `σ` on `ℚ̄`-points;
* `CurveSurj` (curves): a morphism to `P¹` with finite fibres on `ℚ̄`-points, from a proper
  smooth curve over `ℚ` with a `ℚ̄`-point, is onto `P¹(ℚ̄)`;
* `ObjBridge.TorsionStructure` (the decomposition's textbook leaf T5, `A(K̄)[n] ≅ (ℤ/n)^{2g}`).

Contents.
* §0 the qm-pin definitions (verbatim).
* §1 an injective rational function on an algebraically closed field of characteristic 0 has
  degree at most one (`Mob.natDegree_le_one_of_injective`, Wronskian argument); one of degree at
  most one without finite pole fixing `0` and `c ≠ 0` is the identity (`Mob.ratEval_eq_self`).
* §2 the named facts; §3 `mobiusGlue_of_curveFacts` (from the curve facts and
  `TwistClassFinite`).
* §4 `TwistClassFinite` from T5 and `AutOInnerFinite` (finitely many level structures per pair via
  the kernel's `Level3.torsor`; transport of level structures; twists by conjugate automorphisms).
* §5-§6 the combined statements and the downstream comparison/transfer (qm-pin §4 copied).
* §7 `AutOInnerFinite` from Skolem–Noether (the kernel's `TSkolemKW.leafSkolemNoether`, through
  an explicit extension of `α ∈ Aut 𝒪` to `B`) and `NormalizerFinite`.
* §8 `NormalizerFinite` proved (`N(𝒪)/ℚ^×𝒪^× = {1, i, j, ij}`, descent on the reduced norm), hence
  `autOInnerFinite`, `twistClassFinite`, `mobiusGlue_of_curves`, `sameTripleMor_of_curves`,
  `pointwise_of_witness_curves`.
No `sorry`, no `axiom`.
-/

/-! # curve-glue: dimension theory from `scratch/infra-smooth-dim/SmoothDimProps.lean` (its lines
from `open Ideal IsLocalRing` to the end of §4, verbatim, inside a section) -/

section InfraCopy

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

end InfraSmoothDim


end InfraCopy

noncomputable section

namespace LeafQM

namespace AV

namespace Pin

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open PkgI3

/-! (curve-glue: §0 of mobius-glue dropped; the kernel's `ZInQKernel/HDecomp/QM/Pin.lean`
provides `MobiusGlue`, `R1fpProps` etc. One line of `mobiusGlue_of_curveFacts` changed: the
destructuring of `h1' : R1fpProps Y' Φ'` (kernel clause order).) -/

/-! ## §1 Rational functions on `P¹`: an injective one is a Möbius map -/

namespace Mob

open Polynomial

variable {K : Type} [Field K]


open scoped Classical in
/-- The value at a finite point `t` of the rational map `[F : G] : P¹ → P¹`. -/
def ratEval (F G : K[X]) (t : K) : OnePoint K :=
  if G.eval t = 0 then OnePoint.infty else OnePoint.some (F.eval t / G.eval t)

theorem eval_ne_zero_of_coprime {F G : K[X]} (h : IsCoprime F G) {a : K} (hG : G.eval a = 0) :
    F.eval a ≠ 0 := by
  intro hF
  obtain ⟨u, v, huv⟩ := h
  have := congrArg (Polynomial.eval a) huv
  simp [eval_add, eval_mul, hF, hG] at this

/-- The Wronskian `F' G - F G'` of a coprime pair of which one has positive degree is nonzero
(characteristic 0). -/
theorem wronskian_ne_zero [CharZero K] {F G : K[X]} (h : IsCoprime F G)
    (hdeg : F.natDegree ≠ 0 ∨ G.natDegree ≠ 0) :
    derivative F * G - F * derivative G ≠ 0 := by
  intro hW
  have hW' : derivative F * G = F * derivative G := sub_eq_zero.mp hW
  have key : ∀ {P Q : K[X]}, IsCoprime P Q → P ∣ derivative P * Q → P.natDegree = 0 := by
    intro P Q hPQ hd
    have hd' : P ∣ derivative P := hPQ.dvd_of_dvd_mul_right hd
    by_contra hP
    have hne : derivative P ≠ 0 := derivative_ne_zero.mpr hP
    have h1 := natDegree_le_of_dvd hd' hne
    have h2 := natDegree_derivative_lt hP
    omega
  have hF : F.natDegree = 0 := key h ⟨derivative G, hW'⟩
  have hG : G.natDegree = 0 := key h.symm ⟨derivative F, by rw [mul_comm, ← hW', mul_comm]⟩
  rcases hdeg with hdeg | hdeg <;> contradiction

/-- **An injective rational function has degree at most one** (algebraically closed field of
characteristic 0). -/
theorem natDegree_le_one_of_injective [IsAlgClosed K] [CharZero K] {F G : K[X]}
    (hcop : IsCoprime F G) (hinj : ∀ s t : K, ratEval F G s = ratEval F G t → s = t) :
    F.natDegree ≤ 1 ∧ G.natDegree ≤ 1 := by
  classical
  by_contra hcon
  set n := max F.natDegree G.natDegree with hn_def
  have hn : 2 ≤ n := by
    rw [not_and_or] at hcon
    rcases hcon with h | h <;> omega
  set W := derivative F * G - F * derivative G with hW_def
  have hW : W ≠ 0 := wronskian_ne_zero hcop (by omega)
  -- the good values of `c`
  set S : Set K := {c | F.coeff n - c * G.coeff n ≠ 0} with hS_def
  have hS : S.Infinite := by
    have hsub : Sᶜ.Subsingleton := by
      intro c hc d hd
      simp only [hS_def, Set.mem_compl_iff, Set.mem_ofPred_eq, not_not] at hc hd
      by_cases hG : G.coeff n = 0
      · have hF : F.coeff n ≠ 0 := by
          rcases le_total F.natDegree G.natDegree with h | h
          · have hnG : n = G.natDegree := by omega
            have : G.natDegree ≠ 0 := by omega
            rw [hnG] at hG
            exact absurd (leadingCoeff_eq_zero.mp hG) (by rintro rfl; simp at this)
          · have hnF : n = F.natDegree := by omega
            have : F.natDegree ≠ 0 := by omega
            rw [hnF]
            intro h0
            exact absurd (leadingCoeff_eq_zero.mp h0) (by rintro rfl; simp at this)
        rw [hG, mul_zero, sub_zero] at hc
        exact absurd hc hF
      · have e1 : c = F.coeff n / G.coeff n := by rw [eq_div_iff hG]; linear_combination -hc
        have e2 : d = F.coeff n / G.coeff n := by rw [eq_div_iff hG]; linear_combination -hd
        rw [e1, e2]
    have := hsub.finite.infinite_compl
    rwa [compl_compl] at this
  -- every good `c` is the value at a root of `W`
  have hgood : ∀ c ∈ S, ∃ a, W.IsRoot a ∧ F.eval a / G.eval a = c := by
    intro c hc
    set H := F - C c * G with hH_def
    have hHn : H.natDegree = n := by
      apply natDegree_eq_of_le_of_coeff_ne_zero
      · refine (natDegree_sub_le _ _).trans (max_le (le_max_left _ _) ?_)
        exact (natDegree_C_mul_le _ _).trans (le_max_right _ _)
      · have hc' : F.coeff n - c * G.coeff n ≠ 0 := hc
        simpa [hH_def, coeff_sub, coeff_C_mul] using hc'
    have hH0 : H ≠ 0 := by
      intro h0; rw [h0, natDegree_zero] at hHn; omega
    -- a root of `H` has value `c`
    have hval : ∀ b, H.IsRoot b → G.eval b ≠ 0 ∧ F.eval b / G.eval b = c := by
      intro b hb
      have hb' : F.eval b = c * G.eval b := by
        have := hb; simp only [IsRoot, hH_def, eval_sub, eval_mul, eval_C] at this
        linear_combination this
      have hGb : G.eval b ≠ 0 := by
        intro h0
        exact eval_ne_zero_of_coprime hcop h0 (by rw [hb', h0, mul_zero])
      exact ⟨hGb, by rw [hb']; field_simp⟩
    obtain ⟨a, ha⟩ := IsAlgClosed.exists_root H (by
      rw [degree_eq_natDegree hH0]; exact_mod_cast (by omega : H.natDegree ≠ 0))
    obtain ⟨hGa, hFa⟩ := hval a ha
    -- all roots of `H` are `a`
    have hall : ∀ b ∈ H.roots, a = b := by
      intro b hb
      have hb' := (mem_roots hH0).mp hb
      obtain ⟨hGb, hFb⟩ := hval b hb'
      apply hinj
      simp only [ratEval, hGa, hGb, ite_false, hFa, hFb]
    have hcount : H.roots.count a = n := by
      rw [Multiset.count_eq_card.mpr hall, IsAlgClosed.card_roots_eq_natDegree, hHn]
    have hmult : 1 < H.rootMultiplicity a := by
      rw [← count_roots]; convert (show 1 < n by omega) using 2
    obtain ⟨-, hd⟩ := (one_lt_rootMultiplicity_iff_isRoot hH0).mp hmult
    refine ⟨a, ?_, hFa⟩
    have hd' : (derivative F).eval a = c * (derivative G).eval a := by
      have := hd
      simp only [IsRoot, hH_def, derivative_sub, derivative_mul, derivative_C, zero_mul,
        zero_add, eval_sub, eval_mul, eval_C] at this
      linear_combination this
    have ha' : F.eval a = c * G.eval a := by
      have := ha; simp only [IsRoot, hH_def, eval_sub, eval_mul, eval_C] at this
      linear_combination this
    simp only [IsRoot, hW_def, eval_sub, eval_mul, hd', ha']
    ring
  -- so the good values lie in a finite set
  have hfin : S.Finite := by
    refine ((W.roots.toFinset.finite_toSet).image (fun a => F.eval a / G.eval a)).subset ?_
    intro c hc
    obtain ⟨a, ha, rfl⟩ := hgood c hc
    exact ⟨a, by simpa [Multiset.mem_toFinset, mem_roots hW] using ha, rfl⟩
  exact hS hfin


/-- **A rational function of degree at most one with no finite pole, fixing `0` and some
`c ≠ 0`, is the identity on `K`.** (With `∞ ↦ ∞`, which "no finite pole" encodes: a Möbius map
fixing `0, ∞, c` is the identity.) -/
theorem ratEval_eq_self [IsAlgClosed K] {F G : K[X]} (hF1 : F.natDegree ≤ 1)
    (hpole : ∀ t, ratEval F G t ≠ OnePoint.infty) (h0 : ratEval F G 0 = OnePoint.some 0)
    {c : K} (hc : c ≠ 0) (hcc : ratEval F G c = OnePoint.some c) :
    ∀ t, ratEval F G t = OnePoint.some t := by
  classical
  have hGne : ∀ t, G.eval t ≠ 0 := fun t ht => hpole t (by simp [ratEval, ht])
  have hG0 : G.natDegree = 0 := by
    by_contra h
    have hG : G ≠ 0 := by rintro rfl; simp at h
    obtain ⟨a, ha⟩ := IsAlgClosed.exists_root G (by
      rw [degree_eq_natDegree hG]; exact_mod_cast h)
    exact hGne a ha
  have hGC : G = C (G.coeff 0) := eq_C_of_natDegree_eq_zero hG0
  have hFX : F = C (F.coeff 1) * X + C (F.coeff 0) := eq_X_add_C_of_natDegree_le_one hF1
  have hd : G.coeff 0 ≠ 0 := by
    have := hGne 0; rwa [hGC, eval_C] at this
  have hval : ∀ t, ratEval F G t =
      OnePoint.some ((F.coeff 1 * t + F.coeff 0) / G.coeff 0) := by
    intro t
    simp only [ratEval, hGne t, ite_false]
    congr 1
    conv_lhs => rw [hFX, hGC]
    simp
  have hb : F.coeff 0 = 0 := by
    have := h0; rw [hval, OnePoint.coe_eq_coe] at this
    simpa [hd] using this
  have ha : F.coeff 1 = G.coeff 0 := by
    have := hcc; rw [hval, OnePoint.coe_eq_coe, hb, add_zero, div_eq_iff hd] at this
    exact mul_right_cancel₀ hc (by rw [this, mul_comm])
  intro t
  rw [hval, hb, ha, add_zero, mul_div_cancel_left₀ _ hd]

end Mob

/-! ## §2 The named facts -/

open Polynomial in
/-- **Curve fact 1 (factorization through a rational function).** On a proper smooth curve
`S/ℚ`, if `ρ : S → P¹` is constant on the fibres of `σ : S → P¹` (on `ℚ̄`-points), then
`ρ = R ∘ σ` on `ℚ̄`-points with finite `σ`-value, for a rational function `R = [F : G]`,
`F, G ∈ ℚ̄[t]` coprime. (On a geometric component `C` where `σ` is nonconstant: the image of
`(σ, ρ) : C → P¹ × P¹` projects bijectively, hence birationally (char. 0), onto the normal
curve `P¹`, so its inverse is a morphism and `R = pr₂ ∘ pr₁⁻¹`; components where `σ` is
constant are absorbed by the fibre condition, or by Lagrange interpolation if every component
is. STANDARD; not in Mathlib.) -/
def CurveRatFactor : Prop :=
  ∀ (S : Over (Spec (CommRingCat.of ℚ))), IsProper S.hom → SmoothOfRelativeDimension 1 S.hom →
    ∀ σ ρ : ToP1 S.left,
      (∀ y₁ y₂ : fieldPt Qbar ⟶ S, σ.val (K := Qbar) y₁.left = σ.val (K := Qbar) y₂.left →
        ρ.val (K := Qbar) y₁.left = ρ.val (K := Qbar) y₂.left) →
      ∃ F G : Qbar[X], IsCoprime F G ∧ ∀ (y : fieldPt Qbar ⟶ S) (t : Qbar),
        σ.val (K := Qbar) y.left = OnePoint.some t → ρ.val (K := Qbar) y.left = Mob.ratEval F G t

/-- **Curve fact 2 (surjectivity).** A morphism `σ : S → P¹` from a proper smooth curve `S/ℚ`
with a `ℚ̄`-point, whose fibres on `ℚ̄`-points are finite, is onto `P¹(ℚ̄)`. (The geometric
component through the given point has infinitely many `ℚ̄`-points, so `σ` is nonconstant on
it; its image is closed and irreducible, hence `P¹`; closed points of `P¹_ℚ̄` lift to
`ℚ̄`-points. STANDARD, e.g. Hartshorne II.6.8; not in Mathlib.) -/
def CurveSurj : Prop :=
  ∀ (S : Over (Spec (CommRingCat.of ℚ))), IsProper S.hom → SmoothOfRelativeDimension 1 S.hom →
    Nonempty (fieldPt Qbar ⟶ S) → ∀ σ : ToP1 S.left,
      (∀ y : fieldPt Qbar ⟶ S, {y' : fieldPt Qbar ⟶ S |
        σ.val (K := Qbar) y'.left = σ.val (K := Qbar) y.left}.Finite) →
      ∀ t : OnePoint Qbar, ∃ y : fieldPt Qbar ⟶ S, σ.val (K := Qbar) y.left = t

/-- **Moduli fact (finite twist classes).** For a level-3 object `P` over `ℚ̄`, only finitely
many isomorphism classes `[Q]` have `(Q.A, Q.ι)` isomorphic to an `Aut(𝒪)`-twist of
`(P.A, P.ι)`. (The twists of a pair by `α` and by `α ∘ (conjugation by a unit)` are isomorphic
through `ι(u)`, and `Aut(𝒪)` modulo these is the finite group `N(𝒪)/ℚ^×𝒪^×` (Skolem–Noether);
for a fixed pair, `η` is determined by `η(1) ∈ A[3](ℚ̄)`, a finite group. STANDARD; not in
Mathlib.) -/
def TwistClassFinite : Prop :=
  ∀ P : QML3 Qbar, {m : M3 Qbar | ∃ Q : QML3 Qbar, m = M3.mk Q ∧
    ∃ α : O ≃+* O, Nonempty (QMIso (P.q.twist α) Q.q)}.Finite

/-! ## §3 The reduction -/

/-- **`MobiusGlue` from the two curve facts and the moduli fact.** -/
theorem mobiusGlue_of_curveFacts (hRF : CurveRatFactor) (hSu : CurveSurj)
    (hT : TwistClassFinite) : MobiusGlue := by
  intro Y Y' Φ Φ' π π' g h1 h2 h1' h2' hCM hg y
  set σ : ToP1 Y'.left := π.comp g.left with hσ_def
  have hσ : ∀ y : fieldPt Qbar ⟶ Y', σ.val (K := Qbar) y.left =
      π.val (K := Qbar) (y ≫ g).left := by
    intro y; exact ToP1.val_comp_right π g.left y.left
  rw [← hσ]
  -- representatives
  have hout : ∀ y : fieldPt Qbar ⟶ Y', Φ' Qbar y = M3.mk (Quotient.out (Φ' Qbar y)) :=
    fun y => (Quotient.out_eq _).symm
  -- the two maps have the same fibres
  have hrel : ∀ y₁ y₂ : fieldPt Qbar ⟶ Y', σ.val (K := Qbar) y₁.left = σ.val (K := Qbar) y₂.left
      ↔ π'.val (K := Qbar) y₁.left = π'.val (K := Qbar) y₂.left := by
    intro y₁ y₂
    rw [hσ, hσ, (h2 (y₁ ≫ g) (y₂ ≫ g) _ _ ((hg Qbar y₁).symm.trans (hout y₁))
      ((hg Qbar y₂).symm.trans (hout y₂))).1, (h2' y₁ y₂ _ _ (hout y₁) (hout y₂)).1]
  -- CM points of `Y'` and the values there
  obtain ⟨⟨P₄, c₄⟩, ⟨P₃, c₃⟩, ⟨P₂, c₂⟩⟩ := hCM
  have hpt : ∀ P : QML3 Qbar, Φ' Qbar ((Φ' Qbar).symm (M3.mk P)) = M3.mk P :=
    fun P => (Φ' Qbar).apply_symm_apply _
  set y₄ := (Φ' Qbar).symm (M3.mk P₄)
  set y₃ := (Φ' Qbar).symm (M3.mk P₃)
  set y₂ := (Φ' Qbar).symm (M3.mk P₂)
  have hY : ∀ y : fieldPt Qbar ⟶ Y', ∀ P : QML3 Qbar, Φ' Qbar y = M3.mk P →
      Φ Qbar (y ≫ g) = M3.mk P := fun y P hP => (hg Qbar y).symm.trans hP
  have σ₄ : σ.val (K := Qbar) y₄.left = OnePoint.some 0 := by
    rw [hσ]; exact (h2 _ _ _ _ (hY _ _ (hpt P₄)) (hY _ _ (hpt P₄))).2.1 c₄
  have π₄ : π'.val (K := Qbar) y₄.left = OnePoint.some 0 :=
    (h2' _ _ _ _ (hpt P₄) (hpt P₄)).2.1 c₄
  have σ₃ : σ.val (K := Qbar) y₃.left = OnePoint.infty := by
    rw [hσ]; exact (h2 _ _ _ _ (hY _ _ (hpt P₃)) (hY _ _ (hpt P₃))).2.2.1 c₃
  have π₃ : π'.val (K := Qbar) y₃.left = OnePoint.infty :=
    (h2' _ _ _ _ (hpt P₃) (hpt P₃)).2.2.1 c₃
  have σ₂ : σ.val (K := Qbar) y₂.left = OnePoint.some (-16 / 27) := by
    rw [hσ]; exact (h2 _ _ _ _ (hY _ _ (hpt P₂)) (hY _ _ (hpt P₂))).2.2.2 c₂
  have π₂ : π'.val (K := Qbar) y₂.left = OnePoint.some (-16 / 27) :=
    (h2' _ _ _ _ (hpt P₂) (hpt P₂)).2.2.2 c₂
  -- finite fibres
  have hfin : ∀ y : fieldPt Qbar ⟶ Y', {y' : fieldPt Qbar ⟶ Y' |
      σ.val (K := Qbar) y'.left = σ.val (K := Qbar) y.left}.Finite := by
    intro y
    refine ((hT (Quotient.out (Φ' Qbar y))).preimage
      (Set.injOn_of_injective (Φ' Qbar).injective)).subset ?_
    intro y' hy'
    have e : π'.val (K := Qbar) y.left = π'.val (K := Qbar) y'.left :=
      ((hrel y' y).1 hy').symm
    exact ⟨_, hout y', ((h2' y y' _ _ (hout y) (hout y')).1).1 e⟩
  obtain ⟨hprop', hsmooth', hne', -, -, -⟩ := h1'
  have hsurj := hSu Y' hprop' hsmooth' hne' σ hfin
  obtain ⟨F, G, hcop, hFG⟩ := hRF Y' hprop' hsmooth' σ π' (fun y₁ y₂ h => (hrel y₁ y₂).1 h)
  -- the rational function is injective, has no finite pole, and fixes `0` and `-16/27`
  have hinj : ∀ s t : Qbar, Mob.ratEval F G s = Mob.ratEval F G t → s = t := by
    intro s t hst
    obtain ⟨ys, hys⟩ := hsurj (OnePoint.some s)
    obtain ⟨yt, hyt⟩ := hsurj (OnePoint.some t)
    have e : π'.val (K := Qbar) ys.left = π'.val (K := Qbar) yt.left := by
      rw [hFG ys s hys, hFG yt t hyt, hst]
    have := (hrel ys yt).2 e
    rw [hys, hyt] at this
    exact OnePoint.coe_injective this
  have hdeg := Mob.natDegree_le_one_of_injective hcop hinj
  have hpole : ∀ t, Mob.ratEval F G t ≠ OnePoint.infty := by
    intro t ht
    obtain ⟨yt, hyt⟩ := hsurj (OnePoint.some t)
    have e : π'.val (K := Qbar) yt.left = π'.val (K := Qbar) y₃.left := by
      rw [hFG yt t hyt, ht, π₃]
    have := (hrel yt y₃).2 e
    rw [hyt, σ₃] at this
    exact OnePoint.coe_ne_infty t this
  have h0 : Mob.ratEval F G 0 = OnePoint.some 0 := by rw [← hFG y₄ 0 σ₄, π₄]
  have hc : Mob.ratEval F G (-16 / 27) = OnePoint.some (-16 / 27) := by
    rw [← hFG y₂ _ σ₂, π₂]
  have hid := Mob.ratEval_eq_self hdeg.1 hpole h0 (by norm_num) hc
  -- conclusion
  by_cases hinf : σ.val (K := Qbar) y.left = OnePoint.infty
  · rw [hinf]
    rw [← π₃]
    exact (hrel y y₃).1 (by rw [hinf, σ₃])
  · obtain ⟨t, ht⟩ := OnePoint.ne_infty_iff_exists.mp hinf
    rw [← ht, hFG y t ht.symm, hid t]

/-! ## §4 `TwistClassFinite` from the textbook leaf `TorsionStructure` (T5) and an algebra fact -/

/-- **Algebra fact (finiteness of `Aut(𝒪)` modulo inner automorphisms by units).** Every ring
automorphism of `𝒪` is, up to conjugation by a unit of `𝒪`, one of finitely many. (Every
automorphism of `𝒪` extends to `B = 𝒪 ⊗ ℚ`, hence is conjugation by some `x ∈ N(𝒪)`
(Skolem–Noether), and `N(𝒪)/ℚ^×𝒪^×` is finite: for the maximal order of the quaternion algebra
of discriminant 6 it is the Atkin–Lehner group `W ≅ (ℤ/2)²`. STANDARD (Vignéras, *Arithmétique
des algèbres de quaternions*; locator UNVERIFIED); not in Mathlib.) A statement about the concrete
order `O` of the kernel only. -/
def AutOInnerFinite : Prop :=
  ∃ T : Set (O ≃+* O), T.Finite ∧ ∀ α : O ≃+* O, ∃ t ∈ T, ∃ v : Oˣ,
    ∀ a : O, α a = (v : O) * t a * ((v⁻¹ : Oˣ) : O)

section FiniteTwist

variable {K : Type} [Field K]

/-- Every element of `𝒪` is congruent modulo `3𝒪` to some `liftO c`, `c ∈ (ℤ/3)⁴`. -/
theorem exists_liftO_congr (u : O) : ∃ c : Fin 4 → ZMod 3, ∃ k : O, u - liftO c = 3 * k := by
  obtain ⟨n, hn⟩ := u.2
  refine ⟨fun i => (n i : ZMod 3), ⟨ofInt (fun i => n i / 3), ⟨_, rfl⟩⟩, ?_⟩
  apply Subtype.ext
  have h33 : ((3 : O) : B) = 3 := map_ofNat O.subtype 3
  simp only [AddSubgroupClass.coe_sub, MulMemClass.coe_mul, h33, liftO]
  rw [hn, ofInt_sub, three_mul_ofInt]
  congr 1
  funext i
  simp only [Pi.sub_apply, ZMod.val_intCast, Nat.cast_ofNat]
  omega

/-- **Finitely many level structures on one `(A, ι)`** (characteristic 0, given the leaf
`TorsionStructure`): by the kernel's torsor glue `Level3.torsor`, a level structure is
`a ↦ η₀(a u₀)`, which depends only on `u₀ mod 3𝒪`. -/
theorem level3_finite (hT : ObjBridge.TorsionStructure) [CharZero K] {A : AbVar K}
    (s : A.dim = 2) (q : QMStr A) : Finite (Level3 q) := by
  rcases isEmpty_or_nonempty (Level3 q) with h | h
  · infer_instance
  · obtain ⟨e₀⟩ := h
    have key : ∀ e : Level3 q, ∃ c : Fin 4 → ZMod 3, ∀ a : O,
        e.eta a = e₀.eta (a * liftO c) := by
      intro e
      obtain ⟨u₀, -, -, hu⟩ := Level3.torsor hT ⟨A, s, q, e₀⟩ e
      obtain ⟨c, k, hk⟩ := exists_liftO_congr u₀
      refine ⟨c, fun a => (hu a).trans ((e₀.eq_iff _ _).2 ⟨a * k, ?_⟩)⟩
      calc a * u₀ - a * liftO c = a * (u₀ - liftO c) := by noncomm_ring
        _ = a * (3 * k) := by rw [hk]
        _ = 3 * (a * k) := by noncomm_ring
    choose f hf using key
    refine Finite.of_injective f fun e e' h => Level3.ext' ?_
    ext a
    rw [hf e a, hf e' a, h]

/-- Transport of a level structure along an isomorphism of QM pairs. -/
def transportLevel {A A' : AbVar K} {q : QMStr A} {q' : QMStr A'} (f : QMIso q q')
    (e : Level3 q) : Level3 q' where
  eta := (AbVar.ptMap (L := K) f.φ).toAdditive.comp e.eta
  linear a b := by
    change Additive.ofMul (Additive.toMul (e.eta (a * b)) ≫ f.φ.hom) =
      Additive.ofMul ((Additive.toMul (e.eta b) ≫ f.φ.hom) ≫ (q'.iota a).hom)
    rw [e.linear]
    change Additive.ofMul ((Additive.toMul (e.eta b) ≫ (q.iota a).hom) ≫ f.φ.hom) = _
    rw [Category.assoc, f.equivariant a, Category.assoc]
  ker a := by
    rw [← e.ker]
    constructor
    · intro h
      have h' : Additive.toMul (e.eta a) ≫ f.φ.hom = 1 := congrArg Additive.toMul h
      have : Additive.toMul (e.eta a) = 1 := by
        calc Additive.toMul (e.eta a) = Additive.toMul (e.eta a) ≫ f.φ.hom ≫ f.ψ.hom := by
              rw [f.left, Category.comp_id]
          _ = 1 := by rw [← Category.assoc, h', MonObj.one_comp]
      exact congrArg Additive.ofMul this
    · intro h
      change Additive.ofMul (Additive.toMul (e.eta a) ≫ f.φ.hom) = 0
      rw [h]
      change Additive.ofMul ((1 : _ ⟶ _) ≫ f.φ.hom) = 0
      rw [MonObj.one_comp]
      rfl

/-- An object is isomorphic to the transport of its level structure. -/
def QML3.isoTransport (Q : QML3 K) {A' : AbVar K} (s' : A'.dim = 2) {q' : QMStr A'}
    (f : QMIso Q.q q') : Q.Iso ⟨A', s', q', transportLevel f Q.e⟩ where
  φ := f.φ
  ψ := f.ψ
  left := f.left
  right := f.right
  equivariant := f.equivariant
  level _ := rfl

/-- Twists by `t` and by `v t v⁻¹` (`v ∈ 𝒪^×`) are isomorphic through `ι(v)`. -/
def conjUnitIso {A : AbVar K} (q : QMStr A) (t α : O ≃+* O) (v : Oˣ)
    (hv : ∀ a, α a = (v : O) * t a * ((v⁻¹ : Oˣ) : O)) : QMIso (q.twist t) (q.twist α) where
  φ := q.iota v
  ψ := q.iota ↑v⁻¹
  left := by
    have : q.iota ↑v⁻¹ * q.iota ↑v = 1 := by rw [← map_mul, Units.inv_mul, map_one]
    exact congrArg AbVar.Hom.hom this
  right := by
    have : q.iota ↑v * q.iota ↑v⁻¹ = 1 := by rw [← map_mul, Units.mul_inv, map_one]
    exact congrArg AbVar.Hom.hom this
  equivariant a := by
    have : q.iota (v : O) * q.iota (t a) = q.iota (α a) * q.iota v := by
      rw [← map_mul, ← map_mul, hv, _root_.mul_assoc, Units.inv_mul, _root_.mul_one]
    exact congrArg AbVar.Hom.hom this

/-- **`TwistClassFinite` from the leaf `TorsionStructure` and `AutOInnerFinite`.** -/
theorem twistClassFinite_of (hT : ObjBridge.TorsionStructure) (hA : AutOInnerFinite) :
    TwistClassFinite := by
  obtain ⟨T, hTfin, hTα⟩ := hA
  intro P
  let R : (O ≃+* O) → Set (M3 Qbar) := fun t =>
    Set.range (fun e : Level3 (P.q.twist t) => M3.mk ⟨P.A, P.surface, P.q.twist t, e⟩)
  have hR : ∀ t, (R t).Finite := fun t => by
    have := level3_finite hT P.surface (P.q.twist t)
    exact Set.finite_range _
  refine (hTfin.biUnion fun t _ => hR t).subset ?_
  rintro m ⟨Q, rfl, α, ⟨f⟩⟩
  obtain ⟨t, ht, v, hv⟩ := hTα α
  let h : QMIso Q.q (P.q.twist t) := ((conjUnitIso P.q t α v hv).trans f).symm
  refine Set.mem_biUnion ht ⟨transportLevel h Q.e, ?_⟩
  exact Quotient.sound ⟨(QML3.isoTransport Q P.surface h).symm⟩

end FiniteTwist

/-! ## §5 The result -/

/-- **`MobiusGlue` from two curve facts, the textbook leaf `TorsionStructure` (T5, Mumford §4)
and the algebra fact `AutOInnerFinite`.** -/
theorem mobiusGlue_of_named (hRF : CurveRatFactor) (hSu : CurveSurj)
    (hT : ObjBridge.TorsionStructure) (hA : AutOInnerFinite) : MobiusGlue :=
  mobiusGlue_of_curveFacts hRF hSu (twistClassFinite_of hT hA)

end Pin

end AV

end LeafQM


/-! ## §7 `AutOInnerFinite` from Skolem–Noether (proved in the kernel) and `NormalizerFinite`

(Outside the `open MonObj` scope of §0-§6.) -/

namespace LeafQM

namespace AV

namespace Pin

namespace AutOExt

/-! ### Extension of a ring automorphism of `𝒪` to `B` -/

theorem mem_O_of_int (z0 z1 z2 z3 : ℤ) : (⟨z0, z1, z2, z3⟩ : B) ∈ O := by
  refine ⟨![z0 - z2, z1 - z3, 2 * z2, 2 * z3], ?_⟩
  ext <;> simp [ofInt]

theorem nat_smul_mem (n : ℕ) {x : B} (hx : x ∈ O) : (n : ℚ) • x ∈ O := by
  rw [Algebra.smul_def, map_natCast]
  exact O.mul_mem (natCast_mem O n) hx

theorem den_mul_int (q : ℚ) (k : ℕ) : ∃ z : ℤ, ((k * q.den : ℕ) : ℚ) * q = z :=
  ⟨k * q.num, by push_cast; rw [mul_assoc, Rat.den_mul_eq_num]⟩

/-- Every element of `B` has a positive integer multiple in `𝒪`. -/
theorem exists_nat_smul_mem (b : B) : ∃ m : ℕ, 0 < m ∧ (m : ℚ) • b ∈ O := by
  set m := b.re.den * b.imI.den * b.imJ.den * b.imK.den with hm
  refine ⟨m, by positivity, ?_⟩
  obtain ⟨z0, h0⟩ := den_mul_int b.re (b.imI.den * b.imJ.den * b.imK.den)
  obtain ⟨z1, h1⟩ := den_mul_int b.imI (b.re.den * b.imJ.den * b.imK.den)
  obtain ⟨z2, h2⟩ := den_mul_int b.imJ (b.re.den * b.imI.den * b.imK.den)
  obtain ⟨z3, h3⟩ := den_mul_int b.imK (b.re.den * b.imI.den * b.imJ.den)
  have e : (m : ℚ) • b = ⟨z0, z1, z2, z3⟩ := by
    ext
    · rw [QuaternionAlgebra.re_smul, ← h0, smul_eq_mul, hm]; push_cast; ring
    · rw [QuaternionAlgebra.imI_smul, ← h1, smul_eq_mul, hm]; push_cast; ring
    · rw [QuaternionAlgebra.imJ_smul, ← h2, smul_eq_mul, hm]; push_cast; ring
    · rw [QuaternionAlgebra.imK_smul, ← h3, smul_eq_mul, hm]
  rw [e]
  exact mem_O_of_int z0 z1 z2 z3

variable (α : O ≃+* O)

/-- A chosen positive integer `m` with `m b ∈ 𝒪`. -/
def extDen (b : B) : ℕ := Classical.choose (exists_nat_smul_mem b)

theorem extDen_pos (b : B) : 0 < extDen b := (Classical.choose_spec (exists_nat_smul_mem b)).1

theorem extDen_mem (b : B) : ((extDen b : ℕ) : ℚ) • b ∈ O :=
  (Classical.choose_spec (exists_nat_smul_mem b)).2

/-- `α̃(b) = m⁻¹ α(m b)`. -/
def extFun (b : B) : B := ((extDen b : ℚ)⁻¹) • (α ⟨_, extDen_mem b⟩ : B)

theorem natCast_mul_eq_smul (n : ℕ) (x : B) : (n : B) * x = (n : ℚ) • x := by
  rw [Algebra.smul_def, map_natCast]

theorem alpha_nat_smul (n : ℕ) (x : B) (hx : x ∈ O) (hnx : (n : ℚ) • x ∈ O) :
    (α ⟨_, hnx⟩ : B) = (n : ℚ) • (α ⟨x, hx⟩ : B) := by
  have : (⟨_, hnx⟩ : O) = (n : O) * ⟨x, hx⟩ := by
    apply Subtype.ext
    simp only [MulMemClass.coe_mul, SubringClass.coe_natCast]
    rw [natCast_mul_eq_smul]
  rw [this, map_mul, map_natCast, MulMemClass.coe_mul, SubringClass.coe_natCast,
    natCast_mul_eq_smul]

/-- Independence of the choice of `m`. -/
theorem extFun_eq (b : B) (m : ℕ) (hm : 0 < m) (hb : (m : ℚ) • b ∈ O) :
    extFun α b = ((m : ℚ)⁻¹) • (α ⟨_, hb⟩ : B) := by
  have hd : 0 < extDen b := extDen_pos b
  have hdm : (m : ℚ) • ((extDen b : ℚ) • b) ∈ O := nat_smul_mem m (extDen_mem b)
  have hmd : (extDen b : ℚ) • ((m : ℚ) • b) ∈ O := nat_smul_mem (extDen b) hb
  have e1 := alpha_nat_smul α m _ (extDen_mem b) hdm
  have e2 := alpha_nat_smul α (extDen b) _ hb hmd
  have e3 : (⟨_, hdm⟩ : O) = ⟨_, hmd⟩ := Subtype.ext (smul_comm _ _ _)
  rw [e3, e2] at e1
  -- e1 : d • α(m b) = m • α(d b)
  unfold extFun
  have hX : (α ⟨_, extDen_mem b⟩ : B) = ((m : ℚ)⁻¹ * extDen b) • (α ⟨_, hb⟩ : B) := by
    rw [mul_smul, e1, smul_smul, inv_mul_cancel₀ (by exact_mod_cast hm.ne'), one_smul]
  rw [hX, smul_smul]
  congr 1
  have : (extDen b : ℚ) ≠ 0 := by exact_mod_cast hd.ne'
  field_simp

theorem extFun_coe (a : O) : extFun α a = α a := by
  have h1 : ((1 : ℕ) : ℚ) • (a : B) ∈ O := by simp
  rw [extFun_eq α a 1 one_pos h1]
  have : (⟨_, h1⟩ : O) = a := Subtype.ext (by simp)
  rw [this]; simp

/-- A common multiplier for two elements. -/
theorem common_den (b c : B) : ∃ m : ℕ, 0 < m ∧ (m : ℚ) • b ∈ O ∧ (m : ℚ) • c ∈ O := by
  refine ⟨extDen b * extDen c, Nat.mul_pos (extDen_pos b) (extDen_pos c), ?_, ?_⟩
  · have := nat_smul_mem (extDen c) (extDen_mem b)
    rwa [smul_smul, ← Nat.cast_mul, mul_comm] at this
  · have := nat_smul_mem (extDen b) (extDen_mem c)
    rwa [smul_smul, ← Nat.cast_mul] at this

theorem extFun_add (b c : B) : extFun α (b + c) = extFun α b + extFun α c := by
  obtain ⟨m, hm, hb, hc⟩ := common_den b c
  have hbc : (m : ℚ) • (b + c) ∈ O := by rw [smul_add]; exact O.add_mem hb hc
  rw [extFun_eq α _ m hm hbc, extFun_eq α _ m hm hb, extFun_eq α _ m hm hc, ← smul_add]
  congr 1
  have : (⟨_, hbc⟩ : O) = ⟨_, hb⟩ + ⟨_, hc⟩ := Subtype.ext (by simp [smul_add])
  rw [this, map_add]; rfl

theorem smul_mul_smul' (r s : ℚ) (x y : B) : (r • x) * (s • y) = (r * s) • (x * y) := by
  rw [smul_mul_assoc, mul_smul_comm, smul_smul]

theorem extFun_mul (b c : B) : extFun α (b * c) = extFun α b * extFun α c := by
  obtain ⟨m, hm, hb, hc⟩ := common_den b c
  have hbc0 : ((m : ℚ) * m) • (b * c) ∈ O := by
    rw [← smul_mul_smul']; exact O.mul_mem hb hc
  have hbc : ((m * m : ℕ) : ℚ) • (b * c) ∈ O := by rw [Nat.cast_mul]; exact hbc0
  have hprod : (⟨_, hbc⟩ : O) = ⟨_, hb⟩ * ⟨_, hc⟩ := by
    apply Subtype.ext
    show ((m * m : ℕ) : ℚ) • (b * c) = ((m : ℚ) • b) * ((m : ℚ) • c)
    rw [smul_mul_smul', Nat.cast_mul]
  have e1 : (α ⟨_, hbc⟩ : B) = (α ⟨_, hb⟩ : B) * (α ⟨_, hc⟩ : B) := by
    rw [hprod, map_mul, MulMemClass.coe_mul]
  rw [extFun_eq α _ (m * m) (Nat.mul_pos hm hm) hbc, extFun_eq α _ m hm hb,
    extFun_eq α _ m hm hc, smul_mul_smul', e1, Nat.cast_mul, mul_inv]

theorem extFun_algebraMap (q : ℚ) : extFun α (algebraMap ℚ B q) = algebraMap ℚ B q := by
  have hq : ((q.den : ℕ) : ℚ) • algebraMap ℚ B q ∈ O := by
    rw [Algebra.smul_def, ← map_mul, Rat.den_mul_eq_num, map_intCast]
    exact intCast_mem O q.num
  rw [extFun_eq α _ q.den q.den_pos hq]
  have : (⟨_, hq⟩ : O) = (q.num : O) := Subtype.ext (by
    simp only [SubringClass.coe_intCast]
    rw [Algebra.smul_def, ← map_mul, Rat.den_mul_eq_num, map_intCast])
  rw [this, map_intCast, SubringClass.coe_intCast, ← map_intCast (algebraMap ℚ B),
    Algebra.smul_def, ← map_mul]
  congr 1
  rw [inv_mul_eq_div, Rat.num_div_den]

/-- The extension `α̃ : B → B` as a `ℚ`-algebra map. -/
def extAlgHom : B →ₐ[ℚ] B where
  toFun := extFun α
  map_one' := by simpa using extFun_coe α 1
  map_zero' := by simpa using extFun_coe α 0
  map_add' := extFun_add α
  map_mul' := extFun_mul α
  commutes' := extFun_algebraMap α

theorem extAlgHom_apply (b : B) : extAlgHom α b = extFun α b := rfl

theorem extAlgHom_coe (a : O) : extAlgHom α a = α a := extFun_coe α a

theorem extAlgHom_symm_comp : (extAlgHom α.symm).comp (extAlgHom α) = AlgHom.id ℚ B := by
  refine AlgHom.ext fun b => ?_
  change extAlgHom α.symm (extFun α b) = b
  rw [extFun_eq α b (extDen b) (extDen_pos b) (extDen_mem b), map_smul, extAlgHom_coe,
    RingEquiv.symm_apply_apply, smul_smul, inv_mul_cancel₀ (by exact_mod_cast (extDen_pos b).ne'),
    one_smul]

/-- The extension as a `ℚ`-algebra automorphism of `B`. -/
def extAlgEquiv : B ≃ₐ[ℚ] B :=
  AlgEquiv.ofAlgHom (extAlgHom α) (extAlgHom α.symm)
    (by simpa using extAlgHom_symm_comp α.symm) (extAlgHom_symm_comp α)

theorem extAlgEquiv_apply (b : B) : extAlgEquiv α b = extFun α b := rfl

/-! ### `AutOInnerFinite` from Skolem–Noether and the normalizer -/

/-- **Normalizer fact (N(𝒪)/ℚ^×𝒪^× finite).** Every `u ∈ B^×` normalizing `𝒪` is
`q · v · t` with `q ∈ ℚ^×`, `v ∈ 𝒪^×` and `t` in a fixed finite set. -/
def NormalizerFinite : Prop :=
  ∃ T : Set Bˣ, T.Finite ∧ ∀ u : Bˣ, (∀ a : B, a ∈ O ↔ (u : B) * a * ((u⁻¹ : Bˣ) : B) ∈ O) →
    ∃ t ∈ T, ∃ v : Oˣ, ∃ q : ℚ, q ≠ 0 ∧ (u : B) = algebraMap ℚ B q * ((v : O) : B) * (t : B)

/-- Skolem–Noether (proved in the kernel, `TSkolemKW.leafSkolemNoether`) applied to `α̃`. -/
theorem conj_of_skolem : ∃ u : Bˣ, ∀ b : B, extFun α b = u * b * ((u⁻¹ : Bˣ) : B) := by
  obtain ⟨u, hu⟩ := GlueDescent.B6_inner TSkolemKW.leafSkolemNoether (extAlgEquiv α)
  exact ⟨u, fun b => hu b⟩

/-- Conjugation by a unit of `𝒪`, `a ↦ v⁻¹ a v`. -/
def conjUnit (v : Oˣ) : O ≃+* O where
  toFun a := ((v⁻¹ : Oˣ) : O) * a * v
  invFun a := (v : O) * a * ((v⁻¹ : Oˣ) : O)
  left_inv a := by
    simp only [mul_assoc, Units.mul_inv, mul_one, Units.mul_inv_cancel_left]
  right_inv a := by
    simp only [mul_assoc, Units.inv_mul, mul_one, Units.inv_mul_cancel_left]
  map_mul' a b := by
    simp only [mul_assoc, Units.mul_inv_cancel_left]
  map_add' a b := by
    simp only [mul_add, add_mul]

theorem key_conj {R : Type*} [Ring R] (x y w w' c c' t : R) (hvv : w' * w = 1) (hcc : c' * c = 1)
    (hc : c * x = x * c) (h : x * (c * w * t) = c * w * t * y) : w' * x * w * t = t * y := by
  have h1 : x * w * t = w * t * y := by
    calc x * w * t = c' * (c * x) * w * t := by rw [← mul_assoc, hcc, one_mul]
      _ = c' * (x * (c * w * t)) := by rw [hc]; simp only [mul_assoc]
      _ = c' * (c * w * t * y) := by rw [h]
      _ = w * t * y := by simp only [← mul_assoc]; rw [hcc, one_mul]
  calc w' * x * w * t = w' * (x * w * t) := by simp only [mul_assoc]
    _ = w' * (w * t * y) := by rw [h1]
    _ = t * y := by simp only [← mul_assoc]; rw [hvv, one_mul]

/-- **`AutOInnerFinite` from the normalizer fact** (with Skolem–Noether from the kernel). -/
theorem autOInnerFinite_of_normalizer (hN : NormalizerFinite) : AutOInnerFinite := by
  classical
  obtain ⟨T, hT, hTu⟩ := hN
  let P : (O ≃+* O) → Bˣ → Prop := fun β t => ∀ a : O, ((β a : O) : B) * t = t * a
  let T' : Set (O ≃+* O) := {β | ∃ t ∈ T, P β t}
  let f : (O ≃+* O) → Bˣ := fun β => if h : ∃ t ∈ T, P β t then Classical.choose h else 1
  have hf : ∀ β ∈ T', f β ∈ T ∧ P β (f β) := by
    intro β hβ
    have hβ' : ∃ t ∈ T, P β t := hβ
    simp only [f, hβ', dite_true]
    exact Classical.choose_spec hβ'
  have hT' : T'.Finite := by
    refine Set.Finite.of_finite_image (f := f) (hT.subset (t := f '' T') ?_) ?_
    · rintro _ ⟨β, hβ, rfl⟩; exact (hf β hβ).1
    · intro β₁ h₁ β₂ h₂ heq
      apply RingEquiv.ext; intro a
      apply Subtype.ext
      have e1 := (hf β₁ h₁).2 a
      have e2 := (hf β₂ h₂).2 a
      rw [heq] at e1
      exact (Units.mul_left_inj (f β₂)).1 (e1.trans e2.symm)
  refine ⟨T', hT', fun α => ?_⟩
  obtain ⟨u, hu⟩ := conj_of_skolem α
  have hback : ∀ b : B, extFun α.symm (extFun α b) = b := fun b =>
    congrArg (fun φ : B →ₐ[ℚ] B => φ b) (extAlgHom_symm_comp α)
  have hnorm : ∀ a : B, a ∈ O ↔ (u : B) * a * ((u⁻¹ : Bˣ) : B) ∈ O := by
    intro a
    rw [← hu]
    constructor
    · intro ha
      rw [show a = ((⟨a, ha⟩ : O) : B) from rfl, extFun_coe]
      exact (α _).2
    · intro ha
      rw [← hback a, show extFun α a = ((⟨_, ha⟩ : O) : B) from rfl, extFun_coe]
      exact (α.symm _).2
  obtain ⟨t, ht, v, q, hq, huq⟩ := hTu u hnorm
  have hrel : ∀ a : O, ((α a : O) : B) * u = u * a := by
    intro a
    rw [← extFun_coe, hu, Units.inv_mul_cancel_right]
  let β : O ≃+* O := α.trans (conjUnit v)
  have hβ : ∀ a : O, β a = ((v⁻¹ : Oˣ) : O) * α a * v := fun a => rfl
  refine ⟨β, ⟨t, ht, fun a => ?_⟩, v, fun a => ?_⟩
  · have hvv : (((v⁻¹ : Oˣ) : O) : B) * ((v : O) : B) = 1 := by
      rw [← MulMemClass.coe_mul, Units.inv_mul]; rfl
    have hcc : algebraMap ℚ B q⁻¹ * algebraMap ℚ B q = 1 := by
      rw [← map_mul, inv_mul_cancel₀ hq, map_one]
    have h := hrel a
    rw [huq] at h
    rw [hβ, MulMemClass.coe_mul, MulMemClass.coe_mul]
    exact key_conj _ _ _ _ _ _ _ hvv hcc (Algebra.commutes q _) h
  · rw [hβ]
    simp only [mul_assoc, Units.mul_inv, mul_one, Units.mul_inv_cancel_left]

end AutOExt

/-- **`MobiusGlue` from the two curve facts, the leaf `TorsionStructure` (T5) and
`NormalizerFinite` (`N(𝒪)/ℚ^×𝒪^×` finite).** Skolem–Noether enters through the kernel's proof
`TSkolemKW.leafSkolemNoether`. -/
theorem mobiusGlue_of_normalizer (hRF : CurveRatFactor) (hSu : CurveSurj)
    (hT : ObjBridge.TorsionStructure) (hN : AutOExt.NormalizerFinite) : MobiusGlue :=
  mobiusGlue_of_named hRF hSu hT (AutOExt.autOInnerFinite_of_normalizer hN)

end Pin

end AV

end LeafQM


/-! ## §8 `NormalizerFinite`, proved: `N(𝒪)/ℚ^×𝒪^×` is represented by `{1, i, j, ij}`

Descent on `|nrd|`. A prime `p ∤ 6` dividing `nrd(u)` of a normalizing `u ∈ 𝒪` divides `u`: an
explicit identity `6 x_l² = Σ λ · coord(u e_k ū)` (coefficients from PARI's `matsolvemod`,
`scratch/mobius-glue/py/normalizer_identity.py`). If `2 | nrd(u)` then `u i⁻¹ ∈ 𝒪`, and if
`3 | nrd(u)` then `u j⁻¹ ∈ 𝒪` (checks modulo 2 and 3 by `decide`). -/

namespace LeafQM

namespace AV

namespace Pin

namespace NormO

/-! ### Integer coordinates -/

/-- The reduced norm in the coordinates of `ofInt`. -/
def nrdZ (n : Fin 4 → ℤ) : ℤ :=
  n 0 ^ 2 + n 0 * n 2 - 2 * n 1 ^ 2 - 2 * n 1 * n 3 + n 2 ^ 2 - 2 * n 3 ^ 2

/-- The conjugate in the coordinates of `ofInt`. -/
def conjC (n : Fin 4 → ℤ) : Fin 4 → ℤ := ![n 0 + n 2, -n 1, -n 2, -n 3]

theorem mulCoord_conjC (n : Fin 4 → ℤ) : mulCoord n (conjC n) = ![nrdZ n, 0, 0, 0] := by
  funext l; fin_cases l <;> simp [mulCoord, conjC, nrdZ] <;> ring

theorem mulCoord_conjC' (n : Fin 4 → ℤ) : mulCoord (conjC n) n = ![nrdZ n, 0, 0, 0] := by
  funext l; fin_cases l <;> simp [mulCoord, conjC, nrdZ] <;> ring

theorem nrdZ_mul (n m : Fin 4 → ℤ) : nrdZ (mulCoord n m) = nrdZ n * nrdZ m := by
  simp [mulCoord, nrdZ]; ring

theorem ofInt_scalar (z : ℤ) : ofInt ![z, 0, 0, 0] = algebraMap ℚ B (z : ℚ) := by
  ext <;> simp [ofInt]

theorem smul_ofInt (z : ℤ) (n : Fin 4 → ℤ) : (z : ℚ) • ofInt n = ofInt (fun l => z * n l) := by
  ext <;> simp [ofInt] <;> ring

theorem mem_O_iff (x : B) : x ∈ O ↔ ∃ n, x = ofInt n := Iff.rfl

/-- `(1/z) • ofInt m ∈ 𝒪` forces `z ∣ m`. -/
theorem dvd_of_smul_mem {z : ℤ} (hz : z ≠ 0) {m : Fin 4 → ℤ}
    (h : ((z : ℚ)⁻¹) • ofInt m ∈ O) : ∀ l, z ∣ m l := by
  obtain ⟨w, hw⟩ := h
  have : ofInt m = ofInt (fun l => z * w l) := by
    rw [← smul_ofInt, ← hw, smul_smul, mul_inv_cancel₀ (by exact_mod_cast hz), one_smul]
  have e := AV.ofInt_injective this
  intro l
  exact ⟨w l, congrFun e l⟩

/-! ### The units `i`, `j` of `B` -/

def ei : Fin 4 → ℤ := ![0, 1, 0, 0]
def ej : Fin 4 → ℤ := ![-1, 0, 2, 0]

theorem nrdZ_ei : nrdZ ei = -2 := by simp [nrdZ, ei]
theorem nrdZ_ej : nrdZ ej = 3 := by simp [nrdZ, ej]

def ui : Bˣ where
  val := ofInt ei
  inv := ((2 : ℚ)⁻¹) • ofInt ei
  val_inv := by
    rw [mul_smul_comm, ofInt_mul]
    ext <;> simp [ofInt, mulCoord, ei]
  inv_val := by
    rw [smul_mul_assoc, ofInt_mul]
    ext <;> simp [ofInt, mulCoord, ei]

def uj : Bˣ where
  val := ofInt ej
  inv := ((-3 : ℚ)⁻¹) • ofInt ej
  val_inv := by
    rw [mul_smul_comm, ofInt_mul]
    ext <;> simp [ofInt, mulCoord, ej]
  inv_val := by
    rw [smul_mul_assoc, ofInt_mul]
    ext <;> simp [ofInt, mulCoord, ej]

/-- The representatives `{1, i, j, ij}` of `N(𝒪)/ℚ^×𝒪^×`. -/
def T : Set Bˣ := {1, ui, uj, ui * uj}

theorem T_finite : T.Finite := by
  simp only [T]
  exact ((((Set.finite_singleton _).insert _).insert _).insert _)

/-! ### Normalizing units -/

/-- `u` normalizes `𝒪`. -/
def IsNorm (u : Bˣ) : Prop :=
  ∀ a ∈ O, (u : B) * a * ((u⁻¹ : Bˣ) : B) ∈ O ∧ ((u⁻¹ : Bˣ) : B) * a * u ∈ O

theorem IsNorm.mul {u w : Bˣ} (hu : IsNorm u) (hw : IsNorm w) : IsNorm (u * w) := by
  intro a ha
  refine ⟨?_, ?_⟩
  · have := (hu _ (hw a ha).1).1
    simpa [mul_inv_rev, Units.val_mul, mul_assoc] using this
  · have := (hw _ (hu a ha).2).2
    simpa [mul_inv_rev, Units.val_mul, mul_assoc] using this

theorem IsNorm.inv {u : Bˣ} (hu : IsNorm u) : IsNorm u⁻¹ := by
  intro a ha
  obtain ⟨h1, h2⟩ := hu a ha
  exact ⟨h2, by simpa using h1⟩

/-- The unit `c ∈ ℚ^×` of `B`. -/
def sc (c : ℚ) (hc : c ≠ 0) : Bˣ where
  val := algebraMap ℚ B c
  inv := algebraMap ℚ B c⁻¹
  val_inv := by rw [← map_mul, mul_inv_cancel₀ hc, map_one]
  inv_val := by rw [← map_mul, inv_mul_cancel₀ hc, map_one]

theorem isNorm_sc (c : ℚ) (hc : c ≠ 0) : IsNorm (sc c hc) := by
  intro a ha
  have e1 : ((sc c hc : Bˣ) : B) * a * (((sc c hc)⁻¹ : Bˣ) : B) = a := by
    change algebraMap ℚ B c * a * algebraMap ℚ B c⁻¹ = a
    rw [Algebra.commutes, mul_assoc, ← map_mul, mul_inv_cancel₀ hc, map_one, mul_one]
  have e2 : (((sc c hc)⁻¹ : Bˣ) : B) * a * ((sc c hc : Bˣ) : B) = a := by
    change algebraMap ℚ B c⁻¹ * a * algebraMap ℚ B c = a
    rw [Algebra.commutes, mul_assoc, ← map_mul, inv_mul_cancel₀ hc, map_one, mul_one]
  exact ⟨by rw [e1]; exact ha, by rw [e2]; exact ha⟩

theorem isNorm_ui : IsNorm ui := by
  rintro a ⟨n, rfl⟩
  have e : ((ui : Bˣ) : B) * ofInt n * ((ui⁻¹ : Bˣ) : B) =
      ofInt ![n 0 + n 2, n 1 + n 3, -n 2, -n 3] := by
    change ofInt ei * ofInt n * (((2 : ℚ)⁻¹) • ofInt ei) = _
    rw [mul_smul_comm, ofInt_mul, ofInt_mul]
    ext <;> simp [ofInt, mulCoord, ei] <;> ring
  have e' : ((ui⁻¹ : Bˣ) : B) * ofInt n * ((ui : Bˣ) : B) =
      ofInt ![n 0 + n 2, n 1 + n 3, -n 2, -n 3] := by
    change (((2 : ℚ)⁻¹) • ofInt ei) * ofInt n * ofInt ei = _
    rw [smul_mul_assoc, smul_mul_assoc, ofInt_mul, ofInt_mul]
    ext <;> simp [ofInt, mulCoord, ei] <;> ring
  exact ⟨⟨_, e⟩, ⟨_, e'⟩⟩

theorem isNorm_uj : IsNorm uj := by
  rintro a ⟨n, rfl⟩
  have e : ((uj : Bˣ) : B) * ofInt n * ((uj⁻¹ : Bˣ) : B) = ofInt ![n 0, -n 1, n 2, -n 3] := by
    change ofInt ej * ofInt n * (((-3 : ℚ)⁻¹) • ofInt ej) = _
    rw [mul_smul_comm, ofInt_mul, ofInt_mul]
    ext <;> simp [ofInt, mulCoord, ej] <;> ring
  have e' : ((uj⁻¹ : Bˣ) : B) * ofInt n * ((uj : Bˣ) : B) = ofInt ![n 0, -n 1, n 2, -n 3] := by
    change (((-3 : ℚ)⁻¹) • ofInt ej) * ofInt n * ofInt ej = _
    rw [smul_mul_assoc, smul_mul_assoc, ofInt_mul, ofInt_mul]
    ext <;> simp [ofInt, mulCoord, ej] <;> ring
  exact ⟨⟨_, e⟩, ⟨_, e'⟩⟩

/-! ### The norm of a unit in `𝒪` and its inverse -/

theorem nrdZ_ne_zero (u : Bˣ) (n : Fin 4 → ℤ) (hu : (u : B) = ofInt n) : nrdZ n ≠ 0 := by
  intro h0
  have h1 : (u : B) * ofInt (conjC n) = 0 := by
    rw [hu, ofInt_mul, mulCoord_conjC, h0, ofInt_scalar]; simp
  have h2 : ofInt (conjC n) = 0 := by
    have := congrArg (fun x => ((u⁻¹ : Bˣ) : B) * x) h1
    simpa [← mul_assoc] using this
  have h3 : conjC n = 0 := AV.ofInt_injective (h2.trans ofInt_zero.symm)
  have h4 : n = 0 := by
    funext l
    have e0 := congrFun h3 0; have e1 := congrFun h3 1
    have e2 := congrFun h3 2; have e3 := congrFun h3 3
    simp [conjC] at e0 e1 e2 e3
    fin_cases l <;> simp <;> omega
  have : (u : B) = 0 := by rw [hu, h4, ofInt_zero]
  exact u.ne_zero this

theorem inv_eq (u : Bˣ) (n : Fin 4 → ℤ) (hu : (u : B) = ofInt n) :
    ((u⁻¹ : Bˣ) : B) = ((nrdZ n : ℚ)⁻¹) • ofInt (conjC n) := by
  have hN : (nrdZ n : ℚ) ≠ 0 := by exact_mod_cast nrdZ_ne_zero u n hu
  apply Units.inv_eq_of_mul_eq_one_right
  rw [mul_smul_comm, hu, ofInt_mul, mulCoord_conjC, ofInt_scalar, Algebra.smul_def, ← map_mul,
    inv_mul_cancel₀ hN, map_one]

def bas : Fin 4 → (Fin 4 → ℤ) := ![![1, 0, 0, 0], ![0, 1, 0, 0], ![0, 0, 1, 0], ![0, 0, 0, 1]]

/-- For a normalizing `u = ofInt n`, `nrd(u)` divides every coordinate of `u e_k ū`. -/
theorem nrd_dvd_coords (u : Bˣ) (n : Fin 4 → ℤ) (hu : (u : B) = ofInt n) (hN : IsNorm u)
    (k l : Fin 4) : nrdZ n ∣ mulCoord (mulCoord n (bas k)) (conjC n) l := by
  have h := (hN (ofInt (bas k)) ⟨_, rfl⟩).1
  rw [inv_eq u n hu, mul_smul_comm, hu, ofInt_mul, ofInt_mul] at h
  exact dvd_of_smul_mem (nrdZ_ne_zero u n hu) h l

/-- The identities `6 x_l² = Σ λ · coord(u e_k ū)` (coefficients from PARI's `matsolvemod`). -/
theorem six_sq_identities (n : Fin 4 → ℤ) :
    let F := fun k l => mulCoord (mulCoord n (bas k)) (conjC n) l
    6 * n 0 ^ 2 = 2 * F 0 0 + 2 * F 1 1 + 2 * F 1 3 + 2 * F 2 2 - 2 * F 3 1 ∧
    6 * n 1 ^ 2 = -F 1 1 - 2 * F 2 0 + F 3 1 + F 3 3 ∧
    6 * n 2 ^ 2 = 2 * F 0 0 - 2 * F 1 1 + 2 * F 2 2 - 2 * F 3 3 ∧
    6 * n 3 ^ 2 = F 1 1 + F 1 3 - 2 * F 2 0 - F 3 3 := by
  intro F
  simp only [F, mulCoord, bas, conjC]
  refine ⟨?_, ?_, ?_, ?_⟩ <;> simp <;> ring

/-- A prime `p ≠ 2, 3` dividing `nrd(u)` of a normalizing `u = ofInt n` divides `n`. -/
theorem dvd_of_prime_dvd_nrd (u : Bˣ) (n : Fin 4 → ℤ) (hu : (u : B) = ofInt n) (hN : IsNorm u)
    (p : ℕ) (hp : p.Prime) (h2 : p ≠ 2) (h3 : p ≠ 3) (hpd : (p : ℤ) ∣ nrdZ n) :
    ∀ l, (p : ℤ) ∣ n l := by
  have hpZ : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
  have hF : ∀ k l, (p : ℤ) ∣ mulCoord (mulCoord n (bas k)) (conjC n) l :=
    fun k l => hpd.trans (nrd_dvd_coords u n hu hN k l)
  have h6 : ¬ (p : ℤ) ∣ 6 := by
    intro h
    have h' : p ∣ 6 := by exact_mod_cast h
    have : p ∣ 2 * 3 := h'
    rcases (Nat.Prime.dvd_mul hp).mp this with h | h
    · exact h2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h)
    · exact h3 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).mp h)
  obtain ⟨i0, i1, i2, i3⟩ := six_sq_identities n
  have k0 : (p : ℤ) ∣ 6 * n 0 ^ 2 := by
    rw [i0]
    exact dvd_sub (dvd_add (dvd_add (dvd_add (dvd_mul_of_dvd_right (hF 0 0) _)
      (dvd_mul_of_dvd_right (hF 1 1) _)) (dvd_mul_of_dvd_right (hF 1 3) _))
      (dvd_mul_of_dvd_right (hF 2 2) _)) (dvd_mul_of_dvd_right (hF 3 1) _)
  have k1 : (p : ℤ) ∣ 6 * n 1 ^ 2 := by
    rw [i1]
    exact dvd_add (dvd_add (dvd_sub (dvd_neg.mpr (hF 1 1)) (dvd_mul_of_dvd_right (hF 2 0) _))
      (hF 3 1)) (hF 3 3)
  have k2 : (p : ℤ) ∣ 6 * n 2 ^ 2 := by
    rw [i2]
    exact dvd_sub (dvd_add (dvd_sub (dvd_mul_of_dvd_right (hF 0 0) _)
      (dvd_mul_of_dvd_right (hF 1 1) _)) (dvd_mul_of_dvd_right (hF 2 2) _))
      (dvd_mul_of_dvd_right (hF 3 3) _)
  have k3 : (p : ℤ) ∣ 6 * n 3 ^ 2 := by
    rw [i3]
    exact dvd_sub (dvd_sub (dvd_add (hF 1 1) (hF 1 3)) (dvd_mul_of_dvd_right (hF 2 0) _))
      (hF 3 3)
  have key : ∀ l, (p : ℤ) ∣ 6 * n l ^ 2 := by
    intro l; fin_cases l
    exacts [k0, k1, k2, k3]
  intro l
  rcases hpZ.dvd_or_dvd (key l) with h | h
  · exact absurd h h6
  · exact hpZ.dvd_of_dvd_pow h

/-! ### The primes 2 and 3 -/

theorem two_dvd_mulCoord_ei (n : Fin 4 → ℤ) (h : (2 : ℤ) ∣ nrdZ n) :
    ∀ l, (2 : ℤ) ∣ mulCoord n ei l := by
  have hz : ((nrdZ n : ℤ) : ZMod 2) = 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ 2).mpr h
  simp only [nrdZ] at hz
  push_cast at hz
  have key : ∀ a b c d : ZMod 2,
      a ^ 2 + a * c - 2 * b ^ 2 - 2 * b * d + c ^ 2 - 2 * d ^ 2 = 0 → a = 0 ∧ c = 0 := by
    decide
  obtain ⟨h0, h2⟩ := key _ _ _ _ hz
  have d0 : (2 : ℤ) ∣ n 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ 2).mp h0
  have d2 : (2 : ℤ) ∣ n 2 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ 2).mp h2
  intro l
  fin_cases l <;> simp [mulCoord, ei] <;> omega

theorem three_dvd_mulCoord_ej (n : Fin 4 → ℤ) (h : (3 : ℤ) ∣ nrdZ n) :
    ∀ l, (3 : ℤ) ∣ mulCoord n ej l := by
  have hz : ((nrdZ n : ℤ) : ZMod 3) = 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ 3).mpr h
  simp only [nrdZ] at hz
  push_cast at hz
  have key : ∀ a b c d : ZMod 3,
      a ^ 2 + a * c - 2 * b ^ 2 - 2 * b * d + c ^ 2 - 2 * d ^ 2 = 0 → a - c = 0 ∧ b - d = 0 := by
    decide
  obtain ⟨h0, h1⟩ := key _ _ _ _ hz
  have d0 : (3 : ℤ) ∣ n 0 - n 2 :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd _ 3).mp (by push_cast; exact h0)
  have d1 : (3 : ℤ) ∣ n 1 - n 3 :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd _ 3).mp (by push_cast; exact h1)
  intro l
  fin_cases l <;> simp [mulCoord, ej] <;> omega

/-! ### Closure of `T` under right multiplication by `i` and `j` -/

theorem T_mem_iff (t : Bˣ) : t ∈ T ↔ t = 1 ∨ t = ui ∨ t = uj ∨ t = ui * uj := Iff.rfl

theorem T_mul_ui : ∀ t ∈ T, ∃ c : ℚ, c ≠ 0 ∧ ∃ t' ∈ T,
    (t : B) * (ui : B) = algebraMap ℚ B c * (t' : B) := by
  intro t ht
  rcases ht with rfl | rfl | rfl | rfl
  · exact ⟨1, one_ne_zero, ui, by simp [T], by simp⟩
  · refine ⟨2, two_ne_zero, 1, by simp [T], ?_⟩
    change ofInt ei * ofInt ei = _
    rw [ofInt_mul]; ext <;> simp [ofInt, mulCoord, ei, QuaternionAlgebra.algebraMap_eq]
  · refine ⟨-1, by norm_num, ui * uj, by simp [T], ?_⟩
    change ofInt ej * ofInt ei = _ * (ofInt ei * ofInt ej)
    rw [ofInt_mul, ofInt_mul]
    ext <;> simp [ofInt, mulCoord, ei, ej, QuaternionAlgebra.algebraMap_eq] <;> norm_num
  · refine ⟨-2, by norm_num, uj, by simp [T], ?_⟩
    change ofInt ei * ofInt ej * ofInt ei = _ * ofInt ej
    rw [ofInt_mul, ofInt_mul]
    ext <;> simp [ofInt, mulCoord, ei, ej, QuaternionAlgebra.algebraMap_eq] <;> norm_num

theorem T_mul_uj : ∀ t ∈ T, ∃ c : ℚ, c ≠ 0 ∧ ∃ t' ∈ T,
    (t : B) * (uj : B) = algebraMap ℚ B c * (t' : B) := by
  intro t ht
  rcases ht with rfl | rfl | rfl | rfl
  · exact ⟨1, one_ne_zero, uj, by simp [T], by simp⟩
  · exact ⟨1, one_ne_zero, ui * uj, by simp [T], by simp⟩
  · refine ⟨-3, by norm_num, 1, by simp [T], ?_⟩
    change ofInt ej * ofInt ej = _
    rw [ofInt_mul]; ext <;> simp [ofInt, mulCoord, ej, QuaternionAlgebra.algebraMap_eq] <;> norm_num
  · refine ⟨-3, by norm_num, ui, by simp [T], ?_⟩
    change ofInt ei * ofInt ej * ofInt ej = _ * ofInt ei
    rw [ofInt_mul, ofInt_mul]
    ext <;> simp [ofInt, mulCoord, ei, ej, QuaternionAlgebra.algebraMap_eq] <;> norm_num

/-- Rearranging `q v t i = (q c) v t'` for central `c`. -/
theorem rearrange (q c : ℚ) (V Tt I T' : B) (h : Tt * I = algebraMap ℚ B c * T') :
    algebraMap ℚ B q * V * Tt * I = algebraMap ℚ B (q * c) * V * T' := by
  rw [mul_assoc (algebraMap ℚ B q * V), h, ← mul_assoc, mul_assoc (algebraMap ℚ B q),
    ← Algebra.commutes c V, ← mul_assoc, ← map_mul]

theorem mulCoord_smul_right (n m : Fin 4 → ℤ) (z : ℤ) :
    mulCoord n (fun l => z * m l) = fun l => z * mulCoord n m l := by
  funext l; fin_cases l <;> simp [mulCoord] <;> ring

theorem mulCoord_smul_left (n m : Fin 4 → ℤ) (z : ℤ) :
    mulCoord (fun l => z * n l) m = fun l => z * mulCoord n m l := by
  funext l; fin_cases l <;> simp [mulCoord] <;> ring

theorem nrdZ_smul (n : Fin 4 → ℤ) (z : ℤ) : nrdZ (fun l => z * n l) = z ^ 2 * nrdZ n := by
  simp [nrdZ]; ring

/-! ### The descent -/

theorem descent (m : ℕ) : ∀ (u : Bˣ) (n : Fin 4 → ℤ), (u : B) = ofInt n →
    (nrdZ n).natAbs = m → IsNorm u →
    ∃ q : ℚ, q ≠ 0 ∧ ∃ v : Oˣ, ∃ t ∈ T, (u : B) = algebraMap ℚ B q * ((v : O) : B) * t := by
  induction m using Nat.strong_induction_on with
  | _ m ih =>
  intro u n hu hm hN
  have hN0 := nrdZ_ne_zero u n hu
  by_cases h1 : m = 1
  · have hsq : nrdZ n * nrdZ n = 1 := by
      have : (nrdZ n).natAbs = 1 := hm.trans h1
      rcases Int.natAbs_eq_iff.mp this with h | h <;> rw [h] <;> norm_num
    set w : Fin 4 → ℤ := fun l => nrdZ n * conjC n l with hw_def
    have hw1 : mulCoord n w = ![1, 0, 0, 0] := by
      rw [hw_def, mulCoord_smul_right, mulCoord_conjC]
      funext l; fin_cases l <;> simp [hsq]
    have hw2 : mulCoord w n = ![1, 0, 0, 0] := by
      rw [hw_def, mulCoord_smul_left, mulCoord_conjC']
      funext l; fin_cases l <;> simp [hsq]
    let v : Oˣ :=
      ⟨⟨ofInt n, n, rfl⟩, ⟨ofInt w, w, rfl⟩,
        Subtype.ext (by
          change ofInt n * ofInt w = 1
          rw [ofInt_mul, hw1, ofInt_one]),
        Subtype.ext (by
          change ofInt w * ofInt n = 1
          rw [ofInt_mul, hw2, ofInt_one])⟩
    refine ⟨1, one_ne_zero, v, 1, by simp [T], ?_⟩
    rw [map_one, one_mul, Units.val_one, mul_one]
    exact hu
  · have hm0 : m ≠ 0 := by
      rintro rfl; exact hN0 (Int.natAbs_eq_zero.mp hm)
    set p := m.minFac with hp_def
    have hp : p.Prime := Nat.minFac_prime h1
    have hpd : (p : ℤ) ∣ nrdZ n := by
      rw [Int.natCast_dvd, hm]; exact Nat.minFac_dvd m
    have hp1 : 2 ≤ p := hp.two_le
    by_cases hp2 : p = 2
    · have h2 : (2 : ℤ) ∣ nrdZ n := by rw [hp2] at hpd; exact_mod_cast hpd
      have hc := two_dvd_mulCoord_ei n h2
      set n' : Fin 4 → ℤ := fun l => mulCoord n ei l / 2 with hn'_def
      have hn' : mulCoord n ei = fun l => 2 * n' l :=
        funext fun l => (Int.mul_ediv_cancel' (hc l)).symm
      have hu' : ((u * ui⁻¹ : Bˣ) : B) = ofInt n' := by
        change (u : B) * (((2 : ℚ)⁻¹) • ofInt ei) = _
        rw [mul_smul_comm, hu, ofInt_mul, hn', ← smul_ofInt, smul_smul]
        norm_num
      have hmul : mulCoord n' ei = n := by
        apply AV.ofInt_injective
        rw [← ofInt_mul, ← hu', ← hu]
        change ((u * ui⁻¹ : Bˣ) : B) * ((ui : Bˣ) : B) = u
        rw [← Units.val_mul, inv_mul_cancel_right]
      have hlt : (nrdZ n').natAbs < m := by
        have e := nrdZ_mul n' ei
        rw [hmul, nrdZ_ei] at e
        have hne : (nrdZ n').natAbs ≠ 0 := Int.natAbs_ne_zero.mpr (nrdZ_ne_zero _ _ hu')
        have h2' : (-2 : ℤ).natAbs = 2 := rfl
        rw [← hm, e, Int.natAbs_mul, h2']
        omega
      obtain ⟨q, hq, v, t, ht, he⟩ :=
        ih _ hlt (u * ui⁻¹) n' hu' rfl (hN.mul isNorm_ui.inv)
      obtain ⟨c, hc0, t', ht', htc⟩ := T_mul_ui t ht
      refine ⟨q * c, mul_ne_zero hq hc0, v, t', ht', ?_⟩
      have : (u : B) = ((u * ui⁻¹ : Bˣ) : B) * ui := by
        rw [← Units.val_mul, inv_mul_cancel_right]
      rw [this, he, rearrange q c _ _ _ _ htc]
    by_cases hp3 : p = 3
    · have h3 : (3 : ℤ) ∣ nrdZ n := by rw [hp3] at hpd; exact_mod_cast hpd
      have hc := three_dvd_mulCoord_ej n h3
      set n' : Fin 4 → ℤ := fun l => -(mulCoord n ej l / 3) with hn'_def
      have hn' : mulCoord n ej = fun l => (-3) * n' l := by
        funext l
        simp only [hn'_def]
        rw [mul_neg, neg_mul, neg_neg, Int.mul_ediv_cancel' (hc l)]
      have hu' : ((u * uj⁻¹ : Bˣ) : B) = ofInt n' := by
        change (u : B) * (((-3 : ℚ)⁻¹) • ofInt ej) = _
        rw [mul_smul_comm, hu, ofInt_mul, hn', ← smul_ofInt, smul_smul]
        norm_num
      have hmul : mulCoord n' ej = n := by
        apply AV.ofInt_injective
        rw [← ofInt_mul, ← hu', ← hu]
        change ((u * uj⁻¹ : Bˣ) : B) * ((uj : Bˣ) : B) = u
        rw [← Units.val_mul, inv_mul_cancel_right]
      have hlt : (nrdZ n').natAbs < m := by
        have e := nrdZ_mul n' ej
        rw [hmul, nrdZ_ej] at e
        have hne : (nrdZ n').natAbs ≠ 0 := Int.natAbs_ne_zero.mpr (nrdZ_ne_zero _ _ hu')
        have h3' : (3 : ℤ).natAbs = 3 := rfl
        rw [← hm, e, Int.natAbs_mul, h3']
        omega
      obtain ⟨q, hq, v, t, ht, he⟩ :=
        ih _ hlt (u * uj⁻¹) n' hu' rfl (hN.mul isNorm_uj.inv)
      obtain ⟨c, hc0, t', ht', htc⟩ := T_mul_uj t ht
      refine ⟨q * c, mul_ne_zero hq hc0, v, t', ht', ?_⟩
      have : (u : B) = ((u * uj⁻¹ : Bˣ) : B) * uj := by
        rw [← Units.val_mul, inv_mul_cancel_right]
      rw [this, he, rearrange q c _ _ _ _ htc]
    · have hdiv := dvd_of_prime_dvd_nrd u n hu hN p hp hp2 hp3 hpd
      set n' : Fin 4 → ℤ := fun l => n l / p with hn'_def
      have hn' : n = fun l => (p : ℤ) * n' l :=
        funext fun l => (Int.mul_ediv_cancel' (hdiv l)).symm
      have hp0 : (p : ℚ) ≠ 0 := by exact_mod_cast hp.ne_zero
      have hpi : ((p : ℚ)⁻¹) ≠ 0 := inv_ne_zero hp0
      have hu' : ((sc _ hpi * u : Bˣ) : B) = ofInt n' := by
        change algebraMap ℚ B ((p : ℚ)⁻¹) * u = _
        rw [← Algebra.smul_def, hu, hn', ← smul_ofInt, smul_smul]
        push_cast
        rw [inv_mul_cancel₀ hp0, one_smul]
      have hlt : (nrdZ n').natAbs < m := by
        have e : nrdZ n = (p : ℤ) ^ 2 * nrdZ n' := by rw [hn', nrdZ_smul]
        have hne : (nrdZ n').natAbs ≠ 0 := Int.natAbs_ne_zero.mpr (nrdZ_ne_zero _ _ hu')
        rw [← hm, e, Int.natAbs_mul, Int.natAbs_pow, Int.natAbs_natCast]
        have : 4 ≤ p ^ 2 := by nlinarith
        have : (nrdZ n').natAbs < p ^ 2 * (nrdZ n').natAbs := by
          have : 1 * (nrdZ n').natAbs < p ^ 2 * (nrdZ n').natAbs :=
            Nat.mul_lt_mul_of_pos_right (by omega) (by omega)
          simpa using this
        exact this
      obtain ⟨q, hq, v, t, ht, he⟩ :=
        ih _ hlt (sc _ hpi * u) n' hu' rfl ((isNorm_sc _ hpi).mul hN)
      refine ⟨p * q, mul_ne_zero hp0 hq, v, t, ht, ?_⟩
      have : (u : B) = algebraMap ℚ B (p : ℚ) * ((sc _ hpi * u : Bˣ) : B) := by
        change _ = _ * (algebraMap ℚ B ((p : ℚ)⁻¹) * u)
        rw [← mul_assoc, ← map_mul, mul_inv_cancel₀ hp0, map_one, one_mul]
      rw [this, he, ← mul_assoc, ← mul_assoc, ← map_mul]

/-! ### `NormalizerFinite` -/

/-- **`N(𝒪)/ℚ^×𝒪^×` is finite** (represented by `{1, i, j, ij}`). -/
theorem normalizerFinite : AutOExt.NormalizerFinite := by
  refine ⟨T, T_finite, fun u hu => ?_⟩
  obtain ⟨m, hm, ⟨n, hn⟩⟩ := AutOExt.exists_nat_smul_mem (u : B)
  have hm0 : (m : ℚ) ≠ 0 := by exact_mod_cast hm.ne'
  have hu0 : ((sc _ hm0 * u : Bˣ) : B) = ofInt n := by
    change algebraMap ℚ B m * u = _
    rw [← Algebra.smul_def]; exact hn
  have hN : IsNorm u := by
    intro a ha
    refine ⟨(hu a).1 ha, (hu _).2 ?_⟩
    simpa [mul_assoc] using ha
  obtain ⟨q, hq, v, t, ht, he⟩ := descent _ (sc _ hm0 * u) n hu0 rfl ((isNorm_sc _ hm0).mul hN)
  refine ⟨t, ht, v, (m : ℚ)⁻¹ * q, mul_ne_zero (inv_ne_zero hm0) hq, ?_⟩
  have : (u : B) = algebraMap ℚ B ((m : ℚ)⁻¹) * ((sc _ hm0 * u : Bˣ) : B) := by
    change _ = _ * (algebraMap ℚ B m * u)
    rw [← mul_assoc, ← map_mul, inv_mul_cancel₀ hm0, map_one, one_mul]
  rw [this, he, ← mul_assoc, ← mul_assoc, ← map_mul]

end NormO

open CategoryTheory AlgebraicGeometry

/-- **`AutOInnerFinite`, proved** (Skolem–Noether from the kernel, the normalizer from §8). -/
theorem autOInnerFinite : AutOInnerFinite :=
  AutOExt.autOInnerFinite_of_normalizer NormO.normalizerFinite

/-- **`TwistClassFinite` from the leaf `TorsionStructure` alone.** -/
theorem twistClassFinite (hT : ObjBridge.TorsionStructure) : TwistClassFinite :=
  twistClassFinite_of hT autOInnerFinite

/-- **Main result: `MobiusGlue` from the two curve facts and the textbook leaf
`TorsionStructure` (T5).** -/
theorem mobiusGlue_of_curves (hRF : CurveRatFactor) (hSu : CurveSurj)
    (hT : ObjBridge.TorsionStructure) : MobiusGlue :=
  mobiusGlue_of_curveFacts hRF hSu (twistClassFinite hT)

end Pin

end AV

end LeafQM

/-! # curve-glue: curve-facts (verbatim, without its §0 copies) and the C2K/C3K reductions -/

noncomputable section

namespace LeafQM

namespace AV

namespace Pin

open CategoryTheory AlgebraicGeometry Limits
open PkgI3

/-! ## §1 Geometric components (genuine definitions) -/

/-- `S_ℚ̄ = S ×_{Spec ℚ} Spec ℚ̄` (Mathlib's pullback). -/
abbrev bcQbar (S : Over (Spec (CommRingCat.of ℚ))) : Scheme.{0} :=
  pullback S.hom (Spec.map (CommRingCat.ofHom (algebraMap ℚ Qbar)))

/-- The `ℚ̄`-point `Spec ℚ̄ → S_ℚ̄` (a section over `Spec ℚ̄`) induced by a `ℚ̄`-point of `S`
over `ℚ`. -/
def bcPt {S : Over (Spec (CommRingCat.of ℚ))} (y : fieldPt Qbar ⟶ S) :
    Spec (CommRingCat.of Qbar) ⟶ bcQbar S :=
  pullback.lift y.left (𝟙 _) ((Over.w y).trans (Category.id_comp _).symm)

/-- **The geometric component of a `ℚ̄`-point `y` of `S`**: the connected component of the
underlying space of `S_ℚ̄` containing the (closed) point of `S_ℚ̄` at which `bcPt y` sits. For
`S` smooth over `ℚ` the connected components of `S_ℚ̄` are its irreducible components (smooth
implies normal implies locally irreducible). -/
def geomComp {S : Over (Spec (CommRingCat.of ℚ))} (y : fieldPt Qbar ⟶ S) : Set (bcQbar S) :=
  connectedComponent (Scheme.SpecToEquivOfField Qbar (bcQbar S) (bcPt y)).1

/-! ## §2 The named facts -/

/-- **(C1) A geometric component of a smooth curve has infinitely many `ℚ̄`-points.**
Glue (STANDARD): a connected component `C` of `S_ℚ̄` is a smooth curve over `ℚ̄` (a nonempty
scheme of finite type over `ℚ̄` of dimension 1); its closed points are its `ℚ̄`-points
(Nullstellensatz) and there are infinitely many of them (a Jacobson scheme with finitely many
closed points is a finite discrete set, of dimension 0); a `ℚ̄`-point of `S_ℚ̄` over `ℚ̄` is
`bcPt y` for a unique `ℚ̄`-point `y` of `S` over `ℚ` (universal property of the pullback).
Properness is not needed. Not in Mathlib v4.35 (no dimension theory of smooth morphisms). -/
def GeomCompInfinite : Prop :=
  ∀ (S : Over (Spec (CommRingCat.of ℚ))), IsProper S.hom → SmoothOfRelativeDimension 1 S.hom →
    ∀ y₀ : fieldPt Qbar ⟶ S, {y : fieldPt Qbar ⟶ S | geomComp y = geomComp y₀}.Infinite

/-- **(C2) Constant or onto on a geometric component** (Hartshorne, *Algebraic Geometry*,
Prop. II.6.8: a morphism from a complete nonsingular curve to a curve is constant or
surjective; UNVERIFIED numbering, cited so in mobius-glue). On the geometric component of `y₀`,
`σ` either takes the single value `σ(y₀)` at every `ℚ̄`-point, or takes every value of
`P¹(ℚ̄)`. Textbook leaf (published; applied to the connected component of `S_ℚ̄`, a complete
nonsingular curve over `ℚ̄`, with the dictionary between `ℚ̄`-points of `S` and closed points of
`S_ℚ̄`). Not in Mathlib v4.35 (Mathlib has `IsProper → IsClosedMap`, but no `P¹` as a scheme
and no dimension theory of curves). -/
def GeomCompConstOrOnto : Prop :=
  ∀ (S : Over (Spec (CommRingCat.of ℚ))), IsProper S.hom → SmoothOfRelativeDimension 1 S.hom →
    ∀ (σ : ToP1 S.left) (y₀ : fieldPt Qbar ⟶ S),
      (∀ y : fieldPt Qbar ⟶ S, geomComp y = geomComp y₀ →
        σ.val (K := Qbar) y.left = σ.val (K := Qbar) y₀.left) ∨
      (∀ t : OnePoint Qbar, ∃ y : fieldPt Qbar ⟶ S, geomComp y = geomComp y₀ ∧
        σ.val (K := Qbar) y.left = t)

open Polynomial in
/-- **(C3) Factorization on one geometric component where `σ` is nonconstant.** If `σ` is
nonconstant on the geometric component `C` of `y₀` and `ρ` is constant on the `σ`-fibres in `C`
(on `ℚ̄`-points), then `ρ = [F : G] ∘ σ` on the `ℚ̄`-points of `C` with finite `σ`-value, for
coprime `F, G ∈ ℚ̄[t]`. Textbook (STANDARD): `σ|_C : C → P¹` is finite of some degree `n`, and
`ℚ̄(σ) ⊆ ℚ̄(σ, ρ) ⊆ ℚ̄(C)`; the normalization `D` of the image of `(σ, ρ)` is a smooth complete
curve with `D → P¹` finite of degree `[ℚ̄(σ, ρ) : ℚ̄(σ)]`, separable (char. 0), so its general
fibre has that many points (Hartshorne II.6.9 and IV.2.2, UNVERIFIED numbering); the fibre
condition makes the general fibre a single point, so `ℚ̄(σ, ρ) = ℚ̄(σ)`, `ρ = R(σ)` in `ℚ̄(C)`,
and two morphisms `C → P¹` agreeing generically agree (C reduced, `P¹` separated).
Classified as glue (a standard consequence of textbook theorems, not one printed theorem). Not
in Mathlib v4.35 (no degree of a finite morphism of curves, no fibre count). -/
def GeomCompRatFactor : Prop :=
  ∀ (S : Over (Spec (CommRingCat.of ℚ))), IsProper S.hom → SmoothOfRelativeDimension 1 S.hom →
    ∀ (σ ρ : ToP1 S.left) (y₀ : fieldPt Qbar ⟶ S),
      (∃ y : fieldPt Qbar ⟶ S, geomComp y = geomComp y₀ ∧
        σ.val (K := Qbar) y.left ≠ σ.val (K := Qbar) y₀.left) →
      (∀ y₁ y₂ : fieldPt Qbar ⟶ S, geomComp y₁ = geomComp y₀ → geomComp y₂ = geomComp y₀ →
        σ.val (K := Qbar) y₁.left = σ.val (K := Qbar) y₂.left →
        ρ.val (K := Qbar) y₁.left = ρ.val (K := Qbar) y₂.left) →
      ∃ F G : Qbar[X], IsCoprime F G ∧ ∀ (y : fieldPt Qbar ⟶ S) (t : Qbar),
        geomComp y = geomComp y₀ → σ.val (K := Qbar) y.left = OnePoint.some t →
        ρ.val (K := Qbar) y.left = Mob.ratEval F G t

/-- **(C4) Finitely many geometric components.** Proved below (`geomCompFinite`). -/
def GeomCompFinite : Prop :=
  ∀ (S : Over (Spec (CommRingCat.of ℚ))), IsProper S.hom →
    (Set.range (geomComp (S := S))).Finite

/-! ## §3 `GeomCompFinite`, from Mathlib -/

theorem geomCompFinite : GeomCompFinite := by
  intro S hP
  have : IsNoetherian (bcQbar S) := { }
  have hfin := TopologicalSpace.NoetherianSpace.finite_irreducibleComponents (α := bcQbar S)
  classical
  refine (hfin.image (fun Z => if h : Z.Nonempty then connectedComponent h.some else ∅)).subset ?_
  rintro _ ⟨y, rfl⟩
  set x := (Scheme.SpecToEquivOfField Qbar (bcQbar S) (bcPt y)).1 with hx
  have hne : (irreducibleComponent x).Nonempty := ⟨x, mem_irreducibleComponent⟩
  refine ⟨irreducibleComponent x, irreducibleComponent_mem_irreducibleComponents x, ?_⟩
  simp only [dite_eq_left hne]
  exact (connectedComponent_eq (irreducibleComponent_subset_connectedComponent hne.some_mem)).symm

/-! ## §4 Rational interpolation by a coprime pair -/

namespace Mob

open Polynomial

variable {K : Type} [Field K]

theorem isCoprime_X_sub_C_of_eval_one {F : K[X]} {a : K} (h : F.eval a = 1) :
    IsCoprime F (X - C a) := by
  have e := modByMonic_add_div F (X - C a)
  rw [modByMonic_X_sub_C_eq_C_eval, h, map_one] at e
  exact ⟨1, -(F /ₘ (X - C a)), by linear_combination (-1 : K[X]) * e⟩

/-- **Rational interpolation.** Any assignment of values in `P¹(K)` to finitely many nodes
`t ∈ T ⊆ K` is realised by `[F : G]` with `F, G` coprime. -/
theorem exists_interp (T : Finset K) (r : K → OnePoint K) :
    ∃ F G : K[X], IsCoprime F G ∧ ∀ t ∈ T, ratEval F G t = r t := by
  classical
  set Tinf := T.filter (fun t => r t = OnePoint.infty) with hTinf
  set G : K[X] := ∏ a ∈ Tinf, (X - C a) with hG
  have hGeval : ∀ t, G.eval t = ∏ a ∈ Tinf, (t - a) := by
    intro t; simp [hG, eval_prod]
  have hG0 : ∀ t ∈ Tinf, G.eval t = 0 := by
    intro t ht; rw [hGeval]; exact Finset.prod_eq_zero ht (sub_self t)
  have hGne : ∀ t, t ∉ Tinf → G.eval t ≠ 0 := by
    intro t ht; rw [hGeval, Finset.prod_ne_zero_iff]
    intro a ha e; exact ht (by rwa [sub_eq_zero.mp e])
  let w : K → K := fun t =>
    if h : ∃ v : K, r t = OnePoint.some v then h.choose * G.eval t else 1
  set F : K[X] := Lagrange.interpolate T id w with hF
  have hFeval : ∀ t ∈ T, F.eval t = w t := fun t ht =>
    Lagrange.eval_interpolate_at_node (v := id) w (Set.injOn_id _) ht
  refine ⟨F, G, ?_, ?_⟩
  · refine IsCoprime.prod_right fun a ha => isCoprime_X_sub_C_of_eval_one ?_
    have haT : a ∈ T := (Finset.mem_filter.mp ha).1
    have hra : r a = OnePoint.infty := (Finset.mem_filter.mp ha).2
    rw [hFeval a haT]
    have : ¬ ∃ v : K, r a = OnePoint.some v := by
      rintro ⟨v, hv⟩; rw [hra] at hv; exact OnePoint.infty_ne_coe v hv
    simp only [w, dite_eq_right this]
  · intro t ht
    by_cases hti : t ∈ Tinf
    · rw [(Finset.mem_filter.mp hti).2]; simp [ratEval, hG0 t hti]
    · have hrt : r t ≠ OnePoint.infty := fun e => hti (Finset.mem_filter.mpr ⟨ht, e⟩)
      have hex : ∃ v : K, r t = OnePoint.some v := by
        induction h : r t using OnePoint.rec with
        | infty => exact absurd h hrt
        | coe v => exact ⟨v, rfl⟩
      have hGt := hGne t hti
      rw [ratEval, ite_eq_right hGt, hFeval t ht]
      simp only [w, dite_eq_left hex]
      rw [mul_div_cancel_right₀ _ hGt]
      exact hex.choose_spec.symm

end Mob

/-! ## §5 The reductions -/

/-- **`CurveSurj` from (C1) and (C2).** -/
theorem curveSurj_of_comp (h1 : GeomCompInfinite) (h2 : GeomCompConstOrOnto) : CurveSurj := by
  intro S hP hS ⟨y₀⟩ σ hfin t
  rcases h2 S hP hS σ y₀ with hc | ho
  · exact absurd ((hfin y₀).subset fun y hy => hc y hy) (h1 S hP hS y₀)
  · obtain ⟨y, -, hy⟩ := ho t
    exact ⟨y, hy⟩

/-- **`CurveRatFactor` from (C2) and (C3)** (with (C4), proved, and rational interpolation). -/
theorem curveRatFactor_of_comp (h2 : GeomCompConstOrOnto) (h3 : GeomCompRatFactor) :
    CurveRatFactor := by
  classical
  intro S hP hS σ ρ hfib
  by_cases hnc : ∃ y₀ y : fieldPt Qbar ⟶ S, geomComp y = geomComp y₀ ∧
      σ.val (K := Qbar) y.left ≠ σ.val (K := Qbar) y₀.left
  · -- a component on which `σ` is nonconstant: it is onto, and carries the rational function
    obtain ⟨y₀, hne⟩ := hnc
    obtain ⟨F, G, hcop, hR⟩ := h3 S hP hS σ ρ y₀ hne (fun y₁ y₂ _ _ h => hfib y₁ y₂ h)
    refine ⟨F, G, hcop, fun y t hy => ?_⟩
    rcases h2 S hP hS σ y₀ with hc | ho
    · obtain ⟨y', hy', hne'⟩ := hne
      exact absurd (hc y' hy') hne'
    · obtain ⟨y', hy'c, hy't⟩ := ho (OnePoint.some t)
      rw [hfib y y' (hy.trans hy't.symm)]
      exact hR y' t hy'c hy't
  · -- `σ` constant on every component: finitely many values; interpolate
    push Not at hnc
    have hV : (Set.range fun y : fieldPt Qbar ⟶ S => σ.val (K := Qbar) y.left).Finite := by
      refine ((geomCompFinite S hP).image (fun c => if h : ∃ y : fieldPt Qbar ⟶ S,
        geomComp y = c then σ.val (K := Qbar) h.choose.left else OnePoint.infty)).subset ?_
      rintro _ ⟨y, rfl⟩
      have h : ∃ y' : fieldPt Qbar ⟶ S, geomComp y' = geomComp y := ⟨y, rfl⟩
      refine ⟨geomComp y, ⟨y, rfl⟩, ?_⟩
      simp only [dite_eq_left h]
      exact (hnc h.choose y h.choose_spec.symm).symm
    have hT : {t : Qbar | (OnePoint.some t) ∈
        Set.range fun y : fieldPt Qbar ⟶ S => σ.val (K := Qbar) y.left}.Finite :=
      hV.preimage (OnePoint.coe_injective.injOn)
    let r : Qbar → OnePoint Qbar := fun t =>
      if h : ∃ y : fieldPt Qbar ⟶ S, σ.val (K := Qbar) y.left = OnePoint.some t then
        ρ.val (K := Qbar) h.choose.left else OnePoint.infty
    obtain ⟨F, G, hcop, hFG⟩ := Mob.exists_interp hT.toFinset r
    refine ⟨F, G, hcop, fun y t hy => ?_⟩
    have hmem : t ∈ hT.toFinset := by
      rw [Set.Finite.mem_toFinset]; exact ⟨y, hy⟩
    have h : ∃ y : fieldPt Qbar ⟶ S, σ.val (K := Qbar) y.left = OnePoint.some t := ⟨y, hy⟩
    rw [hFG t hmem]
    simp only [r, dite_eq_left h]
    exact hfib y h.choose (hy.trans h.choose_spec.symm)

/-- **Both curve facts from (C1), (C2), (C3).** -/
theorem curveFacts_of_comp (h1 : GeomCompInfinite) (h2 : GeomCompConstOrOnto)
    (h3 : GeomCompRatFactor) : CurveRatFactor ∧ CurveSurj :=
  ⟨curveRatFactor_of_comp h2 h3, curveSurj_of_comp h1 h2⟩

/-! ## §6 (C1) from "no isolated points" -/

/-- **(C1a) A scheme smooth of relative dimension 1 over a field has no isolated point.**
Glue (STANDARD): every point of `X` has an open neighbourhood étale over `𝔸¹_K`, so every
irreducible component of `X` has dimension 1 and every nonempty open of `X` is infinite; an open
point would be a nonempty finite open. Stated for any field `K` and any `X` (the use below is
`X = S_ℚ̄`, `K = ℚ̄`). Not in Mathlib v4.35 (no dimension theory of smooth morphisms). -/
def SmoothCurveNoIsolatedPoint : Prop :=
  ∀ (K : Type) [Field K] (X : Scheme.{0}) (f : X ⟶ Spec (CommRingCat.of K)),
    SmoothOfRelativeDimension 1 f → ∀ x : X, ¬ IsOpen ({x} : Set X)

/-- In a Noetherian space, connected components are open. -/
theorem isOpen_connectedComponent_of_noetherian {α : Type*} [TopologicalSpace α]
    [TopologicalSpace.NoetherianSpace α] (x : α) : IsOpen (connectedComponent x) := by
  classical
  have hfin := TopologicalSpace.NoetherianSpace.finite_irreducibleComponents (α := α)
  have hc : (connectedComponent x)ᶜ =
      ⋃ Z ∈ {Z ∈ irreducibleComponents α | ¬ Z ⊆ connectedComponent x}, Z := by
    ext z
    simp only [Set.mem_compl_iff, Set.mem_iUnion, Set.mem_ofPred_eq, exists_prop]
    constructor
    · intro hz
      exact ⟨irreducibleComponent z, ⟨irreducibleComponent_mem_irreducibleComponents z,
        fun h => hz (h mem_irreducibleComponent)⟩, mem_irreducibleComponent⟩
    · rintro ⟨Z, ⟨hZ, hZC⟩, hzZ⟩ hzC
      apply hZC
      have : Z ⊆ connectedComponent z := hZ.1.isConnected.subset_connectedComponent hzZ
      rwa [← connectedComponent_eq hzC] at this
  rw [← isClosed_compl_iff, hc]
  exact (hfin.subset fun Z hZ => hZ.1).isClosed_biUnion fun Z hZ =>
    isClosed_of_mem_irreducibleComponents Z hZ.1

/-- In a Jacobson space, a nonempty open set with finitely many closed points contains an open
point. -/
theorem exists_isOpen_singleton_of_finite_closedPoints {α : Type*} [TopologicalSpace α]
    [JacobsonSpace α] {U : Set α} (hU : IsOpen U) (hne : U.Nonempty)
    (hfin : (U ∩ closedPoints α).Finite) : ∃ z, IsOpen ({z} : Set α) := by
  classical
  set F := U ∩ closedPoints α with hF
  have hclosed : ∀ G ⊆ F, IsClosed G := by
    intro G hG
    rw [← G.biUnion_of_singleton]
    exact (hfin.subset hG).isClosed_biUnion fun w hw => mem_closedPoints_iff.mp (hG hw).2
  have hFc : IsClosed F := hclosed F le_rfl
  -- `U ⊆ F`: otherwise `U \ F` is a nonempty open with no closed point
  have hUF : U ⊆ F := by
    by_contra hsub
    obtain ⟨z, hzU, hzF⟩ := Set.not_subset.mp hsub
    obtain ⟨w, ⟨hwU, hwF⟩, hwc⟩ := nonempty_inter_closedPoints (Z := U ∩ Fᶜ)
      ⟨z, hzU, hzF⟩ (hU.inter hFc.isOpen_compl).isLocallyClosed
    exact hwF ⟨hwU, hwc⟩
  obtain ⟨z, hz⟩ := hne
  refine ⟨z, ?_⟩
  have hrest : IsClosed (F \ {z}) := hclosed _ Set.sdiff_subset
  have : ({z} : Set α) = U ∩ (F \ {z})ᶜ := by
    ext w
    simp only [Set.mem_singleton_iff, Set.mem_inter_iff, Set.mem_compl_iff, Set.mem_sdiff,
      not_and, not_not]
    constructor
    · rintro rfl; exact ⟨hz, fun _ => rfl⟩
    · rintro ⟨hwU, h⟩; exact h (hUF hwU)
  rw [this]; exact hU.inter hrest.isOpen_compl

/-- **(C1) from (C1a).** -/
theorem geomCompInfinite_of (h : SmoothCurveNoIsolatedPoint) : GeomCompInfinite := by
  intro S hP hS y₀
  classical
  let f : bcQbar S ⟶ Spec (CommRingCat.of Qbar) :=
    pullback.snd S.hom (Spec.map (CommRingCat.ofHom (algebraMap ℚ Qbar)))
  have : IsNoetherian (bcQbar S) := { }
  have : LocallyOfFiniteType f := by
    show LocallyOfFiniteType (pullback.snd _ _); infer_instance
  have hsm : SmoothOfRelativeDimension 1 f := by
    show SmoothOfRelativeDimension 1 (pullback.snd _ _); infer_instance
  have : JacobsonSpace (bcQbar S) := LocallyOfFiniteType.jacobsonSpace f
  set x₀ := (Scheme.SpecToEquivOfField Qbar (bcQbar S) (bcPt y₀)).1 with hx₀
  -- the closed points of the component of `x₀` are infinitely many
  have hCinf : (connectedComponent x₀ ∩ closedPoints (bcQbar S)).Infinite := by
    intro hfin
    obtain ⟨z, hz⟩ := exists_isOpen_singleton_of_finite_closedPoints
      (isOpen_connectedComponent_of_noetherian x₀) ⟨x₀, mem_connectedComponent⟩ hfin
    exact h Qbar (bcQbar S) f hsm z hz
  -- each of them comes from a `ℚ̄`-point of `S` in the component
  intro hfin
  apply hCinf
  refine (hfin.image fun y => (Scheme.SpecToEquivOfField Qbar (bcQbar S) (bcPt y)).1).subset ?_
  rintro x ⟨hxC, hxc⟩
  let p : Spec (CommRingCat.of Qbar) ⟶ bcQbar S := pointOfClosedPoint f x hxc
  have hp : p ≫ f = 𝟙 _ := pointOfClosedPoint_comp f x hxc
  let y : fieldPt Qbar ⟶ S := Over.homMk (p ≫ pullback.fst _ _) (by
    change (p ≫ pullback.fst _ _) ≫ S.hom = Spec.map (CommRingCat.ofHom (algebraMap ℚ Qbar))
    rw [Category.assoc, pullback.condition, ← Category.assoc]
    change (p ≫ f) ≫ _ = _
    rw [hp, Category.id_comp])
  have hy : bcPt y = p := by
    apply pullback.hom_ext
    · exact pullback.lift_fst _ _ _
    · exact (pullback.lift_snd _ _ _).trans hp.symm
  have hpt : (Scheme.SpecToEquivOfField Qbar (bcQbar S) (bcPt y)).1 = x := by
    rw [hy]; exact pointOfClosedPoint_apply f x hxc _
  refine ⟨y, ?_, hpt⟩
  show geomComp y = geomComp y₀
  unfold geomComp
  rw [hpt, ← hx₀]
  exact (connectedComponent_eq hxC).symm

/-- **Both curve facts from (C1a), (C2), (C3).** -/
theorem curveFacts_of_named (h1 : SmoothCurveNoIsolatedPoint) (h2 : GeomCompConstOrOnto)
    (h3 : GeomCompRatFactor) : CurveRatFactor ∧ CurveSurj :=
  curveFacts_of_comp (geomCompInfinite_of h1) h2 h3

/-! ## §7 C2 and C3 over an algebraically closed field (Hartshorne's setting)

The leaves C2 and C3 are restated for a proper smooth curve `X` over an arbitrary algebraically
closed field `K`, its `K`-points (sections `p : Spec K → X` of the structure map) and a connected
component of `X`. `GeomCompConstOrOnto` and `GeomCompRatFactor` follow by base change to `ℚ̄`. -/

/-- The point of `X` at which a field point `p : Spec K → X` sits. -/
abbrev ptOf {K : Type} [Field K] {X : Scheme.{0}} (p : Spec (CommRingCat.of K) ⟶ X) : X :=
  (Scheme.SpecToEquivOfField K X p).1

/-- **(C2K) Constant or onto on a connected component** (Hartshorne, *Algebraic Geometry*,
Prop. II.6.8, UNVERIFIED numbering: a morphism from a complete nonsingular curve over an
algebraically closed field to a curve is constant or surjective; here applied to a connected
component of `X`, a complete nonsingular irreducible curve, and the target `P¹`, whose closed
points are its `K`-points). Textbook leaf. -/
def ConstOrOntoAlgClosed : Prop :=
  ∀ (K : Type) [Field K] [IsAlgClosed K] (X : Scheme.{0}) (f : X ⟶ Spec (CommRingCat.of K)),
    IsProper f → SmoothOfRelativeDimension 1 f →
    ∀ (σ : ToP1 X) (p₀ : Spec (CommRingCat.of K) ⟶ X), p₀ ≫ f = 𝟙 _ →
      (∀ p : Spec (CommRingCat.of K) ⟶ X, p ≫ f = 𝟙 _ →
        connectedComponent (ptOf p) = connectedComponent (ptOf p₀) → σ.val p = σ.val p₀) ∨
      (∀ t : OnePoint K, ∃ p : Spec (CommRingCat.of K) ⟶ X, p ≫ f = 𝟙 _ ∧
        connectedComponent (ptOf p) = connectedComponent (ptOf p₀) ∧ σ.val p = t)

open Polynomial in
/-- **(C3K) Factorization on a connected component where `σ` is nonconstant**, over an
algebraically closed field of characteristic 0 (in characteristic `p` the Frobenius
`σ = ρ^p` is a counterexample). Glue (a standard consequence of textbook results, see
`docs/research/curve-facts.md` §3). -/
def RatFactorAlgClosed : Prop :=
  ∀ (K : Type) [Field K] [IsAlgClosed K] [CharZero K] (X : Scheme.{0})
    (f : X ⟶ Spec (CommRingCat.of K)), IsProper f → SmoothOfRelativeDimension 1 f →
    ∀ (σ ρ : ToP1 X) (p₀ : Spec (CommRingCat.of K) ⟶ X), p₀ ≫ f = 𝟙 _ →
      (∃ p : Spec (CommRingCat.of K) ⟶ X, p ≫ f = 𝟙 _ ∧
        connectedComponent (ptOf p) = connectedComponent (ptOf p₀) ∧ σ.val p ≠ σ.val p₀) →
      (∀ p₁ p₂ : Spec (CommRingCat.of K) ⟶ X, p₁ ≫ f = 𝟙 _ → p₂ ≫ f = 𝟙 _ →
        connectedComponent (ptOf p₁) = connectedComponent (ptOf p₀) →
        connectedComponent (ptOf p₂) = connectedComponent (ptOf p₀) →
        σ.val p₁ = σ.val p₂ → ρ.val p₁ = ρ.val p₂) →
      ∃ F G : K[X], IsCoprime F G ∧ ∀ p : Spec (CommRingCat.of K) ⟶ X, p ≫ f = 𝟙 _ →
        connectedComponent (ptOf p) = connectedComponent (ptOf p₀) → ∀ t : K,
        σ.val p = OnePoint.some t → ρ.val p = Mob.ratEval F G t

section Dictionary

variable {S : Over (Spec (CommRingCat.of ℚ))}

/-- The structure map `S_ℚ̄ → Spec ℚ̄`. -/
abbrev bcSnd (S : Over (Spec (CommRingCat.of ℚ))) : bcQbar S ⟶ Spec (CommRingCat.of Qbar) :=
  pullback.snd S.hom (Spec.map (CommRingCat.ofHom (algebraMap ℚ Qbar)))

theorem bcPt_snd (y : fieldPt Qbar ⟶ S) : bcPt y ≫ bcSnd S = 𝟙 _ :=
  pullback.lift_snd _ _ _

/-- The `ℚ̄`-point of `S` over `ℚ` underlying a section of `S_ℚ̄ → Spec ℚ̄`. -/
def ptOfSection (p : Spec (CommRingCat.of Qbar) ⟶ bcQbar S) (hp : p ≫ bcSnd S = 𝟙 _) :
    fieldPt Qbar ⟶ S :=
  Over.homMk (p ≫ pullback.fst _ _) (by
    change (p ≫ pullback.fst _ _) ≫ S.hom = Spec.map (CommRingCat.ofHom (algebraMap ℚ Qbar))
    rw [Category.assoc, pullback.condition, ← Category.assoc]
    change (p ≫ bcSnd S) ≫ _ = _
    rw [hp, Category.id_comp])

theorem bcPt_ptOfSection (p : Spec (CommRingCat.of Qbar) ⟶ bcQbar S) (hp : p ≫ bcSnd S = 𝟙 _) :
    bcPt (ptOfSection p hp) = p := by
  apply pullback.hom_ext
  · exact pullback.lift_fst _ _ _
  · exact (pullback.lift_snd _ _ _).trans hp.symm

/-- `σ(y) = (σ ∘ pr₁)(bcPt y)`. -/
theorem val_bcPt (σ : ToP1 S.left) (y : fieldPt Qbar ⟶ S) :
    (σ.comp (pullback.fst _ _)).val (bcPt y) = σ.val (K := Qbar) y.left := by
  rw [ToP1.val_comp_right]
  exact congrArg _ (pullback.lift_fst _ _ _)

end Dictionary

/-- **C2 from C2K.** -/
theorem geomCompConstOrOnto_of (h : ConstOrOntoAlgClosed) : GeomCompConstOrOnto := by
  intro S hP hS σ y₀
  have hPf : IsProper (bcSnd S) := inferInstance
  have hSf : SmoothOfRelativeDimension 1 (bcSnd S) := inferInstance
  rcases h Qbar (bcQbar S) (bcSnd S) hPf hSf (σ.comp (pullback.fst _ _)) (bcPt y₀)
    (bcPt_snd y₀) with hc | ho
  · left
    intro y hy
    rw [← val_bcPt, ← val_bcPt]
    exact hc (bcPt y) (bcPt_snd y) hy
  · right
    intro t
    obtain ⟨p, hp, hcc, hv⟩ := ho t
    refine ⟨ptOfSection p hp, ?_, ?_⟩
    · show connectedComponent (ptOf (bcPt (ptOfSection p hp))) = _
      rw [bcPt_ptOfSection]; exact hcc
    · rw [← val_bcPt, bcPt_ptOfSection]; exact hv

/-- **C3 from C3K.** -/
theorem geomCompRatFactor_of (h : RatFactorAlgClosed) : GeomCompRatFactor := by
  intro S hP hS σ ρ y₀ hne hfib
  have hPf : IsProper (bcSnd S) := inferInstance
  have hSf : SmoothOfRelativeDimension 1 (bcSnd S) := inferInstance
  have hcc : ∀ (p : Spec (CommRingCat.of Qbar) ⟶ bcQbar S) (hp : p ≫ bcSnd S = 𝟙 _),
      geomComp (ptOfSection p hp) = connectedComponent (ptOf p) := by
    intro p hp
    show connectedComponent (ptOf (bcPt (ptOfSection p hp))) = _
    rw [bcPt_ptOfSection]
  obtain ⟨F, G, hcop, hR⟩ := h Qbar (bcQbar S) (bcSnd S) hPf hSf (σ.comp (pullback.fst _ _))
    (ρ.comp (pullback.fst _ _)) (bcPt y₀) (bcPt_snd y₀) (by
      obtain ⟨y, hy, hv⟩ := hne
      refine ⟨bcPt y, bcPt_snd y, hy, ?_⟩
      rw [val_bcPt, val_bcPt]; exact hv) (by
      intro p₁ p₂ hp₁ hp₂ h₁ h₂ hv
      have e₁ := val_bcPt σ (ptOfSection p₁ hp₁)
      have e₂ := val_bcPt σ (ptOfSection p₂ hp₂)
      have f₁ := val_bcPt ρ (ptOfSection p₁ hp₁)
      have f₂ := val_bcPt ρ (ptOfSection p₂ hp₂)
      rw [bcPt_ptOfSection] at e₁ e₂ f₁ f₂
      rw [f₁, f₂]
      refine hfib _ _ ((hcc p₁ hp₁).trans h₁) ((hcc p₂ hp₂).trans h₂) ?_
      rw [← e₁, ← e₂]; exact hv)
  refine ⟨F, G, hcop, fun y t hy ht => ?_⟩
  rw [← val_bcPt] at ht ⊢
  exact hR (bcPt y) (bcPt_snd y) hy t ht

/-- **Both curve facts from C1a, C2K, C3K** (the leaves in Hartshorne's setting). -/
theorem curveFacts_of_algClosed (h1 : SmoothCurveNoIsolatedPoint) (h2 : ConstOrOntoAlgClosed)
    (h3 : RatFactorAlgClosed) : CurveRatFactor ∧ CurveSurj :=
  curveFacts_of_named h1 (geomCompConstOrOnto_of h2) (geomCompRatFactor_of h3)

/-! ## §8 C1a from the dimension of local rings at closed points -/

/-- **(C1b) Local rings of a smooth curve at closed points have dimension 1.** If `X → Spec K`
is smooth of relative dimension 1 over a field `K` and `x` is a closed point, then
`dim 𝒪_{X,x} = 1` (STANDARD: smooth of relative dimension `n` over a field means `dim_x X = n`
at every point, and at a closed point of a scheme locally of finite type over a field
`dim 𝒪_{X,x} = dim_x X`; e.g. Stacks, *Morphisms*, smooth morphisms and dimension of fibres,
UNVERIFIED tags). Glue (dimension theory), not in Mathlib v4.35; Mathlib has
`ringKrullDim_stalk_eq_coheight` (Stacks 02IZ), used below. -/
def SmoothStalkDimOne : Prop :=
  ∀ (K : Type) [Field K] (X : Scheme.{0}) (f : X ⟶ Spec (CommRingCat.of K)),
    SmoothOfRelativeDimension 1 f → ∀ x : X, IsClosed ({x} : Set X) →
      ringKrullDim (X.presheaf.stalk x) = 1

/-- **C1a from C1b.** An open point is closed (Jacobson) and has no proper generalization, so its
local ring has dimension `coheight x = 0`. -/
theorem smoothCurveNoIsolatedPoint_of (h : SmoothStalkDimOne) : SmoothCurveNoIsolatedPoint := by
  intro K _ X f hf x hx
  have : Smooth f := hf.smooth
  have : LocallyOfFiniteType f := inferInstance
  have : JacobsonSpace X := LocallyOfFiniteType.jacobsonSpace f
  have hc : IsClosed ({x} : Set X) := isClosed_singleton_of_isLocallyClosed_singleton hx.isLocallyClosed
  have hd := h K X f hf x hc
  rw [ringKrullDim_stalk_eq_coheight] at hd
  have hmax : IsMax x := by
    intro y hxy
    have hyx : y ⤳ x := hxy
    have : y ∈ ({x} : Set X) := hyx.mem_open hx rfl
    rw [Set.mem_singleton_iff.mp this]
  rw [Order.coheight_eq_zero.mpr hmax] at hd
  exact absurd hd (by decide)

/-- **Both curve facts from C1b, C2K, C3K.** -/
theorem curveFacts_of_leaves (h1 : SmoothStalkDimOne) (h2 : ConstOrOntoAlgClosed)
    (h3 : RatFactorAlgClosed) : CurveRatFactor ∧ CurveSurj :=
  curveFacts_of_algClosed (smoothCurveNoIsolatedPoint_of h1) h2 h3


/-! # curve-glue additions (task curve-glue, 2026-11-13)

Everything above is `scratch/curve-facts/CurveFacts.lean` verbatim (its `#print axioms` lines
dropped). Below: `scratch/curve-glue/C2K.lean` §1-§4 (C2K from the leaf `GlobalFunctionsConst`)
and `scratch/curve-glue/C3K.lean` §1-§2 (C3K from the glue `ImagePlaneCurve`, or from C2K and
`ImagePlaneCurveClosed`, and Lean-proved algebra), then the composites. -/

open Opposite TopologicalSpace

/-! ## §1 Values of sections at `K`-points -/

section Ev

variable {K : Type} [Field K] {X : Scheme.{0}}

/-- Restriction of sections along `O' ≤ O`, as a ring hom. -/
abbrev res {O O' : X.Opens} (h : O' ≤ O) : Γ(X, O) →+* Γ(X, O') :=
  (X.presheaf.map (homOfLE h).op).hom

theorem res_res {O O' O'' : X.Opens} (h : O' ≤ O) (h' : O'' ≤ O') (s : Γ(X, O)) :
    res h' (res h s) = res (h'.trans h) s := by
  simp only [res, ← ConcreteCategory.comp_apply, ← Functor.map_comp]
  rfl

/-- The value `s(p) ∈ K` of a section `s ∈ Γ(X, O)` at a field point `p` whose point lies in `O`
(the image of `s(x) ∈ κ(x)` under the embedding `κ(x) → K` of `p`; this is how `ToP1.val`
evaluates). -/
def ev (p : Spec (CommRingCat.of K) ⟶ X) {O : X.Opens} (hx : ptOf p ∈ O) : Γ(X, O) →+* K :=
  (X.evaluation O (ptOf p) hx ≫ (Scheme.SpecToEquivOfField K X p).2).hom

theorem ev_res (p : Spec (CommRingCat.of K) ⟶ X) {O O' : X.Opens} (h : O' ≤ O)
    (hx : ptOf p ∈ O') (s : Γ(X, O)) : ev p hx (res h s) = ev p (h hx) s := by
  simp only [ev, res, CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply]
  congr 1
  simp only [Scheme.evaluation, CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply]
  rw [← ConcreteCategory.comp_apply (X.presheaf.map _), TopCat.Presheaf.germ_res]

theorem ev_eq_zero_iff (p : Spec (CommRingCat.of K) ⟶ X) {O : X.Opens} (hx : ptOf p ∈ O)
    (s : Γ(X, O)) : ev p hx s = 0 ↔ ptOf p ∉ X.basicOpen s := by
  rw [← X.evaluation_eq_zero_iff_notMem_basicOpen (ptOf p) hx s]
  simp only [ev, CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply]
  exact map_eq_zero_iff _ (Scheme.SpecToEquivOfField K X p).2.hom.injective

theorem ev_top (p : Spec (CommRingCat.of K) ⟶ X) (s : Γ(X, ⊤)) :
    ev p (show ptOf p ∈ (⊤ : X.Opens) from trivial) s =
      (Scheme.ΓSpecIso (CommRingCat.of K)).hom (p.appTop s) := by
  have e := Scheme.germ_stalkClosedPointTo p ⊤ trivial
  have e' := congrArg (fun φ => φ.hom s) e
  simp only [CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply] at e'
  simp only [ev, Scheme.evaluation, CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply]
  change (X.residue _ ≫ X.descResidueField (Scheme.stalkClosedPointTo p)).hom
    ((X.presheaf.germ ⊤ _ trivial).hom s) = _
  rw [Scheme.residue_descResidueField, e']
  simp only [Iso.trans_hom, Functor.mapIso_hom, Iso.op_hom, eqToIso.hom, eqToHom_op, eqToHom_map,
    Scheme.Hom.appTop]
  rfl

/-- The constant section `a ∈ K` on `O`, through the structure morphism `f : X → Spec K`. -/
def cst (f : X ⟶ Spec (CommRingCat.of K)) (O : X.Opens) (a : K) : Γ(X, O) :=
  res le_top (f.appTop ((Scheme.ΓSpecIso (CommRingCat.of K)).inv a))

theorem ev_cst (f : X ⟶ Spec (CommRingCat.of K)) (p : Spec (CommRingCat.of K) ⟶ X)
    (hp : p ≫ f = 𝟙 _) {O : X.Opens} (hx : ptOf p ∈ O) (a : K) : ev p hx (cst f O a) = a := by
  rw [cst, ev_res, ev_top]
  have h1 : p.appTop (f.appTop ((Scheme.ΓSpecIso (CommRingCat.of K)).inv a)) =
      (Scheme.ΓSpecIso (CommRingCat.of K)).inv a := by
    rw [← ConcreteCategory.comp_apply, ← Scheme.Hom.comp_appTop, hp, Scheme.Hom.id_appTop]; rfl
  rw [h1]; simp

end Ev

/-! ## §2 Closed points are `K`-points; units by values -/

section Units

variable {K : Type} [Field K] [IsAlgClosed K] {X : Scheme.{0}} (f : X ⟶ Spec (CommRingCat.of K))
  [LocallyOfFiniteType f] [JacobsonSpace X]

theorem exists_point_of_isLocallyClosed {Z : Set X} (hZ : IsLocallyClosed Z) (hne : Z.Nonempty) :
    ∃ p : Spec (CommRingCat.of K) ⟶ X, p ≫ f = 𝟙 _ ∧ ptOf p ∈ Z := by
  obtain ⟨y, hyZ, hyc⟩ := nonempty_inter_closedPoints hne hZ
  have hy : IsClosed ({y} : Set X) := mem_closedPoints_iff.mp hyc
  refine ⟨pointOfClosedPoint f y hy, pointOfClosedPoint_comp f y hy, ?_⟩
  have e : ptOf (pointOfClosedPoint f y hy) = y := pointOfClosedPoint_apply f y hy _
  rw [e]; exact hyZ

/-- A section whose value at every `K`-point of its domain is nonzero is a unit (Jacobson). -/
theorem isUnit_of_ev_ne_zero {O : X.Opens} (s : Γ(X, O))
    (h : ∀ p : Spec (CommRingCat.of K) ⟶ X, p ≫ f = 𝟙 _ → ∀ hx : ptOf p ∈ O, ev p hx s ≠ 0) :
    IsUnit s := by
  refine X.toRingedSpace.isUnit_of_isUnit_germ O s fun x hx => ?_
  rw [← X.mem_basicOpen s x hx]
  by_contra hb
  obtain ⟨p, hp, hpO, hpb⟩ := exists_point_of_isLocallyClosed f
    (Z := (O : Set X) ∩ (X.basicOpen s : Set X)ᶜ)
    (O.isOpen.isLocallyClosed.inter (X.basicOpen s).isOpen.isClosed_compl.isLocallyClosed)
    ⟨x, hx, hb⟩
  exact h p hp hpO ((ev_eq_zero_iff p hpO s).2 hpb)

end Units

/-! ## §3 The leaf: global functions on a connected component are constant -/

/-- **(L) "Liouville": regular functions on a connected component of a proper smooth curve over
an algebraically closed field are constant** (up to nilpotents, which is weaker than the printed
statement). `X → Spec K` proper and smooth of relative dimension 1, `K` algebraically closed,
`W ⊆ X` open, closed and (pre)connected, `s ∈ Γ(W, 𝒪_X)`: then `s − c` is nilpotent for some
constant `c ∈ K` (the image of `c` under `K = Γ(Spec K) → Γ(X) → Γ(W)`).

Source (textbook leaf, STANDARD; numbering UNVERIFIED, recalled without network): `W` is a
proper connected `K`-scheme (an open and closed subscheme of a proper one), so `Γ(W, 𝒪_W)` is a
finite-dimensional `K`-algebra (finiteness of coherent cohomology for proper morphisms, EGA III
3.2.1; Hartshorne III.5.2 in the projective case) without nontrivial idempotents (`W`
connected), hence local Artinian with residue field `K` (`K` algebraically closed): every element
is a constant plus a nilpotent. With `W` reduced (smooth ⇒ reduced) this is the printed form
"`Γ(W, 𝒪_W) = K` for `W` proper, connected and reduced over `K = K̄`" (Stacks, Varieties, lemma
on `Γ` of a proper reduced connected scheme; Hartshorne Ex. II.4.5(d) for integral `W`; I.3.4
for projective varieties). Smoothness and dimension 1 are not needed; they are kept so that the
leaf is applied exactly where C2K is. Not in Mathlib v4.35 (no finiteness theorem for proper
morphisms). -/
def GlobalFunctionsConst : Prop :=
  ∀ (K : Type) [Field K] [IsAlgClosed K] (X : Scheme.{0}) (f : X ⟶ Spec (CommRingCat.of K)),
    IsProper f → SmoothOfRelativeDimension 1 f →
    ∀ W : X.Opens, IsClopen (W : Set X) → _root_.IsPreconnected (W : Set X) →
      ∀ s : Γ(X, W), ∃ c : K, IsNilpotent (s - cst f W c)

section Main

variable {K : Type} [Field K] {X : Scheme.{0}}

theorem ev_eq_of_nilpotent (f : X ⟶ Spec (CommRingCat.of K)) {W : X.Opens} {s : Γ(X, W)} {c : K}
    (hN : IsNilpotent (s - cst f W c)) (p : Spec (CommRingCat.of K) ⟶ X) (hp : p ≫ f = 𝟙 _)
    (hx : ptOf p ∈ W) : ev p hx s = c := by
  have h0 := (hN.map (ev p hx)).eq_zero
  rw [map_sub, ev_cst f p hp] at h0
  exact sub_eq_zero.mp h0

theorem res_cst (f : X ⟶ Spec (CommRingCat.of K)) {O O' : X.Opens} (h : O' ≤ O) (a : K) :
    res h (cst f O a) = cst f O' a := by
  rw [cst, cst, res_res]

theorem val_of_mem (σ : ToP1 X) (p : Spec (CommRingCat.of K) ⟶ X) (h : ptOf p ∈ σ.U) :
    σ.val p = OnePoint.some (ev p h σ.f) := by
  unfold ToP1.val
  split_ifs with h'
  · rfl
  · exact absurd h h'

theorem val_of_not_mem (σ : ToP1 X) (p : Spec (CommRingCat.of K) ⟶ X) (h : ptOf p ∉ σ.U) :
    σ.val p = OnePoint.infty := by
  unfold ToP1.val
  split_ifs with h'
  · exact absurd h' h
  · rfl

theorem ev_f_mul_g (σ : ToP1 X) (p : Spec (CommRingCat.of K) ⟶ X) (hU : ptOf p ∈ σ.U)
    (hV : ptOf p ∈ σ.V) : ev p hU σ.f * ev p hV σ.g = 1 := by
  have e := congrArg (ev p (show ptOf p ∈ σ.U ⊓ σ.V from ⟨hU, hV⟩)) σ.inv
  rw [map_mul, map_one] at e
  rw [← ev_res p (inf_le_left : σ.U ⊓ σ.V ≤ σ.U) ⟨hU, hV⟩,
    ← ev_res p (inf_le_right : σ.U ⊓ σ.V ≤ σ.V) ⟨hU, hV⟩]
  exact e

theorem ev_g_eq_zero (σ : ToP1 X) (p : Spec (CommRingCat.of K) ⟶ X) (hV : ptOf p ∈ σ.V)
    (hU : ptOf p ∉ σ.U) : ev p hV σ.g = 0 := by
  rw [ev_eq_zero_iff, σ.basicOpen_g]
  exact fun h => hU h.1

theorem mem_V_of_not_mem_U (σ : ToP1 X) {x : X} (hU : x ∉ σ.U) : x ∈ σ.V := by
  have hx : x ∈ (σ.U ⊔ σ.V : X.Opens) := by rw [σ.cover]; trivial
  rcases hx with h | h
  · exact absurd h hU
  · exact h

end Main

/-! ## §4 C2K from the leaf (L) -/

/-- **The missed-value lemma.** If `σ` misses a value `t ∈ P¹(K)` on the `K`-points of a
connected component `W`, it is constant on them. For `t = ∞`, `W ⊆ U` (Jacobson) and `f|_W` is
constant by (L). For `t = a ∈ K`, `f − a` is a unit on `W ∩ U` and `1 − a g` on `W ∩ V`, and
`1/(f − a)`, `g/(1 − a g)` glue to `h ∈ Γ(W)`, constant `= c` by (L); `c ≠ 0` if `W ∩ U` has a
`K`-point, which forces `W ⊆ U` (`g = 0` off `U`) and `σ = a + 1/c` on `W`. -/
theorem constant_of_missed (hL : GlobalFunctionsConst) {K : Type} [Field K] [IsAlgClosed K]
    {X : Scheme.{0}} (f : X ⟶ Spec (CommRingCat.of K)) (hP : IsProper f)
    (hS : SmoothOfRelativeDimension 1 f) [JacobsonSpace X] (σ : ToP1 X) (W : X.Opens)
    (hWc : IsClopen (W : Set X)) (hWp : _root_.IsPreconnected (W : Set X)) (t : OnePoint K)
    (ht : ∀ p : Spec (CommRingCat.of K) ⟶ X, p ≫ f = 𝟙 _ → ptOf p ∈ W → σ.val p ≠ t) :
    ∃ v : OnePoint K, ∀ p : Spec (CommRingCat.of K) ⟶ X, p ≫ f = 𝟙 _ → ptOf p ∈ W →
      σ.val p = v := by
  have : LocallyOfFiniteType f := inferInstance
  induction t using OnePoint.rec with
  | infty =>
    have hWU : ∀ p : Spec (CommRingCat.of K) ⟶ X, p ≫ f = 𝟙 _ → ptOf p ∈ W → ptOf p ∈ σ.U :=
      fun p hp hW => by
        by_contra h
        exact ht p hp hW (val_of_not_mem σ p h)
    have hle : W ≤ σ.U := by
      intro x hx
      by_contra hxU
      obtain ⟨p, hp, hpW, hpU⟩ := exists_point_of_isLocallyClosed f
        (Z := (W : Set X) ∩ (σ.U : Set X)ᶜ)
        (W.isOpen.isLocallyClosed.inter σ.U.isOpen.isClosed_compl.isLocallyClosed) ⟨x, hx, hxU⟩
      exact hpU (hWU p hp hpW)
    obtain ⟨c, hc⟩ := hL K X f hP hS W hWc hWp (res hle σ.f)
    refine ⟨OnePoint.some c, fun p hp hpW => ?_⟩
    rw [val_of_mem σ p (hle hpW), ← ev_res p hle hpW, ev_eq_of_nilpotent f hc p hp hpW]
  | coe a =>
    have hmiss : ∀ p : Spec (CommRingCat.of K) ⟶ X, p ≫ f = 𝟙 _ → ∀ (hW : ptOf p ∈ W)
        (hU : ptOf p ∈ σ.U), ev p hU σ.f ≠ a := fun p hp hW hU e =>
      ht p hp hW (by rw [val_of_mem σ p hU, e])
    let O₁ : X.Opens := W ⊓ σ.U
    let O₂ : X.Opens := W ⊓ σ.V
    let u₁ : Γ(X, O₁) := res inf_le_right σ.f - cst f O₁ a
    let u₂ : Γ(X, O₂) := 1 - cst f O₂ a * res inf_le_right σ.g
    have hu₁ev : ∀ p : Spec (CommRingCat.of K) ⟶ X, p ≫ f = 𝟙 _ → ∀ hx : ptOf p ∈ O₁,
        ev p hx u₁ = ev p hx.2 σ.f - a := by
      intro p hp hx
      simp only [u₁, map_sub, ev_res, ev_cst f p hp]
    have hu₂ev : ∀ p : Spec (CommRingCat.of K) ⟶ X, p ≫ f = 𝟙 _ → ∀ hx : ptOf p ∈ O₂,
        ev p hx u₂ = 1 - a * ev p hx.2 σ.g := by
      intro p hp hx
      simp only [u₂, map_sub, map_one, map_mul, ev_res, ev_cst f p hp]
    have hu₁ : IsUnit u₁ := isUnit_of_ev_ne_zero f u₁ fun p hp hx => by
      rw [hu₁ev p hp hx]
      exact sub_ne_zero.mpr (hmiss p hp hx.1 hx.2)
    have hu₂ : IsUnit u₂ := isUnit_of_ev_ne_zero f u₂ fun p hp hx => by
      rw [hu₂ev p hp hx]
      by_cases hU : ptOf p ∈ σ.U
      · have e := ev_f_mul_g σ p hU hx.2
        have hne := hmiss p hp hx.1 hU
        intro h0
        have h1 : ev p hx.2 σ.g * (ev p hU σ.f - a) = 0 := by linear_combination h0 + e
        rcases mul_eq_zero.mp h1 with h | h
        · rw [h, mul_zero] at e; exact zero_ne_one e
        · exact hne (sub_eq_zero.mp h)
      · rw [ev_g_eq_zero σ p hx.2 hU, mul_zero, sub_zero]; exact one_ne_zero
    obtain ⟨i₁, hi₁⟩ := hu₁.exists_left_inv
    obtain ⟨i₂, hi₂⟩ := hu₂.exists_left_inv
    let s₂ : Γ(X, O₂) := res inf_le_right σ.g * i₂
    have hfg : res (show O₁ ⊓ O₂ ≤ σ.U from fun x hx => hx.1.2) σ.f *
        res (show O₁ ⊓ O₂ ≤ σ.V from fun x hx => hx.2.2) σ.g = 1 := by
      have e := congrArg (res (show O₁ ⊓ O₂ ≤ σ.U ⊓ σ.V from fun x hx => ⟨hx.1.2, hx.2.2⟩)) σ.inv
      rw [map_mul, map_one] at e
      rw [← e]
      simp only [res_res]
    have hcomp : res (inf_le_left : O₁ ⊓ O₂ ≤ O₁) i₁ = res (inf_le_right : O₁ ⊓ O₂ ≤ O₂) s₂ := by
      have A : res (inf_le_left : O₁ ⊓ O₂ ≤ O₁) i₁ * res (inf_le_left : O₁ ⊓ O₂ ≤ O₁) u₁ = 1 := by
        rw [← map_mul, hi₁, map_one]
      have C : res (inf_le_right : O₁ ⊓ O₂ ≤ O₂) i₂ * res (inf_le_right : O₁ ⊓ O₂ ≤ O₂) u₂ = 1 := by
        rw [← map_mul, hi₂, map_one]
      have B : res (inf_le_right : O₁ ⊓ O₂ ≤ O₂) s₂ * res (inf_le_left : O₁ ⊓ O₂ ≤ O₁) u₁ = 1 := by
        simp only [s₂, u₁, u₂, map_mul, map_sub, map_one, res_res, res_cst] at C hfg ⊢
        linear_combination C + res (inf_le_right : O₁ ⊓ O₂ ≤ O₂) i₂ * hfg
      calc res (inf_le_left : O₁ ⊓ O₂ ≤ O₁) i₁
          = res (inf_le_left : O₁ ⊓ O₂ ≤ O₁) i₁ *
              (res (inf_le_right : O₁ ⊓ O₂ ≤ O₂) s₂ * res (inf_le_left : O₁ ⊓ O₂ ≤ O₁) u₁) := by
            rw [B, mul_one]
        _ = res (inf_le_right : O₁ ⊓ O₂ ≤ O₂) s₂ *
              (res (inf_le_left : O₁ ⊓ O₂ ≤ O₁) i₁ * res (inf_le_left : O₁ ⊓ O₂ ≤ O₁) u₁) := by
            ring
        _ = res (inf_le_right : O₁ ⊓ O₂ ≤ O₂) s₂ := by rw [A, mul_one]
    -- glue `i₁` and `s₂` to a section on `O₁ ⊔ O₂`
    let h : Γ(X, O₁ ⊔ O₂) := (X.sheaf.objSupIsoProdEqLocus O₁ O₂).inv ⟨(i₁, s₂), hcomp⟩
    have hh₁ : res (le_sup_left : O₁ ≤ O₁ ⊔ O₂) h = i₁ :=
      X.sheaf.objSupIsoProdEqLocus_inv_fst O₁ O₂ _
    have hh₂ : res (le_sup_right : O₂ ≤ O₁ ⊔ O₂) h = s₂ :=
      X.sheaf.objSupIsoProdEqLocus_inv_snd O₁ O₂ _
    have hW'eq : ((O₁ ⊔ O₂ : X.Opens) : Set X) = W := by
      ext x
      simp only [O₁, O₂, Opens.coe_sup, Opens.coe_inf, Set.mem_union, Set.mem_inter_iff,
        SetLike.mem_coe]
      constructor
      · rintro (⟨hx, -⟩ | ⟨hx, -⟩) <;> exact hx
      · intro hx
        by_cases hU : x ∈ σ.U
        · exact Or.inl ⟨hx, hU⟩
        · exact Or.inr ⟨hx, mem_V_of_not_mem_U σ hU⟩
    obtain ⟨c, hc⟩ := hL K X f hP hS (O₁ ⊔ O₂) (hW'eq ▸ hWc) (hW'eq ▸ hWp) h
    have hv₁ : ∀ p : Spec (CommRingCat.of K) ⟶ X, p ≫ f = 𝟙 _ → ∀ hx : ptOf p ∈ O₁,
        ev p hx i₁ = c := by
      intro p hp hx
      rw [← hh₁, ev_res]; exact ev_eq_of_nilpotent f hc p hp _
    have hv₂ : ∀ p : Spec (CommRingCat.of K) ⟶ X, p ≫ f = 𝟙 _ → ∀ hx : ptOf p ∈ O₂,
        ev p hx s₂ = c := by
      intro p hp hx
      rw [← hh₂, ev_res]; exact ev_eq_of_nilpotent f hc p hp _
    by_cases hex : ∃ q : Spec (CommRingCat.of K) ⟶ X, q ≫ f = 𝟙 _ ∧ ptOf q ∈ W ∧ ptOf q ∈ σ.U
    · obtain ⟨q, hq, hqW, hqU⟩ := hex
      have hc0 : c ≠ 0 := by
        intro hc0
        have e := congrArg (ev q (show ptOf q ∈ O₁ from ⟨hqW, hqU⟩)) hi₁
        rw [map_mul, map_one, hv₁ q hq, hc0, zero_mul] at e
        exact zero_ne_one e
      refine ⟨OnePoint.some (a + c⁻¹), fun p hp hpW => ?_⟩
      have hpU : ptOf p ∈ σ.U := by
        by_contra hpU
        have hpV := mem_V_of_not_mem_U σ hpU
        have e := hv₂ p hp (show ptOf p ∈ O₂ from ⟨hpW, hpV⟩)
        simp only [s₂, map_mul] at e
        rw [ev_res, ev_g_eq_zero σ p hpV hpU, zero_mul] at e
        exact hc0 e.symm
      rw [val_of_mem σ p hpU]
      congr 1
      have e1 := congrArg (ev p (show ptOf p ∈ O₁ from ⟨hpW, hpU⟩)) hi₁
      rw [map_mul, map_one, hv₁ p hp, hu₁ev p hp] at e1
      have e2 := eq_inv_of_mul_eq_one_right e1
      linear_combination e2
    · push Not at hex
      exact ⟨OnePoint.infty, fun p hp hpW => val_of_not_mem σ p (hex p hp hpW)⟩

/-- **C2K from the leaf (L).** -/
theorem constOrOntoAlgClosed_of (hL : GlobalFunctionsConst) : ConstOrOntoAlgClosed := by
  intro K _ _ X f hP hS σ p₀ hp₀
  have : LocallyOfFiniteType f := inferInstance
  have : JacobsonSpace X := LocallyOfFiniteType.jacobsonSpace f
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  have : IsNoetherian X := { }
  set x₀ := ptOf p₀ with hx₀
  let W : X.Opens := ⟨connectedComponent x₀, isOpen_connectedComponent_of_noetherian x₀⟩
  have hWc : IsClopen (W : Set X) := ⟨isClosed_connectedComponent, W.isOpen⟩
  have hWp : _root_.IsPreconnected (W : Set X) := isPreconnected_connectedComponent
  have memW : ∀ p : Spec (CommRingCat.of K) ⟶ X, ptOf p ∈ W ↔
      connectedComponent (ptOf p) = connectedComponent x₀ :=
    fun p => ⟨fun h => (connectedComponent_eq h).symm,
      fun h => by
        show ptOf p ∈ connectedComponent x₀
        rw [← h]; exact mem_connectedComponent⟩
  by_cases ho : ∀ t : OnePoint K, ∃ p : Spec (CommRingCat.of K) ⟶ X, p ≫ f = 𝟙 _ ∧
      connectedComponent (ptOf p) = connectedComponent x₀ ∧ σ.val p = t
  · exact Or.inr ho
  · left
    push Not at ho
    obtain ⟨t, ht⟩ := ho
    obtain ⟨v, hv⟩ := constant_of_missed hL f hP hS σ W hWc hWp t
      (fun p hp hpW => ht p hp ((memW p).1 hpW))
    intro p hp hpc
    rw [hv p hp ((memW p).2 hpc), hv p₀ hp₀ (mem_connectedComponent : x₀ ∈ connectedComponent x₀)]

/-! ## §1 Algebra: an irreducible `P(x, y)` of `y`-degree `≥ 2` has a fibre with two roots -/

namespace Alg

open Polynomial

variable {K : Type} [Field K]

/-- `P(t, u)` for `P ∈ K[x][y]` (outer variable `y`, coefficients in `K[x]`). -/
def evalXY (t u : K) (P : K[X][X]) : K := (P.map (evalRingHom t)).eval u

/-- **Two roots in some fibre** (Lean-proved algebra; char. 0 is essential). If `P ∈ K[x][y]` is
irreducible of `y`-degree `d ≥ 2`, `K` algebraically closed of characteristic 0, then for some
`t ∈ K` the polynomial `P(t, y)` has two distinct roots. Proof: `P` is primitive and stays
irreducible over `K(x)` (Gauss), hence separable (char. 0), so the resultant
`r = Res_y(P, ∂P/∂y) ∈ K[x]` is nonzero; at any `t` with `r(t) · lc(P)(t) ≠ 0`, `P(t, y)` has
degree `d` and is separable, so it has `d ≥ 2` distinct roots. -/
theorem exists_two_roots [IsAlgClosed K] [CharZero K] {P : K[X][X]} (hirr : Irreducible P)
    (h2 : 2 ≤ P.natDegree) :
    ∃ t u u' : K, u ≠ u' ∧ evalXY t u P = 0 ∧ evalXY t u' P = 0 := by
  classical
  have hd0 : P.natDegree ≠ 0 := by omega
  have hP0 : P ≠ 0 := fun h => by simp [h] at h2
  set φ := algebraMap K[X] (FractionRing K[X]) with hφ
  have hinj : Function.Injective φ := IsFractionRing.injective _ _
  have hirr' : Irreducible (P.map φ) :=
    ((hirr.isPrimitive hd0).irreducible_iff_irreducible_map_fraction_map).1 hirr
  have hsep : (P.map φ).Separable := hirr'.separable
  have hres := resultant_ne_zero _ _ hsep
  rw [derivative_map, natDegree_map_eq_of_injective hinj,
    natDegree_map_eq_of_injective hinj, resultant_map_map] at hres
  set r := resultant P (derivative P) P.natDegree (derivative P).natDegree with hr
  have hr0 : r ≠ 0 := fun h => hres (by rw [h, map_zero])
  have hlc0 : P.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hP0
  -- a good fibre
  obtain ⟨t, ht⟩ : ∃ t : K, (r * P.leadingCoeff).eval t ≠ 0 := by
    by_contra! h
    exact mul_ne_zero hr0 hlc0 (Polynomial.funext fun t => by rw [h t, eval_zero])
  rw [eval_mul] at ht
  have hrt : r.eval t ≠ 0 := left_ne_zero_of_mul ht
  have hlt : P.leadingCoeff.eval t ≠ 0 := right_ne_zero_of_mul ht
  set ψ := evalRingHom t with hψ
  set Pt := P.map ψ with hPt
  have hdeg : Pt.natDegree = P.natDegree := natDegree_map_of_leadingCoeff_ne_zero ψ hlt
  have hdeg' : ((derivative P).map ψ).natDegree = (derivative P).natDegree := by
    refine natDegree_map_of_leadingCoeff_ne_zero ψ ?_
    rw [leadingCoeff_derivative, map_mul, map_natCast]
    exact mul_ne_zero hlt (by exact_mod_cast hd0)
  have hPt0 : Pt ≠ 0 := fun h => by rw [h, natDegree_zero] at hdeg; omega
  have hrest : resultant Pt (derivative Pt) ≠ 0 := by
    rw [derivative_map, hdeg, hdeg', resultant_map_map]
    exact hrt
  have hsep' : Pt.Separable := by
    have h := mt resultant_eq_zero_iff.2 hrest
    push Not at h
    exact h (Or.inl hPt0)
  have hcard : Pt.roots.card = P.natDegree := by
    rw [← (IsAlgClosed.splits Pt).natDegree_eq_card_roots, hdeg]
  have hnd : Pt.roots.Nodup := nodup_roots hsep'
  have h1 : 1 < Pt.roots.toFinset.card := by
    rw [Multiset.toFinset_card_of_nodup hnd, hcard]; omega
  obtain ⟨u, hu, u', hu', hne⟩ := Finset.one_lt_card.1 h1
  exact ⟨t, u, u', hne, (mem_roots hPt0).1 (Multiset.mem_toFinset.1 hu),
    (mem_roots hPt0).1 (Multiset.mem_toFinset.1 hu')⟩

/-- An irreducible `P ∈ K[x][y]` of `y`-degree 1 has coprime coefficients. -/
theorem isCoprime_coeff_of_irreducible {P : K[X][X]} (hirr : Irreducible P)
    (h1 : P.natDegree = 1) : IsCoprime (P.coeff 1) (P.coeff 0) := by
  have hP : P = C (P.coeff 1) * X + C (P.coeff 0) := eq_X_add_C_of_natDegree_le_one h1.le
  refine IsRelPrime.isCoprime fun d hdA hdB => ?_
  obtain ⟨a, ha⟩ := hdA
  obtain ⟨b, hb⟩ := hdB
  have hfac : P = C d * (C a * X + C b) := by
    rw [hP, ha, hb, C_mul, C_mul]; ring
  rcases hirr.isUnit_or_isUnit hfac with h | h
  · exact isUnit_C.mp h
  · exfalso
    have h0 := natDegree_eq_zero_of_isUnit h
    have : P.natDegree ≤ 0 := by
      rw [hfac]; exact (natDegree_C_mul_le _ _).trans h0.le
    omega

theorem evalXY_mul (t u : K) (P Q : K[X][X]) :
    evalXY t u (P * Q) = evalXY t u P * evalXY t u Q := by
  simp [evalXY]

/-- An irreducible `P ∈ K[x][y]` of positive `y`-degree does not vanish identically on a vertical
line: `P(t, y) ≠ 0` for every `t` (else `x − t` divides the content). -/
theorem map_eval_ne_zero {P : K[X][X]} (hirr : Irreducible P) (hdeg : 1 ≤ P.natDegree) (t : K) :
    P.map (evalRingHom t) ≠ 0 := by
  intro h0
  have hprim := hirr.isPrimitive (by omega)
  have hdvd : C (X - C t) ∣ P := by
    rw [C_dvd_iff_dvd_coeff]
    intro i
    rw [dvd_iff_isRoot]
    have := congrArg (fun q => q.coeff i) h0
    simpa [coeff_map] using this
  exact not_isUnit_X_sub_C t ((isPrimitive_iff_isUnit_of_C_dvd.mp hprim) _ hdvd)

/-- **Bezout-type finiteness** (Lean-proved): if `P ∈ K[x][y]` is irreducible of positive
`y`-degree and does not divide `Q`, then `P = Q = 0` has finitely many solutions in `K²`
(`Res_y(P, Q) ∈ K[x]` is nonzero, and each fibre of `P = 0` is finite). -/
theorem finite_common_zeros {P Q : K[X][X]} (hirr : Irreducible P) (hdeg : 1 ≤ P.natDegree)
    (hPQ : ¬ P ∣ Q) :
    {z : K × K | evalXY z.1 z.2 P = 0 ∧ evalXY z.1 z.2 Q = 0}.Finite := by
  classical
  have hd0 : P.natDegree ≠ 0 := by omega
  set φ := algebraMap K[X] (FractionRing K[X]) with hφ
  have hinj : Function.Injective φ := IsFractionRing.injective _ _
  have hprim := hirr.isPrimitive hd0
  have hirr' : Irreducible (P.map φ) :=
    (hprim.irreducible_iff_irreducible_map_fraction_map).1 hirr
  have hndvd : ¬ P.map φ ∣ Q.map φ := fun h =>
    hPQ ((hprim.dvd_iff_fraction_map_dvd_fraction_map (FractionRing K[X])).2 h)
  have hcop : IsCoprime (P.map φ) (Q.map φ) := hirr'.coprime_iff_not_dvd.2 hndvd
  have hres := resultant_ne_zero _ _ hcop
  rw [natDegree_map_eq_of_injective hinj, natDegree_map_eq_of_injective hinj,
    resultant_map_map] at hres
  set r := resultant P Q P.natDegree Q.natDegree with hr
  have hr0 : r ≠ 0 := fun h => hres (by rw [h, map_zero])
  obtain ⟨a, b, -, -, hab⟩ := exists_mul_add_mul_eq_C_resultant P Q le_rfl le_rfl (Or.inl hd0)
  refine ((r.roots.toFinset.finite_toSet).biUnion fun t _ =>
    ((P.map (evalRingHom t)).roots.toFinset.finite_toSet.image fun u => (t, u))).subset ?_
  rintro ⟨t, u⟩ ⟨h1, h2⟩
  have hrt : r.eval t = 0 := by
    have e := congrArg (evalXY t u) hab
    rw [← hr] at e
    simp only [evalXY, Polynomial.map_add, Polynomial.map_mul, eval_add, eval_mul,
      Polynomial.map_C, eval_C, coe_evalRingHom] at e h1 h2
    rw [h1, h2] at e
    simpa using e.symm
  simp only [Set.mem_iUnion, Set.mem_image, Finset.mem_coe, Multiset.mem_toFinset]
  refine ⟨t, (mem_roots hr0).2 hrt, u, (mem_roots (map_eval_ne_zero hirr hdeg t)).2 h1, rfl⟩

end Alg

/-! ## §2 The geometric glue (G1) and the reduction -/

open Polynomial in
/-- **(G1) The image of a connected component under `(σ, ρ)` is a plane curve.** Setting of C3K
(without characteristic 0): `X → Spec K` proper and smooth of relative dimension 1, `K`
algebraically closed, `σ, ρ : X → P¹`, `W` the connected component of the `K`-point `p₀`, and
`σ` nonconstant on the `K`-points of `W`. Then either `ρ ≡ ∞` on the `K`-points of `W`, or there
is an irreducible `P ∈ K[x][y]` of `y`-degree `≥ 1` such that
(a) `P(σ(p), ρ(p)) = 0` at every `K`-point `p` of `W` with both values finite;
(b) every `(t, u) ∈ K²` with `P(t, u) = 0` is `(σ(p), ρ(p))` for a `K`-point `p` of `W`;
(c) a `K`-point `p` of `W` with `σ(p) = t` finite and `ρ(p) = ∞` has `lc_y(P)(t) = 0`.

Why true (STANDARD; references UNVERIFIED): `W` is a complete nonsingular irreducible curve
(smooth ⇒ normal, so connected components are irreducible), so its image `D` under
`(σ, ρ) : W → P¹ × P¹` is closed (properness) and irreducible, and not a point (σ nonconstant).
If `ρ ≢ ∞`, `D ∩ 𝔸²` is a nonempty open, hence dense, subset of `D`, an irreducible closed curve
in `𝔸²`, so `D ∩ 𝔸² = V(P)` with `P` irreducible (`K[x, y]` is a UFD and height-one primes are
principal: Hartshorne I.1.12 / Ex. I.1.1-type facts); `P ∉ K[x]` because `σ` is nonconstant on
the dense set `W ∩ (σ, ρ)⁻¹(𝔸²)`. (a) is `D ∩ 𝔸² ⊆ V(P)`. (b): `V(P) ⊆ D`, and every closed point
of `D` is the image of a closed point of `W` (the fibre is a nonempty closed subset of a scheme of
finite type over `K`), i.e. of a `K`-point (Nullstellensatz). (c): `D` lies in the closure of
`V(P)` in `𝔸¹ × P¹`, which lies in `V(P^h)`, `P^h(x; y₀ : y₁) = Σ a_i(x) y₁^i y₀^{d−i}`, whose
points over `y = ∞` (`y₀ = 0`) have `a_d(x) = 0`.

Classified as **glue** (several textbook facts: image of a proper curve, plane curves as
hypersurfaces, closure and homogenization). Characteristic 0 is not used here; it enters only
through the Lean-proved `Alg.exists_two_roots`. Not in Mathlib v4.35 (no `P¹ × P¹`, no plane
curves). -/
def ImagePlaneCurve : Prop :=
  ∀ (K : Type) [Field K] [IsAlgClosed K] (X : Scheme.{0})
    (f : X ⟶ Spec (CommRingCat.of K)), IsProper f → SmoothOfRelativeDimension 1 f →
    ∀ (σ ρ : ToP1 X) (p₀ : Spec (CommRingCat.of K) ⟶ X), p₀ ≫ f = 𝟙 _ →
      (∃ p : Spec (CommRingCat.of K) ⟶ X, p ≫ f = 𝟙 _ ∧
        connectedComponent (ptOf p) = connectedComponent (ptOf p₀) ∧ σ.val p ≠ σ.val p₀) →
      (∀ p : Spec (CommRingCat.of K) ⟶ X, p ≫ f = 𝟙 _ →
        connectedComponent (ptOf p) = connectedComponent (ptOf p₀) →
        ρ.val p = OnePoint.infty) ∨
      ∃ P : K[X][X], Irreducible P ∧ 1 ≤ P.natDegree ∧
        (∀ p : Spec (CommRingCat.of K) ⟶ X, p ≫ f = 𝟙 _ →
          connectedComponent (ptOf p) = connectedComponent (ptOf p₀) → ∀ t u : K,
          σ.val p = OnePoint.some t → ρ.val p = OnePoint.some u → Alg.evalXY t u P = 0) ∧
        (∀ t u : K, Alg.evalXY t u P = 0 → ∃ p : Spec (CommRingCat.of K) ⟶ X, p ≫ f = 𝟙 _ ∧
          connectedComponent (ptOf p) = connectedComponent (ptOf p₀) ∧
          σ.val p = OnePoint.some t ∧ ρ.val p = OnePoint.some u) ∧
        (∀ p : Spec (CommRingCat.of K) ⟶ X, p ≫ f = 𝟙 _ →
          connectedComponent (ptOf p) = connectedComponent (ptOf p₀) → ∀ t : K,
          σ.val p = OnePoint.some t → ρ.val p = OnePoint.infty → P.leadingCoeff.eval t = 0)

open Polynomial in
/-- **C3K from (G1) and the Lean-proved algebra.** The fibre condition and
`Alg.exists_two_roots` force `deg_y P = 1`, `P = A y + B` with `A, B` coprime, and then
`ρ = [−B : A] ∘ σ` at every `K`-point of `W` with finite `σ`-value (clause (c) for `ρ = ∞`). -/
theorem ratFactorAlgClosed_of (hG : ImagePlaneCurve) : RatFactorAlgClosed := by
  intro K _ _ _ X f hP hS σ ρ p₀ hp₀ hne hfib
  rcases hG K X f hP hS σ ρ p₀ hp₀ hne with hinf | ⟨P, hirr, hdeg, ha, hb, hc⟩
  · refine ⟨1, 0, isCoprime_one_left, fun p hp hpc t _ => ?_⟩
    rw [hinf p hp hpc]
    simp [Mob.ratEval]
  · have hd1 : P.natDegree = 1 := by
      by_contra h
      obtain ⟨t, u, u', hne', hu, hu'⟩ := Alg.exists_two_roots hirr (by omega)
      obtain ⟨p, hp, hpc, hpt, hpu⟩ := hb t u hu
      obtain ⟨p', hp', hpc', hpt', hpu'⟩ := hb t u' hu'
      have e := hfib p p' hp hp' hpc hpc' (hpt.trans hpt'.symm)
      rw [hpu, hpu'] at e
      exact hne' (OnePoint.coe_injective e)
    have hcop := Alg.isCoprime_coeff_of_irreducible hirr hd1
    have hPe : P = C (P.coeff 1) * Polynomial.X + C (P.coeff 0) :=
      eq_X_add_C_of_natDegree_le_one hd1.le
    have hev : ∀ t u : K, Alg.evalXY t u P = (P.coeff 1).eval t * u + (P.coeff 0).eval t := by
      intro t u
      rw [Alg.evalXY]
      conv_lhs => rw [hPe]
      simp
    have hlc : P.leadingCoeff = P.coeff 1 := by rw [leadingCoeff, hd1]
    have hnotboth : ∀ t : K, (P.coeff 1).eval t = 0 → (P.coeff 0).eval t ≠ 0 := by
      intro t h1 h0
      obtain ⟨a, b, hab⟩ := hcop
      have e := congrArg (eval t) hab
      simp [eval_add, eval_mul, h1, h0] at e
    refine ⟨-(P.coeff 0), P.coeff 1, hcop.symm.neg_left, fun p hp hpc t ht => ?_⟩
    induction hρ : ρ.val p using OnePoint.rec with
    | infty =>
      have e := hc p hp hpc t ht hρ
      rw [hlc] at e
      unfold Mob.ratEval
      split_ifs
      rfl
    | coe u =>
      have e := ha p hp hpc t u ht hρ
      rw [hev] at e
      by_cases hA : (P.coeff 1).eval t = 0
      · exfalso
        rw [hA, zero_mul, zero_add] at e
        exact hnotboth t hA e
      · unfold Mob.ratEval
        split_ifs
        rw [eval_neg]
        refine congrArg _ ?_
        field_simp
        linear_combination e


open Polynomial in
/-- **(G1') The affine image is Zariski closed, and `P` cuts out the image curve.** As
`ImagePlaneCurve`, with clause (b) ("every point of `V(P)` is hit") replaced by (b''): the set of
pairs `(σ(p), ρ(p)) ∈ K²` over the `K`-points `p` of `W` with both values finite is Zariski
closed, i.e. the common zero set of some family `S ⊆ K[x][y]`.

Why true (STANDARD): the image `D` of `W` under `(σ, ρ)` is closed in `P¹ × P¹` (properness), so
`D ∩ 𝔸²` is closed in `𝔸²`, and its closed points are exactly the images of `K`-points of `W`
(fibres of `W → D` over closed points contain closed points, which are `K`-points). Clauses (a)
and (c) are those of `ImagePlaneCurve` (§6 of the report). (b) of `ImagePlaneCurve` follows in Lean
(`imagePlaneCurve_of`) from (b''), C2K (`σ` onto, so the affine image is infinite) and
Bezout-type finiteness (`Alg.finite_common_zeros`). Glue. -/
def ImagePlaneCurveClosed : Prop :=
  ∀ (K : Type) [Field K] [IsAlgClosed K] (X : Scheme.{0})
    (f : X ⟶ Spec (CommRingCat.of K)), IsProper f → SmoothOfRelativeDimension 1 f →
    ∀ (σ ρ : ToP1 X) (p₀ : Spec (CommRingCat.of K) ⟶ X), p₀ ≫ f = 𝟙 _ →
      (∃ p : Spec (CommRingCat.of K) ⟶ X, p ≫ f = 𝟙 _ ∧
        connectedComponent (ptOf p) = connectedComponent (ptOf p₀) ∧ σ.val p ≠ σ.val p₀) →
      (∀ p : Spec (CommRingCat.of K) ⟶ X, p ≫ f = 𝟙 _ →
        connectedComponent (ptOf p) = connectedComponent (ptOf p₀) →
        ρ.val p = OnePoint.infty) ∨
      ∃ P : K[X][X], Irreducible P ∧ 1 ≤ P.natDegree ∧
        (∀ p : Spec (CommRingCat.of K) ⟶ X, p ≫ f = 𝟙 _ →
          connectedComponent (ptOf p) = connectedComponent (ptOf p₀) → ∀ t u : K,
          σ.val p = OnePoint.some t → ρ.val p = OnePoint.some u → Alg.evalXY t u P = 0) ∧
        (∀ p : Spec (CommRingCat.of K) ⟶ X, p ≫ f = 𝟙 _ →
          connectedComponent (ptOf p) = connectedComponent (ptOf p₀) → ∀ t : K,
          σ.val p = OnePoint.some t → ρ.val p = OnePoint.infty → P.leadingCoeff.eval t = 0) ∧
        ∃ S : Set K[X][X], ∀ t u : K,
          (∃ p : Spec (CommRingCat.of K) ⟶ X, p ≫ f = 𝟙 _ ∧
            connectedComponent (ptOf p) = connectedComponent (ptOf p₀) ∧
            σ.val p = OnePoint.some t ∧ ρ.val p = OnePoint.some u) ↔
          ∀ Q ∈ S, Alg.evalXY t u Q = 0

open Polynomial in
/-- **(G1) from C2K and (G1').** -/
theorem imagePlaneCurve_of (h2 : ConstOrOntoAlgClosed) (hG : ImagePlaneCurveClosed) :
    ImagePlaneCurve := by
  classical
  intro K _ _ X f hP hS σ ρ p₀ hp₀ hne
  rcases hG K X f hP hS σ ρ p₀ hp₀ hne with hinf | ⟨P, hirr, hdeg, ha, hc, S, hSc⟩
  · exact Or.inl hinf
  refine Or.inr ⟨P, hirr, hdeg, ha, ?_, hc⟩
  have honto : ∀ t : OnePoint K, ∃ p : Spec (CommRingCat.of K) ⟶ X, p ≫ f = 𝟙 _ ∧
      connectedComponent (ptOf p) = connectedComponent (ptOf p₀) ∧ σ.val p = t := by
    rcases h2 K X f hP hS σ p₀ hp₀ with hcst | ho
    · obtain ⟨p, hp, hpc, hv⟩ := hne
      exact absurd (hcst p hp hpc) hv
    · exact ho
  let Im : Set (K × K) := {z | ∃ p : Spec (CommRingCat.of K) ⟶ X, p ≫ f = 𝟙 _ ∧
    connectedComponent (ptOf p) = connectedComponent (ptOf p₀) ∧
    σ.val p = OnePoint.some z.1 ∧ ρ.val p = OnePoint.some z.2}
  have hImInf : Im.Infinite := by
    have hlc0 : P.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hirr.ne_zero
    have hsub : {t : K | P.leadingCoeff.eval t ≠ 0} ⊆ Prod.fst '' Im := by
      intro t ht
      obtain ⟨p, hp, hpc, hpt⟩ := honto (OnePoint.some t)
      induction hρ : ρ.val p using OnePoint.rec with
      | infty => exact absurd (hc p hp hpc t hpt hρ) ht
      | coe u => exact ⟨(t, u), ⟨p, hp, hpc, hpt, hρ⟩, rfl⟩
    have hinfK : {t : K | P.leadingCoeff.eval t ≠ 0}.Infinite := by
      have e : {t : K | P.leadingCoeff.eval t ≠ 0} =
          ((P.leadingCoeff.roots.toFinset : Finset K) : Set K)ᶜ := by
        ext t
        simp [mem_roots hlc0]
      rw [e]
      exact (Finset.finite_toSet _).infinite_compl
    exact fun hfin => hinfK ((hfin.image Prod.fst).subset hsub)
  intro t u htu
  refine (hSc t u).2 fun Q hQ => ?_
  by_cases hPQ : P ∣ Q
  · obtain ⟨R, rfl⟩ := hPQ
    rw [Alg.evalXY_mul, htu, zero_mul]
  · exfalso
    apply hImInf
    refine (Alg.finite_common_zeros hirr hdeg hPQ).subset ?_
    rintro ⟨t', u'⟩ ⟨p, hp, hpc, hpt, hpu⟩
    exact ⟨ha p hp hpc t' u' hpt hpu, (hSc t' u').1 ⟨p, hp, hpc, hpt, hpu⟩ Q hQ⟩

/-- **C3K from C2K and (G1').** -/
theorem ratFactorAlgClosed_of_closed (h2 : ConstOrOntoAlgClosed) (hG : ImagePlaneCurveClosed) :
    RatFactorAlgClosed :=
  ratFactorAlgClosed_of (imagePlaneCurve_of h2 hG)

/-! ## §5 Clause (c) of (G1') from irreducibility of the component (task curve-glue) -/

/-- **(CI) Connected components of a smooth curve over a field are irreducible.** If `X → Spec K`
is smooth of relative dimension 1 over a field, every connected component of `X` is irreducible.

Why true (STANDARD; references UNVERIFIED): smooth over a field implies regular, hence normal
(Stacks, *Varieties*, smooth ⇒ normal; Hartshorne II.8 for regular local rings being domains);
a locally Noetherian normal scheme is a disjoint union of integral open subschemes (its local rings
are domains, so irreducible components are disjoint and open), so its connected components are
its irreducible components. Glue (standard commutative algebra and topology). Not in Mathlib
v4.35 as stated (task infra-smooth-dim proved that the local rings at closed points are regular of
dimension 1, `stalk_dim_of_smoothOfRelativeDimension`, which is the main input). -/
def ComponentIrreducible : Prop :=
  ∀ (K : Type) [Field K] (X : Scheme.{0}) (f : X ⟶ Spec (CommRingCat.of K)),
    SmoothOfRelativeDimension 1 f → ∀ x : X, IsIrreducible (connectedComponent x)

open Polynomial in
/-- **(G1'') `ImagePlaneCurveClosed` without clause (c).** Either `ρ ≡ ∞` on the `K`-points of
the component `W` of `p₀`, or there is an irreducible `P ∈ K[x][y]` of `y`-degree `≥ 1` with
(a) `P(σ(p), ρ(p)) = 0` at the `K`-points of `W` with both values finite, and (b'') the affine
image `{(σ(p), ρ(p))}` is Zariski closed in `K²`. Why true: §6 of the report (clauses (a), (b'')
of (G1')). Glue. -/
def ImagePlaneCurveIrr : Prop :=
  ∀ (K : Type) [Field K] [IsAlgClosed K] (X : Scheme.{0})
    (f : X ⟶ Spec (CommRingCat.of K)), IsProper f → SmoothOfRelativeDimension 1 f →
    ∀ (σ ρ : ToP1 X) (p₀ : Spec (CommRingCat.of K) ⟶ X), p₀ ≫ f = 𝟙 _ →
      (∃ p : Spec (CommRingCat.of K) ⟶ X, p ≫ f = 𝟙 _ ∧
        connectedComponent (ptOf p) = connectedComponent (ptOf p₀) ∧ σ.val p ≠ σ.val p₀) →
      (∀ p : Spec (CommRingCat.of K) ⟶ X, p ≫ f = 𝟙 _ →
        connectedComponent (ptOf p) = connectedComponent (ptOf p₀) →
        ρ.val p = OnePoint.infty) ∨
      ∃ P : K[X][X], Irreducible P ∧ 1 ≤ P.natDegree ∧
        (∀ p : Spec (CommRingCat.of K) ⟶ X, p ≫ f = 𝟙 _ →
          connectedComponent (ptOf p) = connectedComponent (ptOf p₀) → ∀ t u : K,
          σ.val p = OnePoint.some t → ρ.val p = OnePoint.some u → Alg.evalXY t u P = 0) ∧
        ∃ S : Set K[X][X], ∀ t u : K,
          (∃ p : Spec (CommRingCat.of K) ⟶ X, p ≫ f = 𝟙 _ ∧
            connectedComponent (ptOf p) = connectedComponent (ptOf p₀) ∧
            σ.val p = OnePoint.some t ∧ ρ.val p = OnePoint.some u) ↔
          ∀ Q ∈ S, Alg.evalXY t u Q = 0

section ClauseC

variable {K : Type} [Field K] {X : Scheme.{0}}

/-- `cst f O` as a ring hom. -/
def cstRH (f : X ⟶ Spec (CommRingCat.of K)) (O : X.Opens) : K →+* Γ(X, O) :=
  (res le_top).comp ((f.appTop).hom.comp (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom)

open Polynomial in
/-- `P(F, G) ∈ Γ(X, O)` for `P ∈ K[x][y]` and sections `F, G`. -/
def polySec (f : X ⟶ Spec (CommRingCat.of K)) {O : X.Opens} (P : K[X][X]) (F G : Γ(X, O)) :
    Γ(X, O) :=
  P.eval₂ (eval₂RingHom (cstRH f O) F) G

open Polynomial in
theorem ev_polySec (f : X ⟶ Spec (CommRingCat.of K)) (p : Spec (CommRingCat.of K) ⟶ X)
    (hp : p ≫ f = 𝟙 _) {O : X.Opens} (hx : ptOf p ∈ O) (P : K[X][X]) (F G : Γ(X, O)) :
    ev p hx (polySec f P F G) = P.eval₂ (evalRingHom (ev p hx F)) (ev p hx G) := by
  unfold polySec
  rw [hom_eval₂]
  congr 1
  refine Polynomial.ringHom_ext (fun a => ?_) ?_
  · simp only [RingHom.coe_comp, Function.comp_apply, coe_eval₂RingHom, eval₂_C,
      coe_evalRingHom, eval_C]
    exact ev_cst f p hp hx a
  · simp

open Polynomial in
/-- **Clause (c) from (a) and irreducibility** (Lean-proved). On a preirreducible open `W` with a
`K`-point where `σ` is finite and `ρ ∈ K^×`, if `P(σ, ρ) = 0` at the finite points of `W`, then
`lc_y(P)(σ(p₁)) = 0` at every `K`-point `p₁` of `W` with `σ(p₁)` finite and `ρ(p₁) = ∞`: the
section `P^rev(σ, 1/ρ)` on `W ∩ {σ ≠ ∞} ∩ {ρ ≠ 0}` vanishes on the dense open `{ρ ≠ ∞}`, hence
at `p₁`, where it equals `lc_y(P)(σ(p₁))`. -/
theorem lc_eval_eq_zero_of_irreducible [IsAlgClosed K] (f : X ⟶ Spec (CommRingCat.of K))
    [LocallyOfFiniteType f] [JacobsonSpace X] (σ ρ : ToP1 X) (W : X.Opens)
    (hW : IsPreirreducible (W : Set X)) (P : K[X][X])
    (ha : ∀ p : Spec (CommRingCat.of K) ⟶ X, p ≫ f = 𝟙 _ → ptOf p ∈ W → ∀ t u : K,
      σ.val p = OnePoint.some t → ρ.val p = OnePoint.some u → Alg.evalXY t u P = 0)
    (hne : ((W : Set X) ∩ ((σ.U : Set X) ∩ ((ρ.U : Set X) ∩ ρ.V))).Nonempty)
    (p₁ : Spec (CommRingCat.of K) ⟶ X) (hp₁ : p₁ ≫ f = 𝟙 _) (hW₁ : ptOf p₁ ∈ W) (t : K)
    (ht : σ.val p₁ = OnePoint.some t) (hρ : ρ.val p₁ = OnePoint.infty) :
    P.leadingCoeff.eval t = 0 := by
  have hσU : ptOf p₁ ∈ σ.U := by
    by_contra h
    rw [val_of_not_mem σ p₁ h] at ht
    exact OnePoint.infty_ne_coe t ht
  have hρU : ptOf p₁ ∉ ρ.U := fun h => by
    rw [val_of_mem ρ p₁ h] at hρ
    exact OnePoint.coe_ne_infty _ hρ
  have hρV : ptOf p₁ ∈ ρ.V := mem_V_of_not_mem_U ρ hρU
  let O' : X.Opens := W ⊓ σ.U ⊓ ρ.V
  have hle1 : O' ≤ σ.U := fun x hx => hx.1.2
  have hle2 : O' ≤ ρ.V := fun x hx => hx.2
  let h' : Γ(X, O') := polySec f P.reverse (res hle1 σ.f) (res hle2 ρ.g)
  have hev : ∀ p : Spec (CommRingCat.of K) ⟶ X, p ≫ f = 𝟙 _ → ∀ hx : ptOf p ∈ O',
      ev p hx h' = P.reverse.eval₂ (evalRingHom (ev p (hle1 hx) σ.f)) (ev p (hle2 hx) ρ.g) := by
    intro p hp hx
    simp only [h']
    rw [ev_polySec f p hp, ev_res, ev_res]
  have hvan : ∀ p : Spec (CommRingCat.of K) ⟶ X, p ≫ f = 𝟙 _ → ∀ hx : ptOf p ∈ O',
      ptOf p ∈ ρ.U → ev p hx h' = 0 := by
    intro p hp hx hU
    rw [hev p hp hx]
    have hu : ev p hU ρ.f * ev p (hle2 hx) ρ.g = 1 := ev_f_mul_g ρ p hU (hle2 hx)
    have hu0 : ev p hU ρ.f ≠ 0 := left_ne_zero_of_mul_eq_one hu
    have hg : ev p (hle2 hx) ρ.g = (ev p hU ρ.f)⁻¹ := eq_inv_of_mul_eq_one_right hu
    have hPa : Alg.evalXY (ev p (hle1 hx) σ.f) (ev p hU ρ.f) P = 0 :=
      ha p hp hx.1.1 _ _ (val_of_mem σ p (hle1 hx)) (val_of_mem ρ p hU)
    let _ : Invertible (ev p hU ρ.f) := invertibleOfNonzero hu0
    have key := eval₂_reverse_mul_pow (evalRingHom (ev p (hle1 hx) σ.f)) (ev p hU ρ.f) P
    have e2 : P.eval₂ (evalRingHom (ev p (hle1 hx) σ.f)) (ev p hU ρ.f) =
        Alg.evalXY (ev p (hle1 hx) σ.f) (ev p hU ρ.f) P := (Polynomial.eval_map _ _).symm
    rw [invOf_eq_inv, e2, hPa] at key
    rw [hg]
    exact (mul_eq_zero.mp key).resolve_right (pow_ne_zero _ hu0)
  have hsub : ((O' : Set X) ∩ ρ.U) ⊆ ((X.basicOpen h' : X.Opens) : Set X)ᶜ := by
    rintro x ⟨hxO, hxU⟩ hxb
    obtain ⟨p, hp, ⟨hpO, hpU⟩, hpb⟩ := exists_point_of_isLocallyClosed f
      (Z := ((O' : Set X) ∩ ρ.U) ∩ X.basicOpen h')
      ((O'.isOpen.inter ρ.U.isOpen).inter (X.basicOpen h').isOpen).isLocallyClosed
      ⟨x, ⟨hxO, hxU⟩, hxb⟩
    exact (ev_eq_zero_iff p hpO h').1 (hvan p hp hpO hpU) hpb
  have hcl : ptOf p₁ ∈ closure ((O' : Set X) ∩ ρ.U) := by
    have hopen : IsOpen ((σ.U : Set X) ∩ ((ρ.U : Set X) ∩ ρ.V)) :=
      σ.U.isOpen.inter (ρ.U.isOpen.inter ρ.V.isOpen)
    have h := subset_closure_inter_of_isPreirreducible_of_isOpen hW hopen hne hW₁
    have e : (W : Set X) ∩ ((σ.U : Set X) ∩ ((ρ.U : Set X) ∩ ρ.V)) = (O' : Set X) ∩ ρ.U := by
      ext x
      simp only [O', Opens.coe_inf, Set.mem_inter_iff, SetLike.mem_coe]
      tauto
    rwa [e] at h
  have hnot : ptOf p₁ ∉ X.basicOpen h' :=
    closure_minimal hsub (X.basicOpen h').isOpen.isClosed_compl hcl
  have hx₁ : ptOf p₁ ∈ O' := ⟨⟨hW₁, hσU⟩, hρV⟩
  have h0 := (ev_eq_zero_iff p₁ hx₁ h').2 hnot
  rw [hev p₁ hp₁ hx₁, ev_g_eq_zero ρ p₁ (hle2 hx₁) hρU, eval₂_at_zero, coeff_zero_reverse] at h0
  have hs : ev p₁ (hle1 hx₁) σ.f = t := by
    have e := val_of_mem σ p₁ hσU
    rw [ht] at e
    exact (OnePoint.coe_injective e).symm
  rw [hs] at h0
  simpa using h0

end ClauseC

open Polynomial in
/-- **(G1') from (CI) and (G1'').** -/
theorem imagePlaneCurveClosed_of (hI : ComponentIrreducible) (hG : ImagePlaneCurveIrr) :
    ImagePlaneCurveClosed := by
  intro K _ _ X f hP hS σ ρ p₀ hp₀ hne
  have : LocallyOfFiniteType f := inferInstance
  have : JacobsonSpace X := LocallyOfFiniteType.jacobsonSpace f
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  have : IsNoetherian X := { }
  set x₀ := ptOf p₀ with hx₀
  let W : X.Opens := ⟨connectedComponent x₀, isOpen_connectedComponent_of_noetherian x₀⟩
  have memW : ∀ p : Spec (CommRingCat.of K) ⟶ X, ptOf p ∈ W ↔
      connectedComponent (ptOf p) = connectedComponent x₀ :=
    fun p => ⟨fun h => (connectedComponent_eq h).symm,
      fun h => by
        show ptOf p ∈ connectedComponent x₀
        rw [← h]; exact mem_connectedComponent⟩
  have hWi : IsPreirreducible (W : Set X) := (hI K X f hS x₀).isPreirreducible
  by_cases hinf : ∀ p : Spec (CommRingCat.of K) ⟶ X, p ≫ f = 𝟙 _ →
      connectedComponent (ptOf p) = connectedComponent x₀ → ρ.val p = OnePoint.infty
  · exact Or.inl hinf
  rcases hG K X f hP hS σ ρ p₀ hp₀ hne with hinf' | ⟨P, hirr, hdeg, ha, hclo⟩
  · exact absurd hinf' hinf
  refine Or.inr ⟨P, hirr, hdeg, ha, ?_, hclo⟩
  intro p₁ hp₁ hpc₁ t ht hρ
  refine lc_eval_eq_zero_of_irreducible f σ ρ W hWi P
    (fun p hp hpW => ha p hp ((memW p).1 hpW)) ?_ p₁ hp₁ ((memW p₁).2 hpc₁) t ht hρ
  have h1 : ((W : Set X) ∩ σ.U).Nonempty := by
    obtain ⟨p, hp, hpc, hv⟩ := hne
    by_cases h : ptOf p₀ ∈ σ.U
    · exact ⟨_, (mem_connectedComponent : x₀ ∈ connectedComponent x₀), h⟩
    · have hpU : ptOf p ∈ σ.U := by
        by_contra h'
        exact hv (by rw [val_of_not_mem σ p h', val_of_not_mem σ p₀ h])
      exact ⟨_, (memW p).2 hpc, hpU⟩
  have h2 : ((W : Set X) ∩ ρ.U).Nonempty := by
    push Not at hinf
    obtain ⟨p, hp, hpc, hv⟩ := hinf
    have hpU : ptOf p ∈ ρ.U := by
      by_contra h'
      exact hv (val_of_not_mem ρ p h')
    exact ⟨_, (memW p).2 hpc, hpU⟩
  have h3 : ((W : Set X) ∩ ρ.V).Nonempty := by
    refine ⟨_, (memW p₁).2 hpc₁, mem_V_of_not_mem_U ρ fun h => ?_⟩
    rw [val_of_mem ρ p₁ h] at hρ
    exact OnePoint.coe_ne_infty _ hρ
  have h23 := hWi _ _ ρ.U.isOpen ρ.V.isOpen h2 h3
  exact hWi _ _ σ.U.isOpen (ρ.U.isOpen.inter ρ.V.isOpen) h1 h23

/-- **C3K from C2K, (CI) and (G1'').** -/
theorem ratFactorAlgClosed_of_irr (h2 : ConstOrOntoAlgClosed) (hI : ComponentIrreducible)
    (hG : ImagePlaneCurveIrr) : RatFactorAlgClosed :=
  ratFactorAlgClosed_of_closed h2 (imagePlaneCurveClosed_of hI hG)

/-! ## §6 (G1'') from algebraic dependence, a closed image, irreducibility and C2K (task curve-glue) -/

open Polynomial in
/-- **(AD) `σ` and `ρ` are algebraically dependent on a connected component.** For `X → Spec K`
proper and smooth of relative dimension 1 over `K = K̄`, `σ, ρ : X → P¹` and a `K`-point `p₀`,
some nonzero `P ∈ K[x][y]` has `P(σ(p), ρ(p)) = 0` at every `K`-point `p` of the connected
component of `p₀` where both values are finite.

Why true (STANDARD; numbering UNVERIFIED): the component `W` is an integral curve, its function
field `K(W)` has transcendence degree `dim W = 1` over `K` (Hartshorne I.1.8A and I.6), so the
rational functions `σ, ρ` satisfy a nonzero polynomial relation `P(σ, ρ) = 0` in `K(W)`; the
regular function `P(σ, ρ)` on the open set where both are finite is then zero (`W` reduced), so it
vanishes at those `K`-points. Glue. -/
def AlgDep : Prop :=
  ∀ (K : Type) [Field K] [IsAlgClosed K] (X : Scheme.{0})
    (f : X ⟶ Spec (CommRingCat.of K)), IsProper f → SmoothOfRelativeDimension 1 f →
    ∀ (σ ρ : ToP1 X) (p₀ : Spec (CommRingCat.of K) ⟶ X), p₀ ≫ f = 𝟙 _ →
      ∃ P : K[X][X], P ≠ 0 ∧
        ∀ p : Spec (CommRingCat.of K) ⟶ X, p ≫ f = 𝟙 _ →
          connectedComponent (ptOf p) = connectedComponent (ptOf p₀) → ∀ t u : K,
          σ.val p = OnePoint.some t → ρ.val p = OnePoint.some u → Alg.evalXY t u P = 0

open Polynomial in
/-- **(IC) The affine image of a connected component under `(σ, ρ)` is Zariski closed.** In the
same setting, the set of `(σ(p), ρ(p)) ∈ K²` over the `K`-points `p` of the connected component of
`p₀` with both values finite is the common zero set of some `S ⊆ K[x][y]`.

Why true (STANDARD): the component `W` is proper over `K` (open and closed in `X`), so its image
`D` under `(σ, ρ) : W → P¹ × P¹` is closed (`P¹ × P¹` separated); `D ∩ 𝔸²` is closed in `𝔸²`,
hence `V(I)` for an ideal `I` (take `S = I`), and its `K`-points are exactly the images of the
`K`-points of `W` (a fibre over a closed point is a nonempty closed set of finite type over `K`,
so it contains a closed point, a `K`-point by the Nullstellensatz). Glue (properness). -/
def ImageClosed : Prop :=
  ∀ (K : Type) [Field K] [IsAlgClosed K] (X : Scheme.{0})
    (f : X ⟶ Spec (CommRingCat.of K)), IsProper f → SmoothOfRelativeDimension 1 f →
    ∀ (σ ρ : ToP1 X) (p₀ : Spec (CommRingCat.of K) ⟶ X), p₀ ≫ f = 𝟙 _ →
      ∃ S : Set K[X][X], ∀ t u : K,
        (∃ p : Spec (CommRingCat.of K) ⟶ X, p ≫ f = 𝟙 _ ∧
          connectedComponent (ptOf p) = connectedComponent (ptOf p₀) ∧
          σ.val p = OnePoint.some t ∧ ρ.val p = OnePoint.some u) ↔
        ∀ Q ∈ S, Alg.evalXY t u Q = 0

section FactorSel

variable {K : Type} [Field K] {X : Scheme.{0}}

open Polynomial in
/-- `evalXY t u` as a ring hom. -/
def evalXYHom (t u : K) : K[X][X] →+* K := (evalRingHom u).comp (mapRingHom (evalRingHom t))

open Polynomial in
theorem evalXYHom_apply (t u : K) (P : K[X][X]) : evalXYHom t u P = Alg.evalXY t u P := rfl

open Polynomial in
/-- **Choosing an irreducible factor** (Lean-proved). On an irreducible open `O` of a Jacobson
scheme of finite type over `K = K̄`, if `P(F, G)` vanishes at every `K`-point of `O`, then so does
`q(F, G)` for some irreducible factor `q` of `P` (the zero loci of the factors are closed and
cover `O`). -/
theorem exists_factor_vanishing [IsAlgClosed K] (f : X ⟶ Spec (CommRingCat.of K))
    [LocallyOfFiniteType f] [JacobsonSpace X] {O : X.Opens} (hO : IsIrreducible (O : Set X))
    (F G : Γ(X, O)) (P : K[X][X]) (hP0 : P ≠ 0)
    (hvan : ∀ p : Spec (CommRingCat.of K) ⟶ X, p ≫ f = 𝟙 _ → ∀ hx : ptOf p ∈ O,
      Alg.evalXY (ev p hx F) (ev p hx G) P = 0) :
    ∃ q ∈ UniqueFactorizationMonoid.factors P, ∀ p : Spec (CommRingCat.of K) ⟶ X, p ≫ f = 𝟙 _ →
      ∀ hx : ptOf p ∈ O, Alg.evalXY (ev p hx F) (ev p hx G) q = 0 := by
  classical
  set fs := UniqueFactorizationMonoid.factors P with hfs
  let C : K[X][X] → Set X := fun q => ((X.basicOpen (polySec f q F G) : X.Opens) : Set X)ᶜ
  have hev : ∀ (q : K[X][X]) (p : Spec (CommRingCat.of K) ⟶ X) (hp : p ≫ f = 𝟙 _)
      (hx : ptOf p ∈ O), ev p hx (polySec f q F G) = Alg.evalXY (ev p hx F) (ev p hx G) q := by
    intro q p hp hx
    rw [ev_polySec f p hp]
    exact (Polynomial.eval_map _ _).symm
  have hpt : ∀ (p : Spec (CommRingCat.of K) ⟶ X) (hp : p ≫ f = 𝟙 _) (hx : ptOf p ∈ O),
      ∃ q ∈ fs, Alg.evalXY (ev p hx F) (ev p hx G) q = 0 := by
    intro p hp hx
    obtain ⟨v, hv⟩ := UniqueFactorizationMonoid.factors_prod hP0
    have h0 := hvan p hp hx
    rw [← hv, Alg.evalXY_mul] at h0
    rcases mul_eq_zero.mp h0 with h | h
    · rw [← evalXYHom_apply, map_multiset_prod, Multiset.prod_eq_zero_iff] at h
      obtain ⟨q, hq, hq0⟩ := Multiset.mem_map.1 h
      exact ⟨q, hq, hq0⟩
    · exact absurd h ((v.isUnit.map (evalXYHom (ev p hx F) (ev p hx G))).ne_zero)
  have hcov : (O : Set X) ⊆ ⋃₀ ↑(fs.toFinset.image C) := by
    intro x hx
    by_contra hnot
    let Z : Set X := (O : Set X) ∩ ⋂ q ∈ fs.toFinset, ((X.basicOpen (polySec f q F G) : X.Opens) : Set X)
    have hZo : IsOpen Z :=
      O.isOpen.inter (isOpen_biInter_finset fun q _ => (X.basicOpen (polySec f q F G)).isOpen)
    have hxZ : x ∈ Z := by
      refine ⟨hx, Set.mem_iInter₂.2 fun q hq => ?_⟩
      by_contra hxq
      exact hnot ⟨C q, Finset.mem_coe.2 (Finset.mem_image_of_mem C hq), hxq⟩
    obtain ⟨p, hp, hpO, hpall⟩ := exists_point_of_isLocallyClosed f hZo.isLocallyClosed ⟨x, hxZ⟩
    obtain ⟨q, hq, hq0⟩ := hpt p hp hpO
    have hb : ptOf p ∈ X.basicOpen (polySec f q F G) :=
      Set.mem_iInter₂.1 hpall q (Multiset.mem_toFinset.2 hq)
    exact (ev_eq_zero_iff p hpO _).1 ((hev q p hp hpO).trans hq0) hb
  have hcl : ∀ z ∈ fs.toFinset.image C, IsClosed z := by
    intro z hz
    obtain ⟨q, -, rfl⟩ := Finset.mem_image.1 hz
    exact (X.basicOpen (polySec f q F G)).isOpen.isClosed_compl
  obtain ⟨z, hz, hOz⟩ := (isIrreducible_iff_sUnion_isClosed.1 hO) _ hcl hcov
  obtain ⟨q, hq, rfl⟩ := Finset.mem_image.1 hz
  refine ⟨q, Multiset.mem_toFinset.1 hq, fun p hp hx => ?_⟩
  rw [← hev q p hp hx]
  exact (ev_eq_zero_iff p hx _).2 (hOz hx)

end FactorSel

open Polynomial in
/-- **(G1'') from C2K, (CI), (AD) and (IC).** -/
theorem imagePlaneCurveIrr_of (h2 : ConstOrOntoAlgClosed) (hI : ComponentIrreducible)
    (hA : AlgDep) (hC : ImageClosed) : ImagePlaneCurveIrr := by
  classical
  intro K _ _ X f hP hS σ ρ p₀ hp₀ hne
  have : LocallyOfFiniteType f := inferInstance
  have : JacobsonSpace X := LocallyOfFiniteType.jacobsonSpace f
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  have : IsNoetherian X := { }
  set x₀ := ptOf p₀ with hx₀
  let W : X.Opens := ⟨connectedComponent x₀, isOpen_connectedComponent_of_noetherian x₀⟩
  have memW : ∀ p : Spec (CommRingCat.of K) ⟶ X, ptOf p ∈ W ↔
      connectedComponent (ptOf p) = connectedComponent x₀ :=
    fun p => ⟨fun h => (connectedComponent_eq h).symm,
      fun h => by
        show ptOf p ∈ connectedComponent x₀
        rw [← h]; exact mem_connectedComponent⟩
  have hWi : IsPreirreducible (W : Set X) := (hI K X f hS x₀).isPreirreducible
  by_cases hinf : ∀ p : Spec (CommRingCat.of K) ⟶ X, p ≫ f = 𝟙 _ →
      connectedComponent (ptOf p) = connectedComponent x₀ → ρ.val p = OnePoint.infty
  · exact Or.inl hinf
  right
  obtain ⟨P, hP0, hPa⟩ := hA K X f hP hS σ ρ p₀ hp₀
  obtain ⟨S, hSc⟩ := hC K X f hP hS σ ρ p₀ hp₀
  have memU : ∀ (τ : ToP1 X) (p : Spec (CommRingCat.of K) ⟶ X) (t : K),
      τ.val p = OnePoint.some t → ptOf p ∈ τ.U := by
    intro τ p t h
    by_contra h'
    rw [val_of_not_mem τ p h'] at h
    exact OnePoint.infty_ne_coe t h
  have honto : ∀ t : OnePoint K, ∃ p : Spec (CommRingCat.of K) ⟶ X, p ≫ f = 𝟙 _ ∧
      connectedComponent (ptOf p) = connectedComponent (ptOf p₀) ∧ σ.val p = t := by
    rcases h2 K X f hP hS σ p₀ hp₀ with hcst | ho
    · obtain ⟨p, hp, hpc, hv⟩ := hne
      exact absurd (hcst p hp hpc) hv
    · exact ho
  -- the irreducible open `O = W ∩ {σ ≠ ∞} ∩ {ρ ≠ ∞}`
  let O : X.Opens := W ⊓ σ.U ⊓ ρ.U
  have hle1 : O ≤ σ.U := fun x hx => hx.1.2
  have hle2 : O ≤ ρ.U := fun x hx => hx.2
  have h1 : ((W : Set X) ∩ σ.U).Nonempty := by
    obtain ⟨p, hp, hpc, hpt⟩ := honto (OnePoint.some 0)
    exact ⟨_, (memW p).2 hpc, memU σ p 0 hpt⟩
  have h2' : ((W : Set X) ∩ ρ.U).Nonempty := by
    push Not at hinf
    obtain ⟨p, hp, hpc, hv⟩ := hinf
    have hpU : ptOf p ∈ ρ.U := by
      by_contra h'
      exact hv (val_of_not_mem ρ p h')
    exact ⟨_, (memW p).2 hpc, hpU⟩
  have hOne : (O : Set X).Nonempty := by
    obtain ⟨x, hxW, hx1, hx2⟩ := hWi _ _ σ.U.isOpen ρ.U.isOpen h1 h2'
    exact ⟨x, ⟨hxW, hx1⟩, hx2⟩
  have hOirr : IsIrreducible (O : Set X) :=
    ⟨hOne, hWi.open_subset O.isOpen fun x hx => hx.1.1⟩
  have hvan : ∀ p : Spec (CommRingCat.of K) ⟶ X, p ≫ f = 𝟙 _ → ∀ hx : ptOf p ∈ O,
      Alg.evalXY (ev p hx (res hle1 σ.f)) (ev p hx (res hle2 ρ.f)) P = 0 := by
    intro p hp hx
    rw [ev_res, ev_res]
    exact hPa p hp ((memW p).1 hx.1.1) _ _ (val_of_mem σ p _) (val_of_mem ρ p _)
  obtain ⟨q, hq, hqv⟩ := exists_factor_vanishing f hOirr (res hle1 σ.f) (res hle2 ρ.f) P hP0 hvan
  have hqirr : Irreducible q := UniqueFactorizationMonoid.irreducible_of_factor q hq
  have hqa : ∀ p : Spec (CommRingCat.of K) ⟶ X, p ≫ f = 𝟙 _ →
      connectedComponent (ptOf p) = connectedComponent (ptOf p₀) → ∀ t u : K,
      σ.val p = OnePoint.some t → ρ.val p = OnePoint.some u → Alg.evalXY t u q = 0 := by
    intro p hp hpc t u ht hu
    have hσ : ptOf p ∈ σ.U := memU σ p t ht
    have hρ : ptOf p ∈ ρ.U := memU ρ p u hu
    have hx : ptOf p ∈ O := ⟨⟨(memW p).2 hpc, hσ⟩, hρ⟩
    have e := hqv p hp hx
    rw [ev_res, ev_res] at e
    rw [val_of_mem σ p hσ] at ht
    rw [val_of_mem ρ p hρ] at hu
    rwa [OnePoint.coe_injective ht, OnePoint.coe_injective hu] at e
  have hdeg : 1 ≤ q.natDegree := by
    by_contra hd
    have hq0 : q.natDegree = 0 := by omega
    have hqC : q = C (q.coeff 0) := eq_C_of_natDegree_eq_zero hq0
    set a := q.coeff 0 with ha
    have ha0 : a ≠ 0 := by
      intro h0
      rw [h0, map_zero] at hqC
      exact hqirr.ne_zero hqC
    let O₁ : X.Opens := W ⊓ σ.U
    have hle3 : O₁ ≤ σ.U := fun x hx => hx.2
    let hs : Γ(X, O₁) := polySec f (C a) (res hle3 σ.f) 0
    have hev1 : ∀ p : Spec (CommRingCat.of K) ⟶ X, p ≫ f = 𝟙 _ → ∀ hx : ptOf p ∈ O₁,
        ev p hx hs = a.eval (ev p (hle3 hx) σ.f) := by
      intro p hp hx
      simp only [hs]
      rw [ev_polySec f p hp, ev_res]
      simp
    have hsub : (O : Set X) ⊆ ((X.basicOpen hs : X.Opens) : Set X)ᶜ := by
      intro x hxO hxb
      obtain ⟨p, hp, hpO, hpb⟩ := exists_point_of_isLocallyClosed f
        (Z := (O : Set X) ∩ X.basicOpen hs)
        (O.isOpen.inter (X.basicOpen hs).isOpen).isLocallyClosed ⟨x, hxO, hxb⟩
      have hpO₁ : ptOf p ∈ O₁ := hpO.1
      have e := hqv p hp hpO
      rw [ev_res, ev_res, hqC] at e
      have e' : ev p hpO₁ hs = 0 := by
        rw [hev1 p hp hpO₁]
        simpa [Alg.evalXY] using e
      exact (ev_eq_zero_iff p hpO₁ hs).1 e' hpb
    have hWcl : (W : Set X) ⊆ closure (O : Set X) := by
      have hne' : ((W : Set X) ∩ ((σ.U : Set X) ∩ ρ.U)).Nonempty := by
        obtain ⟨x, hx⟩ := hOne
        exact ⟨x, hx.1.1, hx.1.2, hx.2⟩
      have h := subset_closure_inter_of_isPreirreducible_of_isOpen hWi
        (σ.U.isOpen.inter ρ.U.isOpen) hne'
      have e : (W : Set X) ∩ ((σ.U : Set X) ∩ ρ.U) = (O : Set X) := by
        ext x
        simp only [O, Opens.coe_inf, Set.mem_inter_iff, SetLike.mem_coe]
        tauto
      rwa [e] at h
    obtain ⟨t, ht⟩ : ∃ t : K, a.eval t ≠ 0 := by
      by_contra! h
      exact ha0 (by
        have := Polynomial.funext (p := a) (q := 0) fun t => by rw [h t, eval_zero]
        exact this)
    obtain ⟨p, hp, hpc, hpt⟩ := honto (OnePoint.some t)
    have hσ : ptOf p ∈ σ.U := memU σ p t hpt
    have hx : ptOf p ∈ O₁ := ⟨(memW p).2 hpc, hσ⟩
    have hnot : ptOf p ∉ X.basicOpen hs :=
      closure_minimal hsub (X.basicOpen hs).isOpen.isClosed_compl (hWcl hx.1)
    have e := (ev_eq_zero_iff p hx hs).2 hnot
    rw [hev1 p hp hx] at e
    rw [val_of_mem σ p hσ] at hpt
    rw [OnePoint.coe_injective hpt] at e
    exact ht e
  exact ⟨q, hqirr, hdeg, hqa, S, hSc⟩

/-- **C3K from C2K, (CI), (AD) and (IC).** -/
theorem ratFactorAlgClosed_of_AD (h2 : ConstOrOntoAlgClosed) (hI : ComponentIrreducible)
    (hA : AlgDep) (hC : ImageClosed) : RatFactorAlgClosed :=
  ratFactorAlgClosed_of_irr h2 hI (imagePlaneCurveIrr_of h2 hI hA hC)


/-- **Both curve facts of mobius-glue from C1b (`SmoothStalkDimOne`, glue, task
infra-smooth-dim), the textbook leaf (L) `GlobalFunctionsConst` and the glue (G1)
`ImagePlaneCurve`.** -/
theorem curveFacts_of_glue (h1 : SmoothStalkDimOne) (hL : GlobalFunctionsConst)
    (hG : ImagePlaneCurve) : CurveRatFactor ∧ CurveSurj :=
  curveFacts_of_leaves h1 (constOrOntoAlgClosed_of hL) (ratFactorAlgClosed_of hG)

/-- **The same with (G1') `ImagePlaneCurveClosed` (affine image Zariski closed) for (G1).** -/
theorem curveFacts_of_glue' (h1 : SmoothStalkDimOne) (hL : GlobalFunctionsConst)
    (hG : ImagePlaneCurveClosed) : CurveRatFactor ∧ CurveSurj :=
  curveFacts_of_glue h1 hL (imagePlaneCurve_of (constOrOntoAlgClosed_of hL) hG)

/-- **The same with (CI) `ComponentIrreducible` and (G1'') `ImagePlaneCurveIrr` for (G1').** -/
theorem curveFacts_of_glue'' (h1 : SmoothStalkDimOne) (hL : GlobalFunctionsConst)
    (hI : ComponentIrreducible) (hG : ImagePlaneCurveIrr) : CurveRatFactor ∧ CurveSurj :=
  curveFacts_of_glue' h1 hL (imagePlaneCurveClosed_of hI hG)

/-- **The same with (AD) `AlgDep` and (IC) `ImageClosed` for (G1'').** -/
theorem curveFacts_of_glue_AD (h1 : SmoothStalkDimOne) (hL : GlobalFunctionsConst)
    (hI : ComponentIrreducible) (hA : AlgDep) (hC : ImageClosed) : CurveRatFactor ∧ CurveSurj :=
  curveFacts_of_glue'' h1 hL hI (imagePlaneCurveIrr_of (constOrOntoAlgClosed_of hL) hI hA hC)

/-! ## The leaf (L0) and the reduction -/

section L0

variable {K : Type} [Field K] {X : Scheme.{0}}

/-- `cst f O` as a ring hom `K → Γ(X, O)` (the `K`-algebra structure of `Γ(X, O)`). -/
def cstHom (f : X ⟶ Spec (CommRingCat.of K)) (O : X.Opens) : K →+* Γ(X, O) :=
  (res le_top).comp ((f.appTop).hom.comp (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom)

theorem cstHom_apply (f : X ⟶ Spec (CommRingCat.of K)) (O : X.Opens) (a : K) :
    cstHom f O a = cst f O a := rfl

end L0

/-- **(L0) Finiteness of global sections for proper schemes over a field.** If `X → Spec K` is
proper and `W ⊆ X` is open and closed, then `Γ(W, 𝒪_X)` is a finite `K`-module (for the
`K`-algebra structure through `X → Spec K`).

Source (textbook leaf, STANDARD; numbering UNVERIFIED): the finiteness theorem for proper
morphisms, `f_* 𝓕` coherent for `𝓕` coherent and `f` proper (EGA III₁ 3.2.1; Stacks, *Cohomology
of Schemes*, "coherent sheaves on proper schemes"; Hartshorne II.5.20 / III.8.8 in the projective
case), applied to `𝓕 = 𝒪_W` (`W` is open and closed, hence a closed subscheme, so `W → Spec K` is
proper). Not in Mathlib v4.35. -/
def FiniteGlobalSections : Prop :=
  ∀ (K : Type) [Field K] (X : Scheme.{0}) (f : X ⟶ Spec (CommRingCat.of K)), IsProper f →
    ∀ W : X.Opens, IsClopen (W : Set X) → (cstHom f W).Finite

/-- **Algebra (Lean-proved): a connected finite algebra over an algebraically closed field is
`K` plus nilpotents.** In an Artinian ring with only the trivial idempotents every element is a
unit or nilpotent (Fitting: `s^n = s^{n+1} y` makes `s^n y^n` idempotent); and `s - c` is not a
unit for an eigenvalue `c` of multiplication by `s`. -/
theorem exists_nilpotent_sub_of_finite {K A : Type} [Field K] [IsAlgClosed K] [CommRing A]
    (φ : K →+* A) (hφ : φ.Finite) (hidem : ∀ e : A, IsIdempotentElem e → e = 0 ∨ e = 1)
    (s : A) : ∃ c : K, IsNilpotent (s - φ c) := by
  let _ := φ.toAlgebra
  have : Module.Finite K A := hφ
  have : IsArtinianRing A := IsArtinianRing.of_finite K A
  -- unit or nilpotent
  have key : ∀ x : A, IsUnit x ∨ IsNilpotent x := by
    intro x
    obtain ⟨n, y, hy⟩ := IsArtinian.exists_pow_succ_smul_dvd x (1 : A)
    simp only [smul_eq_mul, mul_one] at hy
    replace hy : x ^ (n + 1) * y = x ^ n := hy
    have hpow : ∀ k : ℕ, x ^ n = x ^ (n + k) * y ^ k := by
      intro k
      induction k with
      | zero => simp
      | succ k ih =>
        rw [ih]
        calc x ^ (n + k) * y ^ k = (x ^ k * x ^ n) * y ^ k := by ring
          _ = (x ^ k * (x ^ (n + 1) * y)) * y ^ k := by rw [hy]
          _ = x ^ (n + (k + 1)) * y ^ (k + 1) := by ring
    have he : IsIdempotentElem (x ^ n * y ^ n) := by
      unfold IsIdempotentElem
      calc x ^ n * y ^ n * (x ^ n * y ^ n) = (x ^ (n + n) * y ^ n) * y ^ n := by ring
        _ = x ^ n * y ^ n := by rw [← hpow n]
    rcases hidem _ he with h0 | h1
    · right
      refine ⟨n, ?_⟩
      rw [hpow n]
      calc x ^ (n + n) * y ^ n = x ^ n * (x ^ n * y ^ n) := by ring
        _ = 0 := by rw [h0, mul_zero]
    · left
      rcases Nat.eq_zero_or_pos n with hn | hn
      · subst hn
        have : x * y = 1 := by simpa using hy
        exact isUnit_iff_exists_inv.mpr ⟨y, this⟩
      · refine isUnit_iff_exists_inv.mpr ⟨x ^ (n - 1) * y ^ n, ?_⟩
        calc x * (x ^ (n - 1) * y ^ n) = x ^ (n - 1 + 1) * y ^ n := by ring
          _ = 1 := by rw [Nat.sub_add_cancel hn, h1]
  by_cases hA : Nontrivial A
  · obtain ⟨c, hc⟩ := Module.End.exists_eigenvalue (LinearMap.mulLeft K s)
    obtain ⟨v, hv⟩ := hc.exists_hasEigenvector
    have hv0 : v ≠ 0 := hv.2
    have hsv : s * v = φ c * v := by
      have := hv.apply_eq_smul
      simpa [Algebra.smul_def, RingHom.algebraMap_toAlgebra] using this
    refine ⟨c, (key (s - φ c)).resolve_left fun hu => hv0 ?_⟩
    have : (s - φ c) * v = 0 := by rw [sub_mul, hsv, sub_self]
    exact (hu.mul_right_eq_zero).mp this
  · rw [not_nontrivial_iff_subsingleton] at hA
    exact ⟨0, ⟨1, Subsingleton.elim _ _⟩⟩

/-- **Topology/sheaves (Lean-proved): idempotent sections over a preconnected open are trivial.**
At each point the germ of an idempotent is `0` or `1` (local ring), so `W` is the disjoint union
of the open sets `D(e)` and `D(1 - e)`. -/
theorem idempotent_trivial_of_isPreconnected {X : Scheme.{0}} {W : X.Opens}
    (hW : _root_.IsPreconnected (W : Set X)) (e : Γ(X, W)) (he : IsIdempotentElem e) :
    e = 0 ∨ e = 1 := by
  have hcover : (W : Set X) ⊆ (X.basicOpen e : Set X) ∪ (X.basicOpen (1 - e) : Set X) := by
    intro x hx
    have hg : IsIdempotentElem (X.presheaf.germ W x hx e) := by
      unfold IsIdempotentElem; rw [← map_mul, he.eq]
    rcases IsLocalRing.isUnit_or_isUnit_one_sub_self (X.presheaf.germ W x hx e) with hu | hu
    · exact Or.inl ((X.mem_basicOpen e x hx).2 hu)
    · right
      refine (X.mem_basicOpen (1 - e) x hx).2 ?_
      rwa [map_sub, map_one]
  have hdisj : Disjoint (X.basicOpen e : Set X) (X.basicOpen (1 - e) : Set X) := by
    rw [Set.disjoint_left]
    intro x h1 h2
    have hxW : x ∈ W := X.basicOpen_le e h1
    have u1 := (X.mem_basicOpen e x hxW).1 h1
    have u2 := (X.mem_basicOpen (1 - e) x hxW).1 h2
    have h0 : X.presheaf.germ W x hxW e * X.presheaf.germ W x hxW (1 - e) = 0 := by
      rw [← map_mul, mul_sub, mul_one, he.eq, sub_self, map_zero]
    exact not_isUnit_zero (h0 ▸ u1.mul u2)
  have hunit : ∀ a : Γ(X, W), (W : Set X) ⊆ (X.basicOpen a : Set X) → IsUnit a := by
    intro a ha
    refine X.toRingedSpace.isUnit_of_isUnit_germ W a fun x hx => ?_
    exact (X.mem_basicOpen a x hx).1 (ha hx)
  rcases hW.subset_or_subset (X.basicOpen e).isOpen (X.basicOpen (1 - e)).isOpen hdisj hcover
    with h | h
  · right
    obtain ⟨u, hu⟩ := hunit e h
    have : (u : Γ(X, W)) * u = u * 1 := by rw [mul_one, hu]; exact he.eq
    rw [← hu]; exact u.isUnit.mul_left_cancel this
  · left
    obtain ⟨u, hu⟩ := hunit (1 - e) h
    have he' : IsIdempotentElem (1 - e) := he.one_sub
    have : (u : Γ(X, W)) * u = u * 1 := by rw [mul_one, hu]; exact he'.eq
    have h1 : 1 - e = 1 := by rw [← hu]; exact u.isUnit.mul_left_cancel this
    rw [sub_eq_self] at h1; exact h1

/-- **(L) from (L0).** -/
theorem globalFunctionsConst_of (h : FiniteGlobalSections) : GlobalFunctionsConst := by
  intro K _ _ X f hP _ W hWc hWp s
  obtain ⟨c, hc⟩ := exists_nilpotent_sub_of_finite (cstHom f W) (h K X f hP W hWc)
    (fun e he => idempotent_trivial_of_isPreconnected hWp e he) s
  exact ⟨c, hc⟩

/-- **`SmoothStalkDimOne` holds** (task infra-smooth-dim). -/
theorem smoothStalkDimOne : SmoothStalkDimOne := by
  intro K _ X f hf x hx
  have := (InfraSmoothDim.stalk_dim_of_smoothOfRelativeDimension f 1 x hx).1
  rw [this, Nat.cast_one]

/-- **Both curve facts from the leaf (L) and the glue (G1) alone** (C1b proved by
infra-smooth-dim). -/
theorem curveFacts_of_L_G1 (hL : GlobalFunctionsConst) (hG : ImagePlaneCurve) :
    CurveRatFactor ∧ CurveSurj :=
  curveFacts_of_glue smoothStalkDimOne hL hG

/-- **Both curve facts from (L0) and (G1).** -/
theorem curveFacts_of_L0_G1 (hL0 : FiniteGlobalSections) (hG : ImagePlaneCurve) :
    CurveRatFactor ∧ CurveSurj :=
  curveFacts_of_L_G1 (globalFunctionsConst_of hL0) hG

/-- **Both curve facts from (L0) and (G1').** -/
theorem curveFacts_of_L0_G1' (hL0 : FiniteGlobalSections) (hG : ImagePlaneCurveClosed) :
    CurveRatFactor ∧ CurveSurj :=
  curveFacts_of_glue' smoothStalkDimOne (globalFunctionsConst_of hL0) hG

/-- **Both curve facts from (L0), (CI) and (G1'').** -/
theorem curveFacts_of_L0_CI_G1'' (hL0 : FiniteGlobalSections) (hI : ComponentIrreducible)
    (hG : ImagePlaneCurveIrr) : CurveRatFactor ∧ CurveSurj :=
  curveFacts_of_glue'' smoothStalkDimOne (globalFunctionsConst_of hL0) hI hG

/-- **Both curve facts from (L0), (CI), (AD) and (IC).** -/
theorem curveFacts_of_L0_CI_AD_IC (hL0 : FiniteGlobalSections) (hI : ComponentIrreducible)
    (hA : AlgDep) (hC : ImageClosed) : CurveRatFactor ∧ CurveSurj :=
  curveFacts_of_glue_AD smoothStalkDimOne (globalFunctionsConst_of hL0) hI hA hC

/-- **The kernel's `MobiusGlue` from C1b, the leaf (L), the glue (G1) and the textbook leaf T5.** -/
theorem mobiusGlue_of_glue (h1 : SmoothStalkDimOne) (hL : GlobalFunctionsConst)
    (hG : ImagePlaneCurve) (hT : ObjBridge.TorsionStructure) : MobiusGlue :=
  mobiusGlue_of_curves (curveFacts_of_glue h1 hL hG).1 (curveFacts_of_glue h1 hL hG).2 hT

end Pin

namespace CurveGlue

open CategoryTheory AlgebraicGeometry Limits
open PkgI3 Pin

/-! ## Copied verbatim from `scratch/h-decomposition/Leaves.lean` (namespace `LeafAdopt`) -/

/-- **R1pi0 (rv-blueprints Q4): `X₆` is geometrically connected over `ℚ`.** For the level-one
curve `X₆ = X₀(6,1)` of the bundle, `X₆ ×_ℚ ℚ̄` is connected (`π₀(X₆_ℚ̄) = 1`), the input of
h-b1 M10 (Lemma NV step 4) and of the shape `ℚ(t)(√(at), √(b(t−1)))` in A10 step 2.
*Published*: Deligne, Sém. Bourbaki 389 (1971), §2: `π₀(Sh_{K₀}) = ℚ^×_{>0}\𝔸_f^×/nrd(K₀)`,
trivial for `K₀ = 𝒪̂^×` since `nrd(𝒪̂^×) = ℤ̂^×` (locator UNVERIFIED; rv-blueprints re-derived the
computation, and `π₀(Y₃) = 2` from `nrd(1 + 3𝒪₃) = 1 + 3ℤ₃`). *Alternative*: rv-blueprints Q4
sketches a glue proof from `R5fpCount` and the CM clauses (Kummer parity of branch points;
SPECULATIVE, not checked in detail). Counted inside leaf R1 (same publications), not as a new
leaf. -/
def R1pi0Props (X : Over (Spec (CommRingCat.of ℚ))) : Prop :=
  GeometricallyConnected X.hom

/-- **R2 on `X₆` with biconditional CM clauses (rv-blueprints Q5).** As `R2X6Props`, with
"CM by `ℤ[i]` (resp. `ℤ[ζ₃]`, `ℤ[√−6]`) `↔` `π₆ = 0` (resp. `∞`, `−16/27`)". *Published*:
Baba–Granath 2008, Thm 2.1 and the §3.1 elliptic-order table (each of `CM(−4)`, `CM(−3)`,
`CM(−24)` is one `W`-orbit, the fibre over the corresponding value); a consequence, as
`R2X6Props` is. In the bundle it is not an extra assumption: `r2X6PropsIff_of` derives it from
`R2X6Props` and `CMExists`. -/
def R2X6PropsIff (X : Over (Spec (CommRingCat.of ℚ)))
    (Ψ : (fieldPt Qbar ⟶ X) ≃ Quotient (pairSetoid Qbar)) (π₆ : ToP1 X.left) : Prop :=
  ∀ (x x' : fieldPt Qbar ⟶ X) (P Q : QMPair Qbar),
    Ψ x = Quotient.mk _ P → Ψ x' = Quotient.mk _ Q →
      (π₆.val (K := Qbar) x.left = π₆.val (K := Qbar) x'.left ↔
          ∃ α : O ≃+* O, Nonempty (QMIso (P.q.twist α) Q.q)) ∧
      (HasCM4 P.q ↔ π₆.val (K := Qbar) x.left = OnePoint.some 0) ∧
      (HasCM3 P.q ↔ π₆.val (K := Qbar) x.left = OnePoint.infty) ∧
      (HasCM24 P.q ↔ π₆.val (K := Qbar) x.left = OnePoint.some (-16 / 27))

/-- The repaired bundle (docstring abridged; the statement is verbatim from LeafAdopt). -/
def R1R2fpRep : Prop :=
  ∃ (Y : Over (Spec (CommRingCat.of ℚ))) (Φ : PtEquiv Y)
    (X : Over (Spec (CommRingCat.of ℚ))) (Ψ : (fieldPt Qbar ⟶ X) ≃ Quotient (pairSetoid Qbar))
    (fY : Y ⟶ X) (π₆ : ToP1 X.left),
    R1fpProps Y Φ ∧ R1heckeProps Y Φ ∧ X6Props Y Φ X Ψ fY ∧ R2X6PropsIff X Ψ π₆ ∧
      R1recProps Y Φ ∧ X6Surj Y X fY π₆ ∧ R5ptProps X Ψ ∧ R1pi0Props X

variable {X : Over (Spec (CommRingCat.of ℚ))} {Ψ : (fieldPt Qbar ⟶ X) ≃ Quotient (pairSetoid Qbar)}
  {π₆ : ToP1 X.left}

/-- The biconditional form gives back the one-way form. -/
theorem r2X6Props_of_iff (h : R2X6PropsIff X Ψ π₆) : R2X6Props X Ψ π₆ := by
  intro x x' P Q hP hQ
  obtain ⟨hf, h4, h3, h24⟩ := h x x' P Q hP hQ
  exact ⟨hf, h4.1, h3.1, h24.1⟩

/-- **Glue (proved): existence of the three CM points** from the biconditionals and the
surjectivity of `π₆` on `ℚ̄`-points (the first half of `X6Surj`). -/
theorem cmExists_of_iff (h : R2X6PropsIff X Ψ π₆)
    (hs : ∀ t : OnePoint Qbar, ∃ x : fieldPt Qbar ⟶ X, π₆.val (K := Qbar) x.left = t) :
    CMExists X Ψ := by
  refine ⟨?_, ?_, ?_⟩
  · obtain ⟨x, hx⟩ := hs (OnePoint.some 0)
    exact ⟨x, (Ψ x).out, (Quotient.out_eq _).symm,
      ((h x x _ _ (Quotient.out_eq _).symm (Quotient.out_eq _).symm).2.1).2 hx⟩
  · obtain ⟨x, hx⟩ := hs OnePoint.infty
    exact ⟨x, (Ψ x).out, (Quotient.out_eq _).symm,
      ((h x x _ _ (Quotient.out_eq _).symm (Quotient.out_eq _).symm).2.2.1).2 hx⟩
  · obtain ⟨x, hx⟩ := hs (OnePoint.some (-16 / 27))
    exact ⟨x, (Ψ x).out, (Quotient.out_eq _).symm,
      ((h x x _ _ (Quotient.out_eq _).symm (Quotient.out_eq _).symm).2.2.2).2 hx⟩

/-- **Glue (proved)**: the repaired bundle implies leaf-qm-fp's `R1R2fp`. -/
theorem R1R2fp_of_rep (h : R1R2fpRep) : R1R2fp := by
  obtain ⟨Y, Φ, X, Ψ, fY, π₆, h1, hh, h6, h2, hr, hs, h5, -⟩ := h
  exact ⟨Y, Φ, X, Ψ, fY, π₆, h1, hh, h6, r2X6Props_of_iff h2, cmExists_of_iff h2 hs.1, hr, hs, h5⟩

/-! ## New: CM points on any triple -/

/-- The three CM objects (the fifth premise of `MobiusGlue`). -/
def CMObjects : Prop :=
  (∃ P : QML3 Qbar, HasCM4 P.q) ∧ (∃ P : QML3 Qbar, HasCM3 P.q) ∧ (∃ P : QML3 Qbar, HasCM24 P.q)

/-- The three CM points of `(Y, Φ, π)` over `0, ∞, −16/27`. -/
def CMPoints (Y : Over (Spec (CommRingCat.of ℚ))) (Φ : PtEquiv Y) (π : ToP1 Y.left) : Prop :=
  (∃ (y : fieldPt Qbar ⟶ Y) (P : QML3 Qbar), Φ Qbar y = M3.mk P ∧ HasCM4 P.q ∧
      π.val (K := Qbar) y.left = OnePoint.some 0) ∧
  (∃ (y : fieldPt Qbar ⟶ Y) (P : QML3 Qbar), Φ Qbar y = M3.mk P ∧ HasCM3 P.q ∧
      π.val (K := Qbar) y.left = OnePoint.infty) ∧
  (∃ (y : fieldPt Qbar ⟶ Y) (P : QML3 Qbar), Φ Qbar y = M3.mk P ∧ HasCM24 P.q ∧
      π.val (K := Qbar) y.left = OnePoint.some (-16 / 27))

/-- **CM points from CM objects** (`Φ Qbar` is onto; only the one-way clauses of `R2fpProps`). -/
theorem cm_points_of_objects {Y : Over (Spec (CommRingCat.of ℚ))} {Φ : PtEquiv Y}
    {π : ToP1 Y.left} (h2 : R2fpProps Y Φ π) (hCM : CMObjects) : CMPoints Y Φ π := by
  obtain ⟨⟨P₄, c₄⟩, ⟨P₃, c₃⟩, ⟨P₂, c₂⟩⟩ := hCM
  have e : ∀ P : QML3 Qbar, Φ Qbar ((Φ Qbar).symm (M3.mk P)) = M3.mk P :=
    fun P => Equiv.apply_symm_apply _ _
  refine ⟨⟨_, P₄, e P₄, c₄, ?_⟩, ⟨_, P₃, e P₃, c₃, ?_⟩, ⟨_, P₂, e P₂, c₂, ?_⟩⟩
  · exact ((h2 _ _ P₄ P₄ (e P₄) (e P₄)).2.1) c₄
  · exact ((h2 _ _ P₃ P₃ (e P₃) (e P₃)).2.2.1) c₃
  · exact ((h2 _ _ P₂ P₂ (e P₂) (e P₂)).2.2.2) c₂

/-- **CM points on every triple, from the leaf bundle `R1R2fp`** (via `CMExists`, `X6Surj`). -/
theorem cm_points_of_R1R2fp (h : R1R2fp) {Y : Over (Spec (CommRingCat.of ℚ))} {Φ : PtEquiv Y}
    {π : ToP1 Y.left} (h2 : R2fpProps Y Φ π) : CMPoints Y Φ π :=
  cm_points_of_objects h2 (cm_objects_of_R1R2fp h)

/-- **CM points on every triple, from the repaired bundle `R1R2fpRep`** (`CMExists` from the
biconditionals and `π₆` onto; level-3 structures from `Y₃ → X₆` onto). -/
theorem cm_points_of_R1R2fpRep (h : R1R2fpRep) {Y : Over (Spec (CommRingCat.of ℚ))}
    {Φ : PtEquiv Y} {π : ToP1 Y.left} (h2 : R2fpProps Y Φ π) : CMPoints Y Φ π :=
  cm_points_of_R1R2fp (R1R2fp_of_rep h) h2

/-- `MobiusGlue` without its CM premise. -/
def MobiusGlueNoCM : Prop :=
  ∀ (Y Y' : Over (Spec (CommRingCat.of ℚ))) (Φ : PtEquiv Y) (Φ' : PtEquiv Y')
    (π : ToP1 Y.left) (π' : ToP1 Y'.left) (g : Y' ⟶ Y),
    R1fpProps Y Φ → R2fpProps Y Φ π → R1fpProps Y' Φ' → R2fpProps Y' Φ' π' →
    (∀ (K : Type) [Field K] [Algebra ℚ K] (y : fieldPt K ⟶ Y'), Φ' K y = Φ K (y ≫ g)) →
    ∀ y : fieldPt Qbar ⟶ Y', π'.val (K := Qbar) y.left = π.val (K := Qbar) (y ≫ g).left

/-- **The CM premise of `MobiusGlue` is discharged by the leaf bundle.** -/
theorem mobiusGlue_noCM_of (hM : MobiusGlue) (h : R1R2fp) : MobiusGlueNoCM :=
  fun Y Y' Φ Φ' π π' g h1 h2 h1' h2' hg =>
    hM Y Y' Φ Φ' π π' g h1 h2 h1' h2' (cm_objects_of_R1R2fp h) hg

theorem mobiusGlue_noCM_of_rep (hM : MobiusGlue) (h : R1R2fpRep) : MobiusGlueNoCM :=
  mobiusGlue_noCM_of hM (R1R2fp_of_rep h)

end CurveGlue

namespace CurveGlue

open CategoryTheory AlgebraicGeometry Limits Pin

/-- **End to end: the CM-free form of `MobiusGlue` from the leaf bundle and the named pieces.** -/
theorem mobiusGlueNoCM_of_glue (h1 : SmoothStalkDimOne) (hL : GlobalFunctionsConst)
    (hG : ImagePlaneCurve) (hT : ObjBridge.TorsionStructure) (h : R1R2fp) : MobiusGlueNoCM :=
  mobiusGlue_noCM_of (mobiusGlue_of_glue h1 hL hG hT) h

end CurveGlue

namespace CurveGlue

open CategoryTheory AlgebraicGeometry Limits Pin

/-- **The kernel's `MobiusGlue` from the textbook leaf (L) `GlobalFunctionsConst`, the glue (G1)
`ImagePlaneCurve` and the textbook leaf T5 `ObjBridge.TorsionStructure`.** -/
theorem mobiusGlue_of_L_G1_T5 (hL : GlobalFunctionsConst) (hG : ImagePlaneCurve)
    (hT : ObjBridge.TorsionStructure) : MobiusGlue :=
  mobiusGlue_of_glue smoothStalkDimOne hL hG hT

/-- **The CM-free form, with the CM objects from the leaf bundle `R1R2fp`.** -/
theorem mobiusGlueNoCM_of_L_G1_T5 (hL : GlobalFunctionsConst) (hG : ImagePlaneCurve)
    (hT : ObjBridge.TorsionStructure) (h : R1R2fp) : MobiusGlueNoCM :=
  mobiusGlue_noCM_of (mobiusGlue_of_L_G1_T5 hL hG hT) h

/-- **The kernel's `MobiusGlue` from the finiteness theorem (L0) `FiniteGlobalSections`, the glue
(G1) `ImagePlaneCurve` and the textbook leaf T5 `ObjBridge.TorsionStructure`.** -/
theorem mobiusGlue_of_L0_G1_T5 (hL0 : FiniteGlobalSections) (hG : ImagePlaneCurve)
    (hT : ObjBridge.TorsionStructure) : MobiusGlue :=
  mobiusGlue_of_L_G1_T5 (globalFunctionsConst_of hL0) hG hT

/-- **The CM-free form, with the CM objects from the leaf bundle `R1R2fp`.** -/
theorem mobiusGlueNoCM_of_L0_G1_T5 (hL0 : FiniteGlobalSections) (hG : ImagePlaneCurve)
    (hT : ObjBridge.TorsionStructure) (h : R1R2fp) : MobiusGlueNoCM :=
  mobiusGlue_noCM_of (mobiusGlue_of_L0_G1_T5 hL0 hG hT) h

/-- **Main result: the kernel's `MobiusGlue` from (L0) `FiniteGlobalSections`, (G1')
`ImagePlaneCurveClosed` and T5 `ObjBridge.TorsionStructure`.** -/
theorem mobiusGlue_of_L0_G1'_T5 (hL0 : FiniteGlobalSections) (hG : ImagePlaneCurveClosed)
    (hT : ObjBridge.TorsionStructure) : MobiusGlue :=
  mobiusGlue_of_L0_G1_T5 hL0
    (imagePlaneCurve_of (constOrOntoAlgClosed_of (globalFunctionsConst_of hL0)) hG) hT

/-- **The kernel's `MobiusGlue` from (L0), (CI) `ComponentIrreducible`, (G1'') `ImagePlaneCurveIrr`
and T5.** -/
theorem mobiusGlue_of_L0_CI_G1''_T5 (hL0 : FiniteGlobalSections) (hI : ComponentIrreducible)
    (hG : ImagePlaneCurveIrr) (hT : ObjBridge.TorsionStructure) : MobiusGlue :=
  mobiusGlue_of_L0_G1'_T5 hL0 (imagePlaneCurveClosed_of hI hG) hT

/-- **Its CM-free form.** -/
theorem mobiusGlueNoCM_of_L0_CI_G1''_T5 (hL0 : FiniteGlobalSections) (hI : ComponentIrreducible)
    (hG : ImagePlaneCurveIrr) (hT : ObjBridge.TorsionStructure) (h : R1R2fp) : MobiusGlueNoCM :=
  mobiusGlue_noCM_of (mobiusGlue_of_L0_CI_G1''_T5 hL0 hI hG hT) h

/-- **Main result: the kernel's `MobiusGlue` from (L0) `FiniteGlobalSections`, (CI)
`ComponentIrreducible`, (AD) `AlgDep`, (IC) `ImageClosed` and T5 `ObjBridge.TorsionStructure`.** -/
theorem mobiusGlue_of_L0_CI_AD_IC_T5 (hL0 : FiniteGlobalSections) (hI : ComponentIrreducible)
    (hA : AlgDep) (hC : ImageClosed) (hT : ObjBridge.TorsionStructure) : MobiusGlue :=
  mobiusGlue_of_L0_CI_G1''_T5 hL0 hI
    (imagePlaneCurveIrr_of (constOrOntoAlgClosed_of (globalFunctionsConst_of hL0)) hI hA hC) hT

/-- **The CM-free form of the main result** (CM objects from the leaf bundle `R1R2fp`). -/
theorem mobiusGlueNoCM_of_L0_CI_AD_IC_T5 (hL0 : FiniteGlobalSections) (hI : ComponentIrreducible)
    (hA : AlgDep) (hC : ImageClosed) (hT : ObjBridge.TorsionStructure) (h : R1R2fp) :
    MobiusGlueNoCM :=
  mobiusGlue_noCM_of (mobiusGlue_of_L0_CI_AD_IC_T5 hL0 hI hA hC hT) h

/-- **The CM-free form of the (G1') result.** -/
theorem mobiusGlueNoCM_of_L0_G1'_T5 (hL0 : FiniteGlobalSections) (hG : ImagePlaneCurveClosed)
    (hT : ObjBridge.TorsionStructure) (h : R1R2fp) : MobiusGlueNoCM :=
  mobiusGlue_noCM_of (mobiusGlue_of_L0_G1'_T5 hL0 hG hT) h

end CurveGlue

end AV

end LeafQM

end

#print axioms LeafQM.AV.Pin.mobiusGlue_of_curves
#print axioms LeafQM.AV.Pin.curveFacts_of_glue
#print axioms LeafQM.AV.Pin.mobiusGlue_of_glue
#print axioms LeafQM.AV.CurveGlue.mobiusGlueNoCM_of_glue
#print axioms LeafQM.AV.Pin.smoothStalkDimOne
#print axioms LeafQM.AV.Pin.globalFunctionsConst_of
#print axioms LeafQM.AV.Pin.curveFacts_of_L0_G1
#print axioms LeafQM.AV.Pin.curveFacts_of_L0_G1'
#print axioms LeafQM.AV.CurveGlue.mobiusGlue_of_L_G1_T5
#print axioms LeafQM.AV.CurveGlue.mobiusGlue_of_L0_G1_T5
#print axioms LeafQM.AV.CurveGlue.mobiusGlueNoCM_of_L0_G1_T5
#print axioms LeafQM.AV.CurveGlue.mobiusGlue_of_L0_G1'_T5
#print axioms LeafQM.AV.CurveGlue.mobiusGlueNoCM_of_L0_G1'_T5
#print axioms LeafQM.AV.Pin.curveFacts_of_L0_CI_G1''
#print axioms LeafQM.AV.CurveGlue.mobiusGlue_of_L0_CI_G1''_T5
#print axioms LeafQM.AV.CurveGlue.mobiusGlueNoCM_of_L0_CI_G1''_T5
#print axioms LeafQM.AV.Pin.curveFacts_of_L0_CI_AD_IC
#print axioms LeafQM.AV.CurveGlue.mobiusGlue_of_L0_CI_AD_IC_T5
#print axioms LeafQM.AV.CurveGlue.mobiusGlueNoCM_of_L0_CI_AD_IC_T5
