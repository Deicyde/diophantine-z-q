import TailD
import ZInQKernel.Hypotheses.JHeight
import ZInQKernel.Compiler.Precision.HeightConstant
import ZInQKernel.Contrib.BrauerT14T15.Main
import ZInQKernel.Contrib.LocalKW.T30
import ZInQKernel.Contrib.KroneckerWeber.Leaves
import ZInQKernel.Contrib.Chebotarev.FrobeniusDense
import ZInQKernel.Contrib.Different.Global
import ZInQKernel.Contrib.T25.NewformOfEigenform
import ZInQKernel.Contrib.T31.Main
import ZInQKernel.HDecomp.Textbook.BrauerNesbitt
import ZInQKernel.Multiplication.Certificate.ConstantsProperties
import ZInQKernel.Progressions.Final.Instance
import ZInQKernel.Size.Constants.T
import ZInQKernel.Contrib.T14.Main
import ZInQKernel.Contrib.T28.Assemble
import ZInQKernel.Contrib.RLeaf.X1ConstantField
import ZInQKernel.HDecomp.QM.Pin
import ZInQKernel.HDecomp.Textbook.SkolemNoether
import Mathlib.LinearAlgebra.Lagrange
import Mathlib.RingTheory.Polynomial.Resultant.Basic
import Mathlib.RingTheory.Polynomial.GaussLemma
import Mathlib.FieldTheory.Separable
import Mathlib.FieldTheory.IsAlgClosed.Basic
import ZInQKernel.HDecomp.Objects
import ZInQKernel.HDecomp.QM.Pairs
import ZInQKernel.HDecomp.Descent.B2Glue
/-! ## leaf-fold2: the root-namespace modules (image-plane's ImagePlaneFinal.lean verbatim, LF2Stalks, LF2UnifRoot, LF2SmoothDim, LF2UnramConj), each in its own section so that its file-level opens do not leak -/
section LF2Root_ImagePlane

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

/-- **(CI) Connected components of a proper smooth curve over a field are irreducible.** If
`X → Spec K` is proper and smooth of relative dimension 1 over a field, every connected component of
`X` is irreducible (properness is not needed, but is kept: it is where (CI) is used, and it makes
the Lean proof `componentIrreducible` in `MobiusFinal.lean` a Noetherian argument).

Why true (STANDARD; references UNVERIFIED): smooth over a field implies regular, hence normal
(Stacks, *Varieties*, smooth ⇒ normal; Hartshorne II.8 for regular local rings being domains);
a locally Noetherian normal scheme is a disjoint union of integral open subschemes (its local rings
are domains, so irreducible components are disjoint and open), so its connected components are
its irreducible components. Glue (standard commutative algebra and topology). Not in Mathlib
v4.35 as stated (task infra-smooth-dim proved that the local rings at closed points are regular of
dimension 1, `stalk_dim_of_smoothOfRelativeDimension`, which is the main input; with it, (CI) is
proved in `MobiusFinal.lean`, `componentIrreducible`). -/
def ComponentIrreducible : Prop :=
  ∀ (K : Type) [Field K] (X : Scheme.{0}) (f : X ⟶ Spec (CommRingCat.of K)), IsProper f →
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
  have hWi : IsPreirreducible (W : Set X) := (hI K X f hP hS x₀).isPreirreducible
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
  have hWi : IsPreirreducible (W : Set X) := (hI K X f hP hS x₀).isPreirreducible
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

/-! ## (CI) proved: components of a proper smooth curve are irreducible (task curve-glue)

Uses task infra-smooth-dim's `InfraSmoothDim.stalk_dim_of_smoothOfRelativeDimension` (local rings
at closed points have Krull dimension 1 and principal maximal ideal). -/

namespace CurveGlueCI

open CategoryTheory AlgebraicGeometry IsLocalRing

/-- **A Noetherian local ring of Krull dimension 1 with principal maximal ideal is a domain.**
(Krull intersection theorem: every nonzero element is `π^n · unit`; `π` is not nilpotent since the
dimension is positive.) -/
theorem isDomain_of_dim_one {R : Type*} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    (hdim : ringKrullDim R = 1) (hspan : (maximalIdeal R).spanFinrank = 1) : IsDomain R := by
  classical
  have hfg : (maximalIdeal R).FG := IsNoetherian.noetherian _
  obtain ⟨s, hs, hspan'⟩ := Submodule.FG.exists_span_set_encard_eq_spanFinrank hfg
  rw [hspan] at hs
  obtain ⟨π, rfl⟩ := Set.encard_eq_one.1 (by exact_mod_cast hs)
  -- `π` is not nilpotent
  have hπ : ∀ n : ℕ, π ^ n ≠ 0 := by
    intro n hn
    have hsub : ∀ p : PrimeSpectrum R, p.asIdeal = maximalIdeal R := by
      intro p
      refine le_antisymm (le_maximalIdeal p.2.ne_top) ?_
      rw [← hspan', Ideal.span_le, Set.singleton_subset_iff]
      exact p.2.mem_of_pow_mem n (by rw [hn]; exact p.asIdeal.zero_mem)
    have : Subsingleton (PrimeSpectrum R) :=
      ⟨fun p q => PrimeSpectrum.ext ((hsub p).trans (hsub q).symm)⟩
    have h0 : ringKrullDim R = 0 := Order.krullDim_eq_zero
    rw [hdim] at h0
    norm_num at h0
  -- every nonzero element is `π ^ n * unit`
  have hdec : ∀ a : R, a ≠ 0 → ∃ (n : ℕ) (u : R), IsUnit u ∧ a = π ^ n * u := by
    intro a ha
    have hex : ∃ k : ℕ, a ∉ maximalIdeal R ^ k := by
      by_contra! h
      apply ha
      have := Ideal.iInf_pow_eq_bot_of_isLocalRing (maximalIdeal R) (maximalIdeal.isMaximal R).ne_top
      rw [← Submodule.mem_bot R, ← this, Submodule.mem_iInf]
      exact h
    let k := Nat.find hex
    have hk : a ∉ maximalIdeal R ^ k := Nat.find_spec hex
    have hk0 : k ≠ 0 := by
      intro h0
      apply hk
      rw [h0, pow_zero, Ideal.one_eq_top]
      exact Submodule.mem_top
    obtain ⟨n, hn⟩ : ∃ n, k = n + 1 := Nat.exists_eq_succ_of_ne_zero hk0
    have hmem : a ∈ maximalIdeal R ^ n := by
      have := Nat.find_min hex (show n < k by omega)
      push Not at this
      exact this
    rw [← hspan', Ideal.span_singleton_pow, Ideal.mem_span_singleton'] at hmem
    obtain ⟨u, hu⟩ := hmem
    refine ⟨n, u, ?_, by rw [← hu, mul_comm]⟩
    by_contra hu'
    have hum : u ∈ maximalIdeal R := (mem_maximalIdeal u).2 hu'
    rw [← hspan', Ideal.mem_span_singleton'] at hum
    obtain ⟨w, hw⟩ := hum
    apply hk
    rw [hn, ← hspan', Ideal.span_singleton_pow, Ideal.mem_span_singleton']
    exact ⟨w, by rw [← hu, ← hw]; ring⟩
  have : NoZeroDivisors R := by
    refine ⟨fun {a b} hab => ?_⟩
    by_contra hne
    push Not at hne
    obtain ⟨n, u, hu, rfl⟩ := hdec a hne.1
    obtain ⟨m, v, hv, rfl⟩ := hdec b hne.2
    have : π ^ (n + m) * (u * v) = 0 := by rw [← hab]; ring
    exact hπ (n + m) ((hu.mul hv).mul_left_eq_zero.mp this)
  exact NoZeroDivisors.to_isDomain R

/-- **Two irreducible components meeting at a point with a domain stalk coincide.** -/
theorem irreducibleComponent_eq_of_isDomain_stalk {X : Scheme} {Z₁ Z₂ : Set X}
    (h₁ : Z₁ ∈ irreducibleComponents X) (h₂ : Z₂ ∈ irreducibleComponents X) {y : X}
    (hy₁ : y ∈ Z₁) (hy₂ : y ∈ Z₂) (hdom : IsDomain (X.presheaf.stalk y)) : Z₁ = Z₂ := by
  let G : Set X := Set.range (X.fromSpecStalk y)
  have hG : IsIrreducible G := by
    have : IrreducibleSpace (Spec (X.presheaf.stalk y)) := PrimeSpectrum.irreducibleSpace
    show IsIrreducible (Set.range (X.fromSpecStalk y))
    rw [← Set.image_univ]
    exact (IrreducibleSpace.isIrreducible_univ _).image _ (X.fromSpecStalk y).continuous.continuousOn
  have key : ∀ Z ∈ irreducibleComponents X, y ∈ Z → Z = closure G := by
    intro Z hZ hyZ
    have hcl : IsClosed Z := isClosed_of_mem_irreducibleComponents Z hZ
    have hgen := hZ.1.isGenericPoint_genericPoint hcl
    have hspec : hZ.1.genericPoint ⤳ y := by
      rw [specializes_iff_mem_closure, hgen.def]; exact hyZ
    have hmem : hZ.1.genericPoint ∈ G := by
      show _ ∈ Set.range (X.fromSpecStalk y)
      rw [Scheme.range_fromSpecStalk]; exact hspec
    have hsub : Z ⊆ closure G := by
      rw [← hgen.def]
      exact closure_mono (Set.singleton_subset_iff.2 hmem)
    exact (hZ.eq_of_subset hG.closure hsub)
  rw [key Z₁ h₁ hy₁, key Z₂ h₂ hy₂]

end CurveGlueCI

/-- **(CI), proved** (from infra-smooth-dim's stalk dimensions). -/
theorem componentIrreducible : ComponentIrreducible := by
  intro K _ X f hP hS x
  have : LocallyOfFiniteType f := inferInstance
  have : JacobsonSpace X := LocallyOfFiniteType.jacobsonSpace f
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  have : IsNoetherian X := { }
  have : SmoothOfRelativeDimension 1 f := hS
  -- stalks at closed points are domains
  have hdom : ∀ y : X, IsClosed ({y} : Set X) → IsDomain (X.presheaf.stalk y) := by
    intro y hy
    obtain ⟨h1, h2⟩ := InfraSmoothDim.stalk_dim_of_smoothOfRelativeDimension f 1 y hy
    exact CurveGlueCI.isDomain_of_dim_one (by exact_mod_cast h1) h2
  -- irreducible components are pairwise disjoint
  have hdisj : ∀ Z₁ ∈ irreducibleComponents X, ∀ Z₂ ∈ irreducibleComponents X,
      (Z₁ ∩ Z₂).Nonempty → Z₁ = Z₂ := by
    intro Z₁ h₁ Z₂ h₂ hne
    have hcl : IsClosed (Z₁ ∩ Z₂) :=
      (isClosed_of_mem_irreducibleComponents Z₁ h₁).inter (isClosed_of_mem_irreducibleComponents Z₂ h₂)
    obtain ⟨y, ⟨hy₁, hy₂⟩, hyc⟩ := nonempty_inter_closedPoints hne hcl.isLocallyClosed
    exact CurveGlueCI.irreducibleComponent_eq_of_isDomain_stalk h₁ h₂ hy₁ hy₂
      (hdom y (mem_closedPoints_iff.mp hyc))
  -- the irreducible component of `x` is clopen
  set Z := irreducibleComponent x with hZ
  have hZc : IsClosed Z := isClosed_irreducibleComponent
  have hZmem := irreducibleComponent_mem_irreducibleComponents x
  have hfin := TopologicalSpace.NoetherianSpace.finite_irreducibleComponents (α := X)
  have hcompl : Zᶜ = ⋃ Z' ∈ {Z' ∈ irreducibleComponents X | Z' ≠ Z}, Z' := by
    ext z
    simp only [Set.mem_compl_iff, Set.mem_iUnion, Set.mem_ofPred_eq, exists_prop]
    constructor
    · intro hz
      refine ⟨irreducibleComponent z, ⟨irreducibleComponent_mem_irreducibleComponents z, ?_⟩,
        mem_irreducibleComponent⟩
      intro h
      exact hz (h ▸ mem_irreducibleComponent)
    · rintro ⟨Z', ⟨hZ', hne⟩, hzZ'⟩ hzZ
      exact hne (hdisj Z' hZ' Z hZmem ⟨z, hzZ', hzZ⟩)
  have hZo : IsOpen Z := by
    rw [← isClosed_compl_iff, hcompl]
    exact (hfin.subset fun Z' hZ' => hZ'.1).isClosed_biUnion fun Z' hZ' =>
      isClosed_of_mem_irreducibleComponents Z' hZ'.1
  have h1 : connectedComponent x ⊆ Z :=
    (IsClopen.connectedComponent_subset ⟨hZc, hZo⟩ mem_irreducibleComponent)
  have h2 : Z ⊆ connectedComponent x :=
    isIrreducible_irreducibleComponent.isConnected.subset_connectedComponent mem_irreducibleComponent
  rw [Set.Subset.antisymm h1 h2]
  exact isIrreducible_irreducibleComponent

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

/-- **Both curve facts from (L0), (AD) and (IC)** ((CI) and C1b proved). -/
theorem curveFacts_of_L0_AD_IC (hL0 : FiniteGlobalSections) (hA : AlgDep) (hC : ImageClosed) :
    CurveRatFactor ∧ CurveSurj :=
  curveFacts_of_glue_AD smoothStalkDimOne (globalFunctionsConst_of hL0) componentIrreducible hA hC

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

/-- **Final result: the kernel's `MobiusGlue` from (L0) `FiniteGlobalSections`, (AD) `AlgDep`, (IC)
`ImageClosed` and T5 `ObjBridge.TorsionStructure`** ((CI) proved, `componentIrreducible`). -/
theorem mobiusGlue_of_L0_AD_IC_T5 (hL0 : FiniteGlobalSections) (hA : AlgDep) (hC : ImageClosed)
    (hT : ObjBridge.TorsionStructure) : MobiusGlue :=
  mobiusGlue_of_L0_CI_AD_IC_T5 hL0 componentIrreducible hA hC hT

/-- **Its CM-free form** (CM objects from the leaf bundle `R1R2fp`). -/
theorem mobiusGlueNoCM_of_L0_AD_IC_T5 (hL0 : FiniteGlobalSections) (hA : AlgDep)
    (hC : ImageClosed) (hT : ObjBridge.TorsionStructure) (h : R1R2fp) : MobiusGlueNoCM :=
  mobiusGlue_noCM_of (mobiusGlue_of_L0_AD_IC_T5 hL0 hA hC hT) h

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

/-! # image-plane additions (task image-plane, 2026-11-13)

Everything above is `scratch/curve-glue/MobiusFinal.lean` verbatim (its `#print axioms` lines
dropped). Below: `scratch/image-plane/IC.lean.part` ((IC) `ImageClosed` from properness),
`AD.lean.part` ((AD) `AlgDep`) and `C2Kproof.lean.part` (C2K from (CI)), then the end-to-end
theorems: (G1') `ImagePlaneCurveClosed` with no hypothesis, and the kernel's `MobiusGlue` from
the textbook leaf T5 alone. -/

noncomputable section

namespace LeafQM

namespace AV

namespace Pin

open CategoryTheory AlgebraicGeometry Limits Opposite TopologicalSpace
open PkgI3

/-! ## §IC `ImageClosed` from properness (task image-plane)

The graph of `(σ, ρ)` over the `K`-points of a closed `T ⊆ X` is cut out, inside
`X ×_K 𝔸²_K`, by the local equations `f_σ = x` (on `U_σ`), `x g_σ = 1` (on `V_σ`) and the same
for `ρ` with `y`. The resulting set is closed (the complement of a union of basic opens) and
its image under the projection to `𝔸²_K = Spec K[x][y]` is closed because `X → Spec K` is
universally closed. Closed points of the image come from `K`-points (Jacobson). -/

set_option linter.unusedSectionVars false

namespace ImagePlane

open Polynomial

section Gen

variable {K : Type} [Field K]

theorem ptOf_comp {X Y : Scheme.{0}} (q : Spec (CommRingCat.of K) ⟶ Y) (h : Y ⟶ X) :
    ptOf (q ≫ h) = h.base (ptOf q) := rfl

/-- Values commute with pullback of sections. -/
theorem ev_comp {X Y : Scheme.{0}} (q : Spec (CommRingCat.of K) ⟶ Y) (h : Y ⟶ X) {O : X.Opens}
    (hx : ptOf (q ≫ h) ∈ O) (s : Γ(X, O)) :
    ev (q ≫ h) hx s = ev q (show ptOf q ∈ h ⁻¹ᵁ O from hx) (h.app O s) := by
  simp only [ev, Scheme.evaluation, CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply]
  change (X.residue _ ≫ X.descResidueField (Scheme.stalkClosedPointTo (q ≫ h))).hom
      ((X.presheaf.germ O _ hx).hom s) =
    (Y.residue _ ≫ Y.descResidueField (Scheme.stalkClosedPointTo q)).hom
      ((Y.presheaf.germ (h ⁻¹ᵁ O) _ hx).hom (h.app O s))
  rw [Scheme.residue_descResidueField, Scheme.residue_descResidueField,
    Scheme.stalkClosedPointTo_comp]
  have key : ∀ (y : Y) (hy : h.base y ∈ O) (φ : Y.presheaf.stalk y ⟶ CommRingCat.of K),
      (h.stalkMap y ≫ φ).hom (X.presheaf.germ O (h.base y) hy s) =
        φ.hom (Y.presheaf.germ (h ⁻¹ᵁ O) y hy (h.app O s)) := by
    intro y hy φ
    rw [CommRingCat.hom_comp, RingHom.comp_apply, Scheme.Hom.germ_stalkMap_apply]
  exact key (ptOf q) hx _

/-- The value of a global function on an affine scheme at `Spec.map φ`. -/
theorem ev_spec_top {R : Type} [CommRing R] (φ : CommRingCat.of R ⟶ CommRingCat.of K) (Q : R) :
    ev (Spec.map φ) (show ptOf (Spec.map φ) ∈ (⊤ : (Spec (CommRingCat.of R)).Opens) from trivial)
      ((Scheme.ΓSpecIso (CommRingCat.of R)).inv Q) = φ Q := by
  rw [ev_top, ← ConcreteCategory.comp_apply, Scheme.ΓSpecIso_naturality]
  simp

/-- The point of `Spec.map φ` is the kernel of `φ`. -/
theorem ptOf_spec_asIdeal {R : Type} [CommRing R] (φ : CommRingCat.of R ⟶ CommRingCat.of K) :
    (ptOf (Spec.map φ)).asIdeal = RingHom.ker φ.hom := by
  change (PrimeSpectrum.comap φ.hom (IsLocalRing.closedPoint K)).asIdeal = _
  rw [PrimeSpectrum.comap_asIdeal]
  show Ideal.comap φ.hom (IsLocalRing.maximalIdeal K) = _
  rw [IsLocalRing.maximalIdeal_eq_bot]
  rfl

end Gen

variable {K : Type} [Field K]

/-- `𝔸²_K = Spec K[x][y] → Spec K`. -/
def g2 (K : Type) [Field K] : Spec (CommRingCat.of K[X][X]) ⟶ Spec (CommRingCat.of K) :=
  Spec.map (CommRingCat.ofHom (algebraMap K K[X][X]))

instance : LocallyOfFiniteType (g2 K) := by
  rw [g2, HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)]
  exact RingHom.finiteType_algebraMap.mpr inferInstance

/-- The coordinate functions `x = C X` and `y = X` on `𝔸²_K`. -/
def xc (K : Type) [Field K] : Γ(Spec (CommRingCat.of K[X][X]), ⊤) :=
  (Scheme.ΓSpecIso (CommRingCat.of K[X][X])).inv (C Polynomial.X)

def yc (K : Type) [Field K] : Γ(Spec (CommRingCat.of K[X][X]), ⊤) :=
  (Scheme.ΓSpecIso (CommRingCat.of K[X][X])).inv Polynomial.X

/-- `evalXYHom t u : K[x][y] → K`, `x ↦ t`, `y ↦ u`. -/
def eHom (t u : K) : K[X][X] →+* K := (evalRingHom u).comp (mapRingHom (evalRingHom t))

theorem eHom_apply (t u : K) (P : K[X][X]) : eHom t u P = Alg.evalXY t u P := rfl

theorem eHom_algebraMap (t u a : K) : eHom t u (algebraMap K K[X][X] a) = a := by
  simp [eHom, Polynomial.algebraMap_apply]

theorem eHom_x (t u : K) : eHom t u (C Polynomial.X) = t := by simp [eHom]

theorem eHom_y (t u : K) : eHom t u Polynomial.X = u := by simp [eHom]

/-- A ring hom `K[x][y] → K` over `K` is the evaluation at `(φ x, φ y)`; the kernel determines
the point. -/
theorem eq_of_ker_eq (φ : K[X][X] →+* K) (hφ : ∀ a : K, φ (algebraMap K K[X][X] a) = a)
    (t u : K) (hk : RingHom.ker φ = RingHom.ker (eHom t u)) :
    φ (C Polynomial.X) = t ∧ φ Polynomial.X = u := by
  have h1 : C Polynomial.X - algebraMap K K[X][X] t ∈ RingHom.ker (eHom t u) := by
    simp [RingHom.mem_ker, eHom]
  have h2 : Polynomial.X - algebraMap K K[X][X] u ∈ RingHom.ker (eHom t u) := by
    simp [RingHom.mem_ker, eHom]
  rw [← hk, RingHom.mem_ker, map_sub, hφ, sub_eq_zero] at h1 h2
  exact ⟨h1, h2⟩

section Main

variable [IsAlgClosed K] {X : Scheme.{0}} (f : X ⟶ Spec (CommRingCat.of K))

/-- `X ×_K 𝔸²_K`. -/
abbrev PB : Scheme.{0} := pullback f (g2 K)

/-- The coordinate `x` (resp. `y`) on `fst⁻¹ O ⊆ X ×_K 𝔸²`. -/
def xO (O : X.Opens) : Γ(PB f, (pullback.fst f (g2 K)) ⁻¹ᵁ O) :=
  res le_top ((pullback.snd f (g2 K)).appTop (xc K))

def yO (O : X.Opens) : Γ(PB f, (pullback.fst f (g2 K)) ⁻¹ᵁ O) :=
  res le_top ((pullback.snd f (g2 K)).appTop (yc K))

/-- The open set where the graph equations of `σ` (against the coordinate `c`) fail. -/
def bad (σ : ToP1 X) (c : ∀ O : X.Opens, Γ(PB f, (pullback.fst f (g2 K)) ⁻¹ᵁ O)) : (PB f).Opens :=
  (PB f).basicOpen ((pullback.fst f (g2 K)).app σ.U σ.f - c σ.U) ⊔
    (PB f).basicOpen (c σ.V * (pullback.fst f (g2 K)).app σ.V σ.g - 1)

/-- The graph of `(σ, ρ)` over `T`. -/
def graph (σ ρ : ToP1 X) (T : Set X) : Set (PB f) :=
  ((bad f σ (xO f) ⊔ bad f ρ (yO f) : (PB f).Opens) : Set (PB f))ᶜ ∩ (pullback.fst f (g2 K)).base ⁻¹' T

theorem isClosed_graph (σ ρ : ToP1 X) {T : Set X} (hT : IsClosed T) :
    IsClosed (graph f σ ρ T) :=
  (bad f σ (xO f) ⊔ bad f ρ (yO f)).isOpen.isClosed_compl.inter
    (hT.preimage (pullback.fst f (g2 K)).base.hom.continuous)

/-- Value of the pulled-back coordinate at a `K`-point of the fibre product. -/
theorem ev_xO (q : Spec (CommRingCat.of K) ⟶ PB f) (O : X.Opens)
    (hx : ptOf q ∈ (pullback.fst f (g2 K)) ⁻¹ᵁ O) :
    ev q hx (xO f O) = (Spec.preimage (q ≫ pullback.snd f (g2 K))).hom (C Polynomial.X) := by
  rw [xO, ev_res]
  have e := ev_comp q (pullback.snd f (g2 K)) (O := ⊤) trivial (xc K)
  rw [Scheme.Hom.appTop]
  refine e.symm.trans ?_
  conv_lhs => rw [← Spec.map_preimage (q ≫ pullback.snd f (g2 K))]
  exact ev_spec_top _ _

theorem ev_yO (q : Spec (CommRingCat.of K) ⟶ PB f) (O : X.Opens)
    (hx : ptOf q ∈ (pullback.fst f (g2 K)) ⁻¹ᵁ O) :
    ev q hx (yO f O) = (Spec.preimage (q ≫ pullback.snd f (g2 K))).hom Polynomial.X := by
  rw [yO, ev_res]
  have e := ev_comp q (pullback.snd f (g2 K)) (O := ⊤) trivial (yc K)
  rw [Scheme.Hom.appTop]
  refine e.symm.trans ?_
  conv_lhs => rw [← Spec.map_preimage (q ≫ pullback.snd f (g2 K))]
  exact ev_spec_top _ _

/-- A `K`-point of the fibre product avoids `bad σ c` iff `σ` takes the finite value `a`
there, where `a` is the value of the coordinate `c`. -/
theorem not_mem_bad_iff (σ : ToP1 X) (c : ∀ O : X.Opens, Γ(PB f, (pullback.fst f (g2 K)) ⁻¹ᵁ O))
    (a : K) (q : Spec (CommRingCat.of K) ⟶ PB f)
    (hc : ∀ (O : X.Opens) (hx : ptOf q ∈ (pullback.fst f (g2 K)) ⁻¹ᵁ O), ev q hx (c O) = a) :
    ptOf q ∉ bad f σ c ↔ σ.val (q ≫ pullback.fst f (g2 K)) = OnePoint.some a := by
  set p := q ≫ pullback.fst f (g2 K) with hpdef
  have hU : ∀ (hx : ptOf q ∈ (pullback.fst f (g2 K)) ⁻¹ᵁ σ.U),
      ev q hx ((pullback.fst f (g2 K)).app σ.U σ.f - c σ.U) = ev p hx σ.f - a := by
    intro hx
    rw [map_sub, hc, ← ev_comp q (pullback.fst f (g2 K)) hx σ.f]
  have hV : ∀ (hx : ptOf q ∈ (pullback.fst f (g2 K)) ⁻¹ᵁ σ.V),
      ev q hx (c σ.V * (pullback.fst f (g2 K)).app σ.V σ.g - 1) = a * ev p hx σ.g - 1 := by
    intro hx
    rw [map_sub, map_mul, map_one, hc, ← ev_comp q (pullback.fst f (g2 K)) hx σ.g]
  constructor
  · intro hq
    by_cases hpU : ptOf p ∈ σ.U
    · rw [val_of_mem σ p hpU]
      have h0 : ptOf q ∉ (PB f).basicOpen ((pullback.fst f (g2 K)).app σ.U σ.f - c σ.U) :=
        fun h => hq (Or.inl h)
      rw [← ev_eq_zero_iff q (show ptOf q ∈ (pullback.fst f (g2 K)) ⁻¹ᵁ σ.U from hpU), hU] at h0
      rw [sub_eq_zero.mp h0]
    · exfalso
      have hpV := mem_V_of_not_mem_U σ hpU
      have h0 : ptOf q ∉ (PB f).basicOpen (c σ.V * (pullback.fst f (g2 K)).app σ.V σ.g - 1) :=
        fun h => hq (Or.inr h)
      rw [← ev_eq_zero_iff q (show ptOf q ∈ (pullback.fst f (g2 K)) ⁻¹ᵁ σ.V from hpV), hV,
        ev_g_eq_zero σ p hpV hpU] at h0
      simp at h0
  · intro hv hq
    have hpU : ptOf p ∈ σ.U := by
      by_contra h'
      rw [val_of_not_mem σ p h'] at hv
      exact OnePoint.infty_ne_coe a hv
    rw [val_of_mem σ p hpU] at hv
    have hfa : ev p hpU σ.f = a := OnePoint.coe_injective hv
    rcases hq with h | h
    · have hx : ptOf q ∈ (pullback.fst f (g2 K)) ⁻¹ᵁ σ.U := Scheme.basicOpen_le _ _ h
      refine (ev_eq_zero_iff q hx _).1 ?_ h
      rw [hU, hfa, sub_self]
    · have hx : ptOf q ∈ (pullback.fst f (g2 K)) ⁻¹ᵁ σ.V := Scheme.basicOpen_le _ _ h
      refine (ev_eq_zero_iff q hx _).1 ?_ h
      rw [hV, ← hfa, ev_f_mul_g σ p hpU hx, sub_self]

/-- **The image of the `K`-points of a closed `T` under `(σ, ρ)`, intersected with `K²`, is
Zariski closed**, for `X` proper over `K = K̄`. -/
theorem image_closed (hP : IsProper f) (σ ρ : ToP1 X) {T : Set X} (hT : IsClosed T) :
    ∃ S : Set K[X][X], ∀ t u : K,
      (∃ p : Spec (CommRingCat.of K) ⟶ X, p ≫ f = 𝟙 _ ∧ ptOf p ∈ T ∧
        σ.val p = OnePoint.some t ∧ ρ.val p = OnePoint.some u) ↔
      ∀ Q ∈ S, Alg.evalXY t u Q = 0 := by
  classical
  have := hP
  have : JacobsonSpace (PB f) := LocallyOfFiniteType.jacobsonSpace (pullback.fst f (g2 K) ≫ f)
  set Z := graph f σ ρ T with hZ
  let C : Set (PrimeSpectrum K[X][X]) := (pullback.snd f (g2 K)).base '' Z
  have hC : IsClosed C := (pullback.snd f (g2 K)).isClosedMap _ (isClosed_graph f σ ρ hT)
  refine ⟨(PrimeSpectrum.vanishingIdeal C : Set K[X][X]), fun t u => ?_⟩
  let φ : CommRingCat.of K[X][X] ⟶ CommRingCat.of K := CommRingCat.ofHom (eHom t u)
  let m : PrimeSpectrum K[X][X] := ptOf (Spec.map φ)
  have hmI : m.asIdeal = RingHom.ker (eHom t u) := ptOf_spec_asIdeal φ
  -- membership of `m` in `C`, algebraically
  have hmC : m ∈ C ↔ ∀ Q ∈ (PrimeSpectrum.vanishingIdeal C : Set K[X][X]),
      Alg.evalXY t u Q = 0 := by
    have e : m ∈ C ↔ m ∈ PrimeSpectrum.zeroLocus (PrimeSpectrum.vanishingIdeal C : Set K[X][X]) := by
      rw [PrimeSpectrum.zeroLocus_vanishingIdeal_eq_closure, hC.closure_eq]
    rw [e, PrimeSpectrum.mem_zeroLocus, hmI]
    exact ⟨fun h Q hQ => h hQ, fun h Q hQ => h Q hQ⟩
  rw [← hmC]
  constructor
  · rintro ⟨p, hp, hpT, hσ, hρ⟩
    have w : p ≫ f = Spec.map φ ≫ g2 K := by
      rw [hp, g2, ← Spec.map_comp, ← Spec.map_id]
      congr 1
      ext a
      exact (eHom_algebraMap t u a).symm
    set q := pullback.lift p (Spec.map φ) w with hq
    have hqs : q ≫ pullback.snd f (g2 K) = Spec.map φ := pullback.lift_snd _ _ _
    have hqf : q ≫ pullback.fst f (g2 K) = p := pullback.lift_fst _ _ _
    have hpre : Spec.preimage (q ≫ pullback.snd f (g2 K)) = φ := by
      rw [hqs, Spec.preimage_map]
    refine ⟨ptOf q, ⟨?_, ?_⟩, ?_⟩
    · rintro (h | h)
      · refine ((not_mem_bad_iff f σ (xO f) t q fun O hx => ?_).2 (hqf ▸ hσ)) h
        rw [ev_xO, hpre]; exact eHom_x t u
      · refine ((not_mem_bad_iff f ρ (yO f) u q fun O hx => ?_).2 (hqf ▸ hρ)) h
        rw [ev_yO, hpre]; exact eHom_y t u
    · show ptOf (q ≫ pullback.fst f (g2 K)) ∈ T
      rw [hqf]; exact hpT
    · show ptOf (q ≫ pullback.snd f (g2 K)) = m
      rw [hqs]
  · rintro ⟨z, hzZ, hzm⟩
    have hmax : m.asIdeal.IsMaximal := by
      rw [hmI]
      exact RingHom.ker_isMaximal_of_surjective _ fun a => ⟨algebraMap K K[X][X] a, eHom_algebraMap t u a⟩
    have hmcl : IsClosed ({m} : Set (PrimeSpectrum K[X][X])) :=
      (PrimeSpectrum.isClosed_singleton_iff_isMaximal m).2 hmax
    have hYcl : IsClosed (Z ∩ (pullback.snd f (g2 K)).base ⁻¹' {m}) :=
      (isClosed_graph f σ ρ hT).inter (hmcl.preimage (pullback.snd f (g2 K)).base.hom.continuous)
    obtain ⟨q, hq, hqY⟩ := exists_point_of_isLocallyClosed (pullback.fst f (g2 K) ≫ f)
      hYcl.isLocallyClosed ⟨z, hzZ, hzm⟩
    set p := q ≫ pullback.fst f (g2 K) with hpdef
    have hp : p ≫ f = 𝟙 _ := by rw [hpdef, Category.assoc]; exact hq
    set ψ := Spec.preimage (q ≫ pullback.snd f (g2 K)) with hψ
    have hψg : ∀ a : K, ψ.hom (algebraMap K K[X][X] a) = a := by
      have e : Spec.map ψ ≫ g2 K = 𝟙 _ := by
        rw [hψ, Spec.map_preimage, Category.assoc, ← pullback.condition, ← Category.assoc]
        exact hq
      rw [g2, ← Spec.map_comp, ← Spec.map_id] at e
      have e' := Spec.map_injective e
      intro a
      exact congrArg (fun χ : CommRingCat.of K ⟶ CommRingCat.of K => χ.hom a) e'
    have hker : RingHom.ker ψ.hom = RingHom.ker (eHom t u) := by
      rw [← ptOf_spec_asIdeal ψ, ← hmI, hψ, Spec.map_preimage, ptOf_comp]
      exact congrArg PrimeSpectrum.asIdeal hqY.2
    obtain ⟨hx, hy⟩ := eq_of_ker_eq ψ.hom hψg t u hker
    refine ⟨p, hp, hqY.1.2, ?_, ?_⟩
    · refine (not_mem_bad_iff f σ (xO f) t q fun O hO => ?_).1 fun h => hqY.1.1 (Or.inl h)
      rw [ev_xO]; exact hx
    · refine (not_mem_bad_iff f ρ (yO f) u q fun O hO => ?_).1 fun h => hqY.1.1 (Or.inr h)
      rw [ev_yO]; exact hy

end Main

end ImagePlane

/-- **(IC) `ImageClosed` holds** (task image-plane): from `IsProper f` alone (Mathlib's
`UniversallyClosed`, `Scheme.Hom.isClosedMap`, Jacobson). Smoothness is not used. -/
theorem imageClosed : ImageClosed := by
  intro K _ _ X f hP _ σ ρ p₀ _
  obtain ⟨S, hS⟩ := ImagePlane.image_closed f hP σ ρ (isClosed_connectedComponent (x := ptOf p₀))
  refine ⟨S, fun t u => (Iff.trans ?_ (hS t u))⟩
  refine exists_congr fun p => and_congr_right fun _ => and_congr_left fun _ => ?_
  exact ⟨fun h => h ▸ mem_connectedComponent, fun h => (connectedComponent_eq h).symm⟩

/-! ## §AD `AlgDep` from C2K, (CI), (C1b) and the closed image (task image-plane)

If `σ` is constant on the `K`-points of the component `W`, take `P = x − c` (or `P = 1`).
Otherwise `σ` is onto (C2K); the locus `W ∩ {σ = 0} = W \ V_σ` is a proper closed subset of the
irreducible (CI) set `W`, hence finite: an irreducible closed `Y' ⊊ W` with a closed point
`x ≠ η(Y')` gives a chain `x < η(Y') < η(W)` of generizations, so `dim 𝒪_{X,x} ≥ 2`, against
(C1b). So only finitely many `u` have `(0, u)` in the affine image; for any other `u` some
`Q ∈ S` (the closed-image equations of `ImagePlane.image_closed`) has `Q(0, u) ≠ 0`, and
`P = Q`. -/

namespace ImagePlane

open Polynomial

/-- In a Noetherian scheme whose closed points have local rings of dimension `1`, a proper closed
subset of an irreducible closed set is finite. -/
theorem finite_of_closed_ssubset {X : Scheme.{0}} [TopologicalSpace.NoetherianSpace X]
    (hdim : ∀ x : X, IsClosed ({x} : Set X) → ringKrullDim (X.presheaf.stalk x) = 1)
    {W : Set X} (hW : IsIrreducible W) (hWc : IsClosed W) {Y : Set X} (hY : IsClosed Y)
    (hYW : Y ⊆ W) (hne : Y ≠ W) : Y.Finite := by
  classical
  -- irreducible closed proper subsets of `W` are points
  have key : ∀ Y' : Set X, IsIrreducible Y' → IsClosed Y' → Y' ⊆ W → Y' ≠ W →
      Y' ⊆ {hW.genericPoint} ∨ Y'.Subsingleton := by
    intro Y' hY' hY'c hY'W hY'ne
    right
    have hη : closure ({hY'.genericPoint} : Set X) = Y' := by
      have := hY'.isGenericPoint_genericPoint_closure
      rw [hY'c.closure_eq] at this
      exact this
    have hξ : closure ({hW.genericPoint} : Set X) = W := by
      have := hW.isGenericPoint_genericPoint_closure
      rw [hWc.closure_eq] at this
      exact this
    set η := hY'.genericPoint
    set ξ := hW.genericPoint
    -- every closed point of `Y'` is `η`
    have hcl : ∀ x ∈ Y', IsClosed ({x} : Set X) → x = η := by
      intro x hx hxc
      by_contra hxη
      have h1 : x < η := by
        have hle : x ≤ η := specializes_iff_mem_closure.mpr (hη ▸ hx)
        refine lt_of_le_not_ge hle fun hge => hxη ?_
        have hmem : η ∈ closure ({x} : Set X) := specializes_iff_mem_closure.mp hge
        rw [hxc.closure_eq] at hmem
        exact hmem.symm
      have h2 : η < ξ := by
        have hle : η ≤ ξ := specializes_iff_mem_closure.mpr (hξ ▸ hY'W (hη ▸ subset_closure rfl))
        refine lt_of_le_not_ge hle fun hge => hY'ne ?_
        have hmem : ξ ∈ closure ({η} : Set X) := specializes_iff_mem_closure.mp hge
        rw [hη] at hmem
        refine le_antisymm hY'W ?_
        rw [← hξ]
        exact closure_minimal (Set.singleton_subset_iff.2 hmem) hY'c
      have c1 := Order.coheight_add_one_le h1
      have c2 := Order.coheight_add_one_le h2
      have h3 : (2 : ℕ∞) ≤ Order.coheight x := by
        calc (2 : ℕ∞) = 0 + 1 + 1 := by norm_num
          _ ≤ Order.coheight ξ + 1 + 1 := by gcongr; exact zero_le
          _ ≤ Order.coheight η + 1 := by gcongr
          _ ≤ Order.coheight x := c1
      have h4 := hdim x hxc
      rw [ringKrullDim_stalk_eq_coheight] at h4
      have h5 : Order.coheight x = 1 := by exact_mod_cast h4
      rw [h5] at h3
      exact absurd h3 (by decide)
    intro a ha b hb
    obtain ⟨x, hx, hxc⟩ := (hY'c.inter isClosed_closure : IsClosed (Y' ∩ closure {a})).exists_closed_singleton
      ⟨a, ha, subset_closure rfl⟩
    have hxη := hcl x hx.1 hxc
    have hY'x : Y' = {x} := by
      rw [← hη, ← hxη, hxc.closure_eq]
    rw [hY'x] at ha hb
    exact ha.trans hb.symm
  obtain ⟨T, hT, hTe⟩ := TopologicalSpace.NoetherianSpace.exists_finset_irreducible ⟨Y, hY⟩
  have hYe : Y = ⋃ k ∈ T, (k : Set X) := by
    have := congrArg (fun c : TopologicalSpace.Closeds X => (c : Set X)) hTe
    simpa [TopologicalSpace.Closeds.coe_finset_sup] using this
  rw [hYe]
  refine T.finite_toSet.biUnion fun k hk => ?_
  have hkY : (k : Set X) ⊆ Y := by rw [hYe]; exact Set.subset_biUnion_of_mem (u := fun k : TopologicalSpace.Closeds X => (k : Set X)) hk
  have hkne : (k : Set X) ≠ W := fun e => hne (le_antisymm hYW (e ▸ hkY))
  rcases key k (hT ⟨k, hk⟩) k.isClosed (hkY.trans hYW) hkne with h | h
  · exact (Set.finite_singleton _).subset h
  · exact h.finite

variable {K : Type} [Field K] {X : Scheme.{0}}

/-- A finite value of `ρ` at a `K`-point depends only on the underlying point. -/
theorem val_eq_of_ptOf_eq (f : X ⟶ Spec (CommRingCat.of K)) (ρ : ToP1 X)
    {p p' : Spec (CommRingCat.of K) ⟶ X} (hp : p ≫ f = 𝟙 _) (hp' : p' ≫ f = 𝟙 _)
    (h : ptOf p = ptOf p') {u u' : K} (hu : ρ.val p = OnePoint.some u)
    (hu' : ρ.val p' = OnePoint.some u') : u = u' := by
  have memU : ∀ (q : Spec (CommRingCat.of K) ⟶ X) (t : K),
      ρ.val q = OnePoint.some t → ptOf q ∈ ρ.U := by
    intro q t h
    by_contra h'
    rw [val_of_not_mem ρ q h'] at h
    exact OnePoint.infty_ne_coe t h
  have hU := memU p u hu
  have hU' := memU p' u' hu'
  rw [val_of_mem ρ p hU] at hu
  rw [val_of_mem ρ p' hU'] at hu'
  have e : ev p hU (ρ.f - cst f ρ.U u) = 0 := by
    rw [map_sub, ev_cst f p hp, OnePoint.coe_injective hu, sub_self]
  rw [ev_eq_zero_iff, h] at e
  rw [← ev_eq_zero_iff p' hU', map_sub, ev_cst f p' hp', OnePoint.coe_injective hu'] at e
  exact (sub_eq_zero.mp e).symm

end ImagePlane

open Polynomial in
/-- **(AD) `AlgDep` from C1b (`SmoothStalkDimOne`, proved by infra-smooth-dim), C2K and (CI)**
(task image-plane). -/
theorem algDep_of (h1 : SmoothStalkDimOne) (h2 : ConstOrOntoAlgClosed)
    (hI : ComponentIrreducible) : AlgDep := by
  classical
  intro K _ _ X f hP hS σ ρ p₀ hp₀
  have : LocallyOfFiniteType f := inferInstance
  have : JacobsonSpace X := LocallyOfFiniteType.jacobsonSpace f
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  have : IsNoetherian X := { }
  set x₀ := ptOf p₀ with hx₀
  set W := connectedComponent x₀ with hWdef
  have memW : ∀ p : Spec (CommRingCat.of K) ⟶ X, ptOf p ∈ W ↔
      connectedComponent (ptOf p) = connectedComponent x₀ :=
    fun p => ⟨fun h => (connectedComponent_eq h).symm,
      fun h => by
        show ptOf p ∈ connectedComponent x₀
        rw [← h]; exact mem_connectedComponent⟩
  obtain ⟨S, hSc⟩ := ImagePlane.image_closed f hP σ ρ (isClosed_connectedComponent (x := x₀))
  by_cases hcst : ∀ p : Spec (CommRingCat.of K) ⟶ X, p ≫ f = 𝟙 _ →
      connectedComponent (ptOf p) = connectedComponent (ptOf p₀) → σ.val p = σ.val p₀
  · induction hv : σ.val p₀ using OnePoint.rec with
    | infty =>
      refine ⟨1, one_ne_zero, fun p hp hpc t u ht _ => ?_⟩
      rw [hcst p hp hpc, hv] at ht
      exact absurd ht (OnePoint.infty_ne_coe t)
    | coe c =>
      refine ⟨C (Polynomial.X - C c), ?_, fun p hp hpc t u ht _ => ?_⟩
      · exact C_ne_zero.mpr (X_sub_C_ne_zero c)
      · rw [hcst p hp hpc, hv] at ht
        have htc : t = c := (OnePoint.coe_injective ht).symm
        simp [Alg.evalXY, htc]
  push Not at hcst
  obtain ⟨pn, hpn, hpnc, hpnv⟩ := hcst
  have honto : ∀ t : OnePoint K, ∃ p : Spec (CommRingCat.of K) ⟶ X, p ≫ f = 𝟙 _ ∧
      connectedComponent (ptOf p) = connectedComponent (ptOf p₀) ∧ σ.val p = t := by
    rcases h2 K X f hP hS σ p₀ hp₀ with hc | ho
    · exact absurd (hc pn hpn hpnc) hpnv
    · exact ho
  -- the zero locus `Y = W \ V_σ` of `σ` on `W` is finite
  set Y : Set X := W ∩ ((σ.V : Set X))ᶜ with hYdef
  have hYc : IsClosed Y := isClosed_connectedComponent.inter σ.V.isOpen.isClosed_compl
  obtain ⟨p₁, hp₁, hp₁c, hp₁v⟩ := honto (OnePoint.some 1)
  have hp₁U : ptOf p₁ ∈ σ.U := by
    by_contra h'
    rw [val_of_not_mem σ p₁ h'] at hp₁v
    exact OnePoint.infty_ne_coe 1 hp₁v
  have hp₁V : ptOf p₁ ∈ σ.V := by
    rw [val_of_mem σ p₁ hp₁U] at hp₁v
    have e1 : ev p₁ hp₁U σ.f ≠ 0 := by rw [OnePoint.coe_injective hp₁v]; exact one_ne_zero
    rw [Ne, ev_eq_zero_iff, not_not, σ.basicOpen_f] at e1
    exact e1.2
  have hYne : Y ≠ W := by
    intro e
    have : ptOf p₁ ∈ Y := e ▸ (memW p₁).2 hp₁c
    exact this.2 hp₁V
  have hYfin : Y.Finite := ImagePlane.finite_of_closed_ssubset
    (fun x hx => h1 K X f hS x hx) (hI K X f hP hS x₀) isClosed_connectedComponent hYc
    Set.inter_subset_left hYne
  -- only finitely many `u` with `(0, u)` in the affine image
  set Us : Set K := {u | ∃ p : Spec (CommRingCat.of K) ⟶ X, p ≫ f = 𝟙 _ ∧ ptOf p ∈ W ∧
    σ.val p = OnePoint.some 0 ∧ ρ.val p = OnePoint.some u} with hUs
  have hUsfin : Us.Finite := by
    refine (hYfin.biUnion fun x _ => (show ({u | ∃ p : Spec (CommRingCat.of K) ⟶ X,
        p ≫ f = 𝟙 _ ∧ ptOf p = x ∧ ρ.val p = OnePoint.some u} : Set K).Subsingleton from ?_).finite).subset ?_
    · rintro u ⟨p, hp, hpx, hpu⟩ u' ⟨p', hp', hpx', hpu'⟩
      exact ImagePlane.val_eq_of_ptOf_eq f ρ hp hp' (hpx.trans hpx'.symm) hpu hpu'
    · rintro u ⟨p, hp, hpW, hp0, hpu⟩
      have hpU : ptOf p ∈ σ.U := by
        by_contra h'
        rw [val_of_not_mem σ p h'] at hp0
        exact OnePoint.infty_ne_coe 0 hp0
      have hpV : ptOf p ∉ σ.V := by
        intro hpV
        rw [val_of_mem σ p hpU] at hp0
        have e0 : ev p hpU σ.f = 0 := OnePoint.coe_injective hp0
        rw [ev_eq_zero_iff, σ.basicOpen_f] at e0
        exact e0 ⟨hpU, hpV⟩
      exact Set.mem_biUnion (x := ptOf p) ⟨hpW, hpV⟩ ⟨p, hp, rfl, hpu⟩
  have : Infinite K := inferInstance
  obtain ⟨u, hu⟩ := hUsfin.infinite_compl.nonempty
  have hnot : ¬ ∀ Q ∈ S, Alg.evalXY 0 u Q = 0 := by
    intro h
    obtain ⟨p, hp, hpc, hp0, hpu⟩ := (hSc 0 u).2 h
    exact hu ⟨p, hp, hpc, hp0, hpu⟩
  push Not at hnot
  obtain ⟨Q, hQS, hQ0⟩ := hnot
  refine ⟨Q, fun e => hQ0 (by rw [e]; simp [Alg.evalXY]), fun p hp hpc t u' ht hu' => ?_⟩
  exact (hSc t u').1 ⟨p, hp, (memW p).2 hpc, ht, hu'⟩ Q hQS

/-! ## §C2K `ConstOrOntoAlgClosed` from (CI) and the closed image (task image-plane)

With `ρ = σ`, the closed image gives: the finite values of `σ` on the `K`-points of a closed `T`
form a Zariski closed subset of `K` (the diagonal section of the equations), so a finite set or
all of `K`. If finite, the loci `{σ = t}` (closed: complements of two basic opens) and
`{σ = ∞} = X \ U` cover the irreducible (CI) component `W` (Jacobson), so one of them contains
`W`: `σ` is constant. Applying this also to `1/σ` (swap the charts) gives "constant or onto".
No leaf is used (in particular not (L0)). -/

namespace ImagePlane

open Polynomial

variable {K : Type} [Field K] {X : Scheme.{0}}

/-- The reciprocal `1/σ` (the charts swapped). -/
def inv (σ : ToP1 X) : ToP1 X where
  U := σ.V
  V := σ.U
  cover := by rw [sup_comm]; exact σ.cover
  f := σ.g
  g := σ.f
  inv := by
    have h : σ.V ⊓ σ.U ≤ σ.U ⊓ σ.V := le_of_eq (inf_comm _ _)
    have e : res h (res (inf_le_left : σ.U ⊓ σ.V ≤ σ.U) σ.f *
        res (inf_le_right : σ.U ⊓ σ.V ≤ σ.V) σ.g) = res h 1 := congrArg _ σ.inv
    rw [map_mul, map_one, res_res, res_res] at e
    change res _ σ.g * res _ σ.f = 1
    rw [mul_comm]
    exact e
  basicOpen_f := by rw [σ.basicOpen_g, inf_comm]
  basicOpen_g := by rw [σ.basicOpen_f, inf_comm]

open scoped Classical in
/-- `v ↦ 1/v` on `P¹(K)`. -/
def recip (v : OnePoint K) : OnePoint K :=
  match v with
  | none => some 0
  | some s => if s = 0 then none else some s⁻¹

theorem recip_infty : recip (OnePoint.infty : OnePoint K) = OnePoint.some 0 := rfl

open scoped Classical in
theorem recip_coe (s : K) :
    recip (OnePoint.some s) = if s = 0 then OnePoint.infty else OnePoint.some s⁻¹ := rfl

theorem val_eq_recip (σ : ToP1 X) (p : Spec (CommRingCat.of K) ⟶ X) :
    σ.val p = recip ((inv σ).val p) := by
  by_cases hU : ptOf p ∈ σ.U
  · by_cases hV : ptOf p ∈ σ.V
    · have h2 : (inv σ).val p = OnePoint.some (ev p hV σ.g) := val_of_mem (inv σ) p hV
      rw [val_of_mem σ p hU, h2, recip_coe]
      have e := ev_f_mul_g σ p hU hV
      have hg : ev p hV σ.g ≠ 0 := right_ne_zero_of_mul_eq_one e
      rw [if_neg hg]
      exact congrArg _ (eq_inv_of_mul_eq_one_left e)
    · have h2 : (inv σ).val p = OnePoint.infty := val_of_not_mem (inv σ) p hV
      rw [val_of_mem σ p hU, h2, recip_infty]
      have : ev p hU σ.f = 0 := by
        rw [ev_eq_zero_iff, σ.basicOpen_f]; exact fun h => hV h.2
      rw [this]
  · have hV := mem_V_of_not_mem_U σ hU
    have h2 : (inv σ).val p = OnePoint.some (ev p hV σ.g) := val_of_mem (inv σ) p hV
    rw [val_of_not_mem σ p hU, h2, recip_coe, ev_g_eq_zero σ p hV hU, if_pos rfl]

/-- The open set where `σ ≠ a`. -/
def badX (f : X ⟶ Spec (CommRingCat.of K)) (σ : ToP1 X) (a : K) : X.Opens :=
  X.basicOpen (σ.f - cst f σ.U a) ⊔ X.basicOpen (cst f σ.V a * σ.g - 1)

theorem not_mem_badX_iff (f : X ⟶ Spec (CommRingCat.of K)) (σ : ToP1 X) (a : K)
    (p : Spec (CommRingCat.of K) ⟶ X) (hp : p ≫ f = 𝟙 _) :
    ptOf p ∉ badX f σ a ↔ σ.val p = OnePoint.some a := by
  have hU : ∀ (hx : ptOf p ∈ σ.U), ev p hx (σ.f - cst f σ.U a) = ev p hx σ.f - a := by
    intro hx; rw [map_sub, ev_cst f p hp]
  have hV : ∀ (hx : ptOf p ∈ σ.V), ev p hx (cst f σ.V a * σ.g - 1) = a * ev p hx σ.g - 1 := by
    intro hx; rw [map_sub, map_mul, map_one, ev_cst f p hp]
  constructor
  · intro hq
    by_cases hpU : ptOf p ∈ σ.U
    · rw [val_of_mem σ p hpU]
      have h0 : ptOf p ∉ X.basicOpen (σ.f - cst f σ.U a) := fun h => hq (Or.inl h)
      rw [← ev_eq_zero_iff p hpU, hU] at h0
      rw [sub_eq_zero.mp h0]
    · exfalso
      have hpV := mem_V_of_not_mem_U σ hpU
      have h0 : ptOf p ∉ X.basicOpen (cst f σ.V a * σ.g - 1) := fun h => hq (Or.inr h)
      rw [← ev_eq_zero_iff p hpV, hV, ev_g_eq_zero σ p hpV hpU] at h0
      simp at h0
  · intro hv hq
    have hpU : ptOf p ∈ σ.U := by
      by_contra h'
      rw [val_of_not_mem σ p h'] at hv
      exact OnePoint.infty_ne_coe a hv
    rw [val_of_mem σ p hpU] at hv
    have hfa : ev p hpU σ.f = a := OnePoint.coe_injective hv
    rcases hq with h | h
    · have hx : ptOf p ∈ σ.U := X.basicOpen_le _ h
      refine (ev_eq_zero_iff p hx _).1 ?_ h
      rw [hU, hfa, sub_self]
    · have hx : ptOf p ∈ σ.V := X.basicOpen_le _ h
      refine (ev_eq_zero_iff p hx _).1 ?_ h
      rw [hV, ← hfa, ev_f_mul_g σ p hpU hx, sub_self]

theorem eval_diag (Q : K[X][X]) (t : K) : (Q.eval Polynomial.X).eval t = Alg.evalXY t t Q := by
  induction Q using Polynomial.induction_on' with
  | add p q hp hq => simp only [eval_add, hp, hq, Alg.evalXY, Polynomial.map_add]
  | monomial n a => simp [Alg.evalXY]

/-- The finite values of `σ` on the `K`-points of a closed `T` form a finite set or all of `K`. -/
theorem image_finite_or_univ [IsAlgClosed K] (f : X ⟶ Spec (CommRingCat.of K)) (hP : IsProper f)
    (σ : ToP1 X) {T : Set X} (hT : IsClosed T) :
    {t : K | ∃ p : Spec (CommRingCat.of K) ⟶ X, p ≫ f = 𝟙 _ ∧ ptOf p ∈ T ∧
      σ.val p = OnePoint.some t}.Finite ∨
    ∀ t : K, ∃ p : Spec (CommRingCat.of K) ⟶ X, p ≫ f = 𝟙 _ ∧ ptOf p ∈ T ∧
      σ.val p = OnePoint.some t := by
  classical
  obtain ⟨S, hS⟩ := image_closed f hP σ σ hT
  have hdiag : ∀ t : K, (∃ p : Spec (CommRingCat.of K) ⟶ X, p ≫ f = 𝟙 _ ∧ ptOf p ∈ T ∧
      σ.val p = OnePoint.some t) ↔ ∀ Q ∈ S, (Q.eval Polynomial.X).eval t = 0 := by
    intro t
    simp_rw [eval_diag]
    rw [← hS t t]
    exact ⟨fun ⟨p, hp, hpT, h⟩ => ⟨p, hp, hpT, h, h⟩, fun ⟨p, hp, hpT, h, _⟩ => ⟨p, hp, hpT, h⟩⟩
  by_cases h : ∀ Q ∈ S, Q.eval Polynomial.X = 0
  · right
    intro t
    exact (hdiag t).2 fun Q hQ => by rw [h Q hQ, eval_zero]
  · left
    push Not at h
    obtain ⟨Q, hQ, hQ0⟩ := h
    refine (Q.eval Polynomial.X).roots.toFinset.finite_toSet.subset fun t ht => ?_
    simp only [Finset.mem_coe, Multiset.mem_toFinset, mem_roots hQ0, IsRoot.def]
    exact (hdiag t).1 ht Q hQ

/-- Finitely many finite values on an irreducible closed set force a constant value. -/
theorem const_of_finite [IsAlgClosed K] (f : X ⟶ Spec (CommRingCat.of K)) [LocallyOfFiniteType f]
    [JacobsonSpace X] (σ : ToP1 X) {W : Set X} (hW : IsIrreducible W) (hWc : IsClosed W)
    (hfin : {t : K | ∃ p : Spec (CommRingCat.of K) ⟶ X, p ≫ f = 𝟙 _ ∧ ptOf p ∈ W ∧
      σ.val p = OnePoint.some t}.Finite) :
    ∃ v : OnePoint K, ∀ p : Spec (CommRingCat.of K) ⟶ X, p ≫ f = 𝟙 _ → ptOf p ∈ W →
      σ.val p = v := by
  classical
  set Fs := hfin.toFinset with hFs
  let fam : Finset (Set X) :=
    insert ((σ.U : Set X)ᶜ) (Fs.image fun t => ((badX f σ t : X.Opens) : Set X)ᶜ)
  have hcl : ∀ z ∈ fam, IsClosed z := by
    intro z hz
    rcases Finset.mem_insert.1 hz with rfl | hz
    · exact σ.U.isOpen.isClosed_compl
    · obtain ⟨t, -, rfl⟩ := Finset.mem_image.1 hz
      exact (badX f σ t).isOpen.isClosed_compl
  have hmem : ∀ p : Spec (CommRingCat.of K) ⟶ X, p ≫ f = 𝟙 _ → ptOf p ∈ W →
      ∃ z ∈ fam, ptOf p ∈ z := by
    intro p hp hpW
    induction hv : σ.val p using OnePoint.rec with
    | infty =>
      refine ⟨(σ.U : Set X)ᶜ, Finset.mem_insert_self _ _, fun hU => ?_⟩
      rw [val_of_mem σ p hU] at hv
      exact OnePoint.coe_ne_infty _ hv
    | coe t =>
      refine ⟨((badX f σ t : X.Opens) : Set X)ᶜ, Finset.mem_insert_of_mem
        (Finset.mem_image_of_mem _ (hfin.mem_toFinset.2 ⟨p, hp, hpW, hv⟩)), ?_⟩
      exact (not_mem_badX_iff f σ t p hp).2 hv
  have hcov : W ⊆ ⋃₀ ↑fam := by
    intro x hx
    by_contra hnot
    let Y : Set X := W ∩ ⋂ z ∈ fam, zᶜ
    have hYo : IsLocallyClosed Y :=
      hWc.isLocallyClosed.inter (isOpen_biInter_finset fun z hz => (hcl z hz).isOpen_compl).isLocallyClosed
    have hxY : x ∈ Y := by
      refine ⟨hx, Set.mem_iInter₂.2 fun z hz hxz => hnot ⟨z, hz, hxz⟩⟩
    obtain ⟨p, hp, hpY⟩ := exists_point_of_isLocallyClosed f hYo ⟨x, hxY⟩
    obtain ⟨z, hz, hpz⟩ := hmem p hp hpY.1
    exact Set.mem_iInter₂.1 hpY.2 z hz hpz
  obtain ⟨z, hz, hWz⟩ := (isIrreducible_iff_sUnion_isClosed.1 hW) fam hcl hcov
  rcases Finset.mem_insert.1 hz with rfl | hz
  · refine ⟨OnePoint.infty, fun p _ hpW => val_of_not_mem σ p (hWz hpW)⟩
  · obtain ⟨t, -, rfl⟩ := Finset.mem_image.1 hz
    exact ⟨OnePoint.some t, fun p hp hpW => (not_mem_badX_iff f σ t p hp).1 (hWz hpW)⟩

end ImagePlane

/-- **C2K `ConstOrOntoAlgClosed` from (CI) alone** (task image-plane; (CI) is proved by
curve-glue's `componentIrreducible`). No leaf: properness enters through Mathlib's
`UniversallyClosed`. -/
theorem constOrOntoAlgClosed_of_CI (hI : ComponentIrreducible) : ConstOrOntoAlgClosed := by
  classical
  intro K _ _ X f hP hS σ p₀ hp₀
  have : LocallyOfFiniteType f := inferInstance
  have : JacobsonSpace X := LocallyOfFiniteType.jacobsonSpace f
  set x₀ := ptOf p₀ with hx₀
  have memW : ∀ p : Spec (CommRingCat.of K) ⟶ X, ptOf p ∈ connectedComponent x₀ ↔
      connectedComponent (ptOf p) = connectedComponent x₀ :=
    fun p => ⟨fun h => (connectedComponent_eq h).symm,
      fun h => by rw [← h]; exact mem_connectedComponent⟩
  have hWi := hI K X f hP hS x₀
  have hWc : IsClosed (connectedComponent x₀) := isClosed_connectedComponent
  have hconst : ∀ v : OnePoint K, (∀ p : Spec (CommRingCat.of K) ⟶ X, p ≫ f = 𝟙 _ →
      ptOf p ∈ connectedComponent x₀ → σ.val p = v) →
      ∀ p : Spec (CommRingCat.of K) ⟶ X, p ≫ f = 𝟙 _ →
        connectedComponent (ptOf p) = connectedComponent (ptOf p₀) → σ.val p = σ.val p₀ := by
    intro v hv p hp hpc
    rw [hv p hp ((memW p).2 hpc), hv p₀ hp₀ mem_connectedComponent]
  rcases ImagePlane.image_finite_or_univ f hP σ hWc with hfin | hall
  · obtain ⟨v, hv⟩ := ImagePlane.const_of_finite f σ hWi hWc hfin
    exact Or.inl (hconst v hv)
  rcases ImagePlane.image_finite_or_univ f hP (ImagePlane.inv σ) hWc with hfin' | hall'
  · obtain ⟨v, hv⟩ := ImagePlane.const_of_finite f (ImagePlane.inv σ) hWi hWc hfin'
    refine Or.inl (hconst (ImagePlane.recip v) fun p hp hpW => ?_)
    rw [ImagePlane.val_eq_recip σ p, hv p hp hpW]
  · right
    intro t
    induction t using OnePoint.rec with
    | infty =>
      obtain ⟨p, hp, hpW, h0⟩ := hall' 0
      refine ⟨p, hp, (memW p).1 hpW, ?_⟩
      rw [ImagePlane.val_eq_recip σ p, h0, ImagePlane.recip_coe, if_pos rfl]
    | coe t =>
      obtain ⟨p, hp, hpW, ht⟩ := hall t
      exact ⟨p, hp, (memW p).1 hpW, ht⟩

/-- **(AD) from C1b and (CI) alone.** -/
theorem algDep_of_CI (h1 : SmoothStalkDimOne) (hI : ComponentIrreducible) : AlgDep :=
  algDep_of h1 (constOrOntoAlgClosed_of_CI hI) hI

/-- **C2K holds** (from (CI), proved by curve-glue). -/
theorem constOrOntoAlgClosed : ConstOrOntoAlgClosed :=
  constOrOntoAlgClosed_of_CI componentIrreducible

/-- **(AD) holds.** -/
theorem algDep : AlgDep :=
  algDep_of_CI smoothStalkDimOne componentIrreducible

/-- **(G1'') holds.** -/
theorem imagePlaneCurveIrr : ImagePlaneCurveIrr :=
  imagePlaneCurveIrr_of constOrOntoAlgClosed componentIrreducible algDep imageClosed

/-- **(G1') `ImagePlaneCurveClosed` holds** (task image-plane): no hypothesis, no leaf. -/
theorem imagePlaneCurveClosed : ImagePlaneCurveClosed :=
  imagePlaneCurveClosed_of componentIrreducible imagePlaneCurveIrr

/-- **(G1) holds.** -/
theorem imagePlaneCurve : ImagePlaneCurve :=
  imagePlaneCurve_of constOrOntoAlgClosed imagePlaneCurveClosed

/-- **C3K holds.** -/
theorem ratFactorAlgClosed : RatFactorAlgClosed :=
  ratFactorAlgClosed_of imagePlaneCurve

/-- **Both curve facts of mobius-glue hold.** -/
theorem curveFacts : CurveRatFactor ∧ CurveSurj :=
  curveFacts_of_leaves smoothStalkDimOne constOrOntoAlgClosed ratFactorAlgClosed

end Pin

namespace CurveGlue

open CategoryTheory AlgebraicGeometry Limits Pin

/-- **The kernel's `MobiusGlue` from the textbook leaf T5 `ObjBridge.TorsionStructure` alone.** -/
theorem mobiusGlue_of_T5 (hT : ObjBridge.TorsionStructure) : MobiusGlue :=
  mobiusGlue_of_curves curveFacts.1 curveFacts.2 hT

/-- **Its CM-free form** (CM objects from the leaf bundle `R1R2fp`). -/
theorem mobiusGlueNoCM_of_T5 (hT : ObjBridge.TorsionStructure) (h : R1R2fp) : MobiusGlueNoCM :=
  mobiusGlue_noCM_of (mobiusGlue_of_T5 hT) h

/-- **The same with T5 in the form of `HSyn.TextbookLeaves.t5`** (`PkgI2.TorsionStructure.{0}`;
the kernel's `ObjBridge.torsionStructure_iff` is `Iff.rfl`): this discharges the field `mobius`
of `HSyn.GluePiecesPin` from the textbook bundle. -/
theorem mobiusGlue_of_t5 (h : PkgI2.TorsionStructure.{0}) : MobiusGlue :=
  mobiusGlue_of_T5 (ObjBridge.torsionStructure_iff.2 h)

end CurveGlue

end AV

end LeafQM

end

#print axioms LeafQM.AV.Pin.imageClosed
#print axioms LeafQM.AV.Pin.constOrOntoAlgClosed
#print axioms LeafQM.AV.Pin.algDep
#print axioms LeafQM.AV.Pin.imagePlaneCurveIrr
#print axioms LeafQM.AV.Pin.imagePlaneCurveClosed
#print axioms LeafQM.AV.Pin.imagePlaneCurve
#print axioms LeafQM.AV.Pin.ratFactorAlgClosed
#print axioms LeafQM.AV.Pin.curveFacts
#print axioms LeafQM.AV.CurveGlue.mobiusGlue_of_T5
#print axioms LeafQM.AV.CurveGlue.mobiusGlueNoCM_of_T5
#print axioms LeafQM.AV.CurveGlue.mobiusGlue_of_t5

end
end LF2Root_ImagePlane

section LF2Root_Stalks

/-! leaf-fold2: scratch/infra-stalks/HeightBCGlue.lean lines 3-850 (its Part 1: general stalk lemmas), verbatim; root namespace. -/

/-! # infra-stalks: height-bc glue `CotangentSpanBC` and `UniformizationLiftAnalytic` proved
Part 1: general lemmas (`StalkPullback.lean`, `local_structure.lean.part`). Part 2: verbatim
`scratch/height-bc/Final.lean` (after its import). Part 3: `bc_proof.lean.part`,
`ula_proof.lean.part`, `hbc_final.lean.part`. -/

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

/-- The stalk of `T` at `t` is *generated* by the stalk maps of `p : T ⟶ X` and `q : T ⟶ Y`:
every element is `c / w` with `c, w` in the subring generated by the two images and `w` a unit. -/
def StalkGen {T X Y : Scheme.{u}} (p : T ⟶ X) (q : T ⟶ Y) (t : T) : Prop :=
  ∀ r : T.presheaf.stalk t, ∃ c ∈ (p.stalkMap t).hom.range ⊔ (q.stalkMap t).hom.range,
    ∃ w ∈ (p.stalkMap t).hom.range ⊔ (q.stalkMap t).hom.range, IsUnit w ∧ r * w = c

theorem stalkMap_comp_apply' {T X X' : Scheme.{u}} (p : T ⟶ X) (j : X ⟶ X') (t : T)
    (y : X'.presheaf.stalk ((p ≫ j) t)) :
    (p ≫ j).stalkMap t y = p.stalkMap t (j.stalkMap (p t) y) := by
  rw [Scheme.Hom.stalkMap_comp]; rfl

theorem range_stalkMap_comp {T X X' : Scheme.{u}} (p : T ⟶ X) (j : X ⟶ X') (t : T) :
    ((p ≫ j).stalkMap t).hom.range = (j.stalkMap (p t)).hom.range.map (p.stalkMap t).hom := by
  ext x
  constructor
  · rintro ⟨y, rfl⟩
    exact ⟨j.stalkMap (p t) y, ⟨y, rfl⟩, (stalkMap_comp_apply' p j t y).symm⟩
  · rintro ⟨_, ⟨y, rfl⟩, rfl⟩
    exact ⟨y, stalkMap_comp_apply' p j t y⟩

/-- Post-composing with a morphism whose stalk map is an isomorphism (e.g. an open immersion)
does not change the image of the stalk map. -/
theorem range_stalkMap_comp_of_isIso {T X X' : Scheme.{u}} (p : T ⟶ X) (j : X ⟶ X') (t : T)
    [IsIso (j.stalkMap (p t))] :
    ((p ≫ j).stalkMap t).hom.range = (p.stalkMap t).hom.range := by
  rw [range_stalkMap_comp]
  have hs : Function.Surjective (j.stalkMap (p t)).hom :=
    (ConcreteCategory.bijective_of_isIso (j.stalkMap (p t))).2
  rw [RingHom.range_eq_top.mpr hs, ← RingHom.range_eq_map]

theorem StalkGen.comp_openImmersion {T X Y X' Y' : Scheme.{u}} {p : T ⟶ X} {q : T ⟶ Y} {t : T}
    (h : StalkGen p q t) (jX : X ⟶ X') (jY : Y ⟶ Y') [IsOpenImmersion jX] [IsOpenImmersion jY] :
    StalkGen (p ≫ jX) (q ≫ jY) t := by
  unfold StalkGen
  rw [range_stalkMap_comp_of_isIso, range_stalkMap_comp_of_isIso]
  exact h

/-- Transport of `StalkGen` along a morphism `m : T ⟶ Q` whose stalk map at `t` is an isomorphism
(e.g. an open immersion). -/
theorem StalkGen.of_comp {T Q X Y : Scheme.{u}} (m : T ⟶ Q) (p : Q ⟶ X) (q : Q ⟶ Y) (t : T)
    [IsIso (m.stalkMap t)] (h : StalkGen (m ≫ p) (m ≫ q) t) : StalkGen p q (m t) := by
  intro r
  set α := m.stalkMap t
  have hα : Function.Bijective α.hom := ConcreteCategory.bijective_of_isIso α
  have hrange : ∀ φ : Q ⟶ X, ((m ≫ φ).stalkMap t).hom.range =
      (φ.stalkMap (m t)).hom.range.map α.hom := fun φ => range_stalkMap_comp m φ t
  have hrange' : ∀ φ : Q ⟶ Y, ((m ≫ φ).stalkMap t).hom.range =
      (φ.stalkMap (m t)).hom.range.map α.hom := fun φ => range_stalkMap_comp m φ t
  obtain ⟨c, hc, w, hw, hwu, hrw⟩ := h (α r)
  rw [hrange, hrange', ← Subring.map_sup] at hc hw
  obtain ⟨c', hc', rfl⟩ := hc
  obtain ⟨w', hw', rfl⟩ := hw
  refine ⟨c', hc', w', hw', ?_, ?_⟩
  · have := hwu.map (inv α).hom
    rwa [← CommRingCat.comp_apply, IsIso.hom_inv_id, CommRingCat.id_apply] at this
  · apply hα.1
    rw [map_mul, hrw]

/-- Germs at `t` of global sections of `Spec S` coming from `R` along `φ : R ⟶ S` are images under
the stalk map of `Spec.map φ`. -/
theorem germ_ΓSpecIso_inv_map {R S : CommRingCat.{u}} (φ : R ⟶ S) (t : Spec S) (a : R) :
    (Spec S).presheaf.germ ⊤ t trivial ((Scheme.ΓSpecIso S).inv (φ a)) =
      (Spec.map φ).stalkMap t
        ((Spec R).presheaf.germ ⊤ (Spec.map φ t) trivial ((Scheme.ΓSpecIso R).inv a)) := by
  erw [Scheme.Hom.germ_stalkMap_apply (Spec.map φ) ⊤ t (by trivial)]
  have h := Scheme.ΓSpecIso_inv_naturality φ
  have h2 : (Scheme.ΓSpecIso S).inv (φ a) = (Spec.map φ).appTop ((Scheme.ΓSpecIso R).inv a) := by
    rw [← CommRingCat.comp_apply, h, CommRingCat.comp_apply]
  rw [h2]
  rfl

open TensorProduct in
/-- **The affine case.** The stalk of `Spec (A ⊗[R] B)` is generated by the images of the stalks
of `Spec A` and `Spec B`. -/
theorem stalkGen_spec_tensor (R A B : CommRingCat.{u}) [Algebra R A] [Algebra R B]
    (t : Spec (CommRingCat.of (A ⊗[R] B))) :
    StalkGen (Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom :
        A →+* A ⊗[R] B)))
      (Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight :
        B →ₐ[R] A ⊗[R] B).toRingHom)) t := by
  let T := Spec (CommRingCat.of (A ⊗[R] B))
  set iL : T ⟶ Spec A := Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom :
        A →+* A ⊗[R] B))
  set iR : T ⟶ Spec B := Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight :
        B →ₐ[R] A ⊗[R] B).toRingHom)
  set S' := (iL.stalkMap t).hom.range ⊔ (iR.stalkMap t).hom.range
  let γ : A ⊗[R] B →+* T.presheaf.stalk t :=
    (T.presheaf.germ ⊤ t trivial).hom.comp
      (Scheme.ΓSpecIso (CommRingCat.of (A ⊗[R] B))).inv.hom
  have hγ : ∀ a, γ a ∈ S' := by
    intro a
    induction a using TensorProduct.induction_on with
    | zero => rw [map_zero]; exact S'.zero_mem
    | add x y hx hy => rw [map_add]; exact S'.add_mem hx hy
    | tmul a b =>
      have e : a ⊗ₜ[R] b = (a ⊗ₜ[R] (1 : B)) * ((1 : A) ⊗ₜ[R] b) := by
        simp [Algebra.TensorProduct.tmul_mul_tmul]
      rw [e, map_mul]
      refine S'.mul_mem ((le_sup_left : _ ≤ S') ⟨_, (germ_ΓSpecIso_inv_map
        (CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom : A →+* A ⊗[R] B)) t a).symm⟩)
        ((le_sup_right : _ ≤ S') ⟨_, (germ_ΓSpecIso_inv_map
        (CommRingCat.ofHom (Algebra.TensorProduct.includeRight :
          B →ₐ[R] A ⊗[R] B).toRingHom) t b).symm⟩)
  intro r
  letI : Algebra Γ(T, ⊤) (T.presheaf.stalk t) := (T.presheaf.germ ⊤ t trivial).hom.toAlgebra
  have hL : IsLocalization.AtPrime (T.presheaf.stalk t)
      ((isAffineOpen_top T).primeIdealOf ⟨t, trivial⟩).asIdeal :=
    (isAffineOpen_top T).isLocalization_stalk ⟨t, trivial⟩
  obtain ⟨⟨a, s⟩, hrs⟩ := @IsLocalization.surj _ _ _ _ _ _ hL r
  refine ⟨_, ?_, _, ?_, @IsLocalization.map_units _ _ _ _ _ _ hL s, hrs⟩
  · have := hγ ((Scheme.ΓSpecIso (CommRingCat.of (A ⊗[R] B))).hom a)
    convert this using 1
    exact (congrArg (T.presheaf.germ ⊤ t trivial).hom
      (Iso.hom_inv_id_apply (Scheme.ΓSpecIso (CommRingCat.of (A ⊗[R] B))) a)).symm
  · have := hγ ((Scheme.ΓSpecIso (CommRingCat.of (A ⊗[R] B))).hom s.1)
    convert this using 1
    exact (congrArg (T.presheaf.germ ⊤ t trivial).hom
      (Iso.hom_inv_id_apply (Scheme.ΓSpecIso (CommRingCat.of (A ⊗[R] B))) s.1)).symm

/-- An affine chart of `X` through `x`, lying over a given affine chart `jV : Spec R ⟶ S` of `S`. -/
theorem exists_affine_chart_over {X S : Scheme.{u}} (f : X ⟶ S) {R : CommRingCat.{u}}
    (jV : Spec R ⟶ S) [IsOpenImmersion jV] (x : X) (hx : f x ∈ Set.range jV) :
    ∃ (A : CommRingCat.{u}) (jU : Spec A ⟶ X) (_ : IsOpenImmersion jU) (φ : R ⟶ A),
      x ∈ Set.range jU ∧ Spec.map φ ≫ jV = jU ≫ f := by
  obtain ⟨x', hx'⟩ : x ∈ Set.range (pullback.fst f jV) := by
    rw [Scheme.Pullback.range_fst]; exact hx
  let 𝒰 := (pullback f jV).affineOpenCover
  obtain ⟨y, hy⟩ := 𝒰.covers x'
  refine ⟨𝒰.X (𝒰.idx x'), 𝒰.f _ ≫ pullback.fst f jV, inferInstance,
    Spec.preimage (𝒰.f _ ≫ pullback.snd f jV), ⟨y, ?_⟩, ?_⟩
  · rw [Scheme.Hom.comp_apply, hy, hx']
  · rw [Spec.map_preimage]
    simp only [Category.assoc, pullback.condition]

/-- **Stalks of a fibre product are generated by the stalks of the factors.** For `f : X ⟶ S`,
`g : Y ⟶ S` and `z ∈ X ×_S Y`, every element of `𝒪_{X ×_S Y, z}` is `c / w` with `c, w` in the
subring generated by the images of `𝒪_{X, fst z}` and `𝒪_{Y, snd z}` and `w` a unit. -/
theorem pullback_stalkGen {X Y S : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S) (z : ↥(pullback f g)) :
    StalkGen (pullback.fst f g) (pullback.snd f g) z := by
  let 𝒱 := S.affineOpenCover
  let R := 𝒱.X (𝒱.idx (f (pullback.fst f g z)))
  let jV : Spec R ⟶ S := 𝒱.f (𝒱.idx (f (pullback.fst f g z)))
  have hs : f (pullback.fst f g z) ∈ Set.range jV := 𝒱.covers _
  obtain ⟨A, jU, _, φ, hxU, eU⟩ := exists_affine_chart_over f jV (pullback.fst f g z) hs
  have hs' : g (pullback.snd f g z) ∈ Set.range jV := by
    rw [← Scheme.Hom.comp_apply, ← pullback.condition, Scheme.Hom.comp_apply]; exact hs
  obtain ⟨B, jW, _, ψ, hyW, eW⟩ := exists_affine_chart_over g jV (pullback.snd f g z) hs'
  let _ : Algebra R A := φ.hom.toAlgebra
  let _ : Algebra R B := ψ.hom.toAlgebra
  let m := pullback.map (Spec.map φ) (Spec.map ψ) f g jU jW jV eU eW
  have hz : z ∈ Set.range m := by
    rw [Scheme.Pullback.range_map]; exact ⟨hxU, hyW⟩
  obtain ⟨t0, ht0⟩ := hz
  let e := pullbackSpecIso R A B
  let m' : Spec (CommRingCat.of (TensorProduct R A B)) ⟶ pullback f g := e.inv ≫ m
  have h1 : m' ≫ pullback.fst f g = Spec.map (CommRingCat.ofHom
      (Algebra.TensorProduct.includeLeftRingHom : A →+* TensorProduct R A B)) ≫ jU := by
    simp only [m', m, e, Category.assoc, pullback.lift_fst]
    rw [← Category.assoc]
    exact congrArg (· ≫ jU) (pullbackSpecIso_inv_fst R A B)
  have h2 : m' ≫ pullback.snd f g = Spec.map (CommRingCat.ofHom
      (Algebra.TensorProduct.includeRight : B →ₐ[R] TensorProduct R A B).toRingHom) ≫ jW := by
    simp only [m', m, e, Category.assoc, pullback.lift_snd]
    rw [← Category.assoc]
    exact congrArg (· ≫ jW) (pullbackSpecIso_inv_snd R A B)
  have key := StalkGen.of_comp m' (pullback.fst f g) (pullback.snd f g) (e.hom t0)
    (by rw [h1, h2]; exact (stalkGen_spec_tensor R A B _).comp_openImmersion jU jW)
  have hpt : m' (e.hom t0) = m t0 := by
    have he : e.inv (e.hom t0) = t0 := by
      rw [← Scheme.Hom.comp_apply, Iso.hom_inv_id]; rfl
    simp only [m']
    rw [Scheme.Hom.comp_apply, he]
  rw [hpt, ht0] at key
  exact key

/-! ### Maximal ideals and residue fields -/

/-- `x` is *rational over* `f x`: every element of `𝒪_{X,x}` is congruent modulo `𝔪_x` to the
image of an element of `𝒪_{S, f x}` (the residue field extension `κ(f x) → κ(x)` is onto). -/
def RationalOver {X S : Scheme.{u}} (f : X ⟶ S) (x : X) : Prop :=
  ∀ a : X.presheaf.stalk x, ∃ c : S.presheaf.stalk (f x),
    a - f.stalkMap x c ∈ IsLocalRing.maximalIdeal (X.presheaf.stalk x)

theorem StalkGen.comp_of_isIso {T Q X Y : Scheme.{u}} (m : T ⟶ Q) (p : Q ⟶ X) (q : Q ⟶ Y)
    (t : T) [IsIso (m.stalkMap t)] (h : StalkGen p q (m t)) : StalkGen (m ≫ p) (m ≫ q) t := by
  intro r
  set α := m.stalkMap t
  have hα : Function.Bijective α.hom := ConcreteCategory.bijective_of_isIso α
  obtain ⟨r', rfl⟩ := hα.2 r
  obtain ⟨c, hc, w, hw, hwu, hrw⟩ := h r'
  refine ⟨α c, ?_, α w, ?_, hwu.map α.hom, by rw [← map_mul, hrw]⟩
  · rw [range_stalkMap_comp, range_stalkMap_comp, ← Subring.map_sup]; exact ⟨c, hc, rfl⟩
  · rw [range_stalkMap_comp, range_stalkMap_comp, ← Subring.map_sup]; exact ⟨w, hw, rfl⟩

/-- The two composite stalk maps `𝒪_{S} → 𝒪_{T,t}` of a commutative square agree. -/
theorem exists_stalkMap_comp_eq {T X Y S : Scheme.{u}} (p : T ⟶ X) (q : T ⟶ Y) (f : X ⟶ S)
    (g : Y ⟶ S) (w : p ≫ f = q ≫ g) (t : T) (c : S.presheaf.stalk (f (p t))) :
    ∃ c' : S.presheaf.stalk (g (q t)),
      p.stalkMap t (f.stalkMap (p t) c) = q.stalkMap t (g.stalkMap (q t) c') := by
  have hpt : (p ≫ f) t = (q ≫ g) t := by rw [w]
  refine ⟨(S.presheaf.stalkCongr (.of_eq hpt)).hom c, ?_⟩
  calc p.stalkMap t (f.stalkMap (p t) c) = (p ≫ f).stalkMap t c :=
        (stalkMap_comp_apply' p f t c).symm
    _ = (q ≫ g).stalkMap t ((S.presheaf.stalkCongr (.of_eq hpt)).hom c) := by
        rw [Scheme.Hom.stalkMap_congr_hom (p ≫ f) (q ≫ g) w t]; rfl
    _ = _ := stalkMap_comp_apply' q g t _

section MaximalIdeal

variable {T X Y S : Scheme.{u}} {p : T ⟶ X} {q : T ⟶ Y} {f : X ⟶ S} {g : Y ⟶ S}

/-- The ideal `𝔪_x 𝒪_t + 𝔪_y 𝒪_t`. -/
noncomputable abbrev stalkIdeal (p : T ⟶ X) (q : T ⟶ Y) (t : T) : Ideal (T.presheaf.stalk t) :=
  (IsLocalRing.maximalIdeal _).map (p.stalkMap t).hom ⊔
    (IsLocalRing.maximalIdeal _).map (q.stalkMap t).hom

theorem stalkIdeal_le (t : T) : stalkIdeal p q t ≤ IsLocalRing.maximalIdeal _ := by
  refine sup_le (Ideal.map_le_iff_le_comap.mpr fun a ha => ?_)
    (Ideal.map_le_iff_le_comap.mpr fun a ha => ?_)
  · exact map_nonunit (p.stalkMap t).hom a ha
  · exact map_nonunit (q.stalkMap t).hom a ha

/-- Every element of the subring generated by the two images is congruent modulo
`𝔪_x 𝒪_t + 𝔪_y 𝒪_t` to an element coming from `𝒪_{Y,y}`, when `x` is rational over `s`. -/
theorem exists_sub_mem_stalkIdeal (w : p ≫ f = q ≫ g) {t : T} (hrat : RationalOver f (p t))
    {u : T.presheaf.stalk t} (hu : u ∈ (p.stalkMap t).hom.range ⊔ (q.stalkMap t).hom.range) :
    ∃ b : Y.presheaf.stalk (q t), u - q.stalkMap t b ∈ stalkIdeal p q t := by
  have hR : (p.stalkMap t).hom.range ⊔ (q.stalkMap t).hom.range ≤
      Subring.closure (Set.range (p.stalkMap t).hom ∪ Set.range (q.stalkMap t).hom) :=
    sup_le (fun x hx => Subring.subset_closure (Or.inl (RingHom.mem_range.mp hx)))
      (fun x hx => Subring.subset_closure (Or.inr (RingHom.mem_range.mp hx)))
  set I := stalkIdeal p q t
  suffices H : ∀ u' (hu' : u' ∈ Subring.closure
      (Set.range (p.stalkMap t).hom ∪ Set.range (q.stalkMap t).hom)),
      ∃ b : Y.presheaf.stalk (q t), u' - q.stalkMap t b ∈ I from H u (hR hu)
  intro u' hu'
  induction hu' using Subring.closure_induction with
  | mem x hx =>
    rcases hx with ⟨a, rfl⟩ | ⟨b, rfl⟩
    · obtain ⟨c, hc⟩ := hrat a
      obtain ⟨c', hc'⟩ := exists_stalkMap_comp_eq p q f g w t c
      refine ⟨g.stalkMap (q t) c', ?_⟩
      rw [← hc', ← map_sub]
      exact Ideal.mem_sup_left (Ideal.mem_map_of_mem _ hc)
    · exact ⟨b, by rw [sub_self]; exact I.zero_mem⟩
  | zero => exact ⟨0, by rw [map_zero, sub_self]; exact I.zero_mem⟩
  | one => exact ⟨1, by rw [map_one, sub_self]; exact I.zero_mem⟩
  | add x y _ _ hx hy =>
    obtain ⟨b1, h1⟩ := hx
    obtain ⟨b2, h2⟩ := hy
    refine ⟨b1 + b2, ?_⟩
    have : x + y - q.stalkMap t (b1 + b2) =
        (x - q.stalkMap t b1) + (y - q.stalkMap t b2) := by rw [map_add]; ring
    rw [this]; exact I.add_mem h1 h2
  | neg x _ hx =>
    obtain ⟨b1, h1⟩ := hx
    refine ⟨-b1, ?_⟩
    have : -x - q.stalkMap t (-b1) = -(x - q.stalkMap t b1) := by rw [map_neg]; ring
    rw [this]; exact I.neg_mem h1
  | mul x y _ _ hx hy =>
    obtain ⟨b1, h1⟩ := hx
    obtain ⟨b2, h2⟩ := hy
    refine ⟨b1 * b2, ?_⟩
    have : x * y - q.stalkMap t (b1 * b2) =
        (x - q.stalkMap t b1) * y + q.stalkMap t b1 * (y - q.stalkMap t b2) := by
      rw [map_mul]; ring
    rw [this]
    exact I.add_mem (I.mul_mem_right _ h1) (I.mul_mem_left _ h2)

/-- **Maximal ideal of a stalk generated by two stalks.** If `𝒪_{T,t}` is generated by the stalks
at `x = p t` and `y = q t` (`StalkGen`, e.g. `T = X ×_S Y`) and `x` is rational over `s`, then
`𝔪_t = 𝔪_x 𝒪_t + 𝔪_y 𝒪_t`. -/
theorem maximalIdeal_eq_of_stalkGen (w : p ≫ f = q ≫ g) {t : T} (h : StalkGen p q t)
    (hrat : RationalOver f (p t)) :
    IsLocalRing.maximalIdeal (T.presheaf.stalk t) = stalkIdeal p q t := by
  refine le_antisymm (fun r hr => ?_) (stalkIdeal_le t)
  obtain ⟨c, hc, w', hw', hwu, hrw⟩ := h r
  obtain ⟨b, hb⟩ := exists_sub_mem_stalkIdeal w hrat hc
  have hcm : c ∈ IsLocalRing.maximalIdeal _ := hrw ▸ Ideal.mul_mem_right _ _ hr
  have hqb : q.stalkMap t b ∈ IsLocalRing.maximalIdeal _ := by
    have := Ideal.sub_mem _ hcm (stalkIdeal_le t hb)
    rwa [sub_sub_cancel] at this
  have hbm : b ∈ IsLocalRing.maximalIdeal _ := by
    intro hbu
    exact hqb (hbu.map (q.stalkMap t).hom)
  have hcI : c ∈ stalkIdeal p q t := by
    have := Ideal.add_mem _ hb (Ideal.mem_sup_right (Ideal.mem_map_of_mem _ hbm))
    rwa [sub_add_cancel] at this
  obtain ⟨v, rfl⟩ := hwu
  have : r = c * ↑v⁻¹ := by rw [← hrw, mul_assoc, Units.mul_inv, mul_one]
  rw [this]
  exact Ideal.mul_mem_right _ _ hcI

/-- **Residue field of a stalk generated by two stalks.** Under the hypotheses of
`maximalIdeal_eq_of_stalkGen`, every element of `𝒪_{T,t}` is congruent modulo `𝔪_t` to the image of
an element of `𝒪_{Y,y}`. -/
theorem exists_sub_mem_maximalIdeal_of_stalkGen (w : p ≫ f = q ≫ g) {t : T} (h : StalkGen p q t)
    (hrat : RationalOver f (p t)) (r : T.presheaf.stalk t) :
    ∃ b : Y.presheaf.stalk (q t), r - q.stalkMap t b ∈ IsLocalRing.maximalIdeal _ := by
  obtain ⟨c, hc, w', hw', hwu, hrw⟩ := h r
  obtain ⟨b1, hb1⟩ := exists_sub_mem_stalkIdeal w hrat hc
  obtain ⟨b2, hb2⟩ := exists_sub_mem_stalkIdeal w hrat hw'
  have e1 : IsLocalRing.residue _ c = IsLocalRing.residue _ (q.stalkMap t b1) := by
    rw [← sub_eq_zero, ← map_sub, IsLocalRing.residue_eq_zero_iff]; exact stalkIdeal_le t hb1
  have e2 : IsLocalRing.residue _ w' = IsLocalRing.residue _ (q.stalkMap t b2) := by
    rw [← sub_eq_zero, ← map_sub, IsLocalRing.residue_eq_zero_iff]; exact stalkIdeal_le t hb2
  have hw0 : IsLocalRing.residue _ w' ≠ 0 := (IsLocalRing.residue_ne_zero_iff_isUnit _).mpr hwu
  have hb2u : IsUnit b2 := by
    rw [e2, IsLocalRing.residue_ne_zero_iff_isUnit] at hw0
    exact isUnit_of_map_unit (q.stalkMap t).hom _ hw0
  obtain ⟨v, rfl⟩ := hb2u
  refine ⟨b1 * ↑v⁻¹, ?_⟩
  rw [← IsLocalRing.residue_eq_zero_iff, map_sub, sub_eq_zero]
  apply mul_right_cancel₀ hw0
  rw [← map_mul, hrw, e1, e2, ← map_mul, ← map_mul, mul_assoc, Units.inv_mul, mul_one]

end MaximalIdeal

/-- **A point on a section is rational.** If `e` is a section of `f` (`e ≫ f = 𝟙`), the point
`e s` is rational over `f (e s)`. -/
theorem rationalOver_of_section {X S : Scheme.{u}} (f : X ⟶ S) (e : S ⟶ X) (he : e ≫ f = 𝟙 S)
    (s : S) : RationalOver f (e s) := by
  intro a
  have hs : f (e s) = s := by rw [← Scheme.Hom.comp_apply, he]; rfl
  refine ⟨(S.presheaf.stalkCongr (.of_eq hs)).inv (e.stalkMap s a), ?_⟩
  have key : e.stalkMap s (f.stalkMap (e s) ((S.presheaf.stalkCongr (.of_eq hs)).inv
      (e.stalkMap s a))) = e.stalkMap s a := by
    have h3 : ∀ y, (S.presheaf.stalkCongr (.of_eq hs)).hom
        ((S.presheaf.stalkCongr (.of_eq hs)).inv y) = y := fun y => Iso.inv_hom_id_apply _ y
    refine (stalkMap_comp_apply' e f s _).symm.trans ?_
    rw [Scheme.Hom.stalkMap_congr_hom (e ≫ f) (𝟙 S) he s, Scheme.Hom.stalkMap_id]
    exact h3 _
  intro hu
  apply hu.map (e.stalkMap s).hom |> fun h' => ?_
  rw [map_sub, key, sub_self] at h'
  exact not_isUnit_zero h'

/-! ### Sections and points with field stalks -/

theorem StalkGen.symm {T X Y : Scheme.{u}} {p : T ⟶ X} {q : T ⟶ Y} {t : T}
    (h : StalkGen p q t) : StalkGen q p t := by
  intro r
  obtain ⟨c, hc, w, hw, hu, h'⟩ := h r
  rw [sup_comm] at hc hw
  exact ⟨c, hc, w, hw, hu, h'⟩

/-- A morphism with a retraction is rational at every point (it is surjective on stalks). -/
theorem rationalOver_of_retraction {X S : Scheme.{u}} (f : X ⟶ S) (r : S ⟶ X)
    (hr : f ≫ r = 𝟙 X) (x : X) : RationalOver f x := by
  intro a
  have hx : r (f x) = x := by rw [← Scheme.Hom.comp_apply, hr]; rfl
  refine ⟨r.stalkMap (f x) ((X.presheaf.stalkCongr (.of_eq hx)).inv a), ?_⟩
  have key : f.stalkMap x (r.stalkMap (f x) ((X.presheaf.stalkCongr (.of_eq hx)).inv a)) = a := by
    have h3 : ∀ y, (X.presheaf.stalkCongr (.of_eq hx)).hom
        ((X.presheaf.stalkCongr (.of_eq hx)).inv y) = y := fun y => Iso.inv_hom_id_apply _ y
    refine (stalkMap_comp_apply' f r x _).symm.trans ?_
    rw [Scheme.Hom.stalkMap_congr_hom (f ≫ r) (𝟙 X) hr x, Scheme.Hom.stalkMap_id]
    exact h3 _
  rw [key, sub_self]
  exact Ideal.zero_mem _

/-- The stalks of the spectrum of a field are fields. -/
theorem maximalIdeal_stalk_spec_field (k : Type u) [Field k] (x : Spec (CommRingCat.of k)) :
    IsLocalRing.maximalIdeal ((Spec (CommRingCat.of k)).presheaf.stalk x) = ⊥ := by
  have h : x = genericPoint (Spec (CommRingCat.of k)) := Subsingleton.elim _ _
  rw [← IsLocalRing.isField_iff_maximalIdeal_eq, h]
  exact Field.toIsField (Spec (CommRingCat.of k)).functionField

theorem mem_maximalIdeal_of_iso {R S : CommRingCat.{u}} [IsLocalRing R] [IsLocalRing S]
    (φ : R ≅ S) {a : R} (ha : a ∈ IsLocalRing.maximalIdeal R) :
    φ.hom a ∈ IsLocalRing.maximalIdeal S := by
  intro hu
  apply ha
  have := hu.map φ.inv.hom
  rwa [Iso.hom_inv_id_apply] at this

/-- In a commutative square `p ≫ f = q ≫ g`, if the stalk of `Y` at `q t` is a field, the
composite `𝒪_{S, f(p t)} → 𝒪_{X, p t} → 𝒪_{T, t}` kills the maximal ideal. -/
theorem stalkMap_comp_eq_zero_of_maximalIdeal_eq_bot {T X Y S : Scheme.{u}} (p : T ⟶ X)
    (q : T ⟶ Y) (f : X ⟶ S) (g : Y ⟶ S) (w : p ≫ f = q ≫ g) (t : T)
    (hY : IsLocalRing.maximalIdeal (Y.presheaf.stalk (q t)) = ⊥)
    (c : S.presheaf.stalk (f (p t))) (hc : c ∈ IsLocalRing.maximalIdeal _) :
    p.stalkMap t (f.stalkMap (p t) c) = 0 := by
  have hpt : (p ≫ f) t = (q ≫ g) t := by rw [w]
  have e : p.stalkMap t (f.stalkMap (p t) c) =
      q.stalkMap t (g.stalkMap (q t) ((S.presheaf.stalkCongr (.of_eq hpt)).hom c)) := by
    calc p.stalkMap t (f.stalkMap (p t) c) = (p ≫ f).stalkMap t c :=
          (stalkMap_comp_apply' p f t c).symm
      _ = (q ≫ g).stalkMap t ((S.presheaf.stalkCongr (.of_eq hpt)).hom c) := by
          rw [Scheme.Hom.stalkMap_congr_hom (p ≫ f) (q ≫ g) w t]; rfl
      _ = _ := stalkMap_comp_apply' q g t _
  have hc' := mem_maximalIdeal_of_iso (S.presheaf.stalkCongr (.of_eq hpt)) hc
  have h0 : g.stalkMap (q t) ((S.presheaf.stalkCongr (.of_eq hpt)).hom c) ∈
      IsLocalRing.maximalIdeal (Y.presheaf.stalk (q t)) := map_nonunit _ _ hc'
  rw [hY, Ideal.mem_bot] at h0
  rw [e, h0, map_zero]

/-- **A section through a point with field stalk is an open immersion.** Let `q : P ⟶ Spec k` be
locally of finite type over a field `k` and `u` a section of `q`. If the stalk of `P` at the
point `u pt` is a field, then `u` is an open immersion. -/
theorem isOpenImmersion_of_section_of_maximalIdeal_eq_bot {k : Type u} [Field k] {P : Scheme.{u}}
    (q : P ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType q] (u : Spec (CommRingCat.of k) ⟶ P)
    (hu : u ≫ q = 𝟙 _) (pt : Spec (CommRingCat.of k))
    (hm : IsLocalRing.maximalIdeal (P.presheaf.stalk (u pt)) = ⊥) : IsOpenImmersion u := by
  have hcl : IsClosedImmersion u := isClosedImmersion_of_comp_eq_id q u hu
  have hF : IsField (P.presheaf.stalk (u pt)) := IsLocalRing.isField_iff_maximalIdeal_eq.mpr hm
  have hinj : Function.Injective (u.stalkMap pt).hom := by
    letI := hF.toField
    exact RingHom.injective _
  have hsurj : Function.Surjective (u.stalkMap pt).hom := u.stalkMap_surjective pt
  have hqs : Function.Surjective (q.stalkMap (u pt)).hom := by
    intro y
    have hpt : (u ≫ q) pt = (𝟙 (Spec (CommRingCat.of k))) pt := by rw [hu]
    let c := ((Spec (CommRingCat.of k)).presheaf.stalkCongr (.of_eq hpt)).inv (u.stalkMap pt y)
    have hc : (u ≫ q).stalkMap pt c = u.stalkMap pt y := by
      rw [Scheme.Hom.stalkMap_congr_hom (u ≫ q) (𝟙 _) hu pt, Scheme.Hom.stalkMap_id]
      exact Iso.inv_hom_id_apply ((Spec (CommRingCat.of k)).presheaf.stalkCongr (.of_eq hpt))
        (u.stalkMap pt y)
    refine ⟨c, hinj ?_⟩
    rw [← hc]
    exact (stalkMap_comp_apply' u q pt c).symm
  have hqf : q.QuasiFiniteAt (u pt) :=
    RingHom.QuasiFinite.of_finite (RingHom.Finite.of_surjective _ hqs)
  have h1 : IsOpen {q.asFiber (u pt)} := Scheme.Hom.quasiFiniteAt_iff_isOpen_singleton_asFiber.mp hqf
  have h2 : IsOpen ((q.fiberHomeo (q (u pt))) '' {q.asFiber (u pt)}) :=
    (q.fiberHomeo _).isOpenMap _ h1
  rw [Set.image_singleton, Scheme.Hom.asFiber, Homeomorph.apply_symm_apply] at h2
  have hopen : IsOpen (q.base ⁻¹' {q (u pt)}) := by
    convert isOpen_univ
    ext y
    simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_univ, iff_true]
    exact Subsingleton.elim _ _
  have h3 : IsOpen ({u pt} : Set P) := by
    have := hopen.isOpenMap_subtype_val _ h2
    simpa using this
  have hrange : Set.range u = {u pt} := by
    ext y
    constructor
    · rintro ⟨x, rfl⟩
      rw [Subsingleton.elim x pt]
      rfl
    · rintro rfl
      exact ⟨pt, rfl⟩
  have hemb : Topology.IsOpenEmbedding u :=
    ⟨u.isClosedEmbedding.isEmbedding, by rw [hrange]; exact h3⟩
  haveI : ∀ x, IsIso (u.stalkMap x) := by
    intro x
    obtain rfl : x = pt := Subsingleton.elim x pt
    exact (ConcreteCategory.isIso_iff_bijective _).mpr ⟨hinj, hsurj⟩
  exact IsOpenImmersion.of_isIso_stalkMap u hemb

theorem stalkMap_congr_point_apply {X Y : Scheme.{u}} (f : X ⟶ Y) {x x' : X} (h : x = x')
    (z : Y.presheaf.stalk (f x)) :
    (X.presheaf.stalkCongr (.of_eq h)).hom (f.stalkMap x z) =
      f.stalkMap x' ((Y.presheaf.stalkCongr (.of_eq (congrArg f h))).hom z) :=
  ConcreteCategory.congr_hom (Scheme.Hom.stalkMap_congr_point f x x' h) z

/-! ### Stalk maps between given points -/

/-- The stalk map of `f` from `y` to `x`, for `f x = y`. -/
noncomputable def Scheme.Hom.stalkMapAt {X Y : Scheme.{u}} (f : X ⟶ Y) {x : X} {y : Y}
    (h : f x = y) : Y.presheaf.stalk y ⟶ X.presheaf.stalk x :=
  (Y.presheaf.stalkCongr (.of_eq h.symm)).hom ≫ f.stalkMap x

instance {X Y : Scheme.{u}} (f : X ⟶ Y) {x : X} {y : Y} (h : f x = y) :
    IsLocalHom (f.stalkMapAt h).hom := by
  unfold Scheme.Hom.stalkMapAt
  rw [CommRingCat.hom_comp]
  infer_instance

theorem Scheme.Hom.stalkMapAt_rfl {X Y : Scheme.{u}} (f : X ⟶ Y) (x : X) :
    f.stalkMapAt (rfl : f x = f x) = f.stalkMap x := by
  unfold Scheme.Hom.stalkMapAt
  have : (Y.presheaf.stalkCongr (.of_eq (rfl : f x = f x).symm)).hom = 𝟙 _ :=
    Y.presheaf.stalkSpecializes_refl _
  rw [this, Category.id_comp]

theorem Scheme.Hom.stalkMapAt_comp {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) {x : X} {y : Y}
    {z : Z} (hf : f x = y) (hg : g y = z) (hfg : (f ≫ g) x = z) :
    (f ≫ g).stalkMapAt hfg = g.stalkMapAt hg ≫ f.stalkMapAt hf := by
  subst hf hg
  rw [Scheme.Hom.stalkMapAt_rfl, Scheme.Hom.stalkMapAt_rfl]
  unfold Scheme.Hom.stalkMapAt
  have : (Z.presheaf.stalkCongr (.of_eq hfg.symm)).hom = 𝟙 _ :=
    Z.presheaf.stalkSpecializes_refl _
  rw [this]
  exact (Category.id_comp _).trans (Scheme.Hom.stalkMap_comp f g x)

theorem Scheme.Hom.stalkMapAt_congr {X Y : Scheme.{u}} {f g : X ⟶ Y} (e : f = g) {x : X} {y : Y}
    (hf : f x = y) (hg : g x = y) : f.stalkMapAt hf = g.stalkMapAt hg := by
  subst e; rfl

theorem Scheme.Hom.stalkMapAt_id {X : Scheme.{u}} (x : X) (h : (𝟙 X) x = x) :
    Scheme.Hom.stalkMapAt (𝟙 X) h = 𝟙 _ := by
  unfold Scheme.Hom.stalkMapAt
  rw [Scheme.Hom.stalkMap_id]
  exact (Category.comp_id _).trans (X.presheaf.stalkSpecializes_refl _)

theorem Scheme.Hom.map_stalkMapAt_maximalIdeal {X Y : Scheme.{u}} (f : X ⟶ Y) {x : X} {y : Y}
    (h : f x = y) :
    Ideal.map (f.stalkMapAt h).hom (IsLocalRing.maximalIdeal (Y.presheaf.stalk y)) =
      Ideal.map (f.stalkMap x).hom (IsLocalRing.maximalIdeal (Y.presheaf.stalk (f x))) := by
  subst h; rw [Scheme.Hom.stalkMapAt_rfl]

theorem Scheme.Hom.exists_stalkMapAt_eq {X Y : Scheme.{u}} (f : X ⟶ Y) {x : X} {y : Y}
    (h : f x = y) (b : Y.presheaf.stalk (f x)) :
    ∃ c : Y.presheaf.stalk y, f.stalkMapAt h c = f.stalkMap x b := by
  subst h; exact ⟨b, by rw [Scheme.Hom.stalkMapAt_rfl]⟩

end AlgebraicGeometry



/-! # Local structure of a fibre product at points with values in a field

For `f : X ⟶ Spec R`, `g : Y ⟶ Spec R` and points `p₁ : Spec F ⟶ X`, `p₂ : Spec F ⟶ Y` over
`Spec R` (`F` a field), a regular function on an open of `X ×_R Y` (pulled back along any
`W : X ×_R Y ⟶ P`) is, near `(p₁, p₂)`, a quotient of sums of products of regular functions on
opens `V₁ ∋ p₁`, `V₂ ∋ p₂`, uniformly for all `F`-points of `V₁ × V₂` where the denominator does
not vanish (`exists_localStructure_pullback`). Proof: affine charts `Spec A → X`, `Spec B → Y`,
the open chart `Spec (A ⊗[R] B) → X ×_R Y`, a basic open `D(h)` around the point inside the open,
`s = a / h^n` on `D(h)`, and pure tensors evaluate to products. -/

namespace AlgebraicGeometry

open CategoryTheory Limits TensorProduct

/-- The value `s(p) ∈ F` of a section at an `F`-point (and `0` if `p ∉ V`); the same formula as
`GroupModel.evalAt`. -/
noncomputable def evalPt {F : Type u} [Field F] {X : Scheme.{u}}
    (p : Spec (CommRingCat.of F) ⟶ X) (V : X.Opens) (s : Γ(X, V)) : F := by
  classical
  exact if h : ⊤ ≤ p ⁻¹ᵁ V then (Scheme.ΓSpecIso (CommRingCat.of F)).hom (p.appLE V ⊤ h s) else 0

/-- The section on `j(Spec A)` corresponding to `α ∈ A`, for an open immersion `j`. -/
noncomputable def secOf {X : Scheme.{u}} {A : CommRingCat.{u}} (j : Spec A ⟶ X) [IsOpenImmersion j]
    (α : A) : Γ(X, j ''ᵁ ⊤) :=
  (j.appIso ⊤).inv ((Scheme.ΓSpecIso A).inv α)

theorem appLE_secOf {X : Scheme.{u}} {A : CommRingCat.{u}} (j : Spec A ⟶ X) [IsOpenImmersion j]
    (α : A) (e : ⊤ ≤ j ⁻¹ᵁ (j ''ᵁ ⊤)) :
    j.appLE (j ''ᵁ ⊤) ⊤ e (secOf j α) = (Scheme.ΓSpecIso A).inv α := by
  unfold secOf
  rw [← CommRingCat.comp_apply, Scheme.Hom.appIso_inv_appLE]
  have : (homOfLE (by rwa [Scheme.Hom.preimage_image_eq] at e) :
      (⊤ : (Spec A).Opens) ⟶ ⊤) = 𝟙 _ := Subsingleton.elim _ _
  rw [this, op_id, CategoryTheory.Functor.map_id]
  rfl

theorem ΓSpecIso_hom_appLE_top {R S : CommRingCat.{u}} (φ : R ⟶ S)
    (e : (⊤ : (Spec S).Opens) ≤ Spec.map φ ⁻¹ᵁ ⊤) (x : Γ(Spec R, ⊤)) :
    (Scheme.ΓSpecIso S).hom ((Spec.map φ).appLE ⊤ ⊤ e x) = φ ((Scheme.ΓSpecIso R).hom x) := by
  have h : (Spec.map φ).appLE ⊤ ⊤ e = (Spec.map φ).appTop :=
    (Scheme.Hom.app_eq_appLE (f := Spec.map φ) (U := ⊤)).symm
  rw [h, ← CommRingCat.comp_apply, Scheme.ΓSpecIso_naturality]
  rfl

theorem evalPt_secOf {F : Type u} [Field F] {X : Scheme.{u}} {A : CommRingCat.{u}}
    (j : Spec A ⟶ X) [IsOpenImmersion j] (χ : A ⟶ CommRingCat.of F) (α : A) :
    evalPt (Spec.map χ ≫ j) (j ''ᵁ ⊤) (secOf j α) = χ α := by
  have hle : ⊤ ≤ (Spec.map χ ≫ j) ⁻¹ᵁ (j ''ᵁ ⊤) := by
    intro x _
    exact ⟨Spec.map χ x, trivial, rfl⟩
  unfold evalPt
  rw [dif_pos hle, ← Scheme.Hom.appLE_comp_appLE (Spec.map χ) j (j ''ᵁ ⊤) ⊤ ⊤
    (Scheme.Hom.preimage_image_eq j ⊤).ge (fun _ _ => trivial), CommRingCat.comp_apply,
    appLE_secOf]
  exact (ΓSpecIso_hom_appLE_top χ _ _).trans (by rw [Iso.inv_hom_id_apply])

/-- Every element of `A ⊗[R] B` is a finite sum of pure tensors. -/
theorem exists_fin_sum_tmul {R A B : Type*} [CommRing R] [CommRing A] [CommRing B] [Algebra R A]
    [Algebra R B] (x : A ⊗[R] B) :
    ∃ (n : ℕ) (a : Fin n → A) (b : Fin n → B), x = ∑ k, a k ⊗ₜ[R] b k := by
  induction x using TensorProduct.induction_on with
  | zero => exact ⟨0, Fin.elim0, Fin.elim0, by simp⟩
  | tmul a b => exact ⟨1, fun _ => a, fun _ => b, by simp⟩
  | add x y hx hy =>
    obtain ⟨n, a, b, rfl⟩ := hx
    obtain ⟨m, a', b', rfl⟩ := hy
    refine ⟨n + m, Fin.append a a', Fin.append b b', ?_⟩
    rw [Fin.sum_univ_add]
    simp [Fin.append_left, Fin.append_right]

/-- Two finite families of pure tensors with a common index type. -/
theorem exists_fin_sum_tmul₂ {R A B : Type*} [CommRing R] [CommRing A] [CommRing B] [Algebra R A]
    [Algebra R B] (x y : A ⊗[R] B) :
    ∃ (n : ℕ) (a c : Fin n → A) (b d : Fin n → B),
      x = ∑ k, a k ⊗ₜ[R] b k ∧ y = ∑ k, c k ⊗ₜ[R] d k := by
  obtain ⟨n, a, b, rfl⟩ := exists_fin_sum_tmul x
  obtain ⟨m, c, d, rfl⟩ := exists_fin_sum_tmul y
  refine ⟨n + m, Fin.append a 0, Fin.append 0 c, Fin.append b 0, Fin.append 0 d, ?_, ?_⟩
  · rw [Fin.sum_univ_add]; simp [Fin.append_left, Fin.append_right]
  · rw [Fin.sum_univ_add]; simp [Fin.append_left, Fin.append_right]

/-- An `F`-point lies in the basic open `D(h)` of `Spec T` iff `h` does not vanish at it. -/
theorem SpecMap_mem_basicOpen_iff {F : Type u} [Field F] {T : CommRingCat.{u}}
    (χ : T ⟶ CommRingCat.of F) (h : Γ(Spec T, ⊤)) (x : Spec (CommRingCat.of F)) :
    Spec.map χ x ∈ (Spec T).basicOpen h ↔ χ ((Scheme.ΓSpecIso T).hom h) ≠ 0 := by
  rw [basicOpen_eq_of_affine']
  change x ∈ Spec.map χ ⁻¹ᵁ PrimeSpectrum.basicOpen _ ↔ _
  rw [SpecMap_preimage_basicOpen]
  change χ ((Scheme.ΓSpecIso T).hom h) ∉ x.asIdeal ↔ _
  have hx : x.asIdeal = ⊥ := @Ideal.eq_bot_of_prime _ _ x.asIdeal x.isPrime
  rw [hx, Ideal.mem_bot]

/-- **Points of the product chart.** If `F`-points `p₁'`, `p₂'` lie in the charts `jU`, `jW`,
then `(p₁', p₂')` factors through `Spec (A ⊗[R] B)` via a ring map `χ` with `χ (α ⊗ 1) = p₁'(α)`
and `χ (1 ⊗ β) = p₂'(β)`. -/
theorem exists_chart_point {F : Type u} [Field F] {R A B : CommRingCat.{u}} {X Y : Scheme.{u}}
    (f : X ⟶ Spec R) (g : Y ⟶ Spec R) (jU : Spec A ⟶ X) [IsOpenImmersion jU] (jW : Spec B ⟶ Y)
    [IsOpenImmersion jW] (φ : R ⟶ A) (ψ : R ⟶ B) (eU : Spec.map φ = jU ≫ f)
    (eW : Spec.map ψ = jW ≫ g)
    (p₁' : Spec (CommRingCat.of F) ⟶ X) (p₂' : Spec (CommRingCat.of F) ⟶ Y)
    (hp' : p₁' ≫ f = p₂' ≫ g) (h1' : ⊤ ≤ p₁' ⁻¹ᵁ (jU ''ᵁ ⊤)) (h2' : ⊤ ≤ p₂' ⁻¹ᵁ (jW ''ᵁ ⊤)) :
    letI : Algebra R A := φ.hom.toAlgebra
    letI : Algebra R B := ψ.hom.toAlgebra
    ∃ χ : CommRingCat.of (A ⊗[R] B) ⟶ CommRingCat.of F,
      p₁' = Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom :
          A →+* A ⊗[R] B) ≫ χ) ≫ jU ∧
      p₂' = Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight :
          B →ₐ[R] A ⊗[R] B).toRingHom ≫ χ) ≫ jW := by
  letI : Algebra R A := φ.hom.toAlgebra
  letI : Algebra R B := ψ.hom.toAlgebra
  have hr1 : Set.range p₁' ⊆ Set.range jU := by
    rintro _ ⟨x, rfl⟩
    obtain ⟨y, -, hy⟩ := h1' (Set.mem_univ x)
    exact ⟨y, hy⟩
  have hr2 : Set.range p₂' ⊆ Set.range jW := by
    rintro _ ⟨x, rfl⟩
    obtain ⟨y, -, hy⟩ := h2' (Set.mem_univ x)
    exact ⟨y, hy⟩
  set l₁ := IsOpenImmersion.lift jU p₁' hr1
  set l₂ := IsOpenImmersion.lift jW p₂' hr2
  have hl₁ : l₁ ≫ jU = p₁' := IsOpenImmersion.lift_fac _ _ _
  have hl₂ : l₂ ≫ jW = p₂' := IsOpenImmersion.lift_fac _ _ _
  set χ₁ := Spec.preimage l₁
  set χ₂ := Spec.preimage l₂
  have hχ₁ : Spec.map χ₁ = l₁ := Spec.map_preimage _
  have hχ₂ : Spec.map χ₂ = l₂ := Spec.map_preimage _
  have hcompat : φ ≫ χ₁ = ψ ≫ χ₂ := by
    apply Spec.map_injective
    rw [Spec.map_comp, Spec.map_comp, hχ₁, hχ₂, eU, eW, ← Category.assoc, ← Category.assoc, hl₁,
      hl₂, hp']
  letI : Algebra R F := (φ ≫ χ₁).hom.toAlgebra
  let χ1a : A →ₐ[R] F := { χ₁.hom with commutes' := fun r => rfl }
  let χ2a : B →ₐ[R] F :=
    { χ₂.hom with
      commutes' := fun r => (congrArg (fun k : R ⟶ CommRingCat.of F => k.hom r) hcompat).symm }
  have hfg : ∀ x y, Commute (χ1a x) (χ2a y) := fun x y => Commute.all _ _
  let χ : CommRingCat.of (A ⊗[R] B) ⟶ CommRingCat.of F :=
    CommRingCat.ofHom (Algebra.TensorProduct.lift χ1a χ2a hfg).toRingHom
  refine ⟨χ, ?_, ?_⟩
  · have : CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom : A →+* A ⊗[R] B) ≫ χ =
        χ₁ := by
      ext a
      change Algebra.TensorProduct.lift χ1a χ2a hfg (a ⊗ₜ[R] 1) = χ₁ a
      rw [Algebra.TensorProduct.lift_tmul, map_one, mul_one]
      rfl
    rw [this, hχ₁, hl₁]
  · have : CommRingCat.ofHom (Algebra.TensorProduct.includeRight :
        B →ₐ[R] A ⊗[R] B).toRingHom ≫ χ = χ₂ := by
      ext b
      change Algebra.TensorProduct.lift χ1a χ2a hfg ((1 : A) ⊗ₜ[R] b) = χ₂ b
      rw [Algebra.TensorProduct.lift_tmul, map_one, one_mul]
      rfl
    rw [this, hχ₂, hl₂]

/-- **Local structure of a fibre product at `F`-points.** See the module docstring. -/
theorem exists_localStructure_pullback {F : Type u} [Field F] {R : CommRingCat.{u}}
    {X Y P : Scheme.{u}} (f : X ⟶ Spec R) (g : Y ⟶ Spec R) (W : pullback f g ⟶ P)
    (U : P.Opens) (s : Γ(P, U)) (p₁ : Spec (CommRingCat.of F) ⟶ X)
    (p₂ : Spec (CommRingCat.of F) ⟶ Y) (hp : p₁ ≫ f = p₂ ≫ g)
    (hU : ⊤ ≤ (pullback.lift p₁ p₂ hp ≫ W) ⁻¹ᵁ U) :
    ∃ (V₁ : X.Opens) (V₂ : Y.Opens) (n : ℕ) (a c : Fin n → Γ(X, V₁)) (b d : Fin n → Γ(Y, V₂)),
      ⊤ ≤ p₁ ⁻¹ᵁ V₁ ∧ ⊤ ≤ p₂ ⁻¹ᵁ V₂ ∧
      (∑ k, evalPt p₁ V₁ (c k) * evalPt p₂ V₂ (d k)) ≠ 0 ∧
      ∀ (p₁' : Spec (CommRingCat.of F) ⟶ X) (p₂' : Spec (CommRingCat.of F) ⟶ Y)
        (hp' : p₁' ≫ f = p₂' ≫ g), ⊤ ≤ p₁' ⁻¹ᵁ V₁ → ⊤ ≤ p₂' ⁻¹ᵁ V₂ →
        (∑ k, evalPt p₁' V₁ (c k) * evalPt p₂' V₂ (d k)) ≠ 0 →
        ⊤ ≤ (pullback.lift p₁' p₂' hp' ≫ W) ⁻¹ᵁ U ∧
        evalPt (pullback.lift p₁' p₂' hp' ≫ W) U s *
            (∑ k, evalPt p₁' V₁ (c k) * evalPt p₂' V₂ (d k)) =
          ∑ k, evalPt p₁' V₁ (a k) * evalPt p₂' V₂ (b k) := by
  classical
  let pt : Spec (CommRingCat.of F) := default
  have hall : ∀ x : Spec (CommRingCat.of F), x = pt := fun x => Subsingleton.elim _ _
  obtain ⟨A, jU, _, φ, hxU, eU⟩ := exists_affine_chart_over f (𝟙 (Spec R)) (p₁ pt) ⟨_, rfl⟩
  obtain ⟨B, jW, _, ψ, hyW, eW⟩ := exists_affine_chart_over g (𝟙 (Spec R)) (p₂ pt) ⟨_, rfl⟩
  have eU' : Spec.map φ = jU ≫ f := by rw [← eU, Category.comp_id]
  have eW' : Spec.map ψ = jW ≫ g := by rw [← eW, Category.comp_id]
  letI : Algebra R A := φ.hom.toAlgebra
  letI : Algebra R B := ψ.hom.toAlgebra
  let m := pullback.map (Spec.map φ) (Spec.map ψ) f g jU jW (𝟙 _) eU eW
  let e := pullbackSpecIso R A B
  let m' : Spec (CommRingCat.of (TensorProduct R A B)) ⟶ pullback f g := e.inv ≫ m
  have h1 : m' ≫ pullback.fst f g = Spec.map (CommRingCat.ofHom
      (Algebra.TensorProduct.includeLeftRingHom : A →+* TensorProduct R A B)) ≫ jU := by
    simp only [m', m, e, Category.assoc, pullback.lift_fst]
    rw [← Category.assoc]
    exact congrArg (· ≫ jU) (pullbackSpecIso_inv_fst R A B)
  have h2 : m' ≫ pullback.snd f g = Spec.map (CommRingCat.ofHom
      (Algebra.TensorProduct.includeRight : B →ₐ[R] TensorProduct R A B).toRingHom) ≫ jW := by
    simp only [m', m, e, Category.assoc, pullback.lift_snd]
    rw [← Category.assoc]
    exact congrArg (· ≫ jW) (pullbackSpecIso_inv_snd R A B)
  have hmi : IsOpenImmersion m' := by infer_instance
  -- the chart point of `(p₁', p₂')`
  have hlift : ∀ (p₁' : Spec (CommRingCat.of F) ⟶ X) (p₂' : Spec (CommRingCat.of F) ⟶ Y)
      (hp' : p₁' ≫ f = p₂' ≫ g), ⊤ ≤ p₁' ⁻¹ᵁ (jU ''ᵁ ⊤) → ⊤ ≤ p₂' ⁻¹ᵁ (jW ''ᵁ ⊤) →
      ∃ χ : CommRingCat.of (A ⊗[R] B) ⟶ CommRingCat.of F,
        pullback.lift p₁' p₂' hp' = Spec.map χ ≫ m' ∧
        (∀ α, evalPt p₁' (jU ''ᵁ ⊤) (secOf jU α) = χ (α ⊗ₜ[R] 1)) ∧
        (∀ β, evalPt p₂' (jW ''ᵁ ⊤) (secOf jW β) = χ ((1 : A) ⊗ₜ[R] β)) := by
    intro p₁' p₂' hp' h1' h2'
    obtain ⟨χ, e1, e2⟩ := exists_chart_point f g jU jW φ ψ eU' eW' p₁' p₂' hp' h1' h2'
    refine ⟨χ, ?_, ?_, ?_⟩
    · apply pullback.hom_ext
      · rw [pullback.lift_fst, Category.assoc, h1, ← Category.assoc, ← Spec.map_comp, e1]
      · rw [pullback.lift_snd, Category.assoc, h2, ← Category.assoc, ← Spec.map_comp, e2]
    · intro α
      rw [e1, evalPt_secOf]
      rfl
    · intro β
      rw [e2, evalPt_secOf]
      rfl
  -- the open, the basic open and the fraction
  let q := pullback.lift p₁ p₂ hp
  have hz : q pt ∈ Set.range m := by
    rw [Scheme.Pullback.range_map]
    refine ⟨?_, ?_⟩
    · show pullback.fst f g (q pt) ∈ Set.range jU
      rw [← Scheme.Hom.comp_apply, pullback.lift_fst]; exact hxU
    · show pullback.snd f g (q pt) ∈ Set.range jW
      rw [← Scheme.Hom.comp_apply, pullback.lift_snd]; exact hyW
  obtain ⟨t0', ht0'⟩ := hz
  let t0 := e.hom t0'
  have hmt0 : m' t0 = q pt := by
    have he : e.inv (e.hom t0') = t0' := by
      rw [← Scheme.Hom.comp_apply, Iso.hom_inv_id]; rfl
    simp only [m', t0]
    rw [Scheme.Hom.comp_apply, he, ht0']
  let U' : (Spec (CommRingCat.of (A ⊗[R] B))).Opens := (m' ≫ W) ⁻¹ᵁ U
  have ht0 : t0 ∈ U' := by
    show (m' ≫ W) t0 ∈ U
    rw [Scheme.Hom.comp_apply, hmt0, ← Scheme.Hom.comp_apply]
    exact hU (Set.mem_univ pt)
  obtain ⟨h, hDU, ht0D⟩ := (isAffineOpen_top (Spec (CommRingCat.of (A ⊗[R] B)))).exists_basicOpen_le
    (⟨t0, ht0⟩ : U') (Set.mem_univ _)
  let s' := (m' ≫ W).appLE U _ hDU s
  haveI := (isAffineOpen_top (Spec (CommRingCat.of (A ⊗[R] B)))).isLocalization_basicOpen h
  obtain ⟨k0, a0, hs'⟩ := IsLocalization.Away.surj h s'
  let h0 := (Scheme.ΓSpecIso (CommRingCat.of (A ⊗[R] B))).hom h
  let a0' := (Scheme.ΓSpecIso (CommRingCat.of (A ⊗[R] B))).hom a0
  obtain ⟨n, a, c, b, d, hN, hH⟩ := exists_fin_sum_tmul₂ (a0' * h0) (h0 ^ (k0 + 1))
  -- evaluation of the sums
  have hsum : ∀ (p₁' : Spec (CommRingCat.of F) ⟶ X) (p₂' : Spec (CommRingCat.of F) ⟶ Y)
      (χ : CommRingCat.of (A ⊗[R] B) ⟶ CommRingCat.of F),
      (∀ α, evalPt p₁' (jU ''ᵁ ⊤) (secOf jU α) = χ (α ⊗ₜ[R] 1)) →
      (∀ β, evalPt p₂' (jW ''ᵁ ⊤) (secOf jW β) = χ ((1 : A) ⊗ₜ[R] β)) →
      (∑ k, evalPt p₁' (jU ''ᵁ ⊤) (secOf jU (c k)) * evalPt p₂' (jW ''ᵁ ⊤) (secOf jW (d k)) =
        χ (h0 ^ (k0 + 1))) ∧
      (∑ k, evalPt p₁' (jU ''ᵁ ⊤) (secOf jU (a k)) * evalPt p₂' (jW ''ᵁ ⊤) (secOf jW (b k)) =
        χ (a0' * h0)) := by
    intro p₁' p₂' χ e1 e2
    constructor
    · rw [hH, map_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [e1, e2, ← map_mul, Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
    · rw [hN, map_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [e1, e2, ← map_mul, Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
  -- evaluation of `s` at a chart point in `D(h)`
  have hval : ∀ χ : CommRingCat.of (A ⊗[R] B) ⟶ CommRingCat.of F, χ h0 ≠ 0 →
      ⊤ ≤ (Spec.map χ ≫ m' ≫ W) ⁻¹ᵁ U ∧
      evalPt (Spec.map χ ≫ m' ≫ W) U s * χ (h0 ^ (k0 + 1)) = χ (a0' * h0) := by
    intro χ hχ
    have hD : ⊤ ≤ Spec.map χ ⁻¹ᵁ (Spec (CommRingCat.of (A ⊗[R] B))).basicOpen h := by
      intro x _
      exact (SpecMap_mem_basicOpen_iff χ h x).mpr hχ
    have hT : ⊤ ≤ (Spec.map χ ≫ m' ≫ W) ⁻¹ᵁ U := fun x hx => hDU (hD hx)
    refine ⟨hT, ?_⟩
    unfold evalPt
    rw [dif_pos hT]
    rw [← Scheme.Hom.appLE_comp_appLE (Spec.map χ) (m' ≫ W) U _ ⊤ hDU hD]
    let ev : Γ(Spec (CommRingCat.of (A ⊗[R] B)), (Spec (CommRingCat.of (A ⊗[R] B))).basicOpen h)
        →+* F := (Scheme.ΓSpecIso (CommRingCat.of F)).hom.hom.comp
        ((Spec.map χ).appLE _ ⊤ hD).hom
    have hev : ∀ x : Γ(Spec (CommRingCat.of (A ⊗[R] B)), ⊤),
        ev (algebraMap _ _ x) = χ ((Scheme.ΓSpecIso _).hom x) := by
      intro x
      change (Scheme.ΓSpecIso (CommRingCat.of F)).hom (((Spec (CommRingCat.of (A ⊗[R] B))).presheaf.map
        (homOfLE ((Spec (CommRingCat.of (A ⊗[R] B))).basicOpen_le h)).op ≫
          (Spec.map χ).appLE _ ⊤ hD) x) = _
      rw [Scheme.Hom.map_appLE]
      exact ΓSpecIso_hom_appLE_top χ _ x
    have key := congrArg ev hs'
    rw [map_mul, map_pow, hev, hev] at key
    change ev s' * χ (h0 ^ (k0 + 1)) = χ (a0' * h0)
    rw [map_pow, pow_succ, ← mul_assoc, key, map_mul]
  refine ⟨jU ''ᵁ ⊤, jW ''ᵁ ⊤, n, fun k => secOf jU (a k), fun k => secOf jU (c k),
    fun k => secOf jW (b k), fun k => secOf jW (d k), ?_, ?_, ?_, ?_⟩
  · intro x _
    rw [hall x]
    obtain ⟨y, hy⟩ := hxU
    exact ⟨y, trivial, hy⟩
  · intro x _
    rw [hall x]
    obtain ⟨y, hy⟩ := hyW
    exact ⟨y, trivial, hy⟩
  · have h1p : ⊤ ≤ p₁ ⁻¹ᵁ (jU ''ᵁ ⊤) := by
      intro x _; rw [hall x]; obtain ⟨y, hy⟩ := hxU; exact ⟨y, trivial, hy⟩
    have h2p : ⊤ ≤ p₂ ⁻¹ᵁ (jW ''ᵁ ⊤) := by
      intro x _; rw [hall x]; obtain ⟨y, hy⟩ := hyW; exact ⟨y, trivial, hy⟩
    obtain ⟨χ, hq, e1, e2⟩ := hlift p₁ p₂ hp h1p h2p
    rw [(hsum p₁ p₂ χ e1 e2).1, map_pow]
    refine pow_ne_zero _ ?_
    rw [← SpecMap_mem_basicOpen_iff χ h pt]
    have : Spec.map χ pt = t0 := by
      apply m'.isOpenEmbedding.injective
      rw [hmt0, ← Scheme.Hom.comp_apply, ← hq]
    rw [this]
    exact ht0D
  · intro p₁' p₂' hp' h1' h2' hne
    obtain ⟨χ, hq, e1, e2⟩ := hlift p₁' p₂' hp' h1' h2'
    obtain ⟨hs1, hs2⟩ := hsum p₁' p₂' χ e1 e2
    rw [hs1] at hne ⊢
    rw [hs2]
    have hχ : χ h0 ≠ 0 := by
      intro h0z
      apply hne
      rw [map_pow, h0z, zero_pow (Nat.succ_ne_zero _)]
    obtain ⟨hT, hv⟩ := hval χ hχ
    rw [hq, Category.assoc]
    exact ⟨hT, hv⟩

end AlgebraicGeometry

end LF2Root_Stalks

section LF2Root_UnifRoot

/-! leaf-fold2: unif-dims' root-namespace lemmas (see mk_unifdims.py) -/


/-!
# The cotangent space of a "product" of local rings

Abstract form of `𝔪/𝔪²` of `X ×_k Y` at a rational point `(x, y)`: if a local ring `R` receives
two maps `φ₁, φ₂ : O → R` with local retractions `ψ₁, ψ₂ : R → O` (`ψᵢ ∘ φᵢ = id`) such that the
cross terms `ψ₁ ∘ φ₂`, `ψ₂ ∘ φ₁` map `𝔪_O` into `𝔪_O²`, and `𝔪_R` is generated by `φ₁(𝔪_O)` and
`φ₂(𝔪_O)` with residue field generated by either image, then for every `x ∈ 𝔪_R`,
`x ≡ φ₁(ψ₁ x) + φ₂(ψ₂ x) (mod 𝔪_R²)`: the cotangent space of `R` is `T*_O ⊕ T*_O` via
`(ψ₁, ψ₂)`, with inverse `φ₁ + φ₂` (`IsLocalRing.sub_mem_maximalIdeal_sq_of_product`).

Mathlib-only; no `sorry`.
-/

namespace IsLocalRing

open Ideal

variable {R O : Type*} [CommRing R] [IsLocalRing R] [CommRing O] [IsLocalRing O]

theorem map_mem_sq_of_le {S T : Type*} [CommRing S] [CommRing T] (φ : S →+* T) {I : Ideal S}
    {J : Ideal T} (h : I.map φ ≤ J) {x : S} (hx : x ∈ I ^ 2) : φ x ∈ J ^ 2 := by
  have h2 : (I ^ 2).map φ ≤ J ^ 2 := by
    rw [pow_two, pow_two, Ideal.map_mul]
    exact Ideal.mul_mono h h
  exact h2 (Ideal.mem_map_of_mem _ hx)

theorem map_maximalIdeal_le_of_local (ψ : R →+* O) [IsLocalHom ψ] :
    (maximalIdeal R).map ψ ≤ maximalIdeal O :=
  Ideal.map_le_iff_le_comap.mpr fun a ha => map_nonunit ψ a ha

/-- Elements of `φ(𝔪_O) 𝒪_R` are congruent mod `𝔪_R²` to an element `φ a`, `a ∈ 𝔪_O`, if the
residue field of `R` is generated by `φ(O)`. -/
theorem exists_sub_mem_sq_of_mem_map (φ : O →+* R) (hle : (maximalIdeal O).map φ ≤ maximalIdeal R)
    (hr : ∀ r : R, ∃ c, r - φ c ∈ maximalIdeal R) {y : R} (hy : y ∈ (maximalIdeal O).map φ) :
    ∃ a ∈ maximalIdeal O, y - φ a ∈ maximalIdeal R ^ 2 := by
  induction hy using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨a, ha, rfl⟩ := hz
    exact ⟨a, ha, by rw [sub_self]; exact Ideal.zero_mem _⟩
  | zero => exact ⟨0, Ideal.zero_mem _, by rw [map_zero, sub_self]; exact Ideal.zero_mem _⟩
  | add y₁ y₂ _ _ h₁ h₂ =>
    obtain ⟨a₁, ha₁, e₁⟩ := h₁
    obtain ⟨a₂, ha₂, e₂⟩ := h₂
    refine ⟨a₁ + a₂, Ideal.add_mem _ ha₁ ha₂, ?_⟩
    have : y₁ + y₂ - φ (a₁ + a₂) = (y₁ - φ a₁) + (y₂ - φ a₂) := by rw [map_add]; ring
    rw [this]
    exact Ideal.add_mem _ e₁ e₂
  | smul r y hy' h =>
    obtain ⟨a, ha, e⟩ := h
    obtain ⟨c, hc⟩ := hr r
    refine ⟨c * a, Ideal.mul_mem_left _ _ ha, ?_⟩
    have : r • y - φ (c * a) = (r - φ c) * y + φ c * (y - φ a) := by
      rw [smul_eq_mul, map_mul]; ring
    rw [this]
    refine Ideal.add_mem _ ?_ (Ideal.mul_mem_left _ _ e)
    rw [pow_two]
    exact Ideal.mul_mem_mul hc (hle hy')

/-- **Cotangent space of a product.** See the module docstring. -/
theorem sub_mem_maximalIdeal_sq_of_product (φ₁ φ₂ : O →+* R) (ψ₁ ψ₂ : R →+* O)
    [IsLocalHom ψ₁] [IsLocalHom ψ₂]
    (h₁ : ∀ a, ψ₁ (φ₁ a) = a) (h₂ : ∀ a, ψ₂ (φ₂ a) = a)
    (h₁₂ : ∀ a ∈ maximalIdeal O, ψ₁ (φ₂ a) ∈ maximalIdeal O ^ 2)
    (h₂₁ : ∀ a ∈ maximalIdeal O, ψ₂ (φ₁ a) ∈ maximalIdeal O ^ 2)
    (hm : maximalIdeal R = (maximalIdeal O).map φ₁ ⊔ (maximalIdeal O).map φ₂)
    (hr₁ : ∀ r : R, ∃ c, r - φ₁ c ∈ maximalIdeal R)
    (hr₂ : ∀ r : R, ∃ c, r - φ₂ c ∈ maximalIdeal R)
    {x : R} (hx : x ∈ maximalIdeal R) :
    x - φ₁ (ψ₁ x) - φ₂ (ψ₂ x) ∈ maximalIdeal R ^ 2 := by
  have hle₁ : (maximalIdeal O).map φ₁ ≤ maximalIdeal R := hm ▸ le_sup_left
  have hle₂ : (maximalIdeal O).map φ₂ ≤ maximalIdeal R := hm ▸ le_sup_right
  rw [hm] at hx
  obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.mp hx
  obtain ⟨a, ha, ea⟩ := exists_sub_mem_sq_of_mem_map φ₁ hle₁ hr₁ hy
  obtain ⟨b, hb, eb⟩ := exists_sub_mem_sq_of_mem_map φ₂ hle₂ hr₂ hz
  -- `x ≡ φ₁ a + φ₂ b`
  have ex : y + z - φ₁ a - φ₂ b ∈ maximalIdeal R ^ 2 := by
    have : y + z - φ₁ a - φ₂ b = (y - φ₁ a) + (z - φ₂ b) := by ring
    rw [this]; exact Ideal.add_mem _ ea eb
  have hψ₁ := map_mem_sq_of_le ψ₁ (map_maximalIdeal_le_of_local ψ₁) ex
  have hψ₂ := map_mem_sq_of_le ψ₂ (map_maximalIdeal_le_of_local ψ₂) ex
  rw [map_sub, map_sub, h₁] at hψ₁
  rw [map_sub, map_sub, h₂] at hψ₂
  -- `ψ₁ x - a ∈ 𝔪²` and `ψ₂ x - b ∈ 𝔪²`
  have ea' : ψ₁ (y + z) - a ∈ maximalIdeal O ^ 2 := by
    have : ψ₁ (y + z) - a = (ψ₁ (y + z) - a - ψ₁ (φ₂ b)) + ψ₁ (φ₂ b) := by ring
    rw [this]; exact Ideal.add_mem _ hψ₁ (h₁₂ b hb)
  have eb' : ψ₂ (y + z) - b ∈ maximalIdeal O ^ 2 := by
    have : ψ₂ (y + z) - b = (ψ₂ (y + z) - ψ₂ (φ₁ a) - b) + ψ₂ (φ₁ a) := by ring
    rw [this]; exact Ideal.add_mem _ hψ₂ (h₂₁ a ha)
  have fa := map_mem_sq_of_le φ₁ hle₁ ea'
  have fb := map_mem_sq_of_le φ₂ hle₂ eb'
  rw [map_sub] at fa fb
  have : y + z - φ₁ (ψ₁ (y + z)) - φ₂ (ψ₂ (y + z)) =
      (y + z - φ₁ a - φ₂ b) - (φ₁ (ψ₁ (y + z)) - φ₁ a) - (φ₂ (ψ₂ (y + z)) - φ₂ b) := by ring
  rw [this]
  exact Ideal.sub_mem _ (Ideal.sub_mem _ ex fa) fb

end IsLocalRing


/-! # unif-dims: toward `ProductCotangent` — cotangent maps of unit-preserving morphisms -/


open CategoryTheory Limits

namespace AlgebraicGeometry

/-- A germ of a global section, pulled back. -/
theorem Scheme.Hom.stalkMapAt_germ_top {X Y : Scheme.{u}} (f : X ⟶ Y) {x : X} {y : Y}
    (h : f x = y) (s : Γ(Y, ⊤)) :
    (f.stalkMapAt h).hom (Y.presheaf.germ ⊤ y (TopologicalSpace.Opens.mem_top _) s) =
      X.presheaf.germ ⊤ x (TopologicalSpace.Opens.mem_top _) (f.appTop s) := by
  subst h
  rw [Scheme.Hom.stalkMapAt_rfl, Scheme.Hom.germ_stalkMap_apply]
  rfl

/-- Stalk maps between given points commute with specialization. -/
theorem Scheme.Hom.stalkMapAt_stalkSpecializes {X Y : Scheme.{u}} (f : X ⟶ Y) {x x' : X}
    {y y' : Y} (hx : x ⤳ x') (hy : y ⤳ y') (h : f x = y) (h' : f x' = y') (r : Y.presheaf.stalk y') :
    X.presheaf.stalkSpecializes hx ((f.stalkMapAt h').hom r) =
      (f.stalkMapAt h).hom (Y.presheaf.stalkSpecializes hy r) := by
  subst h h'
  rw [Scheme.Hom.stalkMapAt_rfl, Scheme.Hom.stalkMapAt_rfl,
    ← Scheme.Hom.stalkSpecializes_stalkMap_apply]

end AlgebraicGeometry

namespace IsLocalRing

open Ideal

/-- infra-stalks' `sub_mem_maximalIdeal_sq_of_product` with two different factor rings (same
proof). -/
theorem sub_mem_maximalIdeal_sq_of_product₂ {R O₁ O₂ : Type*} [CommRing R] [IsLocalRing R]
    [CommRing O₁] [IsLocalRing O₁] [CommRing O₂] [IsLocalRing O₂]
    (φ₁ : O₁ →+* R) (φ₂ : O₂ →+* R) (ψ₁ : R →+* O₁) (ψ₂ : R →+* O₂)
    [IsLocalHom ψ₁] [IsLocalHom ψ₂]
    (h₁ : ∀ a, ψ₁ (φ₁ a) = a) (h₂ : ∀ a, ψ₂ (φ₂ a) = a)
    (h₁₂ : ∀ a ∈ maximalIdeal O₂, ψ₁ (φ₂ a) ∈ maximalIdeal O₁ ^ 2)
    (h₂₁ : ∀ a ∈ maximalIdeal O₁, ψ₂ (φ₁ a) ∈ maximalIdeal O₂ ^ 2)
    (hm : maximalIdeal R = (maximalIdeal O₁).map φ₁ ⊔ (maximalIdeal O₂).map φ₂)
    (hr₁ : ∀ r : R, ∃ c, r - φ₁ c ∈ maximalIdeal R)
    (hr₂ : ∀ r : R, ∃ c, r - φ₂ c ∈ maximalIdeal R)
    {x : R} (hx : x ∈ maximalIdeal R) :
    x - φ₁ (ψ₁ x) - φ₂ (ψ₂ x) ∈ maximalIdeal R ^ 2 := by
  have hle₁ : (maximalIdeal O₁).map φ₁ ≤ maximalIdeal R := hm ▸ le_sup_left
  have hle₂ : (maximalIdeal O₂).map φ₂ ≤ maximalIdeal R := hm ▸ le_sup_right
  rw [hm] at hx
  obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.mp hx
  obtain ⟨a, ha, ea⟩ := exists_sub_mem_sq_of_mem_map φ₁ hle₁ hr₁ hy
  obtain ⟨b, hb, eb⟩ := exists_sub_mem_sq_of_mem_map φ₂ hle₂ hr₂ hz
  have ex : y + z - φ₁ a - φ₂ b ∈ maximalIdeal R ^ 2 := by
    have : y + z - φ₁ a - φ₂ b = (y - φ₁ a) + (z - φ₂ b) := by ring
    rw [this]; exact Ideal.add_mem _ ea eb
  have hψ₁ := map_mem_sq_of_le ψ₁ (map_maximalIdeal_le_of_local ψ₁) ex
  have hψ₂ := map_mem_sq_of_le ψ₂ (map_maximalIdeal_le_of_local ψ₂) ex
  rw [map_sub, map_sub, h₁] at hψ₁
  rw [map_sub, map_sub, h₂] at hψ₂
  have ea' : ψ₁ (y + z) - a ∈ maximalIdeal O₁ ^ 2 := by
    have : ψ₁ (y + z) - a = (ψ₁ (y + z) - a - ψ₁ (φ₂ b)) + ψ₁ (φ₂ b) := by ring
    rw [this]; exact Ideal.add_mem _ hψ₁ (h₁₂ b hb)
  have eb' : ψ₂ (y + z) - b ∈ maximalIdeal O₂ ^ 2 := by
    have : ψ₂ (y + z) - b = (ψ₂ (y + z) - ψ₂ (φ₁ a) - b) + ψ₂ (φ₁ a) := by ring
    rw [this]; exact Ideal.add_mem _ hψ₂ (h₂₁ a ha)
  have fa := map_mem_sq_of_le φ₁ hle₁ ea'
  have fb := map_mem_sq_of_le φ₂ hle₂ eb'
  rw [map_sub] at fa fb
  have : y + z - φ₁ (ψ₁ (y + z)) - φ₂ (ψ₂ (y + z)) =
      (y + z - φ₁ a - φ₂ b) - (φ₁ (ψ₁ (y + z)) - φ₁ a) - (φ₂ (ψ₂ (y + z)) - φ₂ b) := by ring
  rw [this]
  exact Ideal.sub_mem _ (Ideal.sub_mem _ ex fa) fb

end IsLocalRing


end LF2Root_UnifRoot

section LF2Root_SmoothDim

/-! # Dimension theory of smooth schemes over a field, and the glue Props (§0-§4 = SmoothStalk.lean verbatim)

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

namespace LF2.InfraSmoothDim

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

end LF2.InfraSmoothDim


/-! ## §4 Scheme stalks (task infra-smooth-dim) -/

namespace LF2.InfraSmoothDim

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

end LF2.InfraSmoothDim


/-! ## §5 The glue Props (statements copied verbatim) -/

/-! ### curve-facts: `SmoothStalkDimOne` (scratch/curve-facts/CurveFacts.lean, §8) -/

-- (leaf-fold2) section LeafQM.AV.Pin omitted (image-plane has it)

/-! ### hodge-lattice: `RegularAtOrigin`, `DimAtOrigin`, `TangentDimAtOrigin`
(scratch/hodge-lattice/HodgeLattice.lean, §9 and §11; `originPt` copied verbatim from §9) -/

namespace LF2.HodgeLattice
open NumberField CategoryTheory AlgebraicGeometry MonoidalCategory MonObj
open PkgI3 (AbVar)

/-- The origin `0 ∈ B` of an abelian variety over a field `L` (image of the point of `Spec L`
under the unit section). -/
noncomputable def originPt {L : Type} [Field L] (B : AbVar L) : B.X.left :=
  (η[B.X] : 𝟙_ (Over (Spec (CommRingCat.of L))) ⟶ B.X).left
    (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum L)

/-- **(V1)** The local ring of an abelian variety at its origin is regular (a smooth variety is
regular). -/
def RegularAtOrigin : Prop :=
  ∀ (L : Type) [Field L] (B : AbVar L), IsRegularLocalRing (B.X.left.presheaf.stalk (originPt B))

/-- **(V2)** The local ring of an abelian variety of dimension `g` at its origin has Krull dimension
`g` (the local ring of an irreducible variety at a closed point has dimension `dim`). -/
def DimAtOrigin : Prop :=
  ∀ (L : Type) [Field L] (B : AbVar L) (g : ℕ), B.dim = g →
    ringKrullDim (B.X.left.presheaf.stalk (originPt B)) = g

end LF2.HodgeLattice

namespace LF2.HodgeLattice
open NumberField CategoryTheory AlgebraicGeometry IsLocalRing
open PkgI3 (AbVar)

/-- **(V)** The tangent space of an abelian variety `B/L` at the origin has dimension `dim B`. -/
def TangentDimAtOrigin : Prop :=
  ∀ (L : Type) [Field L] (B : AbVar L) (g : ℕ), B.dim = g →
    Module.finrank (ResidueField (B.X.left.presheaf.stalk (originPt B)))
      (CotangentSpace (B.X.left.presheaf.stalk (originPt B))) = g

end LF2.HodgeLattice

namespace LF2.InfraSmoothDim
open CategoryTheory AlgebraicGeometry MonoidalCategory MonObj
open LF2.HodgeLattice

/-- A section of a morphism to `Spec K` is a closed immersion (copied from
scratch/mul-rigidity/MulRigidity.lean). -/
theorem isClosedImmersion_point {K : Type*} [Field K] (G : Over (Spec (.of K)))
    (x : 𝟙_ (Over (Spec (.of K))) ⟶ G) : IsClosedImmersion x.left :=
  isClosedImmersion_of_comp_eq_id (Y := Spec (.of K)) G.hom x.left (by simp)

/-- The origin of an abelian variety is a closed point. -/
theorem isClosed_originPt {L : Type} [Field L] (B : PkgI3.AbVar L) :
    IsClosed ({originPt B} : Set B.X.left) := by
  have := isClosedImmersion_point B.X η[B.X]
  have hr : Set.range (η[B.X] : 𝟙_ (Over (Spec (CommRingCat.of L))) ⟶ B.X).left.base =
      {originPt B} := by
    ext y
    constructor
    · rintro ⟨a, rfl⟩
      have : Subsingleton (PrimeSpectrum L) := inferInstance
      exact congrArg _ (Subsingleton.elim (α := PrimeSpectrum L) a ⟨⊥, Ideal.isPrime_bot⟩)
    · rintro rfl
      exact ⟨_, rfl⟩
  rw [← hr]
  exact (η[B.X] : 𝟙_ (Over (Spec (CommRingCat.of L))) ⟶ B.X).left.isClosedEmbedding.isClosed_range

/-- Dimension and embedding dimension at the origin equal `dim B`. -/
theorem originPt_dims {L : Type} [Field L] (B : PkgI3.AbVar L) :
    B.dim = ringKrullDim (B.X.left.presheaf.stalk (originPt B)) ∧
      ((IsLocalRing.maximalIdeal (B.X.left.presheaf.stalk (originPt B))).spanFinrank :
        WithBot ℕ∞) = ringKrullDim (B.X.left.presheaf.stalk (originPt B)) := by
  have : IrreducibleSpace B.X.left :=
    GeometricallyIrreducible.irreducibleSpace_of_subsingleton (f := B.X.hom)
  exact topologicalKrullDim_eq_of_smooth B.X.hom (originPt B) (isClosed_originPt B)

end LF2.InfraSmoothDim

namespace LF2.HodgeLattice
open NumberField CategoryTheory AlgebraicGeometry IsLocalRing
open PkgI3 (AbVar)

/-- **`RegularAtOrigin` holds** (task infra-smooth-dim). -/
theorem regularAtOrigin : RegularAtOrigin := by
  intro L _ B
  have : IsLocallyNoetherian B.X.left := LocallyOfFiniteType.isLocallyNoetherian B.X.hom
  exact (isRegularLocalRing_iff _).mpr (LF2.InfraSmoothDim.originPt_dims B).2

/-- **`DimAtOrigin` holds** (task infra-smooth-dim). -/
theorem dimAtOrigin : DimAtOrigin := by
  intro L _ B g hg
  rw [← (LF2.InfraSmoothDim.originPt_dims B).1, hg]

/-- **`TangentDimAtOrigin` holds** (task infra-smooth-dim). -/
theorem tangentDimAtOrigin : TangentDimAtOrigin := by
  intro L _ B g hg
  have : IsLocallyNoetherian B.X.left := LocallyOfFiniteType.isLocallyNoetherian B.X.hom
  obtain ⟨h1, h2⟩ := LF2.InfraSmoothDim.originPt_dims B
  rw [← spanFinrank_maximalIdeal_eq_finrank_cotangentSpace]
  rw [← h1, hg] at h2
  exact_mod_cast h2

end LF2.HodgeLattice


end LF2Root_SmoothDim

section LF2Root_UnramConj

/-!
# inner-twist: `G0ModField.UnramifiedConjugates` (from `scratch/fibre-cover/FibreCover.lean`), proved

Task inner-twist (2026-11-13). The Prop `UnramifiedConjugates` is copied verbatim (docstring and
body) from `scratch/fibre-cover/FibreCover.lean`, in the same namespace `G0ModField`; `Qbar` is
`LeafQM.AV.Qbar = AlgebraicClosure ℚ` and `UnramifiedAt` is glue-descent's
`GlueDescent.B2Q.UnramifiedAt` (`ZInQKernel/HDecomp/Descent/B2Glue.lean`), as in the source.

Proof (no leaf, no glue Prop). Let `K = ℚ(α)`, `L = ℚ(roots of minpoly α)` (finite Galois), `Q` a
prime of `𝓞 L` containing `p`, `G = Gal(L/ℚ)`, `I = I(Q) ≤ G`.
1. (`inertia_le_fixing`) `I` fixes `𝓞 K`: let `H ≤ G` fix `𝓞 K`; `H` is a Galois group of
   `𝓞 L / 𝓞 K` (Mathlib `IsGaloisGroup.of_isScalarTower`). Then
   `#(I ∩ H) = #I_H(Q) = e(Q | Q ∩ 𝓞 K) = e(Q | p) / e(Q ∩ 𝓞 K | p) = e(Q | p) = #I`
   (Mathlib `card_inertia_eq_ramificationIdxIn` twice, `ramificationIdx_tower`), so `I ≤ H`.
2. (`inertia_fixes_field`) hence `I` fixes `K = Frac(𝓞 K)`, in particular `α`.
3. (`conj_mem_inertia`) for `σ ∈ G`, `σ⁻¹ I(Q) σ ⊆ I(σ⁻¹Q)`, and `σ⁻¹Q ∋ p`; so `I(Q)` fixes
   `σ(α)` for all `σ`, i.e. every root of `minpoly α` (`Normal.minpoly_eq_iff_mem_orbit`).
4. So `I(Q)` fixes `L`, `I(Q) = 1`, and `e(Q | p) = #I(Q) = 1`.
The argument is uniform in `p : ℕ` (no case split).
-/

open NumberField
open LeafQM.AV GlueDescent.B2Q

namespace G0ModField

/-- **Textbook (STANDARD): the Galois closure of an unramified field is unramified.** If
`ℚ(α) ⊆ ℚ̄` is unramified at `p`, so is the splitting field `ℚ(roots of minpoly α)`, which is
the compositum of the conjugates `σℚ(α) ≅ ℚ(α)`; a compositum of number fields unramified at `p`
is unramified at `p` (Neukirch, *Algebraic Number Theory*, Ch. I §9 or Ch. III §2, the
compositum of unramified extensions; UNVERIFIED locator). Not in Mathlib v4.35 for
`UnramifiedAt` (cf. g0-mod-field's `UnramifiedSup`, the Galois case). -/
def UnramifiedConjugates : Prop :=
  ∀ (α : Qbar) (p : ℕ), UnramifiedAt (IntermediateField.adjoin ℚ {α}) p →
    UnramifiedAt (IntermediateField.adjoin ℚ ((minpoly ℚ α).rootSet Qbar)) p

/-! ## The abstract step: inertia fixes an unramified subfield -/

section Abstract

variable {K L : Type} [Field K] [Field L] [NumberField K] [NumberField L] [Algebra K L]
  [IsGalois ℚ L]

/-- **Inertia fixes the integers of an unramified subfield.** For number fields `K → L`, `L/ℚ`
Galois, `K` unramified at `p` (every prime of `𝓞 K` containing `p` has `e = 1` over `ℤ`), a prime
`Q ∋ p` of `𝓞 L` and `g ∈ I(Q) ≤ Gal(L/ℚ)`: `g` fixes the image of `𝓞 K`. -/
theorem inertia_le_fixing (p : ℕ)
    (hK : ∀ P : Ideal (𝓞 K), P.IsPrime → ((p : ℤ) : 𝓞 K) ∈ P → P.ramificationIdx ℤ = 1)
    (Q : Ideal (𝓞 L)) [hQ : Q.IsPrime] (hpQ : ((p : ℤ) : 𝓞 L) ∈ Q) (g : L ≃ₐ[ℚ] L)
    (hg : g ∈ Q.inertia (L ≃ₐ[ℚ] L)) (y : 𝓞 K) :
    g • algebraMap (𝓞 K) (𝓞 L) y = algebraMap (𝓞 K) (𝓞 L) y := by
  let G := L ≃ₐ[ℚ] L
  let H : Subgroup G := fixingSubgroup G (Set.range (algebraMap (𝓞 K) (𝓞 L)))
  have : IsGaloisGroup H (𝓞 K) (𝓞 L) := IsGaloisGroup.of_isScalarTower G ℤ (𝓞 L) (𝓞 K)
  let QK : Ideal (𝓞 K) := Q.under (𝓞 K)
  have : QK.IsPrime := Ideal.IsPrime.under (𝓞 K) Q
  have : Algebra.HasSeparableResidueFieldsAt (𝓞 K) (𝓞 L) QK :=
    Algebra.HasSeparableResidueFieldsAt.tower_top (Q.under ℤ) QK
  have hpQK : ((p : ℤ) : 𝓞 K) ∈ QK := by
    show algebraMap (𝓞 K) (𝓞 L) ((p : ℤ) : 𝓞 K) ∈ Q
    rw [map_intCast]; exact hpQ
  have he1 : QK.ramificationIdx ℤ = 1 := hK QK inferInstance hpQK
  have htower : Q.ramificationIdx ℤ = QK.ramificationIdx ℤ * Q.ramificationIdx (𝓞 K) :=
    Ideal.ramificationIdx_tower (R := ℤ) QK Q
  have hcardH : Nat.card (Q.inertia H) = Q.ramificationIdx (𝓞 K) := by
    rw [Ideal.card_inertia_eq_ramificationIdxIn (G := H) QK Q,
      Ideal.ramificationIdxIn_eq_ramificationIdx QK Q H]
  have hcardG : Nat.card (Q.inertia G) = Q.ramificationIdx ℤ := by
    rw [Ideal.card_inertia_eq_ramificationIdxIn (G := G) (Q.under ℤ) Q,
      Ideal.ramificationIdxIn_eq_ramificationIdx (Q.under ℤ) Q G]
  have hcard : Nat.card ((Q.inertia G).subgroupOf H) = Nat.card (Q.inertia G) := by
    rw [hcardG, htower, he1, _root_.one_mul, ← hcardH]; rfl
  have hle : Q.inertia G ≤ H := by
    have h1 : Nat.card ((Q.inertia G) ⊓ H : Subgroup G) = Nat.card (Q.inertia G) := by
      rw [← hcard, ← Subgroup.subgroupOf_map_subtype]
      exact Subgroup.card_map_of_injective H.subtype_injective
    have h2 : (Q.inertia G) ⊓ H = Q.inertia G :=
      Subgroup.eq_of_le_of_card_ge inf_le_left h1.ge
    exact inf_eq_left.mp h2
  exact (mem_fixingSubgroup_iff G).mp (hle hg) _ ⟨y, rfl⟩


/-- **Inertia fixes an unramified subfield** (`K = Frac(𝓞 K)`). -/
theorem inertia_fixes_field (p : ℕ)
    (hK : ∀ P : Ideal (𝓞 K), P.IsPrime → ((p : ℤ) : 𝓞 K) ∈ P → P.ramificationIdx ℤ = 1)
    (Q : Ideal (𝓞 L)) [hQ : Q.IsPrime] (hpQ : ((p : ℤ) : 𝓞 L) ∈ Q) (g : L ≃ₐ[ℚ] L)
    (hg : g ∈ Q.inertia (L ≃ₐ[ℚ] L)) (x : K) : g (algebraMap K L x) = algebraMap K L x := by
  obtain ⟨a, b, -, rfl⟩ := IsFractionRing.div_surjective (A := 𝓞 K) x
  have h : ∀ y : 𝓞 K, g (algebraMap K L (algebraMap (𝓞 K) K y)) =
      algebraMap K L (algebraMap (𝓞 K) K y) := fun y =>
    congrArg (fun z : 𝓞 L => (z : L)) (inertia_le_fixing p hK Q hpQ g hg y)
  rw [map_div₀, map_div₀, h a, h b]

omit [IsGalois ℚ L] in
/-- **Conjugation of inertia**: `σ⁻¹ I(Q) σ ⊆ I(σ⁻¹ Q)`, where `σ⁻¹ Q = {x | σ x ∈ Q}`. -/
theorem conj_mem_inertia (Q : Ideal (𝓞 L)) (g σ : L ≃ₐ[ℚ] L)
    (hg : g ∈ Q.inertia (L ≃ₐ[ℚ] L)) :
    σ⁻¹ * g * σ ∈ (Q.comap (MulSemiringAction.toRingHom (L ≃ₐ[ℚ] L) (𝓞 L) σ)).inertia
      (L ≃ₐ[ℚ] L) := by
  rw [Ideal.mem_inertia] at hg ⊢
  intro x
  show MulSemiringAction.toRingHom (L ≃ₐ[ℚ] L) (𝓞 L) σ ((σ⁻¹ * g * σ) • x - x) ∈ Q
  rw [map_sub]
  simp only [MulSemiringAction.toRingHom_apply, mul_smul, smul_inv_smul]
  exact hg (σ • x)

end Abstract

/-- A finite intermediate field of `ℚ̄/ℚ` is a number field. -/
theorem numberField_of_fd (F : IntermediateField ℚ Qbar) [FiniteDimensional ℚ F] :
    NumberField F :=
  { to_charZero := inferInstance, to_finiteDimensional := inferInstance }

/-- **`UnramifiedConjugates`, proved** (no leaf, no glue Prop). -/
theorem unramifiedConjugates : UnramifiedConjugates := by
  classical
  intro α p hK
  have hαint : IsIntegral ℚ α := Algebra.IsIntegral.isIntegral α
  have hf0 : minpoly ℚ α ≠ 0 := minpoly.ne_zero hαint
  set K : IntermediateField ℚ Qbar := IntermediateField.adjoin ℚ {α} with hKdef
  set L : IntermediateField ℚ Qbar :=
    IntermediateField.adjoin ℚ ((minpoly ℚ α).rootSet Qbar) with hLdef
  have hroot : ∀ β ∈ (minpoly ℚ α).rootSet Qbar, β ∈ L :=
    fun β hβ => IntermediateField.subset_adjoin _ _ hβ
  have hαroot : α ∈ (minpoly ℚ α).rootSet Qbar :=
    (Polynomial.mem_rootSet).2 ⟨hf0, minpoly.aeval ℚ α⟩
  have hαL : α ∈ L := hroot α hαroot
  have hKL : K ≤ L := IntermediateField.adjoin_simple_le_iff.2 hαL
  have : Polynomial.IsSplittingField ℚ L (minpoly ℚ α) :=
    IntermediateField.adjoin_rootSet_isSplittingField (IsAlgClosed.splits _)
  have : FiniteDimensional ℚ L := Polynomial.IsSplittingField.finiteDimensional L (minpoly ℚ α)
  have : IsGalois ℚ L :=
    IsGalois.of_separable_splitting_field (minpoly.irreducible hαint).separable
  have : FiniteDimensional ℚ K := IntermediateField.adjoin.finiteDimensional hαint
  have : NumberField K := numberField_of_fd K
  have : NumberField L := numberField_of_fd L
  let : Algebra K L := (IntermediateField.inclusion hKL).toRingHom.toAlgebra
  intro Q hQ hpQ
  -- every element of the inertia group fixes every root of `minpoly α`
  have hfix : ∀ g ∈ Q.inertia (L ≃ₐ[ℚ] L), ∀ β (hβ : β ∈ (minpoly ℚ α).rootSet Qbar),
      g ⟨β, hroot β hβ⟩ = ⟨β, hroot β hβ⟩ := by
    intro g hg β hβ
    have hβ0 : Polynomial.aeval β (minpoly ℚ α) = 0 := ((Polynomial.mem_rootSet).1 hβ).2
    have hmin : minpoly ℚ (⟨β, hroot β hβ⟩ : L) = minpoly ℚ (⟨α, hαL⟩ : L) := by
      rw [← minpoly.algHom_eq L.val Subtype.val_injective (⟨β, hroot β hβ⟩ : L),
        ← minpoly.algHom_eq L.val Subtype.val_injective (⟨α, hαL⟩ : L)]
      exact (minpoly.eq_of_irreducible_of_monic (minpoly.irreducible hαint) hβ0
        (minpoly.monic hαint)).symm
    obtain ⟨σ, hσ⟩ := (Normal.minpoly_eq_iff_mem_orbit (F := ℚ) (E := L)).mp hmin
    -- `σ⁻¹ g σ` lies in the inertia group of `σ⁻¹ Q`, which contains `p`
    let Q' : Ideal (𝓞 L) := Q.comap (MulSemiringAction.toRingHom (L ≃ₐ[ℚ] L) (𝓞 L) σ)
    have : Q'.IsPrime := Ideal.comap_isPrime _ _
    have hpQ' : ((p : ℤ) : 𝓞 L) ∈ Q' := by
      show MulSemiringAction.toRingHom (L ≃ₐ[ℚ] L) (𝓞 L) σ ((p : ℤ) : 𝓞 L) ∈ Q
      rw [map_intCast]; exact hpQ
    have h1 := inertia_fixes_field (K := K) (L := L) p hK Q' hpQ' (σ⁻¹ * g * σ)
      (conj_mem_inertia Q g σ hg) ⟨α, IntermediateField.mem_adjoin_simple_self ℚ α⟩
    have h2 : algebraMap K L ⟨α, IntermediateField.mem_adjoin_simple_self ℚ α⟩ =
        (⟨α, hαL⟩ : L) := rfl
    rw [h2] at h1
    have h3 : (⟨β, hroot β hβ⟩ : L) = σ ⟨α, hαL⟩ := hσ.symm
    rw [h3]
    have h4 := congrArg σ h1
    simpa [AlgEquiv.mul_apply] using h4
  -- hence the inertia group is trivial
  have htriv : ∀ g ∈ Q.inertia (L ≃ₐ[ℚ] L), g = 1 := by
    intro g hg
    let s : Qbar ≃ₐ[ℚ] Qbar := g.liftNormal Qbar
    have hs : ∀ y : L, s (y : Qbar) = ((g y : L) : Qbar) :=
      fun y => AlgEquiv.liftNormal_commutes g Qbar y
    have hsroot : ∀ β ∈ (minpoly ℚ α).rootSet Qbar, s β = β := by
      intro β hβ
      have := hs ⟨β, hroot β hβ⟩
      rw [hfix g hg β hβ] at this
      exact this
    have hL' : L ≤ IntermediateField.fixedField (Subgroup.zpowers s) := by
      rw [hLdef, IntermediateField.adjoin_le_iff]
      intro β hβ
      rw [SetLike.mem_coe, IntermediateField.mem_fixedField_iff]
      intro f hf
      have hsβ : s ∈ MulAction.stabilizer (Qbar ≃ₐ[ℚ] Qbar) β :=
        MulAction.mem_stabilizer_iff.mpr (hsroot β hβ)
      exact MulAction.mem_stabilizer_iff.mp ((Subgroup.zpowers_le.mpr hsβ) hf)
    apply AlgEquiv.ext
    intro y
    apply Subtype.ext
    have hy := hL' y.2 ⟨s, Subgroup.mem_zpowers s⟩
    rw [← hs]
    exact hy
  have hcard : Nat.card (Q.inertia (L ≃ₐ[ℚ] L)) = 1 := by
    rw [Nat.card_eq_one_iff_unique]
    refine ⟨⟨fun a b => Subtype.ext ((htriv a a.2).trans (htriv b b.2).symm)⟩, ⟨1⟩⟩
  rw [← Ideal.ramificationIdxIn_eq_ramificationIdx (Q.under ℤ) Q (L ≃ₐ[ℚ] L),
    ← Ideal.card_inertia_eq_ramificationIdxIn (G := L ≃ₐ[ℚ] L) (Q.under ℤ) Q, hcard]

end G0ModField

#print axioms G0ModField.inertia_le_fixing
#print axioms G0ModField.unramifiedConjugates
#check @G0ModField.UnramifiedConjugates
example : G0ModField.UnramifiedConjugates = ∀ (α : AlgebraicClosure ℚ) (p : ℕ),
    GlueDescent.B2Q.UnramifiedAt (IntermediateField.adjoin ℚ {α}) p →
    GlueDescent.B2Q.UnramifiedAt
      (IntermediateField.adjoin ℚ ((minpoly ℚ α).rootSet (AlgebraicClosure ℚ))) p := rfl

end LF2Root_UnramConj

namespace HDec

set_option maxHeartbeats 1000000

attribute [-instance] TauCeti.FinitePadicExtension.toAlgebra
  TauCeti.FinitePadicExtension.ofInstances TauCeti.FinitePadicExtension.toModuleFinite
  TauCeti.FinitePadicExtension.toValuativeExtension

section G0A2_b05_conjtwist
/-! ## leaf-fold2: conj-twist's later sections (scratch/conj-twist/ConjTwist.lean lines 1624-2004, verbatim; commits
3ecdd95e, 94802c43): §13 N1-surj from T5, §14-§16 N3a and `TwistCEval` proved, and
`conjTwistNontrivial_of_leaves : T5 → T26 → T35 → HomLinearLift → ConjTwistNontrivial`. Part a30 holds
lines 84-191, 206-1612 (g0-assemble2). The `open`s are the file's lines 41-43 and 718. -/
noncomputable section

namespace G0Galois

open PkgI4 (GaloisRep GaloisChar)
open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct CategoryTheory.Obj
open ZInQ.LeafPush2 (CPts cptObj IsUniformization)

/-! ## §13. N1-surj from T5 and a uniformization (proved)

Given a uniformization `Φ : ℂ^g → A(ℂ)_σ` with full lattice `Λ`, `A(ℂ)[n]` injects into
`(ℤ/n)^{2g}` (`Q = Φ(z) ↦` the coordinates of `nz ∈ Λ` mod `n`), and `A(K̄)[n] ≅ (ℤ/n)^{2g}` by T5
(`PkgI2.TorsionStructure`). `toC` is injective, so it is a bijection on `n`-torsion. -/

/-- **Torsion surjectivity from T5 (proved).** -/
theorem torsion_surj_of_T5 (h5 : PkgI2.TorsionStructure.{0}) {K : Type} [Field K]
    (A : PkgI3.AbVar K) (emb : AlgebraicClosure K →+* ℂ) (g : ℕ) (Λ : Submodule ℤ (Fin g → ℂ))
    [DiscreteTopology Λ] [IsZLattice ℝ Λ]
    (Φ : (Fin g → ℂ) → CPts A (emb.comp (algebraMap K (AlgebraicClosure K))))
    (hΦ : IsUniformization (emb.comp (algebraMap K (AlgebraicClosure K))) Λ Φ)
    (hd : A.dim = (g : WithBot ℕ∞)) (n : ℕ) (hn : 0 < n)
    (Q : CPts A (emb.comp (algebraMap K (AlgebraicClosure K)))) (hQ : Q ^ n = 1) :
    ∃ P, toC A emb P = Q := by
  classical
  haveI := ZLattice.module_finite ℝ Λ
  haveI := ZLattice.module_free ℝ Λ
  let b := Module.Free.chooseBasis ℤ Λ
  have hnK : (n : K) ≠ 0 := by
    intro h0
    have := congrArg (emb.comp (algebraMap K (AlgebraicClosure K))) h0
    rw [map_natCast, map_zero] at this
    exact (Nat.cast_ne_zero.mpr hn.ne') this
  obtain ⟨e, -⟩ := h5 K (ObjBridge.toGrp A) g n hd hn hnK
  let S := {P : A.Pt (AlgebraicClosure K) // P ^ n = 1}
  let T := {Q : CPts A (emb.comp (algebraMap K (AlgebraicClosure K))) // Q ^ n = 1}
  let f : S → T := fun P => ⟨toC A emb P.1, by rw [← map_pow, P.2, map_one]⟩
  have hf : Function.Injective f := fun P P' h =>
    Subtype.ext (toC_injective A emb (congrArg Subtype.val h))
  have hpre : ∀ Q : T, ∃ z, Φ z = Q.1 := fun Q => hΦ.2.2.1 Q.1
  choose zz hzz using hpre
  have hnz : ∀ Q : T, n • zz Q ∈ Λ := fun Q => by
    rw [← hΦ.2.1, phi_nsmul A emb Φ hΦ.1, hzz, Q.2]
  let code : T → (Module.Free.ChooseBasisIndex ℤ Λ → ZMod n) := fun Q i =>
    ((b.repr ⟨n • zz Q, hnz Q⟩ i : ℤ) : ZMod n)
  have hcode : Function.Injective code := by
    intro Q Q' hQQ
    have hdvd : ∀ i, (n : ℤ) ∣ b.repr ⟨n • zz Q', hnz Q'⟩ i - b.repr ⟨n • zz Q, hnz Q⟩ i :=
      fun i => (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ _).mp (congrFun hQQ i)
    choose k hk using hdvd
    let mu : Λ := ∑ i, k i • b i
    have hmu : (⟨n • zz Q', hnz Q'⟩ : Λ) - ⟨n • zz Q, hnz Q⟩ = (n : ℤ) • mu := by
      apply b.repr.injective
      refine Finsupp.ext fun i => ?_
      rw [map_sub, Finsupp.sub_apply, hk i, map_smul, Finsupp.smul_apply, smul_eq_mul]
      congr 1
      exact (congrFun (b.repr_sum_self k) i).symm
    have hvec : n • zz Q' - n • zz Q = (n : ℤ) • (mu : Fin g → ℂ) := by
      have := congrArg Subtype.val hmu
      simpa using this
    have e3 : (n : ℂ) • (zz Q' - zz Q) = (n : ℂ) • (mu : Fin g → ℂ) := by
      rw [smul_sub, Nat.cast_smul_eq_nsmul, Nat.cast_smul_eq_nsmul, Nat.cast_smul_eq_nsmul, hvec,
        natCast_zsmul]
    have e4 : zz Q' - zz Q = mu :=
      smul_right_injective (Fin g → ℂ) (Nat.cast_ne_zero.mpr hn.ne' : (n : ℂ) ≠ 0) e3
    apply Subtype.ext
    rw [← hzz Q, ← hzz Q', show zz Q' = zz Q + mu by rw [← e4]; abel, hΦ.1,
      (hΦ.2.1 _).mpr mu.2, _root_.mul_one]
  haveI : NeZero n := ⟨hn.ne'⟩
  haveI : Finite T := Finite.of_injective code hcode
  have hcardS : Nat.card S = n ^ (2 * g) := by
    have hSe : Nat.card S = Nat.card (Fin (2 * g) → ZMod n) := Nat.card_congr e
    rw [hSe, Nat.card_fun, Nat.card_zmod,
      Nat.card_eq_fintype_card, Fintype.card_fin]
  have hcardT : Nat.card T ≤ n ^ (2 * g) := by
    have h1 := Nat.card_le_card_of_injective code hcode
    rw [Nat.card_fun, Nat.card_zmod,
      Nat.card_eq_fintype_card (α := Module.Free.ChooseBasisIndex ℤ Λ),
      ← Module.finrank_eq_card_chooseBasisIndex, ZLattice.rank ℝ Λ,
      Module.finrank_pi_fintype] at h1
    simp only [Complex.finrank_real_complex, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, smul_eq_mul] at h1
    simpa [mul_comm] using h1
  have hbij := hf.bijective_of_nat_card_le (hcardS ▸ hcardT)
  obtain ⟨P, hP⟩ := hbij.2 ⟨Q, hQ⟩
  exact ⟨P.1, congrArg Subtype.val hP⟩

/-- **N4' from T5 (proved).** -/
theorem tateLatticeInj_of_T5 (h5 : PkgI2.TorsionStructure.{0}) : TateLatticeInj := by
  intro K _ A emb g Λ Φ hd _ hlat hΦ ℓ _
  haveI := ZLattice.module_finite ℝ Λ
  haveI := ZLattice.module_free ℝ Λ
  have hsurj := fun n hn Q hQ => torsion_surj_of_T5 h5 A emb g Λ Φ hΦ hd n hn Q hQ
  refine ⟨(xLin A emb Φ ℓ hΦ.1 hΦ.2.1 hsurj).liftBaseChange ℤ_[ℓ],
    xLin_liftBaseChange_injective A emb Φ ℓ hΦ.1 hΦ.2.1 hsurj, fun lam n => ?_⟩
  rw [LinearMap.liftBaseChange_one_tmul]
  exact xSeq_apply A emb Φ ℓ hΦ.1 hΦ.2.1 hsurj lam n

/-- **Final: `ConjTwistNontrivial` from T5, T26, T35, N2 and N3a (proved).** -/
theorem conjTwistNontrivial_final (h5 : PkgI2.TorsionStructure.{0})
    (hT : PkgI3.TateModuleFree) (h35 : ZInQ.LeafPush2.UniformizationExists)
    (hN2 : HomLinearLift) (hN3a : ConjUniformization) : ConjTwistNontrivial :=
  conjTwistNontrivial_of_latticeInj hT h35 hN2 (conjAntiLiftLat_of hN2 hN3a)
    (tateLatticeInj_of_T5 h5)

/-- **Final: `ConjTwistFromLeaves` from N2 and N3a (proved).** T5, T26 and T35 are among the
hypotheses of `ConjTwistFromLeaves`. -/
theorem conjTwistFromLeaves_final (hN2 : HomLinearLift) (hN3a : ConjUniformization) :
    ConjTwistFromLeaves :=
  fun _ _ h35 h5 hT => conjTwistNontrivial_final h5 hT h35 hN2 hN3a

/-! ## §14. N3a split: group-theoretic clauses (proved) and analytic clauses (glue) -/

theorem twistC_inj_aux' {K : Type} [Field K] (σ : K →+* ℂ) (s : K →+* K)
    (h : σ.comp s = (starRingEnd ℂ).comp σ) :
    mapPtIso σ s ≫ conjHom σ s h ≫ conjHomInv σ s h ≫ mapPtIsoInv σ s = 𝟙 _ := by
  apply Over.OverMorphism.ext
  change 𝟙 _ ≫ Spec.map (CommRingCat.ofHom (starRingEnd ℂ)) ≫
    Spec.map (CommRingCat.ofHom (starRingEnd ℂ)) ≫ 𝟙 _ = 𝟙 _
  rw [Category.id_comp, Category.comp_id, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  rw [show (starRingEnd ℂ).comp (starRingEnd ℂ) = RingHom.id ℂ by ext x; simp,
    CommRingCat.ofHom_id, Spec.map_id]

theorem twistC_surjective {K : Type} [Field K] (A : PkgI3.AbVar K) (σ : K →+* ℂ) (s : K →+* K)
    (h : σ.comp s = (starRingEnd ℂ).comp σ) : Function.Surjective (twistC A σ s h) := by
  intro Q'
  obtain ⟨X, hX⟩ := ((Over.mapPullbackAdj (specS s)).homEquiv (cptObj σ) A.X).surjective
    (show cptObj σ ⟶ (Over.pullback (specS s)).obj A.X from Q')
  refine ⟨conjHomInv σ s h ≫ mapPtIsoInv σ s ≫ X, ?_⟩
  have e : mapPtIso σ s ≫ conjHom σ s h ≫ conjHomInv σ s h ≫ mapPtIsoInv σ s ≫ X = X := by
    have := congrArg (· ≫ X) (twistC_inj_aux' σ s h)
    simpa only [Category.assoc, Category.id_comp] using this
  change (Over.mapPullbackAdj (specS s)).homEquiv _ _ (mapPtIso σ s ≫ conjHom σ s h ≫
    conjHomInv σ s h ≫ mapPtIsoInv σ s ≫ X) = Q'
  rw [e]
  exact hX

theorem twistC_mul {K : Type} [Field K] (A : PkgI3.AbVar K) (σ : K →+* ℂ) (s : K →+* K)
    (h : σ.comp s = (starRingEnd ℂ).comp σ) (Q Q' : CPts A σ) :
    twistC A σ s h (Q * Q') = twistC A σ s h Q * twistC A σ s h Q' := by
  change (Over.mapPullbackAdj (specS s)).homEquiv _ _ (mapPtIso σ s ≫ conjHom σ s h ≫ (Q * Q')) =
    (Over.mapPullbackAdj (specS s)).homEquiv _ _ (mapPtIso σ s ≫ conjHom σ s h ≫ Q) *
    (Over.mapPullbackAdj (specS s)).homEquiv _ _ (mapPtIso σ s ≫ conjHom σ s h ≫ Q')
  rw [MonObj.comp_mul, MonObj.comp_mul, homEquiv_mul_conj]

/-- **N3a-an. The analytic clauses for the conjugate uniformization (GLUE, unproved;
STANDARD).** With `ψ(z) = twistC(Φ(z̄))`: the preimages `ψ⁻¹(U(ℂ))` of opens `U` of `A^s` are
open, and regular functions of `A^s` are holomorphic along `ψ`. (`A^s(ℂ)_σ = A(ℂ)_{conj∘σ}`; on
affine charts `twistC` conjugates the values of regular functions, and `z ↦ conj(f(z̄))` is
holomorphic when `f` is; Mumford §1, GAGA.) These are the last two clauses of
`IsUniformization`; the first three are proved (`conjUniformization_of_analytic`). -/
def ConjUniformizationAnalytic : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (A : PkgI3.AbVar K) (σ : K →+* ℂ) (s : K →+* K)
    (h : σ.comp s = (starRingEnd ℂ).comp σ) (g : ℕ) (Λ : Submodule ℤ (Fin g → ℂ))
    (Φ : (Fin g → ℂ) → CPts A σ),
    A.dim = (g : WithBot ℕ∞) → IsUniformization σ Λ Φ →
    (∀ U, IsOpen (ZInQ.LeafPush2.cDom (fun z => twistC A σ s h (Φ (conjL g z))) U)) ∧
    (∀ U (f : Γ((conjVar A s).X.left, U)), DifferentiableOn ℂ
      (fun z => ZInQ.LeafPush2.cEvalAt (twistC A σ s h (Φ (conjL g z))) U f)
      (ZInQ.LeafPush2.cDom (fun z => twistC A σ s h (Φ (conjL g z))) U))

/-- **N3a from its analytic clauses (proved).** -/
theorem conjUniformization_of_analytic (h : ConjUniformizationAnalytic) : ConjUniformization := by
  intro K _ _ A σ s hs g Λ Φ hd hΦ
  obtain ⟨h4, h5⟩ := h K A σ s hs g Λ Φ hd hΦ
  refine ⟨fun z w => ?_, fun z => ?_, fun Q => ?_, h4, h5⟩
  · beta_reduce
    rw [map_add, hΦ.1, twistC_mul]
  · beta_reduce
    rw [Submodule.mem_comap, LinearMap.restrictScalars_apply, ← hΦ.2.1]
    constructor
    · intro h1
      apply twistC_injective A σ s hs
      rw [h1, twistC_one]
    · intro h1
      rw [h1, twistC_one]
  · obtain ⟨Q₀, rfl⟩ := twistC_surjective A σ s hs Q
    obtain ⟨z, hz⟩ := hΦ.2.2.1 Q₀
    exact ⟨conjL g z, by simp only [conjL_conjL, hz]⟩

/-- **Final: `ConjTwistNontrivial` from T5, T26, T35, N2 and N3a-an (proved).** -/
theorem conjTwistNontrivial_final' (h5 : PkgI2.TorsionStructure.{0})
    (hT : PkgI3.TateModuleFree) (h35 : ZInQ.LeafPush2.UniformizationExists)
    (hN2 : HomLinearLift) (hN3 : ConjUniformizationAnalytic) : ConjTwistNontrivial :=
  conjTwistNontrivial_final h5 hT h35 hN2 (conjUniformization_of_analytic hN3)

/-- **Final: `ConjTwistFromLeaves` from N2 and N3a-an (proved).** -/
theorem conjTwistFromLeaves_final' (hN2 : HomLinearLift) (hN3 : ConjUniformizationAnalytic) :
    ConjTwistFromLeaves :=
  conjTwistFromLeaves_final hN2 (conjUniformization_of_analytic hN3)

/-! ## §15. N3a-an from an evaluation identity (proved reduction)

The analytic clauses follow from a purely scheme-theoretic identity (`TwistCEval`): for a number
field, every open `U` of `A^s` is the preimage of an open `V` of `A`, and the value of a section
of `A^s` over `U` at `twistC Q` is the complex conjugate of the value of a section of `A` over `V`
at `Q`. With it, `ψ = twistC ∘ Φ ∘ conj` has open domains `conj⁻¹(cDom Φ V)` and its coordinate
functions are `z ↦ conj(F(z̄))` with `F` holomorphic (`differentiableOn_conj_conj`). -/

theorem conjL_smul {g : ℕ} (c : ℂ) (v : Fin g → ℂ) :
    conjL g (c • v) = starRingEnd ℂ c • conjL g v := by
  funext i; simp [conjL]

/-- **`z ↦ conj(F(z̄))` is holomorphic where `F` is (proved).** -/
theorem differentiableOn_conj_conj {g : ℕ} {F : (Fin g → ℂ) → ℂ} {S : Set (Fin g → ℂ)}
    (hF : DifferentiableOn ℂ F S) :
    DifferentiableOn ℂ (fun z => starRingEnd ℂ (F (conjL g z))) (conjL g ⁻¹' S) := by
  intro x hx
  obtain ⟨F', hF'⟩ := hF (conjL g x) hx
  let cV : (Fin g → ℂ) →L[ℝ] (Fin g → ℂ) := LinearMap.toContinuousLinearMap (conjL g)
  let Gl : (Fin g → ℂ) →ₗ[ℂ] ℂ :=
    { toFun := fun v => starRingEnd ℂ (F' (conjL g v))
      map_add' := fun v w => by simp [map_add]
      map_smul' := fun c v => by simp [conjL_smul, map_smul, smul_eq_mul] }
  let G' : (Fin g → ℂ) →L[ℂ] ℂ := LinearMap.toContinuousLinearMap Gl
  have h1 : HasFDerivWithinAt (fun z => F (conjL g z)) ((F'.restrictScalars ℝ).comp cV)
      (conjL g ⁻¹' S) x :=
    (hF'.restrictScalars ℝ).comp x cV.hasFDerivWithinAt (fun z hz => hz)
  have h2 := (Complex.conjCLE : ℂ →L[ℝ] ℂ).hasFDerivAt.comp_hasFDerivWithinAt x h1
  have h3 : HasFDerivWithinAt (fun z => starRingEnd ℂ (F (conjL g z))) G' (conjL g ⁻¹' S) x := by
    refine h2.of_restrictScalars ℝ ?_
    ext v
    rfl
  exact h3.differentiableWithinAt

/-- **N3a-ev. Values of sections at twisted points (GLUE, unproved; STANDARD; no analysis).**
For a number field `K` (so `A^s → A` is an isomorphism), every open `U` of `A^s` corresponds to an
open `V` of `A` with `twistC Q ∈ U ↔ Q ∈ V`, and every section `f` of `A^s` over `U` to a section
`f'` of `A` over `V` with `f(twistC Q) = conj(f'(Q))`. (`fst ∘ twistC Q = Q ∘ Spec(conj)` as maps
`Spec ℂ → A`; take `V = fst(U)`, `f = fst^* f'`; `Spec(conj)^*` is `conj` on `Γ(Spec ℂ) = ℂ`.) -/
def TwistCEval : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (A : PkgI3.AbVar K) (σ : K →+* ℂ) (s : K →+* K)
    (h : σ.comp s = (starRingEnd ℂ).comp σ) (U : (conjVar A s).X.left.Opens),
    ∃ V : A.X.left.Opens,
      (∀ Q : CPts A σ, (⊤ ≤ (twistC A σ s h Q).left ⁻¹ᵁ U ↔ ⊤ ≤ Q.left ⁻¹ᵁ V)) ∧
      ∀ f : Γ((conjVar A s).X.left, U), ∃ f' : Γ(A.X.left, V), ∀ Q : CPts A σ,
        ⊤ ≤ Q.left ⁻¹ᵁ V →
        ZInQ.LeafPush2.cEvalAt (twistC A σ s h Q) U f =
          starRingEnd ℂ (ZInQ.LeafPush2.cEvalAt Q V f')

/-- **N3a-an (number fields) from N3a-ev (proved).** -/
theorem conjUniformizationAnalytic_of_eval (hE : TwistCEval) : ConjUniformizationAnalytic := by
  intro K _ _ A σ s h g Λ Φ hd hΦ
  have hdom : ∀ U, ∃ V : A.X.left.Opens,
      ZInQ.LeafPush2.cDom (fun z => twistC A σ s h (Φ (conjL g z))) U =
        conjL g ⁻¹' ZInQ.LeafPush2.cDom Φ V ∧
      ∀ f : Γ((conjVar A s).X.left, U), ∃ f' : Γ(A.X.left, V), ∀ z,
        z ∈ conjL g ⁻¹' ZInQ.LeafPush2.cDom Φ V →
        ZInQ.LeafPush2.cEvalAt (twistC A σ s h (Φ (conjL g z))) U f =
          starRingEnd ℂ (ZInQ.LeafPush2.cEvalAt (Φ (conjL g z)) V f') := by
    intro U
    obtain ⟨V, hV, hf⟩ := hE K A σ s h U
    refine ⟨V, ?_, fun f => ?_⟩
    · ext z
      exact hV (Φ (conjL g z))
    · obtain ⟨f', hf'⟩ := hf f
      exact ⟨f', fun z hz => hf' _ hz⟩
  have hcont : Continuous (conjL g) :=
    (LinearMap.toContinuousLinearMap (conjL g)).continuous
  refine ⟨fun U => ?_, fun U f => ?_⟩
  · obtain ⟨V, hV, -⟩ := hdom U
    rw [hV]
    exact (hΦ.2.2.2.1 V).preimage hcont
  · obtain ⟨V, hV, hf⟩ := hdom U
    obtain ⟨f', hf'⟩ := hf f
    rw [hV]
    exact (differentiableOn_conj_conj (hΦ.2.2.2.2 V f')).congr fun z hz => hf' z hz

/-- **Final: `ConjTwistNontrivial` from T5, T26, T35, N2 and N3a-ev (proved).** -/
theorem conjTwistNontrivial_final'' (h5 : PkgI2.TorsionStructure.{0})
    (hT : PkgI3.TateModuleFree) (h35 : ZInQ.LeafPush2.UniformizationExists)
    (hN2 : HomLinearLift) (hE : TwistCEval) : ConjTwistNontrivial :=
  conjTwistNontrivial_final' h5 hT h35 hN2 (conjUniformizationAnalytic_of_eval hE)

/-- **Final: `ConjTwistFromLeaves` from N2 and N3a-ev (proved).** -/
theorem conjTwistFromLeaves_final'' (hN2 : HomLinearLift) (hE : TwistCEval) :
    ConjTwistFromLeaves :=
  conjTwistFromLeaves_final' hN2 (conjUniformizationAnalytic_of_eval hE)

/-! ## §16. `TwistCEval` (N3a-ev) proved

For a number field `Spec(s)` is an isomorphism, hence so is `fst : A^s → A`. The adjunction gives
`(twistC Q).left ≫ fst = Spec(conj) ≫ Q.left`, so `(twistC Q).left = Spec(conj) ≫ Q.left ≫ fst⁻¹`;
take `V = (fst⁻¹)⁻¹(U)`, `f' = (fst⁻¹)^* f`, and use `ΓSpecIso` naturality for `Spec(conj)`. -/

/-- `Spec(conj) : Spec ℂ → Spec ℂ`. -/
abbrev specConj : Spec (CommRingCat.of ℂ) ⟶ Spec (CommRingCat.of ℂ) :=
  Spec.map (CommRingCat.ofHom (starRingEnd ℂ))

theorem appLE_eq_of_eq {X Y : Scheme} {f g : X ⟶ Y} (e : f = g) (U : Y.Opens) (V : X.Opens)
    (h : V ≤ f ⁻¹ᵁ U) : f.appLE U V h = g.appLE U V (e ▸ h) := by
  subst e; rfl

theorem top_le_specConj_preimage (W : (Spec (CommRingCat.of ℂ)).Opens) :
    ⊤ ≤ specConj ⁻¹ᵁ W ↔ ⊤ ≤ W := by
  constructor
  · intro hW x _
    have hx : x = specConj.base (IsLocalRing.closedPoint ℂ) := Subsingleton.elim _ _
    rw [hx]
    exact hW (Set.mem_univ (IsLocalRing.closedPoint ℂ))
  · intro hW y _
    exact hW (Set.mem_univ (specConj.base y))

/-- Evaluation at `P ∘ Spec(conj)` is the complex conjugate of evaluation at `P` (proved). -/
theorem eval_specConj {X : Scheme} (P : Spec (CommRingCat.of ℂ) ⟶ X) (W : X.Opens)
    (hW : ⊤ ≤ (specConj ≫ P) ⁻¹ᵁ W) (hW' : ⊤ ≤ P ⁻¹ᵁ W) (x : Γ(X, W)) :
    (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom ((specConj ≫ P).appLE W ⊤ hW x) =
      starRingEnd ℂ ((Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom (P.appLE W ⊤ hW' x)) := by
  have e2 : ⊤ ≤ specConj ⁻¹ᵁ (⊤ : (Spec (CommRingCat.of ℂ)).Opens) := fun x _ => Set.mem_univ _
  rw [← Scheme.Hom.appLE_comp_appLE specConj P W ⊤ ⊤ hW' e2]
  have e3 : specConj.appLE ⊤ ⊤ e2 = specConj.appTop := by
    rw [Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE]
    rfl
  rw [e3]
  have h := Scheme.ΓSpecIso_naturality (CommRingCat.ofHom (starRingEnd ℂ))
  have := congrArg (fun φ => (CommRingCat.Hom.hom φ) (P.appLE W ⊤ hW' x)) h
  exact this

theorem homEquiv_left_fst {K : Type} [Field K] (s : K →+* K) (X Y : Over (Spec (CommRingCat.of K)))
    (u : (Over.map (specS s)).obj X ⟶ Y) :
    ((Over.mapPullbackAdj (specS s)).homEquiv X Y u).left ≫ Limits.pullback.fst Y.hom (specS s) =
      u.left := by
  dsimp [Over.mapPullbackAdj]
  simp

theorem fst_isIso {K : Type} [Field K] [NumberField K] (A : PkgI3.AbVar K) (s : K →+* K) :
    IsIso (Limits.pullback.fst A.X.hom (specS s)) := by
  have hb := ringHom_bijective_of_numberField K s
  let e : K ≃+* K := RingEquiv.ofBijective s hb
  haveI : IsIso (CommRingCat.ofHom s) :=
    ⟨⟨CommRingCat.ofHom (e.symm : K →+* K), by ext x; exact e.symm_apply_apply x,
      by ext x; exact e.apply_symm_apply x⟩⟩
  haveI : IsIso (specS s) := by unfold specS; infer_instance
  infer_instance

/-- **N3a-ev (proved).** -/
theorem twistCEval : TwistCEval := by
  intro K _ _ A σ s h U
  let fstC : (conjVar A s).X.left ⟶ A.X.left := Limits.pullback.fst A.X.hom (specS s)
  haveI : IsIso fstC := fst_isIso A s
  let iv : A.X.left ⟶ (conjVar A s).X.left := CategoryTheory.inv fstC
  let QL : CPts A σ → (Spec (CommRingCat.of ℂ) ⟶ A.X.left) := fun Q => Q.left
  let TL : CPts A σ → (Spec (CommRingCat.of ℂ) ⟶ (conjVar A s).X.left) :=
    fun Q => (twistC A σ s h Q).left
  have key : ∀ Q : CPts A σ, TL Q = specConj ≫ QL Q ≫ iv := by
    intro Q
    have e1 : TL Q ≫ fstC = specConj ≫ QL Q :=
      (homEquiv_left_fst s (cptObj σ) A.X (mapPtIso σ s ≫ conjCs A σ s h Q)).trans
        (Category.id_comp _)
    calc TL Q = (TL Q ≫ fstC) ≫ iv := by
          rw [Category.assoc, IsIso.hom_inv_id, Category.comp_id]
      _ = specConj ≫ QL Q ≫ iv := by rw [e1, Category.assoc]
  refine ⟨iv ⁻¹ᵁ U, fun Q => ?_, fun f => ⟨iv.app U f, fun Q hQ => ?_⟩⟩
  · change ⊤ ≤ TL Q ⁻¹ᵁ U ↔ ⊤ ≤ QL Q ⁻¹ᵁ (iv ⁻¹ᵁ U)
    rw [key Q]
    change ⊤ ≤ specConj ⁻¹ᵁ ((QL Q ≫ iv) ⁻¹ᵁ U) ↔ _
    rw [top_le_specConj_preimage]
    rfl
  · have hQ' : ⊤ ≤ TL Q ⁻¹ᵁ U := by
      rw [key Q]
      change ⊤ ≤ specConj ⁻¹ᵁ ((QL Q ≫ iv) ⁻¹ᵁ U)
      rw [top_le_specConj_preimage]
      exact hQ
    unfold ZInQ.LeafPush2.cEvalAt
    rw [dif_pos (show ⊤ ≤ (twistC A σ s h Q).left ⁻¹ᵁ U from hQ'), dif_pos hQ]
    change (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom ((TL Q).appLE U ⊤ hQ' f) =
      starRingEnd ℂ ((Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom
        ((QL Q).appLE (iv ⁻¹ᵁ U) ⊤ hQ (iv.app U f)))
    rw [appLE_eq_of_eq (key Q),
      eval_specConj (QL Q ≫ iv) U _ (show ⊤ ≤ (QL Q ≫ iv) ⁻¹ᵁ U from hQ),
      Scheme.Hom.comp_appLE]
    rfl

/-- **Final: `ConjTwistNontrivial` from T5, T26, T35 and N2 (proved).** -/
theorem conjTwistNontrivial_of_leaves (h5 : PkgI2.TorsionStructure.{0})
    (hT : PkgI3.TateModuleFree) (h35 : ZInQ.LeafPush2.UniformizationExists)
    (hN2 : HomLinearLift) : ConjTwistNontrivial :=
  conjTwistNontrivial_final'' h5 hT h35 hN2 twistCEval

/-- **Final: `ConjTwistFromLeaves` from the leaf N2 alone (proved).** -/
theorem conjTwistFromLeaves_of_homLinearLift (hN2 : HomLinearLift) : ConjTwistFromLeaves :=
  conjTwistFromLeaves_final'' hN2 twistCEval

/-! ## §17. Corollaries for G10 (verbatim copies from `scratch/g10-odd/G10Odd.lean`)

`G10Glue`, `G10GlueConcrete` and their reductions `g10Glue_of_conjTwist`,
`g10GlueConcrete_of_conjTwistFromLeaves` are copied verbatim (with `Vb`, `tate`, `Intertwines`,
`G10Out`, the opaque `HSyn.T11_RiemannGAGA`, `HSyn.T12_ArtinComparison` and the algebraic
lemmas), then composed with the main results. -/

end G0Galois

end

end G0A2_b05_conjtwist

section G0A2_b07_infrastalks
/-! ## leaf-fold2: infra-stalks (scratch/infra-stalks/HeightBCGlue.lean lines 2955-3301, its Part 3, verbatim except
that the lines `open PkgI3 (AbVar)` are deleted, as g0-assemble2 did for part a20, and its two `#print` lines; Part 1 is module LF2Stalks) -/


namespace ZInQ.HeightBC

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open NumberField DefFaltings


/-! # infra-stalks: `CotangentSpanBC` from the stalk of a fibre product -/

section InfraStalks

variable {K : Type} [Field K] {A : AbVar K}

/-- The unit section is a section of the structure morphism. -/
theorem unitSection_comp_hom {L : Type} [Field L] [NumberField L] [Algebra K L]
    (𝒢 : GroupModel A L) : 𝒢.unitSection ≫ 𝒢.G.hom = 𝟙 _ := by
  unfold GroupModel.unitSection
  simpa using Over.w η[𝒢.G]

theorem hom_genericUnit {L : Type} [Field L] [NumberField L] [Algebra K L]
    (𝒢 : GroupModel A L) : 𝒢.G.hom 𝒢.genericUnit = genericPt L := by
  unfold GroupModel.genericUnit
  rw [← Scheme.Hom.comp_apply, unitSection_comp_hom]
  rfl

theorem rationalOver_genericUnit {L : Type} [Field L] [NumberField L] [Algebra K L]
    (𝒢 : GroupModel A L) : RationalOver 𝒢.G.hom 𝒢.genericUnit :=
  rationalOver_of_section _ _ (unitSection_comp_hom 𝒢) (genericPt L)

/-- The stalk of `Spec 𝓞_L` at its generic point is a field. -/
theorem isField_stalk_genericPt (L : Type) [Field L] [NumberField L]
    (y : Spec (CommRingCat.of (𝓞 L))) (hy : y = genericPt L) :
    IsField ((Spec (CommRingCat.of (𝓞 L))).presheaf.stalk y) := by
  have h : genericPt L = genericPoint (Spec (CommRingCat.of (𝓞 L))) := by
    rw [genericPoint_eq_bot_of_affine]; rfl
  rw [hy, h]
  exact Field.toIsField (Spec (CommRingCat.of (𝓞 L))).functionField

theorem maximalIdeal_stalk_genericPt (L : Type) [Field L] [NumberField L]
    (y : Spec (CommRingCat.of (𝓞 L))) (hy : y = genericPt L) :
    IsLocalRing.maximalIdeal ((Spec (CommRingCat.of (𝓞 L))).presheaf.stalk y) = ⊥ :=
  (IsLocalRing.isField_iff_maximalIdeal_eq).mp (isField_stalk_genericPt L y hy)

/-- Nonzero global functions are units at the generic point. -/
theorem isUnit_germ_genericPt (L : Type) [Field L] [NumberField L]
    (y : Spec (CommRingCat.of (𝓞 L))) (hy : y = genericPt L) (a : 𝓞 L) (ha : a ≠ 0) :
    IsUnit ((Spec (CommRingCat.of (𝓞 L))).presheaf.germ ⊤ y trivial
      ((Scheme.ΓSpecIso (CommRingCat.of (𝓞 L))).inv a)) := by
  have hF := isField_stalk_genericPt L y hy
  letI := hF.toField
  refine isUnit_iff_ne_zero.mpr fun h0 => ha ?_
  have h1 := germ_injective_of_isIntegral (Spec (CommRingCat.of (𝓞 L))) (U := ⊤) y trivial
    (h0.trans (map_zero _).symm)
  have h2 := congrArg (Scheme.ΓSpecIso (CommRingCat.of (𝓞 L))).hom h1
  rwa [Iso.inv_hom_id_apply, map_zero] at h2

theorem structMap_eq_stalkMap {L : Type} [Field L] [NumberField L] [Algebra K L]
    (𝒢 : GroupModel A L) (a : 𝓞 L) :
    𝒢.structMap a = 𝒢.G.hom.stalkMap 𝒢.genericUnit
      ((Spec (CommRingCat.of (𝓞 L))).presheaf.germ ⊤ (𝒢.G.hom 𝒢.genericUnit) trivial
        ((Scheme.ΓSpecIso (CommRingCat.of (𝓞 L))).inv a)) := by
  erw [Scheme.Hom.germ_stalkMap_apply 𝒢.G.hom ⊤ 𝒢.genericUnit (by trivial)]
  rfl

/-- Nonzero elements of `𝓞_L` are units in the local ring at the origin of the generic fibre. -/
theorem isUnit_structMap {L : Type} [Field L] [NumberField L] [Algebra K L]
    (𝒢 : GroupModel A L) (a : 𝓞 L) (ha : a ≠ 0) : IsUnit (𝒢.structMap a) := by
  rw [structMap_eq_stalkMap]
  exact (isUnit_germ_genericPt L _ (hom_genericUnit 𝒢) a ha).map _

/-- Elements of the maximal ideal act by zero on the cotangent space. -/
theorem smul_cotangent_eq_of_sub_mem {R : Type*} [CommRing R] [IsLocalRing R] {r r' : R}
    (h : r - r' ∈ IsLocalRing.maximalIdeal R) (v : IsLocalRing.CotangentSpace R) :
    r • v = r' • v := by
  obtain ⟨x, rfl⟩ := (IsLocalRing.maximalIdeal R).toCotangent_surjective v
  rw [← sub_eq_zero, ← sub_smul, ← map_smul, Ideal.toCotangent_eq_zero]
  rw [pow_two]
  exact Ideal.mul_mem_mul h x.2

/-- A nonzero `s ∈ 𝓞_L` divides a nonzero integer. -/
theorem exists_int_dvd {L : Type} [Field L] [NumberField L] (s : 𝓞 L) (hs : s ≠ 0) :
    ∃ (N : ℤ) (s' : 𝓞 L), N ≠ 0 ∧ (N : 𝓞 L) = s * s' := by
  have hlt := Ideal.under_lt_under_of_integral_mem_sdiff (R := ℤ) (I := (⊥ : Ideal (𝓞 L)))
    (J := Ideal.span {s}) bot_le (x := s)
    ⟨Ideal.mem_span_singleton_self s, by simpa using hs⟩ (Algebra.IsIntegral.isIntegral s)
  obtain ⟨N, hN, hN0⟩ := IsConcreteLE.exists_of_lt hlt
  rw [Ideal.under, Ideal.mem_comap, Ideal.mem_span_singleton] at hN
  obtain ⟨s', hs'⟩ := hN
  refine ⟨N, s', fun h => hN0 ?_, by simpa using hs'⟩
  rw [h]; exact Ideal.zero_mem _

variable {L L' : Type} [Field L] [NumberField L] [Algebra K L]
    [Field L'] [NumberField L'] [Algebra K L'] [Algebra L L']

/-- `bcCot` commutes with division by a nonzero integer. -/
theorem bcCot_intInv {𝒢 : GroupModel A L} {𝒢' : GroupModel A L'}
    {e : 𝒢'.G ≅ (Over.pullback (bO L L')).obj 𝒢.G} (he : IsMonBC 𝒢 𝒢' e) (N : ℤ) (hN : N ≠ 0)
    (u : 𝒢.cotangent) :
    ∃ u' : 𝒢.cotangent, (↑((isUnit_structMap 𝒢' (N : 𝓞 L') (by exact_mod_cast hN)).unit⁻¹) :
      𝒢'.genStalk) • bcCot he u = bcCot he u' := by
  set U := (isUnit_structMap 𝒢 (N : 𝓞 L) (by exact_mod_cast hN)).unit
  set U' := (isUnit_structMap 𝒢' (N : 𝓞 L') (by exact_mod_cast hN)).unit
  refine ⟨(↑(U⁻¹) : 𝒢.genStalk) • u, ?_⟩
  have hU : (U : 𝒢.genStalk) = (N : 𝒢.genStalk) := by
    simp [U, map_intCast]
  have hU' : (U' : 𝒢'.genStalk) = (N : 𝒢'.genStalk) := by
    simp [U', map_intCast]
  have h1 : u = (N : 𝒢.genStalk) • ((↑(U⁻¹) : 𝒢.genStalk) • u) := by
    rw [smul_smul, ← hU, Units.mul_inv, one_smul]
  have h2 : bcCot he u = (N : 𝒢'.genStalk) • bcCot he ((↑(U⁻¹) : 𝒢.genStalk) • u) := by
    conv_lhs => rw [h1]
    change bcCot he (((N : 𝒢.genStalk)) • ((↑(U⁻¹) : 𝒢.genStalk) • u)) = _
    rw [Int.cast_smul_eq_zsmul, map_zsmul, Int.cast_smul_eq_zsmul]
  rw [h2, smul_smul, ← hU', Units.inv_mul, one_smul]

/-- **`CotangentSpanBC` holds** (glue BC-cot of height-bc, statement verbatim). -/
theorem cotangentSpanBC : CotangentSpanBC := by
  intro K _ A L L' _ _ _ _ _ _ _ _ 𝒢 𝒢' e he
  set p := bcProj 𝒢 𝒢' e
  set ξ' := 𝒢'.genericUnit
  have hw : p ≫ 𝒢.G.hom = 𝒢'.G.hom ≫ bO L L' := bcProj_w 𝒢 𝒢' e
  have hgen : StalkGen p 𝒢'.G.hom ξ' := by
    have h0 := StalkGen.comp_of_isIso e.hom.left (pullback.fst 𝒢.G.hom (bO L L'))
      (pullback.snd _ _) ξ' (pullback_stalkGen _ _ _)
    have hsnd : e.hom.left ≫ pullback.snd 𝒢.G.hom (bO L L') = 𝒢'.G.hom := Over.w e.hom
    rw [hsnd] at h0
    exact h0
  have hrat : RationalOver 𝒢.G.hom (p ξ') := by
    have := rationalOver_genericUnit 𝒢
    rwa [← bcProj_genericUnit he] at this
  have hm := maximalIdeal_eq_of_stalkGen hw hgen hrat
  dsimp only [stalkIdeal] at hm
  rw [maximalIdeal_stalk_genericPt L' _ (hom_genericUnit 𝒢'), Ideal.map_bot, sup_bot_eq] at hm
  have hres := exists_sub_mem_maximalIdeal_of_stalkGen hw hgen hrat
  set N := Submodule.span (𝓞 L') (Set.range (bcCot he))
  -- `N` is stable under the local ring `𝒪_{𝒢',ξ'}`
  have hgenN : ∀ (r : 𝒢'.genStalk) (u : 𝒢.cotangent), r • bcCot he u ∈ N := by
    intro r u
    obtain ⟨b, hb⟩ := hres r
    have e1 : r • bcCot he u = 𝒢'.G.hom.stalkMap ξ' b • bcCot he u :=
      smul_cotangent_eq_of_sub_mem hb _
    rw [e1]
    -- write `b = a / s` in the stalk of `Spec 𝓞_{L'}` at the generic point
    let Y := Spec (CommRingCat.of (𝓞 L'))
    let y := 𝒢'.G.hom ξ'
    letI : Algebra Γ(Y, ⊤) (Y.presheaf.stalk y) := (Y.presheaf.germ ⊤ y trivial).hom.toAlgebra
    have hL : IsLocalization.AtPrime (Y.presheaf.stalk y)
        ((isAffineOpen_top Y).primeIdealOf ⟨y, trivial⟩).asIdeal :=
      (isAffineOpen_top Y).isLocalization_stalk ⟨y, trivial⟩
    obtain ⟨⟨a, s⟩, hbs⟩ := @IsLocalization.surj _ _ _ _ _ _ hL b
    set a0 := (Scheme.ΓSpecIso (CommRingCat.of (𝓞 L'))).hom a
    set s0 := (Scheme.ΓSpecIso (CommRingCat.of (𝓞 L'))).hom s.1
    have hs0 : s0 ≠ 0 := by
      intro h0
      apply s.2
      have : s.1 = 0 := by
        have := congrArg (Scheme.ΓSpecIso (CommRingCat.of (𝓞 L'))).inv h0
        rwa [Iso.hom_inv_id_apply, map_zero] at this
      rw [this]; exact Ideal.zero_mem _
    have hga : ∀ c : Γ(Y, ⊤), 𝒢'.G.hom.stalkMap ξ' (algebraMap Γ(Y, ⊤) _ c) =
        𝒢'.structMap ((Scheme.ΓSpecIso (CommRingCat.of (𝓞 L'))).hom c) := by
      intro c
      rw [structMap_eq_stalkMap, Iso.hom_inv_id_apply]
      rfl
    have hbs' : 𝒢'.G.hom.stalkMap ξ' b * 𝒢'.structMap s0 = 𝒢'.structMap a0 := by
      rw [← hga, ← hga, ← map_mul]; exact congrArg _ hbs
    obtain ⟨N0, s1, hN0, hN0s⟩ := exists_int_dvd s0 hs0
    obtain ⟨u', hu'⟩ := bcCot_intInv he N0 hN0 u
    set U' := (isUnit_structMap 𝒢' (N0 : 𝓞 L') (by exact_mod_cast hN0)).unit
    have hb' : 𝒢'.G.hom.stalkMap ξ' b = 𝒢'.structMap (a0 * s1) * (↑(U'⁻¹) : 𝒢'.genStalk) := by
      rw [Units.eq_mul_inv_iff_mul_eq]
      change _ = 𝒢'.structMap (a0 * s1)
      rw [show (U' : 𝒢'.genStalk) = 𝒢'.structMap (N0 : 𝓞 L') from rfl, hN0s, map_mul,
        map_mul, ← _root_.mul_assoc, hbs']
    rw [hb', mul_smul, hu']
    exact N.smul_mem (a0 * s1) (Submodule.subset_span ⟨u', rfl⟩)
  have hN : ∀ (r : 𝒢'.genStalk) (v : 𝒢'.cotangent), v ∈ N → r • v ∈ N := by
    intro r v hv
    induction hv using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨u, rfl⟩ := hx
      exact hgenN r u
    | zero => rw [smul_zero]; exact N.zero_mem
    | add x y _ _ hx hy => rw [smul_add]; exact N.add_mem hx hy
    | smul c x _ hx =>
      change r • (𝒢'.structMap c • x) ∈ N
      rw [smul_smul, mul_comm, ← smul_smul]
      exact N.smul_mem c hx
  -- every cotangent vector lies in `N`
  rw [eq_top_iff]
  rintro v -
  obtain ⟨x, rfl⟩ := (IsLocalRing.maximalIdeal 𝒢'.genStalk).toCotangent_surjective v
  obtain ⟨x, hx⟩ := x
  have hx' : x ∈ Ideal.map (p.stalkMap ξ').hom (IsLocalRing.maximalIdeal _) := hm ▸ hx
  have hmem : ∀ y, y ∈ Ideal.map (p.stalkMap ξ').hom (IsLocalRing.maximalIdeal _) →
      y ∈ IsLocalRing.maximalIdeal 𝒢'.genStalk := fun y hy => hm ▸ hy
  suffices H : ∀ y (hy : y ∈ Ideal.map (p.stalkMap ξ').hom (IsLocalRing.maximalIdeal _)),
      (IsLocalRing.maximalIdeal 𝒢'.genStalk).toCotangent ⟨y, hmem y hy⟩ ∈ N from H x hx'
  intro y hy
  induction hy using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨a, ha, rfl⟩ := hz
    haveI := isIso_stalkSpecializes_bcMap he
    set sp := 𝒢.G.left.presheaf.stalkSpecializes
      (Inseparable.of_eq (bcProj_genericUnit he)).specializes
    set a' := (inv sp).hom a
    have hsa : sp.hom a' = a := by
      simp only [a']
      rw [← CommRingCat.comp_apply, IsIso.inv_hom_id, CommRingCat.id_apply]
    have ha' : a' ∈ IsLocalRing.maximalIdeal 𝒢.genStalk := by
      intro hu
      apply ha
      rw [← hsa]
      exact hu.map sp.hom
    refine Submodule.subset_span ⟨𝒢.dCls ⟨a', ha'⟩, ?_⟩
    rw [bcCot_dCls]
    unfold GroupModel.dCls
    congr 2
    change (sp ≫ p.stalkMap ξ') a' = _
    rw [CommRingCat.comp_apply, hsa]
  | zero =>
    have : (⟨0, hmem 0 (Submodule.zero_mem _)⟩ : IsLocalRing.maximalIdeal 𝒢'.genStalk) = 0 := rfl
    rw [this, map_zero]; exact N.zero_mem
  | add z w hz hw hzN hwN =>
    have : (⟨z + w, hmem _ (Submodule.add_mem _ hz hw)⟩ : IsLocalRing.maximalIdeal 𝒢'.genStalk) =
        ⟨z, hmem z hz⟩ + ⟨w, hmem w hw⟩ := rfl
    rw [this, map_add]; exact N.add_mem hzN hwN
  | smul c z hz hzN =>
    have : (⟨c • z, hmem _ (Submodule.smul_mem _ c hz)⟩ :
        IsLocalRing.maximalIdeal 𝒢'.genStalk) = c • ⟨z, hmem z hz⟩ := rfl
    rw [this, map_smul]
    exact hN c _ hzN

end InfraStalks

end ZInQ.HeightBC




/-! # infra-stalks: `UniformizationLiftAnalytic` (height-bc) proved -/

namespace ZInQ.HeightBC

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open NumberField DefFaltings

/-- **`UniformizationLiftAnalytic` holds** (glue BC-lift-an of height-bc, statement verbatim), from
`AlgebraicGeometry.exists_localStructure_pullback` applied to `𝒢' ≅ 𝒢 ×_{𝓞_L} 𝓞_{L'}`. -/
theorem uniformizationLiftAnalytic : UniformizationLiftAnalytic := by
  intro K _ A L L' _ _ _ _ _ _ _ _ 𝒢 𝒢' e he σ τ' hστ g Λ Φ' hΦ
  let p₁ : (Fin g → ℂ) → ((GroupModel.ptC τ').left ⟶ 𝒢.G.left) :=
    fun z => (Φ' z).left ≫ bcProj 𝒢 𝒢' e
  let p₂ : (GroupModel.ptC τ').left ⟶ Spec (CommRingCat.of (𝓞 L')) := (GroupModel.ptC τ').hom
  have hsnd : e.hom.left ≫ pullback.snd 𝒢.G.hom (bO L L') = 𝒢'.G.hom := Over.w e.hom
  have hw : ∀ z, p₁ z ≫ 𝒢.G.hom = p₂ ≫ bO L L' := fun z =>
    (Category.assoc _ _ _).trans ((congrArg ((Φ' z).left ≫ ·) (bcProj_w 𝒢 𝒢' e)).trans
      ((Category.assoc _ _ _).symm.trans (congrArg (· ≫ bO L L') (Over.w (Φ' z)))))
  have hei : e.hom.left ≫ e.inv.left = 𝟙 _ := by
    rw [← Over.comp_left, e.hom_inv_id]; rfl
  have hlift : ∀ z, pullback.lift (p₁ z) p₂ (hw z) ≫ e.inv.left = (Φ' z).left := by
    intro z
    have h1 : pullback.lift (p₁ z) p₂ (hw z) = (Φ' z).left ≫ e.hom.left := by
      apply pullback.hom_ext
      · rw [pullback.lift_fst]
        exact (Category.assoc _ _ _).symm
      · rw [pullback.lift_snd]
        exact ((Over.w (Φ' z)).symm.trans (congrArg ((Φ' z).left ≫ ·) hsnd.symm)).trans
          (Category.assoc _ _ _).symm
    rw [h1]
    exact (Category.assoc _ _ _).trans ((congrArg ((Φ' z).left ≫ ·) hei).trans
      (Category.comp_id _))
  obtain ⟨-, -, -, hopen, hdiff⟩ := hΦ
  have hloc : ∀ (U : 𝒢'.G.left.Opens) (s : Γ(𝒢'.G.left, U)) (z₀ : Fin g → ℂ),
      z₀ ∈ 𝒢'.dom Φ' U → ∃ O : Set (Fin g → ℂ), IsOpen O ∧ z₀ ∈ O ∧ O ⊆ 𝒢'.dom Φ' U ∧
        DifferentiableOn ℂ (fun z => 𝒢'.evalAt (Φ' z) U s) O := by
    intro U s z₀ hz₀
    have hU : ⊤ ≤ (pullback.lift (p₁ z₀) p₂ (hw z₀) ≫ e.inv.left) ⁻¹ᵁ U := by
      rw [hlift]; exact hz₀
    obtain ⟨V₁, V₂, n, a, c, b, d, h1, h2, hne, hall⟩ :=
      exists_localStructure_pullback 𝒢.G.hom (bO L L') e.inv.left U s (p₁ z₀) p₂ (hw z₀) hU
    let Hf : (Fin g → ℂ) → ℂ := fun z =>
      ∑ k, 𝒢.evalAt (bcPts e σ τ' hστ (Φ' z)) V₁ (c k) * evalPt p₂ V₂ (d k)
    let Nf : (Fin g → ℂ) → ℂ := fun z =>
      ∑ k, 𝒢.evalAt (bcPts e σ τ' hστ (Φ' z)) V₁ (a k) * evalPt p₂ V₂ (b k)
    let D1 := 𝒢.dom (fun z => bcPts e σ τ' hστ (Φ' z)) V₁
    have hHd : DifferentiableOn ℂ Hf D1 :=
      DifferentiableOn.fun_sum fun k _ => (hdiff V₁ (c k)).mul_const _
    have hNd : DifferentiableOn ℂ Nf D1 :=
      DifferentiableOn.fun_sum fun k _ => (hdiff V₁ (a k)).mul_const _
    let O := D1 ∩ Hf ⁻¹' {0}ᶜ
    have hO : IsOpen O := hHd.continuousOn.isOpen_inter_preimage (hopen V₁) isOpen_compl_singleton
    have hmem : ∀ z ∈ O, z ∈ 𝒢'.dom Φ' U ∧ 𝒢'.evalAt (Φ' z) U s * Hf z = Nf z := by
      rintro z ⟨hz1, hz2⟩
      have := hall (p₁ z) p₂ (hw z) hz1 h2 hz2
      refine ⟨?_, ?_⟩
      · show ⊤ ≤ (Φ' z).left ⁻¹ᵁ U
        exact (hlift z) ▸ this.1
      · show evalPt (Φ' z).left U s * Hf z = Nf z
        exact (hlift z) ▸ this.2
    refine ⟨O, hO, ⟨h1, hne⟩, fun z hz => (hmem z hz).1, ?_⟩
    have hq : ∀ z ∈ O, 𝒢'.evalAt (Φ' z) U s = Nf z * (Hf z)⁻¹ := by
      intro z hz
      rw [← div_eq_mul_inv, eq_div_iff hz.2]
      exact (hmem z hz).2
    exact ((hNd.mono Set.inter_subset_left).mul ((hHd.mono Set.inter_subset_left).inv
      (fun z hz => hz.2))).congr hq
  refine ⟨fun U => ?_, fun U s => ?_⟩
  · rw [isOpen_iff_forall_mem_open]
    intro z hz
    obtain ⟨O, hO, hzO, hOsub, -⟩ := hloc U 0 z hz
    exact ⟨O, hOsub, hO, hzO⟩
  · intro z hz
    obtain ⟨O, hO, hzO, -, hd⟩ := hloc U s z hz
    exact (hd.differentiableAt (hO.mem_nhds hzO)).differentiableWithinAt

/-- `UniformizationLift` is a theorem. -/
theorem uniformizationLift : UniformizationLift :=
  uniformizationLift_of uniformizationLiftAnalytic

end ZInQ.HeightBC




/-! # infra-stalks: height-bc's H4a and `HodgeLineBaseChange` from two glue statements -/

namespace ZInQ.HeightBC

/-- **H4a (`ModelHeightBaseChange`, verbatim) from `HodgeBCInjective` and `OmegaBaseChange`**:
`CotangentSpanBC` and `UniformizationLiftAnalytic` are now theorems. -/
theorem modelHeightBaseChange_of_two (h1 : HodgeBCInjective) (hω : OmegaBaseChange) :
    ModelHeightBaseChange :=
  modelHeightBaseChange_of_glue4 h1 cotangentSpanBC hω uniformizationLiftAnalytic

/-- **`HodgeLineBaseChange` (verbatim) from `HodgeBCInjective` and `OmegaBaseChange`.** -/
theorem hodgeLineBaseChange_of_two (h1 : HodgeBCInjective) (hω : OmegaBaseChange) :
    HodgeLineBaseChange :=
  hodgeLineBaseChange_of_glue4 h1 cotangentSpanBC hω uniformizationLiftAnalytic

end ZInQ.HeightBC

end G0A2_b07_infrastalks

section G0A2_b08_productunif
/-! ## leaf-fold2: product-unif §1-§3 (scratch/product-unif/WithProductHeight.lean lines 980-1577; see mk_b08.sh) -/
/-! ## §1. Elementary analysis (copied from `Analysis.lean`) -/

namespace ZInQ.ProductUnif

open Topology Filter MeasureTheory Metric

section Real

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The real core `{v | ℝ v ⊆ H}` of an additive subgroup. -/
def rcore (H : AddSubgroup E) : Submodule ℝ E where
  carrier := {v | ∀ t : ℝ, t • v ∈ H}
  add_mem' := by
    intro a b ha hb t
    rw [smul_add]
    exact H.add_mem (ha t) (hb t)
  zero_mem' := by
    intro t
    rw [smul_zero]
    exact H.zero_mem
  smul_mem' := by
    intro c a ha t
    rw [smul_smul]
    exact ha _

theorem mem_rcore {H : AddSubgroup E} {v : E} : v ∈ rcore H ↔ ∀ t : ℝ, t • v ∈ H := Iff.rfl

theorem rcore_le_self {H : AddSubgroup E} {v : E} (hv : v ∈ rcore H) : v ∈ H := by
  simpa using hv 1

variable [FiniteDimensional ℝ E]

/-- **Isolation in a complement of the real core.** -/
theorem exists_isolated (H : AddSubgroup E) (hH : IsClosed (H : Set E)) (W : Submodule ℝ E)
    (hW : rcore H ⊓ W = ⊥) : ∃ ε > 0, ∀ c ∈ H, c ∈ W → ‖c‖ < ε → c = 0 := by
  by_contra hne
  push Not at hne
  choose c hcH hcW hcn hc0 using fun n : ℕ => hne (1 / ((n : ℝ) + 1)) (by positivity)
  set u : ℕ → E := fun n => ‖c n‖⁻¹ • c n with hu_def
  have hu : ∀ n, u n ∈ sphere (0 : E) 1 := by
    intro n
    have : ‖c n‖ ≠ 0 := norm_ne_zero_iff.mpr (hc0 n)
    simp [u, norm_smul, this]
  obtain ⟨v, hv, φ, hφ, hlim⟩ := (isCompact_sphere (0 : E) 1).tendsto_subseq hu
  have hc_lim : Tendsto c atTop (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    exact squeeze_zero (fun n => norm_nonneg _) (fun n => (hcn n).le)
      tendsto_one_div_add_atTop_nhds_zero_nat
  have hc_lim' : Tendsto (fun n => c (φ n)) atTop (𝓝 0) := hc_lim.comp hφ.tendsto_atTop
  have hvW : v ∈ W :=
    (W.closed_of_finiteDimensional).mem_of_tendsto hlim
      (Eventually.of_forall fun n => W.smul_mem _ (hcW _))
  have hvR : v ∈ rcore H := by
    intro t
    have h1 : Tendsto (fun n => t • u (φ n)) atTop (𝓝 (t • v)) := hlim.const_smul t
    have h2 : Tendsto (fun n => (⌊t / ‖c (φ n)‖⌋ : ℤ) • c (φ n) - t • u (φ n)) atTop (𝓝 0) := by
      rw [tendsto_zero_iff_norm_tendsto_zero]
      refine squeeze_zero (fun n => norm_nonneg _) (fun n => ?_) (by simpa using hc_lim'.norm)
      have ha : ‖c (φ n)‖ ≠ 0 := norm_ne_zero_iff.mpr (hc0 _)
      have : (⌊t / ‖c (φ n)‖⌋ : ℤ) • c (φ n) - t • u (φ n) =
          (((⌊t / ‖c (φ n)‖⌋ : ℤ) : ℝ) - t / ‖c (φ n)‖) • c (φ n) := by
        rw [sub_smul, ← Int.cast_smul_eq_zsmul ℝ, hu_def]
        simp only
        rw [smul_smul, div_eq_mul_inv]
      rw [this, norm_smul, Real.norm_eq_abs]
      have hfl : |(((⌊t / ‖c (φ n)‖⌋ : ℤ) : ℝ) - t / ‖c (φ n)‖)| ≤ 1 := by
        rw [abs_le]
        constructor
        · linarith [Int.lt_floor_add_one (t / ‖c (φ n)‖)]
        · linarith [Int.floor_le (t / ‖c (φ n)‖)]
      calc |(((⌊t / ‖c (φ n)‖⌋ : ℤ) : ℝ) - t / ‖c (φ n)‖)| * ‖c (φ n)‖
          ≤ 1 * ‖c (φ n)‖ := mul_le_mul_of_nonneg_right hfl (norm_nonneg _)
        _ = ‖c (φ n)‖ := one_mul _
    have h3 := h1.add h2
    simp only [add_sub_cancel, add_zero] at h3
    exact hH.mem_of_tendsto h3 (Eventually.of_forall fun n => H.zsmul_mem (hcH _) _)
  have hv0 : v = 0 := by
    have : v ∈ rcore H ⊓ W := ⟨hvR, hvW⟩
    rw [hW] at this
    exact this
  simp [hv0] at hv

/-- **A closed subgroup is its real core plus a countable set.** -/
theorem exists_countable_add (H : AddSubgroup E) (hH : IsClosed (H : Set E)) :
    ∃ S : Set E, S.Countable ∧ ∀ h ∈ H, ∃ r ∈ rcore H, ∃ s ∈ S, h = r + s := by
  obtain ⟨W, hW⟩ := Submodule.exists_isCompl (rcore H)
  obtain ⟨ε, hε, hiso⟩ := exists_isolated H hH W hW.inf_eq_bot
  set S : Set E := {w | w ∈ H ∧ w ∈ W}
  have hsep : Pairwise fun x y : S => ε ≤ dist x y := by
    intro x y hxy
    by_contra hlt
    push Not at hlt
    apply hxy
    have h0 := hiso ((x : E) - y) (H.sub_mem x.2.1 y.2.1) (W.sub_mem x.2.2 y.2.2)
      (by rw [← dist_eq_norm]; exact hlt)
    exact Subtype.ext (sub_eq_zero.mp h0)
  have : DiscreteTopology S := DiscreteTopology.of_forall_le_dist hε hsep
  have : Countable S := TopologicalSpace.separableSpace_iff_countable.mp inferInstance
  refine ⟨S, Set.countable_coe_iff.mp inferInstance, fun h hh => ?_⟩
  have hmem : h ∈ rcore H ⊔ W := by rw [hW.sup_eq_top]; trivial
  obtain ⟨r, hr, w, hw, rfl⟩ := Submodule.mem_sup.mp hmem
  refine ⟨r, hr, w, ⟨?_, hw⟩, rfl⟩
  have : w = (r + w) - r := by abel
  rw [this]
  exact H.sub_mem hh (rcore_le_self hr)

variable [MeasurableSpace E] [BorelSpace E]

/-- **`H₁ + H₂ = E` forces `rcore H₁ ⊔ rcore H₂ = ⊤`** (a proper subspace is null). -/
theorem rcore_sup_eq_top (H₁ H₂ : AddSubgroup E) (h₁ : IsClosed (H₁ : Set E))
    (h₂ : IsClosed (H₂ : Set E)) (hs : ∀ x : E, ∃ a ∈ H₁, ∃ b ∈ H₂, a + b = x) :
    rcore H₁ ⊔ rcore H₂ = ⊤ := by
  by_contra hne
  obtain ⟨S₁, hS₁, hd₁⟩ := exists_countable_add H₁ h₁
  obtain ⟨S₂, hS₂, hd₂⟩ := exists_countable_add H₂ h₂
  set P := rcore H₁ ⊔ rcore H₂
  let μ : Measure E := Measure.addHaar
  have hP : μ (P : Set E) = 0 := Measure.addHaar_submodule μ P hne
  have : Countable S₁ := hS₁.to_subtype
  have : Countable S₂ := hS₂.to_subtype
  have hcov : (Set.univ : Set E) ⊆
      ⋃ p : S₁ × S₂, (fun x => -((p.1 : E) + p.2) + x) ⁻¹' (P : Set E) := by
    intro x _
    obtain ⟨a, ha, b, hb, rfl⟩ := hs x
    obtain ⟨r₁, hr₁, s₁, hs₁, rfl⟩ := hd₁ a ha
    obtain ⟨r₂, hr₂, s₂, hs₂, rfl⟩ := hd₂ b hb
    refine Set.mem_iUnion.mpr ⟨(⟨s₁, hs₁⟩, ⟨s₂, hs₂⟩), ?_⟩
    show -(s₁ + s₂) + (r₁ + s₁ + (r₂ + s₂)) ∈ P
    have : -(s₁ + s₂) + (r₁ + s₁ + (r₂ + s₂)) = r₁ + r₂ := by abel
    rw [this]
    exact P.add_mem (Submodule.mem_sup_left hr₁) (Submodule.mem_sup_right hr₂)
  have hnull : μ (⋃ p : S₁ × S₂, (fun x => -((p.1 : E) + p.2) + x) ⁻¹' (P : Set E)) = 0 := by
    refine measure_iUnion_null fun p => ?_
    rw [measure_preimage_add]
    exact hP
  have hu : μ Set.univ = 0 := measure_mono_null hcov hnull
  exact (Measure.measure_univ_ne_zero.mpr (NeZero.ne μ)) hu

end Real

section Closed

variable {E : Type*} [NormedAddCommGroup E]

/-- **A subgroup cut out near `0` by functions continuous there is closed.** -/
theorem isClosed_of_local (H : AddSubgroup E) (N : Set E) (hN : IsOpen N) (h0 : (0 : E) ∈ N)
    {ι : Type*} (F : ι → E → ℂ) (hF : ∀ i, ContinuousOn (F i) N)
    (hH : ∀ z ∈ N, z ∈ H ↔ ∀ i, F i z = F i 0) : IsClosed (H : Set E) := by
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp hN 0 h0
  set ρ := r / 2 with hρ
  have hρpos : 0 < ρ := by positivity
  have hcb : closedBall (0 : E) ρ ⊆ N :=
    (closedBall_subset_ball (by linarith)).trans hball
  have hC : IsClosed (closedBall (0 : E) ρ ∩ (H : Set E)) := by
    have : closedBall (0 : E) ρ ∩ (H : Set E) =
        closedBall (0 : E) ρ ∩ ⋂ i, (closedBall (0 : E) ρ ∩ F i ⁻¹' {F i 0}) := by
      ext z
      simp only [Set.mem_inter_iff, Set.mem_iInter, Set.mem_preimage, Set.mem_singleton_iff,
        SetLike.mem_coe]
      constructor
      · rintro ⟨hz, hzH⟩
        exact ⟨hz, fun i => ⟨hz, (hH z (hcb hz)).mp hzH i⟩⟩
      · rintro ⟨hz, hi⟩
        exact ⟨hz, (hH z (hcb hz)).mpr fun i => (hi i).2⟩
    rw [this]
    exact isClosed_closedBall.inter (isClosed_iInter fun i =>
      ((hF i).mono hcb).preimage_isClosed_of_isClosed isClosed_closedBall isClosed_singleton)
  rw [← closure_subset_iff_isClosed]
  intro x hx
  obtain ⟨h, hh, hxh⟩ := Metric.mem_closure_iff.mp hx ρ hρpos
  have hy : x - h ∈ closure (H : Set E) := by
    have hcl : x - h ∈ H.topologicalClosure :=
      H.topologicalClosure.sub_mem hx (H.le_topologicalClosure hh)
    exact hcl
  have hyb : x - h ∈ ball (0 : E) ρ := by
    rw [mem_ball, dist_zero_right, ← dist_eq_norm]
    exact hxh
  have hyC : x - h ∈ closedBall (0 : E) ρ ∩ (H : Set E) := by
    have := isOpen_ball.inter_closure ⟨hyb, hy⟩
    have hsub : closure (ball (0 : E) ρ ∩ (H : Set E)) ⊆ closedBall (0 : E) ρ ∩ (H : Set E) :=
      closure_minimal (Set.inter_subset_inter_left _ ball_subset_closedBall) hC
    exact hsub this
  have : x = (x - h) + h := by abel
  rw [this]
  exact H.add_mem hyC.2 hh

end Closed

section Complex

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- The complex core `{v | ℂ v ⊆ H}` of an additive subgroup. -/
def ccore (H : AddSubgroup E) : Submodule ℂ E where
  carrier := {v | ∀ t : ℂ, t • v ∈ H}
  add_mem' := by
    intro a b ha hb t
    rw [smul_add]
    exact H.add_mem (ha t) (hb t)
  zero_mem' := by
    intro t
    rw [smul_zero]
    exact H.zero_mem
  smul_mem' := by
    intro c a ha t
    rw [smul_smul]
    exact ha _

theorem mem_ccore {H : AddSubgroup E} {v : E} : v ∈ ccore H ↔ ∀ t : ℂ, t • v ∈ H := Iff.rfl

theorem ccore_le_self {H : AddSubgroup E} {v : E} (hv : v ∈ ccore H) : v ∈ H := by
  simpa using hv 1

/-- **Identity theorem step: the real core of a subgroup cut out near `0` by holomorphic
functions is complex.** -/
theorem rcore_le_ccore (H : AddSubgroup E) (N : Set E) (hN : IsOpen N) (h0 : (0 : E) ∈ N)
    {ι : Type*} (F : ι → E → ℂ) (hF : ∀ i, DifferentiableOn ℂ (F i) N)
    (hH : ∀ z ∈ N, z ∈ H ↔ ∀ i, F i z = F i 0) {w : E} (hw : w ∈ rcore H) : w ∈ ccore H := by
  have hcont : Continuous fun t : ℂ => t • w := continuous_id.smul continuous_const
  obtain ⟨δ, hδ, hball⟩ := Metric.isOpen_iff.mp (hN.preimage hcont) 0 (by simpa using h0)
  have hreal : ∀ r : ℝ, ((r : ℂ) • w) ∈ H := by
    intro r
    have := hw r
    rwa [← Complex.coe_smul] at this
  have hsmall : ∀ t ∈ ball (0 : ℂ) δ, t • w ∈ H := by
    intro t ht
    refine (hH _ (hball ht)).mpr fun i => ?_
    have hd : DifferentiableOn ℂ (fun t : ℂ => F i (t • w)) (ball (0 : ℂ) δ) :=
      (hF i).comp (differentiable_id.smul_const w).differentiableOn (fun s hs => hball hs)
    have han := hd.analyticOnNhd isOpen_ball
    have hconst : AnalyticOnNhd ℂ (fun _ : ℂ => F i 0) (ball (0 : ℂ) δ) :=
      analyticOnNhd_const
    have hfreq : ∃ᶠ s in 𝓝[≠] (0 : ℂ), F i (s • w) = F i 0 := by
      have htend : Tendsto (fun n : ℕ => ((1 / ((n : ℝ) + 1) : ℝ) : ℂ)) atTop (𝓝[≠] 0) := by
        refine tendsto_nhdsWithin_iff.mpr ⟨?_, Eventually.of_forall fun n => ?_⟩
        · have := (Complex.continuous_ofReal.tendsto 0).comp
            tendsto_one_div_add_atTop_nhds_zero_nat
          simpa [Function.comp_def] using this
        · simp only [Set.mem_compl_iff, Set.mem_singleton_iff, Complex.ofReal_eq_zero]
          positivity
      refine htend.frequently (Eventually.frequently ?_)
      have hev : ∀ᶠ n : ℕ in atTop, 1 / ((n : ℝ) + 1) < δ :=
        tendsto_one_div_add_atTop_nhds_zero_nat.eventually (gt_mem_nhds hδ)
      filter_upwards [hev] with n hn
      have hb : ((1 / ((n : ℝ) + 1) : ℝ) : ℂ) ∈ ball (0 : ℂ) δ := by
        rw [mem_ball, dist_zero_right, Complex.norm_real, Real.norm_eq_abs,
          abs_of_pos (by positivity)]
        exact hn
      exact (hH _ (hball hb)).mp (hreal _) i
    exact han.eqOn_of_preconnected_of_frequently_eq hconst (convex_ball 0 δ).isPreconnected
      (mem_ball_self hδ) hfreq ht
  intro t
  obtain ⟨n, hn⟩ := exists_nat_gt (‖t‖ / δ)
  have hnpos : (0 : ℝ) < n := lt_of_le_of_lt (by positivity) hn
  have hn0 : (n : ℂ) ≠ 0 := by exact_mod_cast hnpos.ne'
  have htn : t / n ∈ ball (0 : ℂ) δ := by
    rw [mem_ball, dist_zero_right, norm_div, Complex.norm_natCast]
    rw [div_lt_iff₀ hδ] at hn
    rw [div_lt_iff₀ hnpos]
    linarith
  have : t • w = n • ((t / n) • w) := by
    rw [← Nat.cast_smul_eq_nsmul ℂ, smul_smul, mul_div_cancel₀ _ hn0]
  rw [this]
  exact H.nsmul_mem (hsmall _ htn) n

/-- **The real core of a discrete subgroup is `0`.** -/
theorem eq_zero_of_mem_rcore_discrete (Λ : AddSubgroup E) [DiscreteTopology Λ] {v : E}
    (hv : v ∈ rcore Λ) : v = 0 := by
  let f : ℝ → Λ := fun t => ⟨t • v, hv t⟩
  have hf : Continuous f := (continuous_id.smul continuous_const).subtype_mk _
  have := PreconnectedSpace.constant inferInstance hf (x := 1) (y := 0)
  simpa [f] using congrArg Subtype.val this

end Complex

/-- **The real core of a discrete `ℤ`-lattice is `0`.** -/
theorem eq_zero_of_real_line_mem {g : ℕ} (Λ : Submodule ℤ (Fin g → ℂ)) [DiscreteTopology Λ]
    {v : Fin g → ℂ} (hv : ∀ t : ℝ, (t : ℂ) • v ∈ Λ) : v = 0 := by
  let f : ℝ → Λ := fun t => ⟨(t : ℂ) • v, hv t⟩
  have hf : Continuous f :=
    ((Complex.continuous_ofReal.smul continuous_const)).subtype_mk _
  have := PreconnectedSpace.constant inferInstance hf (x := 1) (y := 0)
  simpa [f] using congrArg Subtype.val this

/-- The kernel of a function with `f (z + w) = f z * f w`, as an additive subgroup. -/
def kerSub {G : Type*} [Group G] {E : Type*} [AddGroup E] (f : E → G)
    (hf : ∀ z w, f (z + w) = f z * f w) : AddSubgroup E where
  carrier := {z | f z = 1}
  add_mem' := by
    intro a b ha hb
    simp only [Set.mem_setOf_eq] at *
    rw [hf, ha, hb, mul_one]
  zero_mem' := by
    show f 0 = 1
    have h := hf 0 0
    rw [add_zero] at h
    exact mul_left_cancel (h.symm.trans (mul_one _).symm)
  neg_mem' := by
    intro a ha
    simp only [Set.mem_setOf_eq] at *
    have h0 : f 0 = 1 := by
      have h := hf 0 0
      rw [add_zero] at h
      exact mul_left_cancel (h.symm.trans (mul_one _).symm)
    have h := hf (-a) a
    rw [neg_add_cancel, ha, mul_one, h0] at h
    exact h.symm

theorem mem_kerSub {G : Type*} [Group G] {E : Type*} [AddGroup E] {f : E → G}
    {hf : ∀ z w, f (z + w) = f z * f w} {z : E} : z ∈ kerSub f hf ↔ f z = 1 := Iff.rfl

theorem hom_zero {G : Type*} [Group G] {E : Type*} [AddGroup E] (f : E → G)
    (hf : ∀ z w, f (z + w) = f z * f w) : f 0 = 1 :=
  (kerSub f hf).zero_mem

/-! ## §2. Points of an affine open are determined by the values of its regular functions -/

section Pts

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open NumberField DefFaltings

variable {K : Type} [Field K] {L : Type} [Field L] [NumberField L] [Algebra K L]

/-- **Two complex points lying in an affine open `V` with the same values on `Γ(V)` are equal**
(proved: both factor as `Spec ℂ ≅ Spec Γ(Spec ℂ) → Spec Γ(V) → 𝒢`, by
`IsAffineOpen.SpecMap_appLE_fromSpec`). -/
theorem pts_eq_of_evalAt {A : AbVar K} (𝒢 : GroupModel A L) {τ : L →+* ℂ} {p q : 𝒢.Pts τ}
    {V : 𝒢.G.left.Opens} (hV : IsAffineOpen V) (hp : ⊤ ≤ p.left ⁻¹ᵁ V)
    (hq : ⊤ ≤ q.left ⁻¹ᵁ V) (h : ∀ s, 𝒢.evalAt p V s = 𝒢.evalAt q V s) : p = q := by
  let pl : Spec (CommRingCat.of ℂ) ⟶ 𝒢.G.left := p.left
  let ql : Spec (CommRingCat.of ℂ) ⟶ 𝒢.G.left := q.left
  have hp2 : ⊤ ≤ pl ⁻¹ᵁ V := hp
  have hq2 : ⊤ ≤ ql ⁻¹ᵁ V := hq
  have heq : pl.appLE V ⊤ hp2 = ql.appLE V ⊤ hq2 := by
    ext s
    have hs := h s
    unfold GroupModel.evalAt at hs
    rw [dif_pos hp, dif_pos hq] at hs
    exact (Scheme.ΓSpecIso (CommRingCat.of ℂ)).commRingCatIsoToRingEquiv.injective hs
  have hp' := IsAffineOpen.SpecMap_appLE_fromSpec pl hV
    (isAffineOpen_top (Spec (CommRingCat.of ℂ))) hp2
  have hq' := IsAffineOpen.SpecMap_appLE_fromSpec ql hV
    (isAffineOpen_top (Spec (CommRingCat.of ℂ))) hq2
  have hT : IsIso (isAffineOpen_top (Spec (CommRingCat.of ℂ))).fromSpec := by
    rw [IsAffineOpen.fromSpec_top]
    infer_instance
  have : (isAffineOpen_top (Spec (CommRingCat.of ℂ))).fromSpec ≫ pl =
      (isAffineOpen_top (Spec (CommRingCat.of ℂ))).fromSpec ≫ ql := by
    rw [← hp', ← hq', heq]
  exact Over.OverMorphism.ext
    ((IsIso.epi_of_iso (isAffineOpen_top (Spec (CommRingCat.of ℂ))).fromSpec).left_cancellation
      pl ql this)

/-- `Spec ℂ` has one point. -/
theorem top_le_preimage_of_mem {A : AbVar K} (𝒢 : GroupModel A L) {τ : L →+* ℂ} (p : 𝒢.Pts τ)
    {V : 𝒢.G.left.Opens} (x₀ : (GroupModel.ptC (L := L) τ).left) (h : p.left x₀ ∈ V) :
    ⊤ ≤ p.left ⁻¹ᵁ V := by
  intro x _
  have : x = x₀ := Subsingleton.elim (α := PrimeSpectrum ℂ) x x₀
  subst this
  exact h

/-- **The kernel of a holomorphic homomorphism into the complex points of a group model** is
closed, and its real core is complex (proved, from §1 and §2: near `0` it is cut out by the
regular functions of an affine open around the unit). -/
theorem kerSub_facts {A : AbVar K} (𝒢 : GroupModel A L) {τ : L →+* ℂ} {g : ℕ}
    (ψ : (Fin g → ℂ) → 𝒢.Pts τ) (hm : ∀ z w, ψ (z + w) = ψ z * ψ w)
    (ho : ∀ U, IsOpen (𝒢.dom ψ U))
    (hd : ∀ U (s : Γ(𝒢.G.left, U)),
      DifferentiableOn ℂ (fun z => 𝒢.evalAt (ψ z) U s) (𝒢.dom ψ U)) :
    IsClosed (kerSub ψ hm : Set (Fin g → ℂ)) ∧
      ∀ w ∈ rcore (kerSub ψ hm), w ∈ ccore (kerSub ψ hm) := by
  have h0 : ψ 0 = 1 := hom_zero ψ hm
  let x₀ : (GroupModel.ptC (L := L) τ).left := (default : PrimeSpectrum ℂ)
  obtain ⟨V, hV, hxV, -⟩ :=
    exists_isAffineOpen_mem_and_subset (x := (ψ 0).left x₀) (U := ⊤) trivial
  have hN0 : (0 : Fin g → ℂ) ∈ 𝒢.dom ψ V := top_le_preimage_of_mem 𝒢 (ψ 0) x₀ hxV
  have hH : ∀ z ∈ 𝒢.dom ψ V, z ∈ kerSub ψ hm ↔
      ∀ s : Γ(𝒢.G.left, V), 𝒢.evalAt (ψ z) V s = 𝒢.evalAt (ψ 0) V s := by
    intro z hz
    constructor
    · intro hk s
      rw [show ψ z = ψ 0 from (mem_kerSub.mp hk).trans h0.symm]
    · intro hs
      show ψ z = 1
      rw [← h0]
      exact pts_eq_of_evalAt 𝒢 hV hz hN0 hs
  exact ⟨isClosed_of_local _ _ (ho V) hN0 (fun s z => 𝒢.evalAt (ψ z) V s)
      (fun s => (hd V s).continuousOn) hH,
    fun w hw => rcore_le_ccore _ _ (ho V) hN0 (fun s z => 𝒢.evalAt (ψ z) V s)
      (fun s => hd V s) hH hw⟩

end Pts

/-! ## §3. `ProductUnifSplits` (proved) -/

section Splits

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open NumberField DefFaltings ZInQ.ProductHeight

/-- `ℂ^{g₁+g₂} ≅ ℂ^{g₁} × ℂ^{g₂}` (`ℂ`-linear), `z ↦ (z ∘ castAdd, z ∘ natAdd)`. -/
def splitCE (g₁ g₂ : ℕ) : (Fin (g₁ + g₂) → ℂ) ≃ₗ[ℂ] (Fin g₁ → ℂ) × (Fin g₂ → ℂ) where
  toFun z := (fun i => z (Fin.castAdd g₂ i), fun i => z (Fin.natAdd g₁ i))
  invFun p := Fin.append p.1 p.2
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv _ := Fin.append_castAdd_natAdd
  right_inv p := by ext i <;> simp

/-- **Glue S-an, proved.** -/
theorem productUnifSplits : ProductUnifSplits := by
  intro K _ A B C L _ _ _ 𝒢P 𝒢₁ 𝒢₂ e _ _ τ g Λ _ Φ hZ hΦ
  have ⟨hm, hk, hs, ho, hd⟩ := hΦ
  -- the two components of `Φ`
  let ψ₁ : (Fin g → ℂ) → 𝒢₁.Pts τ := fun z => (ptsEquiv e τ (Φ z)).1
  let ψ₂ : (Fin g → ℂ) → 𝒢₂.Pts τ := fun z => (ptsEquiv e τ (Φ z)).2
  have hψm₁ : ∀ z w, ψ₁ (z + w) = ψ₁ z * ψ₁ w := by
    intro z w
    simp only [ψ₁, hm, map_mul, Prod.fst_mul]
  have hψm₂ : ∀ z w, ψ₂ (z + w) = ψ₂ z * ψ₂ w := by
    intro z w
    simp only [ψ₂, hm, map_mul, Prod.snd_mul]
  have hc₁ := proj_analyticClauses e hΦ (LinearMap.id : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ))
  have hc₂ := analyticClauses_comp 𝒢P 𝒢₂ (e.hom ≫ snd _ _) ho hd
  obtain ⟨hK₁c, hK₁r⟩ := kerSub_facts 𝒢₁ ψ₁ hψm₁ hc₁.1 hc₁.2
  obtain ⟨hK₂c, hK₂r⟩ := kerSub_facts 𝒢₂ ψ₂ hψm₂ hc₂.1 hc₂.2
  set K₁ := kerSub ψ₁ hψm₁ with hK₁
  set K₂ := kerSub ψ₂ hψm₂ with hK₂
  have hΛ : ∀ z, z ∈ Λ ↔ ψ₁ z = 1 ∧ ψ₂ z = 1 := by
    intro z
    rw [← hk]
    constructor
    · intro h
      simp [ψ₁, ψ₂, h]
    · rintro ⟨h1, h2⟩
      apply (ptsEquiv e τ).injective
      rw [map_one]
      exact Prod.ext h1 h2
  -- `K₁ + K₂ = ℂ^g`
  have hsum : ∀ x, ∃ a ∈ K₁, ∃ b ∈ K₂, a + b = x := by
    intro x
    obtain ⟨a, ha⟩ := hs ((ptsEquiv e τ).symm (1, ψ₂ x))
    have ha1 : ψ₁ a = 1 := by simp [ψ₁, ha]
    have ha2 : ψ₂ a = ψ₂ x := by simp [ψ₂, ha]
    refine ⟨a, ha1, x - a, ?_, by abel⟩
    show ψ₂ (x - a) = 1
    have := hψm₂ (x - a) a
    rw [sub_add_cancel, ha2] at this
    exact mul_right_cancel (this.symm.trans (_root_.one_mul _).symm)
  have hR : rcore K₁ ⊔ rcore K₂ = ⊤ := rcore_sup_eq_top K₁ K₂ hK₁c hK₂c hsum
  -- the complex subspaces `V₁ = ccore K₂`, `V₂ = ccore K₁`
  set V₁ := ccore K₂ with hV₁
  set V₂ := ccore K₁ with hV₂
  have hcompl : IsCompl V₁ V₂ := by
    constructor
    · rw [Submodule.disjoint_def]
      intro v hv1 hv2
      refine eq_zero_of_real_line_mem Λ fun t => ?_
      exact (hΛ _).mpr ⟨hv2 (t : ℂ), hv1 (t : ℂ)⟩
    · rw [codisjoint_iff, eq_top_iff]
      intro x _
      have hx : x ∈ rcore K₁ ⊔ rcore K₂ := by rw [hR]; trivial
      obtain ⟨r₁, hr₁, r₂, hr₂, rfl⟩ := Submodule.mem_sup.mp hx
      rw [add_comm]
      exact Submodule.add_mem_sup (hK₂r r₂ hr₂) (hK₁r r₁ hr₁)
  -- dimensions and coordinates
  set g₁ := Module.finrank ℂ V₁ with hg₁
  set g₂ := Module.finrank ℂ V₂ with hg₂
  have hg : g₁ + g₂ = g := by
    rw [hg₁, hg₂, Submodule.finrank_add_eq_of_isCompl hcompl, Module.finrank_fin_fun]
  let b₁ : V₁ ≃ₗ[ℂ] (Fin g₁ → ℂ) := (Module.finBasis ℂ V₁).equivFun
  let b₂ : V₂ ≃ₗ[ℂ] (Fin g₂ → ℂ) := (Module.finBasis ℂ V₂).equivFun
  let ι₁ : (Fin g₁ → ℂ) →ₗ[ℂ] (Fin g → ℂ) := V₁.subtype ∘ₗ b₁.symm.toLinearMap
  let ι₂ : (Fin g₂ → ℂ) →ₗ[ℂ] (Fin g → ℂ) := V₂.subtype ∘ₗ b₂.symm.toLinearMap
  let cE := Submodule.prodEquivOfIsCompl V₁ V₂ hcompl
  let π₁ : (Fin g → ℂ) →ₗ[ℂ] (Fin g₁ → ℂ) :=
    b₁.toLinearMap ∘ₗ LinearMap.fst ℂ V₁ V₂ ∘ₗ cE.symm.toLinearMap
  let π₂ : (Fin g → ℂ) →ₗ[ℂ] (Fin g₂ → ℂ) :=
    b₂.toLinearMap ∘ₗ LinearMap.snd ℂ V₁ V₂ ∘ₗ cE.symm.toLinearMap
  have key₁ : ∀ z, ψ₂ (ι₁ z) = 1 := fun z => ccore_le_self (b₁.symm z).2
  have key₂ : ∀ z, ψ₁ (ι₂ z) = 1 := fun z => ccore_le_self (b₂.symm z).2
  have dec : ∀ y, y = ι₁ (π₁ y) + ι₂ (π₂ y) := by
    intro y
    have h1 := Submodule.coe_prodEquivOfIsCompl' V₁ V₂ hcompl (cE.symm y)
    have h2 : cE (cE.symm y) = y := cE.apply_symm_apply y
    calc y = cE (cE.symm y) := h2.symm
      _ = ↑(cE.symm y).1 + ↑(cE.symm y).2 := h1
      _ = ι₁ (π₁ y) + ι₂ (π₂ y) := by simp [ι₁, ι₂, π₁, π₂]
  have hπ₁ : ∀ x, π₁ (ι₁ x) = x := by
    intro x
    simp [π₁, ι₁, cE]
  have hπ₂ : ∀ x, π₂ (ι₂ x) = x := by
    intro x
    simp [π₂, ι₂, cE]
  -- the factor uniformizations and lattices
  let Φ₁ : (Fin g₁ → ℂ) → 𝒢₁.Pts τ := fun z => ψ₁ (ι₁ z)
  let Φ₂ : (Fin g₂ → ℂ) → 𝒢₂.Pts τ := fun z => ψ₂ (ι₂ z)
  let Λ₁ : Submodule ℤ (Fin g₁ → ℂ) := ZLattice.comap ℝ Λ (ι₁.restrictScalars ℝ)
  let Λ₂ : Submodule ℤ (Fin g₂ → ℂ) := ZLattice.comap ℝ Λ (ι₂.restrictScalars ℝ)
  have hΛ₁ : ∀ z, z ∈ Λ₁ ↔ ι₁ z ∈ Λ := fun z => Iff.rfl
  have hΛ₂ : ∀ z, z ∈ Λ₂ ↔ ι₂ z ∈ Λ := fun z => Iff.rfl
  have hπΛ₁ : ∀ l ∈ Λ, π₁ l ∈ Λ₁ := by
    intro l hl
    rw [hΛ₁, hΛ]
    refine ⟨?_, key₁ _⟩
    have h1 : ψ₁ (ι₁ (π₁ l) + ι₂ (π₂ l)) = 1 := by rw [← dec l]; exact ((hΛ l).mp hl).1
    rwa [hψm₁, key₂, _root_.mul_one] at h1
  have hπΛ₂ : ∀ l ∈ Λ, π₂ l ∈ Λ₂ := by
    intro l hl
    rw [hΛ₂, hΛ]
    refine ⟨key₂ _, ?_⟩
    have h1 : ψ₂ (ι₁ (π₁ l) + ι₂ (π₂ l)) = 1 := by rw [← dec l]; exact ((hΛ l).mp hl).2
    rwa [hψm₂, key₁, _root_.one_mul] at h1
  have hdisc₁ : DiscreteTopology Λ₁ :=
    ZLattice.comap_discreteTopology ℝ Λ (LinearMap.continuous_of_finiteDimensional _)
      (Subtype.val_injective.comp b₁.symm.injective)
  have hdisc₂ : DiscreteTopology Λ₂ :=
    ZLattice.comap_discreteTopology ℝ Λ (LinearMap.continuous_of_finiteDimensional _)
      (Subtype.val_injective.comp b₂.symm.injective)
  have hspan : Submodule.span ℝ (Λ : Set (Fin g → ℂ)) = ⊤ := IsZLattice.span_top
  have hfull₁ : IsZLattice ℝ Λ₁ := by
    refine ⟨eq_top_iff.mpr fun x _ => ?_⟩
    have hy : ι₁ x ∈ Submodule.span ℝ (Λ : Set (Fin g → ℂ)) := by rw [hspan]; trivial
    have hmap : Submodule.map (π₁.restrictScalars ℝ) (Submodule.span ℝ (Λ : Set (Fin g → ℂ))) ≤
        Submodule.span ℝ (Λ₁ : Set (Fin g₁ → ℂ)) := by
      rw [Submodule.map_span]
      apply Submodule.span_mono
      rintro _ ⟨l, hl, rfl⟩
      exact hπΛ₁ l hl
    rw [← hπ₁ x]
    exact hmap ⟨ι₁ x, hy, rfl⟩
  have hfull₂ : IsZLattice ℝ Λ₂ := by
    refine ⟨eq_top_iff.mpr fun x _ => ?_⟩
    have hy : ι₂ x ∈ Submodule.span ℝ (Λ : Set (Fin g → ℂ)) := by rw [hspan]; trivial
    have hmap : Submodule.map (π₂.restrictScalars ℝ) (Submodule.span ℝ (Λ : Set (Fin g → ℂ))) ≤
        Submodule.span ℝ (Λ₂ : Set (Fin g₂ → ℂ)) := by
      rw [Submodule.map_span]
      apply Submodule.span_mono
      rintro _ ⟨l, hl, rfl⟩
      exact hπΛ₂ l hl
    rw [← hπ₂ x]
    exact hmap ⟨ι₂ x, hy, rfl⟩
  have hu₁ : 𝒢₁.IsAnalyticUniformization τ Λ₁ Φ₁ := by
    have hcl := proj_analyticClauses e hΦ ι₁
    refine ⟨fun z w => ?_, fun z => ?_, fun a => ?_, hcl.1, hcl.2⟩
    · show ψ₁ (ι₁ (z + w)) = ψ₁ (ι₁ z) * ψ₁ (ι₁ w)
      rw [map_add, hψm₁]
    · rw [hΛ₁, hΛ]
      exact ⟨fun h => ⟨h, key₁ z⟩, fun h => h.1⟩
    · obtain ⟨y, hy⟩ := hs ((ptsEquiv e τ).symm (a, 1))
      have h1 : ψ₁ y = a := by simp [ψ₁, hy]
      refine ⟨π₁ y, ?_⟩
      show ψ₁ (ι₁ (π₁ y)) = a
      rw [dec y, hψm₁, key₂, _root_.mul_one] at h1
      exact h1
  have hu₂ : 𝒢₂.IsAnalyticUniformization τ Λ₂ Φ₂ := by
    have hcl := analyticClauses_comp 𝒢P 𝒢₂ (e.hom ≫ snd _ _)
      (analyticClauses_precomp 𝒢P ι₂ ho hd).1 (analyticClauses_precomp 𝒢P ι₂ ho hd).2
    refine ⟨fun z w => ?_, fun z => ?_, fun b => ?_, hcl.1, hcl.2⟩
    · show ψ₂ (ι₂ (z + w)) = ψ₂ (ι₂ z) * ψ₂ (ι₂ w)
      rw [map_add, hψm₂]
    · rw [hΛ₂, hΛ]
      exact ⟨fun h => ⟨key₂ z, h⟩, fun h => h.2⟩
    · obtain ⟨y, hy⟩ := hs ((ptsEquiv e τ).symm (1, b))
      have h1 : ψ₂ y = b := by simp [ψ₂, hy]
      refine ⟨π₂ y, ?_⟩
      show ψ₂ (ι₂ (π₂ y)) = b
      rw [dec y, hψm₂, key₁, _root_.one_mul] at h1
      exact h1
  -- the linear change of coordinates
  let T : (Fin g → ℂ) ≃ₗ[ℂ] (Fin g → ℂ) :=
    LinearEquiv.funCongrLeft ℂ ℂ (finCongr hg) ≪≫ₗ splitCE g₁ g₂ ≪≫ₗ
      (b₁.symm.prodCongr b₂.symm) ≪≫ₗ cE
  have hT : ∀ z, T z = ι₁ (fun i => z (Fin.cast hg (Fin.castAdd g₂ i))) +
      ι₂ (fun i => z (Fin.cast hg (Fin.natAdd g₁ i))) := by
    intro z
    show cE _ = _
    rw [Submodule.coe_prodEquivOfIsCompl']
    rfl
  refine ⟨g₁, g₂, hg, Λ₁, Λ₂, Φ₁, Φ₂, T, ⟨hdisc₁, hfull₁⟩, ⟨hdisc₂, hfull₂⟩, hu₁, hu₂,
    fun z => ?_⟩
  rw [hT z]
  unfold prodUnif
  rw [MulEquiv.eq_symm_apply]
  apply Prod.ext
  · show ψ₁ (ι₁ _ + ι₂ _) = Φ₁ _
    rw [hψm₁, key₂, _root_.mul_one]
  · show ψ₂ (ι₁ _ + ι₂ _) = Φ₂ _
    rw [hψm₂, key₁, _root_.one_mul]

end Splits

end ZInQ.ProductUnif

end G0A2_b08_productunif

section G0A2_b09_unifdims
/-! ## leaf-fold2: unif-dims and product-unif §3b-§5 over this file's objects (see mk_unifdims.py) -/


/-! ## §3b. metrization's `JacDetDescends`, `productJacobian`, `productUniformizationAnalytic_of`, on the kernel's types

Verbatim copies (only `open PkgI3 (AbVar)` added after each `open … DefFaltings …` line, and
`#print` lines dropped) from `scratch/metrization/`: `part_exists.lean` lines 30-43 (the Prop
`ZInQ.Metrization.JacDetDescends`), `part_jacdet.lean` lines 1-138, `part_jacgerm.lean`,
`part_jacscalar.lean`, `part_jacclass.lean` lines 1-139. There they are stated over the
def-faltings copy in `scratch/metrization/Base.lean`; here over the kernel's `DefFaltings`
(`ZInQKernel/HDecomp/Faltings/Models.lean`, adopted from def-faltings). -/

namespace ZInQ.Metrization

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open NumberField DefFaltings

/-- **Glue (the Jacobian descends to the Hodge line).** For an analytic uniformization `Φ` of
`𝒢(ℂ)_τ`, the Jacobian determinant `jacDet Φ f = det(∂(f_i ∘ Φ)/∂z_j(0))` depends only on the
classes `df_i ∈ 𝔪_ξ/𝔪_ξ²`, is `𝓞_L`-multilinear (through `τ`) and alternating in them, hence is
the value on `1 ⊗ df₁ ∧ ⋯ ∧ df_g` of a `τ`-semilinear map `hodgeSpace g → ℂ`. Why true: `Φ 0 = 1`
lies over `ξ`; the germ `f ∘ Φ` at `0` is independent of the representative of `f` (`dom Φ U`
open); evaluation at a complex point is a ring map, so `(f f') ∘ Φ = (f ∘ Φ)(f' ∘ Φ)` near `0`,
and for `f, f' ∈ 𝔪_ξ` both vanish at `0`, so `d((ff') ∘ Φ)(0) = 0` (Leibniz); a function from
`𝓞_L` acts by the constant `τ(a)`. Then `⋀^g` (universal property) and `L ⊗_{𝓞_L} -` (extension
of scalars along `τ`) give the map. Elementary calculus plus Mathlib's scheme API; unproved. -/
def JacDetDescends : Prop :=
  ∀ (K : Type) [Field K] (A : AbVar K) (L : Type) [Field L] [NumberField L] [Algebra K L]
    (𝒢 : GroupModel A L) (τ : L →+* ℂ) (g : ℕ) (Λ : Submodule ℤ (Fin g → ℂ))
    (Φ : (Fin g → ℂ) → 𝒢.Pts τ), 𝒢.IsAnalyticUniformization τ Λ Φ →
    ∃ c : 𝒢.hodgeSpace g →ₛₗ[τ] ℂ, ∀ f, c (𝒢.wedge f) = 𝒢.jacDet Φ f

end ZInQ.Metrization


/-! ## metrization: `JacDetDescends` reduced to four calculus properties of `jacDet`

The algebra (universal property of `⋀^g`, extension of scalars `L ⊗_{𝓞_L} -` along `τ`) is
proved; what remains (`JacDetMultilinear`) are four statements about the derivative at `0` of
germs composed with `Φ`. -/

namespace ZInQ.Metrization

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open NumberField DefFaltings

/-- **Glue (calculus of `jacDet`).** For an analytic uniformization `Φ` of `𝒢(ℂ)_τ`, the map
`f ↦ jacDet Φ f = det(∂(f_i ∘ Φ)/∂z_j(0))` on `g`-tuples of germs in `𝔪_ξ`
(i) depends only on the classes `df_i ∈ 𝔪_ξ/𝔪_ξ²`;
(ii) is additive in each slot;
(iii) scales by `τ(a)` when slot `i` is multiplied by the image of `a ∈ 𝓞_L`;
(iv) vanishes when two slots are equal.
Why true: `Φ 0 = 1` lies over `ξ`, and `dom Φ U` is open, so the germ at `0` of `f ∘ Φ` does not
depend on the representative of `f`, and `(f + f') ∘ Φ = f ∘ Φ + f' ∘ Φ`, `(ff') ∘ Φ = (f ∘ Φ)(f' ∘ Φ)`
and `a ∘ Φ = τ(a)` near `0` (evaluation at a complex point is a ring map); for `f, f' ∈ 𝔪_ξ`,
`f ∘ Φ` and `f' ∘ Φ` vanish at `0`, so `d((ff') ∘ Φ)(0) = 0` (Leibniz), which gives (i); (ii)-(iv)
are row operations on the determinant. Elementary, unproved (needs the compatibility of
`evalAt` with restriction, sums, products and stalks in Mathlib's scheme API). -/
def JacDetMultilinear : Prop :=
  ∀ (K : Type) [Field K] (A : AbVar K) (L : Type) [Field L] [NumberField L] [Algebra K L]
    (𝒢 : GroupModel A L) (τ : L →+* ℂ) (g : ℕ) (Λ : Submodule ℤ (Fin g → ℂ))
    (Φ : (Fin g → ℂ) → 𝒢.Pts τ), 𝒢.IsAnalyticUniformization τ Λ Φ →
    (∀ f f' : Fin g → IsLocalRing.maximalIdeal 𝒢.genStalk,
      (∀ i, 𝒢.dCls (f i) = 𝒢.dCls (f' i)) → 𝒢.jacDet Φ f = 𝒢.jacDet Φ f') ∧
    (∀ (f : Fin g → IsLocalRing.maximalIdeal 𝒢.genStalk) (i : Fin g)
      (x y : IsLocalRing.maximalIdeal 𝒢.genStalk),
      𝒢.jacDet Φ (Function.update f i (x + y)) =
        𝒢.jacDet Φ (Function.update f i x) + 𝒢.jacDet Φ (Function.update f i y)) ∧
    (∀ (f : Fin g → IsLocalRing.maximalIdeal 𝒢.genStalk) (i : Fin g) (a : 𝓞 L)
      (x : IsLocalRing.maximalIdeal 𝒢.genStalk),
      𝒢.jacDet Φ (Function.update f i (𝒢.structMap a • x)) =
        τ (algebraMap (𝓞 L) L a) * 𝒢.jacDet Φ (Function.update f i x)) ∧
    (∀ (f : Fin g → IsLocalRing.maximalIdeal 𝒢.genStalk) (i j : Fin g), f i = f j → i ≠ j →
      𝒢.jacDet Φ f = 0)

/-- **`JacDetDescends` from `JacDetMultilinear` (proved).** -/
theorem jacDetDescends_of (h : JacDetMultilinear) : JacDetDescends := by
  intro K _ A L _ _ _ 𝒢 τ g Λ Φ hΦ
  obtain ⟨hcls, hadd, hsmul, halt⟩ := h K A L 𝒢 τ g Λ Φ hΦ
  classical
  letI : Module (𝓞 L) ℂ := Module.compHom ℂ (τ.comp (algebraMap (𝓞 L) L))
  have hsm : ∀ (a : 𝓞 L) (z : ℂ), a • z = τ (algebraMap (𝓞 L) L a) * z := fun _ _ => rfl
  let lift : 𝒢.cotangent → IsLocalRing.maximalIdeal 𝒢.genStalk :=
    Function.surjInv (IsLocalRing.maximalIdeal 𝒢.genStalk).toCotangent_surjective
  have hlift : ∀ v, 𝒢.dCls (lift v) = v := fun v =>
    Function.surjInv_eq (IsLocalRing.maximalIdeal 𝒢.genStalk).toCotangent_surjective v
  have hdadd : ∀ x y, 𝒢.dCls (x + y) = 𝒢.dCls x + 𝒢.dCls y := fun x y =>
    map_add (IsLocalRing.maximalIdeal 𝒢.genStalk).toCotangent x y
  have hdsmul : ∀ (a : 𝓞 L) x, 𝒢.dCls (𝒢.structMap a • x) = a • 𝒢.dCls x := fun a x =>
    map_smul (IsLocalRing.maximalIdeal 𝒢.genStalk).toCotangent (𝒢.structMap a) x
  let ψ : 𝒢.cotangent [⋀^Fin g]→ₗ[𝓞 L] ℂ :=
    { toFun := fun v => 𝒢.jacDet Φ (fun i => lift (v i))
      map_update_add' := by
        intro _ v i x y
        have e0 : 𝒢.jacDet Φ (fun j => lift (Function.update v i (x + y) j)) =
            𝒢.jacDet Φ (Function.update (fun j => lift (v j)) i (lift x + lift y)) := by
          apply hcls
          intro j
          by_cases hj : j = i
          · subst hj; simp [hlift, hdadd]
          · simp [Function.update_apply, hj]
        have e1 : 𝒢.jacDet Φ (fun j => lift (Function.update v i x j)) =
            𝒢.jacDet Φ (Function.update (fun j => lift (v j)) i (lift x)) := by
          apply hcls
          intro j
          by_cases hj : j = i
          · subst hj; simp
          · simp [Function.update_apply, hj]
        have e2 : 𝒢.jacDet Φ (fun j => lift (Function.update v i y j)) =
            𝒢.jacDet Φ (Function.update (fun j => lift (v j)) i (lift y)) := by
          apply hcls
          intro j
          by_cases hj : j = i
          · subst hj; simp
          · simp [Function.update_apply, hj]
        show 𝒢.jacDet Φ (fun j => lift (Function.update v i (x + y) j)) =
          𝒢.jacDet Φ (fun j => lift (Function.update v i x j)) +
            𝒢.jacDet Φ (fun j => lift (Function.update v i y j))
        rw [e0, e1, e2]
        convert hadd (fun j => lift (v j)) i (lift x) (lift y)
      map_update_smul' := by
        intro _ v i a x
        have e0 : 𝒢.jacDet Φ (fun j => lift (Function.update v i (a • x) j)) =
            𝒢.jacDet Φ (Function.update (fun j => lift (v j)) i (𝒢.structMap a • lift x)) := by
          apply hcls
          intro j
          by_cases hj : j = i
          · subst hj; simp [hlift, hdsmul]
          · simp [Function.update_apply, hj]
        have e1 : 𝒢.jacDet Φ (fun j => lift (Function.update v i x j)) =
            𝒢.jacDet Φ (Function.update (fun j => lift (v j)) i (lift x)) := by
          apply hcls
          intro j
          by_cases hj : j = i
          · subst hj; simp
          · simp [Function.update_apply, hj]
        show 𝒢.jacDet Φ (fun j => lift (Function.update v i (a • x) j)) =
          a • 𝒢.jacDet Φ (fun j => lift (Function.update v i x j))
        rw [e0, e1, hsm]
        convert hsmul (fun j => lift (v j)) i a (lift x)
      map_eq_zero_of_eq' := by
        intro v i j hv hij
        exact halt (fun k => lift (v k)) i j (by simp only [hv]) hij }
  let Ψ : ⋀[𝓞 L]^g 𝒢.cotangent →ₗ[𝓞 L] ℂ := exteriorPower.alternatingMapLinearEquiv ψ
  let B : L →ₗ[𝓞 L] ⋀[𝓞 L]^g 𝒢.cotangent →ₗ[𝓞 L] ℂ :=
    LinearMap.mk₂ (𝓞 L) (fun x w => τ x * Ψ w)
      (fun x y w => by rw [map_add, add_mul])
      (fun a x w => by
        rw [hsm, Algebra.smul_def, map_mul, _root_.mul_assoc])
      (fun x w w' => by rw [map_add, mul_add])
      (fun a x w => by
        rw [map_smul, hsm, hsm, mul_left_comm])
  let T : 𝒢.hodgeSpace g →ₗ[𝓞 L] ℂ := TensorProduct.lift B
  have hT : ∀ x w, T (x ⊗ₜ[𝓞 L] w) = τ x * Ψ w := fun x w => rfl
  let c : 𝒢.hodgeSpace g →ₛₗ[τ] ℂ :=
    { toFun := T
      map_add' := T.map_add
      map_smul' := by
        intro y t
        induction t using TensorProduct.induction_on with
        | zero => simp
        | tmul x w =>
          rw [TensorProduct.smul_tmul', hT, hT, smul_eq_mul, map_mul, _root_.mul_assoc]
          rfl
        | add t t' ht ht' => rw [smul_add, map_add, ht, ht', map_add, smul_eq_mul, smul_eq_mul,
            smul_eq_mul, mul_add] }
  refine ⟨c, fun f => ?_⟩
  show T ((1 : L) ⊗ₜ[𝓞 L] exteriorPower.ιMulti (𝓞 L) g (fun i => 𝒢.dCls (f i))) = 𝒢.jacDet Φ f
  rw [hT, map_one, _root_.one_mul, exteriorPower.alternatingMapLinearEquiv_apply_ιMulti]
  exact hcls _ _ fun i => hlift _

end ZInQ.Metrization


/-! ## metrization: two of the four clauses of `JacDetMultilinear`, proved

`Φ 0 = 1` lies over `ξ` (`zero_mem_dom`); `germAlong Φ t` agrees near `0` with `z ↦ evalAt (Φ z) U s`
for every representative `(U, s)` of `t` (`germAlong_eventuallyEq`); hence slot additivity
(`jacDet_update_add`). Vanishing on equal slots is immediate (`jacDet_eq_zero_of_eq`). What
remains is `JacDetClassScalar` (clauses (i) and (iii)). -/

namespace ZInQ.Metrization

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open NumberField DefFaltings Topology

section Germ

variable {K : Type} [Field K] {A : AbVar K} {L : Type} [Field L] [NumberField L] [Algebra K L]
variable (𝒢 : GroupModel A L)

/-- `Spec ℂ → Spec 𝓞_L` (via `τ`) hits the generic point. -/
theorem ptC_hom_apply (τ : L →+* ℂ) (x : Spec (CommRingCat.of ℂ)) :
    (GroupModel.ptC (L := L) τ).hom x = genericPt L := by
  haveI : x.asIdeal.IsPrime := x.isPrime
  have hx : x.asIdeal = ⊥ := Ideal.eq_bot_of_prime x.asIdeal
  apply PrimeSpectrum.ext
  show Ideal.comap (τ.comp (algebraMap (𝓞 L) L)) x.asIdeal = ⊥
  rw [hx]
  exact Ideal.comap_bot_of_injective _
    (τ.injective.comp (IsFractionRing.injective (𝓞 L) L))

/-- The identity complex point lies over `ξ`. -/
theorem one_left_apply (τ : L →+* ℂ) (x : Spec (CommRingCat.of ℂ)) :
    (1 : 𝒢.Pts τ).left x = 𝒢.genericUnit := by
  have hw : (toUnit (GroupModel.ptC (L := L) τ)).left = (GroupModel.ptC (L := L) τ).hom :=
    (Category.comp_id _).symm.trans (Over.w (toUnit (GroupModel.ptC (L := L) τ)))
  show (toUnit (GroupModel.ptC τ) ≫ η[𝒢.G]).left x = 𝒢.unitSection (genericPt L)
  rw [Over.comp_left]
  change (η[𝒢.G]).left ((toUnit (GroupModel.ptC (L := L) τ)).left x) = _
  rw [hw, ptC_hom_apply]
  rfl

/-- For an analytic uniformization, `0 ∈ dom Φ U` whenever `ξ ∈ U`. -/
theorem zero_mem_dom {τ : L →+* ℂ} {g : ℕ} {Λ : Submodule ℤ (Fin g → ℂ)}
    {Φ : (Fin g → ℂ) → 𝒢.Pts τ} (hΦ : 𝒢.IsAnalyticUniformization τ Λ Φ)
    (U : 𝒢.G.left.Opens) (m : 𝒢.genericUnit ∈ U) : (0 : Fin g → ℂ) ∈ 𝒢.dom Φ U := by
  have h1 : Φ 0 = 1 := by
    have h := hΦ.1 0 0
    rw [add_zero] at h
    exact mul_left_cancel (a := Φ 0) (by rw [_root_.mul_one]; exact h.symm)
  show ⊤ ≤ (Φ 0).left ⁻¹ᵁ U
  rw [h1]
  intro x _
  show (1 : 𝒢.Pts τ).left x ∈ U
  erw [one_left_apply]
  exact m

/-- `evalAt` is compatible with restriction. -/
theorem evalAt_res {τ : L →+* ℂ} (p : 𝒢.Pts τ) {U W : 𝒢.G.left.Opens} (i : W ⟶ U)
    (hW : ⊤ ≤ p.left ⁻¹ᵁ W) (s : Γ(𝒢.G.left, U)) :
    𝒢.evalAt p W (𝒢.G.left.presheaf.map i.op s) = 𝒢.evalAt p U s := by
  have hU : ⊤ ≤ p.left ⁻¹ᵁ U := hW.trans ((TopologicalSpace.Opens.map p.left.base).map i).le
  unfold GroupModel.evalAt
  rw [dif_pos hW, dif_pos hU, ← Scheme.Hom.map_appLE p.left hW i.op]
  rfl

/-- `evalAt` is additive in the section. -/
theorem evalAt_add {τ : L →+* ℂ} (p : 𝒢.Pts τ) (U : 𝒢.G.left.Opens) (s s' : Γ(𝒢.G.left, U)) :
    𝒢.evalAt p U (s + s') = 𝒢.evalAt p U s + 𝒢.evalAt p U s' := by
  unfold GroupModel.evalAt
  split_ifs with h
  · rw [map_add]
    exact map_add (ConcreteCategory.hom (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom) _ _
  · simp

/-- **`germAlong Φ t` is, near `0`, the function of any representative of `t`.** -/
theorem germAlong_eventuallyEq {τ : L →+* ℂ} {g : ℕ} {Λ : Submodule ℤ (Fin g → ℂ)}
    {Φ : (Fin g → ℂ) → 𝒢.Pts τ} (hΦ : 𝒢.IsAnalyticUniformization τ Λ Φ)
    (U : 𝒢.G.left.Opens) (m : 𝒢.genericUnit ∈ U) (s : Γ(𝒢.G.left, U)) :
    𝒢.germAlong Φ (𝒢.G.left.presheaf.germ U 𝒢.genericUnit m s) =ᶠ[𝓝 0]
      fun z => 𝒢.evalAt (Φ z) U s := by
  unfold GroupModel.germAlong
  obtain ⟨W, mW, i₁, i₂, hW⟩ := TopCat.Presheaf.germ_eq _ 𝒢.genericUnit _ m _ s
    (𝒢.exists_rep (𝒢.G.left.presheaf.germ U 𝒢.genericUnit m s)).choose_spec.choose_spec.choose_spec
  filter_upwards [(hΦ.2.2.2.1 W).mem_nhds (zero_mem_dom 𝒢 hΦ W mW)] with z hz
  rw [← evalAt_res 𝒢 (Φ z) i₁ hz, ← evalAt_res 𝒢 (Φ z) i₂ hz s, hW]

/-- `germAlong Φ t` is differentiable at `0`. -/
theorem germAlong_differentiableAt {τ : L →+* ℂ} {g : ℕ} {Λ : Submodule ℤ (Fin g → ℂ)}
    {Φ : (Fin g → ℂ) → 𝒢.Pts τ} (hΦ : 𝒢.IsAnalyticUniformization τ Λ Φ) (t : 𝒢.genStalk) :
    DifferentiableAt ℂ (𝒢.germAlong Φ t) 0 := by
  obtain ⟨U, m, s, rfl⟩ := 𝒢.exists_rep t
  have hd : DifferentiableAt ℂ (fun z => 𝒢.evalAt (Φ z) U s) 0 :=
    (hΦ.2.2.2.2 U s).differentiableAt ((hΦ.2.2.2.1 U).mem_nhds (zero_mem_dom 𝒢 hΦ U m))
  exact hd.congr_of_eventuallyEq (germAlong_eventuallyEq 𝒢 hΦ U m s)

/-- `germAlong Φ (x + y) = germAlong Φ x + germAlong Φ y` near `0`. -/
theorem germAlong_add_eventuallyEq {τ : L →+* ℂ} {g : ℕ} {Λ : Submodule ℤ (Fin g → ℂ)}
    {Φ : (Fin g → ℂ) → 𝒢.Pts τ} (hΦ : 𝒢.IsAnalyticUniformization τ Λ Φ) (x y : 𝒢.genStalk) :
    𝒢.germAlong Φ (x + y) =ᶠ[𝓝 0] 𝒢.germAlong Φ x + 𝒢.germAlong Φ y := by
  obtain ⟨U, m, s, rfl⟩ := 𝒢.exists_rep x
  obtain ⟨U', m', s', rfl⟩ := 𝒢.exists_rep y
  have mm : 𝒢.genericUnit ∈ U ⊓ U' := TopologicalSpace.Opens.mem_inf.mpr ⟨m, m'⟩
  have hsum : 𝒢.G.left.presheaf.germ U 𝒢.genericUnit m s +
      𝒢.G.left.presheaf.germ U' 𝒢.genericUnit m' s' =
      𝒢.G.left.presheaf.germ (U ⊓ U') 𝒢.genericUnit mm
        (𝒢.G.left.presheaf.map (homOfLE inf_le_left).op s +
          𝒢.G.left.presheaf.map (homOfLE inf_le_right).op s') := by
    simp only [map_add, TopCat.Presheaf.germ_res_apply]
  rw [hsum]
  filter_upwards [germAlong_eventuallyEq 𝒢 hΦ (U ⊓ U') mm _,
    germAlong_eventuallyEq 𝒢 hΦ U m s, germAlong_eventuallyEq 𝒢 hΦ U' m' s',
    (hΦ.2.2.2.1 (U ⊓ U')).mem_nhds (zero_mem_dom 𝒢 hΦ (U ⊓ U') mm)] with z h1 h2 h3 hz
  rw [Pi.add_apply, h1, h2, h3, evalAt_add, evalAt_res 𝒢 (Φ z) _ hz,
    evalAt_res 𝒢 (Φ z) _ hz]

/-- **Clause (ii) of `JacDetMultilinear`, proved: slot additivity.** -/
theorem jacDet_update_add {τ : L →+* ℂ} {g : ℕ} {Λ : Submodule ℤ (Fin g → ℂ)}
    {Φ : (Fin g → ℂ) → 𝒢.Pts τ} (hΦ : 𝒢.IsAnalyticUniformization τ Λ Φ)
    (f : Fin g → IsLocalRing.maximalIdeal 𝒢.genStalk) (i : Fin g)
    (x y : IsLocalRing.maximalIdeal 𝒢.genStalk) :
    𝒢.jacDet Φ (Function.update f i (x + y)) =
      𝒢.jacDet Φ (Function.update f i x) + 𝒢.jacDet Φ (Function.update f i y) := by
  let row : 𝒢.genStalk → Fin g → ℂ := fun t j => fderiv ℂ (𝒢.germAlong Φ t) 0 (Pi.single j 1)
  have hrow : row ((x + y : IsLocalRing.maximalIdeal 𝒢.genStalk) : 𝒢.genStalk) =
      row (x : 𝒢.genStalk) + row (y : 𝒢.genStalk) := by
    funext j
    simp only [row, Submodule.coe_add, Pi.add_apply]
    rw [(germAlong_add_eventuallyEq 𝒢 hΦ _ _).fderiv_eq,
      fderiv_add (germAlong_differentiableAt 𝒢 hΦ _) (germAlong_differentiableAt 𝒢 hΦ _)]
    rfl
  let M : Matrix (Fin g) (Fin g) ℂ := Matrix.of fun k j => row (f k : 𝒢.genStalk) j
  have e : ∀ z : IsLocalRing.maximalIdeal 𝒢.genStalk,
      𝒢.jacDet Φ (Function.update f i z) = (M.updateRow i (row (z : 𝒢.genStalk))).det := by
    intro z
    unfold GroupModel.jacDet
    congr 1
    ext k j
    by_cases hk : k = i
    · subst hk; simp [M, row]
    · simp [M, row, hk]
  rw [e, e, e, hrow, Matrix.det_updateRow_add]

/-- **Clause (iv) of `JacDetMultilinear`, proved: equal slots give `0`.** -/
theorem jacDet_eq_zero_of_eq {τ : L →+* ℂ} {g : ℕ} (Φ : (Fin g → ℂ) → 𝒢.Pts τ)
    (f : Fin g → IsLocalRing.maximalIdeal 𝒢.genStalk) (i j : Fin g) (h : f i = f j)
    (hij : i ≠ j) : 𝒢.jacDet Φ f = 0 := by
  unfold GroupModel.jacDet
  apply Matrix.det_zero_of_row_eq hij
  funext k
  simp [h]

end Germ

/-- **Glue (the two remaining clauses of `JacDetMultilinear`).** (i) `jacDet Φ f` depends only on
the classes `df_i ∈ 𝔪_ξ/𝔪_ξ²`; (iii) multiplying slot `i` by the image of `a ∈ 𝓞_L` multiplies
`jacDet` by `τ(a)`. Why true: by `germAlong_eventuallyEq` it suffices that for `f ∈ 𝔪_ξ²` the
function `evalAt (Φ z) U s` of a representative has derivative `0` at `0` (it is a sum of products
of functions vanishing at `0`, as evaluation at a complex point over `ξ` kills `𝔪_ξ`: the induced
map `𝒪_{𝒢,ξ} → 𝒪_{Spec ℂ} = ℂ` is local), and that the image of `a` evaluates to `τ(a)` (the point
lies over `Spec 𝓞_L` through `τ`). Unproved: needs `evalAt` through `Scheme.Hom.stalkMap` and
`ΓSpecIso`. -/
def JacDetClassScalar : Prop :=
  ∀ (K : Type) [Field K] (A : AbVar K) (L : Type) [Field L] [NumberField L] [Algebra K L]
    (𝒢 : GroupModel A L) (τ : L →+* ℂ) (g : ℕ) (Λ : Submodule ℤ (Fin g → ℂ))
    (Φ : (Fin g → ℂ) → 𝒢.Pts τ), 𝒢.IsAnalyticUniformization τ Λ Φ →
    (∀ f f' : Fin g → IsLocalRing.maximalIdeal 𝒢.genStalk,
      (∀ i, 𝒢.dCls (f i) = 𝒢.dCls (f' i)) → 𝒢.jacDet Φ f = 𝒢.jacDet Φ f') ∧
    (∀ (f : Fin g → IsLocalRing.maximalIdeal 𝒢.genStalk) (i : Fin g) (a : 𝓞 L)
      (x : IsLocalRing.maximalIdeal 𝒢.genStalk),
      𝒢.jacDet Φ (Function.update f i (𝒢.structMap a • x)) =
        τ (algebraMap (𝓞 L) L a) * 𝒢.jacDet Φ (Function.update f i x))

/-- **`JacDetMultilinear` from `JacDetClassScalar` (proved).** -/
theorem jacDetMultilinear_of (h : JacDetClassScalar) : JacDetMultilinear := by
  intro K _ A L _ _ _ 𝒢 τ g Λ Φ hΦ
  obtain ⟨h1, h3⟩ := h K A L 𝒢 τ g Λ Φ hΦ
  exact ⟨h1, fun f i x y => jacDet_update_add 𝒢 hΦ f i x y, h3,
    fun f i j hij hne => jacDet_eq_zero_of_eq 𝒢 Φ f i j hij hne⟩

end ZInQ.Metrization



/-! ## metrization: clause (iii) of `JacDetMultilinear` (scaling by `τ(a)`), proved -/

namespace ZInQ.Metrization

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open NumberField DefFaltings Topology

section Scalar

variable {K : Type} [Field K] {A : AbVar K} {L : Type} [Field L] [NumberField L] [Algebra K L]
variable (𝒢 : GroupModel A L)

/-- `evalAt` is multiplicative in the section. -/
theorem evalAt_mul {τ : L →+* ℂ} (p : 𝒢.Pts τ) (U : 𝒢.G.left.Opens) (s s' : Γ(𝒢.G.left, U)) :
    𝒢.evalAt p U (s * s') = 𝒢.evalAt p U s * 𝒢.evalAt p U s' := by
  unfold GroupModel.evalAt
  split_ifs with h
  · rw [map_mul]
    exact map_mul (ConcreteCategory.hom (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom) _ _
  · simp

/-- A function from `𝓞_L` evaluates to `τ(a)` at every complex point. -/
theorem evalAt_structSection {τ : L →+* ℂ} (p : 𝒢.Pts τ) (a : 𝓞 L) :
    𝒢.evalAt p ⊤ (𝒢.G.hom.appTop ((Scheme.ΓSpecIso (CommRingCat.of (𝓞 L))).inv a)) =
      τ (algebraMap (𝓞 L) L a) := by
  have htop : ⊤ ≤ p.left ⁻¹ᵁ (⊤ : 𝒢.G.left.Opens) := fun x _ => trivial
  unfold GroupModel.evalAt
  rw [dif_pos htop]
  have hw : p.left ≫ 𝒢.G.hom = (GroupModel.ptC τ).hom := Over.w p
  have h1 : p.left.appLE ⊤ ⊤ htop = p.left.appTop := Scheme.Hom.appLE_eq_app p.left
  have h2 : (p.left.appTop) (𝒢.G.hom.appTop ((Scheme.ΓSpecIso (CommRingCat.of (𝓞 L))).inv a)) =
      ((p.left ≫ 𝒢.G.hom).appTop) ((Scheme.ΓSpecIso (CommRingCat.of (𝓞 L))).inv a) := by
    rw [Scheme.Hom.comp_appTop]
    rfl
  rw [h1, h2, hw]
  have h3 := congrArg (fun f => f ((Scheme.ΓSpecIso (CommRingCat.of (𝓞 L))).inv a))
    (Scheme.ΓSpecIso_naturality (CommRingCat.ofHom (τ.comp (algebraMap (𝓞 L) L))))
  simp only [ConcreteCategory.comp_apply] at h3
  refine h3.trans ?_
  simp

/-- `germAlong Φ (structMap a * x) = τ(a) · germAlong Φ x` near `0`. -/
theorem germAlong_structMap_mul_eventuallyEq {τ : L →+* ℂ} {g : ℕ} {Λ : Submodule ℤ (Fin g → ℂ)}
    {Φ : (Fin g → ℂ) → 𝒢.Pts τ} (hΦ : 𝒢.IsAnalyticUniformization τ Λ Φ) (a : 𝓞 L)
    (x : 𝒢.genStalk) :
    𝒢.germAlong Φ (𝒢.structMap a * x) =ᶠ[𝓝 0]
      fun z => τ (algebraMap (𝓞 L) L a) * 𝒢.germAlong Φ x z := by
  obtain ⟨U, m, s, rfl⟩ := 𝒢.exists_rep x
  set σa : Γ(𝒢.G.left, ⊤) :=
    𝒢.G.hom.appTop ((Scheme.ΓSpecIso (CommRingCat.of (𝓞 L))).inv a) with hσa
  have hprod : 𝒢.structMap a * 𝒢.G.left.presheaf.germ U 𝒢.genericUnit m s =
      𝒢.G.left.presheaf.germ U 𝒢.genericUnit m
        (𝒢.G.left.presheaf.map (homOfLE le_top).op σa * s) := by
    rw [map_mul, TopCat.Presheaf.germ_res_apply]
    rfl
  rw [hprod]
  filter_upwards [germAlong_eventuallyEq 𝒢 hΦ U m _, germAlong_eventuallyEq 𝒢 hΦ U m s,
    (hΦ.2.2.2.1 U).mem_nhds (zero_mem_dom 𝒢 hΦ U m)] with z h1 h2 hz
  rw [h1, h2, evalAt_mul, evalAt_res 𝒢 (Φ z) _ hz, hσa, evalAt_structSection]

/-- **Clause (iii) of `JacDetMultilinear`, proved: scaling by `τ(a)`.** -/
theorem jacDet_update_smul {τ : L →+* ℂ} {g : ℕ} {Λ : Submodule ℤ (Fin g → ℂ)}
    {Φ : (Fin g → ℂ) → 𝒢.Pts τ} (hΦ : 𝒢.IsAnalyticUniformization τ Λ Φ)
    (f : Fin g → IsLocalRing.maximalIdeal 𝒢.genStalk) (i : Fin g) (a : 𝓞 L)
    (x : IsLocalRing.maximalIdeal 𝒢.genStalk) :
    𝒢.jacDet Φ (Function.update f i (𝒢.structMap a • x)) =
      τ (algebraMap (𝓞 L) L a) * 𝒢.jacDet Φ (Function.update f i x) := by
  let row : 𝒢.genStalk → Fin g → ℂ := fun t j => fderiv ℂ (𝒢.germAlong Φ t) 0 (Pi.single j 1)
  have hrow : row ((𝒢.structMap a • x : IsLocalRing.maximalIdeal 𝒢.genStalk) : 𝒢.genStalk) =
      τ (algebraMap (𝓞 L) L a) • row (x : 𝒢.genStalk) := by
    funext j
    simp only [row, Submodule.coe_smul, smul_eq_mul, Pi.smul_apply]
    rw [(germAlong_structMap_mul_eventuallyEq 𝒢 hΦ a _).fderiv_eq,
      fderiv_const_mul (germAlong_differentiableAt 𝒢 hΦ _)]
    rfl
  let M : Matrix (Fin g) (Fin g) ℂ := Matrix.of fun k j => row (f k : 𝒢.genStalk) j
  have e : ∀ z : IsLocalRing.maximalIdeal 𝒢.genStalk,
      𝒢.jacDet Φ (Function.update f i z) = (M.updateRow i (row (z : 𝒢.genStalk))).det := by
    intro z
    unfold GroupModel.jacDet
    congr 1
    ext k j
    by_cases hk : k = i
    · subst hk; simp [M, row]
    · simp [M, row, hk]
  rw [e, e, hrow, Matrix.det_updateRow_smul]

end Scalar

/-- **Glue (the last clause of `JacDetMultilinear`: class invariance).** `jacDet Φ f` depends
only on the classes `df_i ∈ 𝔪_ξ/𝔪_ξ²`. Why true: by `germAlong_eventuallyEq` and
`germAlong_add_eventuallyEq` it suffices that `d(germAlong Φ t)(0) = 0` for `t ∈ 𝔪_ξ²`, a sum of
products `uv` with `u, v ∈ 𝔪_ξ`; `germAlong Φ (uv) = (germAlong Φ u)(germAlong Φ v)` near `0` (as
for sums, with `evalAt_mul`), and `germAlong Φ u` vanishes at `0` because the identity point
`Spec ℂ → 𝒢` lies over `ξ` (`one_left_apply`) and induces a local map `𝒪_{𝒢,ξ} → 𝒪_{Spec ℂ} = ℂ`,
which kills `𝔪_ξ`; then Leibniz. Unproved (needs `evalAt` through `Scheme.Hom.stalkMap` at the
identity point). -/
def JacDetClassInvariant : Prop :=
  ∀ (K : Type) [Field K] (A : AbVar K) (L : Type) [Field L] [NumberField L] [Algebra K L]
    (𝒢 : GroupModel A L) (τ : L →+* ℂ) (g : ℕ) (Λ : Submodule ℤ (Fin g → ℂ))
    (Φ : (Fin g → ℂ) → 𝒢.Pts τ), 𝒢.IsAnalyticUniformization τ Λ Φ →
    ∀ f f' : Fin g → IsLocalRing.maximalIdeal 𝒢.genStalk,
      (∀ i, 𝒢.dCls (f i) = 𝒢.dCls (f' i)) → 𝒢.jacDet Φ f = 𝒢.jacDet Φ f'

/-- **`JacDetClassScalar` from `JacDetClassInvariant` (proved).** -/
theorem jacDetClassScalar_of (h : JacDetClassInvariant) : JacDetClassScalar := by
  intro K _ A L _ _ _ 𝒢 τ g Λ Φ hΦ
  exact ⟨h K A L 𝒢 τ g Λ Φ hΦ, fun f i a x => jacDet_update_smul 𝒢 hΦ f i a x⟩

end ZInQ.Metrization



/-! ## metrization: clause (i) of `JacDetMultilinear` (class invariance), proved

So `JacDetMultilinear`, hence `JacDetDescends`, is a theorem. -/

namespace ZInQ.Metrization

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open NumberField DefFaltings Topology

section ClassInv

variable {K : Type} [Field K] {A : AbVar K} {L : Type} [Field L] [NumberField L] [Algebra K L]
variable (𝒢 : GroupModel A L)

/-- A section whose germ at `ξ` lies in `𝔪_ξ` vanishes at the identity complex point. -/
theorem evalAt_one_eq_zero {τ : L →+* ℂ} (U : 𝒢.G.left.Opens) (m : 𝒢.genericUnit ∈ U)
    (s : Γ(𝒢.G.left, U))
    (hs : 𝒢.G.left.presheaf.germ U 𝒢.genericUnit m s ∈ IsLocalRing.maximalIdeal 𝒢.genStalk) :
    𝒢.evalAt (1 : 𝒢.Pts τ) U s = 0 := by
  set q := (1 : 𝒢.Pts τ).left with hqdef
  have hq : ∀ x, q x = 𝒢.genericUnit := fun x => by
    rw [hqdef]
    erw [one_left_apply]
  have h : ⊤ ≤ q ⁻¹ᵁ U := by
    intro x _
    show q x ∈ U
    rw [hq]
    exact m
  unfold GroupModel.evalAt
  rw [dif_pos h]
  let q' : Spec (CommRingCat.of ℂ) ⟶ 𝒢.G.left := q
  have h' : ⊤ ≤ q' ⁻¹ᵁ U := h
  change (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom (q'.appLE U ⊤ h' s) = 0
  let x : Spec (CommRingCat.of ℂ) := genericPoint (Spec (CommRingCat.of ℂ))
  have hxt : x ∈ (⊤ : (Spec (CommRingCat.of ℂ)).Opens) := by simp
  have hx : q' x ∈ U := h' hxt
  have key : q'.appLE U ⊤ h' ≫ (Spec (CommRingCat.of ℂ)).presheaf.germ ⊤ x hxt =
      𝒢.G.left.presheaf.germ U (q' x) hx ≫ q'.stalkMap x := by
    simp only [Scheme.Hom.appLE, Category.assoc, Scheme.Hom.germ_stalkMap]
    rw [TopCat.Presheaf.germ_res]
  have hmem : ∀ (y : 𝒢.G.left) (hy : y ∈ U), y = 𝒢.genericUnit →
      𝒢.G.left.presheaf.germ U y hy s ∈
        IsLocalRing.maximalIdeal (𝒢.G.left.presheaf.stalk y) := by
    rintro y hy rfl
    exact hs
  have h1 := hmem (q' x) hx (hq x)
  have h2 : (q'.stalkMap x).hom (𝒢.G.left.presheaf.germ U (q' x) hx s) ∈
      IsLocalRing.maximalIdeal ((Spec (CommRingCat.of ℂ)).presheaf.stalk x) :=
    map_nonunit _ _ ((IsLocalRing.mem_maximalIdeal _).mp h1)
  have hfield : IsField ((Spec (CommRingCat.of ℂ)).presheaf.stalk x) := Field.toIsField _
  rw [IsLocalRing.isField_iff_maximalIdeal_eq.mp hfield] at h2
  have h4 : ((Spec (CommRingCat.of ℂ)).presheaf.germ ⊤ x hxt) (q'.appLE U ⊤ h' s) =
      (q'.stalkMap x) (𝒢.G.left.presheaf.germ U (q' x) hx s) := by
    rw [← ConcreteCategory.comp_apply, key, ConcreteCategory.comp_apply]
  have h5 : q'.appLE U ⊤ h' s = 0 := by
    apply germ_injective_of_isIntegral (U := ⊤) _ x hxt
    rw [map_zero]
    exact h4.trans h2
  rw [h5, map_zero]

/-- `germAlong Φ u` vanishes at `0` for `u ∈ 𝔪_ξ`. -/
theorem germAlong_zero_of_mem {τ : L →+* ℂ} {g : ℕ} {Λ : Submodule ℤ (Fin g → ℂ)}
    {Φ : (Fin g → ℂ) → 𝒢.Pts τ} (hΦ : 𝒢.IsAnalyticUniformization τ Λ Φ) (u : 𝒢.genStalk)
    (hu : u ∈ IsLocalRing.maximalIdeal 𝒢.genStalk) : 𝒢.germAlong Φ u 0 = 0 := by
  obtain ⟨U, m, s, rfl⟩ := 𝒢.exists_rep u
  have h1 : Φ 0 = 1 := by
    have h := hΦ.1 0 0
    rw [add_zero] at h
    exact mul_left_cancel (a := Φ 0) (by rw [_root_.mul_one]; exact h.symm)
  rw [(germAlong_eventuallyEq 𝒢 hΦ U m s).eq_of_nhds, h1]
  exact evalAt_one_eq_zero 𝒢 U m s hu

/-- `germAlong Φ (x * y) = germAlong Φ x * germAlong Φ y` near `0`. -/
theorem germAlong_mul_eventuallyEq {τ : L →+* ℂ} {g : ℕ} {Λ : Submodule ℤ (Fin g → ℂ)}
    {Φ : (Fin g → ℂ) → 𝒢.Pts τ} (hΦ : 𝒢.IsAnalyticUniformization τ Λ Φ) (x y : 𝒢.genStalk) :
    𝒢.germAlong Φ (x * y) =ᶠ[𝓝 0] 𝒢.germAlong Φ x * 𝒢.germAlong Φ y := by
  obtain ⟨U, m, s, rfl⟩ := 𝒢.exists_rep x
  obtain ⟨U', m', s', rfl⟩ := 𝒢.exists_rep y
  have mm : 𝒢.genericUnit ∈ U ⊓ U' := TopologicalSpace.Opens.mem_inf.mpr ⟨m, m'⟩
  have hprod : 𝒢.G.left.presheaf.germ U 𝒢.genericUnit m s *
      𝒢.G.left.presheaf.germ U' 𝒢.genericUnit m' s' =
      𝒢.G.left.presheaf.germ (U ⊓ U') 𝒢.genericUnit mm
        (𝒢.G.left.presheaf.map (homOfLE inf_le_left).op s *
          𝒢.G.left.presheaf.map (homOfLE inf_le_right).op s') := by
    simp only [map_mul, TopCat.Presheaf.germ_res_apply]
  rw [hprod]
  filter_upwards [germAlong_eventuallyEq 𝒢 hΦ (U ⊓ U') mm _,
    germAlong_eventuallyEq 𝒢 hΦ U m s, germAlong_eventuallyEq 𝒢 hΦ U' m' s',
    (hΦ.2.2.2.1 (U ⊓ U')).mem_nhds (zero_mem_dom 𝒢 hΦ (U ⊓ U') mm)] with z h1 h2 h3 hz
  rw [Pi.mul_apply, h1, h2, h3, evalAt_mul, evalAt_res 𝒢 (Φ z) _ hz,
    evalAt_res 𝒢 (Φ z) _ hz]

/-- `d(germAlong Φ t)(0) = 0` for `t ∈ 𝔪_ξ²`. -/
theorem fderiv_germAlong_eq_zero_of_mem_sq {τ : L →+* ℂ} {g : ℕ} {Λ : Submodule ℤ (Fin g → ℂ)}
    {Φ : (Fin g → ℂ) → 𝒢.Pts τ} (hΦ : 𝒢.IsAnalyticUniformization τ Λ Φ) (t : 𝒢.genStalk)
    (ht : t ∈ IsLocalRing.maximalIdeal 𝒢.genStalk ^ 2) :
    fderiv ℂ (𝒢.germAlong Φ t) 0 = 0 := by
  rw [pow_two] at ht
  refine Submodule.mul_induction_on ht (fun u hu v hv => ?_) (fun a b ha hb => ?_)
  · rw [(germAlong_mul_eventuallyEq 𝒢 hΦ u v).fderiv_eq,
      fderiv_mul (germAlong_differentiableAt 𝒢 hΦ u) (germAlong_differentiableAt 𝒢 hΦ v),
      germAlong_zero_of_mem 𝒢 hΦ u hu, germAlong_zero_of_mem 𝒢 hΦ v hv]
    ext v
    simp
  · rw [(germAlong_add_eventuallyEq 𝒢 hΦ a b).fderiv_eq,
      fderiv_add (germAlong_differentiableAt 𝒢 hΦ a) (germAlong_differentiableAt 𝒢 hΦ b), ha, hb,
      add_zero]

/-- **Clause (i) of `JacDetMultilinear`, proved: `jacDet` depends only on the classes `df_i`.** -/
theorem jacDet_congr_dCls {τ : L →+* ℂ} {g : ℕ} {Λ : Submodule ℤ (Fin g → ℂ)}
    {Φ : (Fin g → ℂ) → 𝒢.Pts τ} (hΦ : 𝒢.IsAnalyticUniformization τ Λ Φ)
    (f f' : Fin g → IsLocalRing.maximalIdeal 𝒢.genStalk)
    (h : ∀ i, 𝒢.dCls (f i) = 𝒢.dCls (f' i)) : 𝒢.jacDet Φ f = 𝒢.jacDet Φ f' := by
  have hrow : ∀ i, fderiv ℂ (𝒢.germAlong Φ (f i : 𝒢.genStalk)) 0 =
      fderiv ℂ (𝒢.germAlong Φ (f' i : 𝒢.genStalk)) 0 := by
    intro i
    have hsq : ((f i : 𝒢.genStalk) - f' i) ∈ IsLocalRing.maximalIdeal 𝒢.genStalk ^ 2 :=
      (Ideal.toCotangent_eq (IsLocalRing.maximalIdeal 𝒢.genStalk)).mp (h i)
    have hdecomp : (f i : 𝒢.genStalk) = f' i + ((f i : 𝒢.genStalk) - f' i) := by ring
    rw [hdecomp, (germAlong_add_eventuallyEq 𝒢 hΦ _ _).fderiv_eq,
      fderiv_add (germAlong_differentiableAt 𝒢 hΦ _) (germAlong_differentiableAt 𝒢 hΦ _),
      fderiv_germAlong_eq_zero_of_mem_sq 𝒢 hΦ _ hsq, add_zero]
  unfold GroupModel.jacDet
  congr 1
  ext i j
  simp only [Matrix.of_apply, hrow i]

end ClassInv

/-- **`JacDetClassInvariant`, proved.** -/
theorem jacDetClassInvariant : JacDetClassInvariant := by
  intro K _ A L _ _ _ 𝒢 τ g Λ Φ hΦ f f' h
  exact jacDet_congr_dCls 𝒢 hΦ f f' h

/-- **`JacDetDescends`, proved** (no hypotheses). -/
theorem jacDetDescends : JacDetDescends :=
  jacDetDescends_of (jacDetMultilinear_of (jacDetClassScalar_of jacDetClassInvariant))

end ZInQ.Metrization


/-! Further verbatim copies from `scratch/metrization/` (only `open PkgI3 (AbVar)` added, the
declarations after the cut points dropped): `part_prodgeo.lean` up to `ProductLatticeFacts`
(exclusive), `part_prodlat.lean` up to `blockLinearEquiv` (exclusive), `part_produnif.lean` up to
`productUniformization_of` (exclusive), `part_prodsplit.lean` up to `productHodgeCompat_of`
(exclusive), `part_prodjac.lean` up to `productMetrizationGeo_of'''` (exclusive),
`part_produnif2.lean` up to `productMetrizationGeo_of_local` (exclusive). -/


/-! ## metrization (2026-11-13): `ProductMetrizationGeo` reduced

`ProductMetrizationGeo` (P2a-geo) follows from `JacDetDescends` (shared with `MetrizationExists`),
`ProductUniformization` (glue: `Φ₁ × Φ₂` is an analytic uniformization of the product model),
`ProductLatticeFacts` (pure Mathlib glue: `Λ₁ × Λ₂` is a full lattice and covolumes multiply)
and `ProductHodgeCompat` (glue: `⋀^{top}ω_{𝒢P} = ⋀ω₁ ⊗ ⋀ω₂` with the block-diagonal Jacobian). -/

namespace ZInQ.Metrization

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open NumberField DefFaltings

/-- The first `g₁` coordinates of `ℂ^{g₁+g₂}`. -/
noncomputable def leftBlock (g₁ g₂ : ℕ) : (Fin (g₁ + g₂) → ℂ) →ₗ[ℂ] (Fin g₁ → ℂ) :=
  LinearMap.pi fun i => LinearMap.proj (Fin.castAdd g₂ i)

/-- The last `g₂` coordinates of `ℂ^{g₁+g₂}`. -/
noncomputable def rightBlock (g₁ g₂ : ℕ) : (Fin (g₁ + g₂) → ℂ) →ₗ[ℂ] (Fin g₂ → ℂ) :=
  LinearMap.pi fun j => LinearMap.proj (Fin.natAdd g₁ j)

/-- The product lattice `Λ₁ × Λ₂ ⊂ ℂ^{g₁} × ℂ^{g₂} = ℂ^{g₁+g₂}` (coordinates `Fin.append`). -/
noncomputable def prodLattice {g₁ g₂ : ℕ} (Λ₁ : Submodule ℤ (Fin g₁ → ℂ))
    (Λ₂ : Submodule ℤ (Fin g₂ → ℂ)) : Submodule ℤ (Fin (g₁ + g₂) → ℂ) :=
  Λ₁.comap (leftBlock g₁ g₂).toAddMonoidHom.toIntLinearMap ⊓
    Λ₂.comap (rightBlock g₁ g₂).toAddMonoidHom.toIntLinearMap

/-- The product map `ℂ^{g₁+g₂} → 𝒢₁(ℂ)_τ × 𝒢₂(ℂ)_τ ≅ 𝒢P(ℂ)_τ`, `z ↦ e⁻¹(Φ₁(z'), Φ₂(z''))`. -/
noncomputable def prodPts {K : Type} [Field K] {A B C : AbVar K} {L : Type} [Field L]
    [NumberField L] [Algebra K L] {𝒢P : GroupModel C L} {𝒢₁ : GroupModel A L}
    {𝒢₂ : GroupModel B L} (e : 𝒢P.G ≅ 𝒢₁.G ⊗ 𝒢₂.G) {τ : L →+* ℂ} {g₁ g₂ : ℕ}
    (Φ₁ : (Fin g₁ → ℂ) → 𝒢₁.Pts τ) (Φ₂ : (Fin g₂ → ℂ) → 𝒢₂.Pts τ) :
    (Fin (g₁ + g₂) → ℂ) → 𝒢P.Pts τ :=
  fun z => lift (Φ₁ (leftBlock g₁ g₂ z)) (Φ₂ (rightBlock g₁ g₂ z)) ≫ e.inv

end ZInQ.Metrization


/-! ## metrization: `ProductLatticeFacts`, proved (body of ProdLattice.lean, section Proof) -/

namespace ZInQ.Metrization

open MeasureTheory

section Proof

variable {g₁ g₂ : ℕ}

@[simp] theorem leftBlock_apply (z : Fin (g₁ + g₂) → ℂ) (i : Fin g₁) :
    leftBlock g₁ g₂ z i = z (Fin.castAdd g₂ i) := rfl

@[simp] theorem rightBlock_apply (z : Fin (g₁ + g₂) → ℂ) (j : Fin g₂) :
    rightBlock g₁ g₂ z j = z (Fin.natAdd g₁ j) := rfl

theorem mem_prodLattice {Λ₁ : Submodule ℤ (Fin g₁ → ℂ)} {Λ₂ : Submodule ℤ (Fin g₂ → ℂ)}
    {z : Fin (g₁ + g₂) → ℂ} :
    z ∈ prodLattice Λ₁ Λ₂ ↔ leftBlock g₁ g₂ z ∈ Λ₁ ∧ rightBlock g₁ g₂ z ∈ Λ₂ := Iff.rfl

theorem eq_of_blocks {z w : Fin (g₁ + g₂) → ℂ} (h1 : leftBlock g₁ g₂ z = leftBlock g₁ g₂ w)
    (h2 : rightBlock g₁ g₂ z = rightBlock g₁ g₂ w) : z = w := by
  funext k
  refine Fin.addCases (fun i => ?_) (fun j => ?_) k
  · exact congrFun h1 i
  · exact congrFun h2 j

@[simp] theorem leftBlock_append (x : Fin g₁ → ℂ) (y : Fin g₂ → ℂ) :
    leftBlock g₁ g₂ (Fin.append x y) = x := by
  funext i; simp

@[simp] theorem rightBlock_append (x : Fin g₁ → ℂ) (y : Fin g₂ → ℂ) :
    rightBlock g₁ g₂ (Fin.append x y) = y := by
  funext j; simp

end Proof

end ZInQ.Metrization


/-! ## metrization: the algebraic half of `ProductUniformization`, proved

`prodPts e Φ₁ Φ₂` is a surjective homomorphism with kernel `Λ₁ × Λ₂` (from `e` and the universal
property of `⊗`); `ProductUniformization` is reduced to `ProductUniformizationAnalytic` (openness
of `dom` and holomorphy). -/

namespace ZInQ.Metrization

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open NumberField DefFaltings

section ProdPtsAlg

variable {K : Type} [Field K] {A B C : AbVar K} {L : Type} [Field L] [NumberField L]
  [Algebra K L] {𝒢P : GroupModel C L} {𝒢₁ : GroupModel A L} {𝒢₂ : GroupModel B L}
  (e : 𝒢P.G ≅ 𝒢₁.G ⊗ 𝒢₂.G) {τ : L →+* ℂ} {g₁ g₂ : ℕ}

theorem prodPts_comp_fst (Φ₁ : (Fin g₁ → ℂ) → 𝒢₁.Pts τ) (Φ₂ : (Fin g₂ → ℂ) → 𝒢₂.Pts τ)
    (z : Fin (g₁ + g₂) → ℂ) : prodPts e Φ₁ Φ₂ z ≫ e.hom ≫ fst _ _ = Φ₁ (leftBlock g₁ g₂ z) := by
  simp [prodPts]

theorem prodPts_comp_snd (Φ₁ : (Fin g₁ → ℂ) → 𝒢₁.Pts τ) (Φ₂ : (Fin g₂ → ℂ) → 𝒢₂.Pts τ)
    (z : Fin (g₁ + g₂) → ℂ) : prodPts e Φ₁ Φ₂ z ≫ e.hom ≫ snd _ _ = Φ₂ (rightBlock g₁ g₂ z) := by
  simp [prodPts]

theorem pts_ext {p q : 𝒢P.Pts τ} (h1 : p ≫ e.hom ≫ fst _ _ = q ≫ e.hom ≫ fst _ _)
    (h2 : p ≫ e.hom ≫ snd _ _ = q ≫ e.hom ≫ snd _ _) : p = q := by
  rw [← cancel_mono e.hom]
  apply CartesianMonoidalCategory.hom_ext
  · simpa using h1
  · simpa using h2

/-- **The algebraic clauses of `IsAnalyticUniformization` for `prodPts` (proved).** -/
theorem prodPts_alg (hfst : IsMonHom (e.hom ≫ fst _ _)) (hsnd : IsMonHom (e.hom ≫ snd _ _))
    {Λ₁ : Submodule ℤ (Fin g₁ → ℂ)} {Λ₂ : Submodule ℤ (Fin g₂ → ℂ)}
    {Φ₁ : (Fin g₁ → ℂ) → 𝒢₁.Pts τ} {Φ₂ : (Fin g₂ → ℂ) → 𝒢₂.Pts τ}
    (h₁ : 𝒢₁.IsAnalyticUniformization τ Λ₁ Φ₁) (h₂ : 𝒢₂.IsAnalyticUniformization τ Λ₂ Φ₂) :
    (∀ z w, prodPts e Φ₁ Φ₂ (z + w) = prodPts e Φ₁ Φ₂ z * prodPts e Φ₁ Φ₂ w) ∧
    (∀ z, prodPts e Φ₁ Φ₂ z = 1 ↔ z ∈ prodLattice Λ₁ Λ₂) ∧
    Function.Surjective (prodPts e Φ₁ Φ₂) := by
  refine ⟨fun z w => ?_, fun z => ?_, fun p => ?_⟩
  · apply pts_ext e
    · rw [MonObj.mul_comp, prodPts_comp_fst, prodPts_comp_fst, prodPts_comp_fst, map_add,
        h₁.1]
    · rw [MonObj.mul_comp, prodPts_comp_snd, prodPts_comp_snd, prodPts_comp_snd, map_add,
        h₂.1]
  · constructor
    · intro h
      have e1 : Φ₁ (leftBlock g₁ g₂ z) = 1 := by
        rw [← prodPts_comp_fst e Φ₁ Φ₂ z, h, MonObj.one_comp]
      have e2 : Φ₂ (rightBlock g₁ g₂ z) = 1 := by
        rw [← prodPts_comp_snd e Φ₁ Φ₂ z, h, MonObj.one_comp]
      exact mem_prodLattice.mpr ⟨(h₁.2.1 _).mp e1, (h₂.2.1 _).mp e2⟩
    · intro hz
      obtain ⟨hz1, hz2⟩ := mem_prodLattice.mp hz
      apply pts_ext e
      · rw [prodPts_comp_fst, MonObj.one_comp, (h₁.2.1 _).mpr hz1]
      · rw [prodPts_comp_snd, MonObj.one_comp, (h₂.2.1 _).mpr hz2]
  · obtain ⟨x, hx⟩ := h₁.2.2.1 (p ≫ e.hom ≫ fst _ _)
    obtain ⟨y, hy⟩ := h₂.2.2.1 (p ≫ e.hom ≫ snd _ _)
    refine ⟨Fin.append x y, pts_ext e ?_ ?_⟩
    · rw [prodPts_comp_fst, leftBlock_append, hx]
    · rw [prodPts_comp_snd, rightBlock_append, hy]

end ProdPtsAlg

/-- **Glue (the analytic half of the product uniformization).** With the hypotheses of
`ProductUniformization`: each `dom (prodPts e Φ₁ Φ₂) U` is open and each regular function on `U`
is holomorphic along `prodPts e Φ₁ Φ₂` there. Why true: as in `ProductUniformization` (basic opens
`D(h)` of products of affine opens; regular functions `a/hⁿ`, `a, h ∈ R₁ ⊗_{𝓞_L} R₂`). STANDARD,
unproved. -/
def ProductUniformizationAnalytic : Prop :=
  ∀ (K : Type) [Field K] (A B C : AbVar K) (L : Type) [Field L] [NumberField L] [Algebra K L]
    (𝒢P : GroupModel C L) (𝒢₁ : GroupModel A L) (𝒢₂ : GroupModel B L)
    (e : 𝒢P.G ≅ 𝒢₁.G ⊗ 𝒢₂.G), IsMonHom (e.hom ≫ fst _ _) → IsMonHom (e.hom ≫ snd _ _) →
    ∀ (τ : L →+* ℂ) (g₁ g₂ : ℕ) (Λ₁ : Submodule ℤ (Fin g₁ → ℂ)) (Λ₂ : Submodule ℤ (Fin g₂ → ℂ))
      (Φ₁ : (Fin g₁ → ℂ) → 𝒢₁.Pts τ) (Φ₂ : (Fin g₂ → ℂ) → 𝒢₂.Pts τ),
      𝒢₁.IsAnalyticUniformization τ Λ₁ Φ₁ → 𝒢₂.IsAnalyticUniformization τ Λ₂ Φ₂ →
      (∀ U, IsOpen (𝒢P.dom (prodPts e Φ₁ Φ₂) U)) ∧
      (∀ U (s : Γ(𝒢P.G.left, U)), DifferentiableOn ℂ
        (fun z => 𝒢P.evalAt (prodPts e Φ₁ Φ₂ z) U s) (𝒢P.dom (prodPts e Φ₁ Φ₂) U))

end ZInQ.Metrization


/-! ## metrization: `ProductHodgeCompat` split into an algebraic and an analytic Prop

`pullGerm φ : 𝒪_{ℋ,ξ} → 𝒪_{𝒢,ξ}` (pull-back of germs along a homomorphism of group models; it
needs `φ(ξ_𝒢) = ξ_ℋ`, proved from `IsMonHom`). `ProductHodgeLattice` (algebra: `s = p₁*s₁ ∧ p₂*s₂`
lies in the lattice with multiplicative index) and `ProductJacobian` (analysis: block-diagonal
Jacobian) give `ProductHodgeCompat` (with `ProductUniformization`). -/

namespace ZInQ.Metrization

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open NumberField DefFaltings

section Pull

variable {K : Type} [Field K] {A C : AbVar K} {L : Type} [Field L] [NumberField L] [Algebra K L]

/-- A homomorphism of group models maps the identity `ξ` of the generic fibre to `ξ` (proved). -/
theorem map_genericUnit_of_isMonHom {𝒢 : GroupModel C L} {ℋ : GroupModel A L} (φ : 𝒢.G ⟶ ℋ.G)
    [IsMonHom φ] : φ.left 𝒢.genericUnit = ℋ.genericUnit := by
  have h1 : η[𝒢.G] ≫ φ = η[ℋ.G] := IsMonHom.one_hom φ
  have h2 : (η[𝒢.G]).left ≫ φ.left = (η[ℋ.G]).left := by rw [← Over.comp_left, h1]
  show φ.left ((η[𝒢.G]).left (genericPt L)) = (η[ℋ.G]).left (genericPt L)
  rw [← h2]
  rfl

/-- Pull-back of germs at `ξ` along a homomorphism of group models: `𝒪_{ℋ,ξ} → 𝒪_{𝒢,ξ}`. -/
noncomputable def pullGerm {𝒢 : GroupModel C L} {ℋ : GroupModel A L} (φ : 𝒢.G ⟶ ℋ.G)
    [IsMonHom φ] : ℋ.genStalk ⟶ 𝒢.genStalk :=
  ℋ.G.left.presheaf.stalkSpecializes
      ((congrArg (fun x => x ⤳ ℋ.genericUnit) (map_genericUnit_of_isMonHom φ)).mpr
        specializes_rfl) ≫
    φ.left.stalkMap 𝒢.genericUnit

end Pull

/-- **Glue (algebra: the Hodge lattice of a product).** For `e : 𝒢P ≅ M₁.model × M₂.model` with
homomorphic components: `hodgeSpace (g₁+g₂)` of `𝒢P` is a line, and there are germ tuples
`f₁, f₂` and their pull-backs `f = (p₁*f₁, p₂*f₂)`, and `a₁, a₂ ∈ L`, such that `sᵢ = aᵢ · 1⊗dfᵢ`
are nonzero elements of `⋀ω_{𝒢ᵢ}`, `s = a₁a₂ · 1⊗df` is a nonzero element of `⋀ω_{𝒢P}`, and
`[⋀ω_{𝒢P} : 𝓞s] = [⋀ω₁ : 𝓞s₁]·[⋀ω₂ : 𝓞s₂]`. Why true (STANDARD): `ω_{𝒢P} = p₁*ω₁ ⊕ p₂*ω₂` and
`𝔪_ξ/𝔪_ξ² = p₁*C₁ ⊕ p₂*C₂` for a product of smooth group schemes (EGA IV 17.2.3, UNVERIFIED
locator), so `⋀^{g₁+g₂}` is the tensor product of the two lines; for invertible `𝓞_L`-modules
indices multiply (norms of ideals). Unproved (stalks and differentials of fibre products are
not in Mathlib). -/
def ProductHodgeLattice : Prop :=
  ∀ (K : Type) [Field K] (A B C : AbVar K) (L : Type) [Field L] [NumberField L] [Algebra K L]
    (𝒢P : GroupModel C L) (g₁ g₂ : ℕ) (M₁ : MetrizedModel A L g₁) (M₂ : MetrizedModel B L g₂)
    (e : 𝒢P.G ≅ M₁.model.G ⊗ M₂.model.G) (hfst : IsMonHom (e.hom ≫ fst _ _))
    (hsnd : IsMonHom (e.hom ≫ snd _ _)),
    Module.finrank L (𝒢P.hodgeSpace (g₁ + g₂)) = 1 ∧
    ∃ (f₁ : Fin g₁ → IsLocalRing.maximalIdeal M₁.model.genStalk)
      (f₂ : Fin g₂ → IsLocalRing.maximalIdeal M₂.model.genStalk)
      (f : Fin (g₁ + g₂) → IsLocalRing.maximalIdeal 𝒢P.genStalk) (a₁ a₂ : L),
      (∀ i, (f (Fin.castAdd g₂ i) : 𝒢P.genStalk) = (pullGerm (e.hom ≫ fst _ _)).hom (f₁ i)) ∧
      (∀ j, (f (Fin.natAdd g₁ j) : 𝒢P.genStalk) = (pullGerm (e.hom ≫ snd _ _)).hom (f₂ j)) ∧
      a₁ • M₁.model.wedge f₁ ∈ M₁.hodge.lattice ∧ a₁ • M₁.model.wedge f₁ ≠ 0 ∧
      a₂ • M₂.model.wedge f₂ ∈ M₂.hodge.lattice ∧ a₂ • M₂.model.wedge f₂ ≠ 0 ∧
      (a₁ * a₂) • 𝒢P.wedge f ∈ 𝒢P.detLattice (g₁ + g₂) ∧ (a₁ * a₂) • 𝒢P.wedge f ≠ 0 ∧
      secIndex (𝒢P.detLattice (g₁ + g₂)) ((a₁ * a₂) • 𝒢P.wedge f) =
        secIndex M₁.hodge.lattice (a₁ • M₁.model.wedge f₁) *
          secIndex M₂.hodge.lattice (a₂ • M₂.model.wedge f₂)

/-- **Glue (analysis: the Jacobian of the product uniformization is block diagonal).** If
`prodPts e Φ₁ Φ₂` is an analytic uniformization and `f = (p₁*f₁, p₂*f₂)`, then
`jacDet (prodPts e Φ₁ Φ₂) f = jacDet Φ₁ f₁ · jacDet Φ₂ f₂`. Why true: `p₁ ∘ prodPts = Φ₁ ∘ leftBlock`
(`prodPts_comp_fst`), so near `0` the germ `(p₁*f₁ᵢ) ∘ prodPts` is `f₁ᵢ ∘ Φ₁ ∘ leftBlock` (the
representatives agree on an open `V ∋ ξ` and `dom (prodPts) V` is open), whose derivative
vanishes on the last `g₂` coordinates; the matrix is block diagonal (`Matrix.det_fromBlocks_zero₂₁`
after `finSumFinEquiv`). Elementary, unproved (needs the `evalAt`/stalk compatibilities of
`JacDetMultilinear` and functoriality of `evalAt` along morphisms). -/
def ProductJacobian : Prop :=
  ∀ (K : Type) [Field K] (A B C : AbVar K) (L : Type) [Field L] [NumberField L] [Algebra K L]
    (𝒢P : GroupModel C L) (𝒢₁ : GroupModel A L) (𝒢₂ : GroupModel B L)
    (e : 𝒢P.G ≅ 𝒢₁.G ⊗ 𝒢₂.G) (hfst : IsMonHom (e.hom ≫ fst _ _))
    (hsnd : IsMonHom (e.hom ≫ snd _ _))
    (τ : L →+* ℂ) (g₁ g₂ : ℕ) (Λ₁ : Submodule ℤ (Fin g₁ → ℂ)) (Λ₂ : Submodule ℤ (Fin g₂ → ℂ))
    (Φ₁ : (Fin g₁ → ℂ) → 𝒢₁.Pts τ) (Φ₂ : (Fin g₂ → ℂ) → 𝒢₂.Pts τ),
    𝒢₁.IsAnalyticUniformization τ Λ₁ Φ₁ → 𝒢₂.IsAnalyticUniformization τ Λ₂ Φ₂ →
    𝒢P.IsAnalyticUniformization τ (prodLattice Λ₁ Λ₂) (prodPts e Φ₁ Φ₂) →
    ∀ (f₁ : Fin g₁ → IsLocalRing.maximalIdeal 𝒢₁.genStalk)
      (f₂ : Fin g₂ → IsLocalRing.maximalIdeal 𝒢₂.genStalk)
      (f : Fin (g₁ + g₂) → IsLocalRing.maximalIdeal 𝒢P.genStalk),
      (∀ i, (f (Fin.castAdd g₂ i) : 𝒢P.genStalk) = (pullGerm (e.hom ≫ fst _ _)).hom (f₁ i)) →
      (∀ j, (f (Fin.natAdd g₁ j) : 𝒢P.genStalk) = (pullGerm (e.hom ≫ snd _ _)).hom (f₂ j)) →
      𝒢P.jacDet (prodPts e Φ₁ Φ₂) f = 𝒢₁.jacDet Φ₁ f₁ * 𝒢₂.jacDet Φ₂ f₂

end ZInQ.Metrization


/-! ## metrization: `ProductJacobian`, proved (block-diagonal Jacobian of `prodPts`) -/

namespace ZInQ.Metrization

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open NumberField DefFaltings Topology

section ProdJac

variable {K : Type} [Field K] {A B C : AbVar K} {L : Type} [Field L] [NumberField L]
  [Algebra K L]

/-- Pull-back of a germ is the germ of the pulled-back section. -/
theorem pullGerm_germ {𝒢 : GroupModel C L} {ℋ : GroupModel A L} (φ : 𝒢.G ⟶ ℋ.G) [IsMonHom φ]
    (U : ℋ.G.left.Opens) (m : ℋ.genericUnit ∈ U) (s : Γ(ℋ.G.left, U)) :
    (pullGerm φ).hom (ℋ.G.left.presheaf.germ U ℋ.genericUnit m s) =
      𝒢.G.left.presheaf.germ (φ.left ⁻¹ᵁ U) 𝒢.genericUnit
        (by show φ.left 𝒢.genericUnit ∈ U; rw [map_genericUnit_of_isMonHom φ]; exact m)
        (φ.left.app U s) := by
  unfold pullGerm
  rw [ConcreteCategory.comp_apply, TopCat.Presheaf.germ_stalkSpecializes_apply,
    Scheme.Hom.germ_stalkMap_apply]

/-- `evalAt` along a morphism of models. -/
theorem evalAt_comp {𝒢 : GroupModel C L} {ℋ : GroupModel A L} (φ : 𝒢.G ⟶ ℋ.G) {τ : L →+* ℂ}
    (p : 𝒢.Pts τ) (U : ℋ.G.left.Opens) (s : Γ(ℋ.G.left, U))
    (hp : ⊤ ≤ p.left ⁻¹ᵁ (φ.left ⁻¹ᵁ U)) :
    𝒢.evalAt p (φ.left ⁻¹ᵁ U) (φ.left.app U s) = ℋ.evalAt (p ≫ φ) U s := by
  have hp' : ⊤ ≤ (p ≫ φ).left ⁻¹ᵁ U := hp
  unfold GroupModel.evalAt
  rw [dif_pos hp, dif_pos hp']
  rw [show (p ≫ φ).left.appLE U ⊤ hp' = φ.left.app U ≫ p.left.appLE (φ.left ⁻¹ᵁ U) ⊤ hp from
    Scheme.Hom.comp_appLE p.left φ.left U ⊤ hp']
  rfl

variable {𝒢P : GroupModel C L} {𝒢₁ : GroupModel A L} {𝒢₂ : GroupModel B L}
  (e : 𝒢P.G ≅ 𝒢₁.G ⊗ 𝒢₂.G) [IsMonHom (e.hom ≫ fst _ _)] [IsMonHom (e.hom ≫ snd _ _)]
  {τ : L →+* ℂ} {g₁ g₂ : ℕ} {Λ₁ : Submodule ℤ (Fin g₁ → ℂ)} {Λ₂ : Submodule ℤ (Fin g₂ → ℂ)}
  {Φ₁ : (Fin g₁ → ℂ) → 𝒢₁.Pts τ} {Φ₂ : (Fin g₂ → ℂ) → 𝒢₂.Pts τ}

theorem germAlong_pull_fst_eventuallyEq (hΦ₁ : 𝒢₁.IsAnalyticUniformization τ Λ₁ Φ₁)
    (hΦP : 𝒢P.IsAnalyticUniformization τ (prodLattice Λ₁ Λ₂) (prodPts e Φ₁ Φ₂))
    (t : 𝒢₁.genStalk) :
    𝒢P.germAlong (prodPts e Φ₁ Φ₂) ((pullGerm (e.hom ≫ fst _ _)).hom t) =ᶠ[𝓝 0]
      fun z => 𝒢₁.germAlong Φ₁ t (leftBlock g₁ g₂ z) := by
  obtain ⟨U, m, s, rfl⟩ := 𝒢₁.exists_rep t
  rw [pullGerm_germ]
  have ht : Filter.Tendsto (leftBlock g₁ g₂) (𝓝 0) (𝓝 0) :=
    (leftBlock g₁ g₂).continuous_of_finiteDimensional.tendsto' 0 0 (map_zero _)
  filter_upwards [germAlong_eventuallyEq 𝒢P hΦP _ _ _,
    (germAlong_eventuallyEq 𝒢₁ hΦ₁ U m s).comp_tendsto ht,
    (hΦP.2.2.2.1 _).mem_nhds (zero_mem_dom 𝒢P hΦP ((e.hom ≫ fst _ _).left ⁻¹ᵁ U)
      (by show (e.hom ≫ fst _ _).left 𝒢P.genericUnit ∈ U
          rw [map_genericUnit_of_isMonHom]; exact m))] with z h1 h2 hz
  have h2' : 𝒢₁.germAlong Φ₁ (𝒢₁.G.left.presheaf.germ U 𝒢₁.genericUnit m s) (leftBlock g₁ g₂ z) =
      𝒢₁.evalAt (Φ₁ (leftBlock g₁ g₂ z)) U s := h2
  rw [h1, h2', evalAt_comp _ _ _ _ hz, prodPts_comp_fst]

theorem germAlong_pull_snd_eventuallyEq (hΦ₂ : 𝒢₂.IsAnalyticUniformization τ Λ₂ Φ₂)
    (hΦP : 𝒢P.IsAnalyticUniformization τ (prodLattice Λ₁ Λ₂) (prodPts e Φ₁ Φ₂))
    (t : 𝒢₂.genStalk) :
    𝒢P.germAlong (prodPts e Φ₁ Φ₂) ((pullGerm (e.hom ≫ snd _ _)).hom t) =ᶠ[𝓝 0]
      fun z => 𝒢₂.germAlong Φ₂ t (rightBlock g₁ g₂ z) := by
  obtain ⟨U, m, s, rfl⟩ := 𝒢₂.exists_rep t
  rw [pullGerm_germ]
  have ht : Filter.Tendsto (rightBlock g₁ g₂) (𝓝 0) (𝓝 0) :=
    (rightBlock g₁ g₂).continuous_of_finiteDimensional.tendsto' 0 0 (map_zero _)
  filter_upwards [germAlong_eventuallyEq 𝒢P hΦP _ _ _,
    (germAlong_eventuallyEq 𝒢₂ hΦ₂ U m s).comp_tendsto ht,
    (hΦP.2.2.2.1 _).mem_nhds (zero_mem_dom 𝒢P hΦP ((e.hom ≫ snd _ _).left ⁻¹ᵁ U)
      (by show (e.hom ≫ snd _ _).left 𝒢P.genericUnit ∈ U
          rw [map_genericUnit_of_isMonHom]; exact m))] with z h1 h2 hz
  have h2' : 𝒢₂.germAlong Φ₂ (𝒢₂.G.left.presheaf.germ U 𝒢₂.genericUnit m s) (rightBlock g₁ g₂ z) =
      𝒢₂.evalAt (Φ₂ (rightBlock g₁ g₂ z)) U s := h2
  rw [h1, h2', evalAt_comp _ _ _ _ hz, prodPts_comp_snd]

/-- Derivative of `F ∘ ℓ` for a linear `ℓ` on `ℂ^{g₁+g₂}` (chain rule). -/
theorem fderiv_comp_linear {n : ℕ} (ℓ : (Fin (g₁ + g₂) → ℂ) →ₗ[ℂ] (Fin n → ℂ))
    (F : (Fin n → ℂ) → ℂ) (hF : DifferentiableAt ℂ F 0) (w : Fin (g₁ + g₂) → ℂ) :
    fderiv ℂ (fun z => F (ℓ z)) 0 w = fderiv ℂ F 0 (ℓ w) := by
  let ℓc := LinearMap.toContinuousLinearMap ℓ
  have hfun : (fun z => F (ℓ z)) = F ∘ ℓc := by
    funext z; simp [ℓc]
  have hF' : DifferentiableAt ℂ F (ℓc 0) := by rw [map_zero]; exact hF
  rw [hfun, fderiv_comp _ hF' ℓc.differentiableAt, ContinuousLinearMap.fderiv, map_zero]
  simp [ℓc]

end ProdJac

/-- **`ProductJacobian`, proved.** -/
theorem productJacobian : ProductJacobian := by
  intro K _ A B C L _ _ _ 𝒢P 𝒢₁ 𝒢₂ e hfst hsnd τ g₁ g₂ Λ₁ Λ₂ Φ₁ Φ₂ hΦ₁ hΦ₂ hΦP f₁ f₂ f hf1 hf2
  have hl : ∀ (i : Fin g₁) (w : Fin (g₁ + g₂) → ℂ),
      fderiv ℂ (𝒢P.germAlong (prodPts e Φ₁ Φ₂) (f (Fin.castAdd g₂ i) : 𝒢P.genStalk)) 0 w =
        fderiv ℂ (𝒢₁.germAlong Φ₁ (f₁ i : 𝒢₁.genStalk)) 0 (leftBlock g₁ g₂ w) := by
    intro i w
    rw [hf1 i, (germAlong_pull_fst_eventuallyEq e hΦ₁ hΦP _).fderiv_eq]
    exact fderiv_comp_linear (leftBlock g₁ g₂) _ (germAlong_differentiableAt 𝒢₁ hΦ₁ _) w
  have hr : ∀ (j : Fin g₂) (w : Fin (g₁ + g₂) → ℂ),
      fderiv ℂ (𝒢P.germAlong (prodPts e Φ₁ Φ₂) (f (Fin.natAdd g₁ j) : 𝒢P.genStalk)) 0 w =
        fderiv ℂ (𝒢₂.germAlong Φ₂ (f₂ j : 𝒢₂.genStalk)) 0 (rightBlock g₁ g₂ w) := by
    intro j w
    rw [hf2 j, (germAlong_pull_snd_eventuallyEq e hΦ₂ hΦP _).fderiv_eq]
    exact fderiv_comp_linear (rightBlock g₁ g₂) _ (germAlong_differentiableAt 𝒢₂ hΦ₂ _) w
  have hL1 : ∀ j : Fin g₁, leftBlock g₁ g₂ (Pi.single (Fin.castAdd g₂ j) 1) = Pi.single j 1 := by
    intro j; funext k; simp [Pi.single_apply]
  have hL2 : ∀ j : Fin g₂, leftBlock g₁ g₂ (Pi.single (Fin.natAdd g₁ j) 1) = 0 := by
    intro j; funext k; simp [Pi.single_apply, Fin.ext_iff]; omega
  have hR1 : ∀ j : Fin g₁, rightBlock g₁ g₂ (Pi.single (Fin.castAdd g₂ j) 1) = 0 := by
    intro j; funext k; simp [Pi.single_apply, Fin.ext_iff]; omega
  have hR2 : ∀ j : Fin g₂, rightBlock g₁ g₂ (Pi.single (Fin.natAdd g₁ j) 1) = Pi.single j 1 := by
    intro j; funext k; simp [Pi.single_apply]
  let J₁ : Matrix (Fin g₁) (Fin g₁) ℂ :=
    Matrix.of fun i j => fderiv ℂ (𝒢₁.germAlong Φ₁ (f₁ i : 𝒢₁.genStalk)) 0 (Pi.single j 1)
  let J₂ : Matrix (Fin g₂) (Fin g₂) ℂ :=
    Matrix.of fun i j => fderiv ℂ (𝒢₂.germAlong Φ₂ (f₂ i : 𝒢₂.genStalk)) 0 (Pi.single j 1)
  have hblock : Matrix.reindex finSumFinEquiv.symm finSumFinEquiv.symm
      (Matrix.of fun i j : Fin (g₁ + g₂) =>
        fderiv ℂ (𝒢P.germAlong (prodPts e Φ₁ Φ₂) (f i : 𝒢P.genStalk)) 0 (Pi.single j 1)) =
      Matrix.fromBlocks J₁ 0 0 J₂ := by
    ext (i | i) (j | j)
    · simp only [Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.symm_symm,
        finSumFinEquiv_apply_left, Matrix.of_apply, Matrix.fromBlocks_apply₁₁, J₁]
      rw [hl, hL1 j]
    · simp only [Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.symm_symm,
        finSumFinEquiv_apply_left, finSumFinEquiv_apply_right, Matrix.of_apply,
        Matrix.fromBlocks_apply₁₂, Matrix.zero_apply]
      rw [hl, hL2, map_zero]
    · simp only [Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.symm_symm,
        finSumFinEquiv_apply_left, finSumFinEquiv_apply_right, Matrix.of_apply,
        Matrix.fromBlocks_apply₂₁, Matrix.zero_apply]
      rw [hr, hR1, map_zero]
    · simp only [Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.symm_symm,
        finSumFinEquiv_apply_right, Matrix.of_apply, Matrix.fromBlocks_apply₂₂, J₂]
      rw [hr, hR2]
  unfold GroupModel.jacDet
  rw [← Matrix.det_reindex_self finSumFinEquiv.symm, hblock, Matrix.det_fromBlocks_zero₂₁]

end ZInQ.Metrization


/-! ## metrization: `ProductUniformizationAnalytic` reduced to a statement about complex points

`ProductLocalStructure` (pure algebraic geometry, no analysis): near a complex point of
`𝒢₁ × 𝒢₂`, membership in a Zariski open `U` and a regular function on `U` are given, on
`V₁(ℂ) × V₂(ℂ)`, by sums of products of regular functions on opens `V₁ ⊂ 𝒢₁`, `V₂ ⊂ 𝒢₂`. The
analytic consequences (openness of `dom`, holomorphy) are proved. -/

namespace ZInQ.Metrization

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open NumberField DefFaltings Topology

/-- **Glue (local product structure of `𝒢₁ ×_{𝓞_L} 𝒢₂` at complex points).** For
`e : 𝒢P ≅ 𝒢₁ × 𝒢₂`, an open `U ⊂ 𝒢P`, `s ∈ Γ(U)` and complex points `p₁`, `p₂` with
`e⁻¹(p₁, p₂) ∈ U(ℂ)`, there are opens `V₁ ∋ p₁`, `V₂ ∋ p₂` and regular functions
`a_k, c_k` on `V₁`, `b_k, d_k` on `V₂` such that `H = Σ c_k ⊗ d_k` does not vanish at `(p₁, p₂)`,
and at every `(p₁', p₂') ∈ V₁(ℂ) × V₂(ℂ)` with `H(p₁', p₂') ≠ 0`: `e⁻¹(p₁', p₂') ∈ U(ℂ)` and
`s(e⁻¹(p₁', p₂')) · H(p₁', p₂') = Σ a_k(p₁') b_k(p₂')`. Why true (STANDARD): take affine
`V₁ = Spec R₁`, `V₂ = Spec R₂` (over the affine `Spec 𝓞_L`), so `V₁ ×_{𝓞_L} V₂ = Spec(R₁ ⊗ R₂)`
is open in the product; choose a basic open `D(h)` of it with `(p₁, p₂) ∈ D(h) ⊆ e(U)`,
`h ∈ R₁ ⊗ R₂`; on `D(h)`, `s = a/h^m` with `a ∈ R₁ ⊗ R₂`; take `H = h^m` and expand `H` and `a`
as sums of pure tensors; a pure tensor `c ⊗ d` evaluates at `(p₁', p₂')` to `c(p₁') d(p₂')`.
Unproved (needs Mathlib's affine opens of pullbacks and sections on basic opens). -/
def ProductLocalStructure : Prop :=
  ∀ (K : Type) [Field K] (A B C : AbVar K) (L : Type) [Field L] [NumberField L] [Algebra K L]
    (𝒢P : GroupModel C L) (𝒢₁ : GroupModel A L) (𝒢₂ : GroupModel B L)
    (e : 𝒢P.G ≅ 𝒢₁.G ⊗ 𝒢₂.G) (τ : L →+* ℂ) (U : 𝒢P.G.left.Opens) (s : Γ(𝒢P.G.left, U))
    (p₁ : 𝒢₁.Pts τ) (p₂ : 𝒢₂.Pts τ), ⊤ ≤ (lift p₁ p₂ ≫ e.inv).left ⁻¹ᵁ U →
    ∃ (V₁ : 𝒢₁.G.left.Opens) (V₂ : 𝒢₂.G.left.Opens) (n : ℕ)
      (a c : Fin n → Γ(𝒢₁.G.left, V₁)) (b d : Fin n → Γ(𝒢₂.G.left, V₂)),
      ⊤ ≤ p₁.left ⁻¹ᵁ V₁ ∧ ⊤ ≤ p₂.left ⁻¹ᵁ V₂ ∧
      (∑ k, 𝒢₁.evalAt p₁ V₁ (c k) * 𝒢₂.evalAt p₂ V₂ (d k)) ≠ 0 ∧
      ∀ (p₁' : 𝒢₁.Pts τ) (p₂' : 𝒢₂.Pts τ), ⊤ ≤ p₁'.left ⁻¹ᵁ V₁ → ⊤ ≤ p₂'.left ⁻¹ᵁ V₂ →
        (∑ k, 𝒢₁.evalAt p₁' V₁ (c k) * 𝒢₂.evalAt p₂' V₂ (d k)) ≠ 0 →
        ⊤ ≤ (lift p₁' p₂' ≫ e.inv).left ⁻¹ᵁ U ∧
        𝒢P.evalAt (lift p₁' p₂' ≫ e.inv) U s *
            (∑ k, 𝒢₁.evalAt p₁' V₁ (c k) * 𝒢₂.evalAt p₂' V₂ (d k)) =
          ∑ k, 𝒢₁.evalAt p₁' V₁ (a k) * 𝒢₂.evalAt p₂' V₂ (b k)

section Local

variable {K : Type} [Field K] {A B C : AbVar K} {L : Type} [Field L] [NumberField L]
  [Algebra K L] {𝒢P : GroupModel C L} {𝒢₁ : GroupModel A L} {𝒢₂ : GroupModel B L}
  (e : 𝒢P.G ≅ 𝒢₁.G ⊗ 𝒢₂.G) {τ : L →+* ℂ} {g₁ g₂ : ℕ} {Λ₁ : Submodule ℤ (Fin g₁ → ℂ)}
  {Λ₂ : Submodule ℤ (Fin g₂ → ℂ)} {Φ₁ : (Fin g₁ → ℂ) → 𝒢₁.Pts τ} {Φ₂ : (Fin g₂ → ℂ) → 𝒢₂.Pts τ}

theorem leftBlock_differentiable : Differentiable ℂ (leftBlock g₁ g₂) := by
  have h := (LinearMap.toContinuousLinearMap (leftBlock g₁ g₂)).differentiable
  simpa using h

theorem rightBlock_differentiable : Differentiable ℂ (rightBlock g₁ g₂) := by
  have h := (LinearMap.toContinuousLinearMap (rightBlock g₁ g₂)).differentiable
  simpa using h

/-- The local statement: every point of `dom (prodPts) U` has an open neighbourhood inside
`dom (prodPts) U` on which `z ↦ s(prodPts z)` is holomorphic. -/
theorem prodPts_local (hLS : ProductLocalStructure) (h₁ : 𝒢₁.IsAnalyticUniformization τ Λ₁ Φ₁)
    (h₂ : 𝒢₂.IsAnalyticUniformization τ Λ₂ Φ₂) (U : 𝒢P.G.left.Opens) (s : Γ(𝒢P.G.left, U))
    (z₀ : Fin (g₁ + g₂) → ℂ) (hz₀ : z₀ ∈ 𝒢P.dom (prodPts e Φ₁ Φ₂) U) :
    ∃ N : Set (Fin (g₁ + g₂) → ℂ), IsOpen N ∧ z₀ ∈ N ∧ N ⊆ 𝒢P.dom (prodPts e Φ₁ Φ₂) U ∧
      DifferentiableOn ℂ (fun z => 𝒢P.evalAt (prodPts e Φ₁ Φ₂ z) U s) N := by
  obtain ⟨V₁, V₂, n, a, c, b, d, hV₁, hV₂, hne, hall⟩ :=
    hLS K A B C L 𝒢P 𝒢₁ 𝒢₂ e τ U s (Φ₁ (leftBlock g₁ g₂ z₀)) (Φ₂ (rightBlock g₁ g₂ z₀)) hz₀
  let O : Set (Fin (g₁ + g₂) → ℂ) :=
    leftBlock g₁ g₂ ⁻¹' 𝒢₁.dom Φ₁ V₁ ∩ rightBlock g₁ g₂ ⁻¹' 𝒢₂.dom Φ₂ V₂
  have hO : IsOpen O :=
    ((h₁.2.2.2.1 V₁).preimage (leftBlock_differentiable).continuous).inter
      ((h₂.2.2.2.1 V₂).preimage (rightBlock_differentiable).continuous)
  have hd1 : ∀ σ : Γ(𝒢₁.G.left, V₁),
      DifferentiableOn ℂ (fun z => 𝒢₁.evalAt (Φ₁ (leftBlock g₁ g₂ z)) V₁ σ) O := fun σ =>
    (h₁.2.2.2.2 V₁ σ).comp (leftBlock_differentiable).differentiableOn (fun z hz => hz.1)
  have hd2 : ∀ σ : Γ(𝒢₂.G.left, V₂),
      DifferentiableOn ℂ (fun z => 𝒢₂.evalAt (Φ₂ (rightBlock g₁ g₂ z)) V₂ σ) O := fun σ =>
    (h₂.2.2.2.2 V₂ σ).comp (rightBlock_differentiable).differentiableOn (fun z hz => hz.2)
  let H : (Fin (g₁ + g₂) → ℂ) → ℂ := fun z =>
    ∑ k, 𝒢₁.evalAt (Φ₁ (leftBlock g₁ g₂ z)) V₁ (c k) * 𝒢₂.evalAt (Φ₂ (rightBlock g₁ g₂ z)) V₂ (d k)
  let Afun : (Fin (g₁ + g₂) → ℂ) → ℂ := fun z =>
    ∑ k, 𝒢₁.evalAt (Φ₁ (leftBlock g₁ g₂ z)) V₁ (a k) * 𝒢₂.evalAt (Φ₂ (rightBlock g₁ g₂ z)) V₂ (b k)
  have hH : DifferentiableOn ℂ H O := by
    have := DifferentiableOn.sum (u := Finset.univ)
      (A := fun k z => 𝒢₁.evalAt (Φ₁ (leftBlock g₁ g₂ z)) V₁ (c k) *
        𝒢₂.evalAt (Φ₂ (rightBlock g₁ g₂ z)) V₂ (d k))
      (fun k _ => (hd1 (c k)).mul (hd2 (d k)))
    convert this using 1
    funext z
    simp [H, Finset.sum_apply]
  have hA : DifferentiableOn ℂ Afun O := by
    have := DifferentiableOn.sum (u := Finset.univ)
      (A := fun k z => 𝒢₁.evalAt (Φ₁ (leftBlock g₁ g₂ z)) V₁ (a k) *
        𝒢₂.evalAt (Φ₂ (rightBlock g₁ g₂ z)) V₂ (b k))
      (fun k _ => (hd1 (a k)).mul (hd2 (b k)))
    convert this using 1
    funext z
    simp [Afun, Finset.sum_apply]
  let N := O ∩ H ⁻¹' {0}ᶜ
  have hN : IsOpen N := hH.continuousOn.isOpen_inter_preimage hO isOpen_compl_singleton
  have hsub : ∀ z ∈ N, z ∈ 𝒢P.dom (prodPts e Φ₁ Φ₂) U ∧
      𝒢P.evalAt (prodPts e Φ₁ Φ₂ z) U s = Afun z / H z := by
    intro z hz
    obtain ⟨hmem, heq⟩ := hall _ _ hz.1.1 hz.1.2 hz.2
    refine ⟨hmem, ?_⟩
    rw [eq_div_iff hz.2]
    exact heq
  refine ⟨N, hN, ⟨⟨hV₁, hV₂⟩, hne⟩, fun z hz => (hsub z hz).1, ?_⟩
  have hdiv : DifferentiableOn ℂ (fun z => Afun z * (H z)⁻¹) N :=
    (hA.mono Set.inter_subset_left).mul
      ((hH.mono Set.inter_subset_left).inv (fun z hz => hz.2))
  refine hdiv.congr fun z hz => ?_
  rw [(hsub z hz).2, div_eq_mul_inv]

end Local

/-- **`ProductUniformizationAnalytic` from `ProductLocalStructure` (proved).** -/
theorem productUniformizationAnalytic_of (hLS : ProductLocalStructure) :
    ProductUniformizationAnalytic := by
  intro K _ A B C L _ _ _ 𝒢P 𝒢₁ 𝒢₂ e hfst hsnd τ g₁ g₂ Λ₁ Λ₂ Φ₁ Φ₂ h₁ h₂
  refine ⟨fun U => ?_, fun U s => ?_⟩
  · rw [isOpen_iff_forall_mem_open]
    intro z₀ hz₀
    obtain ⟨N, hN, hz₀N, hsub, -⟩ := prodPts_local e hLS h₁ h₂ U 0 z₀ hz₀
    exact ⟨N, hsub, hN, hz₀N⟩
  · intro z₀ hz₀
    obtain ⟨N, hN, hz₀N, -, hd⟩ := prodPts_local e hLS h₁ h₂ U s z₀ hz₀
    exact ((hd z₀ hz₀N).differentiableAt (hN.mem_nhds hz₀N)).differentiableWithinAt

end ZInQ.Metrization


/-! ## §3c. metrization's glue Prop `JacDetNondegenerate` (verbatim, `part_exists.lean` lines
45-57) -/

namespace ZInQ.Metrization

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open NumberField DefFaltings

/-- **Glue (local parameters are analytic coordinates).** For `g = dim A` and an analytic
uniformization `Φ` of `𝒢(ℂ)_τ` with a full lattice as kernel, some `f₁, …, f_g ∈ 𝔪_ξ` have
`jacDet Φ f ≠ 0`. Why true (STANDARD): `𝒪_{𝒢,ξ} = 𝒪_{A_L,0}` is regular of dimension `g`
(smoothness); a regular system of parameters `f₁, …, f_g` gives holomorphic coordinates of the
complex manifold `A_τ(ℂ)` at `0` (Serre, GAGA, or the holomorphic implicit function theorem),
and `Φ` is a local biholomorphism at `0`, so `(f_i ∘ Φ)` has invertible Jacobian at `0`.
Unproved (needs the analytic structure of `A_τ(ℂ)`). -/
def JacDetNondegenerate : Prop :=
  ∀ (K : Type) [Field K] (A : AbVar K) (L : Type) [Field L] [NumberField L] [Algebra K L]
    (𝒢 : GroupModel A L) (τ : L →+* ℂ) (g : ℕ), A.dim = g →
    ∀ (Λ : Submodule ℤ (Fin g → ℂ)) [DiscreteTopology Λ] (Φ : (Fin g → ℂ) → 𝒢.Pts τ),
      IsZLattice ℝ Λ → 𝒢.IsAnalyticUniformization τ Λ Φ →
      ∃ f : Fin g → IsLocalRing.maximalIdeal 𝒢.genStalk, 𝒢.jacDet Φ f ≠ 0

end ZInQ.Metrization

namespace ZInQ.ProductUnif

/-! ## §4. S-alg (`ProductMetrizationOfProductUnif`): reduction to three smaller glue Props

`productMetrizationOfProductUnif_of : HodgeLatticeTheorem → ProductUnifDims → JacDetDescends →
ProductHodgeAdd → ProductMetrizationOfProductUnif` (proved). `HodgeLatticeTheorem` is the kernel's
glue Prop (`ZInQKernel/HDecomp/Faltings/Models.lean`); the other three are new glue. -/

section SAlg

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open NumberField DefFaltings ZInQ.ProductHeight

/-- **Glue S-alg-1 (dimensions and nonsingularity in product form).** Let `e : MP.model ≅ 𝒢₁ ⊗ 𝒢₂`
have homomorphic components, and at `τ` let the metrization `MP` (dimension `g`) be in product
form: period lattice `Λ₁ × Λ₂` and coefficient map computed by `Φ₁ × Φ₂`, for full-lattice
analytic uniformizations `Φᵢ : ℂ^{gᵢ} → 𝒢ᵢ(ℂ)_τ`, `g₁ + g₂ = g`. Then `g₁ = dim A`, `g₂ = dim B`,
and both factor Jacobians are nonsingular on some `gᵢ`-tuple of germs.

Why true (STANDARD; algebra and calculus, no AN3). Write `nᵢ` for the `L`-dimension of the
cotangent space `𝔪/𝔪²` of `𝒢ᵢ` at the generic unit. `genStalk` is the local ring of `A_L` at its
origin (regular, smooth generic fibre), so `n₁ = dim A_L = dim A` (dimension of a finite-type
scheme over a field is invariant under field extension; EGA IV 4.1.4, UNVERIFIED locator); `dim A`
is finite since `A.X.left` is nonempty. Since `cot` is an `L`-space and `L` a localization of
`𝓞_L`, `finrank_L (hodgeSpace g) = C(n, g)`. Via `e` (whose components preserve units),
`𝔪_P/𝔪_P² = 𝔪₁/𝔪₁² ⊕ 𝔪₂/𝔪₂²`, so `MP.hodge.finrank_eq_one` gives `g ∈ {0, n₁ + n₂}`.
If `g = 0`, then `g₁ = g₂ = 0`, the `Φᵢ : ℂ⁰ → 𝒢ᵢ(ℂ)_τ` are onto, so `A_τ(ℂ)`, `B_τ(ℂ)` are single
points and `dim A = dim B = 0` (a positive-dimensional variety over `ℂ` has infinitely many
points); `Fin 0` Jacobians are `1`. Otherwise: the wedges `wedge f` span `hodgeSpace` over `L`, so
`MP.hodge.coeff_ne_zero` and the coefficient formula give `f` with `jacDet (Φ₁ × Φ₂) f ≠ 0`. The map
`prodUnif ∘ cast` satisfies the analytic clauses (product-height's `ProductUnifAnalytic`,
metrization's `ProductUniformizationAnalytic`: true, from basic opens `D(h)` of affine products),
so the derivative at `0` of a germ along it depends only on its class in `cot₁ ⊕ cot₂` and the
Jacobian rows are `(D₁x, 0)`, `(0, D₂y)`; nonsingularity forces `g₁ ≤ n₁`, `g₂ ≤ n₂`, hence
equality, and nonsingular diagonal blocks. Unproved. (Reviewed: true for all instances, including
`g = 0` and an `e` incompatible with any generic-fibre product structure.) -/
def ProductUnifDims : Prop :=
  ∀ (K : Type) [Field K] (A B C : AbVar K) (L : Type) [Field L] [NumberField L] [Algebra K L]
    (𝒢₁ : GroupModel A L) (𝒢₂ : GroupModel B L) (g : ℕ) (MP : MetrizedModel C L g)
    (e : MP.model.G ≅ 𝒢₁.G ⊗ 𝒢₂.G) [IsMonHom (e.hom ≫ fst _ _)] [IsMonHom (e.hom ≫ snd _ _)]
    (τ : L →+* ℂ) (g₁ g₂ : ℕ) (hg : g₁ + g₂ = g) (Λ₁ : Submodule ℤ (Fin g₁ → ℂ))
    (Λ₂ : Submodule ℤ (Fin g₂ → ℂ)) (Φ₁ : (Fin g₁ → ℂ) → 𝒢₁.Pts τ)
    (Φ₂ : (Fin g₂ → ℂ) → 𝒢₂.Pts τ),
    (∃ _ : DiscreteTopology Λ₁, IsZLattice ℝ Λ₁) →
    (∃ _ : DiscreteTopology Λ₂, IsZLattice ℝ Λ₂) →
    𝒢₁.IsAnalyticUniformization τ Λ₁ Φ₁ → 𝒢₂.IsAnalyticUniformization τ Λ₂ Φ₂ →
    (∀ z, z ∈ MP.hodge.periods τ ↔ (fun i => z (Fin.cast hg i)) ∈ prodLattice Λ₁ Λ₂) →
    (∀ f, MP.hodge.coeff τ (MP.model.wedge f) =
      MP.model.jacDet (fun z => prodUnif e Φ₁ Φ₂ (fun i => z (Fin.cast hg i))) f) →
    A.dim = g₁ ∧ B.dim = g₂ ∧ (∃ f₁, 𝒢₁.jacDet Φ₁ f₁ ≠ 0) ∧ (∃ f₂, 𝒢₂.jacDet Φ₂ f₂ ≠ 0)

/-- **Glue S-alg-2 (the Jacobian determinant descends to the Hodge line).** For a group model `𝒢`
of `A_L` with `dim A = d` and an analytic uniformization `Φ : ℂ^d → 𝒢(ℂ)_τ`, the map
`f ↦ jacDet Φ f = det(∂(fᵢ ∘ Φ)/∂zⱼ(0))` on `d`-tuples of germs in `𝔪_ξ` is the restriction to
wedges of a `τ`-semilinear map `hodgeSpace d → ℂ`.

Why true (STANDARD; calculus). The derivative at `0` of `germAlong Φ f` does not depend on the
representative (`dom Φ U` is open and contains `0`), is additive in `f`, satisfies
`d(a f) = τ(a) df` for `a ∈ 𝓞_L` and `d(fh) = f(1) dh + h(1) df = 0` for `f, h ∈ 𝔪_ξ` (clause 5,
Leibniz). So `df ↦ d(f ∘ Φ)(0)` is a `τ`-semilinear map on `𝔪/𝔪²`; the determinant is
alternating multilinear, so it factors through `⋀^d_{𝓞_L}`, then through `L ⊗_{𝓞_L} ⋀^d`
(`l ⊗ ω ↦ τ(l) c(ω)`). Unproved. -/
def JacDetDescends : Prop :=
  ∀ (K : Type) [Field K] (A : AbVar K) (L : Type) [Field L] [NumberField L] [Algebra K L]
    (𝒢 : GroupModel A L) (d : ℕ), A.dim = d → ∀ (τ : L →+* ℂ) (Λ : Submodule ℤ (Fin d → ℂ))
    (Φ : (Fin d → ℂ) → 𝒢.Pts τ), 𝒢.IsAnalyticUniformization τ Λ Φ →
    ∃ c : 𝒢.hodgeSpace d →ₛₗ[τ] ℂ, ∀ f, c (𝒢.wedge f) = 𝒢.jacDet Φ f

/-- **Glue S-alg-3 (additivity of the height for a product-form metrization).** Let
`e : MP.model ≅ 𝒢₁ ⊗ 𝒢₂` have homomorphic components, `g₁ + g₂ = g`, and let `D₁`, `D₂` be Hodge
data of the factors with the genuine lattices `⋀^{gᵢ} ω_{𝒢ᵢ}`, such that at every `τ` there are
analytic uniformizations `Φᵢ` of the factors with kernels the periods of `Dᵢ`, computing the
coefficients of `Dᵢ`, while `MP` has periods `D₁.periods × D₂.periods` and coefficients computed
by `Φ₁ × Φ₂`. Then `h(D₁) + h(D₂) ≤ h(MP)`.

Why true (STANDARD; equality holds). First `gᵢ = dim`, as in `ProductUnifDims` (otherwise the
decomposition of `⋀^g` below fails). `ω_{MP} = ω₁ ⊕ ω₂` (unit of a product; this is a statement
about the conormal lattices `omega`, not only the generic cotangent spaces), so
`s = p₁*s₁ ∧ p₂*s₂ ∈ ⋀^g ω_{MP}` for any nonzero `sᵢ ∈ ⋀^{gᵢ} ω_{𝒢ᵢ}` (an invertible
`𝓞_L`-module, not necessarily free) and
`secIndex s = secIndex s₁ · secIndex s₂`; the Jacobian of `Φ₁ × Φ₂` on `p₁*f ∧ p₂*h` is block
diagonal, so the coefficients multiply; `covol(Λ₁ × Λ₂) = covol Λ₁ · covol Λ₂`
(`prodLattice_facts` of product-height, proved, plus a coordinate permutation `Fin.cast`); then
`modelHeight_add_of` (product-height, proved). Unproved as a whole. -/
def ProductHodgeAdd : Prop :=
  ∀ (K : Type) [Field K] (A B C : AbVar K) (L : Type) [Field L] [NumberField L] [Algebra K L]
    (𝒢₁ : GroupModel A L) (𝒢₂ : GroupModel B L) (g : ℕ) (MP : MetrizedModel C L g)
    (e : MP.model.G ≅ 𝒢₁.G ⊗ 𝒢₂.G) [IsMonHom (e.hom ≫ fst _ _)] [IsMonHom (e.hom ≫ snd _ _)]
    (g₁ g₂ : ℕ) (hg : g₁ + g₂ = g) (D₁ : HodgeData L g₁ (𝒢₁.hodgeSpace g₁))
    (D₂ : HodgeData L g₂ (𝒢₂.hodgeSpace g₂)),
    D₁.lattice = 𝒢₁.detLattice g₁ → D₂.lattice = 𝒢₂.detLattice g₂ →
    (∀ τ : L →+* ℂ, ∃ (Φ₁ : (Fin g₁ → ℂ) → 𝒢₁.Pts τ) (Φ₂ : (Fin g₂ → ℂ) → 𝒢₂.Pts τ),
      𝒢₁.IsAnalyticUniformization τ (D₁.periods τ) Φ₁ ∧
      𝒢₂.IsAnalyticUniformization τ (D₂.periods τ) Φ₂ ∧
      (∀ f, D₁.coeff τ (𝒢₁.wedge f) = 𝒢₁.jacDet Φ₁ f) ∧
      (∀ f, D₂.coeff τ (𝒢₂.wedge f) = 𝒢₂.jacDet Φ₂ f) ∧
      (∀ z, z ∈ MP.hodge.periods τ ↔
        (fun i => z (Fin.cast hg i)) ∈ prodLattice (D₁.periods τ) (D₂.periods τ)) ∧
      ∀ f, MP.hodge.coeff τ (MP.model.wedge f) =
        MP.model.jacDet (fun z => prodUnif e Φ₁ Φ₂ (fun i => z (Fin.cast hg i))) f) →
    D₁.modelHeight + D₂.modelHeight ≤ MP.hodge.modelHeight

theorem natCast_eq_of_dim {K : Type} [Field K] {A : AbVar K} {m n : ℕ} (hm : A.dim = m)
    (hn : A.dim = n) : m = n := by
  have h : ((m : ℕ∞) : WithBot ℕ∞) = ((n : ℕ∞) : WithBot ℕ∞) := hm.symm.trans hn
  exact_mod_cast WithBot.coe_injective h

/-- **S-alg from `HodgeLatticeTheorem`, `ProductUnifDims`, `JacDetDescends`, `ProductHodgeAdd`
(proved).** The factor metrizations are built here: dimension `dᵢ = dim` (constant in `τ` by
`ProductUnifDims`), lattice `⋀^{dᵢ} ω_{𝒢ᵢ}` (`HodgeLatticeTheorem`), periods `Λᵢ(τ)`, coefficient
maps from `JacDetDescends`, nonzero by the nonsingular factor Jacobians. -/
theorem productMetrizationOfProductUnif_of (hH : HodgeLatticeTheorem) (hD : ProductUnifDims)
    (hJ : JacDetDescends) (hP : ProductHodgeAdd) : ProductMetrizationOfProductUnif := by
  intro K _ A B C L _ _ _ 𝒢₁ 𝒢₂ g MP e _ _ hform
  obtain ⟨τ₀⟩ : Nonempty (L →+* ℂ) := inferInstance
  obtain ⟨d₁, d₂, hd, Λ₁₀, Λ₂₀, Φ₁₀, Φ₂₀, hl₁₀, hl₂₀, hu₁₀, hu₂₀, hper₀, hco₀⟩ := hform τ₀
  obtain ⟨hA, hB, -, -⟩ :=
    hD K A B C L 𝒢₁ 𝒢₂ g MP e τ₀ d₁ d₂ hd Λ₁₀ Λ₂₀ Φ₁₀ Φ₂₀ hl₁₀ hl₂₀ hu₁₀ hu₂₀ hper₀ hco₀
  have norm : ∀ τ : L →+* ℂ, ∃ (Λ₁ : Submodule ℤ (Fin d₁ → ℂ)) (Λ₂ : Submodule ℤ (Fin d₂ → ℂ))
      (Φ₁ : (Fin d₁ → ℂ) → 𝒢₁.Pts τ) (Φ₂ : (Fin d₂ → ℂ) → 𝒢₂.Pts τ),
      (∃ _ : DiscreteTopology Λ₁, IsZLattice ℝ Λ₁) ∧
      (∃ _ : DiscreteTopology Λ₂, IsZLattice ℝ Λ₂) ∧
      𝒢₁.IsAnalyticUniformization τ Λ₁ Φ₁ ∧ 𝒢₂.IsAnalyticUniformization τ Λ₂ Φ₂ ∧
      (∀ z, z ∈ MP.hodge.periods τ ↔ (fun i => z (Fin.cast hd i)) ∈ prodLattice Λ₁ Λ₂) ∧
      (∀ f, MP.hodge.coeff τ (MP.model.wedge f) =
        MP.model.jacDet (fun z => prodUnif e Φ₁ Φ₂ (fun i => z (Fin.cast hd i))) f) ∧
      (∃ f₁, 𝒢₁.jacDet Φ₁ f₁ ≠ 0) ∧ (∃ f₂, 𝒢₂.jacDet Φ₂ f₂ ≠ 0) := by
    intro τ
    obtain ⟨g₁, g₂, hg, Λ₁, Λ₂, Φ₁, Φ₂, hl₁, hl₂, hu₁, hu₂, hper, hco⟩ := hform τ
    obtain ⟨hA', hB', hn₁, hn₂⟩ :=
      hD K A B C L 𝒢₁ 𝒢₂ g MP e τ g₁ g₂ hg Λ₁ Λ₂ Φ₁ Φ₂ hl₁ hl₂ hu₁ hu₂ hper hco
    obtain rfl : g₁ = d₁ := natCast_eq_of_dim hA' hA
    obtain rfl : g₂ = d₂ := natCast_eq_of_dim hB' hB
    exact ⟨Λ₁, Λ₂, Φ₁, Φ₂, hl₁, hl₂, hu₁, hu₂, hper, hco, hn₁, hn₂⟩
  choose Λ₁ Λ₂ Φ₁ Φ₂ hl₁ hl₂ hu₁ hu₂ hper hco hn₁ hn₂ using norm
  obtain ⟨hfr₁, hlat₁⟩ := hH K A L 𝒢₁ d₁ hA
  obtain ⟨hfr₂, hlat₂⟩ := hH K B L 𝒢₂ d₂ hB
  choose c₁ hc₁ using fun τ => hJ K A L 𝒢₁ d₁ hA τ (Λ₁ τ) (Φ₁ τ) (hu₁ τ)
  choose c₂ hc₂ using fun τ => hJ K B L 𝒢₂ d₂ hB τ (Λ₂ τ) (Φ₂ τ) (hu₂ τ)
  let D₁ : HodgeData L d₁ (𝒢₁.hodgeSpace d₁) :=
    { lattice := 𝒢₁.detLattice d₁
      finrank_eq_one := hfr₁
      isLattice := hlat₁
      periods := Λ₁
      periods_discrete := fun τ => (hl₁ τ).fst
      periods_isZLattice := fun τ => (hl₁ τ).snd
      coeff := c₁
      coeff_ne_zero := fun τ h => by
        obtain ⟨f, hf⟩ := hn₁ τ
        apply hf
        rw [← hc₁ τ f, h]
        rfl }
  let D₂ : HodgeData L d₂ (𝒢₂.hodgeSpace d₂) :=
    { lattice := 𝒢₂.detLattice d₂
      finrank_eq_one := hfr₂
      isLattice := hlat₂
      periods := Λ₂
      periods_discrete := fun τ => (hl₂ τ).fst
      periods_isZLattice := fun τ => (hl₂ τ).snd
      coeff := c₂
      coeff_ne_zero := fun τ h => by
        obtain ⟨f, hf⟩ := hn₂ τ
        apply hf
        rw [← hc₂ τ f, h]
        rfl }
  let M₁ : MetrizedModel A L d₁ :=
    { model := 𝒢₁, hodge := D₁, lattice_eq := rfl, arch := fun τ => ⟨Φ₁ τ, hu₁ τ, hc₁ τ⟩ }
  let M₂ : MetrizedModel B L d₂ :=
    { model := 𝒢₂, hodge := D₂, lattice_eq := rfl, arch := fun τ => ⟨Φ₂ τ, hu₂ τ, hc₂ τ⟩ }
  refine ⟨d₁, d₂, M₁, M₂, rfl, rfl, ?_⟩
  exact hP K A B C L 𝒢₁ 𝒢₂ g MP e d₁ d₂ hd D₁ D₂ rfl rfl
    (fun τ => ⟨Φ₁ τ, Φ₂ τ, hu₁ τ, hu₂ τ, hc₁ τ, hc₂ τ, hper τ, hco τ⟩)

/-- **Glue S-alg-3a (sections of the Hodge lattices in product form).** Under the hypotheses of
`ProductHodgeAdd`, there are nonzero `s ∈ ⋀^g ω_{MP}`, `sᵢ ∈ ⋀^{gᵢ} ω_{𝒢ᵢ}` whose lattice indices
and coefficients multiply.

Why true (STANDARD). First `gᵢ = nᵢ = dim` (as in `ProductUnifDims`). `ω_{MP} = ω₁ ⊕ ω₂` (pull
back along the projections, restrict along the unit sections of the other factor; `e` preserves
units), so `s = p₁*s₁ ∧ p₂*s₂` generates `⋀^g ω_{MP} = ⋀^{g₁}ω₁ ⊗ ⋀^{g₂}ω₂` locally where the `sᵢ`
do, and `secIndex s = secIndex s₁ · secIndex s₂` (the index of `𝓞_L s₁ ⊗ 𝓞_L s₂` in a tensor
product of invertible modules is multiplicative: norms of fractional ideals). For coefficients:
both sides are `τ`-semilinear in `s₁`, `s₂`, so it suffices to take pure wedges; on
`p₁*f ∧ p₂*h` the Jacobian of `Φ₁ × Φ₂` at `0` is block diagonal (this uses the analytic clauses of
`prodUnif ∘ cast`, which hold although the hypotheses do not state them: product-height's
`ProductUnifAnalytic`), so `coeff_P(s) = coeff₁(s₁) · coeff₂(s₂)`. Reduced below
(`productHodgeSections_of`) to metrization's `ProductUniformizationAnalytic` and
`ProductHodgeLattice`. (Reviewed: true.) -/
def ProductHodgeSections : Prop :=
  ∀ (K : Type) [Field K] (A B C : AbVar K) (L : Type) [Field L] [NumberField L] [Algebra K L]
    (𝒢₁ : GroupModel A L) (𝒢₂ : GroupModel B L) (g : ℕ) (MP : MetrizedModel C L g)
    (e : MP.model.G ≅ 𝒢₁.G ⊗ 𝒢₂.G) [IsMonHom (e.hom ≫ fst _ _)] [IsMonHom (e.hom ≫ snd _ _)]
    (g₁ g₂ : ℕ) (hg : g₁ + g₂ = g) (D₁ : HodgeData L g₁ (𝒢₁.hodgeSpace g₁))
    (D₂ : HodgeData L g₂ (𝒢₂.hodgeSpace g₂)),
    D₁.lattice = 𝒢₁.detLattice g₁ → D₂.lattice = 𝒢₂.detLattice g₂ →
    (∀ τ : L →+* ℂ, ∃ (Φ₁ : (Fin g₁ → ℂ) → 𝒢₁.Pts τ) (Φ₂ : (Fin g₂ → ℂ) → 𝒢₂.Pts τ),
      𝒢₁.IsAnalyticUniformization τ (D₁.periods τ) Φ₁ ∧
      𝒢₂.IsAnalyticUniformization τ (D₂.periods τ) Φ₂ ∧
      (∀ f, D₁.coeff τ (𝒢₁.wedge f) = 𝒢₁.jacDet Φ₁ f) ∧
      (∀ f, D₂.coeff τ (𝒢₂.wedge f) = 𝒢₂.jacDet Φ₂ f) ∧
      (∀ z, z ∈ MP.hodge.periods τ ↔
        (fun i => z (Fin.cast hg i)) ∈ prodLattice (D₁.periods τ) (D₂.periods τ)) ∧
      ∀ f, MP.hodge.coeff τ (MP.model.wedge f) =
        MP.model.jacDet (fun z => prodUnif e Φ₁ Φ₂ (fun i => z (Fin.cast hg i))) f) →
    ∃ (s : MP.model.hodgeSpace g) (s₁ : 𝒢₁.hodgeSpace g₁) (s₂ : 𝒢₂.hodgeSpace g₂),
      s ∈ MP.hodge.lattice ∧ s ≠ 0 ∧ s₁ ∈ D₁.lattice ∧ s₁ ≠ 0 ∧ s₂ ∈ D₂.lattice ∧ s₂ ≠ 0 ∧
      secIndex MP.hodge.lattice s = secIndex D₁.lattice s₁ * secIndex D₂.lattice s₂ ∧
      ∀ τ, MP.hodge.coeff τ s = D₁.coeff τ s₁ * D₂.coeff τ s₂

/-- The covolume of a lattice in product form, up to the coordinate cast (proved, from
product-height's `prodLattice_facts`). -/
theorem covolume_of_cast {g g₁ g₂ : ℕ} (hg : g₁ + g₂ = g) (Λ : Submodule ℤ (Fin g → ℂ))
    (Λ₁ : Submodule ℤ (Fin g₁ → ℂ)) (Λ₂ : Submodule ℤ (Fin g₂ → ℂ)) [DiscreteTopology Λ₁]
    [IsZLattice ℝ Λ₁] [DiscreteTopology Λ₂] [IsZLattice ℝ Λ₂]
    (h : ∀ z, z ∈ Λ ↔ (fun i => z (Fin.cast hg i)) ∈ prodLattice Λ₁ Λ₂) :
    ZLattice.covolume Λ = ZLattice.covolume Λ₁ * ZLattice.covolume Λ₂ := by
  subst hg
  have hΛ : Λ = prodLattice Λ₁ Λ₂ := by
    ext z
    rw [h z]
    rfl
  subst hΛ
  obtain ⟨-, -, hc⟩ := prodLattice_facts Λ₁ Λ₂
  exact hc

/-- **`ProductHodgeAdd` from `ProductHodgeSections` (proved).** The covolumes multiply
(`covolume_of_cast`) and `modelHeight_add_of` gives equality of heights. -/
theorem productHodgeAdd_of (h : ProductHodgeSections) : ProductHodgeAdd := by
  intro K _ A B C L _ _ _ 𝒢₁ 𝒢₂ g MP e _ _ g₁ g₂ hg D₁ D₂ hl₁ hl₂ hform
  obtain ⟨s, s₁, s₂, hs, hs0, hs₁, hs₁0, hs₂, hs₂0, hidx, hco⟩ :=
    h K A B C L 𝒢₁ 𝒢₂ g MP e g₁ g₂ hg D₁ D₂ hl₁ hl₂ hform
  have hcov : ∀ τ, ZLattice.covolume (MP.hodge.periods τ) =
      ZLattice.covolume (D₁.periods τ) * ZLattice.covolume (D₂.periods τ) := by
    intro τ
    obtain ⟨-, -, -, -, -, -, hper, -⟩ := hform τ
    have := D₁.periods_discrete τ
    have := D₁.periods_isZLattice τ
    have := D₂.periods_discrete τ
    have := D₂.periods_isZLattice τ
    exact covolume_of_cast hg _ _ _ hper
  subst hg
  exact (modelHeight_add_of MP.hodge D₁ D₂ hs hs0 hs₁ hs₁0 hs₂ hs₂0 hidx hco hcov).ge

/-- **S-alg from `HodgeLatticeTheorem`, `ProductUnifDims`, `JacDetDescends` and
`ProductHodgeSections` (proved).** -/
theorem productMetrizationOfProductUnif_of' (hH : HodgeLatticeTheorem) (hD : ProductUnifDims)
    (hJ : JacDetDescends) (hS : ProductHodgeSections) : ProductMetrizationOfProductUnif :=
  productMetrizationOfProductUnif_of hH hD hJ (productHodgeAdd_of hS)

/-- **`JacDetDescends` (S-alg-2), proved**: metrization's `jacDetDescends` (§3b, no dimension
hypothesis needed). -/
theorem jacDetDescends' : JacDetDescends :=
  fun K _ A L _ _ _ 𝒢 d _ τ Λ Φ hΦ => ZInQ.Metrization.jacDetDescends K A L 𝒢 τ d Λ Φ hΦ

/-- **S-alg from `HodgeLatticeTheorem`, `ProductUnifDims` and `ProductHodgeSections` (proved).** -/
theorem productMetrizationOfProductUnif_of'' (hH : HodgeLatticeTheorem) (hD : ProductUnifDims)
    (hS : ProductHodgeSections) : ProductMetrizationOfProductUnif :=
  productMetrizationOfProductUnif_of' hH hD jacDetDescends' hS

/-- `prodUnif` (product-height) is metrization's `prodPts` (proved). -/
theorem prodUnif_eq_prodPts {K : Type} [Field K] {A B C : AbVar K} {L : Type} [Field L]
    [NumberField L] [Algebra K L] {𝒢P : GroupModel C L} {𝒢₁ : GroupModel A L}
    {𝒢₂ : GroupModel B L} (e : 𝒢P.G ≅ 𝒢₁.G ⊗ 𝒢₂.G) [IsMonHom (e.hom ≫ fst _ _)]
    [IsMonHom (e.hom ≫ snd _ _)] {τ : L →+* ℂ} {g₁ g₂ : ℕ} (Φ₁ : (Fin g₁ → ℂ) → 𝒢₁.Pts τ)
    (Φ₂ : (Fin g₂ → ℂ) → 𝒢₂.Pts τ) :
    prodUnif e Φ₁ Φ₂ = ZInQ.Metrization.prodPts e Φ₁ Φ₂ := by
  funext z
  unfold prodUnif
  rw [MulEquiv.symm_apply_eq]
  apply Prod.ext
  · exact (ZInQ.Metrization.prodPts_comp_fst e Φ₁ Φ₂ z).symm
  · exact (ZInQ.Metrization.prodPts_comp_snd e Φ₁ Φ₂ z).symm

/-- product-height's `prodLattice` is metrization's (proved). -/
theorem prodLattice_eq_metrization {g₁ g₂ : ℕ} (Λ₁ : Submodule ℤ (Fin g₁ → ℂ))
    (Λ₂ : Submodule ℤ (Fin g₂ → ℂ)) :
    prodLattice Λ₁ Λ₂ = ZInQ.Metrization.prodLattice Λ₁ Λ₂ := by
  ext z
  exact Iff.rfl

/-- **`ProductHodgeSections` from metrization's `ProductUniformizationAnalytic` and
`ProductHodgeLattice` (proved).** The factor metrizations are assembled from the hypotheses;
`ProductHodgeLattice` gives the sections and the index; metrization's `productJacobian`
(proved, §3b) gives the multiplicativity of the coefficients, applied to `prodPts = prodUnif`,
which is an analytic uniformization by `prodPts_alg` and `ProductUniformizationAnalytic`. -/
theorem productHodgeSections_of (hPA : ZInQ.Metrization.ProductUniformizationAnalytic)
    (hL : ZInQ.Metrization.ProductHodgeLattice) : ProductHodgeSections := by
  intro K _ A B C L _ _ _ 𝒢₁ 𝒢₂ g MP e he₁ he₂ g₁ g₂ hg D₁ D₂ hl₁ hl₂ hform
  subst hg
  choose Φ₁ Φ₂ hu₁ hu₂ hc₁ hc₂ hper hco using hform
  let M₁ : MetrizedModel A L g₁ :=
    { model := 𝒢₁, hodge := D₁, lattice_eq := hl₁, arch := fun τ => ⟨Φ₁ τ, hu₁ τ, hc₁ τ⟩ }
  let M₂ : MetrizedModel B L g₂ :=
    { model := 𝒢₂, hodge := D₂, lattice_eq := hl₂, arch := fun τ => ⟨Φ₂ τ, hu₂ τ, hc₂ τ⟩ }
  obtain ⟨-, f₁, f₂, f, a₁, a₂, hf1, hf2, hs₁, hs₁0, hs₂, hs₂0, hs, hs0, hidx⟩ :=
    hL K A B C L MP.model g₁ g₂ M₁ M₂ e he₁ he₂
  refine ⟨(a₁ * a₂) • MP.model.wedge f, a₁ • 𝒢₁.wedge f₁, a₂ • 𝒢₂.wedge f₂, ?_, hs0, hs₁, hs₁0,
    hs₂, hs₂0, ?_, fun τ => ?_⟩
  · rw [MP.lattice_eq]
    exact hs
  · rw [MP.lattice_eq]
    exact hidx
  · obtain ⟨hhom, hker, hsurj⟩ := ZInQ.Metrization.prodPts_alg e he₁ he₂ (hu₁ τ) (hu₂ τ)
    obtain ⟨hopen, hdiff⟩ := hPA K A B C L MP.model 𝒢₁ 𝒢₂ e he₁ he₂ τ g₁ g₂ _ _ (Φ₁ τ) (Φ₂ τ)
      (hu₁ τ) (hu₂ τ)
    have hjac := ZInQ.Metrization.productJacobian K A B C L MP.model 𝒢₁ 𝒢₂ e he₁ he₂ τ g₁ g₂ _ _
      (Φ₁ τ) (Φ₂ τ) (hu₁ τ) (hu₂ τ) ⟨hhom, hker, hsurj, hopen, hdiff⟩ f₁ f₂ f hf1 hf2
    have hfun : (fun z => prodUnif e (Φ₁ τ) (Φ₂ τ) (fun i => z (Fin.cast rfl i))) =
        ZInQ.Metrization.prodPts e (Φ₁ τ) (Φ₂ τ) := by
      rw [← prodUnif_eq_prodPts]
      rfl
    have hc := hco τ f
    rw [hfun] at hc
    rw [map_smulₛₗ, map_smulₛₗ, map_smulₛₗ, hc, hc₁, hc₂, hjac, map_mul]
    simp only [smul_eq_mul]
    ring

/-- **S-alg from `HodgeLatticeTheorem`, `ProductUnifDims`, metrization's
`ProductUniformizationAnalytic` and `ProductHodgeLattice` (proved).** -/
theorem productMetrizationOfProductUnif_of_metrization (hH : HodgeLatticeTheorem)
    (hD : ProductUnifDims) (hPA : ZInQ.Metrization.ProductUniformizationAnalytic)
    (hL : ZInQ.Metrization.ProductHodgeLattice) : ProductMetrizationOfProductUnif :=
  productMetrizationOfProductUnif_of'' hH hD (productHodgeSections_of hPA hL)

/-- **The same with `ProductLocalStructure` (metrization's glue, pure algebraic geometry) in place
of `ProductUniformizationAnalytic` (proved, via metrization's `productUniformizationAnalytic_of`).** -/
theorem productMetrizationOfProductUnif_of_local (hH : HodgeLatticeTheorem)
    (hD : ProductUnifDims) (hLS : ZInQ.Metrization.ProductLocalStructure)
    (hL : ZInQ.Metrization.ProductHodgeLattice) : ProductMetrizationOfProductUnif :=
  productMetrizationOfProductUnif_of_metrization hH hD
    (ZInQ.Metrization.productUniformizationAnalytic_of hLS) hL

/-- **Glue S-alg-1a (dimensions in product form).** The hypotheses of `ProductUnifDims`; the
conclusion is its dimension half: `dim A = g₁` and `dim B = g₂`. Why true: as in `ProductUnifDims`
(the nonsingularity half is not needed for it). Unproved. -/
def ProductUnifDimsEq : Prop :=
  ∀ (K : Type) [Field K] (A B C : AbVar K) (L : Type) [Field L] [NumberField L] [Algebra K L]
    (𝒢₁ : GroupModel A L) (𝒢₂ : GroupModel B L) (g : ℕ) (MP : MetrizedModel C L g)
    (e : MP.model.G ≅ 𝒢₁.G ⊗ 𝒢₂.G) [IsMonHom (e.hom ≫ fst _ _)] [IsMonHom (e.hom ≫ snd _ _)]
    (τ : L →+* ℂ) (g₁ g₂ : ℕ) (hg : g₁ + g₂ = g) (Λ₁ : Submodule ℤ (Fin g₁ → ℂ))
    (Λ₂ : Submodule ℤ (Fin g₂ → ℂ)) (Φ₁ : (Fin g₁ → ℂ) → 𝒢₁.Pts τ)
    (Φ₂ : (Fin g₂ → ℂ) → 𝒢₂.Pts τ),
    (∃ _ : DiscreteTopology Λ₁, IsZLattice ℝ Λ₁) →
    (∃ _ : DiscreteTopology Λ₂, IsZLattice ℝ Λ₂) →
    𝒢₁.IsAnalyticUniformization τ Λ₁ Φ₁ → 𝒢₂.IsAnalyticUniformization τ Λ₂ Φ₂ →
    (∀ z, z ∈ MP.hodge.periods τ ↔ (fun i => z (Fin.cast hg i)) ∈ prodLattice Λ₁ Λ₂) →
    (∀ f, MP.hodge.coeff τ (MP.model.wedge f) =
      MP.model.jacDet (fun z => prodUnif e Φ₁ Φ₂ (fun i => z (Fin.cast hg i))) f) →
    A.dim = g₁ ∧ B.dim = g₂

/-- **`ProductUnifDims` from its dimension half and metrization's `JacDetNondegenerate`
(proved).** An alternative to proving the nonsingularity half from the product structure: it
trades that algebra for metrization's complex-geometry glue (local parameters are analytic
coordinates). -/
theorem productUnifDims_of (hE : ProductUnifDimsEq) (hN : ZInQ.Metrization.JacDetNondegenerate) :
    ProductUnifDims := by
  intro K _ A B C L _ _ _ 𝒢₁ 𝒢₂ g MP e _ _ τ g₁ g₂ hg Λ₁ Λ₂ Φ₁ Φ₂ hl₁ hl₂ hu₁ hu₂ hper hco
  obtain ⟨hA, hB⟩ := hE K A B C L 𝒢₁ 𝒢₂ g MP e τ g₁ g₂ hg Λ₁ Λ₂ Φ₁ Φ₂ hl₁ hl₂ hu₁ hu₂ hper hco
  obtain ⟨hd₁, hz₁⟩ := hl₁
  obtain ⟨hd₂, hz₂⟩ := hl₂
  exact ⟨hA, hB, hN K A L 𝒢₁ τ g₁ hA Λ₁ Φ₁ hz₁ hu₁, hN K B L 𝒢₂ τ g₂ hB Λ₂ Φ₂ hz₂ hu₂⟩

end SAlg

end ZInQ.ProductUnif


namespace ZInQ.ProductUnif

/-- **P2 from the S-alg reduction (proved).** `ProductModelHeight` (the type of
`GluePieces.productModelHeight`) from `HodgeLatticeTheorem` and the three new glue Props;
`ProductUnifSplits` is now a theorem. -/
theorem productModelHeight_of_salg (hH : DefFaltings.HodgeLatticeTheorem)
    (hD : ProductUnifDims) (hJ : JacDetDescends) (hP : ProductHodgeAdd) :
    ZInQ.H5Neron.ProductModelHeight :=
  ZInQ.ProductHeight.productModelHeight_of_splits productUnifSplits
    (productMetrizationOfProductUnif_of hH hD hJ hP)

/-- **P2 from the finest reduction (proved).** -/
theorem productModelHeight_of_salg' (hH : DefFaltings.HodgeLatticeTheorem)
    (hD : ProductUnifDims) (hJ : JacDetDescends) (hS : ProductHodgeSections) :
    ZInQ.H5Neron.ProductModelHeight :=
  productModelHeight_of_salg hH hD hJ (productHodgeAdd_of hS)

/-- **P2 from `HodgeLatticeTheorem`, `ProductUnifDims` and `ProductHodgeSections` (proved).** -/
theorem productModelHeight_of_salg'' (hH : DefFaltings.HodgeLatticeTheorem)
    (hD : ProductUnifDims) (hS : ProductHodgeSections) : ZInQ.H5Neron.ProductModelHeight :=
  productModelHeight_of_salg' hH hD jacDetDescends' hS

/-- **P2 from `HodgeLatticeTheorem`, `ProductUnifDims` and metrization's `ProductLocalStructure`
and `ProductHodgeLattice` (proved).** -/
theorem productModelHeight_of_local (hH : DefFaltings.HodgeLatticeTheorem)
    (hD : ProductUnifDims) (hLS : ZInQ.Metrization.ProductLocalStructure)
    (hL : ZInQ.Metrization.ProductHodgeLattice) : ZInQ.H5Neron.ProductModelHeight :=
  ZInQ.ProductHeight.productModelHeight_of_splits productUnifSplits
    (productMetrizationOfProductUnif_of_local hH hD hLS hL)

/-- **product-height's glue `ProductUnifAnalytic` from metrization's `ProductLocalStructure`
(proved)**, via `prodUnif = prodPts` and metrization's `productUniformizationAnalytic_of`. -/
theorem productUnifAnalytic_of_local (hLS : ZInQ.Metrization.ProductLocalStructure) :
    ZInQ.ProductHeight.ProductUnifAnalytic := by
  intro K _ A B C L _ _ _ 𝒢P 𝒢₁ 𝒢₂ e h1 h2 τ g₁ g₂ Λ₁ Λ₂ Φ₁ Φ₂ hu₁ hu₂
  rw [prodUnif_eq_prodPts]
  exact ZInQ.Metrization.productUniformizationAnalytic_of hLS K A B C L 𝒢P 𝒢₁ 𝒢₂ e h1 h2 τ g₁ g₂
    Λ₁ Λ₂ Φ₁ Φ₂ hu₁ hu₂

end ZInQ.ProductUnif



namespace ZInQ.Metrization
open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open NumberField ZInQ.DefFaltings
/-- **Leaf (AN3 with its dimension: the uniformization theorem).** For every smooth group model
`𝒢` of `A_L`, every `τ : L → ℂ` and `g = dim A`, there are a full lattice `Λ ⊂ ℂ^g` and an analytic
uniformization `Φ : ℂ^g → 𝒢(ℂ)_τ` with kernel `Λ`. This is def-faltings'
`AnalyticUniformizationExists` with the dimension pinned to `dim A` (`𝒢(ℂ)_τ = A_τ(ℂ)` is a compact
connected complex Lie group of dimension `dim A`, hence `≅ ℂ^g/Λ`: Mumford, *Abelian varieties*,
§1 and §4 (UNVERIFIED locators), with Serre's GAGA for the analytic structure of `A_τ(ℂ)`).
Implies `AnalyticUniformizationExists` (`analyticUniformizationExists_of`). -/
def AnalyticUniformizationOfDim : Prop :=
  ∀ (K : Type) [Field K] (A : AbVar K) (L : Type) [Field L] [NumberField L] [Algebra K L]
    (𝒢 : GroupModel A L) (τ : L →+* ℂ) (g : ℕ), A.dim = g →
    ∃ (Λ : Submodule ℤ (Fin g → ℂ)) (Φ : (Fin g → ℂ) → 𝒢.Pts τ),
      ∃ _ : DiscreteTopology Λ, IsZLattice ℝ Λ ∧ 𝒢.IsAnalyticUniformization τ Λ Φ

end ZInQ.Metrization

/-! ## metrization2: `JacDetNondegenerate` from the local structure of morphisms out of a product

Step 1 (linear algebra): if every `jacDet Φ f` vanishes, some `v ≠ 0` is killed by
`d(germAlong Φ t)(0)` for every `t ∈ 𝔪_ξ`. Step 2: then by every regular function near `ξ`
(subtract the pull-back along `𝒢 → Spec 𝓞_L` of its restriction to the unit section). -/

namespace ZInQ.Metrization2

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open NumberField ZInQ.DefFaltings ZInQ.Metrization Topology

/-- Step 1 (pure linear algebra). If every `g × g` matrix whose rows are taken from a family
`F` of vectors of `ℂ^g` has determinant `0`, a nonzero vector is orthogonal (for the bilinear
pairing `Σ_j x_j y_j`) to every member of the family. -/
theorem exists_null_of_det_eq_zero {J : Type*} {g : ℕ} (F : J → (Fin g → ℂ))
    (h : ∀ f : Fin g → J, (Matrix.of fun i j => F (f i) j).det = 0) :
    ∃ v : Fin g → ℂ, v ≠ 0 ∧ ∀ i, ∑ j, F i j * v j = 0 := by
  by_cases hW : Submodule.span ℂ (Set.range F) = ⊤
  · exfalso
    obtain ⟨κ, a, -, hspan, hli⟩ := exists_linearIndependent' ℂ F
    rw [hW] at hspan
    have : Finite κ := hli.finite
    haveI := Fintype.ofFinite κ
    have hcard : Fintype.card κ = g := by
      rw [linearIndependent_iff_card_eq_finrank_span.mp hli, Set.finrank, hspan, finrank_top,
        Module.finrank_fin_fun]
    let eqv : Fin g ≃ κ := (Fintype.equivFinOfCardEq hcard).symm
    have hli' : LinearIndependent ℂ ((F ∘ a) ∘ eqv) := hli.comp eqv eqv.injective
    have hU : IsUnit (Matrix.of fun i j => F (a (eqv i)) j) :=
      Matrix.linearIndependent_row_iff_isUnit.mp hli'
    exact ((Matrix.isUnit_iff_isUnit_det _).mp hU).ne_zero (h (a ∘ eqv))
  · obtain ⟨φ, hφ0, hle⟩ := Submodule.exists_le_ker_of_lt_top _ (lt_top_iff_ne_top.mpr hW)
    refine ⟨fun j => φ (fun k => if j = k then 1 else 0), ?_, ?_⟩
    · intro hv
      apply hφ0
      refine LinearMap.ext fun x => ?_
      rw [LinearMap.pi_apply_eq_sum_univ φ x]
      simp only [LinearMap.zero_apply]
      refine Finset.sum_eq_zero fun j _ => ?_
      have := congrFun hv j
      simp only [Pi.zero_apply] at this
      rw [this, smul_zero]
    · intro i
      have h1 := hle (Submodule.subset_span ⟨i, rfl⟩)
      rw [LinearMap.mem_ker, LinearMap.pi_apply_eq_sum_univ] at h1
      simpa [smul_eq_mul] using h1

section Eval

variable {K : Type} [Field K] {A : AbVar K} {L : Type} [Field L] [NumberField L] [Algebra K L]
variable (𝒢 : GroupModel A L)

/-- The value at the complex point `Spec ℂ → Spec 𝓞_L` (via `τ`) of a function on an open of
`Spec 𝓞_L` (`0` off the open). -/
noncomputable def baseVal (τ : L →+* ℂ) (O : (Spec (CommRingCat.of (𝓞 L))).Opens)
    (x : Γ(Spec (CommRingCat.of (𝓞 L)), O)) : ℂ := by
  classical
  exact if h : ⊤ ≤ (GroupModel.ptC (L := L) τ).hom ⁻¹ᵁ O then
    (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom ((GroupModel.ptC (L := L) τ).hom.appLE O ⊤ h x)
  else 0

/-- A function pulled back from `Spec 𝓞_L` takes the same value at every complex point. -/
theorem evalAt_pullback_base {τ : L →+* ℂ} (p : 𝒢.Pts τ) (O : (Spec (CommRingCat.of (𝓞 L))).Opens)
    (x : Γ(Spec (CommRingCat.of (𝓞 L)), O)) :
    𝒢.evalAt p (𝒢.G.hom ⁻¹ᵁ O) (𝒢.G.hom.app O x) = baseVal τ O x := by
  have hw : p.left ≫ 𝒢.G.hom = (GroupModel.ptC τ).hom := Over.w p
  have hpre : p.left ⁻¹ᵁ (𝒢.G.hom ⁻¹ᵁ O) = (GroupModel.ptC (L := L) τ).hom ⁻¹ᵁ O := by
    rw [← hw]; rfl
  unfold GroupModel.evalAt baseVal
  by_cases h : ⊤ ≤ (GroupModel.ptC (L := L) τ).hom ⁻¹ᵁ O
  · have h' : ⊤ ≤ p.left ⁻¹ᵁ (𝒢.G.hom ⁻¹ᵁ O) := hpre ▸ h
    rw [dif_pos h', dif_pos h]
    congr 1
    have key : ∀ (f : Spec (CommRingCat.of ℂ) ⟶ Spec (CommRingCat.of (𝓞 L)))
        (hf : f = (GroupModel.ptC (L := L) τ).hom) (e : ⊤ ≤ f ⁻¹ᵁ O),
        f.appLE O ⊤ e x = (GroupModel.ptC (L := L) τ).hom.appLE O ⊤ h x := by
      rintro f rfl e; rfl
    have h'' : ⊤ ≤ (p.left ≫ 𝒢.G.hom) ⁻¹ᵁ O := h'
    refine Eq.trans ?_ (key _ hw h'')
    have hc := Scheme.Hom.comp_appLE p.left 𝒢.G.hom O ⊤ h''
    exact congrArg (fun φ => (ConcreteCategory.hom φ) x) hc.symm
  · have h' : ¬ ⊤ ≤ p.left ⁻¹ᵁ (𝒢.G.hom ⁻¹ᵁ O) := fun h' => h (hpre ▸ h')
    rw [dif_neg h', dif_neg h]

/-- A complex point factoring as `Spec ℂ → Spec 𝓞_L → 𝒢` evaluates through the section. -/
theorem evalAt_of_left_eq {τ : L →+* ℂ} (p : 𝒢.Pts τ)
    (f : Spec (CommRingCat.of (𝓞 L)) ⟶ 𝒢.G.left) (hp : p.left = (GroupModel.ptC τ).hom ≫ f)
    (V : 𝒢.G.left.Opens) (b : Γ(𝒢.G.left, V)) :
    𝒢.evalAt p V b = baseVal τ (f ⁻¹ᵁ V) (f.app V b) := by
  have hpre : p.left ⁻¹ᵁ V = (GroupModel.ptC (L := L) τ).hom ⁻¹ᵁ (f ⁻¹ᵁ V) := by
    rw [hp]; rfl
  unfold GroupModel.evalAt baseVal
  by_cases h : ⊤ ≤ (GroupModel.ptC (L := L) τ).hom ⁻¹ᵁ (f ⁻¹ᵁ V)
  · have h' : ⊤ ≤ p.left ⁻¹ᵁ V := hpre ▸ h
    rw [dif_pos h', dif_pos h]
    congr 1
    have key : ∀ (q : Spec (CommRingCat.of ℂ) ⟶ 𝒢.G.left)
        (hq : q = (GroupModel.ptC (L := L) τ).hom ≫ f) (e : ⊤ ≤ q ⁻¹ᵁ V),
        q.appLE V ⊤ e b = ((GroupModel.ptC (L := L) τ).hom ≫ f).appLE V ⊤ h b := by
      rintro q rfl e; rfl
    refine (key _ hp h').trans ?_
    have hc := Scheme.Hom.comp_appLE (GroupModel.ptC (L := L) τ).hom f V ⊤ h
    exact congrArg (fun φ => (ConcreteCategory.hom φ) b) hc
  · have h' : ¬ ⊤ ≤ p.left ⁻¹ᵁ V := fun h' => h (hpre ▸ h')
    rw [dif_neg h', dif_neg h]

/-- `(1 : 𝒢(ℂ)_τ)` is `Spec ℂ → Spec 𝓞_L → 𝒢` through the unit section. -/
theorem one_left_eq (τ : L →+* ℂ) :
    (1 : 𝒢.Pts τ).left = (GroupModel.ptC τ).hom ≫ 𝒢.unitSection := by
  have hw : (toUnit (GroupModel.ptC (L := L) τ)).left = (GroupModel.ptC (L := L) τ).hom :=
    (Category.comp_id _).symm.trans (Over.w (toUnit (GroupModel.ptC (L := L) τ)))
  show (toUnit (GroupModel.ptC τ) ≫ η[𝒢.G]).left = _
  rw [Over.comp_left, hw]
  rfl

/-- The unit section is a section of the structure map. -/
theorem unitSection_comp_hom : 𝒢.unitSection ≫ 𝒢.G.hom = 𝟙 _ := by
  show (η[𝒢.G] : 𝟙_ (Over (Spec (CommRingCat.of (𝓞 L)))) ⟶ 𝒢.G).left ≫ 𝒢.G.hom = 𝟙 _
  rw [Over.w]
  rfl

theorem one_mem_dom (τ : L →+* ℂ) (W : 𝒢.G.left.Opens) (m : 𝒢.genericUnit ∈ W) :
    ⊤ ≤ (1 : 𝒢.Pts τ).left ⁻¹ᵁ W := by
  intro x _
  show (1 : 𝒢.Pts τ).left x ∈ W
  erw [one_left_apply]
  exact m

theorem evalAt_sub {τ : L →+* ℂ} (p : 𝒢.Pts τ) (U : 𝒢.G.left.Opens) (s s' : Γ(𝒢.G.left, U)) :
    𝒢.evalAt p U (s - s') = 𝒢.evalAt p U s - 𝒢.evalAt p U s' := by
  unfold GroupModel.evalAt
  split_ifs with h
  · rw [map_sub]
    exact map_sub (ConcreteCategory.hom (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom) _ _
  · simp

theorem evalAt_one_sec {τ : L →+* ℂ} (p : 𝒢.Pts τ) (U : 𝒢.G.left.Opens) (h : ⊤ ≤ p.left ⁻¹ᵁ U) :
    𝒢.evalAt p U 1 = 1 := by
  unfold GroupModel.evalAt
  rw [dif_pos h, map_one]
  exact map_one (ConcreteCategory.hom (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom)

/-- A section vanishing at the identity complex point has its germ at `ξ` in `𝔪_ξ`. -/
theorem germ_mem_of_evalAt_one {τ : L →+* ℂ} (W : 𝒢.G.left.Opens) (m : 𝒢.genericUnit ∈ W)
    (s : Γ(𝒢.G.left, W)) (h : 𝒢.evalAt (1 : 𝒢.Pts τ) W s = 0) :
    𝒢.G.left.presheaf.germ W 𝒢.genericUnit m s ∈ IsLocalRing.maximalIdeal 𝒢.genStalk := by
  by_contra hn
  obtain ⟨u, hu⟩ := (IsLocalRing.notMem_maximalIdeal.mp hn).exists_right_inv
  obtain ⟨U', m', s', rfl⟩ := 𝒢.exists_rep u
  have mm : 𝒢.genericUnit ∈ W ⊓ U' := TopologicalSpace.Opens.mem_inf.mpr ⟨m, m'⟩
  have hg : 𝒢.G.left.presheaf.germ (W ⊓ U') 𝒢.genericUnit mm
      (𝒢.G.left.presheaf.map (homOfLE inf_le_left).op s *
        𝒢.G.left.presheaf.map (homOfLE inf_le_right).op s') =
      𝒢.G.left.presheaf.germ (W ⊓ U') 𝒢.genericUnit mm 1 := by
    rw [map_mul, TopCat.Presheaf.germ_res_apply, TopCat.Presheaf.germ_res_apply, hu, map_one]
  obtain ⟨W'', m'', i₁, i₂, hW⟩ := TopCat.Presheaf.germ_eq _ 𝒢.genericUnit mm mm _ _ hg
  have hd := one_mem_dom 𝒢 τ W'' m''
  have e1 := congrArg (𝒢.evalAt (1 : 𝒢.Pts τ) W'') hW
  rw [map_mul, map_one, evalAt_mul, evalAt_one_sec 𝒢 _ _ hd, evalAt_res 𝒢 _ _ hd,
    evalAt_res 𝒢 _ _ hd] at e1
  rw [evalAt_res 𝒢 (1 : 𝒢.Pts τ) (homOfLE inf_le_left)
    ((one_mem_dom 𝒢 τ _ mm)) s, h, zero_mul] at e1
  exact zero_ne_one e1

end Eval

end ZInQ.Metrization2
/-! ## metrization2: the glue Prop, step 2 (all regular functions) and step 3 (translation) -/

namespace ZInQ.Metrization2

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open NumberField ZInQ.DefFaltings ZInQ.Metrization Topology

/-- **Glue (local structure of a morphism out of a fibre product, at complex points).** For group
models `𝒢₁`, `𝒢₂`, `ℋ` over `𝓞_L`, a morphism `m : 𝒢₁ ×_{𝓞_L} 𝒢₂ → ℋ` of `𝓞_L`-schemes, an open
`U ⊆ ℋ`, `s ∈ Γ(U, 𝒪_ℋ)` and complex points `p₁`, `p₂` with `m(p₁, p₂) ∈ U(ℂ)`: there are opens
`Vᵢ ∋ pᵢ` and regular functions `a_k, c_k` on `V₁`, `b_k, d_k` on `V₂` such that
`H = Σ c_k(·) d_k(·)` is nonzero at `(p₁, p₂)` and, wherever `H(p₁', p₂') ≠ 0` on
`V₁(ℂ) × V₂(ℂ)`, `m(p₁', p₂') ∈ U(ℂ)` and `s(m(p₁', p₂')) · H(p₁', p₂') = Σ a_k(p₁') b_k(p₂')`.
Why true (STANDARD; pure scheme theory, no analysis): take affine opens `Vᵢ = Spec Rᵢ ∋ pᵢ`;
`V₁ ×_{𝓞_L} V₂ = Spec (R₁ ⊗_{𝓞_L} R₂)` is an open of the product (Mathlib: `pullbackSpecIso`);
choose a basic open `D(h) ∋ (p₁, p₂)` inside `m⁻¹(U) ∩ (V₁ × V₂)`; on it `m^*s = a / h^N`; write
`h^N = Σ c_k ⊗ d_k`, `a = Σ a_k ⊗ b_k`; a complex point `(p₁', p₂')` of `V₁ × V₂` is the ring map
`r₁ ⊗ r₂ ↦ r₁(p₁') r₂(p₂')`, and it lies in `D(h)` iff `h^N(p₁', p₂') ≠ 0`.
Special cases: `m = e.inv` for `e : 𝒢P ≅ 𝒢₁ × 𝒢₂` is metrization's `ProductLocalStructure`
(`productLocalStructure_of`); `m = μ` (the group law) gives `JacDetNondegenerate`
(`jacDetNondegenerate_of`). -/
def ProductMapLocalStructure : Prop :=
  ∀ (K : Type) [Field K] (A B C : AbVar K) (L : Type) [Field L] [NumberField L] [Algebra K L]
    (ℋ : GroupModel C L) (𝒢₁ : GroupModel A L) (𝒢₂ : GroupModel B L)
    (m : 𝒢₁.G ⊗ 𝒢₂.G ⟶ ℋ.G) (τ : L →+* ℂ) (U : ℋ.G.left.Opens) (s : Γ(ℋ.G.left, U))
    (p₁ : 𝒢₁.Pts τ) (p₂ : 𝒢₂.Pts τ), ⊤ ≤ (lift p₁ p₂ ≫ m).left ⁻¹ᵁ U →
    ∃ (V₁ : 𝒢₁.G.left.Opens) (V₂ : 𝒢₂.G.left.Opens) (n : ℕ)
      (a c : Fin n → Γ(𝒢₁.G.left, V₁)) (b d : Fin n → Γ(𝒢₂.G.left, V₂)),
      ⊤ ≤ p₁.left ⁻¹ᵁ V₁ ∧ ⊤ ≤ p₂.left ⁻¹ᵁ V₂ ∧
      (∑ k, 𝒢₁.evalAt p₁ V₁ (c k) * 𝒢₂.evalAt p₂ V₂ (d k)) ≠ 0 ∧
      ∀ (p₁' : 𝒢₁.Pts τ) (p₂' : 𝒢₂.Pts τ), ⊤ ≤ p₁'.left ⁻¹ᵁ V₁ → ⊤ ≤ p₂'.left ⁻¹ᵁ V₂ →
        (∑ k, 𝒢₁.evalAt p₁' V₁ (c k) * 𝒢₂.evalAt p₂' V₂ (d k)) ≠ 0 →
        ⊤ ≤ (lift p₁' p₂' ≫ m).left ⁻¹ᵁ U ∧
        ℋ.evalAt (lift p₁' p₂' ≫ m) U s *
            (∑ k, 𝒢₁.evalAt p₁' V₁ (c k) * 𝒢₂.evalAt p₂' V₂ (d k)) =
          ∑ k, 𝒢₁.evalAt p₁' V₁ (a k) * 𝒢₂.evalAt p₂' V₂ (b k)

/-- `ProductMapLocalStructure` contains metrization's `ProductLocalStructure` (`m = e.inv`). -/
theorem productLocalStructure_of (h : ProductMapLocalStructure) :
    ZInQ.Metrization.ProductLocalStructure := by
  intro K _ A B C L _ _ _ 𝒢P 𝒢₁ 𝒢₂ e τ U s p₁ p₂ hp
  exact h K A B C L 𝒢P 𝒢₁ 𝒢₂ e.inv τ U s p₁ p₂ hp

section Steps

variable {K : Type} [Field K] {A : AbVar K} {L : Type} [Field L] [NumberField L] [Algebra K L]
variable (𝒢 : GroupModel A L)

theorem hom_genericUnit : 𝒢.G.hom 𝒢.genericUnit = genericPt L := by
  show 𝒢.G.hom (𝒢.unitSection (genericPt L)) = genericPt L
  rw [← Scheme.Hom.comp_apply, unitSection_comp_hom]
  rfl

/-- Step 2. If `d(germAlong Φ t)(0)` kills `v` for every `t ∈ 𝔪_ξ`, then the differential at `0`
of `z ↦ b(Φ z)` kills `v` for every regular function `b` near `ξ`. -/
theorem fderiv_evalAt_apply_eq_zero {τ : L →+* ℂ} {g : ℕ} {Λ : Submodule ℤ (Fin g → ℂ)}
    {Φ : (Fin g → ℂ) → 𝒢.Pts τ} (hΦ : 𝒢.IsAnalyticUniformization τ Λ Φ) (v : Fin g → ℂ)
    (hv : ∀ t : IsLocalRing.maximalIdeal 𝒢.genStalk,
      fderiv ℂ (𝒢.germAlong Φ (t : 𝒢.genStalk)) 0 v = 0)
    (V : 𝒢.G.left.Opens) (m : 𝒢.genericUnit ∈ V) (b : Γ(𝒢.G.left, V)) :
    fderiv ℂ (fun z => 𝒢.evalAt (Φ z) V b) 0 v = 0 := by
  set O := 𝒢.unitSection ⁻¹ᵁ V with hO
  set c : Γ(𝒢.G.left, 𝒢.G.hom ⁻¹ᵁ O) := 𝒢.G.hom.app O (𝒢.unitSection.app V b) with hc
  have mO : 𝒢.genericUnit ∈ 𝒢.G.hom ⁻¹ᵁ O := by
    show 𝒢.unitSection (𝒢.G.hom 𝒢.genericUnit) ∈ V
    rw [hom_genericUnit]
    exact m
  set W := V ⊓ 𝒢.G.hom ⁻¹ᵁ O with hW
  have mW : 𝒢.genericUnit ∈ W := TopologicalSpace.Opens.mem_inf.mpr ⟨m, mO⟩
  set b' : Γ(𝒢.G.left, W) := 𝒢.G.left.presheaf.map (homOfLE inf_le_left).op b -
    𝒢.G.left.presheaf.map (homOfLE inf_le_right).op c with hb'
  have h1 : 𝒢.evalAt (1 : 𝒢.Pts τ) W b' = 0 := by
    have hd := one_mem_dom 𝒢 τ W mW
    rw [hb', evalAt_sub, evalAt_res 𝒢 _ _ hd, evalAt_res 𝒢 _ _ hd,
      evalAt_of_left_eq 𝒢 1 𝒢.unitSection (one_left_eq 𝒢 τ) V b, hc, evalAt_pullback_base,
      sub_self]
  have hgerm := germ_mem_of_evalAt_one 𝒢 W mW b' h1
  have hv' := hv ⟨_, hgerm⟩
  have heq : 𝒢.germAlong Φ (𝒢.G.left.presheaf.germ W 𝒢.genericUnit mW b') =ᶠ[𝓝 0]
      fun z => 𝒢.evalAt (Φ z) V b - baseVal τ O (𝒢.unitSection.app V b) := by
    filter_upwards [germAlong_eventuallyEq 𝒢 hΦ W mW b',
      (hΦ.2.2.2.1 W).mem_nhds (zero_mem_dom 𝒢 hΦ W mW)] with z hz1 hz
    rw [hz1, hb', evalAt_sub, evalAt_res 𝒢 _ _ hz, evalAt_res 𝒢 _ _ hz, hc,
      evalAt_pullback_base]
  simp only at hv'
  rw [heq.fderiv_eq, fderiv_sub_const] at hv'
  exact hv'

/-- Step 3 (translation). If every regular function near `ξ` has `d(b ∘ Φ)(0) v = 0`, then for
every regular function `s` on `U` and every `w ∈ Φ⁻¹(U(ℂ))`, `t ↦ s(Φ(w + t v))` has derivative
`0` at `t = 0`: near `0`, `s(Φ w · Φ z) = N(z)/D(z)` with `N`, `D` combinations of regular
functions near `ξ` along `Φ` (`ProductMapLocalStructure` for the group law `μ`). -/
theorem hasDerivAt_line_zero (hML : ProductMapLocalStructure) {τ : L →+* ℂ} {g : ℕ}
    {Λ : Submodule ℤ (Fin g → ℂ)} {Φ : (Fin g → ℂ) → 𝒢.Pts τ}
    (hΦ : 𝒢.IsAnalyticUniformization τ Λ Φ) (v : Fin g → ℂ)
    (hv2 : ∀ (V : 𝒢.G.left.Opens) (_ : 𝒢.genericUnit ∈ V) (b : Γ(𝒢.G.left, V)),
      fderiv ℂ (fun z => 𝒢.evalAt (Φ z) V b) 0 v = 0)
    (U : 𝒢.G.left.Opens) (s : Γ(𝒢.G.left, U)) (w : Fin g → ℂ) (hw : w ∈ 𝒢.dom Φ U) :
    HasDerivAt (fun t : ℂ => 𝒢.evalAt (Φ (w + t • v)) U s) 0 0 := by
  have h0 : Φ 0 = 1 := by
    have h := hΦ.1 0 0
    rw [add_zero] at h
    exact mul_left_cancel (a := Φ 0) (by rw [_root_.mul_one]; exact h.symm)
  have hmul : ∀ z, lift (Φ w) (Φ z) ≫ μ[𝒢.G] = Φ (w + z) := fun z => (hΦ.1 w z).symm
  have hU' : ⊤ ≤ (lift (Φ w) (Φ 0) ≫ μ[𝒢.G]).left ⁻¹ᵁ U := by
    rw [hmul, add_zero]; exact hw
  obtain ⟨V₁, V₂, n, a, c, b, d, hV₁, hV₂, hne, hall⟩ :=
    hML K A A A L 𝒢 𝒢 𝒢 μ[𝒢.G] τ U s (Φ w) (Φ 0) hU'
  have mV₂ : 𝒢.genericUnit ∈ V₂ := by
    obtain ⟨x⟩ : Nonempty (Spec (CommRingCat.of ℂ)) := inferInstance
    have hx := hV₂ (show x ∈ (⊤ : (Spec (CommRingCat.of ℂ)).Opens) from trivial)
    change (Φ 0).left x ∈ V₂ at hx
    rw [h0] at hx
    erw [one_left_apply] at hx
    exact hx
  set Nf : (Fin g → ℂ) → ℂ := fun z =>
    ∑ k, 𝒢.evalAt (Φ w) V₁ (a k) * 𝒢.evalAt (Φ z) V₂ (b k) with hNf
  set Df : (Fin g → ℂ) → ℂ := fun z =>
    ∑ k, 𝒢.evalAt (Φ w) V₁ (c k) * 𝒢.evalAt (Φ z) V₂ (d k) with hDf
  have hdom2 : IsOpen (𝒢.dom Φ V₂) := hΦ.2.2.2.1 V₂
  have h0dom : (0 : Fin g → ℂ) ∈ 𝒢.dom Φ V₂ := hV₂
  have hDcont : ContinuousOn Df (𝒢.dom Φ V₂) := by
    have : DifferentiableOn ℂ Df (𝒢.dom Φ V₂) := by
      simp only [hDf]
      exact DifferentiableOn.fun_sum fun k _ =>
        (hΦ.2.2.2.2 V₂ (d k)).const_mul _
    exact this.continuousOn
  set O := 𝒢.dom Φ V₂ ∩ Df ⁻¹' {0}ᶜ with hO
  have hOopen : IsOpen O := hDcont.isOpen_inter_preimage hdom2 isOpen_compl_singleton
  have hD0 : Df 0 ≠ 0 := hne
  have h0O : (0 : Fin g → ℂ) ∈ O := ⟨h0dom, hD0⟩
  -- derivative along the line of each regular function near `ξ`
  have hline : ∀ (bb : Γ(𝒢.G.left, V₂)),
      HasDerivAt (fun t : ℂ => 𝒢.evalAt (Φ (t • v)) V₂ bb) 0 0 := by
    intro bb
    have hd : DifferentiableAt ℂ (fun z => 𝒢.evalAt (Φ z) V₂ bb) 0 :=
      (hΦ.2.2.2.2 V₂ bb).differentiableAt (hdom2.mem_nhds h0dom)
    have hF : HasFDerivAt (fun z => 𝒢.evalAt (Φ z) V₂ bb)
        (fderiv ℂ (fun z => 𝒢.evalAt (Φ z) V₂ bb) 0) ((0 : ℂ) • v) := by
      rw [zero_smul]; exact hd.hasFDerivAt
    have := hF.comp_hasDerivAt (0 : ℂ) ((hasDerivAt_id (0 : ℂ)).smul_const v)
    simp only [one_smul, hv2 V₂ mV₂ bb] at this
    exact this
  have hN : HasDerivAt (fun t : ℂ => Nf (t • v)) 0 0 := by
    have := HasDerivAt.fun_sum (u := Finset.univ) fun k _ =>
      (hline (b k)).const_mul (𝒢.evalAt (Φ w) V₁ (a k))
    simpa [hNf] using this
  have hD : HasDerivAt (fun t : ℂ => Df (t • v)) 0 0 := by
    have := HasDerivAt.fun_sum (u := Finset.univ) fun k _ =>
      (hline (d k)).const_mul (𝒢.evalAt (Φ w) V₁ (c k))
    simpa [hDf] using this
  have hD0' : Df ((0 : ℂ) • v) ≠ 0 := by rw [zero_smul]; exact hD0
  have hq := hN.div hD hD0'
  simp only [zero_mul, mul_zero, sub_zero, zero_div] at hq
  refine hq.congr_of_eventuallyEq ?_
  have hcont : Continuous fun t : ℂ => t • v := continuous_id.smul continuous_const
  have hev : ∀ᶠ t in 𝓝 (0 : ℂ), t • v ∈ O :=
    hcont.continuousAt.preimage_mem_nhds (by rw [zero_smul]; exact hOopen.mem_nhds h0O)
  filter_upwards [hev] with t ht
  obtain ⟨-, heq⟩ := hall (Φ w) (Φ (t • v)) hV₁ ht.1 ht.2
  rw [hmul] at heq
  exact eq_div_of_mul_eq ht.2 heq

end Steps

end ZInQ.Metrization2
/-! ## metrization2: points are determined by their values on an affine open; the assembly -/

namespace ZInQ.Metrization2

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open NumberField ZInQ.DefFaltings ZInQ.Metrization Topology

section Final

variable {K : Type} [Field K] {A : AbVar K} {L : Type} [Field L] [NumberField L] [Algebra K L]
variable (𝒢 : GroupModel A L)

/-- Two complex points in `U(ℂ)`, `U` affine, with the same values on `Γ(U, 𝒪)` are equal. -/
theorem pts_eq_of_evalAt {τ : L →+* ℂ} (U : 𝒢.G.left.Opens) (hU : IsAffineOpen U)
    (p q : 𝒢.Pts τ) (hp : ⊤ ≤ p.left ⁻¹ᵁ U) (hq : ⊤ ≤ q.left ⁻¹ᵁ U)
    (h : ∀ s : Γ(𝒢.G.left, U), 𝒢.evalAt p U s = 𝒢.evalAt q U s) : p = q := by
  have hTop : IsAffineOpen (⊤ : (Spec (CommRingCat.of ℂ)).Opens) :=
    isAffineOpen_top (Spec (CommRingCat.of ℂ))
  have happ : p.left.appLE U ⊤ hp = q.left.appLE U ⊤ hq := by
    ext s
    have hs := h s
    unfold GroupModel.evalAt at hs
    rw [dif_pos hp, dif_pos hq] at hs
    exact (Scheme.ΓSpecIso (CommRingCat.of ℂ)).commRingCatIsoToRingEquiv.injective hs
  have e1 := IsAffineOpen.SpecMap_appLE_fromSpec p.left hU hTop hp
  have e2 := IsAffineOpen.SpecMap_appLE_fromSpec q.left hU hTop hq
  have e3 : hTop.fromSpec ≫ p.left = hTop.fromSpec ≫ q.left :=
    e1.symm.trans ((congrArg (fun φ => Spec.map φ ≫ hU.fromSpec) happ).trans e2)
  have hiso : IsIso hTop.fromSpec := by
    rw [IsAffineOpen.fromSpec_top]; infer_instance
  apply Over.OverMorphism.ext
  exact (cancel_epi hTop.fromSpec).mp e3

end Final

/-- **`JacDetNondegenerate` from `ProductMapLocalStructure` (proved).** If every `jacDet Φ f`
vanished, some `v ≠ 0` would be killed by the differential at `0` of every regular function near
`ξ` along `Φ` (steps 1 and 2), hence, by translation, by the differential at every point
(step 3); so on an affine `U ∋ ξ` every regular function is constant along `t ↦ Φ(t v)` for small
`t`, so `Φ(t v) = Φ 0 = 1` (points of an affine scheme are determined by their values), so
`t v ∈ Λ` for all small `t`, contradicting the discreteness of `Λ`. Neither `A.dim = g` nor
`IsZLattice ℝ Λ` is used. -/
theorem jacDetNondegenerate_of (hML : ProductMapLocalStructure) :
    ZInQ.Metrization.JacDetNondegenerate := by
  intro K _ A L _ _ _ 𝒢 τ g _ Λ hdisc Φ _ hΦ
  by_contra hcon
  push_neg at hcon
  -- step 1
  obtain ⟨v, hv0, hv⟩ := exists_null_of_det_eq_zero
    (fun t : IsLocalRing.maximalIdeal 𝒢.genStalk => fun j =>
      fderiv ℂ (𝒢.germAlong Φ (t : 𝒢.genStalk)) 0 (Pi.single j 1)) (fun f => hcon f)
  have hsingle : ∀ j : Fin g, (fun k => if j = k then (1 : ℂ) else 0) = Pi.single j 1 := by
    intro j; ext k; simp [Pi.single_apply, eq_comm]
  have hv1 : ∀ t : IsLocalRing.maximalIdeal 𝒢.genStalk,
      fderiv ℂ (𝒢.germAlong Φ (t : 𝒢.genStalk)) 0 v = 0 := by
    intro t
    rw [pi_eq_sum_univ v, map_sum]
    simp only [hsingle, map_smul, smul_eq_mul]
    rw [← hv t]
    exact Finset.sum_congr rfl fun j _ => mul_comm _ _
  -- step 2
  have hv2 := fderiv_evalAt_apply_eq_zero 𝒢 hΦ v hv1
  -- an affine open around `ξ`
  obtain ⟨U, hU, mU, -⟩ := exists_isAffineOpen_mem_and_subset
    (show 𝒢.genericUnit ∈ (⊤ : 𝒢.G.left.Opens) from trivial)
  have hdomU : IsOpen (𝒢.dom Φ U) := hΦ.2.2.2.1 U
  have h0U : (0 : Fin g → ℂ) ∈ 𝒢.dom Φ U := zero_mem_dom 𝒢 hΦ U mU
  have hcont : Continuous fun t : ℂ => t • v := continuous_id.smul continuous_const
  have hBopen : IsOpen {t : ℂ | t • v ∈ 𝒢.dom Φ U} := hdomU.preimage hcont
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp hBopen 0 (by simp [h0U])
  -- steps 3-4: every regular function on `U` is constant along the line on the ball
  have hconst : ∀ t ∈ Metric.ball (0 : ℂ) r, Φ (t • v) = Φ 0 := by
    intro t ht
    have hderiv : ∀ (s : Γ(𝒢.G.left, U)), ∀ t₀ ∈ Metric.ball (0 : ℂ) r,
        HasDerivAt (fun t : ℂ => 𝒢.evalAt (Φ (t • v)) U s) 0 t₀ := by
      intro s t₀ ht₀
      have h3 := hasDerivAt_line_zero 𝒢 hML hΦ v hv2 U s (t₀ • v) (hball ht₀)
      have h4 : HasDerivAt (fun t : ℂ => 𝒢.evalAt (Φ (t₀ • v + (t - t₀) • v)) U s) 0 t₀ := by
        have h3' : HasDerivAt (fun t : ℂ => 𝒢.evalAt (Φ (t₀ • v + t • v)) U s) 0 (t₀ - t₀) := by
          rw [sub_self]; exact h3
        exact h3'.comp_sub_const t₀ t₀
      refine h4.congr_of_eventuallyEq (Filter.Eventually.of_forall fun t => ?_)
      simp only
      rw [← add_smul, add_sub_cancel]
    apply pts_eq_of_evalAt 𝒢 U hU _ _ (hball ht) h0U
    intro s
    have := (Metric.isOpen_ball).is_const_of_deriv_eq_zero (convex_ball (0 : ℂ) r).isPreconnected
      (fun t₀ ht₀ => (hderiv s t₀ ht₀).differentiableAt.differentiableWithinAt)
      (fun t₀ ht₀ => (hderiv s t₀ ht₀).deriv) ht (Metric.mem_ball_self hr)
    simpa using this
  -- step 5: discreteness of `Λ`
  have h0 : Φ 0 = 1 := by
    have h := hΦ.1 0 0
    rw [add_zero] at h
    exact mul_left_cancel (a := Φ 0) (by rw [_root_.mul_one]; exact h.symm)
  have hmem : ∀ t ∈ Metric.ball (0 : ℂ) r, t • v ∈ Λ := fun t ht =>
    (hΦ.2.1 _).mp ((hconst t ht).trans h0)
  obtain ⟨u, hu, hpre⟩ := isOpen_induced_iff.mp (isOpen_discrete ({0} : Set Λ))
  have hu0 : (0 : Fin g → ℂ) ∈ u := by
    have : (0 : Λ) ∈ ({0} : Set Λ) := rfl
    rw [← hpre] at this
    exact this
  have hev1 : ∀ᶠ t in 𝓝 (0 : ℂ), t • v ∈ u :=
    hcont.continuousAt.preimage_mem_nhds (by rw [zero_smul]; exact hu.mem_nhds hu0)
  have hev2 : ∀ᶠ t in 𝓝 (0 : ℂ), t ∈ Metric.ball (0 : ℂ) r := Metric.ball_mem_nhds 0 hr
  have hev : ∀ᶠ t in 𝓝[≠] (0 : ℂ), t • v ∈ u ∧ t ∈ Metric.ball (0 : ℂ) r :=
    nhdsWithin_le_nhds (hev1.and hev2)
  obtain ⟨t, ⟨htu, htb⟩, ht0⟩ := (hev.and self_mem_nhdsWithin).exists
  have hin : (⟨t • v, hmem t htb⟩ : Λ) ∈ Subtype.val ⁻¹' u := htu
  rw [hpre] at hin
  have : t • v = 0 := congrArg Subtype.val hin
  rcases smul_eq_zero.mp this with h | h
  · exact ht0 h
  · exact hv0 h


end ZInQ.Metrization2

/-! ## metrization2: complex points of a group model are complex points of `A_L`

For a group model `𝒢` of `A_L` and `τ : L → ℂ`, `θ : A_L(ℂ)_τ → 𝒢(ℂ)_τ`,
`q ↦ (Spec ℂ → A_L ≅ 𝒢_L → 𝒢)`, is a group isomorphism (inverse `χ`, built from the monoidal
functor `Over.pullback (Spec L → Spec 𝓞_L)`), and evaluation of `s ∈ Γ(U, 𝒪_𝒢)` at `θ q` is
evaluation of the pulled-back section at `q`. So a uniformization of `A_L(ℂ)_τ` in leaf-push2's
sense gives one of `𝒢(ℂ)_τ` in def-faltings' sense. -/

namespace ZInQ.Metrization2

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open NumberField ZInQ.DefFaltings
open ZInQ.LeafPush2 (CPts cptObj cDom cEvalAt IsUniformization UniformizationExists)
open scoped Obj

/-- (leaf-fold2) the two abelian-variety structures of Leaves.lean, field by field (`LeafAdopt.abVarEquiv`). -/
local instance lf2AbVarCoe {K : Type} [Field K] : Coe (AbVar K) (PkgI3.AbVar K) := ⟨fun A => ⟨A.X⟩⟩
open scoped Obj

section Transport

variable {K : Type} [Field K] {A : AbVar K} {L : Type} [Field L] [NumberField L] [Algebra K L]
variable (𝒢 : GroupModel A L)

/-- `Spec L → Spec 𝓞_L`. -/
noncomputable abbrev jO (L : Type) [Field L] [NumberField L] :
    Spec (CommRingCat.of L) ⟶ Spec (CommRingCat.of (𝓞 L)) :=
  Spec.map (CommRingCat.ofHom (algebraMap (𝓞 L) L))

theorem cpt_comp_jO (τ : L →+* ℂ) :
    (cptObj τ).hom ≫ jO L = (GroupModel.ptC (L := L) τ).hom := by
  show Spec.map (CommRingCat.ofHom τ) ≫ Spec.map (CommRingCat.ofHom (algebraMap (𝓞 L) L)) =
    Spec.map (CommRingCat.ofHom (τ.comp (algebraMap (𝓞 L) L)))
  rw [← Spec.map_comp]
  rfl

/-- The projection `𝒢_L → 𝒢`. -/
noncomputable def fstG : (genericFibre L 𝒢.G).left ⟶ 𝒢.G.left := pullback.fst 𝒢.G.hom (jO L)

theorem fstG_comp_hom : fstG 𝒢 ≫ 𝒢.G.hom = (genericFibre L 𝒢.G).hom ≫ jO L :=
  pullback.condition

/-- The morphism `A_L → 𝒢` (through `gen⁻¹ : A_L ≅ 𝒢_L` and the projection `𝒢_L → 𝒢`). -/
noncomputable def toModel : (A.baseChange L).X.left ⟶ 𝒢.G.left := 𝒢.gen.inv.left ≫ fstG 𝒢

theorem toModel_comp_hom :
    (toModel 𝒢) ≫ 𝒢.G.hom = (A.baseChange L).X.hom ≫ jO L := by
  unfold toModel
  rw [Category.assoc, fstG_comp_hom, ← Category.assoc, Over.w 𝒢.gen.inv]

/-- `θ : A_L(ℂ)_τ → 𝒢(ℂ)_τ`. -/
noncomputable def theta {τ : L →+* ℂ} (q : CPts (A.baseChange L) τ) : 𝒢.Pts τ :=
  Over.homMk (q.left ≫ (toModel 𝒢))
    ((Category.assoc _ _ _).trans ((congrArg (q.left ≫ ·) (toModel_comp_hom 𝒢)).trans
      ((Category.assoc _ _ _).symm.trans ((congrArg (· ≫ jO L) (Over.w q)).trans
        (cpt_comp_jO τ)))))

theorem theta_left {τ : L →+* ℂ} (q : CPts (A.baseChange L) τ) :
    ((theta 𝒢) q).left = q.left ≫ (toModel 𝒢) := rfl

/-- The base change `(Spec ℂ)_L` of `ptC τ`. -/
noncomputable abbrev ptCL (τ : L →+* ℂ) : Over (Spec (CommRingCat.of L)) :=
  (Over.pullback (jO L)).obj (GroupModel.ptC (L := L) τ)

/-- Its projection to `Spec ℂ` (`ptC τ`'s underlying scheme). -/
noncomputable def fstC (τ : L →+* ℂ) : (ptCL τ).left ⟶ (GroupModel.ptC (L := L) τ).left :=
  pullback.fst (GroupModel.ptC (L := L) τ).hom (jO L)

/-- The section `Spec ℂ → (Spec ℂ)_L` of the base change of `ptC τ`. -/
noncomputable def secC (τ : L →+* ℂ) : cptObj τ ⟶ ptCL τ :=
  Over.homMk (pullback.lift (𝟙 (Spec (CommRingCat.of ℂ))) (cptObj τ).hom
    ((Category.id_comp _).trans (cpt_comp_jO τ).symm))
    (pullback.lift_snd _ _ _)

theorem secC_fstC (τ : L →+* ℂ) : (secC τ).left ≫ fstC τ = 𝟙 _ :=
  pullback.lift_fst _ _ _

theorem secC_snd (τ : L →+* ℂ) : (secC τ).left ≫ (ptCL τ).hom = (cptObj τ).hom :=
  pullback.lift_snd _ _ _

/-- The base change of a complex point `p` of `𝒢`, as a map to `𝒢_L`. -/
noncomputable def mapG {τ : L →+* ℂ} (p : 𝒢.Pts τ) : ptCL τ ⟶ genericFibre L 𝒢.G :=
  (Over.pullback (jO L)).map p

theorem mapG_fstG {τ : L →+* ℂ} (p : 𝒢.Pts τ) : (mapG 𝒢 p).left ≫ fstG 𝒢 = fstC τ ≫ p.left :=
  pullback.lift_fst _ _ _

theorem mapG_snd {τ : L →+* ℂ} (p : 𝒢.Pts τ) :
    (mapG 𝒢 p).left ≫ (genericFibre L 𝒢.G).hom = (ptCL τ).hom :=
  pullback.lift_snd _ _ _

/-- `χ : 𝒢(ℂ)_τ → A_L(ℂ)_τ`. -/
noncomputable def chi {τ : L →+* ℂ} (p : 𝒢.Pts τ) : CPts (A.baseChange L) τ :=
  secC τ ≫ mapG 𝒢 p ≫ 𝒢.gen.hom

theorem chi_mul {τ : L →+* ℂ} (p₁ p₂ : 𝒢.Pts τ) : (chi 𝒢) (p₁ * p₂) = (chi 𝒢) p₁ * (chi 𝒢) p₂ := by
  letI : GrpObj (genericFibre L 𝒢.G) := Functor.grpObjObj
  haveI : IsMonHom 𝒢.gen.hom := 𝒢.gen_hom
  have hm : mapG 𝒢 (p₁ * p₂) = mapG 𝒢 p₁ * mapG 𝒢 p₂ := Functor.map_mul _ _ _
  unfold chi
  rw [hm, MonObj.mul_comp, MonObj.comp_mul]

theorem gen_hom_inv_left : 𝒢.gen.hom.left ≫ 𝒢.gen.inv.left = 𝟙 _ := by
  rw [← Over.comp_left, Iso.hom_inv_id, Over.id_left]

theorem gen_inv_hom_left : 𝒢.gen.inv.left ≫ 𝒢.gen.hom.left = 𝟙 _ := by
  rw [← Over.comp_left, Iso.inv_hom_id, Over.id_left]

theorem theta_chi {τ : L →+* ℂ} (p : 𝒢.Pts τ) : (theta 𝒢) ((chi 𝒢) p) = p := by
  apply Over.OverMorphism.ext
  rw [theta_left]
  unfold chi toModel
  simp only [Over.comp_left, Category.assoc]
  rw [← Category.assoc 𝒢.gen.hom.left, gen_hom_inv_left, Category.id_comp, mapG_fstG]
  exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ p.left) (secC_fstC τ)).trans
    (Category.id_comp _))

theorem chi_theta {τ : L →+* ℂ} (q : CPts (A.baseChange L) τ) : (chi 𝒢) ((theta 𝒢) q) = q := by
  apply Over.OverMorphism.ext
  have key : (secC τ).left ≫ (mapG 𝒢 ((theta 𝒢) q)).left = q.left ≫ 𝒢.gen.inv.left := by
    apply pullback.hom_ext
    · change ((secC τ).left ≫ (mapG 𝒢 ((theta 𝒢) q)).left) ≫ fstG 𝒢 =
        (q.left ≫ 𝒢.gen.inv.left) ≫ fstG 𝒢
      rw [Category.assoc, mapG_fstG]
      exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ ((theta 𝒢) q).left)
        (secC_fstC τ)).trans ((Category.id_comp _).trans (Category.assoc _ _ _).symm))
    · change ((secC τ).left ≫ (mapG 𝒢 ((theta 𝒢) q)).left) ≫ (genericFibre L 𝒢.G).hom =
        (q.left ≫ 𝒢.gen.inv.left) ≫ (genericFibre L 𝒢.G).hom
      rw [Category.assoc, mapG_snd, secC_snd, Category.assoc, Over.w 𝒢.gen.inv, Over.w q]
  unfold chi
  simp only [Over.comp_left]
  rw [← Category.assoc, key, Category.assoc, gen_inv_hom_left, Category.comp_id]

theorem theta_mul {τ : L →+* ℂ} (q₁ q₂ : CPts (A.baseChange L) τ) :
    (theta 𝒢) (q₁ * q₂) = (theta 𝒢) q₁ * (theta 𝒢) q₂ := by
  conv_lhs => rw [← (chi_theta 𝒢) q₁, ← (chi_theta 𝒢) q₂, ← chi_mul, theta_chi]

theorem theta_injective {τ : L →+* ℂ} : Function.Injective (theta 𝒢 (τ := τ)) := fun a b h => by
  rw [← (chi_theta 𝒢) a, ← (chi_theta 𝒢) b, h]

theorem theta_surjective {τ : L →+* ℂ} : Function.Surjective (theta 𝒢 (τ := τ)) :=
  fun p => ⟨(chi 𝒢) p, (theta_chi 𝒢) p⟩

theorem theta_one {τ : L →+* ℂ} : (theta 𝒢) (1 : CPts (A.baseChange L) τ) = 1 := by
  have h := theta_mul 𝒢 (τ := τ) 1 1
  rw [_root_.mul_one] at h
  exact mul_left_cancel (a := (theta 𝒢) 1) (by rw [_root_.mul_one]; exact h.symm)

theorem evalAt_theta {τ : L →+* ℂ} (q : CPts (A.baseChange L) τ) (U : 𝒢.G.left.Opens)
    (s : Γ(𝒢.G.left, U)) :
    𝒢.evalAt ((theta 𝒢) q) U s = cEvalAt q ((toModel 𝒢) ⁻¹ᵁ U) ((toModel 𝒢).app U s) := by
  unfold GroupModel.evalAt cEvalAt
  by_cases h : ⊤ ≤ q.left ⁻¹ᵁ ((toModel 𝒢) ⁻¹ᵁ U)
  · have h' : ⊤ ≤ ((theta 𝒢) q).left ⁻¹ᵁ U := h
    rw [dif_pos h', dif_pos h]
    congr 1
  · have h' : ¬ ⊤ ≤ ((theta 𝒢) q).left ⁻¹ᵁ U := h
    rw [dif_neg h', dif_neg h]

end Transport

/-- **`AnalyticUniformizationOfDim` follows from leaf-push2's leaf `UniformizationExists`
(T35), proved.** Apply T35 to `A_L` over `L` at `σ = τ` (`dim A_L = dim A` by g0-dim's
`G0Dim.dim_baseChange`) and transport along `θ`. -/
theorem analyticUniformizationOfDim_of_uniformizationExists
    (hT : ZInQ.LeafPush2.UniformizationExists) : ZInQ.Metrization.AnalyticUniformizationOfDim := by
  intro K _ A L _ _ _ 𝒢 τ g hg
  have hgL : (A.baseChange L).dim = (g : WithBot ℕ∞) := by
    rw [← hg]
    exact G0Dim.dim_baseChange L A.X.left A.X.hom
  obtain ⟨Λ, Φ₀, hd, hZ, hmul, hker, hsurj, hopen, hdiff⟩ := hT L (A.baseChange L) τ g hgL
  refine ⟨Λ, fun z => (theta 𝒢) (Φ₀ z), hd, hZ, fun z w => ?_, fun z => ?_, ?_, fun U => ?_,
    fun U s => ?_⟩
  · simp only [hmul, theta_mul]
  · rw [← hker z, ← theta_one 𝒢 (τ := τ)]
    exact (theta_injective 𝒢).eq_iff
  · exact (theta_surjective 𝒢).comp hsurj
  · exact hopen ((toModel 𝒢) ⁻¹ᵁ U)
  · have := hdiff ((toModel 𝒢) ⁻¹ᵁ U) ((toModel 𝒢).app U s)
    refine this.congr fun z _ => ?_
    exact (evalAt_theta 𝒢) (Φ₀ z) U s

end ZInQ.Metrization2

/-! ## metrization2: toward `ProductMapLocalStructure` — evaluation at complex points of schemes,
and sums of products in a pushout of commutative rings -/

namespace ZInQ.Metrization2

open CategoryTheory AlgebraicGeometry Limits Opposite

/-- The value at a complex point `q : Spec ℂ → X` of `s ∈ Γ(X, U)` (`0` if `q ∉ U(ℂ)`). Same
formula as def-faltings' `GroupModel.evalAt` (which is `ev p.left`). -/
noncomputable def ev {X : Scheme.{0}} (q : Spec (CommRingCat.of ℂ) ⟶ X) (U : X.Opens)
    (s : Γ(X, U)) : ℂ := by
  classical
  exact if h : ⊤ ≤ q ⁻¹ᵁ U then (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom (q.appLE U ⊤ h s)
    else 0

section Ev

variable {X Y : Scheme.{0}} (q : Spec (CommRingCat.of ℂ) ⟶ X)

theorem ev_comp (f : X ⟶ Y) (U : Y.Opens) (s : Γ(Y, U)) :
    ev (q ≫ f) U s = ev q (f ⁻¹ᵁ U) (f.app U s) := by
  unfold ev
  by_cases h : ⊤ ≤ q ⁻¹ᵁ (f ⁻¹ᵁ U)
  · have h' : ⊤ ≤ (q ≫ f) ⁻¹ᵁ U := h
    rw [dif_pos h', dif_pos h]
    congr 1
  · have h' : ¬ ⊤ ≤ (q ≫ f) ⁻¹ᵁ U := h
    rw [dif_neg h', dif_neg h]

theorem ev_res {U V : X.Opens} (i : V ⟶ U) (hV : ⊤ ≤ q ⁻¹ᵁ V) (s : Γ(X, U)) :
    ev q V (X.presheaf.map i.op s) = ev q U s := by
  have hU : ⊤ ≤ q ⁻¹ᵁ U := hV.trans ((TopologicalSpace.Opens.map q.base).map i).le
  unfold ev
  rw [dif_pos hV, dif_pos hU, ← Scheme.Hom.map_appLE q hV i.op]
  rfl

theorem ev_add (U : X.Opens) (s s' : Γ(X, U)) : ev q U (s + s') = ev q U s + ev q U s' := by
  unfold ev
  split_ifs with h
  · rw [map_add]
    exact map_add (ConcreteCategory.hom (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom) _ _
  · simp

theorem ev_mul (U : X.Opens) (s s' : Γ(X, U)) : ev q U (s * s') = ev q U s * ev q U s' := by
  unfold ev
  split_ifs with h
  · rw [map_mul]
    exact map_mul (ConcreteCategory.hom (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom) _ _
  · simp

theorem ev_zero (U : X.Opens) : ev q U 0 = 0 := by
  unfold ev
  split_ifs with h
  · rw [map_zero]
    exact map_zero (ConcreteCategory.hom (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom)
  · rfl

theorem ev_one (U : X.Opens) (h : ⊤ ≤ q ⁻¹ᵁ U) : ev q U 1 = 1 := by
  unfold ev
  rw [dif_pos h, map_one]
  exact map_one (ConcreteCategory.hom (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom)

theorem ev_pow (U : X.Opens) (h : ⊤ ≤ q ⁻¹ᵁ U) (s : Γ(X, U)) (n : ℕ) :
    ev q U (s ^ n) = ev q U s ^ n := by
  induction n with
  | zero => rw [pow_zero, pow_zero, ev_one q U h]
  | succ n ih => rw [pow_succ, pow_succ, ev_mul, ih]

theorem ev_sum (U : X.Opens) {n : ℕ} (s : Fin n → Γ(X, U)) :
    ev q U (∑ k, s k) = ∑ k, ev q U (s k) := by
  induction n with
  | zero => simp [ev_zero]
  | succ n ih => rw [Fin.sum_univ_succ, Fin.sum_univ_succ, ev_add, ih]

/-- A complex point in `X.basicOpen s` gives `s` a nonzero value. -/
theorem ev_ne_zero_of_mem {U : X.Opens} (s : Γ(X, U)) (h : ⊤ ≤ q ⁻¹ᵁ X.basicOpen s) :
    ev q U s ≠ 0 := by
  have hu : IsUnit (X.presheaf.map (homOfLE (X.basicOpen_le s)).op s) :=
    X.toRingedSpace.isUnit_res_basicOpen s
  rw [← ev_res q (homOfLE (X.basicOpen_le s)) h]
  obtain ⟨u, hu'⟩ := hu
  intro h0
  have h1 := congrArg (ev q (X.basicOpen s)) u.mul_inv
  rw [ev_mul, ev_one q _ h, hu', h0, zero_mul] at h1
  exact zero_ne_one h1

/-- A complex point of `U` at which `s` has a nonzero value lies in `X.basicOpen s`. -/
theorem mem_basicOpen_of_ev_ne_zero {U : X.Opens} (s : Γ(X, U)) (hU : ⊤ ≤ q ⁻¹ᵁ U)
    (h : ev q U s ≠ 0) : ⊤ ≤ q ⁻¹ᵁ X.basicOpen s := by
  unfold ev at h
  rw [dif_pos hU] at h
  have hu : IsUnit (q.appLE U ⊤ hU s) := by
    have hu' : IsUnit ((Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom (q.appLE U ⊤ hU s)) :=
      isUnit_iff_ne_zero.mpr h
    have := hu'.map (Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv.hom
    simpa using this
  have hb := (Spec (CommRingCat.of ℂ)).basicOpen_of_isUnit hu
  rw [Scheme.Hom.preimage_basicOpen]
  have he : q.appLE U ⊤ hU s = (Spec (CommRingCat.of ℂ)).presheaf.map (homOfLE hU).op
      (q.app U s) := rfl
  rw [he, Scheme.basicOpen_res] at hb
  rw [← hb]
  exact inf_le_right

end Ev

/-- Finite sums of products `inl(α) · inr(β)`. -/
def IsSumProd {B C P : Type} [CommRing B] [CommRing C] [CommRing P] (inl : B →+* P)
    (inr : C →+* P) (r : P) : Prop :=
  ∃ (n : ℕ) (α : Fin n → B) (β : Fin n → C), r = ∑ k, inl (α k) * inr (β k)

theorem isSumProd_add {B C P : Type} [CommRing B] [CommRing C] [CommRing P] {inl : B →+* P}
    {inr : C →+* P} {r r' : P} (h : IsSumProd inl inr r) (h' : IsSumProd inl inr r') :
    IsSumProd inl inr (r + r') := by
  obtain ⟨n, α, β, rfl⟩ := h
  obtain ⟨m, α', β', rfl⟩ := h'
  refine ⟨n + m, Fin.append α α', Fin.append β β', ?_⟩
  rw [Fin.sum_univ_add]
  simp [Fin.append_left, Fin.append_right]

theorem isSumProd_mul {B C P : Type} [CommRing B] [CommRing C] [CommRing P] {inl : B →+* P}
    {inr : C →+* P} {r r' : P} (h : IsSumProd inl inr r) (h' : IsSumProd inl inr r') :
    IsSumProd inl inr (r * r') := by
  obtain ⟨n, α, β, rfl⟩ := h
  obtain ⟨m, α', β', rfl⟩ := h'
  refine ⟨n * m, fun k => α (finProdFinEquiv.symm k).1 * α' (finProdFinEquiv.symm k).2,
    fun k => β (finProdFinEquiv.symm k).1 * β' (finProdFinEquiv.symm k).2, ?_⟩
  rw [Finset.sum_mul_sum, ← Finset.sum_product', Finset.univ_product_univ]
  show _ = ∑ k, (fun p : Fin n × Fin m => inl (α p.1 * α' p.2) * inr (β p.1 * β' p.2))
    (finProdFinEquiv.symm k)
  refine Eq.trans ?_ (Equiv.sum_comp finProdFinEquiv.symm
    (fun p : Fin n × Fin m => inl (α p.1 * α' p.2) * inr (β p.1 * β' p.2))).symm
  refine Finset.sum_congr rfl fun p _ => ?_
  simp only [map_mul]
  ring

theorem isSumProd_neg {B C P : Type} [CommRing B] [CommRing C] [CommRing P] {inl : B →+* P}
    {inr : C →+* P} {r : P} (h : IsSumProd inl inr r) : IsSumProd inl inr (-r) := by
  obtain ⟨n, α, β, rfl⟩ := h
  exact ⟨n, fun k => -α k, β, by simp [Finset.sum_neg_distrib]⟩

/-- In a pushout square of commutative rings, every element of the pushout is a finite sum of
products `inl(α) · inr(β)`. -/
theorem exists_sum_of_isPushout {A B C P : CommRingCat.{0}} {f : A ⟶ B} {g : A ⟶ C}
    {inl : B ⟶ P} {inr : C ⟶ P} (h : IsPushout f g inl inr) (r : P) :
    ∃ (n : ℕ) (α : Fin n → B) (β : Fin n → C), r = ∑ k, inl (α k) * inr (β k) := by
  let T : Subring P := Subring.closure (Set.range inl.hom ∪ Set.range inr.hom)
  have hT : ∀ x ∈ T, IsSumProd inl.hom inr.hom x := by
    intro x hx
    induction hx using Subring.closure_induction with
    | mem x hx =>
      rcases hx with ⟨b, rfl⟩ | ⟨c, rfl⟩
      · exact ⟨1, fun _ => b, fun _ => 1, by simp⟩
      · exact ⟨1, fun _ => 1, fun _ => c, by simp⟩
    | zero => exact ⟨0, Fin.elim0, Fin.elim0, by simp⟩
    | one => exact ⟨1, fun _ => 1, fun _ => 1, by simp⟩
    | add x y _ _ hx hy => exact isSumProd_add hx hy
    | neg x _ hx => exact isSumProd_neg hx
    | mul x y _ _ hx hy => exact isSumProd_mul hx hy
  let jl : B ⟶ CommRingCat.of T := CommRingCat.ofHom
    (inl.hom.codRestrict T fun b => Subring.subset_closure (Or.inl ⟨b, rfl⟩))
  let jr : C ⟶ CommRingCat.of T := CommRingCat.ofHom
    (inr.hom.codRestrict T fun c => Subring.subset_closure (Or.inr ⟨c, rfl⟩))
  have w : f ≫ jl = g ≫ jr := by
    ext a
    exact congrArg (fun φ => (ConcreteCategory.hom φ) a) h.w
  let ι : CommRingCat.of T ⟶ P := CommRingCat.ofHom T.subtype
  have hid : h.desc jl jr w ≫ ι = 𝟙 P := by
    apply h.hom_ext
    · rw [h.inl_desc_assoc, Category.comp_id]; rfl
    · rw [h.inr_desc_assoc, Category.comp_id]; rfl
  have hr : r ∈ T := by
    have : ι (h.desc jl jr w r) = r := by rw [← ConcreteCategory.comp_apply, hid]; rfl
    rw [← this]
    exact ((h.desc jl jr w) r).2
  exact hT r hr

end ZInQ.Metrization2
/-! ## metrization2: `ProductMapLocalStructure`, proved

The local structure of a fibre product of schemes over an affine base at complex points
(`core_local`): affine opens `Vᵢ`, the affine scheme `Q = V₁ ×_S V₂` (an open of the product
through `j`), whose ring is the pushout `Γ(V₁) ⊗_{Γ(S)} Γ(V₂)` (`isPushout_appTop_of_isPullback`),
a basic open `D(h) ⊆ j⁻¹W` of `Q` and a fraction `t = a/h^N` on it. -/

namespace ZInQ.Metrization2

open CategoryTheory AlgebraicGeometry Limits Opposite

theorem specC_eq (z w : Spec (CommRingCat.of ℂ)) : z = w := by
  have hz : z.asIdeal = ⊥ := by
    haveI := z.isPrime; exact Ideal.eq_bot_of_prime _
  have hw : w.asIdeal = ⊥ := by
    haveI := w.isPrime; exact Ideal.eq_bot_of_prime _
  exact PrimeSpectrum.ext (hz.trans hw.symm)

theorem top_le_of_mem {X : Scheme.{0}} (q : Spec (CommRingCat.of ℂ) ⟶ X) (U : X.Opens)
    (pt : Spec (CommRingCat.of ℂ)) (h : q pt ∈ U) : ⊤ ≤ q ⁻¹ᵁ U := by
  intro z _
  rw [specC_eq z pt]
  exact h

/-- The section of `X` on `U` corresponding to a global section of `U.toScheme`. -/
noncomputable def secOf {X : Scheme.{0}} (U : X.Opens) (α : Γ(U.toScheme, ⊤)) : Γ(X, U) :=
  (inv (U.ι.appLE U ⊤ U.ι_preimage_self.ge)) α

theorem ev_secOf {X : Scheme.{0}} (U : X.Opens) (y : Spec (CommRingCat.of ℂ) ⟶ U.toScheme)
    (α : Γ(U.toScheme, ⊤)) : ev (y ≫ U.ι) U (secOf U α) = ev y ⊤ α := by
  have h1 : ⊤ ≤ (y ≫ U.ι) ⁻¹ᵁ U := by
    intro z _
    show U.ι (y z) ∈ U
    exact (y z).2
  have h2 : ⊤ ≤ y ⁻¹ᵁ (⊤ : U.toScheme.Opens) := fun _ _ => trivial
  unfold ev
  rw [dif_pos h1, dif_pos h2]
  congr 1
  rw [← Scheme.Hom.appLE_comp_appLE y U.ι U ⊤ ⊤ U.ι_preimage_self.ge h2]
  unfold secOf
  rw [← ConcreteCategory.comp_apply, ← Category.assoc, IsIso.inv_hom_id, Category.id_comp]

theorem ev_comp_top {X Y : Scheme.{0}} (q : Spec (CommRingCat.of ℂ) ⟶ X) (f : X ⟶ Y)
    (s : Γ(Y, ⊤)) : ev (q ≫ f) ⊤ s = ev q ⊤ (f.appTop s) :=
  ev_comp q f ⊤ s

section Core

variable {S X₁ X₂ : Scheme.{0}} (f₁ : X₁ ⟶ S) (f₂ : X₂ ⟶ S)

/-- **The local structure of a fibre product over an affine base, at complex points.** -/
theorem core_local [IsAffine S] (W : (pullback f₁ f₂).Opens) (t : Γ(pullback f₁ f₂, W))
    (x₁ : Spec (CommRingCat.of ℂ) ⟶ X₁) (x₂ : Spec (CommRingCat.of ℂ) ⟶ X₂)
    (hx12 : x₁ ≫ f₁ = x₂ ≫ f₂) (hx : ⊤ ≤ (pullback.lift x₁ x₂ hx12) ⁻¹ᵁ W) :
    ∃ (V₁ : X₁.Opens) (V₂ : X₂.Opens) (n : ℕ) (a c : Fin n → Γ(X₁, V₁))
      (b d : Fin n → Γ(X₂, V₂)),
      ⊤ ≤ x₁ ⁻¹ᵁ V₁ ∧ ⊤ ≤ x₂ ⁻¹ᵁ V₂ ∧
      (∑ k, ev x₁ V₁ (c k) * ev x₂ V₂ (d k)) ≠ 0 ∧
      ∀ (y₁ : Spec (CommRingCat.of ℂ) ⟶ X₁) (y₂ : Spec (CommRingCat.of ℂ) ⟶ X₂)
        (hy : y₁ ≫ f₁ = y₂ ≫ f₂), ⊤ ≤ y₁ ⁻¹ᵁ V₁ → ⊤ ≤ y₂ ⁻¹ᵁ V₂ →
        (∑ k, ev y₁ V₁ (c k) * ev y₂ V₂ (d k)) ≠ 0 →
        ⊤ ≤ (pullback.lift y₁ y₂ hy) ⁻¹ᵁ W ∧
        ev (pullback.lift y₁ y₂ hy) W t * (∑ k, ev y₁ V₁ (c k) * ev y₂ V₂ (d k)) =
          ∑ k, ev y₁ V₁ (a k) * ev y₂ V₂ (b k) := by
  obtain ⟨pt⟩ : Nonempty (Spec (CommRingCat.of ℂ)) := inferInstance
  have hpt : pt ∈ (⊤ : (Spec (CommRingCat.of ℂ)).Opens) := trivial
  obtain ⟨V₁, hV₁, m₁, -⟩ := exists_isAffineOpen_mem_and_subset
    (show x₁ pt ∈ (⊤ : X₁.Opens) from trivial)
  obtain ⟨V₂, hV₂, m₂, -⟩ := exists_isAffineOpen_mem_and_subset
    (show x₂ pt ∈ (⊤ : X₂.Opens) from trivial)
  haveI : IsAffine V₁.toScheme := hV₁
  haveI : IsAffine V₂.toScheme := hV₂
  set g₁ := V₁.ι ≫ f₁ with hg₁
  set g₂ := V₂.ι ≫ f₂ with hg₂
  let j : pullback g₁ g₂ ⟶ pullback f₁ f₂ :=
    pullback.map g₁ g₂ f₁ f₂ V₁.ι V₂.ι (𝟙 S) (by simp [hg₁]) (by simp [hg₂])
  have hj1 : j ≫ pullback.fst f₁ f₂ = pullback.fst g₁ g₂ ≫ V₁.ι := pullback.lift_fst _ _ _
  have hj2 : j ≫ pullback.snd f₁ f₂ = pullback.snd g₁ g₂ ≫ V₂.ι := pullback.lift_snd _ _ _
  -- complex points of `V₁ × V₂` lift to `Q`
  have lift_pt : ∀ (y₁ : Spec (CommRingCat.of ℂ) ⟶ X₁) (y₂ : Spec (CommRingCat.of ℂ) ⟶ X₂)
      (hy : y₁ ≫ f₁ = y₂ ≫ f₂), ⊤ ≤ y₁ ⁻¹ᵁ V₁ → ⊤ ≤ y₂ ⁻¹ᵁ V₂ →
      ∃ yQ : Spec (CommRingCat.of ℂ) ⟶ pullback g₁ g₂, yQ ≫ j = pullback.lift y₁ y₂ hy ∧
        yQ ≫ pullback.fst g₁ g₂ ≫ V₁.ι = y₁ ∧ yQ ≫ pullback.snd g₁ g₂ ≫ V₂.ι = y₂ := by
    intro y₁ y₂ hy h1 h2
    have r1 : Set.range y₁ ⊆ Set.range V₁.ι := by
      rw [Scheme.Opens.range_ι]; rintro _ ⟨z, rfl⟩; exact h1 (show z ∈ ⊤ from trivial)
    have r2 : Set.range y₂ ⊆ Set.range V₂.ι := by
      rw [Scheme.Opens.range_ι]; rintro _ ⟨z, rfl⟩; exact h2 (show z ∈ ⊤ from trivial)
    let z₁ := IsOpenImmersion.lift V₁.ι y₁ r1
    let z₂ := IsOpenImmersion.lift V₂.ι y₂ r2
    have hz₁ : z₁ ≫ V₁.ι = y₁ := IsOpenImmersion.lift_fac _ _ _
    have hz₂ : z₂ ≫ V₂.ι = y₂ := IsOpenImmersion.lift_fac _ _ _
    have hc : z₁ ≫ g₁ = z₂ ≫ g₂ := by
      rw [hg₁, hg₂, ← Category.assoc, hz₁, ← Category.assoc, hz₂, hy]
    refine ⟨pullback.lift z₁ z₂ hc, ?_, ?_, ?_⟩
    · apply pullback.hom_ext
      · rw [Category.assoc, hj1, pullback.lift_fst, pullback.lift_fst_assoc, hz₁]
      · rw [Category.assoc, hj2, pullback.lift_snd, pullback.lift_snd_assoc, hz₂]
    · rw [pullback.lift_fst_assoc, hz₁]
    · rw [pullback.lift_snd_assoc, hz₂]
  obtain ⟨xQ, hxQ, -, -⟩ := lift_pt x₁ x₂ hx12 (top_le_of_mem _ _ pt m₁)
    (top_le_of_mem _ _ pt m₂)
  have hxQW : xQ pt ∈ j ⁻¹ᵁ W := by
    have := hx hpt
    rw [← hxQ] at this
    exact this
  obtain ⟨h, hhW, hhx⟩ := (isAffineOpen_top (pullback g₁ g₂)).exists_basicOpen_le
    (V := j ⁻¹ᵁ W) ⟨xQ pt, hxQW⟩ trivial
  -- the fraction
  set tQ : Γ(pullback g₁ g₂, (pullback g₁ g₂).basicOpen h) :=
    (pullback g₁ g₂).presheaf.map (homOfLE hhW).op (j.app W t) with htQ
  obtain ⟨⟨a0, ⟨_, N, rfl⟩⟩, heq⟩ := IsLocalization.surj (Submonoid.powers h) tQ
  have hal : ∀ r : Γ(pullback g₁ g₂, ⊤),
      algebraMap Γ(pullback g₁ g₂, ⊤) Γ(pullback g₁ g₂, (pullback g₁ g₂).basicOpen h) r =
        (pullback g₁ g₂).presheaf.map (homOfLE ((pullback g₁ g₂).basicOpen_le h)).op r :=
    fun _ => rfl
  have heq' : tQ * (pullback g₁ g₂).presheaf.map (homOfLE ((pullback g₁ g₂).basicOpen_le h)).op
      (h ^ (N + 1)) = (pullback g₁ g₂).presheaf.map
        (homOfLE ((pullback g₁ g₂).basicOpen_le h)).op (a0 * h) := by
    simp only at heq
    rw [← hal, ← hal, pow_succ, map_mul, map_mul, ← mul_assoc, heq]
  -- sums of products
  have hpo := isPushout_appTop_of_isPullback (IsPullback.of_hasPullback g₁ g₂)
  obtain ⟨n₁, α, β, hα⟩ := exists_sum_of_isPushout hpo (a0 * h)
  obtain ⟨n₂, γ, δ, hγ⟩ := exists_sum_of_isPushout hpo (h ^ (N + 1))
  -- evaluation of a sum of products at a lifted point
  have key : ∀ (yQ : Spec (CommRingCat.of ℂ) ⟶ pullback g₁ g₂) {m : ℕ}
      (u : Fin m → Γ(V₁.toScheme, ⊤)) (v : Fin m → Γ(V₂.toScheme, ⊤)),
      (∑ k, ev (yQ ≫ pullback.fst g₁ g₂ ≫ V₁.ι) V₁ (secOf V₁ (u k)) *
        ev (yQ ≫ pullback.snd g₁ g₂ ≫ V₂.ι) V₂ (secOf V₂ (v k))) =
      ev yQ ⊤ (∑ k, (pullback.fst g₁ g₂).appTop (u k) * (pullback.snd g₁ g₂).appTop (v k)) := by
    intro yQ m u v
    rw [ev_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [ev_mul, ← Category.assoc, ev_secOf, ← Category.assoc, ev_secOf, ev_comp_top,
      ev_comp_top]
  let a : Fin (n₁ + n₂) → Γ(X₁, V₁) := Fin.append (fun k => secOf V₁ (α k)) 0
  let b : Fin (n₁ + n₂) → Γ(X₂, V₂) := Fin.append (fun k => secOf V₂ (β k)) 0
  let c : Fin (n₁ + n₂) → Γ(X₁, V₁) := Fin.append 0 (fun k => secOf V₁ (γ k))
  let d : Fin (n₁ + n₂) → Γ(X₂, V₂) := Fin.append 0 (fun k => secOf V₂ (δ k))
  have hA : ∀ (yQ : Spec (CommRingCat.of ℂ) ⟶ pullback g₁ g₂),
      (∑ k, ev (yQ ≫ pullback.fst g₁ g₂ ≫ V₁.ι) V₁ (a k) *
        ev (yQ ≫ pullback.snd g₁ g₂ ≫ V₂.ι) V₂ (b k)) = ev yQ ⊤ (a0 * h) := by
    intro yQ
    rw [Fin.sum_univ_add]
    simp only [a, b, Fin.append_left, Fin.append_right, Pi.zero_apply, ev_zero, mul_zero,
      Finset.sum_const_zero, add_zero]
    rw [key, hα]
  have hH : ∀ (yQ : Spec (CommRingCat.of ℂ) ⟶ pullback g₁ g₂),
      (∑ k, ev (yQ ≫ pullback.fst g₁ g₂ ≫ V₁.ι) V₁ (c k) *
        ev (yQ ≫ pullback.snd g₁ g₂ ≫ V₂.ι) V₂ (d k)) = ev yQ ⊤ h ^ (N + 1) := by
    intro yQ
    rw [Fin.sum_univ_add]
    simp only [c, d, Fin.append_left, Fin.append_right, Pi.zero_apply, ev_zero, zero_mul,
      Finset.sum_const_zero, zero_add]
    rw [key, ← hγ, ev_pow yQ ⊤ (fun _ _ => trivial)]
  refine ⟨V₁, V₂, n₁ + n₂, a, c, b, d, top_le_of_mem _ _ pt m₁, top_le_of_mem _ _ pt m₂, ?_, ?_⟩
  · obtain ⟨xQ', hxQ', e1, e2⟩ := lift_pt x₁ x₂ hx12 (top_le_of_mem _ _ pt m₁)
      (top_le_of_mem _ _ pt m₂)
    have hxQ'h : ⊤ ≤ xQ' ⁻¹ᵁ (pullback g₁ g₂).basicOpen h := by
      have hjinj : xQ' = xQ := by
        apply pullback.hom_ext
        · apply (cancel_mono V₁.ι).mp
          rw [Category.assoc, Category.assoc, e1, ← hj1, ← Category.assoc, hxQ,
            pullback.lift_fst]
        · apply (cancel_mono V₂.ι).mp
          rw [Category.assoc, Category.assoc, e2, ← hj2, ← Category.assoc, hxQ,
            pullback.lift_snd]
      rw [hjinj]
      exact top_le_of_mem _ _ pt hhx
    rw [← e1, ← e2, hH]
    exact pow_ne_zero _ (ev_ne_zero_of_mem xQ' h hxQ'h)
  · intro y₁ y₂ hy h1 h2 hne
    obtain ⟨yQ, hyQ, e1, e2⟩ := lift_pt y₁ y₂ hy h1 h2
    subst e1 e2
    rw [hH] at hne ⊢
    rw [hA]
    have hev : ev yQ ⊤ h ≠ 0 := fun h0 => hne (by rw [h0, zero_pow (Nat.succ_ne_zero N)])
    have hmem : ⊤ ≤ yQ ⁻¹ᵁ (pullback g₁ g₂).basicOpen h :=
      mem_basicOpen_of_ev_ne_zero yQ h (fun _ _ => trivial) hev
    have hW : ⊤ ≤ yQ ⁻¹ᵁ (j ⁻¹ᵁ W) := hmem.trans ((TopologicalSpace.Opens.map yQ.base).map
      (homOfLE hhW)).le
    refine ⟨?_, ?_⟩
    · rw [← hyQ]; exact hW
    · rw [← hyQ, ev_comp, ← ev_res yQ (homOfLE hhW) hmem, ← htQ,
        ← ev_pow yQ ⊤ (fun _ _ => trivial),
        ← ev_res yQ (homOfLE ((pullback g₁ g₂).basicOpen_le h)) hmem (h ^ (N + 1)),
        ← ev_mul, heq', ev_res yQ _ hmem]

end Core

end ZInQ.Metrization2
/-! ## metrization2: `ProductMapLocalStructure`, hence `JacDetNondegenerate` and
`ProductLocalStructure`, proved -/

namespace ZInQ.Metrization2

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open NumberField ZInQ.DefFaltings

/-- **`ProductMapLocalStructure`, proved** (from `core_local` with `S = Spec 𝓞_L`,
`W = m⁻¹(U)`, `t = m^*s`). -/
theorem productMapLocalStructure : ProductMapLocalStructure := by
  intro K _ A B C L _ _ _ ℋ 𝒢₁ 𝒢₂ m τ U s p₁ p₂ hp
  have hw : ∀ (p₁' : 𝒢₁.Pts τ) (p₂' : 𝒢₂.Pts τ), p₁'.left ≫ 𝒢₁.G.hom = p₂'.left ≫ 𝒢₂.G.hom :=
    fun p₁' p₂' => (Over.w p₁').trans (Over.w p₂').symm
  obtain ⟨V₁, V₂, n, a, c, b, d, h1, h2, hne, hall⟩ :=
    core_local 𝒢₁.G.hom 𝒢₂.G.hom (m.left ⁻¹ᵁ U) (m.left.app U s) p₁.left p₂.left (hw p₁ p₂) hp
  refine ⟨V₁, V₂, n, a, c, b, d, h1, h2, hne, fun p₁' p₂' h1' h2' hne' => ?_⟩
  obtain ⟨hmem, heq⟩ := hall p₁'.left p₂'.left (hw p₁' p₂') h1' h2' hne'
  refine ⟨hmem, ?_⟩
  have hev : ℋ.evalAt (lift p₁' p₂' ≫ m) U s =
      ev (pullback.lift p₁'.left p₂'.left (hw p₁' p₂')) (m.left ⁻¹ᵁ U) (m.left.app U s) :=
    ev_comp (pullback.lift p₁'.left p₂'.left (hw p₁' p₂')) m.left U s
  rw [hev]
  exact heq

/-- **`JacDetNondegenerate`, proved** (no hypotheses). -/
theorem jacDetNondegenerate : ZInQ.Metrization.JacDetNondegenerate :=
  jacDetNondegenerate_of productMapLocalStructure

/-- **metrization's `ProductLocalStructure`, proved** (no hypotheses). -/
theorem productLocalStructure : ZInQ.Metrization.ProductLocalStructure :=
  productLocalStructure_of productMapLocalStructure

end ZInQ.Metrization2




/-! # unif-dims: the 2-torsion of `ℂ^g/Λ` has `4^g` elements (Mathlib only)

If `Φ : ℂ^g → G` is a surjective homomorphism onto a group with kernel a discrete full `ℤ`-lattice
`Λ`, then `#{p ∈ G | p² = 1} = 2^(2g)`. Hence the dimension `g` of such a "uniformization" is
determined by the abstract group `G`. -/

namespace ZInQ.UnifDims

open Module

variable {G : Type*} [Group G] {g : ℕ}

/-- The additive homomorphism `λ ↦ Φ(λ/2)` from the lattice to `G`. -/
noncomputable def halfHom (Φ : (Fin g → ℂ) → G) (Λ : Submodule ℤ (Fin g → ℂ))
    (hmul : ∀ z w, Φ (z + w) = Φ z * Φ w) : Λ →+ Additive G :=
  AddMonoidHom.mk' (fun l => Additive.ofMul (Φ ((1 / 2 : ℂ) • (l : Fin g → ℂ)))) (by
    intro a b
    simp only [Submodule.coe_add, smul_add, hmul]
    rfl)

/-- **The 2-torsion of a uniformized group.** -/
theorem card_twoTorsion (Φ : (Fin g → ℂ) → G) (Λ : Submodule ℤ (Fin g → ℂ)) [DiscreteTopology Λ]
    [IsZLattice ℝ Λ] (hmul : ∀ z w, Φ (z + w) = Φ z * Φ w) (hker : ∀ z, Φ z = 1 ↔ z ∈ Λ)
    (hsurj : Function.Surjective Φ) : Nat.card {p : G // p * p = 1} = 2 ^ (2 * g) := by
  set ψ := halfHom Φ Λ hmul
  -- rank of `Λ`
  have hrank : finrank ℤ Λ = 2 * g := by
    rw [ZLattice.rank ℝ Λ, Module.finrank_pi_fintype]
    simp [Complex.finrank_real_complex, mul_comm]
  let b := Module.finBasisOfFinrankEq ℤ Λ hrank
  -- `Λ ⧸ ker ψ ≃ range ψ ≃ G[2]`
  have hrange : ∀ p : G, p * p = 1 ↔ Additive.ofMul p ∈ ψ.range := by
    intro p
    constructor
    · intro hp
      obtain ⟨z, rfl⟩ := hsurj p
      have h2 : (2 : ℂ) • z ∈ Λ := by
        rw [← hker, two_smul, hmul, hp]
      refine ⟨⟨_, h2⟩, ?_⟩
      show Additive.ofMul (Φ ((1 / 2 : ℂ) • (2 : ℂ) • z)) = _
      rw [smul_smul]
      norm_num
    · rintro ⟨l, hl⟩
      have hl' : Φ ((1 / 2 : ℂ) • (l : Fin g → ℂ)) = p := hl
      rw [← hl', ← hmul, ← add_smul]
      norm_num
      exact (hker _).mpr l.2
  have hker' : ψ.ker = (AddSubgroup.pi Set.univ (fun _ : Fin (2 * g) =>
      AddSubgroup.zmultiples (2 : ℤ))).comap b.equivFun.toLinearMap.toAddMonoidHom := by
    ext l
    simp only [AddMonoidHom.mem_ker, AddSubgroup.mem_comap, AddSubgroup.mem_pi, Set.mem_univ,
      true_implies, Int.mem_zmultiples_iff]
    show Φ ((1 / 2 : ℂ) • (l : Fin g → ℂ)) = 1 ↔ _
    rw [hker]
    constructor
    · intro h i
      set μ : Λ := ⟨_, h⟩
      have hl : l = (2 : ℤ) • μ := by
        ext1
        simp only [SetLike.val_smul, μ]
        rw [← Int.cast_smul_eq_zsmul ℂ, smul_smul]
        norm_num
      refine ⟨b.equivFun μ i, ?_⟩
      have := congrArg (fun x => b.equivFun x i) hl
      simp only [LinearEquiv.map_smul, Pi.smul_apply, smul_eq_mul] at this
      exact this
    · intro h
      choose d hd using h
      let μ : Λ := b.equivFun.symm d
      have hl : l = (2 : ℤ) • μ := by
        apply b.equivFun.injective
        ext i
        simp only [LinearEquiv.map_smul, Pi.smul_apply, smul_eq_mul, μ,
          LinearEquiv.apply_symm_apply]
        exact hd i
      have : (1 / 2 : ℂ) • (l : Fin g → ℂ) = (μ : Fin g → ℂ) := by
        rw [hl, SetLike.val_smul, ← Int.cast_smul_eq_zsmul ℂ, smul_smul]
        norm_num
      rw [this]
      exact μ.2
  have hidx : ψ.ker.index = 2 ^ (2 * g) := by
    rw [hker', AddSubgroup.index_comap_of_surjective _ b.equivFun.surjective,
      AddSubgroup.index_pi]
    simp [Int.index_zmultiples]
  calc Nat.card {p : G // p * p = 1}
      = Nat.card ψ.range := Nat.card_congr
        (Equiv.subtypeEquiv Additive.ofMul (fun p => hrange p))
    _ = Nat.card (Λ ⧸ ψ.ker) := Nat.card_congr (QuotientAddGroup.quotientKerEquivRange ψ).toEquiv.symm
    _ = 2 ^ (2 * g) := hidx

/-- **The dimension of a uniformization is determined by the group.** -/
theorem dim_eq_of_unif {g g' : ℕ} (Φ : (Fin g → ℂ) → G) (Λ : Submodule ℤ (Fin g → ℂ))
    (Φ' : (Fin g' → ℂ) → G) (Λ' : Submodule ℤ (Fin g' → ℂ))
    (hd : DiscreteTopology Λ) (hz : IsZLattice ℝ Λ) (hd' : DiscreteTopology Λ')
    (hz' : IsZLattice ℝ Λ')
    (hmul : ∀ z w, Φ (z + w) = Φ z * Φ w) (hker : ∀ z, Φ z = 1 ↔ z ∈ Λ)
    (hsurj : Function.Surjective Φ)
    (hmul' : ∀ z w, Φ' (z + w) = Φ' z * Φ' w) (hker' : ∀ z, Φ' z = 1 ↔ z ∈ Λ')
    (hsurj' : Function.Surjective Φ') : g = g' := by
  have h1 := card_twoTorsion Φ Λ hmul hker hsurj
  have h2 := card_twoTorsion Φ' Λ' hmul' hker' hsurj'
  rw [h1] at h2
  have := Nat.pow_right_injective (le_refl 2) h2
  omega

end ZInQ.UnifDims


/-! ## unif-dims: `ProductUnifDims` from T35 (`UniformizationExists`)

The dimension half (`ProductUnifDimsEq`) holds because the dimension of an analytic uniformization
of `𝒢(ℂ)_τ` is determined by the group `𝒢(ℂ)_τ` (its 2-torsion has `4^g` elements,
`ZInQ.UnifDims.dim_eq_of_unif`), and T35 supplies one uniformization of dimension `dim A`
(`AnalyticUniformizationOfDim`, metrization2's transport of T35 to group models). The
nonsingularity half is metrization2's `jacDetNondegenerate` (proved, no hypotheses). The product
structure and the metrization `MP` are not used. -/

namespace ZInQ.UnifDims

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open NumberField ZInQ.DefFaltings

/-- An abelian variety has finite dimension (copied from metrization's `abVar_dim_finite`). -/
theorem abVar_dim_finite (K : Type) [Field K] (A : AbVar K) :
    ∃ n : ℕ, A.dim = (n : WithBot ℕ∞) := by
  haveI : Nonempty A.X.left :=
    ⟨η[A.X].left (Nonempty.some (inferInstance : Nonempty (Spec (CommRingCat.of K))))⟩
  exact G0Dim.dim_finite A.X.left A.X.hom

/-- **The dimension of an analytic uniformization is `dim A`** (from `AnalyticUniformizationOfDim`,
i.e. from T35). Any full-lattice analytic uniformization `Φ : ℂ^g → 𝒢(ℂ)_τ` has `g = dim A`. Only
the algebraic clauses (homomorphism, kernel, onto) of the two uniformizations are used. -/
theorem dim_eq_of_isAnalyticUniformization (hU : ZInQ.Metrization.AnalyticUniformizationOfDim)
    {K : Type} [Field K] {A : AbVar K} {L : Type} [Field L] [NumberField L] [Algebra K L]
    (𝒢 : GroupModel A L) (τ : L →+* ℂ) {g : ℕ} (Λ : Submodule ℤ (Fin g → ℂ))
    (Φ : (Fin g → ℂ) → 𝒢.Pts τ) (hd : DiscreteTopology Λ) (hz : IsZLattice ℝ Λ)
    (hΦ : 𝒢.IsAnalyticUniformization τ Λ Φ) : A.dim = (g : WithBot ℕ∞) := by
  obtain ⟨n, hn⟩ := abVar_dim_finite K A
  obtain ⟨Λ', Φ', hd', hz', hΦ'⟩ := hU K A L 𝒢 τ n hn
  have := dim_eq_of_unif Φ Λ Φ' Λ' hd hz hd' hz' hΦ.1 hΦ.2.1 hΦ.2.2.1 hΦ'.1 hΦ'.2.1 hΦ'.2.2.1
  rw [hn, this]

/-- **`ProductUnifDimsEq` from `AnalyticUniformizationOfDim` (proved).** -/
theorem productUnifDimsEq_of (hU : ZInQ.Metrization.AnalyticUniformizationOfDim) :
    ZInQ.ProductUnif.ProductUnifDimsEq := by
  intro K _ A B C L _ _ _ 𝒢₁ 𝒢₂ g MP e _ _ τ g₁ g₂ hg Λ₁ Λ₂ Φ₁ Φ₂ hl₁ hl₂ hu₁ hu₂ _ _
  obtain ⟨hd₁, hz₁⟩ := hl₁
  obtain ⟨hd₂, hz₂⟩ := hl₂
  exact ⟨dim_eq_of_isAnalyticUniformization hU 𝒢₁ τ Λ₁ Φ₁ hd₁ hz₁ hu₁,
    dim_eq_of_isAnalyticUniformization hU 𝒢₂ τ Λ₂ Φ₂ hd₂ hz₂ hu₂⟩

/-- **`ProductUnifDims` from `AnalyticUniformizationOfDim` (proved).** -/
theorem productUnifDims_of_unifOfDim (hU : ZInQ.Metrization.AnalyticUniformizationOfDim) :
    ZInQ.ProductUnif.ProductUnifDims :=
  ZInQ.ProductUnif.productUnifDims_of (productUnifDimsEq_of hU)
    ZInQ.Metrization2.jacDetNondegenerate

/-- **`ProductUnifDims` from the textbook leaf T35 `UniformizationExists` (proved).** -/
theorem productUnifDims_of_uniformizationExists (hT : ZInQ.LeafPush2.UniformizationExists) :
    ZInQ.ProductUnif.ProductUnifDims :=
  productUnifDims_of_unifOfDim
    (ZInQ.Metrization2.analyticUniformizationOfDim_of_uniformizationExists hT)

end ZInQ.UnifDims




/-! # unif-dims: `DetLatticeProd` (determinant lattice of a direct sum), proof attempt -/

namespace ZInQ.UnifDims

open NumberField TensorProduct ZInQ.DefFaltings ZInQ.DefFaltings.HodgeLattice
open scoped nonZeroDivisors

section Line

variable {K : Type} [Field K] [NumberField K]
variable {M : Type} [AddCommGroup M] [Module (𝓞 K) M]

/-- The determinant functional `K ⊗ ⋀^g M → K` of a `K`-basis of `K ⊗ M`. -/
noncomputable def detFun {g : ℕ} (b : Module.Basis (Fin g) K (K ⊗[𝓞 K] M)) :
    (K ⊗[𝓞 K] ⋀[𝓞 K]^g M) →ₗ[K] K :=
  (exteriorPower.alternatingMapLinearEquiv
    ({ toMultilinearMap := (b.det.toMultilinearMap.restrictScalars (𝓞 K)).compLinearMap
          (fun _ => TensorProduct.mk (𝓞 K) K M 1)
       map_eq_zero_of_eq' := fun v i j hv hij =>
          b.det.map_eq_zero_of_eq (fun k => (1 : K) ⊗ₜ[𝓞 K] v k) (by simp [hv]) hij } :
      M [⋀^Fin g]→ₗ[𝓞 K] K)).liftBaseChange K

theorem detFun_tmul {g : ℕ} (b : Module.Basis (Fin g) K (K ⊗[𝓞 K] M)) (v : Fin g → M) :
    detFun b ((1 : K) ⊗ₜ[𝓞 K] exteriorPower.ιMulti (𝓞 K) g v) =
      b.det (fun k => (1 : K) ⊗ₜ[𝓞 K] v k) := by
  simp only [detFun, LinearMap.liftBaseChange_one_tmul,
    exteriorPower.alternatingMapLinearEquiv_apply_ιMulti]
  rfl

/-- The determinant functional of a basis `1 ⊗ wⱼ` is injective (the Hodge space is the line
spanned by `1 ⊗ ∧w`); steps 2-4 of hodge-lattice's `hodgeLattice_of_lattice`. -/
theorem detFun_injective {g : ℕ} (b : Module.Basis (Fin g) K (K ⊗[𝓞 K] M)) (w : Fin g → M)
    (hbw : ∀ j, (1 : K) ⊗ₜ[𝓞 K] w j = b j) : Function.Injective (detFun b) := by
  have hclear := exists_clear (K := K) w (fun v => by
    have hr : Set.range (fun j => (1 : K) ⊗ₜ[𝓞 K] w j) = Set.range b := by
      rw [show (fun j => (1 : K) ⊗ₜ[𝓞 K] w j) = b from funext hbw]
    rw [hr, b.span_eq]; exact Submodule.mem_top)
  set s0 : K ⊗[𝓞 K] ⋀[𝓞 K]^g M := (1 : K) ⊗ₜ[𝓞 K] exteriorPower.ιMulti (𝓞 K) g w with hs0
  have hone : ∀ x : ⋀[𝓞 K]^g M, (1 : K) ⊗ₜ[𝓞 K] x ∈ Submodule.span K {s0} := by
    intro x
    have hx : x ∈ Submodule.span (𝓞 K) (Set.range (exteriorPower.ιMulti (𝓞 K) g)) := by
      rw [exteriorPower.ιMulti_span]; exact Submodule.mem_top
    induction hx using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨v, rfl⟩ := hy
      exact tmul_ιMulti_mem_span w hclear v
    | zero => rw [TensorProduct.tmul_zero]; exact Submodule.zero_mem _
    | add y z _ _ hy hz => rw [TensorProduct.tmul_add]; exact Submodule.add_mem _ hy hz
    | smul r y _ hy =>
      rw [TensorProduct.tmul_smul]; exact Submodule.smul_of_tower_mem _ r hy
  have htop : Submodule.span K {s0} = ⊤ := by
    rw [eq_top_iff]
    rintro h -
    induction h using TensorProduct.induction_on with
    | zero => exact Submodule.zero_mem _
    | tmul k x =>
      have : k ⊗ₜ[𝓞 K] x = k • ((1 : K) ⊗ₜ[𝓞 K] x) := by
        rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
      rw [this]; exact Submodule.smul_mem _ k (hone x)
    | add x y hx hy => exact Submodule.add_mem _ hx hy
  have hΨ : detFun b s0 = 1 := by
    rw [hs0, detFun_tmul, show (fun k => (1 : K) ⊗ₜ[𝓞 K] w k) = b from funext hbw,
      Module.Basis.det_self]
  rw [← LinearMap.ker_eq_bot, eq_bot_iff]
  intro x hx
  have : x ∈ Submodule.span K {s0} := htop ▸ Submodule.mem_top
  obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp this
  rw [LinearMap.mem_ker, map_smul, hΨ, smul_eq_mul, mul_one] at hx
  rw [hx, zero_smul]
  exact Submodule.zero_mem _

/-- Step 1 of hodge-lattice's `hodgeLattice_of_lattice`: a `K`-basis of `K ⊗ M` of the form
`1 ⊗ wⱼ` with `wⱼ ∈ ω`. -/
theorem exists_basis_of_span {g : ℕ} (ω : Submodule (𝓞 K) M)
    (hrank : Module.rank K (K ⊗[𝓞 K] M) = g)
    (hspan : Submodule.span K (Set.range fun x : ω => (1 : K) ⊗ₜ[𝓞 K] (x : M)) = ⊤) :
    ∃ (w : Fin g → ω) (b : Module.Basis (Fin g) K (K ⊗[𝓞 K] M)),
      ∀ j, (1 : K) ⊗ₜ[𝓞 K] (w j : M) = b j := by
  classical
  set V := K ⊗[𝓞 K] M
  set f : ω → V := fun x => (1 : K) ⊗ₜ[𝓞 K] (x : M) with hf
  have : FiniteDimensional K V := Module.finite_of_rank_eq_nat hrank
  have hfin : Module.finrank K V = g := Module.finrank_eq_of_rank_eq hrank
  obtain ⟨s, hs_sub, hs_span, hs_li⟩ := exists_linearIndependent K (Set.range f)
  let bs : Module.Basis s K V := Module.Basis.mk hs_li (by
    rw [Subtype.range_coe, hs_span, hspan])
  let b : Module.Basis (Fin g) K V :=
    bs.reindex (bs.indexEquiv (Module.finBasisOfFinrankEq K V hfin))
  have hmem : ∀ j, ∃ x : ω, f x = b j := fun j => by
    have : (b j : V) ∈ s := by
      simp only [b, Module.Basis.reindex_apply, bs, Module.Basis.coe_mk]
      exact Subtype.mem _
    exact hs_sub this
  choose w hw using hmem
  exact ⟨w, b, hw⟩

/-- `secIndex` is invariant under an injective `K`-linear map. -/
theorem secIndex_map {V : Type*} [AddCommGroup V] [Module K V] [Module (𝓞 K) V]
    [IsScalarTower (𝓞 K) K V] (Ψ : V →ₗ[K] K) (hΨ : Function.Injective Ψ)
    (Λ : Submodule (𝓞 K) V) (s : V) :
    secIndex Λ s = secIndex (Λ.map (Ψ.restrictScalars (𝓞 K))) (Ψ s) := by
  unfold secIndex
  have hspan : Submodule.map (Ψ.restrictScalars (𝓞 K)) (Submodule.span (𝓞 K) {s}) =
      Submodule.span (𝓞 K) {Ψ s} := by
    rw [Submodule.map_span, Set.image_singleton]; rfl
  rw [← hspan, Submodule.map_toAddSubgroup, Submodule.map_toAddSubgroup]
  exact (AddSubgroup.relIndex_map_map_of_injective _ _
    (f := ((Ψ.restrictScalars (𝓞 K)) : V →+ K)) hΨ).symm

/-- **Indices of `1` multiply** in a product of finitely generated `𝓞_K`-submodules of `K`
containing `1` (through `FractionalIdeal.absNorm` and the kernel's `secIndex_mul_absNorm`). -/
theorem secIndex_one_mul (I J : Submodule (𝓞 K) K) (hI : I.FG) (hJ : J.FG) (h1I : (1 : K) ∈ I)
    (h1J : (1 : K) ∈ J) : secIndex (I * J) 1 = secIndex I 1 * secIndex J 1 := by
  let I' : FractionalIdeal (𝓞 K)⁰ K := ⟨I, FractionalIdeal.isFractional_of_fg hI⟩
  let J' : FractionalIdeal (𝓞 K)⁰ K := ⟨J, FractionalIdeal.isFractional_of_fg hJ⟩
  have hIJ : ((I' * J' : FractionalIdeal (𝓞 K)⁰ K) : Submodule (𝓞 K) K) = I * J :=
    FractionalIdeal.coe_mul _ _
  have h1 : (1 : K) ∈ (I' * J' : FractionalIdeal (𝓞 K)⁰ K) := by
    rw [← FractionalIdeal.mem_coe, hIJ, ← mul_one (1 : K)]
    exact Submodule.mul_mem_mul h1I h1J
  have e1 := secIndex_mul_absNorm I' h1I one_ne_zero
  have e2 := secIndex_mul_absNorm J' h1J one_ne_zero
  have e3 := secIndex_mul_absNorm (I' * J') h1 one_ne_zero
  rw [hIJ] at e3
  simp only [map_one, abs_one, map_mul] at e1 e2 e3
  have : (secIndex (I * J) 1 : ℚ) = secIndex I 1 * secIndex J 1 := by
    have hI0 : FractionalIdeal.absNorm I' ≠ 0 := by
      intro h; rw [h, mul_zero] at e1; exact zero_ne_one e1
    have hJ0 : FractionalIdeal.absNorm J' ≠ 0 := by
      intro h; rw [h, mul_zero] at e2; exact zero_ne_one e2
    change (secIndex (I * J) 1 : ℚ) * (FractionalIdeal.absNorm I' * FractionalIdeal.absNorm J')
      = 1 at e3
    change (secIndex I 1 : ℚ) * FractionalIdeal.absNorm I' = 1 at e1
    change (secIndex J 1 : ℚ) * FractionalIdeal.absNorm J' = 1 at e2
    linear_combination (-(secIndex (I * J) 1 : ℚ)) * e1 +
      (-(secIndex (I * J) 1 : ℚ) * secIndex I 1 * FractionalIdeal.absNorm I') * e2 +
      ((secIndex I 1 : ℚ) * secIndex J 1) * e3
  exact_mod_cast this

end Line


section Prod

variable {K : Type} [Field K] [NumberField K]
variable {M₁ M₂ M : Type} [AddCommGroup M₁] [Module (𝓞 K) M₁] [AddCommGroup M₂] [Module (𝓞 K) M₂]
  [AddCommGroup M] [Module (𝓞 K) M]

/-- `K ⊗ M₁ × K ⊗ M₂ ≃ K ⊗ M` from `M₁ × M₂ ≃ M`. -/
noncomputable def sumIso (j₁ : M₁ →ₗ[𝓞 K] M) (j₂ : M₂ →ₗ[𝓞 K] M)
    (hbij : Function.Bijective (LinearMap.coprod j₁ j₂)) :
    ((K ⊗[𝓞 K] M₁) × (K ⊗[𝓞 K] M₂)) ≃ₗ[K] (K ⊗[𝓞 K] M) :=
  (TensorProduct.prodRight (𝓞 K) K K M₁ M₂).symm ≪≫ₗ
    LinearEquiv.baseChange (𝓞 K) K _ _ (LinearEquiv.ofBijective _ hbij)

theorem sumIso_inl (j₁ : M₁ →ₗ[𝓞 K] M) (j₂ : M₂ →ₗ[𝓞 K] M)
    (hbij : Function.Bijective (LinearMap.coprod j₁ j₂)) (m : M₁) :
    sumIso j₁ j₂ hbij ((1 : K) ⊗ₜ[𝓞 K] m, 0) = (1 : K) ⊗ₜ[𝓞 K] j₁ m := by
  simp only [sumIso, LinearEquiv.trans_apply]
  rw [show ((1 : K) ⊗ₜ[𝓞 K] m, (0 : K ⊗[𝓞 K] M₂)) = ((1 : K) ⊗ₜ m, (1 : K) ⊗ₜ (0 : M₂)) by
    rw [tmul_zero], prodRight_symm_tmul]
  simp [LinearEquiv.baseChange, AlgebraTensorModule.congr_tmul]

theorem sumIso_inr (j₁ : M₁ →ₗ[𝓞 K] M) (j₂ : M₂ →ₗ[𝓞 K] M)
    (hbij : Function.Bijective (LinearMap.coprod j₁ j₂)) (m : M₂) :
    sumIso j₁ j₂ hbij (0, (1 : K) ⊗ₜ[𝓞 K] m) = (1 : K) ⊗ₜ[𝓞 K] j₂ m := by
  simp only [sumIso, LinearEquiv.trans_apply]
  rw [show ((0 : K ⊗[𝓞 K] M₁), (1 : K) ⊗ₜ[𝓞 K] m) = ((1 : K) ⊗ₜ (0 : M₁), (1 : K) ⊗ₜ m) by
    rw [tmul_zero], prodRight_symm_tmul]
  simp [LinearEquiv.baseChange, AlgebraTensorModule.congr_tmul]

/-- The concatenated basis of `K ⊗ M`. -/
noncomputable def prodBasis {g₁ g₂ : ℕ} (b₁ : Module.Basis (Fin g₁) K (K ⊗[𝓞 K] M₁))
    (b₂ : Module.Basis (Fin g₂) K (K ⊗[𝓞 K] M₂))
    (E : ((K ⊗[𝓞 K] M₁) × (K ⊗[𝓞 K] M₂)) ≃ₗ[K] (K ⊗[𝓞 K] M)) :
    Module.Basis (Fin (g₁ + g₂)) K (K ⊗[𝓞 K] M) :=
  ((b₁.prod b₂).map E).reindex finSumFinEquiv

theorem prodBasis_castAdd {g₁ g₂ : ℕ} (b₁ : Module.Basis (Fin g₁) K (K ⊗[𝓞 K] M₁))
    (b₂ : Module.Basis (Fin g₂) K (K ⊗[𝓞 K] M₂))
    (E : ((K ⊗[𝓞 K] M₁) × (K ⊗[𝓞 K] M₂)) ≃ₗ[K] (K ⊗[𝓞 K] M)) (i : Fin g₁) :
    prodBasis b₁ b₂ E (Fin.castAdd g₂ i) = E (b₁ i, 0) := by
  simp [prodBasis, Module.Basis.prod_apply]

theorem prodBasis_natAdd {g₁ g₂ : ℕ} (b₁ : Module.Basis (Fin g₁) K (K ⊗[𝓞 K] M₁))
    (b₂ : Module.Basis (Fin g₂) K (K ⊗[𝓞 K] M₂))
    (E : ((K ⊗[𝓞 K] M₁) × (K ⊗[𝓞 K] M₂)) ≃ₗ[K] (K ⊗[𝓞 K] M)) (i : Fin g₂) :
    prodBasis b₁ b₂ E (Fin.natAdd g₁ i) = E (0, b₂ i) := by
  simp [prodBasis, Module.Basis.prod_apply]

/-- **Block determinant.** -/
theorem det_prodBasis_append {g₁ g₂ : ℕ} (b₁ : Module.Basis (Fin g₁) K (K ⊗[𝓞 K] M₁))
    (b₂ : Module.Basis (Fin g₂) K (K ⊗[𝓞 K] M₂))
    (E : ((K ⊗[𝓞 K] M₁) × (K ⊗[𝓞 K] M₂)) ≃ₗ[K] (K ⊗[𝓞 K] M))
    (j₁ : M₁ →ₗ[𝓞 K] M) (j₂ : M₂ →ₗ[𝓞 K] M)
    (hE1 : ∀ m, E ((1 : K) ⊗ₜ[𝓞 K] m, 0) = (1 : K) ⊗ₜ[𝓞 K] j₁ m)
    (hE2 : ∀ m, E (0, (1 : K) ⊗ₜ[𝓞 K] m) = (1 : K) ⊗ₜ[𝓞 K] j₂ m)
    (u : Fin g₁ → M₁) (v : Fin g₂ → M₂) :
    (prodBasis b₁ b₂ E).det (fun k => (1 : K) ⊗ₜ[𝓞 K] Fin.append (j₁ ∘ u) (j₂ ∘ v) k) =
      b₁.det (fun i => (1 : K) ⊗ₜ[𝓞 K] u i) * b₂.det (fun j => (1 : K) ⊗ₜ[𝓞 K] v j) := by
  have h1 : ∀ m, E.symm ((1 : K) ⊗ₜ[𝓞 K] j₁ m) = ((1 : K) ⊗ₜ m, 0) := fun m => by
    rw [LinearEquiv.symm_apply_eq, hE1]
  have h2 : ∀ m, E.symm ((1 : K) ⊗ₜ[𝓞 K] j₂ m) = (0, (1 : K) ⊗ₜ m) := fun m => by
    rw [LinearEquiv.symm_apply_eq, hE2]
  rw [prodBasis, Module.Basis.det_reindex, Module.Basis.det_map, Module.Basis.det_apply,
    Module.Basis.det_apply, Module.Basis.det_apply]
  have hM : (b₁.prod b₂).toMatrix (⇑E.symm ∘
      (fun k => (1 : K) ⊗ₜ[𝓞 K] Fin.append (j₁ ∘ u) (j₂ ∘ v) k) ∘ ⇑finSumFinEquiv) =
      Matrix.fromBlocks (b₁.toMatrix (fun i => (1 : K) ⊗ₜ[𝓞 K] u i)) 0 0
        (b₂.toMatrix (fun j => (1 : K) ⊗ₜ[𝓞 K] v j)) := by
    ext (i | i) (j | j) <;>
      simp [Module.Basis.toMatrix_apply, Matrix.fromBlocks, h1, h2,
        Module.Basis.prod_repr_inl, Module.Basis.prod_repr_inr]
  rw [hM, Matrix.det_fromBlocks_zero₂₁]

/-- A linearly independent family inside the range of a map from a space of dimension `n` has
at most `n` members. -/
theorem card_le_of_li_range {V W : Type*} [AddCommGroup V] [Module K V] [AddCommGroup W]
    [Module K W] [FiniteDimensional K V] [FiniteDimensional K W] (J : V →ₗ[K] W) {ι : Type*}
    [Fintype ι] (F : ι → W) (hF : LinearIndependent K F) (hr : ∀ i, F i ∈ LinearMap.range J) :
    Fintype.card ι ≤ Module.finrank K V := by
  rw [linearIndependent_iff_card_eq_finrank_span.mp hF]
  calc Module.finrank K (Submodule.span K (Set.range F))
      ≤ Module.finrank K (LinearMap.range J) :=
        Submodule.finrank_mono (Submodule.span_le.mpr (by rintro _ ⟨i, rfl⟩; exact hr i))
    _ ≤ _ := LinearMap.finrank_range_le J

end Prod

/-- **`DetLatticeProd`, proved** (the statement is the body of `ZInQ.UnifDims.DetLatticeProd`). -/
theorem detLatticeProd_aux :
  ∀ (K : Type) [Field K] [NumberField K] (M₁ M₂ M : Type) [AddCommGroup M₁] [Module (𝓞 K) M₁]
    [AddCommGroup M₂] [Module (𝓞 K) M₂] [AddCommGroup M] [Module (𝓞 K) M]
    (ω₁ : Submodule (𝓞 K) M₁) (ω₂ : Submodule (𝓞 K) M₂) (j₁ : M₁ →ₗ[𝓞 K] M)
    (j₂ : M₂ →ₗ[𝓞 K] M) (g₁ g₂ : ℕ),
    Function.Bijective (LinearMap.coprod j₁ j₂) → ω₁.FG → ω₂.FG →
    Module.rank K (K ⊗[𝓞 K] M₁) = g₁ → Module.rank K (K ⊗[𝓞 K] M₂) = g₂ →
    Submodule.span K (Set.range fun x : ω₁ => (1 : K) ⊗ₜ[𝓞 K] (x : M₁)) = ⊤ →
    Submodule.span K (Set.range fun x : ω₂ => (1 : K) ⊗ₜ[𝓞 K] (x : M₂)) = ⊤ →
    ∃ (x₁ : Fin g₁ → M₁) (x₂ : Fin g₂ → M₂) (a₁ a₂ : K),
      a₁ • ((1 : K) ⊗ₜ[𝓞 K] exteriorPower.ιMulti (𝓞 K) g₁ x₁) ∈ detLat ω₁ g₁ ∧
      a₁ • ((1 : K) ⊗ₜ[𝓞 K] exteriorPower.ιMulti (𝓞 K) g₁ x₁) ≠ 0 ∧
      a₂ • ((1 : K) ⊗ₜ[𝓞 K] exteriorPower.ιMulti (𝓞 K) g₂ x₂) ∈ detLat ω₂ g₂ ∧
      a₂ • ((1 : K) ⊗ₜ[𝓞 K] exteriorPower.ιMulti (𝓞 K) g₂ x₂) ≠ 0 ∧
      (a₁ * a₂) • ((1 : K) ⊗ₜ[𝓞 K] exteriorPower.ιMulti (𝓞 K) (g₁ + g₂)
        (Fin.append (j₁ ∘ x₁) (j₂ ∘ x₂))) ∈ detLat (ω₁.map j₁ ⊔ ω₂.map j₂) (g₁ + g₂) ∧
      (a₁ * a₂) • ((1 : K) ⊗ₜ[𝓞 K] exteriorPower.ιMulti (𝓞 K) (g₁ + g₂)
        (Fin.append (j₁ ∘ x₁) (j₂ ∘ x₂))) ≠ 0 ∧
      secIndex (detLat (ω₁.map j₁ ⊔ ω₂.map j₂) (g₁ + g₂))
          ((a₁ * a₂) • ((1 : K) ⊗ₜ[𝓞 K] exteriorPower.ιMulti (𝓞 K) (g₁ + g₂)
            (Fin.append (j₁ ∘ x₁) (j₂ ∘ x₂)))) =
        secIndex (detLat ω₁ g₁) (a₁ • ((1 : K) ⊗ₜ[𝓞 K] exteriorPower.ιMulti (𝓞 K) g₁ x₁)) *
          secIndex (detLat ω₂ g₂) (a₂ • ((1 : K) ⊗ₜ[𝓞 K] exteriorPower.ιMulti (𝓞 K) g₂ x₂)) := by
  intro K _ _ M₁ M₂ M _ _ _ _ _ _ ω₁ ω₂ j₁ j₂ g₁ g₂ hbij hfg₁ hfg₂ hr₁ hr₂ hsp₁ hsp₂
  classical
  have : FiniteDimensional K (K ⊗[𝓞 K] M₁) := Module.finite_of_rank_eq_nat hr₁
  have : FiniteDimensional K (K ⊗[𝓞 K] M₂) := Module.finite_of_rank_eq_nat hr₂
  obtain ⟨w₁, b₁, hb₁⟩ := exists_basis_of_span ω₁ hr₁ hsp₁
  obtain ⟨w₂, b₂, hb₂⟩ := exists_basis_of_span ω₂ hr₂ hsp₂
  set E := sumIso (K := K) j₁ j₂ hbij
  have hE1 : ∀ m, E ((1 : K) ⊗ₜ[𝓞 K] m, 0) = (1 : K) ⊗ₜ[𝓞 K] j₁ m := sumIso_inl j₁ j₂ hbij
  have hE2 : ∀ m, E (0, (1 : K) ⊗ₜ[𝓞 K] m) = (1 : K) ⊗ₜ[𝓞 K] j₂ m := sumIso_inr j₁ j₂ hbij
  set b := prodBasis b₁ b₂ E
  have : FiniteDimensional K (K ⊗[𝓞 K] M) := Module.Basis.finiteDimensional_of_finite b
  set x₁ : Fin g₁ → M₁ := fun i => (w₁ i : M₁)
  set x₂ : Fin g₂ → M₂ := fun i => (w₂ i : M₂)
  set y : Fin (g₁ + g₂) → M := Fin.append (j₁ ∘ x₁) (j₂ ∘ x₂) with hy
  have hb : ∀ k, (1 : K) ⊗ₜ[𝓞 K] y k = b k := by
    intro k
    refine Fin.addCases (fun i => ?_) (fun i => ?_) k
    · rw [prodBasis_castAdd, ← hb₁, hE1, hy, Fin.append_left]; rfl
    · rw [prodBasis_natAdd, ← hb₂, hE2, hy, Fin.append_right]; rfl
  set ω := ω₁.map j₁ ⊔ ω₂.map j₂ with hω
  have hi₁ := detFun_injective b₁ x₁ hb₁
  have hi₂ := detFun_injective b₂ x₂ hb₂
  have hi := detFun_injective b y hb
  set I₁ := (detLat ω₁ g₁).map ((detFun b₁).restrictScalars (𝓞 K)) with hI₁
  set I₂ := (detLat ω₂ g₂).map ((detFun b₂).restrictScalars (𝓞 K)) with hI₂
  set I := (detLat ω (g₁ + g₂)).map ((detFun b).restrictScalars (𝓞 K)) with hI
  have hblock := det_prodBasis_append b₁ b₂ E j₁ j₂ hE1 hE2
  have happ : ∀ (u : Fin g₁ → ω₁) (v : Fin g₂ → ω₂) (k : Fin (g₁ + g₂)),
      Fin.append (j₁ ∘ fun i => (u i : M₁)) (j₂ ∘ fun i => (v i : M₂)) k ∈ ω := by
    intro u v k
    refine Fin.addCases (fun i => ?_) (fun i => ?_) k
    · rw [Fin.append_left]
      exact Submodule.mem_sup_left (Submodule.mem_map_of_mem (u i).2)
    · rw [Fin.append_right]
      exact Submodule.mem_sup_right (Submodule.mem_map_of_mem (v i).2)
  have hgen₁ : ∀ u : Fin g₁ → ω₁, b₁.det (fun i => (1 : K) ⊗ₜ[𝓞 K] (u i : M₁)) ∈ I₁ := by
    intro u
    rw [← detFun_tmul]
    exact Submodule.mem_map_of_mem (Submodule.subset_span ⟨u, rfl⟩)
  have hgen₂ : ∀ u : Fin g₂ → ω₂, b₂.det (fun i => (1 : K) ⊗ₜ[𝓞 K] (u i : M₂)) ∈ I₂ := by
    intro u
    rw [← detFun_tmul]
    exact Submodule.mem_map_of_mem (Submodule.subset_span ⟨u, rfl⟩)
  have hge : I₁ * I₂ ≤ I := by
    rw [hI₁, hI₂, detLat, detLat, Submodule.map_span, Submodule.map_span, Submodule.span_mul_span,
      Submodule.span_le]
    rintro _ ⟨_, ⟨_, ⟨u, rfl⟩, rfl⟩, _, ⟨_, ⟨v, rfl⟩, rfl⟩, rfl⟩
    simp only [LinearMap.coe_restrictScalars]
    rw [detFun_tmul, detFun_tmul, ← hblock, ← detFun_tmul]
    exact Submodule.mem_map_of_mem (Submodule.subset_span ⟨fun k => ⟨_, happ u v k⟩, rfl⟩)
  have hle : I ≤ I₁ * I₂ := by
    rw [hI, detLat, Submodule.map_span, Submodule.span_le]
    rintro _ ⟨_, ⟨v, rfl⟩, rfl⟩
    have hdec : ∀ k, ∃ (a : ω₁) (c : ω₂), (v k : M) = j₁ a + j₂ c := fun k => by
      obtain ⟨y', hy', z, hz, hyz⟩ := Submodule.mem_sup.mp (v k).2
      obtain ⟨a, ha, rfl⟩ := hy'
      obtain ⟨c, hc, rfl⟩ := hz
      exact ⟨⟨a, ha⟩, ⟨c, hc⟩, hyz.symm⟩
    choose a c hac using hdec
    simp only [SetLike.mem_coe, LinearMap.coe_restrictScalars]
    rw [detFun_tmul]
    have hsplit : (fun k => (1 : K) ⊗ₜ[𝓞 K] (v k : M)) = fun k =>
        (1 : K) ⊗ₜ[𝓞 K] j₁ (a k) + (1 : K) ⊗ₜ[𝓞 K] j₂ (c k) := funext fun k => by
      rw [hac, tmul_add]
    rw [hsplit]
    have hexp := (b.det : (K ⊗[𝓞 K] M) [⋀^Fin (g₁ + g₂)]→ₗ[K] K).toMultilinearMap.map_add_univ
      (fun k => (1 : K) ⊗ₜ[𝓞 K] j₁ (a k)) (fun k => (1 : K) ⊗ₜ[𝓞 K] j₂ (c k))
    simp only [AlternatingMap.coe_multilinearMap] at hexp
    rw [show (fun k => (1 : K) ⊗ₜ[𝓞 K] j₁ (a k) + (1 : K) ⊗ₜ[𝓞 K] j₂ (c k)) =
      (fun k => (1 : K) ⊗ₜ[𝓞 K] j₁ (a k)) + (fun k => (1 : K) ⊗ₜ[𝓞 K] j₂ (c k)) from rfl, hexp]
    refine Submodule.sum_mem _ fun T _ => ?_
    set F := T.piecewise (fun k => (1 : K) ⊗ₜ[𝓞 K] j₁ (a k)) (fun k => (1 : K) ⊗ₜ[𝓞 K] j₂ (c k))
      with hF
    show b.det F ∈ _
    by_cases hT : T.card = g₁
    · have hTc : Tᶜ.card = g₂ := by rw [Finset.card_compl, Fintype.card_fin, hT]; omega
      let e1 := T.orderIsoOfFin hT
      let e2 := Tᶜ.orderIsoOfFin hTc
      let σ : Equiv.Perm (Fin (g₁ + g₂)) := finSumFinEquiv.symm.trans
        ((Equiv.sumCongr e1.toEquiv
          (e2.toEquiv.trans (Equiv.subtypeEquivRight (fun x => Finset.mem_compl)))).trans
          (Equiv.sumCompl (· ∈ T)))
      have hσ1 : ∀ i, σ (Fin.castAdd g₂ i) = (e1 i : Fin (g₁ + g₂)) := by
        intro i; simp [σ]
      have hσ2 : ∀ i, σ (Fin.natAdd g₁ i) = (e2 i : Fin (g₁ + g₂)) := by
        intro i; simp [σ]
      have hFσ : F ∘ σ = fun k => (1 : K) ⊗ₜ[𝓞 K] Fin.append (j₁ ∘ fun i => ((a (e1 i)) : M₁))
          (j₂ ∘ fun i => ((c (e2 i)) : M₂)) k := by
        funext k
        refine Fin.addCases (fun i => ?_) (fun i => ?_) k
        · rw [Function.comp_apply, hσ1, Fin.append_left, hF,
            Finset.piecewise_eq_of_mem _ _ _ (e1 i).2]
          rfl
        · rw [Function.comp_apply, hσ2, Fin.append_right, hF,
            Finset.piecewise_eq_of_notMem _ _ _ (Finset.mem_compl.mp (e2 i).2)]
          rfl
      have key : b.det F = (Equiv.Perm.sign σ) • b.det (F ∘ σ) := by
        rw [AlternatingMap.map_perm, smul_smul, Int.units_mul_self, one_smul]
      rw [key, hFσ, hblock]
      have hm := Submodule.mul_mem_mul (hgen₁ fun i => a (e1 i)) (hgen₂ fun i => c (e2 i))
      rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h
      · rw [h, one_smul]; exact hm
      · rw [h, Units.neg_smul, one_smul]; exact neg_mem hm
    · have hnli : ¬ LinearIndependent K F := by
        intro hli
        have h1 : T.card ≤ g₁ := by
          have := card_le_of_li_range (E.toLinearMap ∘ₗ LinearMap.inl K _ _)
            (fun k : T => F k) (hli.comp _ Subtype.val_injective) (fun k =>
              ⟨(1 : K) ⊗ₜ[𝓞 K] (a k : M₁), by
                simp only [LinearMap.comp_apply, LinearMap.inl_apply, LinearEquiv.coe_coe, hE1]
                rw [hF, Finset.piecewise_eq_of_mem _ _ _ k.2]⟩)
          rwa [Fintype.card_coe, Module.finrank_eq_of_rank_eq hr₁] at this
        have h2 : Tᶜ.card ≤ g₂ := by
          have := card_le_of_li_range (E.toLinearMap ∘ₗ LinearMap.inr K _ _)
            (fun k : (Tᶜ : Finset _) => F k) (hli.comp _ Subtype.val_injective) (fun k =>
              ⟨(1 : K) ⊗ₜ[𝓞 K] (c k : M₂), by
                simp only [LinearMap.comp_apply, LinearMap.inr_apply, LinearEquiv.coe_coe, hE2]
                rw [hF, Finset.piecewise_eq_of_notMem _ _ _ (Finset.mem_compl.mp k.2)]⟩)
          rwa [Fintype.card_coe, Module.finrank_eq_of_rank_eq hr₂] at this
        have h3 : T.card + Tᶜ.card = g₁ + g₂ := by
          rw [Finset.card_add_card_compl, Fintype.card_fin]
        omega
      rw [b.det.map_linearDependent F hnli]
      exact Submodule.zero_mem _
  have hIP : I = I₁ * I₂ := le_antisymm hle hge
  have hΨ1 : detFun b₁ ((1 : K) ⊗ₜ[𝓞 K] exteriorPower.ιMulti (𝓞 K) g₁ x₁) = 1 := by
    rw [detFun_tmul, show (fun k => (1 : K) ⊗ₜ[𝓞 K] x₁ k) = b₁ from funext hb₁,
      Module.Basis.det_self]
  have hΨ2 : detFun b₂ ((1 : K) ⊗ₜ[𝓞 K] exteriorPower.ιMulti (𝓞 K) g₂ x₂) = 1 := by
    rw [detFun_tmul, show (fun k => (1 : K) ⊗ₜ[𝓞 K] x₂ k) = b₂ from funext hb₂,
      Module.Basis.det_self]
  have hΨ : detFun b ((1 : K) ⊗ₜ[𝓞 K] exteriorPower.ιMulti (𝓞 K) (g₁ + g₂) y) = 1 := by
    rw [detFun_tmul, show (fun k => (1 : K) ⊗ₜ[𝓞 K] y k) = b from funext hb,
      Module.Basis.det_self]
  have hm₁ : (1 : K) ⊗ₜ[𝓞 K] exteriorPower.ιMulti (𝓞 K) g₁ x₁ ∈ detLat ω₁ g₁ :=
    Submodule.subset_span ⟨w₁, rfl⟩
  have hm₂ : (1 : K) ⊗ₜ[𝓞 K] exteriorPower.ιMulti (𝓞 K) g₂ x₂ ∈ detLat ω₂ g₂ :=
    Submodule.subset_span ⟨w₂, rfl⟩
  have hm : (1 : K) ⊗ₜ[𝓞 K] exteriorPower.ιMulti (𝓞 K) (g₁ + g₂) y ∈ detLat ω (g₁ + g₂) :=
    Submodule.subset_span ⟨fun k => ⟨y k, happ w₁ w₂ k⟩, rfl⟩
  have h1I₁ : (1 : K) ∈ I₁ := hΨ1 ▸ Submodule.mem_map_of_mem hm₁
  have h1I₂ : (1 : K) ∈ I₂ := hΨ2 ▸ Submodule.mem_map_of_mem hm₂
  have hne : ∀ {V : Type} [AddCommGroup V] [Module K V] (Ψ : V →ₗ[K] K) (s : V), Ψ s = 1 →
      s ≠ 0 := fun Ψ s h hs => by rw [hs, map_zero] at h; exact zero_ne_one h
  refine ⟨x₁, x₂, 1, 1, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [one_smul]; exact hm₁
  · rw [one_smul]; exact hne _ _ hΨ1
  · rw [one_smul]; exact hm₂
  · rw [one_smul]; exact hne _ _ hΨ2
  · rw [mul_one, one_smul]; exact hm
  · rw [mul_one, one_smul]; exact hne _ _ hΨ
  · rw [mul_one, one_smul, one_smul, one_smul, secIndex_map _ hi, secIndex_map _ hi₁,
      secIndex_map _ hi₂, hΨ, hΨ1, hΨ2]
    change secIndex I 1 = secIndex I₁ 1 * secIndex I₂ 1
    rw [hIP]
    exact secIndex_one_mul I₁ I₂ ((detLat_fg ω₁ hfg₁ g₁).map _) ((detLat_fg ω₂ hfg₂ g₂).map _)
      h1I₁ h1I₂

end ZInQ.UnifDims


/-! ## unif-dims: metrization's `ProductHodgeLattice` reduced

`ProductHodgeLattice` (metrization's glue, copied verbatim above) follows from:
* `ProductCotangent` (new glue, algebraic geometry; proved below as `productCotangent`): the
  cotangent space at the generic unit of a product model is the direct sum of the factors' cotangent spaces, through the pull-backs of germs
  along the two projections, and the conormal lattice `ω` of the product is the sum of the two
  pulled-back lattices;
* `DetLatticeProd` (new glue, pure commutative algebra over `𝓞_K`, no geometry; proved below as
  `detLatticeProd`): for a direct sum of two modules with full lattices `ω₁, ω₂` of ranks `g₁, g₂`,
  the determinant lattice of `ω₁ ⊕ ω₂` has particular sections `s₁, s₂, s = s₁ ∧ s₂` with
  `[⋀ω : 𝓞s] = [⋀ω₁ : 𝓞s₁]·[⋀ω₂ : 𝓞s₂]`;
* the kernel's `HodgeLattice.CotangentRank` (already reduced by hodge-lattice to
  `TangentDimAtOrigin`, with `DimBaseChange` proved below from g0-dim);
* `AnalyticUniformizationOfDim` (from T35), only to know `gᵢ = dim` for the metrizations `Mᵢ`.
The kernel's `omegaLocal` (proved) supplies finiteness and fullness of each `ω`. -/

namespace ZInQ.UnifDims

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open NumberField ZInQ.DefFaltings ZInQ.DefFaltings.HodgeLattice TensorProduct

/-- **Glue (algebraic geometry: the cotangent space and conormal lattice of a product model).**
Let `e : 𝒢P ≅ 𝒢₁ ×_{𝓞_L} 𝒢₂` have homomorphic components `pᵢ`. There are `𝓞_L`-linear maps
`jᵢ : 𝔪ᵢ/𝔪ᵢ² → 𝔪_P/𝔪_P²` (at the generic units `ξ`) such that
* `jᵢ(df) = d(pᵢ* f)` for every germ `f ∈ 𝔪ᵢ` (in particular `pᵢ* f ∈ 𝔪_P`), where `pᵢ*` is
  metrization's `pullGerm`;
* `(x, y) ↦ j₁ x + j₂ y` is bijective;
* `ω_{𝒢P} = j₁(ω_{𝒢₁}) + j₂(ω_{𝒢₂})`.
Why true (STANDARD). `𝒪_{𝒢P,ξ}` is the local ring of `A_L ×_L B_L` at the origin, a localization
of `𝒪_{A_L,0} ⊗_L 𝒪_{B_L,0}`, and `𝔪/𝔪²` of a product of `L`-rational points is the direct sum
(`Ω_{X ×_S Y/S} = p₁*Ω_{X/S} ⊕ p₂*Ω_{Y/S}`; EGA IV 16.4.23 / Stacks, differentials of a fibre
product, UNVERIFIED locators). For the lattices: at every point `s` of `Spec 𝓞_L`, the ideal of the
unit section of `𝒢₁ ×_S 𝒢₂` at `e(s)` is generated by `p₁*I₁ + p₂*I₂` (the section is the
product of the two sections), so `(ω_P)_s = j₁(ω₁)_s ⊕ j₂(ω₂)_s`, and intersecting over `s` in the
direct sum gives the claim. `jᵢ` is `𝓞_L`-linear because `pᵢ` lies over `Spec 𝓞_L`. Proved:
`productCotangent` (`PC.lean`, with infra-stalks' stalk lemmas for fibre products). -/
def ProductCotangent : Prop :=
  ∀ (K : Type) [Field K] (A B C : AbVar K) (L : Type) [Field L] [NumberField L] [Algebra K L]
    (𝒢P : GroupModel C L) (𝒢₁ : GroupModel A L) (𝒢₂ : GroupModel B L)
    (e : 𝒢P.G ≅ 𝒢₁.G ⊗ 𝒢₂.G) (hfst : IsMonHom (e.hom ≫ fst _ _))
    (hsnd : IsMonHom (e.hom ≫ snd _ _)),
    ∃ (j₁ : 𝒢₁.cotangent →ₗ[𝓞 L] 𝒢P.cotangent) (j₂ : 𝒢₂.cotangent →ₗ[𝓞 L] 𝒢P.cotangent),
      (∀ f : IsLocalRing.maximalIdeal 𝒢₁.genStalk,
        ∃ h : (ZInQ.Metrization.pullGerm (e.hom ≫ fst _ _)).hom (f : 𝒢₁.genStalk) ∈
          IsLocalRing.maximalIdeal 𝒢P.genStalk, j₁ (𝒢₁.dCls f) = 𝒢P.dCls ⟨_, h⟩) ∧
      (∀ f : IsLocalRing.maximalIdeal 𝒢₂.genStalk,
        ∃ h : (ZInQ.Metrization.pullGerm (e.hom ≫ snd _ _)).hom (f : 𝒢₂.genStalk) ∈
          IsLocalRing.maximalIdeal 𝒢P.genStalk, j₂ (𝒢₂.dCls f) = 𝒢P.dCls ⟨_, h⟩) ∧
      Function.Bijective (LinearMap.coprod j₁ j₂) ∧
      𝒢P.omega = 𝒢₁.omega.map j₁ ⊔ 𝒢₂.omega.map j₂

/-- **Glue (commutative algebra: the determinant lattice of a direct sum).** Let `K` be a number
field, `M₁, M₂, M` modules over `𝓞_K` with `M₁ × M₂ ≅ M` through `(x, y) ↦ j₁ x + j₂ y`, and
`ωᵢ ⊆ Mᵢ` finitely generated submodules spanning `K ⊗ Mᵢ`, which has `K`-rank `gᵢ`. Put
`ω = j₁ω₁ + j₂ω₂`. Then there are `xᵢ ∈ Mᵢ^{gᵢ}` and `aᵢ ∈ K` such that `sᵢ = aᵢ · 1 ⊗ ∧xᵢ` is a
nonzero element of `detLat ωᵢ gᵢ`, `s = a₁a₂ · 1 ⊗ ∧(j₁x₁, j₂x₂)` is a nonzero element of
`detLat ω (g₁+g₂)`, and `[detLat ω : 𝓞s] = [detLat ω₁ : 𝓞s₁]·[detLat ω₂ : 𝓞s₂]`.
Why true (STANDARD). `K ⊗ M = (K ⊗ M₁) ⊕ (K ⊗ M₂)` and the images `Ω̄ᵢ` of `ωᵢ` are full
`𝓞_K`-lattices (projective of rank `gᵢ`); `K ⊗ ⋀^{g₁+g₂} M = ⋀^{g₁}(K⊗M₁) ⊗ ⋀^{g₂}(K⊗M₂)` and
`det(Ω̄₁ ⊕ Ω̄₂) = det Ω̄₁ ⊗ det Ω̄₂` (Bourbaki, Algèbre III §7, UNVERIFIED locator; in coordinates,
generalized Laplace expansion along the first `g₁` columns). Identifying the lines with `K`, the
lattices become fractional ideals `I₁, I₂, I₁I₂`, and the indices multiply because
`[I : 𝓞x] = |N(x)| / N(I)` (the kernel's `secIndex_mul_absNorm`) and both norms are
multiplicative. Take `xᵢ` an `𝓞_K`-family in `ωᵢ` forming a `K`-basis and `aᵢ = 1`. Proved:
`detLatticeProd` (`DetProd.lean`). -/
def DetLatticeProd : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (M₁ M₂ M : Type) [AddCommGroup M₁] [Module (𝓞 K) M₁]
    [AddCommGroup M₂] [Module (𝓞 K) M₂] [AddCommGroup M] [Module (𝓞 K) M]
    (ω₁ : Submodule (𝓞 K) M₁) (ω₂ : Submodule (𝓞 K) M₂) (j₁ : M₁ →ₗ[𝓞 K] M)
    (j₂ : M₂ →ₗ[𝓞 K] M) (g₁ g₂ : ℕ),
    Function.Bijective (LinearMap.coprod j₁ j₂) → ω₁.FG → ω₂.FG →
    Module.rank K (K ⊗[𝓞 K] M₁) = g₁ → Module.rank K (K ⊗[𝓞 K] M₂) = g₂ →
    Submodule.span K (Set.range fun x : ω₁ => (1 : K) ⊗ₜ[𝓞 K] (x : M₁)) = ⊤ →
    Submodule.span K (Set.range fun x : ω₂ => (1 : K) ⊗ₜ[𝓞 K] (x : M₂)) = ⊤ →
    ∃ (x₁ : Fin g₁ → M₁) (x₂ : Fin g₂ → M₂) (a₁ a₂ : K),
      a₁ • ((1 : K) ⊗ₜ[𝓞 K] exteriorPower.ιMulti (𝓞 K) g₁ x₁) ∈ detLat ω₁ g₁ ∧
      a₁ • ((1 : K) ⊗ₜ[𝓞 K] exteriorPower.ιMulti (𝓞 K) g₁ x₁) ≠ 0 ∧
      a₂ • ((1 : K) ⊗ₜ[𝓞 K] exteriorPower.ιMulti (𝓞 K) g₂ x₂) ∈ detLat ω₂ g₂ ∧
      a₂ • ((1 : K) ⊗ₜ[𝓞 K] exteriorPower.ιMulti (𝓞 K) g₂ x₂) ≠ 0 ∧
      (a₁ * a₂) • ((1 : K) ⊗ₜ[𝓞 K] exteriorPower.ιMulti (𝓞 K) (g₁ + g₂)
        (Fin.append (j₁ ∘ x₁) (j₂ ∘ x₂))) ∈ detLat (ω₁.map j₁ ⊔ ω₂.map j₂) (g₁ + g₂) ∧
      (a₁ * a₂) • ((1 : K) ⊗ₜ[𝓞 K] exteriorPower.ιMulti (𝓞 K) (g₁ + g₂)
        (Fin.append (j₁ ∘ x₁) (j₂ ∘ x₂))) ≠ 0 ∧
      secIndex (detLat (ω₁.map j₁ ⊔ ω₂.map j₂) (g₁ + g₂))
          ((a₁ * a₂) • ((1 : K) ⊗ₜ[𝓞 K] exteriorPower.ιMulti (𝓞 K) (g₁ + g₂)
            (Fin.append (j₁ ∘ x₁) (j₂ ∘ x₂)))) =
        secIndex (detLat ω₁ g₁) (a₁ • ((1 : K) ⊗ₜ[𝓞 K] exteriorPower.ιMulti (𝓞 K) g₁ x₁)) *
          secIndex (detLat ω₂ g₂) (a₂ • ((1 : K) ⊗ₜ[𝓞 K] exteriorPower.ιMulti (𝓞 K) g₂ x₂))

/-- hodge-lattice's `DimBaseChange`, proved (g0-dim's `G0Dim.dim_baseChange`). -/
theorem dimBaseChange : DimBaseChange := fun _ _ A L _ _ =>
  G0Dim.dim_baseChange L A.X.left A.X.hom

/-- `K ⊗ -` turns a direct sum decomposition into a sum of ranks. -/
theorem rank_tensor_of_bijective {K : Type} [Field K] [NumberField K] {M₁ M₂ M : Type}
    [AddCommGroup M₁] [Module (𝓞 K) M₁] [AddCommGroup M₂] [Module (𝓞 K) M₂] [AddCommGroup M]
    [Module (𝓞 K) M] (j₁ : M₁ →ₗ[𝓞 K] M) (j₂ : M₂ →ₗ[𝓞 K] M)
    (hbij : Function.Bijective (LinearMap.coprod j₁ j₂)) {g₁ g₂ : ℕ}
    (h₁ : Module.rank K (K ⊗[𝓞 K] M₁) = g₁) (h₂ : Module.rank K (K ⊗[𝓞 K] M₂) = g₂) :
    Module.rank K (K ⊗[𝓞 K] M) = ((g₁ + g₂ : ℕ) : Cardinal) := by
  let E : (M₁ × M₂) ≃ₗ[𝓞 K] M := LinearEquiv.ofBijective _ hbij
  rw [← (LinearEquiv.baseChange (𝓞 K) K _ _ E).rank_eq,
    (TensorProduct.prodRight (𝓞 K) K K M₁ M₂).rank_eq, rank_prod', h₁, h₂]
  push_cast
  rfl

/-- **`ProductHodgeLattice` from `ProductCotangent`, `DetLatticeProd`, `CotangentRank` and
`AnalyticUniformizationOfDim` (proved).** -/
theorem productHodgeLattice_of (hPC : ProductCotangent) (hDL : DetLatticeProd)
    (hCR : CotangentRank) (hU : ZInQ.Metrization.AnalyticUniformizationOfDim) :
    ZInQ.Metrization.ProductHodgeLattice := by
  intro K _ A B C L _ _ _ 𝒢P g₁ g₂ M₁ M₂ e hfst hsnd
  obtain ⟨j₁, j₂, hc₁, hc₂, hbij, hom⟩ := hPC K A B C L 𝒢P M₁.model M₂.model e hfst hsnd
  obtain ⟨τ⟩ := (inferInstance : Nonempty (L →+* ℂ))
  have hg : ∀ {X : AbVar K} {g : ℕ} (M : MetrizedModel X L g), X.dim = (g : WithBot ℕ∞) := by
    intro X g M
    obtain ⟨Φ, hΦ, -⟩ := M.arch τ
    exact dim_eq_of_isAnalyticUniformization hU M.model τ _ Φ (M.hodge.periods_discrete τ)
      (M.hodge.periods_isZLattice τ) hΦ
  have hr₁ := hCR K A L M₁.model g₁ (hg M₁)
  have hr₂ := hCR K B L M₂.model g₂ (hg M₂)
  have hfg : ∀ {X : AbVar K} (𝒢 : GroupModel X L), 𝒢.omega.FG := fun 𝒢 =>
    omegaFG_of_omegaLocal omegaLocal K _ L 𝒢
  have hsp : ∀ {X : AbVar K} (𝒢 : GroupModel X L), Submodule.span L
      (Set.range fun x : 𝒢.omega => (1 : L) ⊗ₜ[𝓞 L] (x : 𝒢.cotangent)) = ⊤ := fun 𝒢 =>
    omegaSpans_of_omegaLocal omegaLocal K _ L 𝒢
  have hrP := rank_tensor_of_bijective j₁ j₂ hbij hr₁ hr₂
  refine ⟨(hodgeLattice_of_lattice 𝒢P.omega (hfg 𝒢P) hrP (hsp 𝒢P)).1, ?_⟩
  obtain ⟨x₁, x₂, a₁, a₂, h₁, h₁', h₂, h₂', hP, hP', hidx⟩ :=
    hDL L M₁.model.cotangent M₂.model.cotangent 𝒢P.cotangent M₁.model.omega M₂.model.omega
      j₁ j₂ g₁ g₂ hbij (hfg _) (hfg _) hr₁ hr₂ (hsp _) (hsp _)
  choose f₁ hf₁ using fun i => (IsLocalRing.maximalIdeal M₁.model.genStalk).toCotangent_surjective
    (x₁ i)
  choose f₂ hf₂ using fun i => (IsLocalRing.maximalIdeal M₂.model.genStalk).toCotangent_surjective
    (x₂ i)
  choose m₁ hm₁ using fun i => hc₁ (f₁ i)
  choose m₂ hm₂ using fun i => hc₂ (f₂ i)
  let f : Fin (g₁ + g₂) → IsLocalRing.maximalIdeal 𝒢P.genStalk :=
    Fin.append (fun i => ⟨_, m₁ i⟩) (fun j => ⟨_, m₂ j⟩)
  have hw₁ : M₁.model.wedge f₁ = (1 : L) ⊗ₜ[𝓞 L] exteriorPower.ιMulti (𝓞 L) g₁ x₁ := by
    unfold GroupModel.wedge
    congr 2
    funext i
    exact hf₁ i
  have hw₂ : M₂.model.wedge f₂ = (1 : L) ⊗ₜ[𝓞 L] exteriorPower.ιMulti (𝓞 L) g₂ x₂ := by
    unfold GroupModel.wedge
    congr 2
    funext i
    exact hf₂ i
  have hw : 𝒢P.wedge f = (1 : L) ⊗ₜ[𝓞 L] exteriorPower.ιMulti (𝓞 L) (g₁ + g₂)
      (Fin.append (j₁ ∘ x₁) (j₂ ∘ x₂)) := by
    unfold GroupModel.wedge
    congr 2
    funext k
    refine Fin.addCases (fun i => ?_) (fun j => ?_) k
    · simp only [f, Fin.append_left, Function.comp_apply]
      rw [← hm₁ i, ← hf₁ i]
      rfl
    · simp only [f, Fin.append_right, Function.comp_apply]
      rw [← hm₂ j, ← hf₂ j]
      rfl
  have hL₁ : M₁.hodge.lattice = detLat M₁.model.omega g₁ := M₁.lattice_eq
  have hL₂ : M₂.hodge.lattice = detLat M₂.model.omega g₂ := M₂.lattice_eq
  have hLP : 𝒢P.detLattice (g₁ + g₂) =
      detLat (M₁.model.omega.map j₁ ⊔ M₂.model.omega.map j₂) (g₁ + g₂) := by
    rw [detLattice_eq, hom]
  refine ⟨f₁, f₂, f, a₁, a₂, fun i => ?_, fun j => ?_, ?_⟩
  · simp only [f, Fin.append_left]
  · simp only [f, Fin.append_right]
  rw [hw₁, hw₂, hw, hL₁, hL₂, hLP]
  exact ⟨h₁, h₁', h₂, h₂', hP, hP', hidx⟩

/-- **`ProductHodgeLattice` from `ProductCotangent`, `DetLatticeProd`, hodge-lattice's
`TangentDimAtOrigin` and T35 (proved).** -/
theorem productHodgeLattice_of_tangent (hPC : ProductCotangent) (hDL : DetLatticeProd)
    (hT : TangentDimAtOrigin) (hT35 : ZInQ.LeafPush2.UniformizationExists) :
    ZInQ.Metrization.ProductHodgeLattice :=
  productHodgeLattice_of hPC hDL
    (cotangentRank_of_tangentDim (tangentDim_of_abVar hT dimBaseChange))
    (ZInQ.Metrization2.analyticUniformizationOfDim_of_uniformizationExists hT35)

end ZInQ.UnifDims




/-! ## unif-dims: `DetLatticeProd` closed; `ProductHodgeLattice` from `ProductCotangent`,
`TangentDimAtOrigin` and T35 -/

namespace ZInQ.UnifDims

open ZInQ.DefFaltings.HodgeLattice

/-- **`DetLatticeProd`, proved** (`detLatticeProd_aux`, `DetProd.lean`). -/
theorem detLatticeProd : DetLatticeProd := detLatticeProd_aux

/-- **`ProductHodgeLattice` from `ProductCotangent`, hodge-lattice's `TangentDimAtOrigin` and T35
(proved).** -/
theorem productHodgeLattice_of_cotangent (hPC : ProductCotangent) (hT : TangentDimAtOrigin)
    (hT35 : ZInQ.LeafPush2.UniformizationExists) : ZInQ.Metrization.ProductHodgeLattice :=
  productHodgeLattice_of_tangent hPC detLatticeProd hT hT35

end ZInQ.UnifDims




/-! ## unif-dims: S-alg and P2 from T35, `ProductCotangent` and `TangentDimAtOrigin` -/

namespace ZInQ.UnifDims

open ZInQ.DefFaltings ZInQ.DefFaltings.HodgeLattice

/-- **S-alg (`ProductMetrizationOfProductUnif`) from T35, `ProductCotangent` and
`TangentDimAtOrigin` (proved).** product-unif's `productMetrizationOfProductUnif_of_local` with
`HodgeLatticeTheorem` from hodge-lattice (`TangentDimAtOrigin`, `DimBaseChange` proved here),
`ProductUnifDims` from T35, metrization2's `productLocalStructure`, and `ProductHodgeLattice`
from `ProductCotangent`. -/
theorem productMetrizationOfProductUnif_of_cotangent (hT35 : ZInQ.LeafPush2.UniformizationExists)
    (hPC : ProductCotangent) (hT : TangentDimAtOrigin) :
    ZInQ.ProductHeight.ProductMetrizationOfProductUnif :=
  ZInQ.ProductUnif.productMetrizationOfProductUnif_of_local
    (hodgeLatticeTheorem_of_tangent hT dimBaseChange)
    (productUnifDims_of_uniformizationExists hT35)
    ZInQ.Metrization2.productLocalStructure
    (productHodgeLattice_of_cotangent hPC hT hT35)

/-- **Glue piece 5 of `GluePieces` (P2, `ProductModelHeight`) from T35, `ProductCotangent` and
`TangentDimAtOrigin` (proved).** -/
theorem productModelHeight_of_cotangent (hT35 : ZInQ.LeafPush2.UniformizationExists)
    (hPC : ProductCotangent) (hT : TangentDimAtOrigin) : ZInQ.H5Neron.ProductModelHeight :=
  ZInQ.ProductUnif.productModelHeight_of_local (hodgeLatticeTheorem_of_tangent hT dimBaseChange)
    (productUnifDims_of_uniformizationExists hT35) ZInQ.Metrization2.productLocalStructure
    (productHodgeLattice_of_cotangent hPC hT hT35)

end ZInQ.UnifDims



open CategoryTheory Limits

namespace ZInQ.UnifDims

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open NumberField ZInQ.DefFaltings

variable {K : Type} [Field K] {L : Type} [Field L] [NumberField L] [Algebra K L]

section CotMap

variable {A C : AbVar K} (𝒢 : GroupModel C L) (ℋ : GroupModel A L)

/-- The stalk map at the generic units of a morphism of models preserving them. -/
noncomputable abbrev germMap (φ : 𝒢.G ⟶ ℋ.G) (h : φ.left 𝒢.genericUnit = ℋ.genericUnit) :
    ℋ.genStalk →+* 𝒢.genStalk :=
  (φ.left.stalkMapAt h).hom

/-- A morphism of models over `Spec 𝓞_L` is compatible with the structure maps. -/
theorem germMap_structMap (φ : 𝒢.G ⟶ ℋ.G) (h : φ.left 𝒢.genericUnit = ℋ.genericUnit)
    (c : 𝓞 L) : germMap 𝒢 ℋ φ h (ℋ.structMap c) = 𝒢.structMap c := by
  rw [HodgeLattice.structMap_eq, HodgeLattice.structMap_eq, germMap,
    Scheme.Hom.stalkMapAt_germ_top]
  congr 1
  rw [← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop, Over.w φ]

/-- **The cotangent map** `cot_ℋ → cot_𝒢`, `df ↦ d(φ* f)`. -/
noncomputable def cotMap (φ : 𝒢.G ⟶ ℋ.G) (h : φ.left 𝒢.genericUnit = ℋ.genericUnit) :
    ℋ.cotangent →ₗ[𝓞 L] 𝒢.cotangent := by
  let ρ := germMap 𝒢 ℋ φ h
  letI : Module ℋ.genStalk 𝒢.cotangent := Module.compHom _ ρ
  let f : IsLocalRing.maximalIdeal ℋ.genStalk →ₗ[ℋ.genStalk] 𝒢.cotangent :=
    { toFun := fun x => 𝒢.dCls ⟨ρ x, map_nonunit ρ _ x.2⟩
      map_add' := fun x y => by
        simp only [GroupModel.dCls]
        have e : (⟨ρ ↑(x + y), map_nonunit ρ _ (x + y).2⟩ :
            IsLocalRing.maximalIdeal 𝒢.genStalk) =
            (⟨ρ x, map_nonunit ρ _ x.2⟩ : IsLocalRing.maximalIdeal 𝒢.genStalk) +
              ⟨ρ y, map_nonunit ρ _ y.2⟩ := Subtype.ext (by simp)
        refine (congrArg (IsLocalRing.maximalIdeal 𝒢.genStalk).toCotangent e).trans ?_
        exact LinearMap.map_add _ _ _
      map_smul' := fun r x => by
        simp only [GroupModel.dCls, RingHom.id_apply]
        have e : (⟨ρ ↑(r • x), map_nonunit ρ _ (r • x).2⟩ : IsLocalRing.maximalIdeal 𝒢.genStalk) =
            ρ r • (⟨ρ x, map_nonunit ρ _ x.2⟩ : IsLocalRing.maximalIdeal 𝒢.genStalk) :=
          Subtype.ext (by simp [ρ])
        refine (congrArg (IsLocalRing.maximalIdeal 𝒢.genStalk).toCotangent e).trans ?_
        exact LinearMap.map_smul _ _ _ }
  let j0 : ℋ.cotangent →ₗ[ℋ.genStalk] 𝒢.cotangent := Ideal.Cotangent.lift f (fun x y => by
    refine (Ideal.toCotangent_eq_zero _ _).mpr ?_
    show ρ (↑x * ↑y) ∈ _
    rw [map_mul, pow_two]
    exact Ideal.mul_mem_mul (map_nonunit ρ _ x.2) (map_nonunit ρ _ y.2))
  exact
    { toFun := j0
      map_add' := j0.map_add
      map_smul' := fun c x => by
        show j0 (ℋ.structMap c • x) = 𝒢.structMap c • j0 x
        rw [j0.map_smul]
        show ρ (ℋ.structMap c) • j0 x = _
        rw [germMap_structMap] }

theorem cotMap_dCls (φ : 𝒢.G ⟶ ℋ.G) (h : φ.left 𝒢.genericUnit = ℋ.genericUnit)
    (f : IsLocalRing.maximalIdeal ℋ.genStalk) :
    cotMap 𝒢 ℋ φ h (ℋ.dCls f) =
      𝒢.dCls ⟨germMap 𝒢 ℋ φ h f, map_nonunit (germMap 𝒢 ℋ φ h) _ f.2⟩ := by
  rfl


theorem cotMap_comp {B : AbVar K} (𝒦 : GroupModel B L) (φ : 𝒢.G ⟶ ℋ.G) (ψ : ℋ.G ⟶ 𝒦.G)
    (h : φ.left 𝒢.genericUnit = ℋ.genericUnit) (h' : ψ.left ℋ.genericUnit = 𝒦.genericUnit)
    (h'' : (φ ≫ ψ).left 𝒢.genericUnit = 𝒦.genericUnit) :
    cotMap 𝒢 𝒦 (φ ≫ ψ) h'' = cotMap 𝒢 ℋ φ h ∘ₗ cotMap ℋ 𝒦 ψ h' := by
  apply LinearMap.ext
  intro x
  obtain ⟨f, rfl⟩ := (IsLocalRing.maximalIdeal 𝒦.genStalk).toCotangent_surjective x
  change cotMap 𝒢 𝒦 (φ ≫ ψ) h'' (𝒦.dCls f) = cotMap 𝒢 ℋ φ h (cotMap ℋ 𝒦 ψ h' (𝒦.dCls f))
  rw [cotMap_dCls, cotMap_dCls, cotMap_dCls]
  congr 2
  simp only [germMap]
  rw [Scheme.Hom.stalkMapAt_congr (Over.comp_left _ _ _ φ ψ) h'' (by rw [← h', ← h]; rfl),
    Scheme.Hom.stalkMapAt_comp φ.left ψ.left h h']
  rfl

theorem cotMap_id (h : (𝟙 𝒢.G : 𝒢.G ⟶ 𝒢.G).left 𝒢.genericUnit = 𝒢.genericUnit) :
    cotMap 𝒢 𝒢 (𝟙 𝒢.G) h = LinearMap.id := by
  apply LinearMap.ext
  intro x
  obtain ⟨f, rfl⟩ := (IsLocalRing.maximalIdeal 𝒢.genStalk).toCotangent_surjective x
  change cotMap 𝒢 𝒢 (𝟙 𝒢.G) h (𝒢.dCls f) = 𝒢.dCls f
  rw [cotMap_dCls]
  congr 2
  simp only [germMap]
  rw [Scheme.Hom.stalkMapAt_congr (Over.id_left 𝒢.G) h h, Scheme.Hom.stalkMapAt_id]
  rfl

/-- A morphism of models preserving the unit sections maps every `e(s)` to `e(s)`. -/
theorem map_unitSection (φ : 𝒢.G ⟶ ℋ.G) (hφ : η[𝒢.G] ≫ φ = η[ℋ.G])
    (s : Spec (CommRingCat.of (𝓞 L))) : φ.left (𝒢.unitSection s) = ℋ.unitSection s := by
  have h2 : 𝒢.unitSection ≫ φ.left = ℋ.unitSection := by
    unfold GroupModel.unitSection
    rw [← Over.comp_left, hφ]
  rw [← h2]
  rfl

/-- **Functoriality of `ω`.** A morphism of models preserving the unit sections maps
`ω_ℋ` into `ω_𝒢` under the cotangent map. -/
theorem omega_map_le (φ : 𝒢.G ⟶ ℋ.G) (hφ : η[𝒢.G] ≫ φ = η[ℋ.G])
    (h : φ.left 𝒢.genericUnit = ℋ.genericUnit) :
    ℋ.omega.map (cotMap 𝒢 ℋ φ h) ≤ 𝒢.omega := by
  refine le_iInf fun s => (Submodule.map_mono (iInf_le _ s)).trans ?_
  rw [GroupModel.omegaAt, Submodule.map_span, Submodule.span_le]
  rintro _ ⟨_, ⟨f, hf, hfm, rfl⟩, rfl⟩
  have hs := map_unitSection 𝒢 ℋ φ hφ s
  set f' := (φ.left.stalkMapAt hs).hom f with hf'
  have h2 : 𝒢.unitSection ≫ φ.left = ℋ.unitSection := by
    unfold GroupModel.unitSection
    rw [← Over.comp_left, hφ]
  have hker : f' ∈ RingHom.ker (𝒢.unitSection.stalkMap s).hom := by
    rw [RingHom.mem_ker] at hf ⊢
    have e1 := Scheme.Hom.stalkMapAt_comp 𝒢.unitSection φ.left (rfl : 𝒢.unitSection s = _) hs
      (by rw [← hs]; rfl)
    rw [Scheme.Hom.stalkMapAt_congr h2 _ rfl, Scheme.Hom.stalkMapAt_rfl,
      Scheme.Hom.stalkMapAt_rfl] at e1
    rw [hf', ← CommRingCat.comp_apply, ← e1, hf]
  have hspec : 𝒢.G.left.presheaf.stalkSpecializes (𝒢.specializes_genericUnit s) f' =
      germMap 𝒢 ℋ φ h (ℋ.G.left.presheaf.stalkSpecializes (ℋ.specializes_genericUnit s) f) :=
    Scheme.Hom.stalkMapAt_stalkSpecializes φ.left _ _ h hs f
  have hm : 𝒢.G.left.presheaf.stalkSpecializes (𝒢.specializes_genericUnit s) f' ∈
      IsLocalRing.maximalIdeal 𝒢.genStalk := by
    rw [hspec]; exact map_nonunit (germMap 𝒢 ℋ φ h) _ hfm
  apply Submodule.subset_span
  refine ⟨f', hker, hm, ?_⟩
  rw [cotMap_dCls]
  congr 2
  exact hspec.symm

theorem cotMap_congr {φ φ' : 𝒢.G ⟶ ℋ.G} (e : φ = φ') (h : φ.left 𝒢.genericUnit = ℋ.genericUnit)
    (h' : φ'.left 𝒢.genericUnit = ℋ.genericUnit) : cotMap 𝒢 ℋ φ h = cotMap 𝒢 ℋ φ' h' := by
  subst e; rfl

end CotMap

section Helpers

variable {X : AbVar K} (𝒢 : GroupModel X L)

/-- The unit section is a section of the structure morphism (copied from infra-stalks). -/
theorem unitSection_comp_hom : 𝒢.unitSection ≫ 𝒢.G.hom = 𝟙 _ := by
  unfold GroupModel.unitSection
  simpa using Over.w η[𝒢.G]

theorem hom_genericUnit : 𝒢.G.hom 𝒢.genericUnit = genericPt L := by
  unfold GroupModel.genericUnit
  rw [← Scheme.Hom.comp_apply, unitSection_comp_hom]
  rfl

theorem rationalOver_genericUnit : RationalOver 𝒢.G.hom 𝒢.genericUnit :=
  rationalOver_of_section _ _ (unitSection_comp_hom 𝒢) (genericPt L)

omit [Algebra K L] in
/-- The stalk of `Spec 𝓞_L` at its generic point is a field (copied from infra-stalks). -/
theorem maximalIdeal_stalk_genericPt :
    IsLocalRing.maximalIdeal ((Spec (CommRingCat.of (𝓞 L))).presheaf.stalk (genericPt L)) = ⊥ := by
  have h : genericPt L = genericPoint (Spec (CommRingCat.of (𝓞 L))) := by
    rw [genericPoint_eq_bot_of_affine]; rfl
  refine (IsLocalRing.isField_iff_maximalIdeal_eq).mp ?_
  rw [h]
  exact Field.toIsField (Spec (CommRingCat.of (𝓞 L))).functionField

end Helpers

section Trivial

variable {A C : AbVar K} (𝒢 : GroupModel C L) (ℋ : GroupModel A L)

/-- A morphism of models that factors through `Spec 𝓞_L` kills `𝔪` at the generic units. -/
theorem germMap_eq_zero_of_factor (φ : 𝒢.G ⟶ ℋ.G) (h : φ.left 𝒢.genericUnit = ℋ.genericUnit)
    (b : Spec (CommRingCat.of (𝓞 L)) ⟶ ℋ.G.left) (hφ : φ.left = 𝒢.G.hom ≫ b)
    (a : ℋ.genStalk) (ha : a ∈ IsLocalRing.maximalIdeal ℋ.genStalk) : germMap 𝒢 ℋ φ h a = 0 := by
  have h1 : 𝒢.G.hom 𝒢.genericUnit = genericPt L := hom_genericUnit 𝒢
  have h2 : b (genericPt L) = ℋ.genericUnit := by
    rw [← h, hφ, Scheme.Hom.comp_apply, h1]
  simp only [germMap]
  rw [Scheme.Hom.stalkMapAt_congr hφ h (by rw [Scheme.Hom.comp_apply, h1, h2]),
    Scheme.Hom.stalkMapAt_comp 𝒢.G.hom b h1 h2]
  have hz : (b.stalkMapAt h2).hom a = 0 := by
    have hm := map_nonunit (b.stalkMapAt h2).hom a ha
    rw [maximalIdeal_stalk_genericPt] at hm
    exact (Submodule.mem_bot _).mp hm
  rw [CommRingCat.comp_apply, hz, map_zero]

end Trivial

section Product

variable {A B C : AbVar K} (𝒢P : GroupModel C L) (𝒢₁ : GroupModel A L) (𝒢₂ : GroupModel B L)
  (e : 𝒢P.G ≅ 𝒢₁.G ⊗ 𝒢₂.G) [IsMonHom (e.hom ≫ fst _ _)] [IsMonHom (e.hom ≫ snd _ _)]

/-- `x ↦ (x, 1)`. -/
noncomputable def inc₁ : 𝒢₁.G ⟶ 𝒢P.G := lift (𝟙 _) (toUnit _ ≫ η[𝒢₂.G]) ≫ e.inv

/-- `y ↦ (1, y)`. -/
noncomputable def inc₂ : 𝒢₂.G ⟶ 𝒢P.G := lift (toUnit _ ≫ η[𝒢₁.G]) (𝟙 _) ≫ e.inv

theorem eta_e : η[𝒢P.G] ≫ e.hom = lift η[𝒢₁.G] η[𝒢₂.G] := by
  apply CartesianMonoidalCategory.hom_ext
  · rw [Category.assoc, IsMonHom.one_hom, lift_fst]
  · rw [Category.assoc, IsMonHom.one_hom, lift_snd]

theorem eta_inc₁ : η[𝒢₁.G] ≫ inc₁ 𝒢P 𝒢₁ 𝒢₂ e = η[𝒢P.G] := by
  rw [inc₁, ← Category.assoc, Iso.comp_inv_eq, eta_e]
  apply CartesianMonoidalCategory.hom_ext <;> simp

theorem eta_inc₂ : η[𝒢₂.G] ≫ inc₂ 𝒢P 𝒢₁ 𝒢₂ e = η[𝒢P.G] := by
  rw [inc₂, ← Category.assoc, Iso.comp_inv_eq, eta_e]
  apply CartesianMonoidalCategory.hom_ext <;> simp

theorem inc₁_p₁ : inc₁ 𝒢P 𝒢₁ 𝒢₂ e ≫ (e.hom ≫ fst _ _) = 𝟙 _ := by simp [inc₁]
theorem inc₁_p₂ : inc₁ 𝒢P 𝒢₁ 𝒢₂ e ≫ (e.hom ≫ snd _ _) = toUnit _ ≫ η[𝒢₂.G] := by simp [inc₁]
theorem inc₂_p₁ : inc₂ 𝒢P 𝒢₁ 𝒢₂ e ≫ (e.hom ≫ fst _ _) = toUnit _ ≫ η[𝒢₁.G] := by simp [inc₂]
theorem inc₂_p₂ : inc₂ 𝒢P 𝒢₁ 𝒢₂ e ≫ (e.hom ≫ snd _ _) = 𝟙 _ := by simp [inc₂]

theorem toUnit_eta_left {X Y : AbVar K} (𝒳 : GroupModel X L) (𝒴 : GroupModel Y L) :
    (toUnit 𝒳.G ≫ η[𝒴.G]).left = 𝒳.G.hom ≫ 𝒴.unitSection := rfl

theorem hp₁ : (e.hom ≫ fst _ _).left 𝒢P.genericUnit = 𝒢₁.genericUnit :=
  map_unitSection 𝒢P 𝒢₁ _ (IsMonHom.one_hom _) (genericPt L)
theorem hp₂ : (e.hom ≫ snd _ _).left 𝒢P.genericUnit = 𝒢₂.genericUnit :=
  map_unitSection 𝒢P 𝒢₂ _ (IsMonHom.one_hom _) (genericPt L)
theorem hi₁ : (inc₁ 𝒢P 𝒢₁ 𝒢₂ e).left 𝒢₁.genericUnit = 𝒢P.genericUnit :=
  map_unitSection 𝒢₁ 𝒢P _ (eta_inc₁ 𝒢P 𝒢₁ 𝒢₂ e) (genericPt L)
theorem hi₂ : (inc₂ 𝒢P 𝒢₁ 𝒢₂ e).left 𝒢₂.genericUnit = 𝒢P.genericUnit :=
  map_unitSection 𝒢₂ 𝒢P _ (eta_inc₂ 𝒢P 𝒢₁ 𝒢₂ e) (genericPt L)

/-- A retraction on stalks. -/
theorem retract_apply {X Y : Scheme.{0}} (f : X ⟶ Y) (g : Y ⟶ X) (hfg : f ≫ g = 𝟙 X) {x : X}
    {y : Y} (hf : f x = y) (hg : g y = x) (a : X.presheaf.stalk x) :
    (f.stalkMapAt hf).hom ((g.stalkMapAt hg).hom a) = a := by
  subst hf
  have h1 : (f ≫ g).stalkMapAt hg = g.stalkMapAt hg ≫ f.stalkMapAt rfl :=
    Scheme.Hom.stalkMapAt_comp f g rfl hg hg
  rw [← CommRingCat.comp_apply, ← h1]
  have key : ∀ (k : X ⟶ X) (_ : k = 𝟙 X) (h : k x = x), (k.stalkMapAt h).hom a = a := by
    intro k hk h; subst hk; rw [Scheme.Hom.stalkMapAt_id]; rfl
  exact key _ hfg hg

/-- germ-level retraction identities -/
theorem germ_retract₁ (a : 𝒢₁.genStalk) :
    germMap 𝒢₁ 𝒢P _ (hi₁ 𝒢P 𝒢₁ 𝒢₂ e) (germMap 𝒢P 𝒢₁ _ (hp₁ 𝒢P 𝒢₁ 𝒢₂ e) a) = a :=
  retract_apply _ _ (by rw [← Over.comp_left, inc₁_p₁]; rfl) _ _ a

theorem germ_retract₂ (a : 𝒢₂.genStalk) :
    germMap 𝒢₂ 𝒢P _ (hi₂ 𝒢P 𝒢₁ 𝒢₂ e) (germMap 𝒢P 𝒢₂ _ (hp₂ 𝒢P 𝒢₁ 𝒢₂ e) a) = a :=
  retract_apply _ _ (by rw [← Over.comp_left, inc₂_p₂]; rfl) _ _ a

theorem germ_cross₁₂ (a : 𝒢₂.genStalk) (ha : a ∈ IsLocalRing.maximalIdeal 𝒢₂.genStalk) :
    germMap 𝒢₁ 𝒢P _ (hi₁ 𝒢P 𝒢₁ 𝒢₂ e) (germMap 𝒢P 𝒢₂ _ (hp₂ 𝒢P 𝒢₁ 𝒢₂ e) a) = 0 := by
  have hc : (inc₁ 𝒢P 𝒢₁ 𝒢₂ e ≫ (e.hom ≫ snd _ _)).left 𝒢₁.genericUnit = 𝒢₂.genericUnit := by
    rw [Over.comp_left, Scheme.Hom.comp_apply, hi₁, hp₂]
  have := germMap_eq_zero_of_factor 𝒢₁ 𝒢₂ _ hc 𝒢₂.unitSection
    (by rw [inc₁_p₂]; rfl) a ha
  simp only [germMap] at this ⊢
  rw [Scheme.Hom.stalkMapAt_congr (Over.comp_left _ _ _ _ _) hc
    (by rw [Scheme.Hom.comp_apply, hi₁, hp₂]),
    Scheme.Hom.stalkMapAt_comp _ _ (hi₁ 𝒢P 𝒢₁ 𝒢₂ e) (hp₂ 𝒢P 𝒢₁ 𝒢₂ e)] at this
  exact this

theorem germ_cross₂₁ (a : 𝒢₁.genStalk) (ha : a ∈ IsLocalRing.maximalIdeal 𝒢₁.genStalk) :
    germMap 𝒢₂ 𝒢P _ (hi₂ 𝒢P 𝒢₁ 𝒢₂ e) (germMap 𝒢P 𝒢₁ _ (hp₁ 𝒢P 𝒢₁ 𝒢₂ e) a) = 0 := by
  have hc : (inc₂ 𝒢P 𝒢₁ 𝒢₂ e ≫ (e.hom ≫ fst _ _)).left 𝒢₂.genericUnit = 𝒢₁.genericUnit := by
    rw [Over.comp_left, Scheme.Hom.comp_apply, hi₂, hp₁]
  have := germMap_eq_zero_of_factor 𝒢₂ 𝒢₁ _ hc 𝒢₁.unitSection
    (by rw [inc₂_p₁]; rfl) a ha
  simp only [germMap] at this ⊢
  rw [Scheme.Hom.stalkMapAt_congr (Over.comp_left _ _ _ _ _) hc
    (by rw [Scheme.Hom.comp_apply, hi₂, hp₁]),
    Scheme.Hom.stalkMapAt_comp _ _ (hi₂ 𝒢P 𝒢₁ 𝒢₂ e) (hp₁ 𝒢P 𝒢₁ 𝒢₂ e)] at this
  exact this

end Product


section ProductCot

variable {A B C : AbVar K} (𝒢P : GroupModel C L) (𝒢₁ : GroupModel A L) (𝒢₂ : GroupModel B L)
  (e : 𝒢P.G ≅ 𝒢₁.G ⊗ 𝒢₂.G) [IsMonHom (e.hom ≫ fst _ _)] [IsMonHom (e.hom ≫ snd _ _)]

/-- **The generic stalk of a product, modulo `𝔪²`.** For `m ∈ 𝔪_P`:
`m ≡ p₁*(i₁* m) + p₂*(i₂* m) (mod 𝔪_P²)` (infra-stalks' `pullback_stalkGen`,
`maximalIdeal_eq_of_stalkGen`, `exists_sub_mem_maximalIdeal_of_stalkGen`). -/
theorem germ_decomp (m : 𝒢P.genStalk) (hm : m ∈ IsLocalRing.maximalIdeal 𝒢P.genStalk) :
    m - germMap 𝒢P 𝒢₁ _ (hp₁ 𝒢P 𝒢₁ 𝒢₂ e) (germMap 𝒢₁ 𝒢P _ (hi₁ 𝒢P 𝒢₁ 𝒢₂ e) m) -
      germMap 𝒢P 𝒢₂ _ (hp₂ 𝒢P 𝒢₁ 𝒢₂ e) (germMap 𝒢₂ 𝒢P _ (hi₂ 𝒢P 𝒢₁ 𝒢₂ e) m) ∈
      IsLocalRing.maximalIdeal 𝒢P.genStalk ^ 2 := by
  set p := (e.hom ≫ fst 𝒢₁.G 𝒢₂.G).left with hpdef
  set q := (e.hom ≫ snd 𝒢₁.G 𝒢₂.G).left with hqdef
  have w : p ≫ 𝒢₁.G.hom = q ≫ 𝒢₂.G.hom := by rw [hpdef, hqdef, Over.w, Over.w]
  have hgen : StalkGen p q 𝒢P.genericUnit :=
    StalkGen.comp_of_isIso e.hom.left (pullback.fst 𝒢₁.G.hom 𝒢₂.G.hom) (pullback.snd _ _) _
      (pullback_stalkGen _ _ _)
  have hrat₁ : RationalOver 𝒢₁.G.hom (p 𝒢P.genericUnit) := by
    rw [hpdef, hp₁]; exact rationalOver_genericUnit 𝒢₁
  have hrat₂ : RationalOver 𝒢₂.G.hom (q 𝒢P.genericUnit) := by
    rw [hqdef, hp₂]; exact rationalOver_genericUnit 𝒢₂
  have hm0 := maximalIdeal_eq_of_stalkGen w hgen hrat₁
  have hmax : IsLocalRing.maximalIdeal 𝒢P.genStalk =
      (IsLocalRing.maximalIdeal 𝒢₁.genStalk).map (germMap 𝒢P 𝒢₁ _ (hp₁ 𝒢P 𝒢₁ 𝒢₂ e)) ⊔
        (IsLocalRing.maximalIdeal 𝒢₂.genStalk).map (germMap 𝒢P 𝒢₂ _ (hp₂ 𝒢P 𝒢₁ 𝒢₂ e)) := by
    rw [hm0, stalkIdeal, germMap, germMap, Scheme.Hom.map_stalkMapAt_maximalIdeal,
      Scheme.Hom.map_stalkMapAt_maximalIdeal]
  have hr₂ : ∀ r, ∃ c, r - germMap 𝒢P 𝒢₂ _ (hp₂ 𝒢P 𝒢₁ 𝒢₂ e) c ∈
      IsLocalRing.maximalIdeal 𝒢P.genStalk := by
    intro r
    obtain ⟨b, hb⟩ := exists_sub_mem_maximalIdeal_of_stalkGen w hgen hrat₁ r
    obtain ⟨c, hc⟩ := Scheme.Hom.exists_stalkMapAt_eq q (hp₂ 𝒢P 𝒢₁ 𝒢₂ e) b
    exact ⟨c, by rw [germMap, hc]; exact hb⟩
  have hr₁ : ∀ r, ∃ c, r - germMap 𝒢P 𝒢₁ _ (hp₁ 𝒢P 𝒢₁ 𝒢₂ e) c ∈
      IsLocalRing.maximalIdeal 𝒢P.genStalk := by
    intro r
    obtain ⟨b, hb⟩ := exists_sub_mem_maximalIdeal_of_stalkGen w.symm hgen.symm hrat₂ r
    obtain ⟨c, hc⟩ := Scheme.Hom.exists_stalkMapAt_eq p (hp₁ 𝒢P 𝒢₁ 𝒢₂ e) b
    exact ⟨c, by rw [germMap, hc]; exact hb⟩
  exact IsLocalRing.sub_mem_maximalIdeal_sq_of_product₂ _ _ _ _ (germ_retract₁ 𝒢P 𝒢₁ 𝒢₂ e)
    (germ_retract₂ 𝒢P 𝒢₁ 𝒢₂ e)
    (fun a ha => by rw [germ_cross₁₂ 𝒢P 𝒢₁ 𝒢₂ e a ha]; exact Ideal.zero_mem _)
    (fun a ha => by rw [germ_cross₂₁ 𝒢P 𝒢₁ 𝒢₂ e a ha]; exact Ideal.zero_mem _) hmax hr₁ hr₂ hm

/-- **The cotangent space of a product.** `x = j₁(ψ₁ x) + j₂(ψ₂ x)`. -/
theorem cot_decomp (x : 𝒢P.cotangent) :
    x = cotMap 𝒢P 𝒢₁ _ (hp₁ 𝒢P 𝒢₁ 𝒢₂ e) (cotMap 𝒢₁ 𝒢P _ (hi₁ 𝒢P 𝒢₁ 𝒢₂ e) x) +
      cotMap 𝒢P 𝒢₂ _ (hp₂ 𝒢P 𝒢₁ 𝒢₂ e) (cotMap 𝒢₂ 𝒢P _ (hi₂ 𝒢P 𝒢₁ 𝒢₂ e) x) := by
  obtain ⟨m, rfl⟩ := (IsLocalRing.maximalIdeal 𝒢P.genStalk).toCotangent_surjective x
  change 𝒢P.dCls m = cotMap 𝒢P 𝒢₁ _ _ (cotMap 𝒢₁ 𝒢P _ _ (𝒢P.dCls m)) +
    cotMap 𝒢P 𝒢₂ _ _ (cotMap 𝒢₂ 𝒢P _ _ (𝒢P.dCls m))
  rw [cotMap_dCls, cotMap_dCls, cotMap_dCls, cotMap_dCls]
  refine ((Ideal.toCotangent_eq _).mpr ?_).trans
    (map_add (IsLocalRing.maximalIdeal 𝒢P.genStalk).toCotangent _ _)
  show (m : 𝒢P.genStalk) - (_ + _) ∈ _
  rw [← sub_sub]
  exact germ_decomp 𝒢P 𝒢₁ 𝒢₂ e m m.2

end ProductCot

end ZInQ.UnifDims



/-! ## unif-dims: `ProductCotangent`, proved -/

namespace ZInQ.UnifDims

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open NumberField ZInQ.DefFaltings

/-- **`ProductCotangent`, proved** (the statement is the body of `ZInQ.UnifDims.ProductCotangent`).
`jᵢ` is the cotangent map of the projection `pᵢ`; the retractions are the cotangent maps of
`x ↦ (x, 1)` and `y ↦ (1, y)`; `cot_decomp` gives surjectivity, the retractions injectivity, and
`omega_map_le` (functoriality of `ω`) the lattice. -/
theorem productCotangent_aux :
  ∀ (K : Type) [Field K] (A B C : AbVar K) (L : Type) [Field L] [NumberField L] [Algebra K L]
    (𝒢P : GroupModel C L) (𝒢₁ : GroupModel A L) (𝒢₂ : GroupModel B L)
    (e : 𝒢P.G ≅ 𝒢₁.G ⊗ 𝒢₂.G) (hfst : IsMonHom (e.hom ≫ fst _ _))
    (hsnd : IsMonHom (e.hom ≫ snd _ _)),
    ∃ (j₁ : 𝒢₁.cotangent →ₗ[𝓞 L] 𝒢P.cotangent) (j₂ : 𝒢₂.cotangent →ₗ[𝓞 L] 𝒢P.cotangent),
      (∀ f : IsLocalRing.maximalIdeal 𝒢₁.genStalk,
        ∃ h : (ZInQ.Metrization.pullGerm (e.hom ≫ fst _ _)).hom (f : 𝒢₁.genStalk) ∈
          IsLocalRing.maximalIdeal 𝒢P.genStalk, j₁ (𝒢₁.dCls f) = 𝒢P.dCls ⟨_, h⟩) ∧
      (∀ f : IsLocalRing.maximalIdeal 𝒢₂.genStalk,
        ∃ h : (ZInQ.Metrization.pullGerm (e.hom ≫ snd _ _)).hom (f : 𝒢₂.genStalk) ∈
          IsLocalRing.maximalIdeal 𝒢P.genStalk, j₂ (𝒢₂.dCls f) = 𝒢P.dCls ⟨_, h⟩) ∧
      Function.Bijective (LinearMap.coprod j₁ j₂) ∧
      𝒢P.omega = 𝒢₁.omega.map j₁ ⊔ 𝒢₂.omega.map j₂ := by
  intro K _ A B C L _ _ _ 𝒢P 𝒢₁ 𝒢₂ e hfst hsnd
  set j₁ := cotMap 𝒢P 𝒢₁ _ (hp₁ 𝒢P 𝒢₁ 𝒢₂ e) with hj₁
  set j₂ := cotMap 𝒢P 𝒢₂ _ (hp₂ 𝒢P 𝒢₁ 𝒢₂ e) with hj₂
  set ψ₁ := cotMap 𝒢₁ 𝒢P _ (hi₁ 𝒢P 𝒢₁ 𝒢₂ e) with hψ₁
  set ψ₂ := cotMap 𝒢₂ 𝒢P _ (hi₂ 𝒢P 𝒢₁ 𝒢₂ e) with hψ₂
  have r11 : ∀ a, ψ₁ (j₁ a) = a := by
    intro a
    obtain ⟨f, rfl⟩ := (IsLocalRing.maximalIdeal 𝒢₁.genStalk).toCotangent_surjective a
    change ψ₁ (j₁ (𝒢₁.dCls f)) = 𝒢₁.dCls f
    rw [hψ₁, hj₁, cotMap_dCls, cotMap_dCls]
    congr 1
    exact Subtype.ext (germ_retract₁ 𝒢P 𝒢₁ 𝒢₂ e f)
  have r22 : ∀ a, ψ₂ (j₂ a) = a := by
    intro a
    obtain ⟨f, rfl⟩ := (IsLocalRing.maximalIdeal 𝒢₂.genStalk).toCotangent_surjective a
    change ψ₂ (j₂ (𝒢₂.dCls f)) = 𝒢₂.dCls f
    rw [hψ₂, hj₂, cotMap_dCls, cotMap_dCls]
    congr 1
    exact Subtype.ext (germ_retract₂ 𝒢P 𝒢₁ 𝒢₂ e f)
  have r12 : ∀ c, ψ₁ (j₂ c) = 0 := by
    intro c
    obtain ⟨f, rfl⟩ := (IsLocalRing.maximalIdeal 𝒢₂.genStalk).toCotangent_surjective c
    change ψ₁ (j₂ (𝒢₂.dCls f)) = 0
    rw [hψ₁, hj₂, cotMap_dCls, cotMap_dCls]
    have h0 : (⟨_, map_nonunit _ _ (map_nonunit _ _ f.2)⟩ :
        IsLocalRing.maximalIdeal 𝒢₁.genStalk) = 0 :=
      Subtype.ext (germ_cross₁₂ 𝒢P 𝒢₁ 𝒢₂ e f f.2)
    exact (congrArg (IsLocalRing.maximalIdeal 𝒢₁.genStalk).toCotangent h0).trans (map_zero _)
  have r21 : ∀ a, ψ₂ (j₁ a) = 0 := by
    intro a
    obtain ⟨f, rfl⟩ := (IsLocalRing.maximalIdeal 𝒢₁.genStalk).toCotangent_surjective a
    change ψ₂ (j₁ (𝒢₁.dCls f)) = 0
    rw [hψ₂, hj₁, cotMap_dCls, cotMap_dCls]
    have h0 : (⟨_, map_nonunit _ _ (map_nonunit _ _ f.2)⟩ :
        IsLocalRing.maximalIdeal 𝒢₂.genStalk) = 0 :=
      Subtype.ext (germ_cross₂₁ 𝒢P 𝒢₁ 𝒢₂ e f f.2)
    exact (congrArg (IsLocalRing.maximalIdeal 𝒢₂.genStalk).toCotangent h0).trans (map_zero _)
  have dec : ∀ x, x = j₁ (ψ₁ x) + j₂ (ψ₂ x) := cot_decomp 𝒢P 𝒢₁ 𝒢₂ e
  refine ⟨j₁, j₂, fun f => ⟨map_nonunit (germMap 𝒢P 𝒢₁ _ (hp₁ 𝒢P 𝒢₁ 𝒢₂ e)) _ f.2, ?_⟩,
    fun f => ⟨map_nonunit (germMap 𝒢P 𝒢₂ _ (hp₂ 𝒢P 𝒢₁ 𝒢₂ e)) _ f.2, ?_⟩,
    ⟨?_, ?_⟩, ?_⟩
  · rw [hj₁, cotMap_dCls]; rfl
  · rw [hj₂, cotMap_dCls]; rfl
  · rintro ⟨a, c⟩ ⟨a', c'⟩ h
    simp only [LinearMap.coprod_apply] at h
    have h1 := congrArg ψ₁ h
    have h2 := congrArg ψ₂ h
    simp only [map_add, r11, r12, r21, r22, add_zero, zero_add] at h1 h2
    rw [h1, h2]
  · intro x
    exact ⟨(ψ₁ x, ψ₂ x), by rw [LinearMap.coprod_apply]; exact (dec x).symm⟩
  · refine le_antisymm (fun x hx => ?_) (sup_le ?_ ?_)
    · rw [dec x]
      exact Submodule.add_mem_sup
        (Submodule.mem_map_of_mem (omega_map_le 𝒢₁ 𝒢P _ (eta_inc₁ 𝒢P 𝒢₁ 𝒢₂ e)
          (hi₁ 𝒢P 𝒢₁ 𝒢₂ e) (Submodule.mem_map_of_mem hx)))
        (Submodule.mem_map_of_mem (omega_map_le 𝒢₂ 𝒢P _ (eta_inc₂ 𝒢P 𝒢₁ 𝒢₂ e)
          (hi₂ 𝒢P 𝒢₁ 𝒢₂ e) (Submodule.mem_map_of_mem hx)))
    · exact omega_map_le 𝒢P 𝒢₁ _ (IsMonHom.one_hom _) (hp₁ 𝒢P 𝒢₁ 𝒢₂ e)
    · exact omega_map_le 𝒢P 𝒢₂ _ (IsMonHom.one_hom _) (hp₂ 𝒢P 𝒢₁ 𝒢₂ e)

end ZInQ.UnifDims




/-! ## unif-dims: `ProductCotangent` closed; `ProductHodgeLattice` from `TangentDimAtOrigin` and T35 -/

namespace ZInQ.UnifDims

open ZInQ.DefFaltings.HodgeLattice

/-- **`ProductCotangent`, proved** (`productCotangent_aux`, `PC.lean`). -/
theorem productCotangent : ProductCotangent := productCotangent_aux

/-- **metrization's `ProductHodgeLattice` from hodge-lattice's `TangentDimAtOrigin` and the
textbook leaf T35 (proved).** -/
theorem productHodgeLattice_of_tangentDim (hT : TangentDimAtOrigin)
    (hT35 : ZInQ.LeafPush2.UniformizationExists) : ZInQ.Metrization.ProductHodgeLattice :=
  productHodgeLattice_of_cotangent productCotangent hT hT35

end ZInQ.UnifDims




/-! ## unif-dims: S-alg and P2 from T35 and `TangentDimAtOrigin` alone -/

namespace ZInQ.UnifDims

open ZInQ.DefFaltings ZInQ.DefFaltings.HodgeLattice

/-- **S-alg (`ProductMetrizationOfProductUnif`) from T35 and `TangentDimAtOrigin` (proved).** -/
theorem productMetrizationOfProductUnif_of_tangentDim (hT35 : ZInQ.LeafPush2.UniformizationExists)
    (hT : TangentDimAtOrigin) : ZInQ.ProductHeight.ProductMetrizationOfProductUnif :=
  productMetrizationOfProductUnif_of_cotangent hT35 productCotangent hT

/-- **Glue piece 5 of `GluePieces` (P2, `ProductModelHeight`) from the textbook leaf T35 and
hodge-lattice's `TangentDimAtOrigin` (proved).** -/
theorem productModelHeight_of_tangentDim (hT35 : ZInQ.LeafPush2.UniformizationExists)
    (hT : TangentDimAtOrigin) : ZInQ.H5Neron.ProductModelHeight :=
  productModelHeight_of_cotangent hT35 productCotangent hT

end ZInQ.UnifDims


end G0A2_b09_unifdims

section G0A2_b10_abvarbc
/-! ## leaf-fold2: g9-abvarbc (ZInQKernel/Contrib/AbVarBC/*.lean), copied; see mk_abvarbc.py -/

-- ===== ZInQKernel/Contrib/AbVarBC/Dim.lean
section LF2_AbVarBC_Dim

/-!
# Base change of abelian varieties, I: the dimension

Copyright: this file is part of the fork Deicyde/diophantine-z-q (task g9-abvarbc, 2026-11-13).
The proofs of §1-§2 are those of task g0-dim (`scratch/g0-dim/Dim.lean`, namespace `G0Dim`),
moved into the namespace `ZInQ.Contrib.AbVarBC` so that they cannot collide with a later copy.

Main results (Mathlib only, no hypothesis):
* `dim_baseChange_scheme`: for `X` locally of finite type over a field `K` and any field
  extension `L/K`, `dim (X ×_K L) = dim X` (Stacks 00P4, globalized).
* `PkgI3.AbVar.dim_baseChange`: `(A.baseChange L).dim = A.dim` for the project's abelian
  varieties (`ZInQKernel/HDecomp/Objects.lean`).
* `PkgI3.AbVar.dim_finite`: `A.dim` is a natural number.
-/

set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false

open Order TensorProduct

namespace ZInQ.Contrib.AbVarBC

/-! ## §1. Commutative algebra -/
/-- Integral injective extensions have the same Krull dimension (going up + incomparability;
Stacks 00OK, Matsumura Thm 9.4 — STANDARD). -/
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

/-- **Stacks 00P4 (affine case), proved.** For a finitely generated algebra `R` over a field `K`
and any field extension `L/K`, `dim (R ⊗_K L) = dim R`. Proof: Noether normalization
`K[X_1..X_s] → R` (finite, injective) base-changes to `L[X_1..X_s] → R ⊗ L` (finite, injective
since `L` is flat over `K`). -/
theorem ringKrullDim_tensor_field (K : Type*) [Field K] (R : Type*) [CommRing R] [Algebra K R]
    [Algebra.FiniteType K R] (L : Type*) [Field L] [Algebra K L] :
    ringKrullDim (R ⊗[K] L) = ringKrullDim R := by
  rcases subsingleton_or_nontrivial R with h | h
  · haveI : Subsingleton (R ⊗[K] L) := by
      have h1 : (1 : R ⊗[K] L) = 0 := by
        rw [Algebra.TensorProduct.one_def, Subsingleton.elim (1 : R) 0, TensorProduct.zero_tmul]
      exact subsingleton_of_zero_eq_one h1.symm
    rw [ringKrullDim_eq_bot_of_subsingleton, ringKrullDim_eq_bot_of_subsingleton]
  · obtain ⟨s, g, ginj, gfin⟩ := exists_finite_inj_algHom_of_fg K R
    have hR : ringKrullDim R = s := by
      letI := g.toRingHom.toAlgebra
      haveI : Algebra.IsIntegral (MvPolynomial (Fin s) K) R := ⟨gfin.to_isIntegral⟩
      rw [ringKrullDim_eq_of_isIntegral_of_injective (A := MvPolynomial (Fin s) K) ginj,
        ringKrullDim_mvPolynomial_field]
    let g' := Algebra.TensorProduct.map g (AlgHom.id K L)
    have g'inj : Function.Injective g' :=
      Module.Flat.rTensor_preserves_injective_linearMap (M := L) g.toLinearMap ginj
    have g'fin : g'.toRingHom.Finite := RingHom.Finite.tensorProductMap gfin (by exact RingHom.Finite.id L)
    have hP : ringKrullDim (MvPolynomial (Fin s) K ⊗[K] L) = s := by
      rw [ringKrullDim_eq_of_ringEquiv ((Algebra.TensorProduct.comm K _ L).toRingEquiv.trans
        (MvPolynomial.algebraTensorAlgEquiv K L).toRingEquiv), ringKrullDim_mvPolynomial_field]
    rw [hR, ← hP]
    letI := g'.toRingHom.toAlgebra
    haveI : Algebra.IsIntegral (MvPolynomial (Fin s) K ⊗[K] L) (R ⊗[K] L) := ⟨g'fin.to_isIntegral⟩
    exact ringKrullDim_eq_of_isIntegral_of_injective g'inj

/-- A finitely generated algebra over a field has finite Krull dimension (or is zero). -/
theorem ringKrullDim_le_of_finiteType (K : Type*) [Field K] (R : Type*) [CommRing R] [Algebra K R]
    [Algebra.FiniteType K R] : ∃ n : ℕ, ringKrullDim R ≤ n := by
  rcases subsingleton_or_nontrivial R with h | h
  · exact ⟨0, by rw [ringKrullDim_eq_bot_of_subsingleton]; exact bot_le⟩
  · obtain ⟨s, g, ginj, gfin⟩ := exists_finite_inj_algHom_of_fg K R
    letI := g.toRingHom.toAlgebra
    haveI : Algebra.IsIntegral (MvPolynomial (Fin s) K) R := ⟨gfin.to_isIntegral⟩
    refine ⟨s, le_of_eq ?_⟩
    rw [ringKrullDim_eq_of_isIntegral_of_injective (A := MvPolynomial (Fin s) K) ginj,
      ringKrullDim_mvPolynomial_field]


/-! ## §2. Topology and schemes -/

open TopologicalSpace Topology


/-- The Krull dimension of a space is the supremum of the dimensions of the members of a cover
by open embeddings (Stacks 0055 for open covers; STANDARD). -/
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

open AlgebraicGeometry CategoryTheory Limits

theorem scheme_dim_eq_iSup_cover {X : Scheme} (𝒰 : X.OpenCover) :
    topologicalKrullDim X = ⨆ i, topologicalKrullDim (𝒰.X i) :=
  topologicalKrullDim_eq_iSup_of_openEmbedding (fun i => 𝒰.f i) (fun i => (𝒰.f i).isOpenEmbedding)
    (fun x => ⟨𝒰.idx x, 𝒰.covers x⟩)

theorem scheme_dim_eq_of_iso {X Y : Scheme} (e : X ≅ Y) :
    topologicalKrullDim X = topologicalKrullDim Y :=
  IsHomeomorph.topologicalKrullDim_eq _ (Scheme.homeoOfIso e).isHomeomorph

theorem spec_dim (R : CommRingCat) : topologicalKrullDim (Spec R) = ringKrullDim R :=
  PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim R


/-- **Stacks 00P4, affine piece over `Spec K`.** For `m : Spec R → Spec K` locally of finite
type, `Spec R ×_K Spec L ≅ Spec (R ⊗_K L)` has the dimension of `Spec R`. -/
theorem dim_pullback_spec {K : Type} [Field K] (L : Type) [Field L] [Algebra K L]
    (R : CommRingCat.{0}) (m : Spec R ⟶ Spec (CommRingCat.of K)) [LocallyOfFiniteType m] :
    topologicalKrullDim (pullback m (Spec.map (CommRingCat.ofHom (algebraMap K L))) : Scheme) =
      topologicalKrullDim (Spec R) := by
  obtain ⟨φ, rfl⟩ : ∃ φ, Spec.map φ = m := ⟨Spec.preimage m, Spec.map_preimage m⟩
  have hφ : φ.hom.FiniteType :=
    (HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)).mp inferInstance
  letI : Algebra K R := φ.hom.toAlgebra
  haveI : Algebra.FiniteType K R := hφ
  have e := scheme_dim_eq_of_iso (pullbackSpecIso K R L)
  refine e.trans ?_
  rw [spec_dim, spec_dim]
  exact ringKrullDim_tensor_field K R L

/-- A scheme of finite type over a field: each affine piece `Spec R → Spec K` has bounded
dimension. -/
theorem dim_spec_le {K : Type} [Field K] (R : CommRingCat.{0}) (m : Spec R ⟶ Spec (CommRingCat.of K))
    [LocallyOfFiniteType m] : ∃ n : ℕ, topologicalKrullDim (Spec R) ≤ n := by
  obtain ⟨φ, rfl⟩ : ∃ φ, Spec.map φ = m := ⟨Spec.preimage m, Spec.map_preimage m⟩
  have hφ : φ.hom.FiniteType :=
    (HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)).mp inferInstance
  letI : Algebra K R := φ.hom.toAlgebra
  haveI : Algebra.FiniteType K R := hφ
  rw [spec_dim]
  exact ringKrullDim_le_of_finiteType K R

/-- **Dimension is invariant under field base change** (Stacks 00P4 globalized; proved). For a
scheme `X` locally of finite type over a field `K` and any field extension `L/K`,
`dim (X ×_K L) = dim X`. -/
theorem dim_baseChange_scheme {K : Type} [Field K] (L : Type) [Field L] [Algebra K L] (X : Scheme.{0})
    (h : X ⟶ Spec (CommRingCat.of K)) [LocallyOfFiniteType h] :
    topologicalKrullDim (pullback h (Spec.map (CommRingCat.ofHom (algebraMap K L))) : Scheme) =
      topologicalKrullDim X := by
  let g := Spec.map (CommRingCat.ofHom (algebraMap K L))
  let 𝒰 := X.affineCover
  rw [scheme_dim_eq_iSup_cover 𝒰, scheme_dim_eq_iSup_cover (𝒰.pullback₁ (pullback.fst h g))]
  refine iSup_congr fun i => ?_
  have e : (𝒰.pullback₁ (pullback.fst h g)).X i ≅ pullback (𝒰.f i ≫ h) g :=
    (pullbackSymmetry _ _).trans (pullbackRightPullbackFstIso h g (𝒰.f i))
  rw [scheme_dim_eq_of_iso e]
  haveI : IsOpenImmersion (𝒰.f i) := 𝒰.map_prop i
  have hc : LocallyOfFiniteType (𝒰.f i ≫ h) := locallyOfFiniteType_comp _ _
  exact @dim_pullback_spec K _ L _ _ _ (𝒰.f i ≫ h) hc

theorem exists_nat_of_le (x : WithBot ℕ∞) (h0 : x ≠ ⊥) (N : ℕ) (h : x ≤ N) :
    ∃ n : ℕ, x = n := by
  induction x using WithBot.recBotCoe with
  | bot => exact absurd rfl h0
  | coe e =>
    induction e using ENat.recTopCoe with
    | top =>
      have h' : ((⊤ : ℕ∞) : WithBot ℕ∞) ≤ ((N : ℕ∞) : WithBot ℕ∞) := by exact_mod_cast h
      exact absurd (WithBot.coe_le_coe.mp h') (by simp)
    | coe n => exact ⟨n, rfl⟩

/-- **A nonempty scheme of finite type over a field has finite dimension** (proved). -/
theorem dim_finite {K : Type} [Field K] (X : Scheme.{0}) (h : X ⟶ Spec (CommRingCat.of K))
    [LocallyOfFiniteType h] [QuasiCompact h] [Nonempty X] :
    ∃ n : ℕ, topologicalKrullDim X = n := by
  haveI : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace h
  let 𝒰 := X.affineCover.finiteSubcover
  have hb : ∀ i, ∃ n : ℕ, topologicalKrullDim (𝒰.X i) ≤ n := fun i => by
    haveI : IsOpenImmersion (𝒰.f i) := 𝒰.map_prop i
    have hc : LocallyOfFiniteType (𝒰.f i ≫ h) := locallyOfFiniteType_comp _ _
    exact @dim_spec_le K _ _ (𝒰.f i ≫ h) hc
  choose n hn using hb
  have hle : topologicalKrullDim X ≤ ((∑ i, n i : ℕ) : WithBot ℕ∞) := by
    rw [scheme_dim_eq_iSup_cover 𝒰]
    refine iSup_le fun i => (hn i).trans ?_
    exact_mod_cast Finset.single_le_sum (fun j _ => Nat.zero_le (n j)) (Finset.mem_univ i)
  have hne : topologicalKrullDim X ≠ ⊥ := by
    obtain ⟨x⟩ := ‹Nonempty X›
    haveI : Nonempty (IrreducibleCloseds X) :=
      ⟨⟨closure {x}, isIrreducible_singleton.closure, isClosed_closure⟩⟩
    exact Order.krullDim_ne_bot_iff.mpr inferInstance
  exact exists_nat_of_le _ hne _ hle

end ZInQ.Contrib.AbVarBC

/-! ## §3. The project's abelian varieties -/

namespace PkgI3.AbVar

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj

/-- **Dimension is invariant under base change** (Stacks 00P4; proved, no hypothesis). -/
theorem dim_baseChange {K : Type} [Field K] (A : PkgI3.AbVar K) (L : Type) [Field L]
    [Algebra K L] : (A.baseChange L).dim = A.dim :=
  ZInQ.Contrib.AbVarBC.dim_baseChange_scheme L A.X.left A.X.hom

/-- **The dimension of an abelian variety is a natural number** (proved, no hypothesis). -/
theorem dim_finite {K : Type} [Field K] (A : PkgI3.AbVar K) :
    ∃ n : ℕ, A.dim = (n : WithBot ℕ∞) := by
  haveI : Nonempty A.X.left :=
    ⟨η[A.X].left (Nonempty.some (inferInstance : Nonempty (Spec (CommRingCat.of K))))⟩
  exact ZInQ.Contrib.AbVarBC.dim_finite A.X.left A.X.hom

end PkgI3.AbVar

end LF2_AbVarBC_Dim

-- ===== ZInQKernel/Contrib/AbVarBC/Points.lean
section LF2_AbVarBC_Points

/-!
# Base change of abelian varieties, II: points

Copyright: this file is part of the fork Deicyde/diophantine-z-q (task g9-abvarbc, 2026-11-13).
§1 is task unram-tate's `scratch/unram-tate/BCPoints.lean` (namespace `UnramTate`), moved into the
namespace `ZInQ.Contrib.AbVarBC`. §2 is new.

For the project's abelian varieties (`PkgI3.AbVar`, `ZInQKernel/HDecomp/Objects.lean`):
* `bcPt : (A.baseChange L).Pt Ω ≃* A.Pt Ω` (points of a base change), natural for
  `L`-automorphisms of `Ω` (`bcPt_galAct`);
* `extPt κ : A.Pt Ω →* A.Pt Ω₂` along a `K`-embedding of fields `κ : Ω →ₐ[K] Ω₂`, **injective**
  (`extPt_injective`: `Spec Ω₂ → Spec Ω` is faithfully flat and quasi-compact, hence an effective
  epimorphism, Mathlib's Stacks 023Q), and Galois-natural (`extPt_galAct`).
-/

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.Obj

set_option linter.style.haveILetI false

namespace ZInQ.Contrib.AbVarBC

/-! ## §1. Points of a base change (task unram-tate) -/

/-- `Spec L → Spec K`. -/
noncomputable abbrev sK (K L : Type) [Field K] [Field L] [Algebra K L] :
    Spec (CommRingCat.of L) ⟶ Spec (CommRingCat.of K) :=
  Spec.map (CommRingCat.ofHom (algebraMap K L))

section BC

variable {K L : Type} [Field K] [Field L] [Algebra K L] (A : PkgI3.AbVar K)
  (Ω : Type) [Field Ω] [Algebra L Ω] [Algebra K Ω] [IsScalarTower K L Ω]

theorem specMap_comp_sK :
    Spec.map (CommRingCat.ofHom (algebraMap L Ω)) ≫ sK K L =
      Spec.map (CommRingCat.ofHom (algebraMap K Ω)) := by
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, IsScalarTower.algebraMap_eq K L Ω]

/-- `Over.map (Spec L → Spec K) (Spec Ω / L) ≅ Spec Ω / K`. -/
noncomputable def ptMapIso :
    (Over.map (sK K L)).obj (PkgI3.AbVar.ptObj (K := L) Ω) ≅ PkgI3.AbVar.ptObj (K := K) Ω :=
  Over.isoMk (Iso.refl _) (by
    simp only [Over.map_obj_hom, Iso.refl_hom, PkgI3.AbVar.ptObj, Over.mk_hom]
    erw [Category.id_comp]
    exact (specMap_comp_sK (K := K) (L := L) Ω).symm)

/-- The adjunction bijection is multiplicative. -/
theorem homEquiv_mul (X : Over (Spec (CommRingCat.of L)))
    (p q : (Over.map (sK K L)).obj X ⟶ A.X) :
    (Over.mapPullbackAdj (sK K L)).homEquiv X A.X (p * q) =
      (Over.mapPullbackAdj (sK K L)).homEquiv X A.X p *
        (Over.mapPullbackAdj (sK K L)).homEquiv X A.X q := by
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit, Adjunction.homEquiv_unit,
    Functor.map_mul, MonObj.comp_mul]

/-- **Points of a base change**: `A_L(Ω) ≃* A(Ω)`. -/
noncomputable def bcPt : (A.baseChange L).Pt Ω ≃* A.Pt Ω where
  toFun p := (ptMapIso Ω).inv ≫ ((Over.mapPullbackAdj (sK K L)).homEquiv _ _).symm p
  invFun x := (Over.mapPullbackAdj (sK K L)).homEquiv _ _ ((ptMapIso Ω).hom ≫ x)
  left_inv p := Equiv.apply_symm_apply ((Over.mapPullbackAdj (sK K L)).homEquiv _ A.X) p
  right_inv x := by
    show (ptMapIso Ω).inv ≫ ((Over.mapPullbackAdj (sK K L)).homEquiv _ _).symm
      ((Over.mapPullbackAdj (sK K L)).homEquiv _ _ ((ptMapIso Ω).hom ≫ x)) = x
    rw [Equiv.symm_apply_apply, ← Category.assoc, Iso.inv_hom_id, Category.id_comp]
  map_mul' p q := by
    obtain ⟨p', rfl⟩ := ((Over.mapPullbackAdj (sK K L)).homEquiv _ A.X).surjective p
    obtain ⟨q', rfl⟩ := ((Over.mapPullbackAdj (sK K L)).homEquiv _ A.X).surjective q
    show (ptMapIso Ω).inv ≫ ((Over.mapPullbackAdj (sK K L)).homEquiv _ _).symm
        ((Over.mapPullbackAdj (sK K L)).homEquiv _ A.X p' *
          (Over.mapPullbackAdj (sK K L)).homEquiv _ A.X q') = _
    rw [← homEquiv_mul, Equiv.symm_apply_apply, Equiv.symm_apply_apply, Equiv.symm_apply_apply,
      MonObj.comp_mul]

/-- `bcPt` is natural for `L`-automorphisms of `Ω`. -/
theorem bcPt_galAct (σ : Ω ≃ₐ[L] Ω) (p : (A.baseChange L).Pt Ω) :
    bcPt A Ω ((A.baseChange L).galAct σ p) = A.galAct (σ.restrictScalars K) (bcPt A Ω p) := by
  show (ptMapIso Ω).inv ≫ ((Over.mapPullbackAdj (sK K L)).homEquiv _ _).symm
      (PkgI3.AbVar.galHom σ ≫ p) =
    PkgI3.AbVar.galHom (σ.restrictScalars K) ≫ (ptMapIso Ω).inv ≫
      ((Over.mapPullbackAdj (sK K L)).homEquiv _ _).symm p
  have hnat := Adjunction.homEquiv_naturality_left_symm (Over.mapPullbackAdj (sK K L))
    (PkgI3.AbVar.galHom σ) (p : PkgI3.AbVar.ptObj Ω ⟶ (Over.pullback (sK K L)).obj A.X)
  have hsq : (ptMapIso Ω).inv ≫ (Over.map (sK K L)).map (PkgI3.AbVar.galHom σ) =
      PkgI3.AbVar.galHom (σ.restrictScalars K) ≫ (ptMapIso Ω).inv := by
    apply Over.OverMorphism.ext
    simp [ptMapIso, PkgI3.AbVar.galHom]
    rfl
  erw [hnat]
  rw [← Category.assoc, hsq, Category.assoc]

end BC

section Tr

variable {K : Type} [Field K] (A : PkgI3.AbVar K)
  {Ω Ω₂ : Type} [Field Ω] [Algebra K Ω] [Field Ω₂] [Algebra K Ω₂]

/-- `Spec Ω₂ → Spec Ω` over `K`, for a `K`-isomorphism `φ : Ω ≃ Ω₂`. -/
noncomputable def trHom (φ : Ω ≃ₐ[K] Ω₂) :
    PkgI3.AbVar.ptObj (K := K) Ω₂ ⟶ PkgI3.AbVar.ptObj (K := K) Ω :=
  Over.homMk (Spec.map (CommRingCat.ofHom (φ : Ω →+* Ω₂))) (by
    simp only [PkgI3.AbVar.ptObj, Over.mk_hom, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    congr 2
    ext x
    simp)

theorem trHom_left (φ : Ω ≃ₐ[K] Ω₂) :
    (trHom φ).left = Spec.map (CommRingCat.ofHom (φ : Ω →+* Ω₂)) := rfl

theorem trHom_symm_comp (φ : Ω ≃ₐ[K] Ω₂) : trHom φ.symm ≫ trHom φ = 𝟙 _ := by
  apply Over.OverMorphism.ext
  change Spec.map (CommRingCat.ofHom (φ.symm : Ω₂ →+* Ω)) ≫
    Spec.map (CommRingCat.ofHom (φ : Ω →+* Ω₂)) = 𝟙 (Spec (CommRingCat.of Ω))
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp,
    show (φ.symm : Ω₂ →+* Ω).comp (φ : Ω →+* Ω₂) = RingHom.id Ω by ext x; simp,
    CommRingCat.ofHom_id, Spec.map_id]

theorem trHom_comp_symm (φ : Ω ≃ₐ[K] Ω₂) : trHom φ ≫ trHom φ.symm = 𝟙 _ := by
  simpa using trHom_symm_comp φ.symm

/-- **Transport of points** along `φ : Ω ≃ₐ[K] Ω₂`. -/
noncomputable def trPt (φ : Ω ≃ₐ[K] Ω₂) : A.Pt Ω ≃* A.Pt Ω₂ where
  toFun p := trHom φ ≫ p
  invFun x := trHom φ.symm ≫ x
  left_inv p := by simp [← Category.assoc, trHom_symm_comp]
  right_inv x := by simp [← Category.assoc, trHom_comp_symm]
  map_mul' _ _ := MonObj.comp_mul _ _ _

/-- `trPt φ` carries the action of `σ` to that of `φσφ⁻¹`. -/
theorem trPt_galAct (φ : Ω ≃ₐ[K] Ω₂) (σ : Ω ≃ₐ[K] Ω) (σ₂ : Ω₂ ≃ₐ[K] Ω₂)
    (h : ∀ x, σ₂ (φ x) = φ (σ x)) (p : A.Pt Ω) :
    trPt A φ (A.galAct σ p) = A.galAct σ₂ (trPt A φ p) := by
  show trHom φ ≫ PkgI3.AbVar.galHom σ ≫ p = PkgI3.AbVar.galHom σ₂ ≫ trHom φ ≫ p
  have hsq : trHom φ ≫ PkgI3.AbVar.galHom σ = PkgI3.AbVar.galHom σ₂ ≫ trHom φ := by
    apply Over.OverMorphism.ext
    change Spec.map (CommRingCat.ofHom (φ : Ω →+* Ω₂)) ≫
        Spec.map (CommRingCat.ofHom (σ : Ω →+* Ω)) =
      Spec.map (CommRingCat.ofHom (σ₂ : Ω₂ →+* Ω₂)) ≫ Spec.map (CommRingCat.ofHom (φ : Ω →+* Ω₂))
    rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp]
    congr 2
    ext x
    exact (h x).symm
  rw [← Category.assoc, ← Category.assoc, hsq]

end Tr

/-! ## §2. Points over an extension of fields -/

section Ext

variable {K : Type} [Field K] (A : PkgI3.AbVar K)
  {Ω Ω₂ : Type} [Field Ω] [Algebra K Ω] [Field Ω₂] [Algebra K Ω₂]

/-- `Spec Ω₂ → Spec Ω` over `K`, for a `K`-embedding `κ : Ω → Ω₂`. -/
noncomputable def extHom (κ : Ω →ₐ[K] Ω₂) :
    PkgI3.AbVar.ptObj (K := K) Ω₂ ⟶ PkgI3.AbVar.ptObj (K := K) Ω :=
  Over.homMk (Spec.map (CommRingCat.ofHom (κ : Ω →+* Ω₂))) (by
    simp only [PkgI3.AbVar.ptObj, Over.mk_hom, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    congr 2
    ext x
    simp)

theorem extHom_left (κ : Ω →ₐ[K] Ω₂) :
    (extHom κ).left = Spec.map (CommRingCat.ofHom (κ : Ω →+* Ω₂)) := rfl

/-- `Spec` of a map of fields is an epimorphism of schemes (faithfully flat, quasi-compact). -/
theorem epi_spec_map_field (κ : Ω →+* Ω₂) : Epi (Spec.map (CommRingCat.ofHom κ)) := by
  haveI : Surjective (Spec.map (CommRingCat.ofHom κ)) := by
    constructor
    intro y
    refine ⟨IsLocalRing.closedPoint Ω₂, Subsingleton.elim _ _⟩
  haveI : Flat (Spec.map (CommRingCat.ofHom κ)) := by
    rw [HasRingHomProperty.Spec_iff (P := @Flat)]
    algebraize [κ]
    change Module.Flat Ω Ω₂
    infer_instance
  infer_instance

instance epi_extHom (κ : Ω →ₐ[K] Ω₂) : Epi (extHom κ) := by
  haveI : Epi ((Over.forget _).map (extHom κ)) := epi_spec_map_field (κ : Ω →+* Ω₂)
  exact (Over.forget _).epi_of_epi_map this

/-- **Points along a field extension**: `A(Ω) → A(Ω₂)`, `p ↦ p ∘ Spec κ`. -/
noncomputable def extPt (κ : Ω →ₐ[K] Ω₂) : A.Pt Ω →* A.Pt Ω₂ where
  toFun p := extHom κ ≫ p
  map_one' := MonObj.comp_one _
  map_mul' _ _ := MonObj.comp_mul _ _ _

theorem extPt_apply (κ : Ω →ₐ[K] Ω₂) (p : A.Pt Ω) : extPt A κ p = extHom κ ≫ p := rfl

/-- **`A(Ω) → A(Ω₂)` is injective.** -/
theorem extPt_injective (κ : Ω →ₐ[K] Ω₂) : Function.Injective (extPt A κ) :=
  fun _ _ h => (cancel_epi (extHom κ)).1 h

/-- `extPt κ` carries the action of `τ ∈ Aut_K(Ω)` to that of `σ ∈ Aut_K(Ω₂)` when
`κ ∘ τ = σ ∘ κ`. -/
theorem extPt_galAct (κ : Ω →ₐ[K] Ω₂) (τ : Ω ≃ₐ[K] Ω) (σ : Ω₂ ≃ₐ[K] Ω₂)
    (h : ∀ x, κ (τ x) = σ (κ x)) (p : A.Pt Ω) :
    extPt A κ (A.galAct τ p) = A.galAct σ (extPt A κ p) := by
  show extHom κ ≫ PkgI3.AbVar.galHom τ ≫ p = PkgI3.AbVar.galHom σ ≫ extHom κ ≫ p
  have hsq : extHom κ ≫ PkgI3.AbVar.galHom τ = PkgI3.AbVar.galHom σ ≫ extHom κ := by
    apply Over.OverMorphism.ext
    change Spec.map (CommRingCat.ofHom (κ : Ω →+* Ω₂)) ≫
        Spec.map (CommRingCat.ofHom (τ : Ω →+* Ω)) =
      Spec.map (CommRingCat.ofHom (σ : Ω₂ →+* Ω₂)) ≫ Spec.map (CommRingCat.ofHom (κ : Ω →+* Ω₂))
    rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp]
    congr 2
    ext x
    exact (h x)
  rw [← Category.assoc, ← Category.assoc, hsq]

end Ext

end ZInQ.Contrib.AbVarBC

end LF2_AbVarBC_Points

-- ===== ZInQKernel/Contrib/AbVarBC/Tate.lean
section LF2_AbVarBC_Tate

/-!
# Base change of abelian varieties, III: Tate modules

Copyright: this file is part of the fork Deicyde/diophantine-z-q (task g9-abvarbc, 2026-11-13).

For `A : PkgI3.AbVar K` (the kernel's abelian varieties, `ZInQKernel/HDecomp/Objects.lean`), a
field extension `L/K` and a `K`-embedding `κ : K̄ → L̄`:
* `ptBC A κ : A(K̄) →* A_L(L̄)` is injective (`ptBC_injective`) and Galois-natural
  (`ptBC_galAct`: if `κ ∘ τ = σ ∘ κ` for `τ ∈ G_K`, `σ ∈ G_L`);
* `tateBC A ℓ κ : T_ℓ(A) →ₗ[ℤ_ℓ] T_ℓ(A_L)` is injective and Galois-natural (`tateBC_galT`);
* it is bijective as soon as the `ℓ`-power torsion of `A_L(L̄)` comes from `A(K̄)`
  (`tateBC_bijective_of_torsionDescends`), or under leaf T26 `PkgI3.TateModuleFree`
  (`tateBC_bijective_of_tateModuleFree`, through the kernel glue `PkgI3.Tate.map_bijective` and
  `dim A_L = dim A`);
* `vBC A ℓ κ hb : V_ℓ(A_L) ≃ₗ[ℚ_ℓ] V_ℓ(A)` with `vBC_galRep`: it intertwines `ρ_{A_L}(σ)` with
  `ρ_A(τ)`.
-/

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct

set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false

namespace ZInQ.Contrib.AbVarBC

/-! ## §1. Tate modules along an injective map whose `ℓ`-power torsion is in the image -/

section TateGen

variable {ℓ : ℕ} [Fact ℓ.Prime] {M N : Type*} [AddCommGroup M] [AddCommGroup N]

/-- If `φ : M → N` is injective and every `ℓ`-power torsion element of `N` is in its image,
`T_ℓ(φ)` is bijective. -/
theorem tate_map_bijective_of_torsion (φ : M →+ N) (hφ : Function.Injective φ)
    (htors : ∀ (n : ℕ) (q : N), (ℓ ^ n) • q = 0 → ∃ p, φ p = q) :
    Function.Bijective (PkgI3.Tate.map (ℓ := ℓ) φ) := by
  refine ⟨PkgI3.Tate.map_injective φ hφ, fun x => ?_⟩
  have hx : ∀ n, ∃ p, φ p = x.1 n := fun n =>
    htors n (x.1 n) (PkgI3.Tate.pow_smul_eq_zero x.2 n)
  choose y hy using hx
  refine ⟨⟨y, ?_, fun n => ?_⟩, ?_⟩
  · apply hφ
    rw [hy, x.2.1, map_zero]
  · apply hφ
    rw [map_nsmul, hy, hy, x.2.2 n]
  · apply Subtype.ext
    funext n
    exact hy n

end TateGen

/-! ## §2. Points and Tate modules of a base change -/

/-- An element of `G_K` as an automorphism of `K̄`. -/
abbrev galK {K : Type*} [Field K] (σ : Field.absoluteGaloisGroup K) :
    AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K := σ

section BC

variable {K L : Type} [Field K] [Field L] [Algebra K L] (A : PkgI3.AbVar K)
  (κ : AlgebraicClosure K →ₐ[K] AlgebraicClosure L)

/-- `A(K̄) → A(L̄) ≅ A_L(L̄)`. -/
noncomputable def ptBC : A.Pt (AlgebraicClosure K) →* (A.baseChange L).Pt (AlgebraicClosure L) :=
  (bcPt A (AlgebraicClosure L)).symm.toMonoidHom.comp (extPt A κ)

theorem ptBC_injective : Function.Injective (ptBC A κ) :=
  (bcPt A (AlgebraicClosure L)).symm.injective.comp (extPt_injective A κ)

/-- Galois-naturality of `ptBC`. -/
theorem ptBC_galAct (τ : Field.absoluteGaloisGroup K) (σ : Field.absoluteGaloisGroup L)
    (h : ∀ x, κ (galK τ x) = galK σ (κ x)) (p : A.Pt (AlgebraicClosure K)) :
    ptBC A κ (A.galAct τ p) = (A.baseChange L).galAct σ (ptBC A κ p) := by
  have h1 := extPt_galAct A κ τ ((σ : AlgebraicClosure L ≃ₐ[L] AlgebraicClosure L).restrictScalars K)
    h p
  have h2 := bcPt_galAct A (AlgebraicClosure L) σ
    ((bcPt A (AlgebraicClosure L)).symm (extPt A κ p))
  rw [MulEquiv.apply_symm_apply] at h2
  change (bcPt A (AlgebraicClosure L)).symm (extPt A κ (A.galAct τ p)) =
    (A.baseChange L).galAct σ ((bcPt A (AlgebraicClosure L)).symm (extPt A κ p))
  rw [h1, ← h2, MulEquiv.symm_apply_apply]

variable (ℓ : ℕ) [Fact ℓ.Prime]

/-- `T_ℓ(A) → T_ℓ(A_L)`. -/
noncomputable def tateBC : A.T ℓ →ₗ[ℤ_[ℓ]] (A.baseChange L).T ℓ :=
  PkgI3.Tate.map (MonoidHom.toAdditive (ptBC A κ))

theorem tateBC_injective : Function.Injective (tateBC A κ ℓ) :=
  PkgI3.Tate.map_injective _ (ptBC_injective A κ)

/-- Galois-naturality of `tateBC`. -/
theorem tateBC_galT (τ : Field.absoluteGaloisGroup K) (σ : Field.absoluteGaloisGroup L)
    (h : ∀ x, κ (galK τ x) = galK σ (κ x)) (x : A.T ℓ) :
    tateBC A κ ℓ (A.galT τ x) = (A.baseChange L).galT σ (tateBC A κ ℓ x) := by
  apply Subtype.ext
  funext n
  exact congrArg Additive.ofMul (ptBC_galAct A κ τ σ h (Additive.toMul (x.1 n)))

/-- **Descent of `ℓ`-power torsion** (the content of "`A[ℓⁿ]` is finite étale"): every
`ℓ`-power torsion point of `A_L(L̄)` comes from `A(K̄)`. -/
def TorsionDescends : Prop :=
  ∀ (n : ℕ) (q : (A.baseChange L).Pt (AlgebraicClosure L)), q ^ (ℓ ^ n) = 1 →
    ∃ p, ptBC A κ p = q

theorem tateBC_bijective_of_torsionDescends (h : TorsionDescends A κ ℓ) :
    Function.Bijective (tateBC A κ ℓ) :=
  tate_map_bijective_of_torsion _ (ptBC_injective A κ) fun n q hq => h n (Additive.toMul q) hq

/-- **Under leaf T26 (`TateModuleFree`), `T_ℓ(A) → T_ℓ(A_L)` is bijective** (`ℓ ≠ char K`). -/
theorem tateBC_bijective_of_tateModuleFree (hT : PkgI3.TateModuleFree) (hℓ : (ℓ : K) ≠ 0) :
    Function.Bijective (tateBC A κ ℓ) := by
  have hℓL : (ℓ : L) ≠ 0 := by
    rw [← map_natCast (algebraMap K L)]
    exact (map_ne_zero_iff _ (algebraMap K L).injective).mpr hℓ
  obtain ⟨hfree, hfin, hrk⟩ := hT K A ℓ hℓ
  obtain ⟨-, hfinL, hrkL⟩ := hT L (A.baseChange L) ℓ hℓL
  rw [PkgI3.AbVar.dim_baseChange] at hrkL
  have hr : Module.finrank ℤ_[ℓ] (A.T ℓ) = Module.finrank ℤ_[ℓ] ((A.baseChange L).T ℓ) := by
    have := hrk.trans hrkL.symm
    exact_mod_cast this
  exact PkgI3.Tate.map_bijective _ (ptBC_injective A κ) hr

/-- **`V_ℓ(A_L) ≅ V_ℓ(A)`**, from a bijective `tateBC`. -/
noncomputable def vBC (hb : Function.Bijective (tateBC A κ ℓ)) :
    (A.baseChange L).V ℓ ≃ₗ[ℚ_[ℓ]] A.V ℓ :=
  ((LinearEquiv.ofBijective (tateBC A κ ℓ) hb).baseChange ℤ_[ℓ] ℚ_[ℓ] _ _).symm

/-- `vBC` intertwines `ρ_{A_L}(σ)` with `ρ_A(τ)` when `κ ∘ τ = σ ∘ κ`. -/
theorem vBC_galRep (hb : Function.Bijective (tateBC A κ ℓ)) (τ : Field.absoluteGaloisGroup K)
    (σ : Field.absoluteGaloisGroup L) (h : ∀ x, κ (galK τ x) = galK σ (κ x)) (v : (A.baseChange L).V ℓ) :
    vBC A κ ℓ hb ((A.baseChange L).galRep ℓ σ v) = A.galRep ℓ τ (vBC A κ ℓ hb v) := by
  set e := (LinearEquiv.ofBijective (tateBC A κ ℓ) hb).baseChange ℤ_[ℓ] ℚ_[ℓ] _ _ with he
  have key : ∀ w : A.V ℓ, e (A.galRep ℓ τ w) = (A.baseChange L).galRep ℓ σ (e w) := by
    intro w
    induction w using TensorProduct.inductionOn with
    | tmul a t =>
      change e ((A.galT τ).baseChange ℚ_[ℓ] (a ⊗ₜ t)) =
        ((A.baseChange L).galT σ).baseChange ℚ_[ℓ] (e (a ⊗ₜ t))
      rw [LinearMap.baseChange_tmul, he, LinearEquiv.baseChange_tmul, LinearEquiv.baseChange_tmul,
        LinearMap.baseChange_tmul, LinearEquiv.ofBijective_apply, LinearEquiv.ofBijective_apply,
        tateBC_galT A κ ℓ τ σ h]
    | add w₁ w₂ h₁ h₂ => rw [map_add, map_add, h₁, h₂, map_add, map_add]
  show e.symm ((A.baseChange L).galRep ℓ σ v) = A.galRep ℓ τ (e.symm v)
  apply e.injective
  rw [LinearEquiv.apply_symm_apply, key, LinearEquiv.apply_symm_apply]

end BC

end ZInQ.Contrib.AbVarBC

end LF2_AbVarBC_Tate

-- ===== ZInQKernel/Contrib/AbVarBC/Torsion.lean
section LF2_AbVarBC_Torsion

/-!
# Base change of abelian varieties, V: descent of torsion points from finiteness of `[N]`

Copyright: this file is part of the fork Deicyde/diophantine-z-q (task g9-abvarbc, 2026-11-13).

* `mem_range_of_isIntegral`: an element of a field `Ω₂ ⊇ K` integral over `K` lies in the image of
  any `K`-embedding `K̄ → Ω₂`.
* `exists_lift_of_isFinite`: for `g : Z → Spec K` finite and `κ : Ω → Ω₂` a `K`-embedding with
  `Ω` algebraically closed, every `Ω₂`-point of `Z` over `K` comes from an `Ω`-point (STANDARD:
  `Z = Spec R`, `R` finite over `K`, and the image of `R → Ω₂` is algebraic over `K`).
* `torsionDescends_of_isFinite`: if `[ℓⁿ] : A → A` is finite for every `n`, then
  `TorsionDescends A κ ℓ` (the `ℓ`-power torsion points of `A_L(L̄)` come from `A(K̄)`).
-/

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct

set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false

namespace ZInQ.Contrib.AbVarBC

/-! ## §1. Algebra -/

/-- An element integral over `K` lies in the image of any `K`-embedding of an algebraically
closed field. -/
theorem mem_range_of_isIntegral {K Ω Ω₂ : Type*} [Field K] [Field Ω] [IsAlgClosed Ω] [Field Ω₂]
    [Algebra K Ω] [Algebra K Ω₂] (κ : Ω →ₐ[K] Ω₂) {x : Ω₂} (hx : IsIntegral K x) :
    x ∈ (κ : Ω →+* Ω₂).range := by
  have hf0 : (minpoly K x).map (algebraMap K Ω) ≠ 0 :=
    Polynomial.map_ne_zero (minpoly.ne_zero hx)
  refine Polynomial.Splits.mem_range_of_isRoot (IsAlgClosed.splits _) hf0 ?_
  rw [Polynomial.map_map, κ.comp_algebraMap, Polynomial.IsRoot, Polynomial.eval_map_algebraMap]
  exact minpoly.aeval K x

/-! ## §2. Points of a scheme finite over a field -/

/-- **Points of a finite `K`-scheme over an algebraically closed field.** -/
theorem exists_lift_of_isFinite {K : Type} [Field K] {Ω Ω₂ : Type} [Field Ω] [IsAlgClosed Ω]
    [Field Ω₂] [Algebra K Ω] [Algebra K Ω₂] (κ : Ω →ₐ[K] Ω₂) {Z : Scheme.{0}}
    (g : Z ⟶ Spec (CommRingCat.of K)) [IsFinite g] (q : Spec (CommRingCat.of Ω₂) ⟶ Z)
    (hq : q ≫ g = Spec.map (CommRingCat.ofHom (algebraMap K Ω₂))) :
    ∃ p : Spec (CommRingCat.of Ω) ⟶ Z,
      Spec.map (CommRingCat.ofHom (κ : Ω →+* Ω₂)) ≫ p = q ∧
        p ≫ g = Spec.map (CommRingCat.ofHom (algebraMap K Ω)) := by
  haveI : IsAffine Z := isAffine_of_isAffineHom g
  let e := Z.isoSpec
  let φ := Spec.preimage (q ≫ e.hom)
  let θ := Spec.preimage (e.inv ≫ g)
  have hφ : Spec.map φ = q ≫ e.hom := Spec.map_preimage _
  have hθ : Spec.map θ = e.inv ≫ g := Spec.map_preimage _
  have hθfin : θ.hom.Finite := by
    rw [← IsFinite.SpecMap_iff, hθ]
    infer_instance
  have hcomp : θ ≫ φ = CommRingCat.ofHom (algebraMap K Ω₂) := by
    apply Spec.map_injective
    rw [Spec.map_comp, hφ, hθ, Category.assoc, e.hom_inv_id_assoc, hq]
  -- every element of the image of `φ` is integral over `K`
  have hint : ∀ r, IsIntegral K (φ.hom r) := by
    intro r
    have hr : θ.hom.IsIntegralElem r := hθfin.to_isIntegral r
    obtain ⟨P, hPm, hP⟩ := hr
    refine ⟨P, hPm, ?_⟩
    have := congrArg φ.hom hP
    rw [map_zero, Polynomial.hom_eval₂] at this
    rw [Polynomial.eval₂_eq_eval_map] at this ⊢
    have h2 : φ.hom.comp θ.hom = algebraMap K Ω₂ := congrArg CommRingCat.Hom.hom hcomp
    rw [h2] at this
    exact this
  choose ψ0 hψ0 using fun r => mem_range_of_isIntegral κ (hint r)
  have hκinj : Function.Injective (κ : Ω →+* Ω₂) := (κ : Ω →+* Ω₂).injective
  let ψ : Γ(Z, ⊤) →+* Ω :=
    { toFun := ψ0
      map_one' := hκinj (by rw [hψ0, map_one, map_one])
      map_mul' := fun a b => hκinj (by rw [hψ0, map_mul, map_mul, hψ0, hψ0])
      map_zero' := hκinj (by rw [hψ0, map_zero, map_zero])
      map_add' := fun a b => hκinj (by rw [hψ0, map_add, map_add, hψ0, hψ0]) }
  have hψ : CommRingCat.ofHom ψ ≫ CommRingCat.ofHom (κ : Ω →+* Ω₂) = φ := by
    ext r
    exact hψ0 r
  have hlift : Spec.map (CommRingCat.ofHom (κ : Ω →+* Ω₂)) ≫ (Spec.map (CommRingCat.ofHom ψ) ≫
      e.inv) = q := by
    rw [← Category.assoc, ← Spec.map_comp, hψ, hφ, Category.assoc, e.hom_inv_id,
      Category.comp_id]
  refine ⟨Spec.map (CommRingCat.ofHom ψ) ≫ e.inv, hlift, ?_⟩
  haveI := epi_spec_map_field (κ : Ω →+* Ω₂)
  apply (cancel_epi (Spec.map (CommRingCat.ofHom (κ : Ω →+* Ω₂)))).1
  rw [← Category.assoc, hlift, hq, ← Spec.map_comp, ← CommRingCat.ofHom_comp, κ.comp_algebraMap]

/-! ## §3. Torsion points of a base change -/

section Tors

variable {K : Type} [Field K] (A : PkgI3.AbVar K)

/-- `q ≫ [N] = q ^ N` for `[N] = ((N : ℤ) : End A).hom`. -/
theorem comp_natCast_hom {T : Over (Spec (CommRingCat.of K))} (q : T ⟶ A.X) (N : ℕ) :
    q ≫ (((N : ℤ) : PkgI3.AbVar.End A)).hom = q ^ N := by
  induction N with
  | zero =>
    rw [Nat.cast_zero, Int.cast_zero, PkgI3.AbVar.Hom.hom_zero, MonObj.comp_one, pow_zero]
  | succ N ih =>
    rw [Nat.cast_succ, Int.cast_add, Int.cast_one, PkgI3.AbVar.Hom.hom_add, MonObj.comp_mul, ih,
      pow_succ]
    congr 1

variable {L : Type} [Field L] [Algebra K L]

/-- **Torsion descent from finiteness of `[ℓⁿ]`.** If `[ℓⁿ] : A → A` is a finite morphism for
every `n`, then every `ℓ`-power torsion point of `A_L(L̄)` comes from `A(K̄)`. -/
theorem torsionDescends_of_isFinite (κ : AlgebraicClosure K →ₐ[K] AlgebraicClosure L)
    (ℓ : ℕ) [Fact ℓ.Prime]
    (hfin : ∀ n : ℕ, IsFinite ((((ℓ ^ n : ℕ) : ℤ) : PkgI3.AbVar.End A).hom.left)) :
    TorsionDescends A κ ℓ := by
  intro n q hq
  set N := ℓ ^ n with hN
  set q₀ := bcPt A (AlgebraicClosure L) q with hq₀
  have h0 : q₀ ^ N = 1 := by rw [hq₀, ← map_pow, hq, map_one]
  have h1 : q₀ ≫ ((N : ℤ) : PkgI3.AbVar.End A).hom = 1 := by rw [comp_natCast_hom, h0]
  haveI := hfin n
  let fN : A.X.left ⟶ A.X.left := ((N : ℤ) : PkgI3.AbVar.End A).hom.left
  let e : Spec (CommRingCat.of K) ⟶ A.X.left := η[A.X].left
  have hq0 : q₀.left ≫ fN = Spec.map (CommRingCat.ofHom (algebraMap K (AlgebraicClosure L))) ≫ e := by
    have h2 := congrArg (fun f => f.left) h1
    simp only [Over.comp_left, Hom.one_def] at h2
    exact h2
  have hfN : IsFinite fN := hfin n
  let z : Spec (CommRingCat.of (AlgebraicClosure L)) ⟶ pullback fN e :=
    pullback.lift q₀.left (Spec.map (CommRingCat.ofHom (algebraMap K (AlgebraicClosure L)))) hq0
  obtain ⟨p0, hp0, hp0g⟩ := exists_lift_of_isFinite κ (pullback.snd fN e) z (pullback.lift_snd _ _ _)
  have hfst : pullback.fst fN e ≫ A.X.hom = pullback.snd fN e := by
    have hw : fN ≫ A.X.hom = A.X.hom := Over.w ((N : ℤ) : PkgI3.AbVar.End A).hom
    have he : e ≫ A.X.hom = 𝟙 _ := Over.w η[A.X]
    rw [← hw, ← Category.assoc, pullback.condition, Category.assoc, he, Category.comp_id]
  let p : A.Pt (AlgebraicClosure K) := Over.homMk (p0 ≫ pullback.fst fN e) (by
    change (p0 ≫ pullback.fst fN e) ≫ A.X.hom = _
    rw [Category.assoc, hfst, hp0g]
    rfl)
  refine ⟨p, ?_⟩
  change (bcPt A (AlgebraicClosure L)).symm (extPt A κ p) = q
  rw [MulEquiv.symm_apply_eq]
  apply Over.OverMorphism.ext
  change Spec.map (CommRingCat.ofHom (κ : AlgebraicClosure K →+* AlgebraicClosure L)) ≫
    p0 ≫ pullback.fst fN e = q₀.left
  rw [← Category.assoc, hp0]
  exact pullback.lift_fst _ _ _

end Tors

end ZInQ.Contrib.AbVarBC

end LF2_AbVarBC_Torsion

-- ===== ZInQKernel/Contrib/AbVarBC/Mul.lean
section LF2_AbVarBC_Mul

/-!
# mul-rigidity: the textbook leaf `MulIsogeny` reduced to smaller named Props

Copyright: this file is part of the fork Deicyde/diophantine-z-q. It is task mul-rigidity's
`scratch/mul-rigidity/Mul.lean` (2026-11-13), copied by task g9-abvarbc into `Contrib` with the
namespaces `MulRigidity` and `G0FibreSimple` moved under `ZInQ.Contrib.AbVarBC` (no other change),
so that `Contrib/AbVarBC/G9Instance.lean` can use `MulIsogeny`, `KerUnitOpen` and the two
cotangent glue statements.

`MulIsogeny` is copied verbatim from scratch/g0-fibresimple/FibreSimple.lean (§4″). Mathlib
proves "finite and surjective" from local properties of `[n]`:
* proper (`A` proper) and locally quasi-finite give finite (Zariski's main theorem, Mathlib
  `IsFinite.of_isProper_of_locallyQuasiFinite`, Stacks 02LS);
* a locally quasi-finite closed self-map of an irreducible Noetherian scheme is surjective
  (`surjective_of_lqf_self`, generic-point orbit), so `QuasiFiniteEndSurjective` is proved;
* formally unramified + locally of finite type gives locally quasi-finite;
* `[n]` is formally unramified once the unit section of `A[n]` is an open immersion
  (`diagonal_isPullback`: `Δ_f` is a base change of that section).
Chain: `KerUnitOpenOfCotangentSurj` + `CotangentMulN` (glue, unproved) ⇒ `KerUnitOpen` (leaf,
implied by the published `MulEtale`) ⇒ `MulUnramified` ⇒ `MulIsogeny`.
-/

noncomputable section

namespace ZInQ.Contrib.AbVarBC.MulRigidity

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj

/-- Formally unramified and locally of finite type implies locally quasi-finite (Mathlib's algebra
instance `Algebra.QuasiFinite` from `EssFiniteType` and `FormallyUnramified`, made affine-local). -/
theorem locallyQuasiFinite_of_formallyUnramified {X Y : Scheme} (f : X ⟶ Y)
    [FormallyUnramified f] [LocallyOfFiniteType f] : LocallyQuasiFinite f := by
  rw [HasRingHomProperty.iff_appLE (P := @LocallyQuasiFinite)]
  intro U V e
  have h1 : (f.appLE U V e).hom.FormallyUnramified :=
    HasRingHomProperty.appLE @FormallyUnramified f inferInstance U V e
  have h2 : (f.appLE U V e).hom.FiniteType :=
    HasRingHomProperty.appLE @LocallyOfFiniteType f inferInstance U V e
  algebraize [(f.appLE U V e).hom]
  exact (inferInstance : Algebra.QuasiFinite Γ(Y, U) Γ(X, V))

variable {K : Type} [Field K]

/-- A `K`-morphism between abelian varieties is proper (source proper, target separated). -/
theorem isProper_left (A B : PkgI3.AbVar K) (f : A.X ⟶ B.X) : IsProper f.left := by
  have : IsProper (f.left ≫ B.X.hom) := by rw [Over.w]; infer_instance
  exact IsProper.of_comp f.left B.X.hom

/-- **Glue.** A locally quasi-finite open `K`-endomorphism of an abelian variety is finite and
surjective. -/
theorem isIsogenyMor_of_lqf_of_isOpenMap (A : PkgI3.AbVar K) (f : A.X ⟶ A.X)
    [LocallyQuasiFinite f.left] (ho : IsOpenMap f.left.base) : PkgI3.AbVar.IsIsogenyMor f := by
  have := isProper_left A A f
  refine ⟨IsFinite.of_isProper_of_locallyQuasiFinite f.left, ⟨?_⟩⟩
  have : IrreducibleSpace A.X.left :=
    GeometricallyIrreducible.irreducibleSpace_of_subsingleton (f := A.X.hom)
  have hcl : IsClopen (Set.range f.left.base) :=
    ⟨f.left.isClosedMap.isClosed_range, ho.isOpen_range⟩
  have hne : (Set.range f.left.base).Nonempty :=
    ⟨_, ⟨η[A.X].left (IsLocalRing.closedPoint K), rfl⟩⟩
  exact Set.range_eq_univ.mp (hcl.eq_univ hne)

/-- Under a locally quasi-finite morphism, a strict specialization maps to two distinct points
(the fibres are discrete, Mathlib `Scheme.Hom.isDiscrete_preimage_singleton`). -/
theorem ne_of_specializes_of_lqf {X Y : Scheme} (f : X ⟶ Y) [LocallyQuasiFinite f]
    {x y : X} (hxy : x ⤳ y) (hne : x ≠ y) : f x ≠ f y := by
  intro heq
  have hd := (f.isDiscrete_preimage_singleton (f y)).to_subtype
  let x' : (f.base ⁻¹' {f y} : Set X) := ⟨x, heq⟩
  let y' : (f.base ⁻¹' {f y} : Set X) := ⟨y, rfl⟩
  have h' : x' ⤳ y' := (subtype_specializes_iff x' y').mpr hxy
  exact hne (congrArg Subtype.val h'.eq)

/-- **A locally quasi-finite closed self-map of an irreducible Noetherian scheme is
surjective.** If `f ξ ≠ ξ` for the generic point `ξ`, then `ξ ⤳ f ξ ⤳ f² ξ ⤳ ⋯` are strict
specializations (continuity, and `ne_of_specializes_of_lqf`), so the closures `cl{fᵐ ξ}` form a
strictly decreasing chain of closed sets, contradicting Noetherianity. So `ξ ∈ range f`, which is
closed, hence everything. -/
theorem surjective_of_lqf_self {X : Scheme} [IrreducibleSpace X] [TopologicalSpace.NoetherianSpace X]
    (f : X ⟶ X) [LocallyQuasiFinite f] (hc : IsClosedMap f.base) :
    Function.Surjective f.base := by
  set ξ := genericPoint X
  have hξ : ∀ x : X, ξ ⤳ x := fun x => (genericPoint_spec X).specializes trivial
  have hfix : f ξ = ξ := by
    by_contra hne
    let s : ℕ → X := fun m => (f.base)^[m] ξ
    have hs : ∀ m, s m ⤳ s (m + 1) ∧ s m ≠ s (m + 1) := by
      intro m
      induction m with
      | zero => exact ⟨hξ _, fun h => hne h.symm⟩
      | succ m ih =>
        have e1 : s (m + 1) = f (s m) := Function.iterate_succ_apply' _ _ _
        have e2 : s (m + 1 + 1) = f (s (m + 1)) := Function.iterate_succ_apply' _ _ _
        rw [e1, e2]
        exact ⟨ih.1.map f.base.hom.continuous, ne_of_specializes_of_lqf f ih.1 ih.2⟩
    let c : ℕ → TopologicalSpace.Closeds X := fun m => ⟨closure {s m}, isClosed_closure⟩
    have hc' : StrictAnti c := by
      refine strictAnti_nat_of_succ_lt fun m => ?_
      refine lt_of_le_of_ne ?_ ?_
      · change closure {s (m + 1)} ⊆ closure {s m}
        exact specializes_iff_closure_subset.mp (hs m).1
      · intro h
        have h2 : closure {s (m + 1)} = closure {s m} := congrArg SetLike.coe h
        exact (hs m).2 (inseparable_iff_closure_eq.mpr h2.symm).eq
    exact not_strictAnti_of_wellFoundedLT c hc'
  intro y
  have hy : y ∈ closure {ξ} := specializes_iff_mem_closure.mp (hξ y)
  exact (hc.isClosed_range.closure_subset_iff.mpr
    (Set.singleton_subset_iff.mpr ⟨ξ, hfix⟩)) hy

end ZInQ.Contrib.AbVarBC.MulRigidity

namespace ZInQ.Contrib.AbVarBC.G0FibreSimple

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj

/-- **Textbook leaf (Mumford, *Abelian varieties*, §4, Application 2 / §6, over an algebraically
closed field; Milne, *Abelian varieties* (Cornell–Silverman 1986), Thm 8.2, over any field;
locators UNVERIFIED): multiplication by `n ≠ 0` is an isogeny** (finite and surjective, of degree
`n^{2g}`), stated in characteristic `0`. The degree is dropped, so this is a consequence of the
published statement. -/
def MulIsogeny : Prop :=
  ∀ (k : Type) [Field k] [CharZero k] (A : PkgI3.AbVar k) (n : ℤ), n ≠ 0 →
    PkgI3.AbVar.IsIsogenyMor ((n : PkgI3.AbVar.End A).hom)

end ZInQ.Contrib.AbVarBC.G0FibreSimple

namespace ZInQ.Contrib.AbVarBC.MulRigidity

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj

/-- **Leaf (Mumford, *Abelian varieties*, §4 Application 2 and §6: `n_X` is separable when
`char k ∤ n`; Milne, *Abelian varieties* (Cornell–Silverman 1986), Thm 8.2: `n_A` is étale iff
`char k ∤ n`; locators UNVERIFIED).** In characteristic `0`, `[n]` is étale for `n ≠ 0`. A
consequence of the published statement (only characteristic `0`). -/
def MulEtale : Prop :=
  ∀ (k : Type) [Field k] [CharZero k] (A : PkgI3.AbVar k) (n : ℤ), n ≠ 0 →
    Etale ((n : PkgI3.AbVar.End A).hom).left

/-- **Leaf (the infinitesimal half of `MulEtale`; Mumford §4: `d(n_X) = n` on the tangent space
at `0`, so `n_X^* ω = n ω` for invariant differentials; locator UNVERIFIED).** In characteristic
`0`, `[n]` is formally unramified (`Ω_{[n]} = 0`) for `n ≠ 0`. Implied by `MulEtale`
(`mulUnramified_of_mulEtale`). -/
def MulUnramified : Prop :=
  ∀ (k : Type) [Field k] [CharZero k] (A : PkgI3.AbVar k) (n : ℤ), n ≠ 0 →
    FormallyUnramified ((n : PkgI3.AbVar.End A).hom).left

/-- **Leaf (dimension theory; Mumford §4 / Milne, *Abelian varieties*, Prop. 8.1: a homomorphism
of abelian varieties of the same dimension with finite kernel is surjective, an isogeny; locators
UNVERIFIED).** A locally quasi-finite endomorphism of an abelian variety is surjective
(any characteristic). -/
def QuasiFiniteEndSurjective : Prop :=
  ∀ (k : Type) [Field k] (A : PkgI3.AbVar k) (f : PkgI3.AbVar.End A),
    LocallyQuasiFinite f.hom.left → Surjective f.hom.left

theorem mulUnramified_of_mulEtale (h : MulEtale) : MulUnramified := by
  intro k _ _ A n hn
  have := h k A n hn
  infer_instance

/-- **`MulIsogeny` from `MulEtale`** (glue proved here). -/
theorem mulIsogeny_of_mulEtale (h : MulEtale) : G0FibreSimple.MulIsogeny := by
  intro k _ _ A n hn
  have := h k A n hn
  have := isProper_left A A ((n : PkgI3.AbVar.End A).hom)
  have := locallyQuasiFinite_of_formallyUnramified ((n : PkgI3.AbVar.End A).hom).left
  exact isIsogenyMor_of_lqf_of_isOpenMap A _ (Scheme.Hom.isOpenMap _)

/-- **`MulIsogeny` from `MulUnramified` and `QuasiFiniteEndSurjective`** (glue proved here). -/
theorem mulIsogeny_of_mulUnramified (h1 : MulUnramified) (h2 : QuasiFiniteEndSurjective) :
    G0FibreSimple.MulIsogeny := by
  intro k _ _ A n hn
  have := h1 k A n hn
  have := isProper_left A A ((n : PkgI3.AbVar.End A).hom)
  have := locallyQuasiFinite_of_formallyUnramified ((n : PkgI3.AbVar.End A).hom).left
  exact ⟨IsFinite.of_isProper_of_locallyQuasiFinite _, h2 k A _ inferInstance⟩

/-- **`QuasiFiniteEndSurjective` holds** (proved from Mathlib; it is not a leaf). -/
theorem quasiFiniteEndSurjective : QuasiFiniteEndSurjective := by
  intro k _ A f hf
  have := isProper_left A A f.hom
  have : IrreducibleSpace A.X.left :=
    GeometricallyIrreducible.irreducibleSpace_of_subsingleton (f := A.X.hom)
  have : CompactSpace A.X.left := QuasiCompact.compactSpace_of_compactSpace A.X.hom
  have : IsNoetherian A.X.left := { __ := LocallyOfFiniteType.isLocallyNoetherian A.X.hom }
  exact ⟨surjective_of_lqf_self f.hom.left f.hom.left.isClosedMap⟩

/-- **`MulIsogeny` from the single leaf `MulUnramified`** (glue proved here). -/
theorem mulIsogeny_of_mulUnramified' (h : MulUnramified) : G0FibreSimple.MulIsogeny :=
  mulIsogeny_of_mulUnramified h quasiFiniteEndSurjective

end ZInQ.Contrib.AbVarBC.MulRigidity


/-! ## `MulUnramified` reduced to a statement at the origin of the kernel `A[n]` -/

namespace ZInQ.Contrib.AbVarBC.MulRigidity

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj

variable {K : Type} [Field K]

/-- The unit section `Spec K → ker f = A ×_{f, A, e} Spec K` of the kernel of a homomorphism. -/
def kerUnit (A : PkgI3.AbVar K) (f : A.X ⟶ A.X) [IsMonHom f] :
    𝟙_ (Over (Spec (.of K))) ⟶ pullback f η[A.X] :=
  pullback.lift η[A.X] (𝟙 _) (by rw [IsMonHom.one_hom, Category.id_comp])

/-- `(x, y) ↦ x⁻¹ y : A ×_{f, A, f} A → ker f`. -/
def diffKer (A : PkgI3.AbVar K) (f : A.X ⟶ A.X) [IsMonHom f] :
    pullback f f ⟶ pullback f η[A.X] :=
  pullback.lift ((pullback.fst f f)⁻¹ * pullback.snd f f) (toUnit _) (by
    rw [MonObj.mul_comp, GrpObj.inv_comp, pullback.condition, inv_mul_cancel, Hom.one_def])

/-- **The diagonal of a homomorphism `f` is the base change of the unit section of `ker f`**
along `(x, y) ↦ x⁻¹ y` (the square is cartesian: `x⁻¹ y = e ⇔ x = y`). -/
theorem diagonal_isPullback (A : PkgI3.AbVar K) (f : A.X ⟶ A.X) [IsMonHom f] :
    IsPullback (toUnit A.X) (pullback.diagonal f) (kerUnit A f) (diffKer A f) := by
  have key : ∀ {T : Over (Spec (.of K))} (a : T ⟶ pullback f f),
      a ≫ diffKer A f ≫ pullback.fst f η[A.X] = (a ≫ pullback.fst f f)⁻¹ * (a ≫ pullback.snd f f) := by
    intro T a
    simp only [diffKer, pullback.lift_fst, MonObj.comp_mul, GrpObj.comp_inv]
  refine IsPullback.flip ⟨⟨?_⟩, ⟨PullbackCone.IsLimit.mk _ (fun c => c.fst ≫ pullback.fst f f)
    ?_ ?_ ?_⟩⟩
  · apply pullback.hom_ext
    · rw [Category.assoc, key, pullback.diagonal_fst, pullback.diagonal_snd, inv_mul_cancel,
        Category.assoc]
      simp only [kerUnit, pullback.lift_fst, Hom.one_def]
    · exact toUnit_unique _ _
  · intro c
    have hc := congrArg (· ≫ pullback.fst f η[A.X]) c.condition
    simp only [Category.assoc] at hc
    simp only [kerUnit, pullback.lift_fst] at hc
    rw [key, toUnit_unique c.snd (toUnit _), ← Hom.one_def, inv_mul_eq_one] at hc
    apply pullback.hom_ext
    · simp
    · simp [hc]
  · intro c
    exact toUnit_unique _ _
  · intro c m hm _
    rw [← hm, Category.assoc, pullback.diagonal_fst, Category.comp_id]

/-- **Glue.** If the unit section of `ker f` is an open immersion, the homomorphism `f` is formally
unramified (its diagonal is an open immersion, as a base change of the unit section). -/
theorem formallyUnramified_of_kerUnit (A : PkgI3.AbVar K) (f : A.X ⟶ A.X) [IsMonHom f]
    (h : IsOpenImmersion (kerUnit A f).left) : FormallyUnramified f.left := by
  have hP := (Over.forget _).map_isPullback (diagonal_isPullback A f)
  have h1 : IsOpenImmersion (pullback.diagonal f).left :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback (P := @IsOpenImmersion) hP h
  let e := PreservesPullback.iso (Over.forget (Spec (.of K))) f f
  have he : pullback.diagonal f.left = (pullback.diagonal f).left ≫ e.hom := by
    apply pullback.hom_ext
    · rw [pullback.diagonal_fst, Category.assoc]
      erw [PreservesPullback.iso_hom_fst]
      show 𝟙 _ = (pullback.diagonal f).left ≫ (pullback.fst f f).left
      rw [← Over.comp_left, pullback.diagonal_fst]
      rfl
    · rw [pullback.diagonal_snd, Category.assoc]
      erw [PreservesPullback.iso_hom_snd]
      show 𝟙 _ = (pullback.diagonal f).left ≫ (pullback.snd f f).left
      rw [← Over.comp_left, pullback.diagonal_snd]
      rfl
  have : IsOpenImmersion (pullback.diagonal f.left) := by rw [he]; infer_instance
  infer_instance

/-- **Leaf (Mumford, *Abelian varieties*, §4, Application 2 and §6: `A[n]` is étale, of order
`n^{2g}`, when `char k ∤ n`; equivalently `d[n] = n` on the tangent space at `0`; Milne, *Abelian
varieties* (Cornell–Silverman 1986), Thm 8.2; locators UNVERIFIED).** In characteristic `0`, for
`n ≠ 0`, the unit section of the kernel `A[n] = A ×_{[n], A, e} Spec k` is an open immersion
(`A[n]` is unramified over `k` at the origin: its tangent space there, `ker(n · : Lie A → Lie A)`,
vanishes). A consequence of "`A[n]` is étale over `k`" (a section of an étale separated morphism
is an open immersion; `kerUnitOpen_of_mulEtale`). -/
def KerUnitOpen : Prop :=
  ∀ (k : Type) [Field k] [CharZero k] (A : PkgI3.AbVar k) (n : ℤ), n ≠ 0 →
    IsOpenImmersion (kerUnit A ((n : PkgI3.AbVar.End A).hom)).left

/-- A section of a formally unramified morphism locally of finite type is an open immersion
(Stacks 024T; from Mathlib's `isOpenImmersion_diagonal` and
`MorphismProperty.hasOfPostcompProperty_iff_le_diagonal`). -/
theorem isOpenImmersion_of_section {X Y : Scheme} (s : Y ⟶ X) (q : X ⟶ Y)
    [FormallyUnramified q] [LocallyOfFiniteType q] (h : s ≫ q = 𝟙 _) : IsOpenImmersion s := by
  set gr : Y ⟶ pullback (s ≫ q) q := pullback.lift (𝟙 Y) s (by simp)
  have e : s = gr ≫ pullback.snd _ _ := by simp [gr]
  rw [e]
  have h1 : IsOpenImmersion gr :=
    MorphismProperty.of_isPullback (P := @IsOpenImmersion) (pullback_lift_diagonal_isPullback s q)
      (FormallyUnramified.isOpenImmersion_diagonal q)
  have h2 : IsOpenImmersion (pullback.snd (s ≫ q) q) :=
    MorphismProperty.pullback_snd (P := @IsOpenImmersion) _ _
      (by rw [h]; exact (inferInstance : IsOpenImmersion (𝟙 Y)))
  infer_instance

/-- **`KerUnitOpen` is a consequence of `MulEtale`** (so it is implied by the published
statement): the kernel is a base change of `[n]`, hence étale over `k`, and its unit section is a
section of an étale morphism. -/
theorem kerUnitOpen_of_mulEtale (h : MulEtale) : KerUnitOpen := by
  intro k _ _ A n hn
  have hE : Etale ((n : PkgI3.AbVar.End A).hom).left := h k A n hn
  have hP := (Over.forget _).map_isPullback
    (IsPullback.of_hasPullback ((n : PkgI3.AbVar.End A).hom) η[A.X])
  have : Etale (pullback.snd ((n : PkgI3.AbVar.End A).hom) η[A.X]).left :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback (P := @Etale) hP hE
  refine isOpenImmersion_of_section _ (pullback.snd ((n : PkgI3.AbVar.End A).hom) η[A.X]).left ?_
  rw [← Over.comp_left]
  simp [kerUnit]

/-- `MulUnramified` from `KerUnitOpen` (glue proved here). -/
theorem mulUnramified_of_kerUnitOpen (h : KerUnitOpen) : MulUnramified := by
  intro k _ _ A n hn
  exact formallyUnramified_of_kerUnit A _ (h k A n hn)

/-- **`MulIsogeny` from the single leaf `KerUnitOpen`.** -/
theorem mulIsogeny_of_kerUnitOpen (h : KerUnitOpen) : G0FibreSimple.MulIsogeny :=
  mulIsogeny_of_mulUnramified' (mulUnramified_of_kerUnitOpen h)

end ZInQ.Contrib.AbVarBC.MulRigidity


/-! ## `KerUnitOpen` reduced to two glue statements on the cotangent space at the origin -/

namespace ZInQ.Contrib.AbVarBC.MulRigidity

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj

variable {K : Type} [Field K]

/-- The origin of `A`, as a point of the underlying space. -/
def origin (A : PkgI3.AbVar K) : A.X.left := η[A.X].left (IsLocalRing.closedPoint K)

theorem map_origin (A : PkgI3.AbVar K) (f : A.X ⟶ A.X) [IsMonHom f] :
    f.left (origin A) = origin A := by
  have h := congrArg (fun g : 𝟙_ (Over (Spec (.of K))) ⟶ A.X => g.left) (IsMonHom.one_hom f)
  simp only [Over.comp_left] at h
  exact (Scheme.Hom.comp_apply _ _ _).symm.trans
    (congrArg (fun g : (𝟙_ (Over (Spec (.of K)))).left ⟶ A.X.left => g (IsLocalRing.closedPoint K)) h)

/-- The local ring `𝒪_{A,0}` at the origin. -/
abbrev O0 (A : PkgI3.AbVar K) : CommRingCat := A.X.left.presheaf.stalk (origin A)

/-- The local endomorphism `f^♯ : 𝒪_{A,0} → 𝒪_{A,0}` of a homomorphism `f` (which fixes `0`). -/
def stalkEndo (A : PkgI3.AbVar K) (f : A.X ⟶ A.X) [IsMonHom f] : O0 A ⟶ O0 A :=
  (A.X.left.presheaf.stalkCongr (Inseparable.of_eq (map_origin A f).symm)).hom ≫
    f.left.stalkMap (origin A)

instance (A : PkgI3.AbVar K) (f : A.X ⟶ A.X) [IsMonHom f] : IsLocalHom (stalkEndo A f).hom := by
  unfold stalkEndo
  rw [CommRingCat.hom_comp]
  infer_instance

/-- The cotangent map `m₀/m₀² → m₀/m₀²` of a homomorphism `f` at the origin. -/
def cotangentMap (A : PkgI3.AbVar K) (f : A.X ⟶ A.X) [IsMonHom f] :
    IsLocalRing.CotangentSpace (O0 A) →ₗ[ℤ] IsLocalRing.CotangentSpace (O0 A) :=
  Ideal.mapCotangent _ _ (stalkEndo A f).hom.toIntAlgHom (fun x hx => by
    simp only [Ideal.mem_comap, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] at hx ⊢
    exact fun hu => hx (isUnit_of_map_unit (stalkEndo A f).hom x hu))

/-- **Glue (commutative algebra of the fibre `ker f`; Nakayama).** For a homomorphism `f : A → A`
over `k` whose cotangent map at the origin is surjective, the unit section of `ker f` is an open
immersion. *Why true* (STANDARD): `𝒪_{ker f, 0} = 𝒪_{A,0} / f^♯(m₀)𝒪_{A,0}` (the fibre of `f`
over the rational point `0`), so surjectivity gives `m₀ = f^♯(m₀)𝒪 + m₀²`, hence
`m₀ = f^♯(m₀)𝒪` by Nakayama, so `𝒪_{ker f, 0} = k`; a rational point of a Noetherian scheme with
local ring a field is isolated, and the open point is `Spec k`. Glue, unproved. -/
def KerUnitOpenOfCotangentSurj : Prop :=
  ∀ (k : Type) [Field k] (A : PkgI3.AbVar k) (f : A.X ⟶ A.X) [IsMonHom f],
    Function.Surjective (cotangentMap A f) → IsOpenImmersion (kerUnit A f).left

/-- **Glue (the group law to first order; Mumford §4, `d(n_X) = n`, UNVERIFIED locator).** The
cotangent map of `[n]` at the origin is multiplication by `n`, for every `n ∈ ℤ` and in every
characteristic. *Why true* (STANDARD): the unit axioms give `μ^♯(φ) ≡ φ ⊗ 1 + 1 ⊗ φ` modulo
`m ⊗ m` on cotangent spaces, so the cotangent map of `f * g = μ ∘ (f, g)` is the sum of those of
`f` and `g`; induct on `n`. Glue, unproved. -/
def CotangentMulN : Prop :=
  ∀ (k : Type) [Field k] (A : PkgI3.AbVar k) (n : ℤ),
    cotangentMap A ((n : PkgI3.AbVar.End A).hom) = n • LinearMap.id

/-- The residue field at the origin has characteristic `0` when `k` does. -/
theorem charZero_residueField [CharZero K] (A : PkgI3.AbVar K) :
    CharZero (IsLocalRing.ResidueField (O0 A)) := by
  let φ : K →+* IsLocalRing.ResidueField (O0 A) :=
    (IsLocalRing.residue (O0 A)).comp ((A.X.left.presheaf.Γgerm (origin A)).hom.comp
      ((A.X.hom.appTop).hom.comp (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom))
  exact (RingHom.charZero_iff φ.injective).mp inferInstance

/-- **`KerUnitOpen` from the two glue statements** (proved here: in characteristic `0`,
multiplication by `n ≠ 0` is bijective on the cotangent space, a vector space over the residue
field). -/
theorem kerUnitOpen_of_cotangent (h1 : KerUnitOpenOfCotangentSurj) (h2 : CotangentMulN) :
    KerUnitOpen := by
  intro k _ _ A n hn
  apply h1
  rw [h2]
  have := charZero_residueField A
  have hn' : (n : IsLocalRing.ResidueField (O0 A)) ≠ 0 := Int.cast_ne_zero.mpr hn
  intro v
  refine ⟨((n : IsLocalRing.ResidueField (O0 A))⁻¹) • v, ?_⟩
  rw [LinearMap.smul_apply, LinearMap.id_apply,
    ← Int.cast_smul_eq_zsmul (IsLocalRing.ResidueField (O0 A)), smul_smul, mul_inv_cancel₀ hn',
    one_smul]

/-- **`MulIsogeny` from glue alone**: the two cotangent-space glue statements imply it, with no
literature leaf. -/
theorem mulIsogeny_of_cotangent (h1 : KerUnitOpenOfCotangentSurj) (h2 : CotangentMulN) :
    G0FibreSimple.MulIsogeny :=
  mulIsogeny_of_kerUnitOpen (kerUnitOpen_of_cotangent h1 h2)

end ZInQ.Contrib.AbVarBC.MulRigidity



end

end LF2_AbVarBC_Mul

-- ===== ZInQKernel/Contrib/AbVarBC/Tangent.lean
section LF2_AbVarBC_Tangent

/-!
# Base change of abelian varieties, VIII: tangent vectors as dual-number points

Copyright: this file is part of the fork Deicyde/diophantine-z-q (task g9-abvarbc, 2026-11-13).

§1 For an affine open `U` of a scheme `X` and a local ring `Λ`, a morphism `p : Spec Λ → X`
sending the closed point into `U` is the same as a ring map `ptRing p : Γ(X, U) → Λ`
(`eq_ofRing_ptRing`, `ptRing_ofRing`, `ptRing_specMap_comp`, `ptRing_comp`).
-/

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct

set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

noncomputable section

namespace ZInQ.Contrib.AbVarBC.Tangent

/-! ## §1. Points of an affine open -/

section Gen

variable {X : Scheme.{0}} {U : X.Opens} (hU : IsAffineOpen U)
  {Λ : CommRingCat.{0}} [IsLocalRing Λ]

/-- The ring map `Γ(X, U) → Λ` of a `Λ`-point whose closed point lies in `U`. -/
def ptRing (p : Spec Λ ⟶ X) (hp : p (IsLocalRing.closedPoint Λ) ∈ U) : Γ(X, U) ⟶ Λ :=
  p.appLE U ⊤ (Scheme.preimage_eq_top_of_closedPoint_mem p hp).ge ≫ (Scheme.ΓSpecIso Λ).hom

theorem ptRing_congr {p q : Spec Λ ⟶ X} (e : p = q) (hp : p (IsLocalRing.closedPoint Λ) ∈ U)
    (hq : q (IsLocalRing.closedPoint Λ) ∈ U) : ptRing p hp = ptRing q hq := by
  subst e; rfl

/-- The point attached to a ring map `Γ(X, U) → Λ`. -/
def ofRing (φ : Γ(X, U) ⟶ Λ) : Spec Λ ⟶ X := Spec.map φ ≫ hU.fromSpec

theorem ofRing_mem (φ : Γ(X, U) ⟶ Λ) : ofRing hU φ (IsLocalRing.closedPoint Λ) ∈ U := by
  change ofRing hU φ _ ∈ (U : Set X)
  rw [← hU.range_fromSpec]
  exact ⟨_, (Scheme.Hom.comp_apply _ _ _).symm⟩

theorem eq_ofRing_ptRing (p : Spec Λ ⟶ X) (hp : p (IsLocalRing.closedPoint Λ) ∈ U) :
    p = ofRing hU (ptRing p hp) := by
  have h := IsAffineOpen.SpecMap_appLE_fromSpec p hU (isAffineOpen_top _)
    (Scheme.preimage_eq_top_of_closedPoint_mem p hp).ge
  rw [IsAffineOpen.fromSpec_top, Scheme.isoSpec_Spec_inv] at h
  rw [ofRing, ptRing, Spec.map_comp, Category.assoc, h, ← Category.assoc, ← Spec.map_comp,
    Iso.inv_hom_id, Spec.map_id, Category.id_comp]

theorem ptRing_ext (hU : IsAffineOpen U) {p q : Spec Λ ⟶ X} (hp : p (IsLocalRing.closedPoint Λ) ∈ U)
    (hq : q (IsLocalRing.closedPoint Λ) ∈ U) (h : ptRing p hp = ptRing q hq) : p = q := by
  rw [eq_ofRing_ptRing hU p hp, eq_ofRing_ptRing hU q hq, h]

theorem ptRing_ofRing (φ : Γ(X, U) ⟶ Λ) : ptRing (ofRing hU φ) (ofRing_mem hU φ) = φ := by
  have h := eq_ofRing_ptRing hU (ofRing hU φ) (ofRing_mem hU φ)
  unfold ofRing at h
  rw [cancel_mono] at h
  exact (Spec.map_injective h).symm

/-- Naturality in the local ring. -/
theorem ptRing_specMap_comp (hU : IsAffineOpen U) {Λ' : CommRingCat.{0}} [IsLocalRing Λ'] (ρ : Λ ⟶ Λ')
    (p : Spec Λ ⟶ X) (hp : p (IsLocalRing.closedPoint Λ) ∈ U)
    (hp' : (Spec.map ρ ≫ p) (IsLocalRing.closedPoint Λ') ∈ U) :
    ptRing (Spec.map ρ ≫ p) hp' = ptRing p hp ≫ ρ := by
  have e : Spec.map ρ ≫ p = ofRing hU (ptRing p hp ≫ ρ) := by
    conv_lhs => rw [eq_ofRing_ptRing hU p hp]
    rw [ofRing, ofRing, ← Category.assoc, ← Spec.map_comp]
  rw [ptRing_congr e hp' (ofRing_mem hU _), ptRing_ofRing]

/-- Naturality in the scheme. -/
theorem ptRing_comp (hU : IsAffineOpen U) {Y : Scheme.{0}} (f : X ⟶ Y) {U' : Y.Opens} (hU' : IsAffineOpen U')
    (hle : U ≤ f ⁻¹ᵁ U') (p : Spec Λ ⟶ X) (hp : p (IsLocalRing.closedPoint Λ) ∈ U)
    (hp' : (p ≫ f) (IsLocalRing.closedPoint Λ) ∈ U') :
    ptRing (p ≫ f) hp' = f.appLE U' U hle ≫ ptRing p hp := by
  have e : p ≫ f = ofRing hU' (f.appLE U' U hle ≫ ptRing p hp) := by
    conv_lhs => rw [eq_ofRing_ptRing hU p hp]
    rw [ofRing, ofRing, Category.assoc, ← IsAffineOpen.SpecMap_appLE_fromSpec f hU' hU hle,
      ← Category.assoc, ← Spec.map_comp]
  rw [ptRing_congr e hp' (ofRing_mem hU' _), ptRing_ofRing]

end Gen

/-! ## §2. Dual-number points of a `K`-scheme -/

section Dual

open TrivSqZeroExt

variable {K : Type} [Field K]

instance isLocalRing_tsze (V : Type) [AddCommGroup V] [Module K V] [Module Kᵐᵒᵖ V]
    [IsCentralScalar K V] : IsLocalRing (TrivSqZeroExt K V) where
  isUnit_or_isUnit_of_add_one {a b} h := by
    have h1 : a.fst + b.fst = 1 := by simpa using congrArg TrivSqZeroExt.fst h
    rcases eq_or_ne a.fst 0 with ha | ha
    · right
      rw [isUnit_iff_isUnit_fst, isUnit_iff_ne_zero]
      rw [ha, zero_add] at h1
      rw [h1]
      exact one_ne_zero
    · left
      rw [isUnit_iff_isUnit_fst, isUnit_iff_ne_zero]
      exact ha

/-- `Spec Λ` as a `K`-scheme. -/
def ptR (Λ : Type) [CommRing Λ] [Algebra K Λ] : Over (Spec (CommRingCat.of K)) :=
  Over.mk (Spec.map (CommRingCat.ofHom (algebraMap K Λ)))

/-- `Spec ρ` over `K` for a `K`-algebra map `ρ`. -/
def specHom {Λ Λ' : Type} [CommRing Λ] [Algebra K Λ] [CommRing Λ'] [Algebra K Λ']
    (ρ : Λ →ₐ[K] Λ') : ptR (K := K) Λ' ⟶ ptR Λ :=
  Over.homMk (Spec.map (CommRingCat.ofHom (ρ : Λ →+* Λ'))) (by
    simp only [ptR, Over.mk_hom, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    congr 2
    ext x
    simp)

theorem specHom_left {Λ Λ' : Type} [CommRing Λ] [Algebra K Λ] [CommRing Λ'] [Algebra K Λ']
    (ρ : Λ →ₐ[K] Λ') :
    (specHom ρ).left = Spec.map (CommRingCat.ofHom (ρ : Λ →+* Λ')) := rfl

theorem specHom_comp {Λ Λ' Λ'' : Type} [CommRing Λ] [Algebra K Λ] [CommRing Λ'] [Algebra K Λ']
    [CommRing Λ''] [Algebra K Λ''] (ρ : Λ →ₐ[K] Λ') (ρ' : Λ' →ₐ[K] Λ'') :
    specHom ρ' ≫ specHom ρ = specHom (ρ'.comp ρ) := by
  apply Over.OverMorphism.ext
  change Spec.map _ ≫ Spec.map _ = Spec.map _
  rw [← Spec.map_comp]
  rfl

theorem specHom_id {Λ : Type} [CommRing Λ] [Algebra K Λ] :
    specHom (AlgHom.id K Λ) = 𝟙 (ptR Λ) := by
  apply Over.OverMorphism.ext
  change Spec.map (CommRingCat.ofHom (RingHom.id Λ)) = 𝟙 _
  rw [CommRingCat.ofHom_id, Spec.map_id]

variable (A : PkgI3.AbVar K)

/-- The origin of `A` as a morphism `Spec K → A`. -/
def orig : Spec (CommRingCat.of K) ⟶ A.X.left := η[A.X].left

/-- The trivial point is `Spec Λ → Spec K → A` through the origin. -/
theorem one_left {Λ : Type} [CommRing Λ] [Algebra K Λ] :
    (1 : ptR (K := K) Λ ⟶ A.X).left =
      Spec.map (CommRingCat.ofHom (algebraMap K Λ)) ≫ orig A := by
  rw [Hom.one_def, Over.comp_left]
  rfl

end Dual

/-! ## §3. Tangent vectors of an abelian variety at the origin -/

section AbTan

open TrivSqZeroExt

variable {K : Type} [Field K] (A : PkgI3.AbVar K)

instance isLocalHom_fstHom (V : Type) [AddCommGroup V] [Module K V] [Module Kᵐᵒᵖ V]
    [IsCentralScalar K V] : IsLocalHom ((fstHom K K V : TrivSqZeroExt K V →ₐ[K] K) :
      TrivSqZeroExt K V →+* K) where
  map_nonunit _ hx := isUnit_iff_isUnit_fst.mpr hx

/-- A `V`-valued tangent vector at the origin: a point `Spec (K ⊕ V) → A` over `K` reducing to the
origin. -/
def AtOrigin {V : Type} [AddCommGroup V] [Module K V] [Module Kᵐᵒᵖ V] [IsCentralScalar K V]
    (a : ptR (K := K) (TrivSqZeroExt K V) ⟶ A.X) : Prop :=
  specHom (fstHom K K V) ≫ a = 1

variable {V W : Type} [AddCommGroup V] [Module K V] [Module Kᵐᵒᵖ V] [IsCentralScalar K V]
  [AddCommGroup W] [Module K W] [Module Kᵐᵒᵖ W] [IsCentralScalar K W]

theorem atOrigin_one : AtOrigin A (1 : ptR (K := K) (TrivSqZeroExt K V) ⟶ A.X) :=
  MonObj.comp_one _

theorem atOrigin_mul {a b : ptR (K := K) (TrivSqZeroExt K V) ⟶ A.X} (ha : AtOrigin A a)
    (hb : AtOrigin A b) : AtOrigin A (a * b) := by
  unfold AtOrigin at *
  rw [MonObj.comp_mul, ha, hb, _root_.mul_one]

theorem atOrigin_map (g : V →ₗ[K] W) {a : ptR (K := K) (TrivSqZeroExt K V) ⟶ A.X}
    (ha : AtOrigin A a) : AtOrigin A (specHom (map g) ≫ a) := by
  unfold AtOrigin at *
  rw [← Category.assoc, specHom_comp, fstHom_comp_map, ha]

theorem closedPoint_eq :
    Spec.map (CommRingCat.ofHom ((fstHom K K V : TrivSqZeroExt K V →ₐ[K] K) :
      TrivSqZeroExt K V →+* K)) (IsLocalRing.closedPoint K) =
      IsLocalRing.closedPoint (TrivSqZeroExt K V) := by
  haveI : IsLocalHom (CommRingCat.ofHom ((fstHom K K V : TrivSqZeroExt K V →ₐ[K] K) :
      TrivSqZeroExt K V →+* K)).hom := isLocalHom_fstHom V
  exact Spec_closedPoint (R := CommRingCat.of (TrivSqZeroExt K V)) (S := CommRingCat.of K)

/-- The closed point of a tangent vector at the origin is the origin. -/
theorem left_closedPoint {a : ptR (K := K) (TrivSqZeroExt K V) ⟶ A.X} (ha : AtOrigin A a) :
    a.left (IsLocalRing.closedPoint (TrivSqZeroExt K V)) =
      orig A (IsLocalRing.closedPoint K) := by
  have h1 := congrArg (fun f => (f.left : Spec (CommRingCat.of K) ⟶ A.X.left)
    (IsLocalRing.closedPoint K)) ha
  simp only at h1
  rw [one_left, Over.comp_left] at h1
  erw [Scheme.Hom.comp_apply, Scheme.Hom.comp_apply] at h1
  rw [← closedPoint_eq]
  refine h1.trans ?_
  congr 1

end AbTan

/-! ## §4. The derivation of a tangent vector; additivity under the group law -/

section Deriv

open TrivSqZeroExt

variable {K : Type} [Field K] (A : PkgI3.AbVar K) {U : A.X.left.Opens} (hU : IsAffineOpen U)
  (ho : orig A (IsLocalRing.closedPoint K) ∈ U)

variable {V W : Type} [AddCommGroup V] [Module K V] [Module Kᵐᵒᵖ V] [IsCentralScalar K V]
  [AddCommGroup W] [Module K W] [Module Kᵐᵒᵖ W] [IsCentralScalar K W]

theorem mem_of_atOrigin (ho : orig A (IsLocalRing.closedPoint K) ∈ U) {a : ptR (K := K) (TrivSqZeroExt K V) ⟶ A.X} (ha : AtOrigin A a) :
    a.left (IsLocalRing.closedPoint (TrivSqZeroExt K V)) ∈ U := by
  rw [left_closedPoint A ha]
  exact ho

theorem comp_orig_mem (ho : orig A (IsLocalRing.closedPoint K) ∈ U) {Λ : CommRingCat.{0}} (p : Spec Λ ⟶ Spec (CommRingCat.of K)) (x : Spec Λ) :
    (p ≫ orig A) x ∈ U := by
  show orig A (p x) ∈ U
  rw [Subsingleton.elim (p x) (IsLocalRing.closedPoint K)]
  exact ho

/-- The evaluation `Γ(A, U) → K` at the origin. -/
def ev0 : Γ(A.X.left, U) ⟶ CommRingCat.of K := ptRing (orig A) ho

/-- The ring map `Γ(A, U) → K ⊕ V` of a tangent vector at the origin. -/
def tRing {a : ptR (K := K) (TrivSqZeroExt K V) ⟶ A.X} (ha : AtOrigin A a) :
    Γ(A.X.left, U) ⟶ CommRingCat.of (TrivSqZeroExt K V) :=
  ptRing (Λ := CommRingCat.of (TrivSqZeroExt K V)) a.left (mem_of_atOrigin A ho ha)

/-- The derivation `Γ(A, U) → V` of a tangent vector at the origin. -/
def D {a : ptR (K := K) (TrivSqZeroExt K V) ⟶ A.X} (ha : AtOrigin A a) (x : Γ(A.X.left, U)) : V :=
  ((tRing A ho ha).hom x).snd

theorem tRing_specHom (hU : IsAffineOpen U) {a : ptR (K := K) (TrivSqZeroExt K V) ⟶ A.X} (ha : AtOrigin A a)
    (g : V →ₗ[K] W) :
    tRing A ho (atOrigin_map A g ha) =
      tRing A ho ha ≫ CommRingCat.ofHom ((map g : TrivSqZeroExt K V →ₐ[K] _) :
        TrivSqZeroExt K V →+* TrivSqZeroExt K W) :=
  ptRing_specMap_comp hU _ _ _ _

theorem tRing_congr {a b : ptR (K := K) (TrivSqZeroExt K V) ⟶ A.X} (e : a = b)
    (ha : AtOrigin A a) (hb : AtOrigin A b) : tRing A ho ha = tRing A ho hb := by
  subst e; rfl

theorem tRing_one (hU : IsAffineOpen U) :
    tRing A ho (atOrigin_one A (V := V)) =
      ev0 A ho ≫ CommRingCat.ofHom (algebraMap K (TrivSqZeroExt K V)) := by
  unfold tRing ev0
  rw [← ptRing_specMap_comp hU _ _ ho (comp_orig_mem A ho _ _)]
  exact ptRing_congr (one_left A) _ _

theorem fst_tRing (hU : IsAffineOpen U) {a : ptR (K := K) (TrivSqZeroExt K V) ⟶ A.X} (ha : AtOrigin A a)
    (x : Γ(A.X.left, U)) : ((tRing A ho ha).hom x).fst = (ev0 A ho).hom x := by
  have h1 : tRing A ho ha ≫ CommRingCat.ofHom ((fstHom K K V : TrivSqZeroExt K V →ₐ[K] K) :
      TrivSqZeroExt K V →+* K) = ev0 A ho ≫ CommRingCat.ofHom (algebraMap K K) := by
    unfold tRing ev0
    rw [← ptRing_specMap_comp hU _ _ (mem_of_atOrigin A ho ha) (by
        show a.left (Spec.map (CommRingCat.ofHom ((fstHom K K V : TrivSqZeroExt K V →ₐ[K] K) :
          TrivSqZeroExt K V →+* K)) (IsLocalRing.closedPoint K)) ∈ U
        rw [closedPoint_eq]
        exact mem_of_atOrigin A ho ha),
      ← ptRing_specMap_comp hU _ _ ho (comp_orig_mem A ho _ _)]
    refine ptRing_congr ?_ _ _
    have := congrArg (fun f => f.left) ha
    simp only [Over.comp_left, one_left] at this
    exact this
  have := congrArg (fun f => f.hom x) h1
  simpa using this

theorem D_one (hU : IsAffineOpen U) : D A ho (atOrigin_one A (V := V)) = 0 := by
  funext x
  unfold D
  rw [tRing_one A ho hU]
  simp [algebraMap_eq_inl]

/-- A tangent vector at the origin is determined by its derivation. -/
theorem eq_of_D_eq (hU : IsAffineOpen U) {a b : ptR (K := K) (TrivSqZeroExt K V) ⟶ A.X} (ha : AtOrigin A a)
    (hb : AtOrigin A b) (h : D A ho ha = D A ho hb) : a = b := by
  apply Over.OverMorphism.ext
  apply ptRing_ext hU (mem_of_atOrigin A ho ha) (mem_of_atOrigin A ho hb)
  ext x
  · exact (fst_tRing A ho hU ha x).trans (fst_tRing A ho hU hb x).symm
  · exact congrFun h x

end Deriv

/-! ## §5. Additivity: `D (v * w) = D v + D w` -/

section Mul

open TrivSqZeroExt

variable {K : Type} [Field K] (A : PkgI3.AbVar K) {U : A.X.left.Opens}
  (ho : orig A (IsLocalRing.closedPoint K) ∈ U)

theorem map_fst_inr :
    (map (LinearMap.fst K K K)).comp (map (LinearMap.inr K K K)) =
      (inlAlgHom K K K).comp (fstHom K K K) := by
  rw [← map_comp_map]
  apply algHom_ext
  intro x
  rw [map_inr, AlgHom.comp_apply, fstHom_apply, fst_inr]
  simp only [LinearMap.comp_apply, LinearMap.inr_apply, LinearMap.fst_apply,
    LinearMap.inl_apply, LinearMap.snd_apply, inr_zero, map_zero]

theorem map_snd_inl :
    (map (LinearMap.snd K K K)).comp (map (LinearMap.inl K K K)) =
      (inlAlgHom K K K).comp (fstHom K K K) := by
  rw [← map_comp_map]
  apply algHom_ext
  intro x
  rw [map_inr, AlgHom.comp_apply, fstHom_apply, fst_inr]
  simp only [LinearMap.comp_apply, LinearMap.inr_apply, LinearMap.fst_apply,
    LinearMap.inl_apply, LinearMap.snd_apply, inr_zero, map_zero]

theorem map_fst_inl :
    (map (LinearMap.fst K K K)).comp (map (LinearMap.inl K K K)) = AlgHom.id K _ := by
  rw [← map_comp_map, LinearMap.fst_comp_inl, map_id]

theorem map_snd_inr :
    (map (LinearMap.snd K K K)).comp (map (LinearMap.inr K K K)) = AlgHom.id K _ := by
  rw [← map_comp_map, LinearMap.snd_comp_inr, map_id]

theorem map_add_inl :
    (map (LinearMap.fst K K K + LinearMap.snd K K K)).comp (map (LinearMap.inl K K K)) =
      AlgHom.id K _ := by
  rw [← map_comp_map]
  convert map_id (R' := K) (M := K)
  ext
  simp

theorem map_add_inr :
    (map (LinearMap.fst K K K + LinearMap.snd K K K)).comp (map (LinearMap.inr K K K)) =
      AlgHom.id K _ := by
  rw [← map_comp_map]
  convert map_id (R' := K) (M := K)
  ext
  simp

theorem spec_inl_fst_comp {a : ptR (K := K) (TrivSqZeroExt K K) ⟶ A.X} (ha : AtOrigin A a) :
    specHom ((inlAlgHom K K K).comp (fstHom K K K)) ≫ a = 1 := by
  rw [← specHom_comp, Category.assoc]
  unfold AtOrigin at ha
  rw [ha, MonObj.comp_one]

/-- **Additivity of the derivation under the group law.** -/
theorem D_mul (hU : IsAffineOpen U) {v w : ptR (K := K) (TrivSqZeroExt K K) ⟶ A.X}
    (hv : AtOrigin A v) (hw : AtOrigin A w) :
    D A ho (atOrigin_mul A hv hw) = D A ho hv + D A ho hw := by
  set c := (specHom (map (LinearMap.inl K K K)) ≫ v) * (specHom (map (LinearMap.inr K K K)) ≫ w)
    with hcdef
  have hc : AtOrigin A c := atOrigin_mul A (atOrigin_map A _ hv) (atOrigin_map A _ hw)
  have e1 : specHom (map (LinearMap.fst K K K)) ≫ c = v := by
    rw [hcdef, MonObj.comp_mul, ← Category.assoc, ← Category.assoc, specHom_comp, specHom_comp,
      map_fst_inl, map_fst_inr, specHom_id, Category.id_comp, spec_inl_fst_comp A hw,
      _root_.mul_one]
  have e2 : specHom (map (LinearMap.snd K K K)) ≫ c = w := by
    rw [hcdef, MonObj.comp_mul, ← Category.assoc, ← Category.assoc, specHom_comp, specHom_comp,
      map_snd_inl, map_snd_inr, specHom_id, Category.id_comp, spec_inl_fst_comp A hv,
      _root_.one_mul]
  have e3 : specHom (map (LinearMap.fst K K K + LinearMap.snd K K K)) ≫ c = v * w := by
    rw [hcdef, MonObj.comp_mul, ← Category.assoc, ← Category.assoc, specHom_comp, specHom_comp,
      map_add_inl, map_add_inr, specHom_id, Category.id_comp, Category.id_comp]
  have h1 := (tRing_congr A ho e1 (atOrigin_map A _ hc) hv).symm.trans
    (tRing_specHom A ho hU hc _)
  have h2 := (tRing_congr A ho e2 (atOrigin_map A _ hc) hw).symm.trans
    (tRing_specHom A ho hU hc _)
  have h3 := (tRing_congr A ho e3 (atOrigin_map A _ hc) (atOrigin_mul A hv hw)).symm.trans
    (tRing_specHom A ho hU hc _)
  funext x
  simp only [D, Pi.add_apply, h1, h2, h3, CommRingCat.hom_comp, RingHom.comp_apply,
    CommRingCat.hom_ofHom, AlgHom.coe_toRingHom, snd_map, LinearMap.add_apply,
    LinearMap.fst_apply, LinearMap.snd_apply]

end Mul

/-! ## §6. `[n]` on tangent vectors -/

section Zpow

open TrivSqZeroExt

variable {K : Type} [Field K] (A : PkgI3.AbVar K) {U : A.X.left.Opens}
  (ho : orig A (IsLocalRing.closedPoint K) ∈ U)

theorem intCast_hom (n : ℤ) : ((n : PkgI3.AbVar.End A)).hom = (𝟙 A.X) ^ n := by
  rw [← zsmul_one]
  change (Additive.toMul (n • (1 : PkgI3.AbVar.End A))).1 = _
  rw [toMul_zsmul, Subgroup.coe_zpow]
  rfl

/-- `q ≫ [n] = q ^ n`. -/
theorem comp_intCast_hom {T : Over (Spec (CommRingCat.of K))} (q : T ⟶ A.X) (n : ℤ) :
    q ≫ ((n : PkgI3.AbVar.End A)).hom = q ^ n := by
  rw [intCast_hom, GrpObj.comp_zpow, Category.comp_id]

variable {V : Type} [AddCommGroup V] [Module K V] [Module Kᵐᵒᵖ V] [IsCentralScalar K V]

theorem atOrigin_inv {a : ptR (K := K) (TrivSqZeroExt K V) ⟶ A.X} (ha : AtOrigin A a) :
    AtOrigin A a⁻¹ := by
  unfold AtOrigin at *
  rw [GrpObj.comp_inv, ha, inv_one]

theorem atOrigin_zpow {a : ptR (K := K) (TrivSqZeroExt K V) ⟶ A.X} (ha : AtOrigin A a) (n : ℤ) :
    AtOrigin A (a ^ n) := by
  unfold AtOrigin at *
  rw [GrpObj.comp_zpow, ha, one_zpow]

theorem D_congr {a b : ptR (K := K) (TrivSqZeroExt K V) ⟶ A.X} (e : a = b) (ha : AtOrigin A a)
    (hb : AtOrigin A b) : D A ho ha = D A ho hb := by
  subst e; rfl

theorem D_inv (hU : IsAffineOpen U) {v : ptR (K := K) (TrivSqZeroExt K K) ⟶ A.X}
    (hv : AtOrigin A v) : D A ho (atOrigin_inv A hv) = - D A ho hv := by
  have h := D_mul A ho hU hv (atOrigin_inv A hv)
  rw [D_congr A ho (mul_inv_cancel v) _ (atOrigin_one A), D_one A ho hU] at h
  exact (neg_eq_of_add_eq_zero_right h.symm).symm

theorem D_zpow (hU : IsAffineOpen U) {v : ptR (K := K) (TrivSqZeroExt K K) ⟶ A.X}
    (hv : AtOrigin A v) (n : ℤ) : D A ho (atOrigin_zpow A hv n) = n • D A ho hv := by
  induction n using Int.induction_on with
  | zero =>
    rw [D_congr A ho (zpow_zero v) _ (atOrigin_one A), D_one A ho hU, zero_smul]
  | succ m ih =>
    rw [D_congr A ho (zpow_add_one v m) _ (atOrigin_mul A (atOrigin_zpow A hv m) hv),
      D_mul A ho hU (atOrigin_zpow A hv m) hv, ih, add_smul, one_smul]
  | pred m ih =>
    rw [D_congr A ho (zpow_sub_one v (-(m : ℤ))) _
      (atOrigin_mul A (atOrigin_zpow A hv _) (atOrigin_inv A hv)),
      D_mul A ho hU (atOrigin_zpow A hv _) (atOrigin_inv A hv), ih, D_inv A ho hU, sub_smul,
      one_smul, sub_eq_add_neg]

/-- **A tangent vector at the origin killed by `[n]`, `n ≠ 0`, characteristic `0`, is trivial.** -/
theorem eq_one_of_comp_intCast [CharZero K] (ho : orig A (IsLocalRing.closedPoint K) ∈ U) (hU : IsAffineOpen U)
    {v : ptR (K := K) (TrivSqZeroExt K K) ⟶ A.X} (hv : AtOrigin A v) (n : ℤ) (hn : n ≠ 0)
    (h : v ≫ ((n : PkgI3.AbVar.End A)).hom = 1) : v = 1 := by
  rw [comp_intCast_hom] at h
  have h1 := D_zpow A ho hU hv n
  rw [D_congr A ho h _ (atOrigin_one A), D_one A ho hU] at h1
  have h2 : D A ho hv = 0 := by
    funext x
    have := congrFun h1 x
    simp only [Pi.zero_apply, Pi.smul_apply] at this
    rw [← Int.cast_smul_eq_zsmul K, smul_eq_mul] at this
    exact (mul_eq_zero.mp this.symm).resolve_left (Int.cast_ne_zero.mpr hn)
  refine eq_of_D_eq A ho hU hv (atOrigin_one A) ?_
  rw [h2, D_one A ho hU]

end Zpow

end ZInQ.Contrib.AbVarBC.Tangent

end

end LF2_AbVarBC_Tangent

-- ===== ZInQKernel/Contrib/AbVarBC/KerUnit.lean
section LF2_AbVarBC_KerUnit

/-!
# Base change of abelian varieties, IX: the unit section of `A[n]` is an open immersion

Copyright: this file is part of the fork Deicyde/diophantine-z-q (task g9-abvarbc, 2026-11-13).

In characteristic `0` and for `n ≠ 0`, the unit section `kerUnit A [n] : Spec K → A[n]` is an
open immersion: mul-rigidity's leaf `KerUnitOpen` is a theorem (`kerUnitOpen`). Proof:
* §1 a `K`-derivation `D : Γ(A[n], W) → K` at the origin gives a tangent vector `v` of `A[n]`;
  its image in `A` is a tangent vector killed by `[n]`, hence trivial (`Tangent.lean` §6), so
  `v` is trivial and `D = 0` (`derivation_eq_zero`);
* §2 hence the maximal ideal `P` of the origin in `T = Γ(A[n], W)` satisfies `P = P²`
  (functionals on `P / P²` are derivations), so `P = (e)` with `e` idempotent (`T` Noetherian);
* §3 on the basic open `D(1 - e)` the structure map to `Spec K` is surjective on sections, so
  formally unramified, and the unit section is a section of it, hence an open immersion.
-/

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct

set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

noncomputable section

namespace ZInQ.Contrib.AbVarBC.Tangent

open TrivSqZeroExt

/-! ## §1. Derivations at the origin of `A[n]` vanish -/

section Der

variable {K : Type} [Field K]

/-- The ring map `t ↦ ev t + ε D t` of a derivation `D` at `ev`. -/
def dualHom {T : Type} [CommRing T] (ev : T →+* K) (D : T → K)
    (hadd : ∀ a b, D (a + b) = D a + D b) (hmul : ∀ a b, D (a * b) = ev a * D b + ev b * D a) :
    T →+* TrivSqZeroExt K K where
  toFun t := inl (ev t) + inr (D t)
  map_one' := by
    have h : D 1 = 0 := by
      have := hmul 1 1
      rw [_root_.mul_one, map_one, _root_.one_mul] at this
      linear_combination -this
    ext <;> simp [h]
  map_mul' a b := by
    ext
    · simp
    · simp [hmul]
      ring
  map_zero' := by
    have h : D 0 = 0 := by
      have := hadd 0 0
      rw [add_zero] at this
      linear_combination -this
    ext <;> simp [h]
  map_add' a b := by
    ext
    · simp
    · simp [hadd]

end Der

section KerDer

variable {K : Type} [Field K] (A : PkgI3.AbVar K) (n : ℤ)

/-- `[n] : A → A`. -/
abbrev mulN : A.X ⟶ A.X := ((n : PkgI3.AbVar.End A)).hom

/-- The kernel `A[n]` (as an object over `Spec K`). -/
abbrev KerN : Over (Spec (CommRingCat.of K)) := pullback (mulN A n) η[A.X]

/-- The unit section of `A[n]`, as a morphism of schemes. -/
def ks : Spec (CommRingCat.of K) ⟶ (KerN A n).left :=
  (MulRigidity.kerUnit A (mulN A n)).left

theorem ks_hom : ks A n ≫ (KerN A n).hom = 𝟙 _ :=
  Over.w (MulRigidity.kerUnit A (mulN A n))

theorem comp_mem_of_subsingleton {X : Scheme.{0}} {W : X.Opens}
    (s : Spec (CommRingCat.of K) ⟶ X) (hs : s (IsLocalRing.closedPoint K) ∈ W) {Λ : CommRingCat.{0}}
    (p : Spec Λ ⟶ Spec (CommRingCat.of K)) (x : Spec Λ) : (p ≫ s) x ∈ W := by
  show s (p x) ∈ W
  rw [Subsingleton.elim (p x) (IsLocalRing.closedPoint K)]
  exact hs

theorem exists_affine_orig :
    ∃ U : A.X.left.Opens, IsAffineOpen U ∧ orig A (IsLocalRing.closedPoint K) ∈ U := by
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, -⟩ := A.X.left.isBasis_affineOpens.exists_subset_of_mem_open
    (Set.mem_univ (orig A (IsLocalRing.closedPoint K))) isOpen_univ
  exact ⟨U, hU, hxU⟩

/-- **A derivation at the origin of `A[n]` vanishes** (characteristic `0`, `n ≠ 0`). -/
theorem derivation_eq_zero [CharZero K] (hn : n ≠ 0) {W : (KerN A n).left.Opens}
    (hW : IsAffineOpen W) (hz0 : ks A n (IsLocalRing.closedPoint K) ∈ W)
    (D : Γ((KerN A n).left, W) → K) (hadd : ∀ a b, D (a + b) = D a + D b)
    (hmul : ∀ a b, D (a * b) = (ptRing (Λ := CommRingCat.of K) (ks A n) hz0).hom a * D b +
      (ptRing (Λ := CommRingCat.of K) (ks A n) hz0).hom b * D a)
    (hκ : ∀ x, D ((KerN A n).hom.appLE ⊤ W le_top x) = 0) : ∀ t, D t = 0 := by
  obtain ⟨U, hU, ho⟩ := exists_affine_orig A
  set ev := ptRing (Λ := CommRingCat.of K) (ks A n) hz0 with hev
  set φ : Γ((KerN A n).left, W) ⟶ CommRingCat.of (TrivSqZeroExt K K) :=
    CommRingCat.ofHom (dualHom ev.hom D hadd hmul) with hφ
  set v := ofRing hW φ with hv
  have hvmem := ofRing_mem hW φ
  have hpv : ptRing v hvmem = φ := ptRing_ofRing hW φ
  have htop : ∀ (Λ : CommRingCat.{0}) [IsLocalRing Λ] (p : Spec Λ ⟶ Spec (CommRingCat.of K)),
      p (IsLocalRing.closedPoint Λ) ∈ (⊤ : (Spec (CommRingCat.of K)).Opens) :=
    fun _ _ _ => trivial
  -- the evaluation on sections coming from `K`
  have hevκ : ∀ x, ev.hom ((KerN A n).hom.appLE ⊤ W le_top x) =
      (ptRing (Λ := CommRingCat.of K) (𝟙 (Spec (CommRingCat.of K))) (htop _ _)).hom x := by
    intro x
    have h := ptRing_comp hW (KerN A n).hom (isAffineOpen_top _) le_top (ks A n) hz0
      (htop _ _)
    rw [ptRing_congr (ks_hom A n) _ (htop _ _)] at h
    rw [h]
    rfl
  -- `v` is a point over `K`
  have hvK : v ≫ (KerN A n).hom = Spec.map (CommRingCat.ofHom
      (algebraMap K (TrivSqZeroExt K K))) := by
    apply ptRing_ext (isAffineOpen_top _) (htop _ _) (htop _ _)
    rw [ptRing_comp hW (KerN A n).hom (isAffineOpen_top _) le_top v hvmem (htop _ _), hpv,
      ptRing_congr (Category.comp_id _).symm (htop _ _) (htop _ _),
      ptRing_specMap_comp (isAffineOpen_top _) _ _ (htop _ _)]
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro x
    rw [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_comp, RingHom.comp_apply, hφ,
      CommRingCat.hom_ofHom, CommRingCat.hom_ofHom]
    change inl (ev.hom _) + inr (D _) = _
    rw [hκ, inr_zero, add_zero, hevκ, algebraMap_eq_inl]
  let vt : ptR (K := K) (TrivSqZeroExt K K) ⟶ KerN A n := Over.homMk v hvK
  -- its reduction is the unit section
  have hfst : specHom (fstHom K K K) ≫ vt = toUnit _ ≫ MulRigidity.kerUnit A (mulN A n) := by
    apply Over.OverMorphism.ext
    change Spec.map _ ≫ v = Spec.map (CommRingCat.ofHom (algebraMap K K)) ≫ ks A n
    have m1 : (Spec.map (CommRingCat.ofHom ((fstHom K K K : TrivSqZeroExt K K →ₐ[K] K) :
        TrivSqZeroExt K K →+* K)) ≫ v) (IsLocalRing.closedPoint K) ∈ W := by
      show v (Spec.map (CommRingCat.ofHom ((fstHom K K K : TrivSqZeroExt K K →ₐ[K] K) :
        TrivSqZeroExt K K →+* K)) (IsLocalRing.closedPoint K)) ∈ W
      rw [closedPoint_eq]
      exact hvmem
    have m2 := comp_mem_of_subsingleton (ks A n) hz0
      (Spec.map (CommRingCat.ofHom (algebraMap K K))) (IsLocalRing.closedPoint K)
    apply ptRing_ext hW m1 m2
    rw [ptRing_specMap_comp hW _ _ hvmem, ptRing_specMap_comp hW _ _ hz0, hpv]
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro t
    rw [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_comp, RingHom.comp_apply, hφ,
      CommRingCat.hom_ofHom, CommRingCat.hom_ofHom, CommRingCat.hom_ofHom]
    change (inl (ev.hom t) + inr (D t) : TrivSqZeroExt K K).fst = algebraMap K K (ev.hom t)
    rw [fst_add, fst_inl, fst_inr, add_zero, Algebra.algebraMap_self, RingHom.id_apply]
  set u := vt ≫ pullback.fst (mulN A n) η[A.X] with hu
  have hu0 : AtOrigin A u := by
    unfold AtOrigin
    rw [hu, ← Category.assoc, hfst, Category.assoc, MulRigidity.kerUnit, pullback.lift_fst,
      Hom.one_def]
  have huf : u ≫ mulN A n = 1 := by
    rw [hu, Category.assoc, pullback.condition, ← Category.assoc, Hom.one_def]
    congr 1
    exact toUnit_unique _ _
  have hu1 : u = 1 := eq_one_of_comp_intCast A ho hU hu0 n hn huf
  have hvt : vt = toUnit _ ≫ MulRigidity.kerUnit A (mulN A n) := by
    apply pullback.hom_ext
    · rw [← hu, hu1, Category.assoc, MulRigidity.kerUnit, pullback.lift_fst, Hom.one_def]
    · exact toUnit_unique _ _
  have hvl : v = Spec.map (CommRingCat.ofHom (algebraMap K (TrivSqZeroExt K K))) ≫ ks A n :=
    congrArg (fun g => g.left) hvt
  have m3 := comp_mem_of_subsingleton (ks A n) hz0
    (Spec.map (CommRingCat.ofHom (algebraMap K (TrivSqZeroExt K K))))
    (IsLocalRing.closedPoint (TrivSqZeroExt K K))
  have key := (ptRing_congr hvl hvmem m3).trans (ptRing_specMap_comp hW _ _ hz0 m3)
  rw [hpv] at key
  intro t
  have := congrArg (fun g => (g.hom t).snd) key
  simp only [hφ, CommRingCat.hom_ofHom, CommRingCat.hom_comp, RingHom.comp_apply] at this
  change (inl (ev.hom t) + inr (D t) : TrivSqZeroExt K K).snd = _ at this
  rw [snd_add, snd_inl, snd_inr, zero_add, algebraMap_eq_inl, snd_inl] at this
  exact this

end KerDer

/-! ## §2. Commutative algebra: no derivations means `P = P²` -/

section Alg

variable {K : Type} [Field K]

/-- If every `K`-derivation `T → K` at `ev` vanishes, the kernel `P` of `ev` satisfies `P ≤ P²`
(a functional on `P / P²` is a derivation). -/
theorem ker_le_sq_of_derivations {T : Type} [CommRing T] (ev : T →+* K) (jK : K →+* T)
    (hevj : ∀ c, ev (jK c) = c)
    (hD : ∀ D : T → K, (∀ a b, D (a + b) = D a + D b) →
      (∀ a b, D (a * b) = ev a * D b + ev b * D a) → (∀ c, D (jK c) = 0) → ∀ t, D t = 0) :
    RingHom.ker ev ≤ (RingHom.ker ev) ^ 2 := by
  intro a ha
  by_contra hna
  letI : Algebra K T := jK.toAlgebra
  have hsmul : ∀ (c : K) (t : T), c • t = jK c * t := fun c t => Algebra.smul_def c t
  set P := RingHom.ker ev with hP
  let P' : Submodule K T := P.restrictScalars K
  let N : Submodule K P' := ((P ^ 2).restrictScalars K).comap P'.subtype
  have hmem : ∀ t, t - jK (ev t) ∈ P' := fun t => by
    change t - jK (ev t) ∈ RingHom.ker ev
    rw [RingHom.mem_ker, map_sub, hevj, sub_self]
  let q : T → P' ⧸ N := fun t => N.mkQ ⟨t - jK (ev t), hmem t⟩
  have hqa : q a ≠ 0 := by
    intro h
    change N.mkQ ⟨a - jK (ev a), hmem a⟩ = 0 at h
    rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at h
    apply hna
    have h' : a - jK (ev a) ∈ P ^ 2 := h
    rwa [RingHom.mem_ker.mp ha, map_zero, sub_zero] at h'
  obtain ⟨l, hl⟩ : ∃ l : Module.Dual K (P' ⧸ N), l (q a) ≠ 0 := by
    by_contra h
    push Not at h
    exact hqa ((Module.forall_dual_apply_eq_zero_iff K _).mp h)
  have hadd : ∀ x y, l (q (x + y)) = l (q x) + l (q y) := by
    intro x y
    rw [← map_add]
    congr 1
    change N.mkQ _ = N.mkQ _ + N.mkQ _
    rw [← map_add]
    congr 1
    apply Subtype.ext
    simp only [Submodule.coe_add, map_add]
    ring
  have hmul : ∀ x y, l (q (x * y)) = ev x * l (q y) + ev y * l (q x) := by
    intro x y
    suffices hq : q (x * y) = ev x • q y + ev y • q x by
      rw [hq, map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul]
    change N.mkQ _ = ev x • N.mkQ _ + ev y • N.mkQ _
    rw [← map_smul, ← map_smul, ← map_add, Submodule.mkQ_apply, Submodule.mkQ_apply,
      Submodule.Quotient.eq]
    change ((⟨x * y - jK (ev (x * y)), hmem _⟩ : P') -
      (ev x • ⟨y - jK (ev y), hmem y⟩ + ev y • ⟨x - jK (ev x), hmem x⟩) : P').1 ∈ P ^ 2
    have e1 : ((⟨x * y - jK (ev (x * y)), hmem _⟩ : P') -
        (ev x • ⟨y - jK (ev y), hmem y⟩ + ev y • ⟨x - jK (ev x), hmem x⟩) : P').1 =
        (x - jK (ev x)) * (y - jK (ev y)) := by
      simp only [Submodule.coe_sub, Submodule.coe_add, Submodule.coe_smul, hsmul, map_mul]
      ring
    rw [e1, pow_two]
    exact Ideal.mul_mem_mul (hmem x) (hmem y)
  have hj : ∀ c, l (q (jK c)) = 0 := by
    intro c
    have : q (jK c) = 0 := by
      change N.mkQ _ = 0
      have : (⟨jK c - jK (ev (jK c)), hmem _⟩ : P') = 0 := by
        apply Subtype.ext
        simp [hevj]
      rw [this, map_zero]
    rw [this, map_zero]
  exact hl (hD (fun t => l (q t)) hadd hmul hj a)

end Alg

/-! ## §3. The unit section of `A[n]` is an open immersion -/

section Final

variable {K : Type} [Field K] (A : PkgI3.AbVar K) (n : ℤ)

theorem locallyOfFiniteType_kerN : LocallyOfFiniteType (KerN A n).hom := by
  have h1 : LocallyOfFiniteType (mulN A n).left := by
    have : LocallyOfFiniteType ((mulN A n).left ≫ A.X.hom) := by
      rw [Over.w]; infer_instance
    exact locallyOfFiniteType_of_comp _ A.X.hom
  have hP := (Over.forget _).map_isPullback (IsPullback.of_hasPullback (mulN A n) η[A.X])
  have h2 : LocallyOfFiniteType (pullback.snd (mulN A n) η[A.X]).left :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback (P := @LocallyOfFiniteType) hP h1
  have h3 : (pullback.snd (mulN A n) η[A.X]).left ≫
      (𝟙_ (Over (Spec (CommRingCat.of K)))).hom = (KerN A n).hom := Over.w _
  rw [← h3]
  change LocallyOfFiniteType (_ ≫ 𝟙 _)
  rw [Category.comp_id]
  exact h2

theorem id_appLE_top (h : (⊤ : (Spec (CommRingCat.of K)).Opens) ≤
    (𝟙 (Spec (CommRingCat.of K))) ⁻¹ᵁ ⊤) :
    Scheme.Hom.appLE (𝟙 (Spec (CommRingCat.of K))) ⊤ ⊤ h = 𝟙 _ := by
  simp only [Scheme.Hom.appLE, Scheme.Hom.id_app]
  erw [Category.id_comp]
  exact (Spec (CommRingCat.of K)).presheaf.map_id (Opposite.op ⊤)

theorem ptRing_id_top :
    ptRing (Λ := CommRingCat.of K) (𝟙 (Spec (CommRingCat.of K)))
      (show _ ∈ (⊤ : (Spec (CommRingCat.of K)).Opens) from trivial) =
      (Scheme.ΓSpecIso (CommRingCat.of K)).hom := by
  unfold ptRing
  rw [id_appLE_top, Category.id_comp]

/-- **mul-rigidity's leaf `KerUnitOpen`, proved**: in characteristic `0`, for `n ≠ 0`, the unit
section of `A[n]` is an open immersion. -/
theorem ks_isOpenImmersion [CharZero K] (hn : n ≠ 0) : IsOpenImmersion (ks A n) := by
  set Z := (KerN A n).left with hZ
  obtain ⟨_, ⟨W, hW, rfl⟩, hz0, -⟩ := Z.isBasis_affineOpens.exists_subset_of_mem_open
    (Set.mem_univ (ks A n (IsLocalRing.closedPoint K))) isOpen_univ
  haveI := locallyOfFiniteType_kerN A n
  haveI : IsLocallyNoetherian Z := LocallyOfFiniteType.isLocallyNoetherian (KerN A n).hom
  haveI : IsNoetherianRing Γ(Z, W) := IsLocallyNoetherian.component_noetherian ⟨W, hW⟩
  set ev := ptRing (Λ := CommRingCat.of K) (ks A n) hz0 with hev
  set κ := (KerN A n).hom.appLE ⊤ W le_top with hκ
  let jK : K →+* Γ(Z, W) := κ.hom.comp (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom
  have htop : ∀ (Λ : CommRingCat.{0}) [IsLocalRing Λ] (p : Spec Λ ⟶ Spec (CommRingCat.of K)),
      p (IsLocalRing.closedPoint Λ) ∈ (⊤ : (Spec (CommRingCat.of K)).Opens) :=
    fun _ _ _ => trivial
  have hevκ : ∀ x, ev.hom (κ.hom x) = (Scheme.ΓSpecIso (CommRingCat.of K)).hom.hom x := by
    intro x
    have h := ptRing_comp hW (KerN A n).hom (isAffineOpen_top _) le_top (ks A n) hz0
      (htop _ _)
    rw [ptRing_congr (ks_hom A n) _ (htop _ _), ptRing_id_top] at h
    rw [h]
    rfl
  let eK := (Scheme.ΓSpecIso (CommRingCat.of K)).commRingCatIsoToRingEquiv
  have hevj : ∀ c, ev.hom (jK c) = c := by
    intro c
    change ev.hom (κ.hom (eK.symm c)) = c
    rw [hevκ]
    exact eK.apply_symm_apply c
  have hκj : ∀ x, κ.hom x = jK ((Scheme.ΓSpecIso (CommRingCat.of K)).hom.hom x) := by
    intro x
    change κ.hom x = κ.hom (eK.symm (eK x))
    rw [RingEquiv.symm_apply_apply]
  have hPP := ker_le_sq_of_derivations ev.hom jK hevj (fun D hadd hmul hj =>
    derivation_eq_zero A n hn hW hz0 D hadd hmul (fun x => by rw [hκj]; exact hj _))
  have hidem : IsIdempotentElem (RingHom.ker ev.hom) := by
    unfold IsIdempotentElem
    rw [← pow_two]
    exact le_antisymm (Ideal.pow_le_self two_ne_zero) hPP
  obtain ⟨e, he, hPe⟩ :=
    (Ideal.isIdempotentElem_iff_of_fg _ (IsNoetherian.noetherian _)).mp hidem
  have heP : e ∈ RingHom.ker ev.hom := by
    rw [hPe]; exact Submodule.mem_span_singleton_self e
  set g : Γ(Z, W) := 1 - e with hg
  have hevg : ev.hom g = 1 := by
    rw [hg, map_sub, map_one, RingHom.mem_ker.mp heP, sub_zero]
  -- the origin lies in `D(g)`
  have hle : (⊤ : (Spec (CommRingCat.of K)).Opens) ≤ ks A n ⁻¹ᵁ W :=
    (Scheme.preimage_eq_top_of_closedPoint_mem (ks A n) hz0).ge
  have hz0' : ks A n (IsLocalRing.closedPoint K) ∈ Z.basicOpen g := by
    have hb := Scheme.basicOpen_appLE (ks A n) ⊤ W hle g
    have hu : IsUnit ((ks A n).appLE W ⊤ hle g) := by
      have h1 : eK ((ks A n).appLE W ⊤ hle g) = 1 := hevg
      have : (ks A n).appLE W ⊤ hle g = 1 := by
        rw [← eK.symm_apply_apply ((ks A n).appLE W ⊤ hle g), h1, map_one]
      rw [this]
      exact isUnit_one
    rw [Scheme.basicOpen_of_isUnit _ hu] at hb
    have hmem : IsLocalRing.closedPoint K ∈ (⊤ : (Spec (CommRingCat.of K)).Opens) := trivial
    rw [hb] at hmem
    exact hmem.2
  set W' := Z.basicOpen g with hW'def
  have hW' : IsAffineOpen W' := hW.basicOpen g
  haveI hloc := hW.isLocalization_basicOpen g
  have hge : algebraMap Γ(Z, W) Γ(Z, W') g * algebraMap Γ(Z, W) Γ(Z, W') e = 0 := by
    have hge0 : g * e = 0 := by
      change (1 - e) * e = 0
      rw [sub_mul, _root_.one_mul, he.eq, sub_self]
    rw [← map_mul, hge0, map_zero]
  have hgu : IsUnit (algebraMap Γ(Z, W) Γ(Z, W') g) := IsLocalization.Away.algebraMap_isUnit g
  have hre : algebraMap Γ(Z, W) Γ(Z, W') e = 0 := hgu.mul_right_eq_zero.mp hge
  have hrg : algebraMap Γ(Z, W) Γ(Z, W') g = 1 := by
    have h := map_sub (algebraMap Γ(Z, W) Γ(Z, W')) 1 e
    rw [map_one, hre, sub_zero] at h
    exact h
  have hrP : ∀ t ∈ RingHom.ker ev.hom, algebraMap Γ(Z, W) Γ(Z, W') t = 0 := by
    intro t ht
    rw [hPe] at ht
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp ht
    rw [smul_eq_mul, map_mul, hre, MulZeroClass.mul_zero]
  set κ' := (KerN A n).hom.appLE ⊤ W' le_top with hκ'def
  have hκ' : κ' = κ ≫ Z.presheaf.map (homOfLE (Z.basicOpen_le g)).op := by
    rw [hκ'def, hκ]
    exact (Scheme.Hom.appLE_map (KerN A n).hom le_top (homOfLE (Z.basicOpen_le g)).op).symm
  have hsurj : Function.Surjective ((Scheme.ΓSpecIso (CommRingCat.of K)).inv ≫ κ').hom := by
    intro y
    obtain ⟨⟨t, s⟩, rfl⟩ := IsLocalization.mk'_surjective (Submonoid.powers g) y
    obtain ⟨k, hk⟩ := s.2
    refine ⟨ev.hom t, ?_⟩
    have hs1 : algebraMap Γ(Z, W) Γ(Z, W') (s : Γ(Z, W)) = 1 := by
      rw [← hk, map_pow, hrg, one_pow]
    rw [eq_comm, IsLocalization.mk'_eq_iff_eq_mul, hs1, _root_.mul_one]
    have hmem : t - jK (ev.hom t) ∈ RingHom.ker ev.hom := by
      rw [RingHom.mem_ker, map_sub, hevj, sub_self]
    have h0 := hrP _ hmem
    rw [map_sub, sub_eq_zero] at h0
    rw [h0, hκ']
    rfl
  let i := hW'.fromSpec
  have hrange : Set.range (ks A n) ⊆ Set.range i := by
    rw [hW'.range_fromSpec]
    rintro _ ⟨x, rfl⟩
    rw [Subsingleton.elim x (IsLocalRing.closedPoint K)]
    exact hz0'
  let s' := IsOpenImmersion.lift i (ks A n) hrange
  have hs' : s' ≫ i = ks A n := IsOpenImmersion.lift_fac _ _ _
  have hiK : i ≫ (KerN A n).hom =
      Spec.map ((Scheme.ΓSpecIso (CommRingCat.of K)).inv ≫ κ') := by
    have h := IsAffineOpen.SpecMap_appLE_fromSpec (KerN A n).hom (isAffineOpen_top _) hW' le_top
    rw [IsAffineOpen.fromSpec_top, Scheme.isoSpec_Spec_inv] at h
    rw [Spec.map_comp]
    exact h.symm
  haveI : FormallyUnramified (i ≫ (KerN A n).hom) := by
    rw [hiK, HasRingHomProperty.Spec_iff (P := @FormallyUnramified)]
    exact RingHom.FormallyUnramified.of_surjective hsurj
  have hsec : s' ≫ (i ≫ (KerN A n).hom) = 𝟙 _ := by
    rw [← Category.assoc, hs', ks_hom]
  haveI := MulRigidity.isOpenImmersion_of_section s' (i ≫ (KerN A n).hom) hsec
  rw [← hs']
  infer_instance

end Final

end ZInQ.Contrib.AbVarBC.Tangent

end

end LF2_AbVarBC_KerUnit

-- ===== ZInQKernel/Contrib/AbVarBC/G9Instance.lean
section LF2_AbVarBC_G9Instance

/-!
# Base change of abelian varieties, IV: the instance `G9Bridge.AbVarBaseChange`

Copyright: this file is part of the fork Deicyde/diophantine-z-q (task g9-abvarbc, 2026-11-13).

`G9Bridge.AbVarBaseChange` (task g9-derham, `ZInQKernel/Contrib/G9/LocalModel.lean`) is stated over
two verbatim copies of the kernel's abelian varieties: `_root_.HDec.PkgI3.AbVar`
(`Contrib/G9/I3Layer.lean`) and `_root_.HDec.PkgI4.I3.AbVar` (`Contrib/G9/I4Layer.lean`).
§1 transports between the copies and the kernel's `PkgI3.AbVar` (all identities are `rfl`);
§2 derives the instance from the general lemmas of `Contrib/AbVarBC/{Dim,Points,Tate}.lean`.

* `abVarBaseChange_of_torsionDescends`: from descent of `ℓ`-power torsion points;
* `abVarBaseChange_of_tateModuleFree`: from leaf T26 `PkgI3.TateModuleFree` (I3.M0);
* `g9Glue_of_tateModuleFree`: `TateModuleFree → R10Weights → G9Glue`.
-/

open CategoryTheory AlgebraicGeometry Limits

set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false

namespace ZInQ.Contrib.AbVarBC

/-! ## §1. Transport between the copies -/

section Transport

variable {K : Type} [Field K]

/-- G9's copy of pkg-I3's abelian variety, as a kernel `PkgI3.AbVar`. -/
def ofG9 (A : _root_.HDec.PkgI3.AbVar K) : _root_.HDec.PkgI3.AbVar K :=
  @_root_.HDec.PkgI3.AbVar.mk K _ A.X A.grp A.proper A.smooth A.geomInt

/-- A kernel `PkgI3.AbVar`, as pkg-I4's copy `PkgI4.I3.AbVar` (in G9's namespace). -/
def toI4 (A : _root_.HDec.PkgI3.AbVar K) : _root_.HDec.PkgI4.I3.AbVar K :=
  @_root_.HDec.PkgI4.I3.AbVar.mk K _ A.X A.grp A.proper A.smooth A.geomInt

theorem dim_ofG9 (A : _root_.HDec.PkgI3.AbVar K) : (ofG9 A).dim = A.dim := rfl

theorem dim_toI4 (A : _root_.HDec.PkgI3.AbVar K) : (toI4 A).dim = A.dim := rfl

variable (ℓ : ℕ) [Fact ℓ.Prime]

/-- `V_ℓ` of G9's copy is `V_ℓ` of the kernel's object (identity map). -/
noncomputable def vOfG9 (A : _root_.HDec.PkgI3.AbVar K) : A.V ℓ ≃ₗ[ℚ_[ℓ]] (ofG9 A).V ℓ :=
  LinearEquiv.refl ℚ_[ℓ] (A.V ℓ)

theorem vOfG9_galRep (A : _root_.HDec.PkgI3.AbVar K) (σ : Field.absoluteGaloisGroup K)
    (v : A.V ℓ) : vOfG9 ℓ A (A.galRep ℓ σ v) = (ofG9 A).galRep ℓ σ (vOfG9 ℓ A v) := rfl

theorem vOfG9_symm_galRep (A : _root_.HDec.PkgI3.AbVar K) (σ : Field.absoluteGaloisGroup K)
    (v : (ofG9 A).V ℓ) :
    (vOfG9 ℓ A).symm ((ofG9 A).galRep ℓ σ v) = A.galRep ℓ σ ((vOfG9 ℓ A).symm v) := rfl

/-- `V_ℓ` of pkg-I4's copy is `V_ℓ` of the kernel's object (identity map). -/
noncomputable def vToI4 (A : _root_.HDec.PkgI3.AbVar K) : (toI4 A).V ℓ ≃ₗ[ℚ_[ℓ]] A.V ℓ :=
  LinearEquiv.refl ℚ_[ℓ] (A.V ℓ)

theorem vToI4_galRep (A : _root_.HDec.PkgI3.AbVar K) (σ : Field.absoluteGaloisGroup K)
    (v : (toI4 A).V ℓ) : vToI4 ℓ A ((toI4 A).galRep ℓ σ v) = A.galRep ℓ σ (vToI4 ℓ A v) := rfl

end Transport

/-! ## §2. The instance -/

/-- `Field.absoluteGaloisGroup.map i` is restriction along the `K`-embedding `K̄ → L̄` it is
built from (`IsAlgClosed.lift`). -/
theorem map_comm {K L : Type} [Field K] [Field L] (i : K →+* L) :
    letI : Algebra K L := i.toAlgebra
    ∀ (σ : Field.absoluteGaloisGroup L) (x : AlgebraicClosure K),
      (IsAlgClosed.lift : AlgebraicClosure K →ₐ[K] AlgebraicClosure L)
          (galK (Field.absoluteGaloisGroup.map i σ) x) =
        galK σ ((IsAlgClosed.lift : AlgebraicClosure K →ₐ[K] AlgebraicClosure L) x) := by
  letI : Algebra K L := i.toAlgebra
  let g0 : AlgebraicClosure K →ₐ[K] AlgebraicClosure L := IsAlgClosed.lift
  letI : Algebra (AlgebraicClosure K) (AlgebraicClosure L) := g0.toAlgebra
  exact fun σ x =>
    AlgEquiv.restrictNormal_commutes (AlgEquiv.restrictScalars K σ) (AlgebraicClosure K) x

/-- **`AbVarBaseChange` from descent of `ℓ`-power torsion points.** The hypothesis is the
statement "every `ℓ`-power torsion point of `A_L(L̄)` comes from `A(K̄)`" for the kernel's
objects and the embedding `K̄ → L̄` of `Field.absoluteGaloisGroup.map`. -/
theorem abVarBaseChange_of_torsionDescends
    (hD : ∀ (K : Type) [Field K] [CharZero K] (A : _root_.HDec.PkgI3.AbVar K) (L : Type) [Field L]
      (i : K →+* L) (ℓ : ℕ) [Fact ℓ.Prime],
      letI : Algebra K L := i.toAlgebra
      TorsionDescends A (IsAlgClosed.lift : AlgebraicClosure K →ₐ[K] AlgebraicClosure L) ℓ) :
    ZInQ.Contrib.G9.G9Bridge.AbVarBaseChange := by
  intro K _ _ A L _ i ℓ _
  letI : Algebra K L := i.toAlgebra
  let κ : AlgebraicClosure K →ₐ[K] AlgebraicClosure L := IsAlgClosed.lift
  have hb := tateBC_bijective_of_torsionDescends (ofG9 A) κ ℓ (hD K (ofG9 A) L i ℓ)
  refine ⟨toI4 ((ofG9 A).baseChange L),
    (vToI4 ℓ _).trans ((vBC (ofG9 A) κ ℓ hb).trans (vOfG9 ℓ A).symm), ?_, ?_⟩
  · exact (dim_toI4 _).trans (((ofG9 A).dim_baseChange L).trans (dim_ofG9 A))
  · intro σ v
    simp only [LinearEquiv.trans_apply]
    rw [vToI4_galRep, vBC_galRep (ofG9 A) κ ℓ hb (Field.absoluteGaloisGroup.map i σ) σ
      (map_comm i σ)]
    exact vOfG9_symm_galRep ℓ A _ _

/-- **`AbVarBaseChange` from leaf T26 (`PkgI3.TateModuleFree`, Mumford §§4, 18-19).** -/
theorem abVarBaseChange_of_tateModuleFree (hT : _root_.HDec.PkgI3.TateModuleFree) :
    ZInQ.Contrib.G9.G9Bridge.AbVarBaseChange := by
  intro K _ _ A L _ i ℓ hℓ
  letI : Algebra K L := i.toAlgebra
  let κ : AlgebraicClosure K →ₐ[K] AlgebraicClosure L := IsAlgClosed.lift
  have hb := tateBC_bijective_of_tateModuleFree (ofG9 A) κ ℓ hT
    (Nat.cast_ne_zero.mpr hℓ.out.ne_zero)
  refine ⟨toI4 ((ofG9 A).baseChange L),
    (vToI4 ℓ _).trans ((vBC (ofG9 A) κ ℓ hb).trans (vOfG9 ℓ A).symm), ?_, ?_⟩
  · exact (dim_toI4 _).trans (((ofG9 A).dim_baseChange L).trans (dim_ofG9 A))
  · intro σ v
    simp only [LinearEquiv.trans_apply]
    rw [vToI4_galRep, vBC_galRep (ofG9 A) κ ℓ hb (Field.absoluteGaloisGroup.map i σ) σ
      (map_comm i σ)]
    exact vOfG9_symm_galRep ℓ A _ _

/-- **G9 from T26 and the weight clause**: `TateModuleFree → R10Weights → G9Glue`. -/
theorem g9Glue_of_tateModuleFree (hT : _root_.HDec.PkgI3.TateModuleFree)
    (hW : ZInQ.Contrib.G9.G9Bridge.R10Weights) : _root_.HDec.G0Galois.G9Glue :=
  ZInQ.Contrib.G9.g9Glue_of_abVarBaseChange (abVarBaseChange_of_tateModuleFree hT) hW

end ZInQ.Contrib.AbVarBC

end LF2_AbVarBC_G9Instance

-- ===== ZInQKernel/Contrib/AbVarBC/G9Mul.lean
section LF2_AbVarBC_G9Mul

/-!
# Base change of abelian varieties, VI: `AbVarBaseChange` from finiteness of `[n]`

Copyright: this file is part of the fork Deicyde/diophantine-z-q (task g9-abvarbc, 2026-11-13).

The `V_ℓ` clause of `G9Bridge.AbVarBaseChange` needs exactly the descent of `ℓ`-power torsion
points (`TorsionDescends`), which follows from finiteness of `[ℓⁿ]`
(`torsionDescends_of_isFinite`). Finiteness of `[n]` is mul-rigidity's `MulIsogeny`
(Mumford §4; Milne Thm 8.2), which mul-rigidity reduced to the single point statement
`KerUnitOpen` and further to two cotangent-space glue statements. Hence:

* `abVarBaseChangeK_of_mulIsogeny`: the kernel-level statement `AbVarBaseChangeK`;
* `abVarBaseChange_of_mulIsogeny`, `…_of_kerUnitOpen`, `…_of_mulEtale`, `…_of_cotangent`;
* `g9Glue_of_kerUnitOpen`, `g9Glue_of_cotangent`.
-/

open CategoryTheory AlgebraicGeometry Limits

set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false

namespace ZInQ.Contrib.AbVarBC

/-- **The statement of `G9Bridge.AbVarBaseChange` over the kernel's `PkgI3.AbVar`**, with the
witness pinned to `A.baseChange L`. -/
def AbVarBaseChangeK : Prop :=
  ∀ (K : Type) [Field K] [CharZero K] (A : _root_.HDec.PkgI3.AbVar K) (L : Type) [Field L]
    (i : K →+* L) (ℓ : ℕ) [Fact ℓ.Prime],
    letI : Algebra K L := i.toAlgebra
    (A.baseChange L).dim = A.dim ∧
      ∃ c : (A.baseChange L).V ℓ ≃ₗ[ℚ_[ℓ]] A.V ℓ,
        ∀ σ v, c ((A.baseChange L).galRep ℓ σ v) =
          A.galRep ℓ (Field.absoluteGaloisGroup.map i σ) (c v)

/-- `AbVarBaseChangeK` from torsion descent. -/
theorem abVarBaseChangeK_of_torsionDescends
    (hD : ∀ (K : Type) [Field K] [CharZero K] (A : _root_.HDec.PkgI3.AbVar K) (L : Type) [Field L]
      (i : K →+* L) (ℓ : ℕ) [Fact ℓ.Prime],
      letI : Algebra K L := i.toAlgebra
      TorsionDescends A (IsAlgClosed.lift : AlgebraicClosure K →ₐ[K] AlgebraicClosure L) ℓ) :
    AbVarBaseChangeK := by
  intro K _ _ A L _ i ℓ _
  letI : Algebra K L := i.toAlgebra
  let κ : AlgebraicClosure K →ₐ[K] AlgebraicClosure L := IsAlgClosed.lift
  have hb := tateBC_bijective_of_torsionDescends A κ ℓ (hD K A L i ℓ)
  exact ⟨A.dim_baseChange L, vBC A κ ℓ hb, fun σ v =>
    vBC_galRep A κ ℓ hb (Field.absoluteGaloisGroup.map i σ) σ (map_comm i σ) v⟩

/-- `MulIsogeny` gives torsion descent. -/
theorem torsionDescends_of_mulIsogeny (h : G0FibreSimple.MulIsogeny) {K : Type} [Field K]
    [CharZero K] (A : _root_.HDec.PkgI3.AbVar K) {L : Type} [Field L] [Algebra K L]
    (κ : AlgebraicClosure K →ₐ[K] AlgebraicClosure L) (ℓ : ℕ) [hℓ : Fact ℓ.Prime] :
    TorsionDescends A κ ℓ :=
  torsionDescends_of_isFinite A κ ℓ fun n =>
    (h K A _ (by exact_mod_cast (pow_pos hℓ.out.pos n).ne')).1

/-- **`AbVarBaseChangeK` from `MulIsogeny`.** -/
theorem abVarBaseChangeK_of_mulIsogeny (h : G0FibreSimple.MulIsogeny) : AbVarBaseChangeK :=
  abVarBaseChangeK_of_torsionDescends fun K _ _ A L _ i ℓ _ => by
    letI : Algebra K L := i.toAlgebra
    exact torsionDescends_of_mulIsogeny h A _ ℓ

/-- **`AbVarBaseChange` from `MulIsogeny`** (`[n]` finite and surjective in characteristic 0). -/
theorem abVarBaseChange_of_mulIsogeny (h : G0FibreSimple.MulIsogeny) :
    ZInQ.Contrib.G9.G9Bridge.AbVarBaseChange :=
  abVarBaseChange_of_torsionDescends fun K _ _ A L _ i ℓ _ => by
    letI : Algebra K L := i.toAlgebra
    exact torsionDescends_of_mulIsogeny h A _ ℓ

/-- **`AbVarBaseChange` from the point statement `KerUnitOpen`** (the unit section of `A[n]` is an
open immersion, char 0, `n ≠ 0`; a consequence of the published `MulEtale`). -/
theorem abVarBaseChange_of_kerUnitOpen (h : MulRigidity.KerUnitOpen) :
    ZInQ.Contrib.G9.G9Bridge.AbVarBaseChange :=
  abVarBaseChange_of_mulIsogeny (MulRigidity.mulIsogeny_of_kerUnitOpen h)

/-- **`AbVarBaseChange` from `MulEtale`** (Mumford §4 Appl. 2, Milne Thm 8.2; char 0). -/
theorem abVarBaseChange_of_mulEtale (h : MulRigidity.MulEtale) :
    ZInQ.Contrib.G9.G9Bridge.AbVarBaseChange :=
  abVarBaseChange_of_mulIsogeny (MulRigidity.mulIsogeny_of_mulEtale h)

/-- **`AbVarBaseChange` from the two cotangent-space glue statements** (no literature leaf). -/
theorem abVarBaseChange_of_cotangent (h1 : MulRigidity.KerUnitOpenOfCotangentSurj)
    (h2 : MulRigidity.CotangentMulN) : ZInQ.Contrib.G9.G9Bridge.AbVarBaseChange :=
  abVarBaseChange_of_mulIsogeny (MulRigidity.mulIsogeny_of_cotangent h1 h2)

/-- `G9Glue` from `KerUnitOpen` and the weight clause. -/
theorem g9Glue_of_kerUnitOpen (h : MulRigidity.KerUnitOpen)
    (hW : ZInQ.Contrib.G9.G9Bridge.R10Weights) : _root_.HDec.G0Galois.G9Glue :=
  ZInQ.Contrib.G9.g9Glue_of_abVarBaseChange (abVarBaseChange_of_kerUnitOpen h) hW

/-- `G9Glue` from the two cotangent glue statements and the weight clause. -/
theorem g9Glue_of_cotangent (h1 : MulRigidity.KerUnitOpenOfCotangentSurj)
    (h2 : MulRigidity.CotangentMulN) (hW : ZInQ.Contrib.G9.G9Bridge.R10Weights) :
    _root_.HDec.G0Galois.G9Glue :=
  ZInQ.Contrib.G9.g9Glue_of_abVarBaseChange (abVarBaseChange_of_cotangent h1 h2) hW

end ZInQ.Contrib.AbVarBC

end LF2_AbVarBC_G9Mul

-- ===== ZInQKernel/Contrib/AbVarBC/Main.lean
section LF2_AbVarBC_Main

/-!
# Base change of abelian varieties: main results

Copyright: this file is part of the fork Deicyde/diophantine-z-q (task g9-abvarbc, 2026-11-13).

All statements below are proved from Mathlib alone (no leaf, no hypothesis):
* `kerUnitOpen : MulRigidity.KerUnitOpen` (mul-rigidity's leaf: the unit section of `A[n]` is an
  open immersion in characteristic `0`, `n ≠ 0`), from `Tangent.ks_isOpenImmersion`;
* `mulIsogeny : G0FibreSimple.MulIsogeny` (`[n]` is finite and surjective in characteristic `0`);
* `torsionDescends`, `tateBC_bijective`: `T_ℓ(A) ≅ T_ℓ(A_L)` Galois-equivariantly;
* `abVarBaseChangeK : AbVarBaseChangeK` (the kernel-level statement);
* **`abVarBaseChange : ZInQ.Contrib.G9.G9Bridge.AbVarBaseChange`** (task g9-derham's bridge);
* `g9Glue_of_r10Weights : G9Bridge.R10Weights → G0Galois.G9Glue`.
-/

namespace ZInQ.Contrib.AbVarBC

/-- **mul-rigidity's leaf `KerUnitOpen`, proved.** -/
theorem kerUnitOpen : MulRigidity.KerUnitOpen := by
  intro k _ _ A n hn
  exact Tangent.ks_isOpenImmersion A n hn

/-- **`MulIsogeny`, proved**: in characteristic `0`, `[n]` is finite and surjective for `n ≠ 0`. -/
theorem mulIsogeny : G0FibreSimple.MulIsogeny :=
  MulRigidity.mulIsogeny_of_kerUnitOpen kerUnitOpen

/-- `ℓ`-power torsion points of `A_L(L̄)` come from `A(K̄)` (characteristic `0`). -/
theorem torsionDescends {K : Type} [Field K] [CharZero K] (A : _root_.HDec.PkgI3.AbVar K) {L : Type}
    [Field L] [Algebra K L] (κ : AlgebraicClosure K →ₐ[K] AlgebraicClosure L) (ℓ : ℕ)
    [Fact ℓ.Prime] : TorsionDescends A κ ℓ :=
  torsionDescends_of_mulIsogeny mulIsogeny A κ ℓ

/-- **`T_ℓ(A) → T_ℓ(A_L)` is bijective** (characteristic `0`). -/
theorem tateBC_bijective {K : Type} [Field K] [CharZero K] (A : _root_.HDec.PkgI3.AbVar K) {L : Type}
    [Field L] [Algebra K L] (κ : AlgebraicClosure K →ₐ[K] AlgebraicClosure L) (ℓ : ℕ)
    [Fact ℓ.Prime] : Function.Bijective (tateBC A κ ℓ) :=
  tateBC_bijective_of_torsionDescends A κ ℓ (torsionDescends A κ ℓ)

/-- **Base change of abelian varieties, kernel form, proved.** -/
theorem abVarBaseChangeK : AbVarBaseChangeK :=
  abVarBaseChangeK_of_mulIsogeny mulIsogeny

/-- **`G9Bridge.AbVarBaseChange`, proved** (no hypothesis). -/
theorem abVarBaseChange : ZInQ.Contrib.G9.G9Bridge.AbVarBaseChange :=
  abVarBaseChange_of_mulIsogeny mulIsogeny

/-- **G9 from the weight clause alone**: `R10Weights → G9Glue`. -/
theorem g9Glue_of_r10Weights (hW : ZInQ.Contrib.G9.G9Bridge.R10Weights) :
    _root_.HDec.G0Galois.G9Glue :=
  ZInQ.Contrib.G9.g9Glue_of_abVarBaseChange abVarBaseChange hW

end ZInQ.Contrib.AbVarBC

end LF2_AbVarBC_Main

end G0A2_b10_abvarbc

section G0A2_b20_fold
/-! ## leaf-fold2: the results proved since leaf-fold, folded into the statement of what remains open

Task leaf-fold2, 2026-11-13. Everything above this part is `scratch/h-decomposition/Leaves.lean`
(with the ten unused `TextbookLeaves` fields deleted, see `mk_prefix.py`), g0-assemble2's 41 parts
(`GluePieces3`, `ResearchLeaves3`, `sixContactMin_of_leaves3`) and g9-abvarbc's
`ZInQKernel/Contrib/AbVarBC` (part b10, copied over this file's objects). The kernel theorems used
below are imported (`ZInQKernel.Contrib.T14.Main`, `ZInQKernel.Contrib.T28.Assemble`,
`ZInQKernel.Contrib.RLeaf.X1ConstantField`, which imports T36 and T37) and image-plane's
`scratch/image-plane/ImagePlaneFinal.lean` (module `LF2ImagePlane`, verbatim). Each closed field
is a theorem `HSyn.xxx_proved` whose type is this file's own Prop and whose proof is the imported
or copied theorem: Lean checks that the two statements agree (definitional unfolding; for the
statements over `ToP1`, a structure of which the kernel has its own copy, through the explicit
field-by-field map `toP1K`). -/

noncomputable section

namespace HSyn

open CategoryTheory AlgebraicGeometry G0Split

/-! ### Textbook leaves closed since leaf-fold -/

/-- **T14(a′) proved** (task t1415-tc / `ZInQKernel/Contrib/T14/Main.lean`). -/
theorem t14a_proved : PkgI6.BrauerHasse2C := _root_.ZInQ.Contrib.T14.brauerHasse2C

/-- **T14(b′) proved** (`ZInQKernel/Contrib/T14/Main.lean`). -/
theorem t14b_proved : PkgI6.BrauerReciprocity2C := _root_.ZInQ.Contrib.T14.brauerReciprocity2C

/-- **T28 proved** (`ZInQKernel/Contrib/T28/Assemble.lean`). T28 is not used by the proof (its
field was deleted from `TextbookLeaves`, see `mk_prefix.py`); recorded for completeness. -/
theorem t28_proved : PkgI1.IgusaClebschSeparation :=
  _root_.T28.igusaClebschSeparation_proved

/-- **T36 proved** (`ZInQKernel/Contrib/RLeaf/T36Torsion.lean`). -/
theorem t36_proved : X1Belyi.TorsionStructure := _root_.ZInQ.RLeaf.t36_torsionStructure

/-- **T37 proved** (`ZInQKernel/Contrib/RLeaf/T37GoodReduction.lean`). -/
theorem t37_proved : X1Belyi.GoodReductionUnramified :=
  _root_.ZInQ.RLeaf.T37.t37_goodReductionUnramified

/-- **T39 from T40** (`ZInQKernel/Contrib/RLeaf/X1ConstantField.lean`): a degree-one place of
`K_N` makes `ℚ` algebraically closed in `K_N`. -/
theorem t39_of_t40 (h : X1Belyi.X1RationalCusp) : X1Belyi.X1ConstantField :=
  _root_.ZInQ.RLeaf.x1ConstantField_of_x1RationalCusp h

/-! ### Curve facts closed (infra-smooth-dim, image-plane): `MobiusGlue` from T5 alone -/

/-- This file's `ToP1` as the kernel's (`ZInQKernel/HDecomp/QM/Pairs.lean`), field by field. -/
def toP1K {X : Scheme.{0}} (σ : LeafQM.AV.ToP1 X) : _root_.LeafQM.AV.ToP1 X :=
  ⟨σ.U, σ.V, σ.cover, σ.f, σ.g, σ.inv, σ.basicOpen_f, σ.basicOpen_g⟩

/-- **C1b proved** (infra-smooth-dim; image-plane's copy `LeafQM.AV.Pin.smoothStalkDimOne`). -/
theorem smoothStalkDimOne_proved : LeafQM.AV.Pin.SmoothStalkDimOne :=
  _root_.LeafQM.AV.Pin.smoothStalkDimOne

/-- **C2K proved** (image-plane, `LeafQM.AV.Pin.constOrOntoAlgClosed`). -/
theorem constOrOntoAlgClosed_proved : LeafQM.AV.Pin.ConstOrOntoAlgClosed :=
  fun K _ _ X f hP hS σ => _root_.LeafQM.AV.Pin.constOrOntoAlgClosed K X f hP hS (toP1K σ)

/-- **C3K proved** (image-plane, `LeafQM.AV.Pin.ratFactorAlgClosed`). -/
theorem ratFactorAlgClosed_proved : LeafQM.AV.Pin.RatFactorAlgClosed :=
  fun K _ _ _ X f hP hS σ ρ => _root_.LeafQM.AV.Pin.ratFactorAlgClosed K X f hP hS (toP1K σ) (toP1K ρ)

/-- **`MobiusGlue` from T5 alone** (mobius-glue, curve-facts with the three facts above). -/
theorem mobiusGlue_of_t5' (h5 : PkgI2.TorsionStructure.{0}) : LeafQM.AV.Pin.MobiusGlue :=
  LeafQM.AV.Pin.mobiusGlue_of_curves'
    (LeafQM.AV.Pin.curveFacts_of_leaves smoothStalkDimOne_proved constOrOntoAlgClosed_proved
      ratFactorAlgClosed_proved).1
    (LeafQM.AV.Pin.curveFacts_of_leaves smoothStalkDimOne_proved constOrOntoAlgClosed_proved
      ratFactorAlgClosed_proved).2
    h5

/-! ### Abelian-variety glue closed (g9-abvarbc, part b10) -/

/-- **`MulIsogeny` proved** (g9-abvarbc; replaces the leaf `mulEtale` of `GluePieces3`, which was
used only through `mulIsogeny_of_mulEtale`). -/
theorem mulIsogeny_proved : G0FibreSimple.MulIsogeny := ZInQ.Contrib.AbVarBC.mulIsogeny

/-- **`KerUnitOpen` proved** (g9-abvarbc; mul-rigidity's leaf, implied by `MulEtale`). Not needed
below (`MulIsogeny` is proved directly); recorded for completeness. -/
theorem kerUnitOpen_proved : MulRigidity.KerUnitOpen := ZInQ.Contrib.AbVarBC.kerUnitOpen

/-- **F2 of G9 proved** (g9-abvarbc: `G9Bridge.AbVarBaseChange` from Mathlib alone). -/
theorem g9AbVarBaseChange_proved : ZInQ.Contrib.G9.G9Bridge.AbVarBaseChange :=
  ZInQ.Contrib.AbVarBC.abVarBaseChange

/-- **G9 from the amended R10** (r10-amend's result, over this file's objects): the weight clause
`R10Weights` is the second half of `PkgI4.DeRhamComparisonHT`. -/
theorem g9Glue_of_deRhamComparisonHT (h : PkgI4.DeRhamComparisonHT) : G0Galois.G9Glue :=
  ZInQ.Contrib.G9.g9Glue_of_abVarBaseChange g9AbVarBaseChange_proved
    (PkgI4.deRhamComparisonHT_iff.mp h).2

/-! ### Kernel-field and conj-twist glue closed (their later commits; parts a75, b05) -/

/-- **`OMaximal` proved** (kernel-field, `G0ModField.KernelField.oMaximal`, pure algebra). -/
theorem oMaximal_proved : G0ModField.KernelField.OMaximal := G0ModField.KernelField.oMaximal

/-- **`EndTransport` proved** (kernel-field: from `EndTransportBC`, which follows from
`RigidityHom`, proved by mul-rigidity). -/
theorem endTransport_proved : G0ModField.KernelField.EndTransport :=
  G0ModField.KernelField.endTransport_of
    (G0ModField.KernelField.endTransportBC_of_rigidity G0FibreSimple.rigidityHom)

/-- **`ConjTwistNontrivial` from T5, T26, T35 and the leaf N2** (conj-twist's final theorem): the
glue `ArtinTorsionSurj` and `ConjUniformization` of `GluePieces3` are no longer needed. -/
theorem conjTwistNontrivial_proved (h5 : PkgI2.TorsionStructure.{0}) (hT : PkgI3.TateModuleFree)
    (h35 : ZInQ.LeafPush2.UniformizationExists) (hN2 : G0Galois.HomLinearLift) :
    G0Galois.ConjTwistNontrivial :=
  G0Galois.conjTwistNontrivial_of_leaves h5 hT h35 hN2

/-! ### Height-bc glue closed (infra-stalks, part b07) -/

/-- **`CotangentSpanBC` proved** (infra-stalks, from the stalk of a fibre product). -/
theorem cotangentSpanBC_proved : ZInQ.HeightBC.CotangentSpanBC := ZInQ.HeightBC.cotangentSpanBC

/-- **`UniformizationLiftAnalytic` proved** (infra-stalks). -/
theorem uniformizationLiftAnalytic_proved : ZInQ.HeightBC.UniformizationLiftAnalytic :=
  ZInQ.HeightBC.uniformizationLiftAnalytic

/-- **`ProductUnifSplits` proved** (product-unif, part b08: elementary analysis). -/
theorem productUnifSplits_proved : ZInQ.ProductHeight.ProductUnifSplits :=
  ZInQ.ProductUnif.productUnifSplits

/-- This file's def-faltings `AbVar` as the kernel's `PkgI3.AbVar` (`ZInQKernel/HDecomp/Objects.lean`),
field by field. -/
def toAbVarK {L : Type} [Field L] (B : ZInQ.DefFaltings.AbVar L) : _root_.PkgI3.AbVar L := ⟨B.X⟩

/-- **`TangentDimAtOrigin` proved** (infra-smooth-dim, module `LF2SmoothDim`; transferred through
`toAbVarK`). -/
theorem tangentDimAtOrigin_proved : ZInQ.DefFaltings.HodgeLattice.TangentDimAtOrigin :=
  fun L _ B g hg => _root_.LF2.HodgeLattice.tangentDimAtOrigin L (toAbVarK B) g hg

/-- **`ProductMetrizationOfProductUnif` from the textbook leaf T35** (unif-dims, part b09, with
`TangentDimAtOrigin` proved). -/
theorem productMetrizationOfProductUnif_of_t35 (h35 : ZInQ.LeafPush2.UniformizationExists) :
    ZInQ.ProductHeight.ProductMetrizationOfProductUnif :=
  ZInQ.UnifDims.productMetrizationOfProductUnif_of_tangentDim h35 tangentDimAtOrigin_proved

/-- **`UnramifiedConjugates` proved** (inner-twist, module `LF2UnramConj`, Mathlib only). -/
theorem unramifiedConjugates_proved : G0ModField.UnramifiedConjugates :=
  _root_.G0ModField.unramifiedConjugates

/-! ### The open statements -/

/-- **The research-level leaves still open** (leaf-fold2). `ResearchLeaves3` (g0-assemble2: no
`opaque` placeholder) with four fields in their published, corrected or concrete form:
* `r1b`: R1(b) concretely, in family form (fibre-qm-period's `R1bFamily`; was `GluePieces3.r1bFamily`
  and, before that, the `opaque` `r1an`);
* `r10`: R10 corrected (`PkgI4.DeRhamComparisonHT`, with the multiplicity-0 clause; g9-derham,
  r10-amend);
* `r14`: R14 corrected (`G0Galois.R14Det`, with the determinant clause; was also
  `GluePieces3.r14Det`);
* `r17`: R17 concretely (`LadicCond.CarayolR17'`, Carayol 1986 Thm (A); was
  `GluePieces3.carayolR17` and, before that, the `opaque` `r17`). -/
structure OpenResearchLeaves2 : Prop where
  r1r2 : LeafAdopt.R1R2fpRep
  /-- R1(b), concrete (family form), for the triple of the leaf bundle. -/
  r1b : ∀ h : LeafAdopt.R1R2fpRep,
    G0Split.FibreQM.R1bFamily (G0Split.FibreQM.ownY (LeafAdopt.R1R2fp_of_rep h))
      (G0Split.FibreQM.ownΦ (LeafAdopt.R1R2fp_of_rep h))
      (G0Split.FibreQM.ownπ (LeafAdopt.R1R2fp_of_rep h))
  r1rec : LeafQM.AV.R1rec
  r3 : ZInQ.LeafPush2.R03_LinYang
  r4 : PkgI1.ThetaModularity
  r5 : LeafQM.AV.R5fp
  r5count : LeafQM.AV.R5fpCount
  r6 : PkgI2.RaynaudCriterion.{0}
  r7a : PkgI2.NeronOggShafarevich.{0}
  r7b : PkgI2.SerreTatePotentialGood.{0}
  r8 : PkgI2.GrothendieckMonodromy.{0}
  r9a : PkgI3.FaltingsSemisimple
  r9b : PkgI3.FaltingsTate
  /-- R10 corrected (with multiplicity `0` off `{0, −1}`). -/
  r10 : PkgI4.DeRhamComparisonHT
  r11r12 : PkgI4.PanBerger
  r13 : PkgI4.EigenformHT
  /-- R14 corrected (with the determinant clause). -/
  r14 : G0Galois.R14Det
  r15 : DeligneSerreConseq
  r16 : LeafModCurves.R16_EichlerShimuraJ1'
  /-- R17, concrete (Carayol 1986, Thm (A)). -/
  r17 : LadicCond.CarayolR17'
  r18 : ZInQ.LeafPush2.R18_Javanpeykar
  r19 : ZInQ.DefFaltings.R19_GaudronRemond
  r20 : ZInQ.DefFaltings.R20_FaltingsLemma5
  r21 : ZInQ.DefFaltings.R21_Bost
  r22 : ZInQ.LeafPush2.R22_Pazuki
  /-- H5's finiteness half (its `NeronModelMinimal` half is proved, h5-glue). -/
  h5fin : ZInQ.DefFaltings.StableHeightFinite

/-- **The textbook leaves still open** (leaf-fold2): `TextbookLeaves` without the ten fields no
proof uses (deleted, `mk_prefix.py`), without the eight proved fields (`t14a`, `t14b` here;
`t15`, `t16a`, `t17`, `t18`, `t25`, `t31` by leaf-fold), and with `x1` (T36-T40) cut to T38 and
T40 (T36, T37 proved; T39 follows from T40). -/
structure OpenTextbookLeaves2 : Prop where
  t5 : PkgI2.TorsionStructure.{0}
  t6 : PkgI3.HomFreeFinite
  t7 : PkgI3.CharPolyIndepOfEll
  t8 : PkgI3.PoincareReducibility
  t9 : LeafPush.T09_WeilPairing.{0}
  t10 : T10Etale.T10_TateDuality
  t11a : ZInQ.LeafPush2.T11a_RiemannEnd
  t11b : ZInQ.LeafPush2.T11b_Rigidity
  t23 : ∀ (p : ℕ) [Fact p.Prime], PkgI4.T23_FontaineClosure p
  t24 : EigenformTwist
  t26 : PkgI3.TateModuleFree
  t27 : PkgI3.QMDichotomyYu
  t33 : LeafModCurves.JacobianExists ℚ
  t34 : LeafModCurves.DimJ1Genus
  t35 : ZInQ.LeafPush2.UniformizationExists
  /-- T38 (x1-belyi): a function field over `ℚ` with constant field `ℚ` is that of a smooth
  proper curve. -/
  t38 : X1Belyi.CurveOfFunctionFieldQ
  /-- T40 (x1-belyi): `K_N` has a degree-one place. -/
  t40 : X1Belyi.X1RationalCusp
  t41 : ZInQ.H5Neron.NeronModelExists

/-- **The leaves introduced by the wave 26-27 reductions** (g0-assemble2's `GluePieces3` fields of
kind LEAF or LEAF?, minus those now proved or moved to `OpenResearchLeaves2`). -/
structure OpenAddedLeaves2 : Prop where
  /-- fs5-nocm N1b′, LEAF (CM points via optimal embeddings). -/
  cmOptimalEmbedding : FS5NoCM.CMOptimalEmbedding
  /-- g0-thetapoint, LEAF? (theta-constant ratios at a CM period matrix are algebraic). -/
  thetaRatiosAlgebraic : G0Split.ThetaPt.ThetaRatiosAlgebraic
  /-- fibre-qm-period, LEAF? (pkg-I1's composite leaf: the theta-quotient Hauptmodul of `Γ*`). -/
  qmHauptmodul : PkgI1.QMHauptmodul
  /-- fibre-qm-period, LEAF (Eichler class number one, lattice form). -/
  qmClassNumberOne : G0Split.FibreQM.QMClassNumberOne
  /-- fibre-qm-period, LEAF? (Lin–Yang's divisor of `ψ₄`). -/
  qmDenZeroCM3 : G0Split.FibreQM.QMDenZeroCM3
  /-- g0-mod-galois, LEAF (Burnside). -/
  burnsideAbsIrred : G0Galois.BurnsideAbsIrred
  /-- conj-twist N2, LEAF (Birkenhake–Lange Prop. 1.2.1). -/
  homLinearLift : G0Galois.HomLinearLift
  /-- g12-det, LEAF (Sen 1980). -/
  senTwist : G0Galois.SenTwist
  /-- g12-det, LEAF (Tate 1967, Ax–Sen–Tate). -/
  finiteImageHT : G0Galois.FiniteImageHT
  /-- weil-pairing, LEAF (T9 restated). -/
  t09SymmIsogenyExists : WeilPairing.T09_SymmIsogenyExists
  /-- weil-pairing, LEAF (Mumford §7-8). -/
  isogenyQuasiInverse : WeilPairing.IsogenyQuasiInverse
  /-- weil-pairing, LEAF (Mumford §4 Appl. 2). -/
  divisiblePoints : WeilPairing.DivisiblePoints

/-- **The glue still open** (leaf-fold2): g0-assemble2's `GluePieces3` fields of kind GLUE, minus
the nine now proved (`smoothStalkDimOne`, `ratFactorAlgClosed`, `g9AbVarBaseChange`, `oMaximal`,
`endTransport`, `cotangentSpanBC`, `uniformizationLiftAnalytic`, `productUnifSplits`,
`unramifiedConjugates`) and the one now
following from the leaf T35 (`productMetrizationOfProductUnif`) and the two no longer used (`artinTorsionSurj`, `conjUniformization`: conj-twist's
final theorem needs neither). -/
structure OpenGlue2 : Prop where
  x6KummerFibre : FS5NoCM.X6KummerFibre
  hodgeBCInjective : ZInQ.HeightBC.HodgeBCInjective
  omegaBaseChange : ZInQ.HeightBC.OmegaBaseChange
  periodMapGlue : ∀ h : LeafAdopt.R1R2fpRep,
    G0Split.FibreQM.PeriodMapGlue (G0Split.FibreQM.ownY (LeafAdopt.R1R2fp_of_rep h))
      (G0Split.FibreQM.ownΦ (LeafAdopt.R1R2fp_of_rep h))
      (G0Split.FibreQM.ownπ (LeafAdopt.R1R2fp_of_rep h))
  hauptmodulUnique : G0Split.FibreQM.HauptmodulUnique
  cPtsTransport : G0Split.FibreQM.CPtsTransport
  propTSAll : G0ModField.PropTSAll
  conjIsogMaps : G0ModField.KernelField.ConjIsogMaps
  modelG3 : G0AssembleMod.ModelG3
  linkedTateLocal : G0AssembleMod.LinkedTateLocal

/-! ### From the open statements back to g0-assemble2's bundles -/

theorem researchLeaves3_of_open2 (r : OpenResearchLeaves2) : ResearchLeaves3 where
  r1r2 := r.r1r2
  r1rec := r.r1rec
  r3 := r.r3
  r4 := r.r4
  r5 := r.r5
  r5count := r.r5count
  r6 := r.r6
  r7a := r.r7a
  r7b := r.r7b
  r8 := r.r8
  r9a := r.r9a
  r9b := r.r9b
  r10 := PkgI4.deRhamComparison_of_HT r.r10
  r11r12 := r.r11r12
  r13 := r.r13
  r14 := eigenformRepExists_of_r14Det r.r14
  r15 := r.r15
  r16 := r.r16
  r18 := r.r18
  r19 := r.r19
  r20 := r.r20
  r21 := r.r21
  r22 := r.r22
  h5fin := r.h5fin

theorem x1Leaves_of_open2 (t : OpenTextbookLeaves2) : X1Belyi.X1Leaves where
  torsion := t36_proved
  goodRed := t37_proved
  curve := t.t38
  constants := t39_of_t40 t.t40
  cusp := t.t40

theorem textbookLeaves_of_open2 (t : OpenTextbookLeaves2) : TextbookLeaves where
  t5 := t.t5
  t6 := t.t6
  t7 := t.t7
  t8 := t.t8
  t9 := t.t9
  t10 := t.t10
  t11a := t.t11a
  t11b := t.t11b
  t14a := t14a_proved
  t14b := t14b_proved
  t15 := t15_proved
  t16a := t16a_proved
  t17 := t17_proved
  t18 := t18_proved
  t23 := t.t23
  t24 := t.t24
  t25 := t25_proved
  t26 := t.t26
  t27 := t.t27
  t31 := t31_proved
  t33 := t.t33
  t34 := t.t34
  t35 := t.t35
  x1 := x1Leaves_of_open2 t
  t41 := t.t41

/-- **Leaves.lean's `GluePieces` from the open statements.** g0-assemble2's
`gluePieces_of_gluePieces3`, with every proved field replaced by its proof (`mulIsogeny_proved` for
`mulIsogeny_of_mulEtale gp.mulEtale`, the curve facts inside `mobiusGlue_of_t5'`, `oMaximal_proved`,
`endTransport_proved`, `cotangentSpanBC_proved`, `uniformizationLiftAnalytic_proved`, G9 from
`r.r10`, G10 from conj-twist's `conjTwistNontrivial_of_leaves`). -/
theorem gluePieces_of_open2 (r : OpenResearchLeaves2) (t : OpenTextbookLeaves2)
    (l : OpenAddedLeaves2) (g : OpenGlue2) : GluePieces :=
  let r3 := researchLeaves3_of_open2 r
  let t3 := textbookLeaves_of_open2 t
  have hMob : LeafQM.AV.Pin.MobiusGlue := mobiusGlue_of_t5' t.t5
  have hFS5 : G0FibreSimple.FibreComTrivial :=
    fibreComTrivial_of_full (FS5NoCM.fibreComTrivialFull_of_leaves'' (r1r2fpFull_of r3)
      hMob t.t27 t.t6 l.cmOptimalEmbedding g.x6KummerFibre r.r5count)
  have hFS : G0Split.FibreSimple :=
    G0FibreSimple.fibreSimple_of_leaves t3 mulIsogeny_proved G0FibreSimple.rigidityHom
      ⟨G0FibreSimple.finiteDescends_proof, hFS5⟩
  { dimFinite := G0Split.dimFinite
    dimBaseChange := G0Split.dimBaseChange
    fibreSimple := hFS
    productModelHeight := ZInQ.ProductHeight.productModelHeight_of_splits productUnifSplits_proved
      (productMetrizationOfProductUnif_of_t35 t.t35)
    stableHeightBaseChange := G0StableBC.stableHeightBaseChange_of_hodgeLine
      (ZInQ.HeightBC.g0_hodgeLine_iff.mpr (ZInQ.HeightBC.hodgeLineBaseChange_of_glue4
        g.hodgeBCInjective cotangentSpanBC_proved g.omegaBaseChange
        uniformizationLiftAnalytic_proved))
    productExists := G0Product.productExists
    reverseIsogeny := G0RevIsog.reverseIsogeny_of_leaves3 r3 G0Split.dimFinite
    thetaPoint := G0Split.ThetaPt.thetaPointOfFibre_of_qm_ratios
      (G0Split.FibreQM.fibreQMPeriod_main_rep r.r1r2 hMob l.qmHauptmodul
        t.t35 t.t11a l.qmClassNumberOne (r.r1b r.r1r2) (g.periodMapGlue r.r1r2)
        g.hauptmodulUnique l.qmDenZeroCM3 g.cPtsTransport)
      l.thetaRatiosAlgebraic
    modularConstituent := modularConstituent_of_field t3
      (G0ModField.fibreCoverExists_of_propTSAll' t.t5 g.propTSAll unramifiedConjugates_proved)
      (G0ModField.KernelField.kernelFieldExists_of_split'' t.t6 r.r7a r.r6 t.t5 t.t27
        hFS5 G0ModField.KernelField.oMaximal endTransport_proved g.conjIsogMaps)
      UnramTate.unramifiedSup_mf
      (G0AssembleMod.afterG7_of3 r3 t3
        ⟨l.burnsideAbsIrred, r.r14,
          g9Glue_of_deRhamComparisonHT r.r10,
          G0Galois.g10Glue_of_conjTwist
            (G0Galois.conjTwistNontrivial_of_leaves t.t5 t.t26 t.t35 l.homLinearLift),
          G0Galois.g12Weight_of_senTwist l.senTwist l.finiteImageHT,
          G0Galois.detTate_of_leaves l.t09SymmIsogenyExists l.isogenyQuasiInverse
            l.divisiblePoints t.t26,
          G0AssembleMod.resQFiniteIndex⟩
        (G0ModNewform.dirichletOfFinite_of_t17 t17_proved) r.r17
        Swan.swanIndependent_proved Swan.swanIntegral_proved
        Swan.adaptedExists_proved
        (G0AssembleMod.modelG3G6_of hFS
          (G0AssembleMod.modelNoncomm_of_mulIsogeny mulIsogeny_proved) g.modelG3)
        (G0AssembleMod.linkedTateData_of_local t.t7 g.linkedTateLocal))
    heightCopies := G0HeightCopies.heightCopiesAgree }

/-- **G0 with only the open leaves and the open glue** (leaf-fold2; no `sorry`, standard axioms).
`ZInQ.SixContactMin` follows from
* `OpenResearchLeaves2`: 26 research-level fields (R1(b), R10, R14, R17 in concrete or corrected
  form; no `opaque` placeholder);
* `OpenTextbookLeaves2`: 18 textbook fields;
* `OpenAddedLeaves2`: 12 leaves (9 LEAF, 3 LEAF?) introduced by the wave 26-27 reductions;
* `OpenGlue2`: 10 glue Props.
The table of every field, its kind and source is `docs/research/leaf-fold2.md`. -/
theorem sixContactMin_of_open2 (r : OpenResearchLeaves2) (t : OpenTextbookLeaves2)
    (l : OpenAddedLeaves2) (g : OpenGlue2) : ZInQ.SixContactMin :=
  sixContactMin_of_leavesR3 (researchLeaves3_of_open2 r) (textbookLeaves_of_open2 t)
    (gluePieces_of_open2 r t l g)

end HSyn

end

#print axioms HSyn.t14a_proved
#print axioms HSyn.t14b_proved
#print axioms HSyn.t28_proved
#print axioms HSyn.t36_proved
#print axioms HSyn.t37_proved
#print axioms HSyn.t39_of_t40
#print axioms HSyn.smoothStalkDimOne_proved
#print axioms HSyn.constOrOntoAlgClosed_proved
#print axioms HSyn.ratFactorAlgClosed_proved
#print axioms HSyn.mobiusGlue_of_t5'
#print axioms HSyn.mulIsogeny_proved
#print axioms HSyn.kerUnitOpen_proved
#print axioms HSyn.g9AbVarBaseChange_proved
#print axioms HSyn.g9Glue_of_deRhamComparisonHT
#print axioms HSyn.oMaximal_proved
#print axioms HSyn.endTransport_proved
#print axioms HSyn.conjTwistNontrivial_proved
#print axioms HSyn.cotangentSpanBC_proved
#print axioms HSyn.uniformizationLiftAnalytic_proved
#print axioms HSyn.productUnifSplits_proved
#print axioms HSyn.tangentDimAtOrigin_proved
#print axioms HSyn.productMetrizationOfProductUnif_of_t35
#print axioms HSyn.unramifiedConjugates_proved
#print axioms HSyn.researchLeaves3_of_open2
#print axioms HSyn.textbookLeaves_of_open2
#print axioms HSyn.gluePieces_of_open2
#print axioms HSyn.sixContactMin_of_open2

end G0A2_b20_fold

end HDec
