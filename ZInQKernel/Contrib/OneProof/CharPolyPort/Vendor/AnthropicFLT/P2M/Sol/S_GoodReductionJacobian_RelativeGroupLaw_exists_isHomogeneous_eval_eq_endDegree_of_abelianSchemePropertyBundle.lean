/-
Vendored from anthropics/fermats-last-theorem @ 6e837e75355538c7f80bab5b956861e86c4eacc2.
Original module: P2M.Sol.S_GoodReductionJacobian_RelativeGroupLaw_exists_isHomogeneous_eval_eq_endDegree_of_abelianSchemePropertyBundle. Apache-2.0.
Modification notice (CloudB3 Worker13, 2026-11-15/16): ported to Lean 4.35.0 / Mathlib v4.35.0
(namespace-wrapped port on origin/cloud-b3/w13-recovery).
Modified for the Z-in-Q kernel (charpoly-port, 2026-11-17): the Worker13 port unwrapped into the
CloudB3W16Torsion conventions (original declaration namespaces; imports relocated to the
CloudB3W16Torsion vendor; the FLT-suffixed renames of CloudB3W16Torsion/NOTICE.md applied; port
shim commands removed). Mathematical statements and proofs retained, subject to Lean 4.35 adaptations
listed in scratch/charpoly-port/log.md.
Full original notices/credits: LICENSE, NOTICE.upstream, ATTRIBUTION.upstream.md in this vendor root.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_JacJ1Iface
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_RelativeGroupLaw
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_GoodReductionJacobian_RelativeGroupLawKernel
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_NeronModelEndomorphismExtension
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_RelativeGroupLawEndDegree
import ZInQKernel.Contrib.OneProof.CharPolyPort.Vendor.AnthropicFLT.Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_exists_polynomial_eval_eq_endDegree_zpow_mul_of_abelianSchemePropertyBundle
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_endDegree_nsmul_idPoint_eq_pow_of_natCast_ne_zero
import ZInQKernel.Contrib.OneProof.CharPolyPort.Vendor.AnthropicFLT.Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_isFinite_and_flat_schemeNsmul_of_isUnit
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_isFinite_of_isFinite_endKerStr
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Theorems.Thm_GoodReductionJacobian_AbelianSchemePropertyBundle_flat_of_isFinite
import ZInQKernel.Contrib.OneProof.CharPolyPort.Vendor.AnthropicFLT.Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_endDegree_schemeHomOverComp_of_isFinite_of_flat
import ZInQKernel.Contrib.OneProof.CharPolyPort.Vendor.AnthropicFLT.Theorems.Thm_AddCommGroup_exists_mvPolynomial_totalDegree_le_eval_eq_of_forall_exists_polynomial_zsmul_add
import ZInQKernel.Contrib.OneProof.CharPolyPort.Vendor.AnthropicFLT.Theorems.Thm_MvPolynomial_isHomogeneous_of_forall_eval_intCast_mul_eq_pow_mul
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.P2M.Util

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false

namespace P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_isHomogeneous_eval_eq_endDegree_of_abelianSchemePropertyBundle

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian

universe u

namespace P2mPolyFun

variable {K : Type u} [Field K] {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of K)}

local infixl:80 " ⊚ " => NeronModelInfra.schemeHomOverComp

def IsHom (L : RelativeGroupLaw K f) (β : SchemeHomOver f f) : Prop :=
  ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of K)) (x y : SchemeHomOver t f),
    (L.mul t x y) ⊚ β = L.mul t (x ⊚ β) (y ⊚ β)

section Points

variable (L : RelativeGroupLaw K f)

theorem compT_mul {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of K)} (z : SchemeHomOver t f)
    (β γ : SchemeHomOver f f) :
    z ⊚ (L.mul f β γ) = L.mul t (z ⊚ β) (z ⊚ γ) := by
  have h := L.mul_natural f t z.1 z.2 β γ
  have e : ∀ δ : SchemeHomOver f f, GoodReductionJacobian.schemeHomOverComp z.1 z.2 δ = z ⊚ δ :=
    fun δ => Subtype.ext rfl
  rw [e, e, e] at h
  exact h

theorem compT_one {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of K)} (z : SchemeHomOver t f) :
    z ⊚ (L.one f) = L.one t := by
  have h := L.one_natural f t z.1 z.2
  have e : GoodReductionJacobian.schemeHomOverComp z.1 z.2 (L.one f) = z ⊚ (L.one f) := Subtype.ext rfl
  rw [e] at h
  exact h

def evalHom {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of K)} (z : SchemeHomOver t f) :
    letI := L.pointGroup f; letI := L.pointGroup t; SchemeHomOver f f →* SchemeHomOver t f :=
  letI := L.pointGroup f; letI := L.pointGroup t
  { toFun := fun δ => z ⊚ δ
    map_one' := compT_one L z
    map_mul' := fun β γ => compT_mul L z β γ }

theorem compT_inv {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of K)} (z : SchemeHomOver t f)
    (β : SchemeHomOver f f) :
    letI := L.pointGroup f; letI := L.pointGroup t; z ⊚ β⁻¹ = (z ⊚ β)⁻¹ := by
  letI := L.pointGroup f; letI := L.pointGroup t
  exact map_inv (evalHom L z) β

theorem compT_inv' {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of K)} (z : SchemeHomOver t f)
    (β : SchemeHomOver f f) :
    z ⊚ (L.inv f β) = L.inv t (z ⊚ β) :=
  compT_inv L z β

theorem compT_pow {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of K)} (z : SchemeHomOver t f)
    (β : SchemeHomOver f f) (n : ℕ) :
    letI := L.pointGroup f; letI := L.pointGroup t; z ⊚ (β ^ n) = (z ⊚ β) ^ n := by
  letI := L.pointGroup f; letI := L.pointGroup t
  exact map_pow (evalHom L z) β n

theorem compT_zpow {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of K)} (z : SchemeHomOver t f)
    (β : SchemeHomOver f f) (n : ℤ) :
    letI := L.pointGroup f; letI := L.pointGroup t; z ⊚ (β ^ n) = (z ⊚ β) ^ n := by
  letI := L.pointGroup f; letI := L.pointGroup t
  exact map_zpow (evalHom L z) β n

theorem pow_eq_nsmul {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of K)) (x : SchemeHomOver t f) (n : ℕ) :
    letI := L.pointGroup t; x ^ n = L.nsmul t n x := by
  letI := L.pointGroup t
  induction n with
  | zero => rfl
  | succ n ih => rw [pow_succ, ih]; rfl

theorem id_pow_eq (n : ℕ) :
    letI := L.pointGroup f; (schemeHomOverId f) ^ n = L.nsmul f n RelativeGroupLaw.idPoint :=
  pow_eq_nsmul L f _ n

theorem pow_eq_comp_nsmul (γ : SchemeHomOver f f) (n : ℕ) :
    letI := L.pointGroup f; γ ^ n = γ ⊚ (L.nsmul f n RelativeGroupLaw.idPoint) := by
  letI := L.pointGroup f
  have h := compT_pow L γ (schemeHomOverId f) n
  rw [NeronModelInfra.schemeHomOverComp_id_right] at h
  rw [← h, ← id_pow_eq L n]

theorem inv_eq_comp_inv (γ : SchemeHomOver f f) :
    letI := L.pointGroup f; γ⁻¹ = γ ⊚ (schemeHomOverId f)⁻¹ := by
  letI := L.pointGroup f
  have h := compT_inv L γ (schemeHomOverId f)
  rw [NeronModelInfra.schemeHomOverComp_id_right] at h
  exact h.symm

theorem isIso_inv_id : letI := L.pointGroup f; IsIso ((schemeHomOverId f)⁻¹).1 := by
  letI := L.pointGroup f
  have h : ((schemeHomOverId f)⁻¹) ⊚ ((schemeHomOverId f)⁻¹) = schemeHomOverId f := by
    rw [← inv_eq_comp_inv L, inv_inv]
  have h1 : ((schemeHomOverId f)⁻¹).1 ≫ ((schemeHomOverId f)⁻¹).1 = 𝟙 A := congrArg Subtype.val h
  exact ⟨⟨_, h1, h1⟩⟩

theorem unit_comp_nsmul (n : ℕ) :
    (L.one (𝟙 _)).1 ≫ (L.nsmul f n RelativeGroupLaw.idPoint).1 = (L.one (𝟙 (Spec (CommRingCat.of K)))).1 := by
  set e := L.one (𝟙 (Spec (CommRingCat.of K)))
  have h := L.nsmul_natural f (𝟙 _) e.1 e.2 n RelativeGroupLaw.idPoint
  have h0 : GoodReductionJacobian.schemeHomOverComp e.1 e.2 (RelativeGroupLaw.idPoint (f := f)) = e :=
    Subtype.ext (Category.comp_id _)
  rw [h0, L.nsmul_unit] at h
  exact congrArg Subtype.val h

theorem unit_comp_inv :
    letI := L.pointGroup f;
    (L.one (𝟙 _)).1 ≫ ((schemeHomOverId f)⁻¹).1 = (L.one (𝟙 (Spec (CommRingCat.of K)))).1 := by
  letI := L.pointGroup f
  letI := L.pointGroup (𝟙 (Spec (CommRingCat.of K)))
  set e := L.one (𝟙 (Spec (CommRingCat.of K)))
  have h : e ⊚ (schemeHomOverId f)⁻¹ = e := by
    rw [compT_inv L e, NeronModelInfra.schemeHomOverComp_id_right]
    change (1 : SchemeHomOver (𝟙 _) f)⁻¹ = 1
    exact inv_one
  exact congrArg Subtype.val h

end Points

section HomSubgroup

variable (L : RelativeGroupLaw K f) (hc : L.IsCommutative)

include hc in

def homSubgroup : letI := L.pointCommGroup hc f; Subgroup (SchemeHomOver f f) :=
  letI := L.pointCommGroup hc f
  { carrier := {β | IsHom L β}
    mul_mem' := by
      intro β γ hβ hγ T t x y
      change (L.mul t x y) ⊚ (L.mul f β γ) = L.mul t (x ⊚ L.mul f β γ) (y ⊚ L.mul f β γ)
      rw [compT_mul, compT_mul, compT_mul, hβ, hγ]
      letI := L.pointCommGroup hc t
      change (x ⊚ β * (y ⊚ β)) * (x ⊚ γ * (y ⊚ γ)) = (x ⊚ β * (x ⊚ γ)) * (y ⊚ β * (y ⊚ γ))
      exact mul_mul_mul_comm _ _ _ _
    one_mem' := by
      intro T t x y
      change (L.mul t x y) ⊚ (L.one f) = L.mul t (x ⊚ L.one f) (y ⊚ L.one f)
      rw [compT_one, compT_one, compT_one, L.one_mul]
    inv_mem' := by
      intro β hβ T t x y
      change (L.mul t x y) ⊚ (L.inv f β) = L.mul t (x ⊚ L.inv f β) (y ⊚ L.inv f β)
      letI := L.pointCommGroup hc t
      rw [compT_inv', compT_inv', compT_inv', hβ]
      change (x ⊚ β * (y ⊚ β))⁻¹ = (x ⊚ β)⁻¹ * (y ⊚ β)⁻¹
      rw [mul_inv] }

include hc in
theorem isHom_zpow {γ : SchemeHomOver f f} (hγ : IsHom L γ) (n : ℤ) :
    IsHom L (letI := L.pointCommGroup hc f; γ ^ n) := by
  letI := L.pointCommGroup hc f
  have hm : γ ^ n ∈ homSubgroup L hc :=
    Subgroup.zpow_mem (homSubgroup L hc) (show γ ∈ homSubgroup L hc from hγ) n
  exact fun {T} t x y => hm t x y

include hc in
theorem isHom_pow {γ : SchemeHomOver f f} (hγ : IsHom L γ) (n : ℕ) :
    IsHom L (letI := L.pointCommGroup hc f; γ ^ n) := by
  letI := L.pointCommGroup hc f
  have hm : γ ^ n ∈ homSubgroup L hc :=
    Subgroup.pow_mem (homSubgroup L hc) (show γ ∈ homSubgroup L hc from hγ) n
  exact fun {T} t x y => hm t x y

end HomSubgroup

section Kernel

variable (L : RelativeGroupLaw K f)

theorem isFinite_endKerStr_of_comp [IsSeparated f] (δ η : SchemeHomOver f f)
    (hη : (L.one (𝟙 _)).1 ≫ η.1 = (L.one (𝟙 (Spec (CommRingCat.of K)))).1)
    [IsFinite (L.endKerStr (δ ⊚ η))] : IsFinite (L.endKerStr δ) := by
  set e := L.one (𝟙 (Spec (CommRingCat.of K))) with he

  haveI : IsClosedImmersion e.1 := by
    have : IsClosedImmersion (e.1 ≫ f) := by rw [e.2]; infer_instance
    exact IsClosedImmersion.of_comp e.1 f

  have w : L.endKerι δ ≫ (δ ⊚ η).1 = L.endKerStr δ ≫ e.1 := by
    change L.endKerι δ ≫ (δ.1 ≫ η.1) = _
    rw [← Category.assoc, L.endKerι_comp, Category.assoc, hη]
  let c : L.endKer δ ⟶ L.endKer (δ ⊚ η) := pullback.lift (L.endKerι δ) (L.endKerStr δ) w
  have hc1 : c ≫ L.endKerι (δ ⊚ η) = L.endKerι δ := pullback.lift_fst _ _ _
  have hc2 : c ≫ L.endKerStr (δ ⊚ η) = L.endKerStr δ := pullback.lift_snd _ _ _
  haveI : IsClosedImmersion (L.endKerι (δ ⊚ η)) := by
    change IsClosedImmersion (pullback.fst _ _); infer_instance
  haveI : IsClosedImmersion (c ≫ L.endKerι (δ ⊚ η)) := by
    rw [hc1]; change IsClosedImmersion (pullback.fst _ _); infer_instance
  haveI : IsClosedImmersion c := IsClosedImmersion.of_comp c (L.endKerι (δ ⊚ η))
  rw [← hc2]
  infer_instance

theorem endDegree_of_isIso (η : SchemeHomOver f f) [IsIso η.1] : L.endDegree η = 1 := by
  haveI : IsIso (L.endKerStr η) := by
    change IsIso (pullback.snd η.1 (L.one (𝟙 (Spec (CommRingCat.of K)))).1); infer_instance
  haveI : IsFinite (L.endKerStr η) := inferInstance
  rw [L.endDegree_of_isFinite]
  exact congrFun (Scheme.Hom.finrank_eq_one_of_isIso _) _

end Kernel

section Homog

variable (L : RelativeGroupLaw K f)

theorem connectedSpace (hA : AbelianSchemePropertyBundle K f) : ConnectedSpace A := by
  have h := hA.connectedFibres (IsLocalRing.closedPoint K)
  have h' : _root_.IsConnected (Set.univ : Set A) := by
    convert h using 1
    exact (Set.eq_univ_of_forall fun _ => Subsingleton.elim _ _).symm
  exact connectedSpace_iff_univ.mpr h'

theorem endDegree_comp (hA : AbelianSchemePropertyBundle K f) (γ η : SchemeHomOver f f) (hγ : IsHom L γ)
    [IsFinite η.1] [Flat η.1]
    (hη : (L.one (𝟙 _)).1 ≫ η.1 = (L.one (𝟙 (Spec (CommRingCat.of K)))).1) :
    L.endDegree (γ ⊚ η) = L.endDegree γ * L.endDegree η := by
  haveI := hA.proper
  haveI := hA.smooth
  haveI := connectedSpace hA
  by_cases hfin : IsFinite (L.endKerStr γ)
  · haveI : IsFinite γ.1 :=
      GoodReductionJacobian.RelativeGroupLaw.isFinite_of_isFinite_endKerStr K f L γ hγ
    haveI : Flat γ.1 := GoodReductionJacobian.AbelianSchemePropertyBundle.flat_of_isFinite K hA γ
    exact GoodReductionJacobian.RelativeGroupLaw.endDegree_schemeHomOverComp_of_isFinite_of_flat K f L γ η
  · have h1 : L.endDegree γ = 0 := L.endDegree_of_not_isFinite γ hfin
    have h2 : ¬ IsFinite (L.endKerStr (γ ⊚ η)) := fun h =>
      hfin (isFinite_endKerStr_of_comp L γ η hη)
    rw [L.endDegree_of_not_isFinite _ h2, h1, zero_mul]

variable [IsAlgClosed K] (hc : L.IsCommutative) (hA : AbelianSchemePropertyBundle K f)
  (g : ℕ) [SmoothOfRelativeDimension g f]

include hA in

theorem endDegree_pow (γ : SchemeHomOver f f) (hγ : IsHom L γ) (n : ℕ) (hn : (n : K) ≠ 0) :
    L.endDegree (letI := L.pointCommGroup hc f; γ ^ n) = L.endDegree γ * n ^ (2 * g) := by
  letI := L.pointCommGroup hc f
  have hpow : γ ^ n = γ ⊚ (L.nsmul f n RelativeGroupLaw.idPoint) := pow_eq_comp_nsmul L γ n
  obtain ⟨hF, hFl⟩ := GoodReductionJacobian.RelativeGroupLaw.isFinite_and_flat_schemeNsmul_of_isUnit L hA
    (fun t x y => hc t x y) n (Ne.isUnit hn)
  haveI : IsFinite (L.nsmul f n RelativeGroupLaw.idPoint).1 := hF
  haveI : Flat (L.nsmul f n RelativeGroupLaw.idPoint).1 := hFl
  rw [hpow, endDegree_comp L hA γ _ hγ (unit_comp_nsmul L n),
    GoodReductionJacobian.RelativeGroupLaw.endDegree_nsmul_idPoint_eq_pow_of_natCast_ne_zero K f L hc hA g n hn]

include hA in
omit [IsAlgClosed K] in

theorem endDegree_inv (γ : SchemeHomOver f f) (hγ : IsHom L γ) :
    L.endDegree (letI := L.pointCommGroup hc f; γ⁻¹) = L.endDegree γ := by
  letI := L.pointCommGroup hc f
  haveI : IsIso ((schemeHomOverId f)⁻¹).1 := isIso_inv_id L
  rw [inv_eq_comp_inv L γ, endDegree_comp L hA γ _ hγ (unit_comp_inv L),
    endDegree_of_isIso L ((schemeHomOverId f)⁻¹), mul_one]

include hA in

theorem endDegree_zpow (γ : SchemeHomOver f f) (hγ : IsHom L γ) (n : ℤ) (hn : (n : K) ≠ 0) :
    ((L.endDegree (letI := L.pointCommGroup hc f; γ ^ n) : ℕ) : ℚ) =
      (n : ℚ) ^ (2 * g) * (L.endDegree γ : ℚ) := by
  letI := L.pointCommGroup hc f
  obtain ⟨m, rfl | rfl⟩ := Int.eq_nat_or_neg n
  · have hm : (m : K) ≠ 0 := by exact_mod_cast hn
    rw [zpow_natCast, endDegree_pow L hc hA g γ hγ m hm]
    push_cast
    ring
  · have hm : (m : K) ≠ 0 := by
      intro h; apply hn; push_cast; rw [h, neg_zero]
    rw [zpow_neg, zpow_natCast, endDegree_inv L hc hA _ (isHom_pow L hc hγ m),
      endDegree_pow L hc hA g γ hγ m hm]
    push_cast
    rw [Even.neg_pow (even_two_mul g)]
    ring

end Homog

section Assembly

theorem infinite_setOf_intCast_ne_zero (K : Type u) [Field K] : Set.Infinite {n : ℤ | (n : K) ≠ 0} := by

  obtain ⟨q, hq2, hqK⟩ : ∃ q : ℕ, 2 ≤ q ∧ (q : K) ≠ 0 := by
    by_cases h2 : (2 : K) = 0
    · refine ⟨3, by norm_num, ?_⟩
      have : ((3 : ℕ) : K) = (2 : K) + 1 := by norm_num
      rw [this, h2, zero_add]; exact one_ne_zero
    · exact ⟨2, le_rfl, by exact_mod_cast h2⟩
  refine Set.infinite_of_injective_forall_mem (f := fun k : ℕ => ((q ^ k : ℕ) : ℤ)) ?_ ?_
  · intro a b h
    have h' : ((q ^ a : ℕ) : ℤ) = ((q ^ b : ℕ) : ℤ) := h
    exact Nat.pow_right_injective hq2 (by exact_mod_cast h')
  · intro k
    change (((q ^ k : ℕ) : ℤ) : K) ≠ 0
    push_cast
    exact pow_ne_zero _ hqK

theorem eval_intCast_mul_eq_of_ne_zero (K : Type u) [Field K] {ι : Type*} (P : MvPolynomial ι ℚ) (d : ℕ)
    (h : ∀ (n : ℤ) (c : ι → ℤ), (n : K) ≠ 0 → MvPolynomial.eval (fun i => ((n * c i : ℤ) : ℚ)) P =
      (n : ℚ) ^ d * MvPolynomial.eval (fun i => (c i : ℚ)) P)
    (n : ℤ) (c : ι → ℤ) :
    MvPolynomial.eval (fun i => ((n * c i : ℤ) : ℚ)) P = (n : ℚ) ^ d * MvPolynomial.eval (fun i => (c i : ℚ)) P := by

  let Q₁ : Polynomial ℚ := MvPolynomial.aeval (fun i => Polynomial.C (c i : ℚ) * Polynomial.X) P
  let Q₂ : Polynomial ℚ := Polynomial.X ^ d * Polynomial.C (MvPolynomial.eval (fun i => (c i : ℚ)) P)
  have hQ₁ : ∀ m : ℤ, Q₁.eval (m : ℚ) = MvPolynomial.eval (fun i => ((m * c i : ℤ) : ℚ)) P := by
    intro m
    change Polynomial.eval (m : ℚ) (MvPolynomial.aeval _ P) = _
    rw [← Polynomial.coe_aeval_eq_eval, MvPolynomial.comp_aeval_apply]
    change MvPolynomial.eval _ P = _
    refine congrArg (fun φ : ι → ℚ => MvPolynomial.eval φ P) (funext fun i => ?_)
    simp only [map_mul, Polynomial.aeval_C, Polynomial.aeval_X, Algebra.algebraMap_self, RingHom.id_apply]
    push_cast
    ring
  have hQ₂ : ∀ m : ℤ, Q₂.eval (m : ℚ) = (m : ℚ) ^ d * MvPolynomial.eval (fun i => (c i : ℚ)) P := by
    intro m
    simp only [Q₂, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_C]
  have hQ : Q₁ = Q₂ := by
    apply Polynomial.eq_of_infinite_eval_eq
    have hsub : (fun m : ℤ => (m : ℚ)) '' {m : ℤ | (m : K) ≠ 0} ⊆ {x | Q₁.eval x = Q₂.eval x} := by
      rintro _ ⟨m, hm, rfl⟩
      change Q₁.eval (m : ℚ) = Q₂.eval (m : ℚ)
      rw [hQ₁, hQ₂, h m c hm]
    exact ((infinite_setOf_intCast_ne_zero K).image Int.cast_injective.injOn).mono hsub
  rw [← hQ₁, ← hQ₂, hQ]

variable (L : RelativeGroupLaw K f) (hc : L.IsCommutative) (g : ℕ)

include hc in

theorem polyFun_of_oneParam (deg : SchemeHomOver f f → ℕ)
    (h1 : ∀ α β : SchemeHomOver f f, IsHom L α → IsHom L β →
      ∃ p : Polynomial ℚ, p.natDegree ≤ 2 * g ∧
        ∀ n : ℤ, ((deg (letI := L.pointCommGroup hc f; α ^ n * β) : ℕ) : ℚ) = p.eval (n : ℚ))
    (h2 : ∀ γ : SchemeHomOver f f, IsHom L γ → ∀ n : ℤ, (n : K) ≠ 0 →
      ((deg (letI := L.pointCommGroup hc f; γ ^ n) : ℕ) : ℚ) = (n : ℚ) ^ (2 * g) * (deg γ : ℚ))
    {ι : Type*} [Fintype ι] (α : ι → SchemeHomOver f f) (hα : ∀ i, IsHom L (α i)) :
    ∃ P : MvPolynomial ι ℚ, P.IsHomogeneous (2 * g) ∧
      ∀ n : ι → ℤ, ((deg (letI := L.pointCommGroup hc f; ∏ i, α i ^ n i) : ℕ) : ℚ) =
        MvPolynomial.eval (fun i => (n i : ℚ)) P := by
  letI := L.pointCommGroup hc f
  let H := homSubgroup L hc
  let M := Additive H
  let F : M → ℚ := fun x => (deg ((Additive.toMul x : H) : SchemeHomOver f f) : ℚ)
  have hF : ∀ x y : M, ∃ p : Polynomial ℚ, p.natDegree ≤ 2 * g ∧
      ∀ n : ℤ, F (n • x + y) = p.eval (n : ℚ) := by
    intro x y
    obtain ⟨p, hp, hpF⟩ := h1 (Additive.toMul x : H) (Additive.toMul y : H) (Additive.toMul x).2
      (Additive.toMul y).2
    exact ⟨p, hp, fun n => hpF n⟩
  let e : ι → M := fun i => Additive.ofMul ⟨α i, hα i⟩
  obtain ⟨P, -, hP⟩ :=
    AddCommGroup.exists_mvPolynomial_totalDegree_le_eval_eq_of_forall_exists_polynomial_zsmul_add F (2 * g)
      hF e
  have hval : ∀ c : ι → ℤ, MvPolynomial.eval (fun i => (c i : ℚ)) P = (deg (∏ i, α i ^ c i) : ℚ) := by
    intro c
    rw [hP c]
    change (deg ((Additive.toMul (∑ i, c i • e i) : H) : SchemeHomOver f f) : ℚ) = _
    congr 2
    rw [toMul_sum]
    simp only [e]
    rw [Subgroup.val_finsetProd]
    rfl
  refine ⟨P, ?_, fun n => (hval n).symm⟩
  apply MvPolynomial.isHomogeneous_of_forall_eval_intCast_mul_eq_pow_mul
  apply eval_intCast_mul_eq_of_ne_zero K P (2 * g)
  intro n c hn
  rw [hval, hval]
  have hprod : (∏ i, α i ^ (n * c i)) = (∏ i, α i ^ c i) ^ n := by
    rw [← Finset.prod_zpow]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [mul_comm, zpow_mul]
  rw [hprod]
  have hhom : IsHom L (∏ i, α i ^ c i) := by
    have hm : (∏ i, α i ^ c i) ∈ H := Subgroup.prod_mem H fun i _ => Subgroup.zpow_mem H (hα i) _
    exact fun {T} t x y => hm t x y
  exact h2 _ hhom n hn

end Assembly

theorem main (K : Type u) [Field K] [IsAlgClosed K] {A : Scheme.{u}} (f : A ⟶ Spec (CommRingCat.of K))
    (L : RelativeGroupLaw K f) (hc : L.IsCommutative) (hA : AbelianSchemePropertyBundle K f)
    (g : ℕ) [SmoothOfRelativeDimension g f]
    {ι : Type*} [Fintype ι] (α : ι → SchemeHomOver f f)
    (hα : ∀ (i : ι) {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of K)) (x y : SchemeHomOver t f),
      NeronModelInfra.schemeHomOverComp (L.mul t x y) (α i) =
        L.mul t (NeronModelInfra.schemeHomOverComp x (α i)) (NeronModelInfra.schemeHomOverComp y (α i))) :
    ∃ P : MvPolynomial ι ℚ, P.IsHomogeneous (2 * g) ∧
      ∀ n : ι → ℤ,
        ((L.endDegree (letI := L.pointCommGroup hc f; ∏ i, α i ^ n i) : ℕ) : ℚ) =
          MvPolynomial.eval (fun i => (n i : ℚ)) P :=
  polyFun_of_oneParam L hc g L.endDegree
    (fun α β hα hβ =>
      GoodReductionJacobian.RelativeGroupLaw.exists_polynomial_eval_eq_endDegree_zpow_mul_of_abelianSchemePropertyBundle
        K f L hc hA g α β hα hβ)
    (fun γ hγ n hn => endDegree_zpow L hc hA g γ hγ n hn) α (fun i => hα i)

end P2mPolyFun

theorem solution
    (K : Type u) [Field K] [IsAlgClosed K] {A : Scheme.{u}} (f : A ⟶ Spec (CommRingCat.of K))
    (L : RelativeGroupLaw K f) (hc : L.IsCommutative) (hA : AbelianSchemePropertyBundle K f)
    (g : ℕ) [SmoothOfRelativeDimension g f]
    {ι : Type*} [Fintype ι] (α : ι → SchemeHomOver f f)
    (hα : ∀ (i : ι) {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of K)) (x y : SchemeHomOver t f),
      NeronModelInfra.schemeHomOverComp (L.mul t x y) (α i) =
        L.mul t (NeronModelInfra.schemeHomOverComp x (α i)) (NeronModelInfra.schemeHomOverComp y (α i))) :
    ∃ P : MvPolynomial ι ℚ, P.IsHomogeneous (2 * g) ∧
      ∀ n : ι → ℤ,
        ((L.endDegree (letI := L.pointCommGroup hc f; ∏ i, α i ^ n i) : ℕ) : ℚ) =
          MvPolynomial.eval (fun i => (n i : ℚ)) P :=
  P2mPolyFun.main K f L hc hA g α hα

end

end S_GoodReductionJacobian_RelativeGroupLaw_exists_isHomogeneous_eval_eq_endDegree_of_abelianSchemePropertyBundle
end P2MW

