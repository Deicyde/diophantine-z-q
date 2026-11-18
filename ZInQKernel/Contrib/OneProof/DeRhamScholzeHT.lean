import ZInQKernel.Contrib.OneProof.DeRhamScholze

/-!
# derham-scholze, part 2 (`ZInQKernel/Contrib/OneProof/DeRhamScholzeHT.lean`, scratch copy
`scratch/derham-scholze/HTFromDR.lean`): de Rham with Hodge jumps in `[0, 1]` implies Hodge–Tate (`DeRhamHodgeTate01`)

The manuscript reads the Hodge–Tate weights of `V_ℓ(A)` off the filtered de Rham comparison
(`lem:de-rham-descent`, L10993-10998: "The two Hodge numbers of `H¹_dR(A/F)` are `2,2`. Consequently the Tate
module has weights `0,0,−1,−1`"). The step behind "consequently" is Fontaine's: a de Rham representation is
Hodge–Tate, with `gr^j D_dR ↪ (ℂ_p(j) ⊗ W)^{G_F}`. Here it is proved for jumps in `[0, 1]` from

* Tate's theorems `ℂ_p(i)^{G_K} = 0` (`i ≠ 0`) and `ℂ_p^{G_K} = K` (`tateTwistInvariants_proof`,
  `axSenTate_proof`, both proved in the tree), and
* `FontaineTwistT`: `B_dR^+` has a uniformizer `t` with `σ(t) = χ(σ) t` (Fontaine's `t = log [ε]`).
-/

set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option warn.classDefReducibility false
set_option synthInstance.maxHeartbeats 400000

namespace DeRhamScholze.HT

open ZInQ.Contrib.G9 ZInQ.Contrib.G9.PkgI4 ZInQ.Contrib.HodgeSplit Module
open scoped TensorProduct

noncomputable section

/-- **GLUE (standard; Fontaine's `t`).** `B_dR^+` has a uniformizer `t` (`𝔪 = (t)`) on which `G_{ℚ_p}` acts by
the cyclotomic character: `σ(t) = χ(σ) t`. Fontaine's `t = log [ε]` (Fontaine, Astérisque 223 (1994), Exp. II,
§1.5; Brinon–Conrad, CMI notes, §4.3; numbers UNVERIFIED). In the tree: `TDict.tt` is `log [ε]` and
`TDict.tt_eq_varpi_mul_unit` makes it a uniformizer; the Galois equivariance is not proved there. -/
def FontaineTwistT : Prop :=
  ∀ (p : ℕ) [Fact p.Prime], ∃ t : BDeRhamPlus 𝓞_ℂ_[p] p,
    IsLocalRing.maximalIdeal (BDeRhamPlus 𝓞_ℂ_[p] p) = Ideal.span {t} ∧
    ∀ σ : GQp p, DR.bdrPlusMap p (oAct p σ) t = qpToPlus p (cycPow p σ 1) * t

variable (p : ℕ) [Fact p.Prime]

/-! ## §1. `θ` on `Fil⁰ B_dR` -/

section Theta

/-- `B_dR^+ → B_dR`. -/
abbrev iota : BDeRhamPlus 𝓞_ℂ_[p] p →+* BdR p := algebraMap (BDeRhamPlus 𝓞_ℂ_[p] p) (BdR p)

theorem iota_injective : Function.Injective (iota p) := BdRInv.alg_injective p

/-- `θ : B_dR^+ → ℂ_p`. -/
abbrev theta : BDeRhamPlus 𝓞_ℂ_[p] p →+* ℂ_[p] := BdrKer.Cp.thetaPlusCp p

theorem ker_theta : RingHom.ker (theta p) = IsLocalRing.maximalIdeal (BDeRhamPlus 𝓞_ℂ_[p] p) := by
  haveI : (RingHom.ker (theta p)).IsMaximal :=
    RingHom.ker_isMaximal_of_surjective _ (BdrKer.Cp.thetaPlusCp_surjective p)
  exact IsLocalRing.eq_maximalIdeal this

theorem mem_filB_zero (x : BdR p) : x ∈ filB p 0 ↔ ∃ b, iota p b = x := by
  constructor
  · rintro ⟨b, -, hb⟩; exact ⟨b, hb⟩
  · rintro ⟨b, hb⟩; exact ⟨b, by simp, hb⟩

/-- The preimage in `B_dR^+` of an element of `Fil⁰ B_dR`. -/
def pre (x : filB p 0) : BDeRhamPlus 𝓞_ℂ_[p] p := ((mem_filB_zero p x).mp x.2).choose

theorem iota_pre (x : filB p 0) : iota p (pre p x) = x := ((mem_filB_zero p x).mp x.2).choose_spec

theorem pre_eq {x : filB p 0} {b : BDeRhamPlus 𝓞_ℂ_[p] p} (h : iota p b = x) : pre p x = b :=
  iota_injective p ((iota_pre p x).trans h.symm)

theorem theta_qpToPlus (c : ℚ_[p]) : theta p (qpToPlus p c) = algebraMap ℚ_[p] ℂ_[p] c :=
  thetaPlusCp_qpToPlus p c

theorem iota_qpToPlus_mul (c : ℚ_[p]) (b : BDeRhamPlus 𝓞_ℂ_[p] p) :
    iota p (qpToPlus p c * b) = c • iota p b := by
  rw [map_mul, Algebra.smul_def]
  rfl

/-- `θ` on `Fil⁰ B_dR = B_dR^+`, as a `ℚ_p`-linear map. -/
def theta0 : filB p 0 →ₗ[ℚ_[p]] ℂ_[p] where
  toFun x := theta p (pre p x)
  map_add' x y := by
    rw [pre_eq p (show iota p (pre p x + pre p y) = ((x + y : filB p 0) : BdR p) by
      rw [map_add, iota_pre, iota_pre, Submodule.coe_add]), map_add]
  map_smul' c x := by
    rw [pre_eq p (show iota p (qpToPlus p c * pre p x) = ((c • x : filB p 0) : BdR p) by
      rw [iota_qpToPlus_mul, iota_pre, Submodule.coe_smul]), map_mul, theta_qpToPlus, RingHom.id_apply,
      Algebra.smul_def]

theorem theta0_spec {x : filB p 0} {b : BDeRhamPlus 𝓞_ℂ_[p] p} (h : iota p b = x) : theta0 p x = theta p b := by
  change theta p (pre p x) = _
  rw [pre_eq p h]

end Theta

/-! ## §2. The graded pieces `gr⁰`, `gr¹` of `D_dR(V^∨) = Hom_{G_F}(V, B_dR)` -/

section FilH

variable {V : Type*} [AddCommGroup V] [Module ℚ_[p] V]

/-- `Fil^j Hom(V, B_dR) = Hom(V, Fil^j B_dR)`. -/
def filH (j : ℕ) : Submodule ℚ_[p] (V →ₗ[ℚ_[p]] BdR p) where
  carrier := {φ | ∀ v, φ v ∈ filB p j}
  zero_mem' v := by simp only [LinearMap.zero_apply]; exact zero_mem _
  add_mem' ha hb v := by simp only [LinearMap.add_apply]; exact add_mem (ha v) (hb v)
  smul_mem' c φ h v := by simp only [LinearMap.smul_apply]; exact (filB p j).smul_mem c (h v)

end FilH

section Graded

variable {p}
variable {t : BDeRhamPlus 𝓞_ℂ_[p] p} (ht : IsLocalRing.maximalIdeal (BDeRhamPlus 𝓞_ℂ_[p] p) = Ideal.span {t})
include ht

theorem mem_filB_iff (j : ℕ) (x : BdR p) : x ∈ filB p j ↔ ∃ c, iota p (t ^ j * c) = x := by
  constructor
  · rintro ⟨b, hb, rfl⟩
    rw [ht, Ideal.span_singleton_pow, Ideal.mem_span_singleton'] at hb
    obtain ⟨c, rfl⟩ := hb
    exact ⟨c, by rw [mul_comm]⟩
  · rintro ⟨c, rfl⟩
    refine ⟨t ^ j * c, ?_, rfl⟩
    rw [ht, Ideal.span_singleton_pow]
    exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _)

theorem t_ne_zero : t ≠ 0 := by
  intro h
  have h1 : IsLocalRing.maximalIdeal (BDeRhamPlus 𝓞_ℂ_[p] p) = ⊥ := by
    rw [ht, h, Ideal.span_singleton_eq_bot]
  have h2 := DeRhamPrint.TDict.varpi_mem_max (p := p)
  rw [h1, Ideal.mem_bot] at h2
  exact DeRhamPrint.TDict.varpi_ne_zero (p := p) h2

theorem mul_left_cancel_t {c c' : BDeRhamPlus 𝓞_ℂ_[p] p} (h : iota p (t * c) = iota p (t * c')) : c = c' :=
  mul_left_cancel₀ (t_ne_zero ht) (iota_injective p h)

/-- The preimage `c` of `x = ι(t c) ∈ Fil¹ B_dR`. -/
def pre1 (x : filB p 1) : BDeRhamPlus 𝓞_ℂ_[p] p := ((mem_filB_iff ht 1 x).mp x.2).choose

theorem iota_pre1 (x : filB p 1) : iota p (t * pre1 ht x) = x := by
  have h := ((mem_filB_iff ht 1 x).mp x.2).choose_spec
  calc iota p (t * pre1 ht x) = iota p (t ^ 1 * pre1 ht x) := by rw [pow_one]
    _ = x := h

theorem pre1_eq {x : filB p 1} {c : BDeRhamPlus 𝓞_ℂ_[p] p} (h : iota p (t * c) = x) : pre1 ht x = c :=
  mul_left_cancel_t ht ((iota_pre1 ht x).trans h.symm)

/-- `gr¹ B_dR → ℂ_p(1)`: `ι(t c) ↦ θ(c)`, a `ℚ_p`-linear map on `Fil¹ B_dR`. -/
def theta1 : filB p 1 →ₗ[ℚ_[p]] ℂ_[p] where
  toFun x := theta p (pre1 ht x)
  map_add' x y := by
    rw [pre1_eq ht (show iota p (t * (pre1 ht x + pre1 ht y)) = ((x + y : filB p 1) : BdR p) by
      rw [mul_add, map_add, iota_pre1, iota_pre1, Submodule.coe_add]), map_add]
  map_smul' c x := by
    rw [pre1_eq ht (show iota p (t * (qpToPlus p c * pre1 ht x)) = ((c • x : filB p 1) : BdR p) by
      rw [mul_left_comm, iota_qpToPlus_mul, iota_pre1, Submodule.coe_smul]), map_mul, theta_qpToPlus, RingHom.id_apply,
      Algebra.smul_def]

theorem theta1_spec {x : filB p 1} {c : BDeRhamPlus 𝓞_ℂ_[p] p} (h : iota p (t * c) = x) :
    theta1 ht x = theta p c := by
  change theta p (pre1 ht x) = _
  rw [pre1_eq ht h]

end Graded

section GrMaps

variable {p}
variable {F : Type*} [Field F] [Algebra ℚ_[p] F] [FiniteDimensional ℚ_[p] F]
variable {V : Type*} [AddCommGroup V] [Module ℚ_[p] V] (ρ : Representation ℚ_[p] (Field.absoluteGaloisGroup F) V)

/-- `Hom(V, Fil^j B_dR) → Hom(V, Fil^j B_dR)` as maps into the subspace. -/
def codR (j : ℕ) : (filH p j : Submodule ℚ_[p] (V →ₗ[ℚ_[p]] BdR p)) →ₗ[ℚ_[p]] (V →ₗ[ℚ_[p]] filB p j) where
  toFun φ := LinearMap.codRestrict (filB p j) φ.1 φ.2
  map_add' _ _ := LinearMap.ext fun _ => Subtype.ext rfl
  map_smul' _ _ := LinearMap.ext fun _ => Subtype.ext rfl

/-- `gr⁰ : Hom(V, Fil⁰ B_dR) → Hom(V, ℂ_p)`, `φ ↦ θ ∘ φ`. -/
def gr0 : (filH p 0 : Submodule ℚ_[p] (V →ₗ[ℚ_[p]] BdR p)) →ₗ[ℚ_[p]] (V →ₗ[ℚ_[p]] ℂ_[p]) :=
  LinearMap.llcomp ℚ_[p] V (filB p 0) ℂ_[p] (theta0 p) ∘ₗ codR 0

theorem gr0_apply (φ : (filH p 0 : Submodule ℚ_[p] (V →ₗ[ℚ_[p]] BdR p))) (v : V) {b : BDeRhamPlus 𝓞_ℂ_[p] p}
    (hb : iota p b = φ.1 v) : gr0 φ v = theta p b :=
  theta0_spec p (x := ⟨φ.1 v, φ.2 v⟩) hb

variable {t : BDeRhamPlus 𝓞_ℂ_[p] p} (ht : IsLocalRing.maximalIdeal (BDeRhamPlus 𝓞_ℂ_[p] p) = Ideal.span {t})

/-- `gr¹ : Hom(V, Fil¹ B_dR) → Hom(V, ℂ_p)`, `φ ↦ θ ∘ (φ/t)`. -/
def gr1 : (filH p 1 : Submodule ℚ_[p] (V →ₗ[ℚ_[p]] BdR p)) →ₗ[ℚ_[p]] (V →ₗ[ℚ_[p]] ℂ_[p]) :=
  LinearMap.llcomp ℚ_[p] V (filB p 1) ℂ_[p] (theta1 ht) ∘ₗ codR 1

theorem gr1_apply (φ : (filH p 1 : Submodule ℚ_[p] (V →ₗ[ℚ_[p]] BdR p))) (v : V) {c : BDeRhamPlus 𝓞_ℂ_[p] p}
    (hc : iota p (t * c) = φ.1 v) : gr1 ht φ v = theta p c :=
  theta1_spec ht (x := ⟨φ.1 v, φ.2 v⟩) hc

/-- `gr⁰` lands in `Hom_{G_F}(V, ℂ_p)`. -/
theorem gr0_mem (φ : (filH p 0 : Submodule ℚ_[p] (V →ₗ[ℚ_[p]] BdR p))) (hφ : φ.1 ∈ ddrSpaceOver p ρ) :
    gr0 φ ∈ htSpaceOver p ρ 0 := by
  intro σ v
  obtain ⟨b, hb⟩ := (mem_filB_zero p _).mp (φ.2 v)
  have h2 : iota p (DR.bdrPlusMap p (oAct p (gfToGqp p F σ)) b) = φ.1 (ρ σ v) := by
    rw [hφ σ v, ← hb]
    exact (BdRInv.bdrAct_algebraMap p _ b).symm
  rw [gr0_apply φ (ρ σ v) h2, gr0_apply φ v hb, cycPow_zero, one_smul]
  exact thetaPlusCp_bdrPlusMap p _ b

/-- `gr¹` lands in `Hom_{G_F}(V, ℂ_p(1))`, given `σ(t) = χ(σ) t`. -/
theorem gr1_mem (hσ : ∀ σ : GQp p, DR.bdrPlusMap p (oAct p σ) t = qpToPlus p (cycPow p σ 1) * t)
    (φ : (filH p 1 : Submodule ℚ_[p] (V →ₗ[ℚ_[p]] BdR p))) (hφ : φ.1 ∈ ddrSpaceOver p ρ) :
    gr1 ht φ ∈ htSpaceOver p ρ 1 := by
  intro σ v
  obtain ⟨c, hc⟩ : ∃ c, iota p (t * c) = φ.1 v := by
    obtain ⟨c, hc⟩ := (mem_filB_iff ht 1 _).mp (φ.2 v)
    exact ⟨c, by rwa [pow_one] at hc⟩
  have h2 : iota p (t * (qpToPlus p (cycPow p (gfToGqp p F σ) 1) *
      DR.bdrPlusMap p (oAct p (gfToGqp p F σ)) c)) = φ.1 (ρ σ v) := by
    rw [hφ σ v, ← hc, BdRInv.bdrAct_algebraMap,
      RingHom.map_mul (DR.bdrPlusMap p (oAct p (gfToGqp p F σ))) t c, hσ]
    congr 1
    ring
  rw [gr1_apply ht φ (ρ σ v) h2, gr1_apply ht φ v hc, map_mul, theta_qpToPlus, thetaPlusCp_bdrPlusMap,
    Algebra.smul_def]

include ht in
theorem mem_filH1_of_gr0 (φ : (filH p 0 : Submodule ℚ_[p] (V →ₗ[ℚ_[p]] BdR p))) (h : gr0 φ = 0) :
    φ.1 ∈ (filH p 1 : Submodule ℚ_[p] (V →ₗ[ℚ_[p]] BdR p)) := by
  intro v
  obtain ⟨b, hb⟩ := (mem_filB_zero p _).mp (φ.2 v)
  have h0 : theta p b = 0 := by rw [← gr0_apply φ v hb, h]; rfl
  have hm : b ∈ IsLocalRing.maximalIdeal (BDeRhamPlus 𝓞_ℂ_[p] p) := by rw [← ker_theta]; exact h0
  rw [ht, Ideal.mem_span_singleton'] at hm
  obtain ⟨c, rfl⟩ := hm
  exact (mem_filB_iff ht 1 _).mpr ⟨c, by rw [pow_one, mul_comm, hb]⟩

theorem mem_filH2_of_gr1 (φ : (filH p 1 : Submodule ℚ_[p] (V →ₗ[ℚ_[p]] BdR p))) (h : gr1 ht φ = 0) :
    φ.1 ∈ (filH p 2 : Submodule ℚ_[p] (V →ₗ[ℚ_[p]] BdR p)) := by
  intro v
  obtain ⟨c, hc⟩ : ∃ c, iota p (t * c) = φ.1 v := by
    obtain ⟨c, hc⟩ := (mem_filB_iff ht 1 _).mp (φ.2 v)
    exact ⟨c, by rwa [pow_one] at hc⟩
  have h0 : theta p c = 0 := by rw [← gr1_apply ht φ v hc, h]; rfl
  have hm : c ∈ IsLocalRing.maximalIdeal (BDeRhamPlus 𝓞_ℂ_[p] p) := by rw [← ker_theta]; exact h0
  rw [ht, Ideal.mem_span_singleton'] at hm
  obtain ⟨d, rfl⟩ := hm
  exact (mem_filB_iff ht 2 _).mpr ⟨d, by rw [← hc]; congr 1; ring⟩

include ht in
/-- **`dim D_dR(V^∨) ≤ dim Hom_{G_F}(V, ℂ_p) + dim Hom_{G_F}(V, ℂ_p(1))`** when the Hodge filtration of
`Hom_{G_F}(V, B_dR)` has its jumps in `[0, 1]` (`gr⁰ ↪ Hom_{G_F}(V, ℂ_p)`, `gr¹ ↪ Hom_{G_F}(V, ℂ_p(1))`). -/
theorem finrank_ddr_le (hσ : ∀ σ : GQp p, DR.bdrPlusMap p (oAct p σ) t = qpToPlus p (cycPow p σ 1) * t)
    (h0 : ddrSpaceOver p ρ ≤ filH p 0) (h2 : ddrSpaceOver p ρ ⊓ filH p 2 = ⊥)
    [FiniteDimensional ℚ_[p] (htSpaceOver p ρ 0)] [FiniteDimensional ℚ_[p] (htSpaceOver p ρ 1)] :
    finrank ℚ_[p] (ddrSpaceOver p ρ) ≤
      finrank ℚ_[p] (htSpaceOver p ρ 0) + finrank ℚ_[p] (htSpaceOver p ρ 1) := by
  letI : AddCommGroup (ddrSpaceOver p ρ) := Module.addCommMonoidToAddCommGroup ℚ_[p]
  let G0 : ddrSpaceOver p ρ →ₗ[ℚ_[p]] htSpaceOver p ρ 0 :=
    LinearMap.codRestrict _ (gr0 ∘ₗ Submodule.inclusion h0) (fun φ => gr0_mem ρ _ φ.2)
  let incl : LinearMap.ker G0 →ₗ[ℚ_[p]] (filH p 1 : Submodule ℚ_[p] (V →ₗ[ℚ_[p]] BdR p)) :=
    { toFun := fun φ => ⟨φ.1.1, mem_filH1_of_gr0 ht ⟨φ.1.1, h0 φ.1.2⟩
        (congrArg Subtype.val (LinearMap.mem_ker.mp φ.2))⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  let G1 : LinearMap.ker G0 →ₗ[ℚ_[p]] htSpaceOver p ρ 1 :=
    LinearMap.codRestrict _ (gr1 ht ∘ₗ incl) (fun φ => gr1_mem ρ ht hσ _ φ.1.2)
  have hG1 : Function.Injective G1 := by
    refine (injective_iff_map_eq_zero G1).mpr fun φ hφ => ?_
    have h3 : gr1 ht (incl φ) = 0 := congrArg Subtype.val hφ
    have h4 : φ.1.1 ∈ ddrSpaceOver p ρ ⊓ filH p 2 := ⟨φ.1.2, mem_filH2_of_gr1 ht (incl φ) h3⟩
    rw [h2, Submodule.mem_bot] at h4
    exact Subtype.ext (Subtype.ext h4)
  have hr1 : Module.rank ℚ_[p] (LinearMap.range G0) ≤ finrank ℚ_[p] (htSpaceOver p ρ 0) := by
    rw [Module.finrank_eq_rank]; exact Submodule.rank_le _
  have hr2 : Module.rank ℚ_[p] (LinearMap.ker G0) ≤ finrank ℚ_[p] (htSpaceOver p ρ 1) := by
    rw [Module.finrank_eq_rank]; exact LinearMap.rank_le_of_injective G1 hG1
  have hrk : Module.rank ℚ_[p] (ddrSpaceOver p ρ) ≤
      ((finrank ℚ_[p] (htSpaceOver p ρ 0) + finrank ℚ_[p] (htSpaceOver p ρ 1) : ℕ) : Cardinal) := by
    rw [← LinearMap.rank_range_add_rank_ker G0, Nat.cast_add]
    exact add_le_add hr1 hr2
  exact Module.finrank_le_of_rank_le hrk

end GrMaps

/-! ## §3. Tate–Sen: `F'`-independent invariant vectors of weights `0` and `1` are `ℂ_p`-independent -/

section TateSen

variable {p}
variable (F : Type*) [Field F] [Algebra ℚ_[p] F] [FiniteDimensional ℚ_[p] F]

/-- `ℂ_p` is an `F'`-algebra (`F' ⊆ ℚ̄_p ⊆ ℂ_p`, Mathlib's instance); its structure map is `iotaCp`. -/
theorem algebraMap_algCp (x : fieldF p F) : algebraMap (fieldF p F) ℂ_[p] x = iotaCp p F x := rfl

variable {F} {V : Type*} [AddCommGroup V] [Module ℚ_[p] V] (ρ : Representation ℚ_[p] (Field.absoluteGaloisGroup F) V)

/-- `Hom_{G_F}(V, ℂ_p(i))` as an `F'`-space (same carrier as `htSpaceOver`). -/
def htF (i : ℤ) : Submodule (fieldF p F) (V →ₗ[ℚ_[p]] ℂ_[p]) where
  carrier := {φ | ∀ σ v, φ (ρ σ v) = cycPow p (gfToGqp p F σ) i • cpAct p (gfToGqp p F σ) (φ v)}
  zero_mem' σ v := by simp
  add_mem' ha hb σ v := by simp only [LinearMap.add_apply, ha σ v, hb σ v, map_add, smul_add]
  smul_mem' c φ hφ σ v := by
    simp only [LinearMap.smul_apply, hφ σ v]
    rw [Algebra.smul_def c (φ v), map_mul, algebraMap_algCp, DeRhamPrint.Direct.cpAct_iotaCp_gf, ← algebraMap_algCp,
      ← Algebra.smul_def, smul_comm]

theorem restrictScalars_htF (i : ℤ) : (htF ρ i).restrictScalars ℚ_[p] = htSpaceOver p ρ i :=
  Submodule.ext fun _ => Iff.rfl

theorem finrank_htSpaceOver_eq (i : ℤ) :
    finrank ℚ_[p] (htSpaceOver p ρ i) = finrank ℚ_[p] F * finrank (fieldF p F) (htF ρ i) := by
  rw [← restrictScalars_htF, ← finrank_fieldF p F,
    ((htF ρ i).restrictScalarsEquiv ℚ_[p] (fieldF p F)).restrictScalars ℚ_[p] |>.finrank_eq]
  have : Module.Free (fieldF p F) (htF ρ i) := Module.Free.of_divisionRing _ _
  exact (Module.finrank_mul_finrank ℚ_[p] (fieldF p F) (htF ρ i)).symm

theorem cycPow_add (σ : GQp p) (i j : ℤ) : cycPow p σ (i + j) = cycPow p σ i * cycPow p σ j := by
  simp only [cycPow, zpow_add, Units.val_mul, PadicInt.coe_mul]

theorem smul_eq_iota (c : fieldF p F) (φ : V →ₗ[ℚ_[p]] ℂ_[p]) : c • φ = iotaCp p F c • φ :=
  LinearMap.ext fun v => by simp only [LinearMap.smul_apply, Algebra.smul_def, algebraMap_algCp]; rfl

variable (hT : TateTwistInvariants) (hA : AxSenTate)
include hT in
theorem twist_fixed_eq_zero {i : ℤ} (hi : i ≠ 0) {x : ℂ_[p]}
    (h : ∀ σ : Field.absoluteGaloisGroup F, cycPow p (gfToGqp p F σ) i • cpAct p (gfToGqp p F σ) x = x) :
    x = 0 := by
  apply hT p (fieldF p F) i hi x
  intro τ hτ
  have : τ ∈ Set.range (gfToGqp p F) := by rw [range_gfToGqp_eq]; exact hτ
  obtain ⟨σ, rfl⟩ := this
  exact h σ

include hA in
theorem fixed_mem_range {x : ℂ_[p]} (h : ∀ σ : Field.absoluteGaloisGroup F, cpAct p (gfToGqp p F σ) x = x) :
    ∃ y : fieldF p F, x = iotaCp p F y := by
  obtain ⟨y, hy⟩ := hA p (fieldF p F) x (fun τ hτ => by
    have : τ ∈ Set.range (gfToGqp p F) := by rw [range_gfToGqp_eq]; exact hτ
    obtain ⟨σ, rfl⟩ := this
    exact h σ)
  refine ⟨y, hy.trans ?_⟩
  simp only [iotaCp, AlgHom.comp_apply, IsScalarTower.coe_toAlgHom']
  rw [← PadicComplex.coe_eq]
  rfl

/-- The weight of an index: `0` on `Fin a`, `1` on `Fin b`. -/
def wt {a b : ℕ} : Fin a ⊕ Fin b → ℤ := Sum.elim (fun _ => 0) (fun _ => 1)

include hT hA in
/-- **Tate–Sen.** `F'`-linearly independent families in `Hom_{G_F}(V, ℂ_p)` and in `Hom_{G_F}(V, ℂ_p(1))`
together are `ℂ_p`-linearly independent in `Hom_{ℚ_p}(V, ℂ_p)` (minimal relation; Tate's `ℂ_p(±1)^{G_F} = 0` and
`ℂ_p^{G_F} = F'`). -/
theorem linIndep_two {a b : ℕ} (x : Fin a → htF ρ 0) (y : Fin b → htF ρ 1)
    (hx : LinearIndependent (fieldF p F) x) (hy : LinearIndependent (fieldF p F) y) :
    LinearIndependent ℂ_[p]
      (Sum.elim (fun i => (x i : V →ₗ[ℚ_[p]] ℂ_[p])) (fun j => (y j : V →ₗ[ℚ_[p]] ℂ_[p]))) := by
  classical
  set z : Fin a ⊕ Fin b → (V →ₗ[ℚ_[p]] ℂ_[p]) :=
    Sum.elim (fun i => (x i : V →ₗ[ℚ_[p]] ℂ_[p])) (fun j => (y j : V →ₗ[ℚ_[p]] ℂ_[p])) with hz
  have hzk : ∀ k σ v, z k (ρ σ v) = cycPow p (gfToGqp p F σ) (wt k) • cpAct p (gfToGqp p F σ) (z k v) := by
    rintro (i | j) σ v
    · exact (x i).2 σ v
    · exact (y j).2 σ v
  rw [Fintype.linearIndependent_iff]
  suffices H : ∀ (N : ℕ) (c : Fin a ⊕ Fin b → ℂ_[p]), (Finset.univ.filter fun k => c k ≠ 0).card = N →
      c ≠ 0 → ∑ k, c k • z k = 0 → False by
    intro c hc
    by_contra hne
    push_neg at hne
    obtain ⟨k, hk⟩ := hne
    exact H _ c rfl (fun h0 => hk (congrFun h0 k)) hc
  intro N
  induction N using Nat.strong_induction_on with
  | _ N ih =>
  intro c hcard hc0 hrel
  obtain ⟨j, hj⟩ : ∃ j, c j ≠ 0 := by
    by_contra h
    push_neg at h
    exact hc0 (funext h)
  set c' : Fin a ⊕ Fin b → ℂ_[p] := fun k => (c j)⁻¹ * c k with hc'
  have hc'j : c' j = 1 := inv_mul_cancel₀ hj
  have hrel' : ∑ k, c' k • z k = 0 := by
    simp only [hc', mul_smul, ← Finset.smul_sum, hrel, smul_zero]
  have hsupp' : ∀ k, c' k ≠ 0 ↔ c k ≠ 0 := fun k => by
    simp only [hc', ne_eq, mul_eq_zero, inv_eq_zero, hj, false_or]
  -- the twisted relation: `Σ_k χ(σ)^{wt j - wt k} σ(c'_k) z_k = 0`
  set e : Field.absoluteGaloisGroup F → Fin a ⊕ Fin b → ℂ_[p] := fun σ k =>
    algebraMap ℚ_[p] ℂ_[p] (cycPow p (gfToGqp p F σ) (wt j - wt k)) * cpAct p (gfToGqp p F σ) (c' k) with he
  have htw : ∀ σ, ∑ k, e σ k • z k = 0 := by
    intro σ
    refine LinearMap.ext fun w => ?_
    obtain ⟨v, rfl⟩ : ∃ v, ρ σ v = w := ⟨ρ σ⁻¹ w, by
      rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]⟩
    have h0 : ∑ k, c' k * z k v = 0 := by
      have := LinearMap.congr_fun hrel' v
      simpa using this
    have h1 := congrArg (fun y => algebraMap ℚ_[p] ℂ_[p] (cycPow p (gfToGqp p F σ) (wt j)) *
      cpAct p (gfToGqp p F σ) y) h0
    simp only [map_sum, map_mul, map_zero, mul_zero, Finset.mul_sum] at h1
    rw [LinearMap.sum_apply, LinearMap.zero_apply, ← h1]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [LinearMap.smul_apply, hzk, he, smul_eq_mul, Algebra.smul_def]
    have hcy : cycPow p (gfToGqp p F σ) (wt j) =
        cycPow p (gfToGqp p F σ) (wt j - wt k) * cycPow p (gfToGqp p F σ) (wt k) := by
      rw [← cycPow_add, sub_add_cancel]
    rw [hcy, map_mul]
    ring
  by_cases hfix : ∀ σ k, e σ k = c' k
  · -- all coefficients are fixed: they vanish off the weight of `j` and lie in `F'` on it
    have hzero : ∀ k, wt k ≠ wt j → c' k = 0 := fun k hk =>
      twist_fixed_eq_zero hT (i := wt j - wt k) (sub_ne_zero.mpr (Ne.symm hk)) (fun σ => by
        rw [Algebra.smul_def]; exact hfix σ k)
    have hin : ∀ k, wt k = wt j → ∃ d : fieldF p F, c' k = iotaCp p F d := fun k hk =>
      fixed_mem_range hA (fun σ => by
        have := hfix σ k
        simp only [he, hk, sub_self, cycPow_zero, map_one, one_mul] at this
        exact this)
    obtain ⟨j0, hj0⟩ | ⟨j0, hj0⟩ : (∃ j0, j = Sum.inl j0) ∨ (∃ j0, j = Sum.inr j0) := by
      rcases j with j0 | j0
      exacts [Or.inl ⟨j0, rfl⟩, Or.inr ⟨j0, rfl⟩]
    · choose d hd using fun i : Fin a => hin (Sum.inl i) (by rw [hj0]; rfl)
      have hsum : ∑ i, d i • x i = 0 := by
        apply Subtype.ext
        rw [Submodule.coe_sum, Submodule.coe_zero, ← hrel', Fintype.sum_sum_type]
        have h2 : ∑ i : Fin b, c' (Sum.inr i) • z (Sum.inr i) = 0 :=
          Finset.sum_eq_zero fun i _ => by
            rw [hzero (Sum.inr i) (by rw [hj0]; simp [wt]), zero_smul]
        rw [h2, add_zero]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [Submodule.coe_smul, smul_eq_iota, ← hd i]
        rfl
      have := (Fintype.linearIndependent_iff.mp hx) d hsum j0
      have h1 : iotaCp p F (d j0) = 1 := by rw [← hd j0, ← hj0]; exact hc'j
      rw [this, map_zero] at h1
      exact zero_ne_one h1
    · choose d hd using fun i : Fin b => hin (Sum.inr i) (by rw [hj0]; rfl)
      have hsum : ∑ i, d i • y i = 0 := by
        apply Subtype.ext
        rw [Submodule.coe_sum, Submodule.coe_zero, ← hrel', Fintype.sum_sum_type]
        have h2 : ∑ i : Fin a, c' (Sum.inl i) • z (Sum.inl i) = 0 :=
          Finset.sum_eq_zero fun i _ => by
            rw [hzero (Sum.inl i) (by rw [hj0]; simp [wt]), zero_smul]
        rw [h2, zero_add]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [Submodule.coe_smul, smul_eq_iota, ← hd i]
        rfl
      have := (Fintype.linearIndependent_iff.mp hy) d hsum j0
      have h1 : iotaCp p F (d j0) = 1 := by rw [← hd j0, ← hj0]; exact hc'j
      rw [this, map_zero] at h1
      exact zero_ne_one h1
  · push_neg at hfix
    obtain ⟨σ, k₀, hk₀⟩ := hfix
    set d : Fin a ⊕ Fin b → ℂ_[p] := fun k => e σ k - c' k with hd
    have hdrel : ∑ k, d k • z k = 0 := by
      simp only [hd, sub_smul, Finset.sum_sub_distrib, htw σ, hrel', sub_zero]
    have hdj : d j = 0 := by
      simp only [hd, he, hc'j, sub_self, show cycPow p (gfToGqp p F σ) 0 = 1 from cycPow_zero p _, map_one,
        one_mul]
    have hd0 : d ≠ 0 := fun h0 => hk₀ (sub_eq_zero.mp (congrFun h0 k₀))
    have hsub : (Finset.univ.filter fun k => d k ≠ 0) ⊂ (Finset.univ.filter fun k => c k ≠ 0) := by
      refine Finset.ssubset_iff_of_subset (fun k hk => ?_) |>.mpr ⟨j, ?_, ?_⟩
      · simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hk ⊢
        rw [← hsupp']
        intro h0
        apply hk
        simp only [hd, he, h0, map_zero, mul_zero, sub_zero]
      · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        exact hj
      · simp only [Finset.mem_filter, Finset.mem_univ, true_and, hdj, ne_eq, not_true_eq_false,
          not_false_eq_true]
    exact ih _ (hcard ▸ Finset.card_lt_card hsub) d rfl hd0 hdrel

end TateSen

/-! ## §4. Assembly: `DeRhamHodgeTate01` from `FontaineTwistT` -/

section Assembly

variable {p}
variable {F : Type*} [Field F] [Algebra ℚ_[p] F] [FiniteDimensional ℚ_[p] F]
variable {V : Type*} [AddCommGroup V] [Module ℚ_[p] V] [FiniteDimensional ℚ_[p] V]
  (ρ : Representation ℚ_[p] (Field.absoluteGaloisGroup F) V)

/-- `B_dR ⊗ V^∨ ≅ Hom(V, B_dR)` carries `D_dR(V^∨)` onto `Hom_{G_F}(V, B_dR)` (hodge-split's argument). -/
theorem map_ddrFam_dual :
    Submodule.map (tensorDualEquiv p).toLinearMap (ddrFam p (fun σ => ρ.dual σ)) = ddrSpaceOver p ρ := by
  ext φ
  constructor
  · rintro ⟨x, hx, rfl⟩ σ w
    have h := congrArg (fun y => tensorDualEquiv p y (ρ σ w)) (hx σ)
    simp only at h
    rw [tensorDualEquiv_map, ← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one,
      Module.End.one_apply] at h
    exact h.symm
  · intro hφ
    refine ⟨(tensorDualEquiv p).symm φ, fun σ => ?_, by simp⟩
    apply (tensorDualEquiv p).injective
    refine LinearMap.ext fun v => ?_
    rw [tensorDualEquiv_map, LinearEquiv.apply_symm_apply]
    have := hφ σ (ρ σ⁻¹ v)
    rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply] at this
    rw [this]
    rfl

/-- ... and `Fil^j B_dR ⊗ V^∨` onto `Hom(V, Fil^j B_dR)`. -/
theorem map_filRange_dual (j : ℕ) :
    Submodule.map (tensorDualEquiv p).toLinearMap
        (LinearMap.range (TensorProduct.map (filB p j).subtype
          (LinearMap.id : Module.Dual ℚ_[p] V →ₗ[ℚ_[p]] Module.Dual ℚ_[p] V))) = filH p j := by
  apply le_antisymm
  · rintro _ ⟨_, ⟨y, rfl⟩, rfl⟩ v
    induction y using TensorProduct.inductionOn with
    | tmul b f =>
      change tensorDualEquiv p ((b : BdR p) ⊗ₜ f) v ∈ filB p j
      rw [tensorDualEquiv_tmul]
      exact (filB p j).smul_mem _ b.2
    | add y y' hy hy' =>
      rw [map_add, map_add, LinearMap.add_apply]
      exact add_mem hy hy'
  · intro φ hφ
    classical
    let bV := Module.finBasis ℚ_[p] V
    refine ⟨∑ i, ((φ (bV i) : BdR p) ⊗ₜ bV.dualBasis i),
      ⟨∑ i, (⟨φ (bV i), hφ (bV i)⟩ : filB p j) ⊗ₜ bV.dualBasis i, by simp [map_sum]⟩, ?_⟩
    apply bV.ext
    intro k
    simp only [LinearEquiv.coe_coe, map_sum, LinearMap.sum_apply, tensorDualEquiv_tmul,
      Basis.dualBasis_apply_self, ite_smul, one_smul, zero_smul, Finset.sum_ite_eq, Finset.mem_univ, if_true]

end Assembly

section Final

variable {p}
variable {F : Type*} [Field F] [Algebra ℚ_[p] F] [FiniteDimensional ℚ_[p] F]
variable {V : Type*} [AddCommGroup V] [Module ℚ_[p] V] [FiniteDimensional ℚ_[p] V]
  (ρ : Representation ℚ_[p] (Field.absoluteGaloisGroup F) V)

/-- `Hom_{ℚ_p}(V, ℂ_p)` has `ℂ_p`-dimension `dim V`. -/
theorem finrank_hom : finrank ℂ_[p] (V →ₗ[ℚ_[p]] ℂ_[p]) = finrank ℚ_[p] V := by
  rw [← ((Module.finBasis ℚ_[p] V).constr ℂ_[p]).finrank_eq, Module.finrank_fin_fun]

theorem fd_hom : FiniteDimensional ℂ_[p] (V →ₗ[ℚ_[p]] ℂ_[p]) :=
  LinearEquiv.finiteDimensional ((Module.finBasis ℚ_[p] V).constr ℂ_[p])

/-- The bound `dim_{F'} Hom_{G_F}(V, ℂ_p(i)) ≤ dim V` (`i = 0, 1`), with finiteness. -/
theorem fd_htF_aux (hT : TateTwistInvariants) (hA : AxSenTate) (i : ℤ)
    (hb : ∀ s : Finset (htF ρ i), (LinearIndependent (fieldF p F) fun k : s => (k : htF ρ i)) →
      s.card ≤ finrank ℚ_[p] V) :
    FiniteDimensional (fieldF p F) (htF ρ i) ∧ finrank (fieldF p F) (htF ρ i) ≤ finrank ℚ_[p] V := by
  have hrank := rank_le hb
  have hfin : FiniteDimensional (fieldF p F) (htF ρ i) :=
    Module.rank_lt_aleph0_iff.mp (lt_of_le_of_lt hrank (Cardinal.natCast_lt_aleph0))
  exact ⟨hfin, Module.finrank_le_of_rank_le hrank⟩

/-- The bound `dim_{F'} Hom_{G_F}(V, ℂ_p) ≤ dim V`, with finiteness. -/
theorem fd_htF0 (hT : TateTwistInvariants) (hA : AxSenTate) :
    FiniteDimensional (fieldF p F) (htF ρ 0) ∧ finrank (fieldF p F) (htF ρ 0) ≤ finrank ℚ_[p] V := by
  haveI := fd_hom (p := p) (V := V)
  refine fd_htF_aux ρ hT hA 0 fun s hs => ?_
  let e := s.equivFin
  have hs' : LinearIndependent (fieldF p F) (fun k : Fin s.card => ((e.symm k : s) : htF ρ 0)) :=
    hs.comp e.symm e.symm.injective
  have h := (linIndep_two ρ hT hA (fun k : Fin s.card => ((e.symm k : s) : htF ρ 0))
    (Fin.elim0 : Fin 0 → htF ρ 1) hs' (linearIndependent_empty_type)).fintype_card_le_finrank
  rw [Fintype.card_sum, Fintype.card_fin, Fintype.card_fin, add_zero, finrank_hom] at h
  exact h

/-- The bound `dim_{F'} Hom_{G_F}(V, ℂ_p(1)) ≤ dim V`, with finiteness. -/
theorem fd_htF1 (hT : TateTwistInvariants) (hA : AxSenTate) :
    FiniteDimensional (fieldF p F) (htF ρ 1) ∧ finrank (fieldF p F) (htF ρ 1) ≤ finrank ℚ_[p] V := by
  haveI := fd_hom (p := p) (V := V)
  refine fd_htF_aux ρ hT hA 1 fun s hs => ?_
  let e := s.equivFin
  have hs' : LinearIndependent (fieldF p F) (fun k : Fin s.card => ((e.symm k : s) : htF ρ 1)) :=
    hs.comp e.symm e.symm.injective
  have h := (linIndep_two ρ hT hA (Fin.elim0 : Fin 0 → htF ρ 0)
    (fun k : Fin s.card => ((e.symm k : s) : htF ρ 1)) (linearIndependent_empty_type) hs').fintype_card_le_finrank
  rw [Fintype.card_sum, Fintype.card_fin, Fintype.card_fin, zero_add, finrank_hom] at h
  exact h

theorem fd_htSpaceOver (i : ℤ) [FiniteDimensional (fieldF p F) (htF ρ i)] :
    FiniteDimensional ℚ_[p] (htSpaceOver p ρ i) := by
  haveI : Module.Finite ℚ_[p] (htF ρ i) := Module.Finite.trans (fieldF p F) (htF ρ i)
  rw [← restrictScalars_htF]
  exact LinearEquiv.finiteDimensional
    (((htF ρ i).restrictScalarsEquiv ℚ_[p] (fieldF p F)).restrictScalars ℚ_[p]).symm

/-- The semilinear action `T_σ f = σ ∘ f ∘ ρ(σ)⁻¹` on `Hom_{ℚ_p}(V, ℂ_p)`. -/
abbrev tAct (σ : Field.absoluteGaloisGroup F) (f : V →ₗ[ℚ_[p]] ℂ_[p]) : V →ₗ[ℚ_[p]] ℂ_[p] :=
  cpLin p (gfToGqp p F σ) ∘ₗ f ∘ₗ ρ σ⁻¹

theorem tAct_sum {ι : Type*} [Fintype ι] (σ : Field.absoluteGaloisGroup F) (c : ι → ℂ_[p])
    (z : ι → V →ₗ[ℚ_[p]] ℂ_[p]) :
    tAct ρ σ (∑ k, c k • z k) = ∑ k, cpAct p (gfToGqp p F σ) (c k) • tAct ρ σ (z k) := by
  refine LinearMap.ext fun w => ?_
  simp only [LinearMap.comp_apply, LinearMap.sum_apply, LinearMap.smul_apply,
    cpLin_apply, map_sum, smul_eq_mul, map_mul]

theorem tAct_of_mem {i : ℤ} {f : V →ₗ[ℚ_[p]] ℂ_[p]} (hf : f ∈ htSpaceOver p ρ i) (σ : Field.absoluteGaloisGroup F) :
    tAct ρ σ f = algebraMap ℚ_[p] ℂ_[p] (cycPow p (gfToGqp p F σ) (-i)) • f := by
  refine LinearMap.ext fun w => ?_
  obtain ⟨v, rfl⟩ : ∃ v, ρ σ v = w := ⟨ρ σ⁻¹ w, by
    rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]⟩
  have hv : ρ σ⁻¹ (ρ σ v) = v := by
    rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]
  simp only [LinearMap.comp_apply, cpLin_apply, hv, LinearMap.smul_apply, smul_eq_mul]
  rw [hf σ v, Algebra.smul_def, ← mul_assoc, ← map_mul, ← cycPow_add, neg_add_cancel,
    cycPow_zero, map_one, one_mul]

/-- **`DeRhamHodgeTate01` from `FontaineTwistT`** (with Tate's two theorems, proved in the tree). -/
theorem deRhamHodgeTate01_of_fontaineT (hF : FontaineTwistT) : DeRhamHodgeTate01 := by
  intro p _ F _ _ _ V _ _ ρ h1 h2
  obtain ⟨t, ht, hσ⟩ := hF p
  obtain ⟨hfdD, hrank⟩ := h1
  haveI : FiniteDimensional ℚ_[p] V := (Module.finite_dual_iff (K := ℚ_[p]) (V := V)).mp hfdD
  have hT := ZInQ.Contrib.CloudB3W11.tateTwistInvariants_proof
  have hA := ZInQ.Contrib.CloudB3W11.axSenTate_proof
  -- `dim_{ℚ_p} Hom_{G_F}(V, B_dR) = [F:ℚ_p] dim V`
  have hD : finrank ℚ_[p] (ddrSpaceOver p ρ) = finrank ℚ_[p] F * finrank ℚ_[p] V := by
    rw [← map_ddrFam_dual ρ, LinearEquiv.finrank_map_eq, hrank, Subspace.dual_finrank_eq]
  -- the Hodge filtration in Hom form
  have hfil : ∀ j, Submodule.map (tensorDualEquiv p).toLinearMap (filD p (fun σ => ρ.dual σ) j) =
      ddrSpaceOver p ρ ⊓ filH p j := by
    intro j
    rw [filD, Submodule.map_inf _ (tensorDualEquiv p).injective, map_ddrFam_dual, map_filRange_dual]
  obtain ⟨hf0, hf2⟩ := h2
  have h0 : ddrSpaceOver p ρ ≤ filH p 0 := by
    have := hfil 0
    rw [hf0, map_ddrFam_dual] at this
    exact inf_eq_left.mp this.symm
  have h2' : ddrSpaceOver p ρ ⊓ filH p 2 = ⊥ := by
    rw [← hfil 2]
    exact (congrArg _ hf2).trans (Submodule.map_bot _)
  -- the `F'`-dimensions `a`, `b`
  obtain ⟨hfa, hale⟩ := fd_htF0 ρ hT hA
  obtain ⟨hfb, hble⟩ := fd_htF1 ρ hT hA
  haveI := hfa
  haveI := hfb
  haveI := fd_htSpaceOver ρ (0 : ℤ)
  haveI := fd_htSpaceOver ρ (1 : ℤ)
  haveI := fd_hom (p := p) (V := V)
  set a := finrank (fieldF p F) (htF ρ 0)
  set b := finrank (fieldF p F) (htF ρ 1)
  have hle := finrank_ddr_le ρ ht hσ h0 h2'
  rw [hD, finrank_htSpaceOver_eq, finrank_htSpaceOver_eq, ← mul_add] at hle
  have hdab : finrank ℚ_[p] V ≤ a + b := Nat.le_of_mul_le_mul_left hle Module.finrank_pos
  -- the `ℂ_p`-basis
  let bx := Module.finBasis (fieldF p F) (htF ρ 0)
  let by' := Module.finBasis (fieldF p F) (htF ρ 1)
  have hz := linIndep_two ρ hT hA (fun i => bx i) (fun i => by' i) bx.linearIndependent by'.linearIndependent
  have hcard : Fintype.card (Fin a ⊕ Fin b) = finrank ℂ_[p] (V →ₗ[ℚ_[p]] ℂ_[p]) := by
    rw [Fintype.card_sum, Fintype.card_fin, Fintype.card_fin, finrank_hom]
    exact le_antisymm (by have := hz.fintype_card_le_finrank; rwa [Fintype.card_sum, Fintype.card_fin,
      Fintype.card_fin, finrank_hom] at this) hdab
  let B := basisOfLinearIndependentOfCardEqFinrank' _ hz hcard
  refine ⟨a, b, B.equivFun.trans (LinearEquiv.sumArrowLequivProdArrow (Fin a) (Fin b) ℂ_[p] ℂ_[p]), ?_⟩
  intro σ f
  -- `T_σ f = Σ_k σ(c_k) χ(σ)^{-wt k} z_k`
  have hB : ∀ k, (B k) ∈ htSpaceOver p ρ (wt k) := by
    rintro (i | i)
    · simp only [B, coe_basisOfLinearIndependentOfCardEqFinrank', Sum.elim_inl]; exact (bx i).2
    · simp only [B, coe_basisOfLinearIndependentOfCardEqFinrank', Sum.elim_inr]; exact (by' i).2
  have hexp : tAct ρ σ f = ∑ k, (cpAct p (gfToGqp p F σ) (B.repr f k) *
      algebraMap ℚ_[p] ℂ_[p] (cycPow p (gfToGqp p F σ) (-wt k))) • B k := by
    conv_lhs => rw [← B.sum_repr f]
    rw [tAct_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [tAct_of_mem ρ (hB k), smul_smul, mul_comm]
  have hrep : B.repr (tAct ρ σ f) = fun k => cpAct p (gfToGqp p F σ) (B.repr f k) *
      algebraMap ℚ_[p] ℂ_[p] (cycPow p (gfToGqp p F σ) (-wt k)) := by
    rw [hexp]
    ext k
    rw [B.repr_sum_self]
  change (LinearEquiv.sumArrowLequivProdArrow (Fin a) (Fin b) ℂ_[p] ℂ_[p]) (B.equivFun (tAct ρ σ f)) = _
  rw [Basis.equivFun_apply, hrep]
  ext k
  · simp only [LinearEquiv.sumArrowLequivProdArrow_apply_fst, Function.comp_apply, wt, Sum.elim_inl, neg_zero,
      cycPow_zero, map_one, mul_one, LinearEquiv.trans_apply, Basis.equivFun_apply]
  · simp only [LinearEquiv.sumArrowLequivProdArrow_apply_snd, Function.comp_apply, wt, Sum.elim_inr,
      LinearEquiv.trans_apply, Basis.equivFun_apply, Algebra.smul_def]
    ring

end Final

end

end DeRhamScholze.HT
