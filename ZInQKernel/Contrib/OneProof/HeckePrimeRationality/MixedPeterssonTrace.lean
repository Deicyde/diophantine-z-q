import ZInQKernel.Contrib.TauCeti.NumberTheory.ModularForms.Petersson.Trace
import ZInQKernel.Contrib.OneProof.HeckePrimeRationality.MixedAllLevelTrace
import ZInQKernel.Contrib.OneProof.HeckePrimeRationality.AllLevelPrincipalProductTrace

/-!
# Petersson pairing of a cusp form with a modular form, and the trace

For a finite-index `Γ ≤ SL(2, ℤ)`, a cusp form `f` and a modular form `G` (not necessarily
cuspidal) for `Γ`, `cuspModPairing f G` is the sum over the cosets of `Γ·{±I}` of the
level-one-domain Petersson integrals of the correspondingly slashed functions. Each integral
converges because one argument is cuspidal. The pairing is conjugate-linear in `f` and linear in
`G`.

Main results:

* `cuspModPairing_sum_slash_right`, `cuspModPairing_trace_right`: for `Γ' ≤ Γ` of finite index
  with `-I ∈ Γ → -I ∈ Γ'`, the actual trace of a modular form `G` for `Γ'` satisfies
  `⟪f, tr G⟫_Γ = ⟪res f, G⟫_Γ'`.
* `principal_pairing_normalizedTrace`: for `3 ≤ N ∣ M`,
  `⟪f, traceIndex⁻¹ • tr G⟫_{Γ(N)} = traceIndex⁻¹ · ⟪res f, G⟫_{Γ(M)}`, with nonzero relative index.
* Orthogonality transport: a cusp form of level `N` that is orthogonal to the same-level mixed
  space (weight three), or to the admissible degree-two product span (weight two), has its
  restriction orthogonal to the corresponding space at every level `M` divisible by `N`.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
open UpperHalfPlane ModularGroup Matrix.SpecialLinearGroup MeasureTheory
open scoped MatrixGroups ModularForm ComplexConjugate Pointwise

namespace ZInQ.Contrib.HeckePrimeRationality.MixedPeterssonTrace

variable {k : ℤ}

/-! ### The pairing -/

/-- The Petersson pairing of a cusp form with a modular form for a finite-index `Γ`. -/
def cuspModPairing {Γ : Subgroup SL(2, ℤ)} [Γ.FiniteIndex] (f : CuspForm (Γ.map (mapGL ℝ)) k)
    (G : _root_.ModularForm (Γ.map (mapGL ℝ)) k) : ℂ :=
  ∑ q : SL(2, ℤ) ⧸ Γ.withCenter,
    UpperHalfPlane.peterssonInner k fd (⇑f ∣[k] (q.out)⁻¹) (⇑G ∣[k] (q.out)⁻¹)

theorem cuspModPairing_def {Γ : Subgroup SL(2, ℤ)} [Γ.FiniteIndex]
    (f : CuspForm (Γ.map (mapGL ℝ)) k) (G : _root_.ModularForm (Γ.map (mapGL ℝ)) k) :
    cuspModPairing f G = ∑ q : SL(2, ℤ) ⧸ Γ.withCenter,
      UpperHalfPlane.peterssonInner k fd (⇑f ∣[k] (q.out)⁻¹) (⇑G ∣[k] (q.out)⁻¹) := rfl

theorem cuspModPairing_smul_right {Γ : Subgroup SL(2, ℤ)} [Γ.FiniteIndex] (c : ℂ)
    (f : CuspForm (Γ.map (mapGL ℝ)) k) (G : _root_.ModularForm (Γ.map (mapGL ℝ)) k) :
    cuspModPairing f (c • G) = c * cuspModPairing f G := by
  simp only [cuspModPairing, Finset.mul_sum]
  refine Finset.sum_congr rfl fun q _ => ?_
  rw [FunLike.coe_smul, ModularForm.SL_smul_slash, peterssonInner_smul_right]

theorem cuspModPairing_add_right {Γ : Subgroup SL(2, ℤ)} [Γ.FiniteIndex]
    (f : CuspForm (Γ.map (mapGL ℝ)) k) (G₁ G₂ : _root_.ModularForm (Γ.map (mapGL ℝ)) k) :
    cuspModPairing f (G₁ + G₂) = cuspModPairing f G₁ + cuspModPairing f G₂ := by
  simp only [cuspModPairing, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun q _ => ?_
  rw [FunLike.coe_add, SlashAction.add_slash]
  exact peterssonInner_add_right k fd _ _ _
    (integrableOn_petersson_slash_left k _ f G₁ _)
    (integrableOn_petersson_slash_left k _ f G₂ _)

theorem cuspModPairing_zero_right {Γ : Subgroup SL(2, ℤ)} [Γ.FiniteIndex]
    (f : CuspForm (Γ.map (mapGL ℝ)) k) :
    cuspModPairing f (0 : _root_.ModularForm (Γ.map (mapGL ℝ)) k) = 0 := by
  have h := cuspModPairing_smul_right (0 : ℂ) f 0
  rwa [zero_smul, zero_mul] at h

/-- The pairing against a fixed cusp form is a linear functional in the modular form. -/
def cuspModPairingₗ {Γ : Subgroup SL(2, ℤ)} [Γ.FiniteIndex] (f : CuspForm (Γ.map (mapGL ℝ)) k) :
    _root_.ModularForm (Γ.map (mapGL ℝ)) k →ₗ[ℂ] ℂ where
  toFun := cuspModPairing f
  map_add' := cuspModPairing_add_right f
  map_smul' c G := cuspModPairing_smul_right c f G

/-! ### Independence of coset representatives -/

theorem exists_slash_eq_smul_of_mem_withCenter {Γ : Subgroup SL(2, ℤ)} {γ : SL(2, ℤ)}
    (hγ : γ ∈ Γ.withCenter) :
    ∃ c : ℂ, conj c * c = 1 ∧
      (∀ f : CuspForm (Γ.map (mapGL ℝ)) k, ⇑f ∣[k] γ = c • ⇑f) ∧
      (∀ G : _root_.ModularForm (Γ.map (mapGL ℝ)) k, ⇑G ∣[k] γ = c • ⇑G) := by
  obtain ⟨γ', hγ', hcase⟩ := Subgroup.mem_withCenter_iff_exists_eq_or_eq_neg.mp hγ
  rcases hcase with rfl | rfl
  · exact ⟨1, by simp, fun f => by rw [SlashInvariantFormClass.SL_slash_eq f _ hγ', one_smul],
      fun G => by rw [SlashInvariantFormClass.SL_slash_eq G _ hγ', one_smul]⟩
  · have hcoe : ((-1 : SL(2, ℤ)) : GL (Fin 2) ℝ) = -1 := mapGL_neg_one
    refine ⟨(-1 : ℂ) ^ k, ?_, fun f => ?_, fun G => ?_⟩
    · have hreal : conj ((-1 : ℂ) ^ k) = (-1 : ℂ) ^ k := by simp
      rw [hreal, ← zpow_add₀ (by norm_num : (-1 : ℂ) ≠ 0), ← two_mul, zpow_mul]
      norm_num
    · rw [← mul_neg_one γ', SlashAction.slash_mul, ModularForm.SL_slash (γ := (-1 : SL(2, ℤ))),
        hcoe, ModularForm.slash_neg_one, SlashInvariantFormClass.SL_slash_eq f _ hγ']
    · rw [← mul_neg_one γ', SlashAction.slash_mul, ModularForm.SL_slash (γ := (-1 : SL(2, ℤ))),
        hcoe, ModularForm.slash_neg_one, SlashInvariantFormClass.SL_slash_eq G _ hγ']

theorem peterssonInner_slash_slash_of_mem_withCenter {Γ : Subgroup SL(2, ℤ)}
    (f : CuspForm (Γ.map (mapGL ℝ)) k) (G : _root_.ModularForm (Γ.map (mapGL ℝ)) k)
    {γ : SL(2, ℤ)} (hγ : γ ∈ Γ.withCenter) (β : SL(2, ℤ)) :
    UpperHalfPlane.peterssonInner k fd ((⇑f ∣[k] γ) ∣[k] β) ((⇑G ∣[k] γ) ∣[k] β) =
      UpperHalfPlane.peterssonInner k fd (⇑f ∣[k] β) (⇑G ∣[k] β) := by
  obtain ⟨c, hc, hf, hG⟩ := exists_slash_eq_smul_of_mem_withCenter (k := k) hγ
  rw [hf f, hG G, ModularForm.SL_smul_slash, ModularForm.SL_smul_slash,
    peterssonInner_smul_left, peterssonInner_smul_right, ← mul_assoc, hc, one_mul]

theorem peterssonInner_slash_inv_out {Γ : Subgroup SL(2, ℤ)}
    (f : CuspForm (Γ.map (mapGL ℝ)) k) (G : _root_.ModularForm (Γ.map (mapGL ℝ)) k)
    (δ : SL(2, ℤ)) :
    UpperHalfPlane.peterssonInner k fd
        (⇑f ∣[k] ((QuotientGroup.mk δ : SL(2, ℤ) ⧸ Γ.withCenter).out)⁻¹)
        (⇑G ∣[k] ((QuotientGroup.mk δ : SL(2, ℤ) ⧸ Γ.withCenter).out)⁻¹) =
      UpperHalfPlane.peterssonInner k fd (⇑f ∣[k] δ⁻¹) (⇑G ∣[k] δ⁻¹) := by
  have hmem : ((QuotientGroup.mk δ : SL(2, ℤ) ⧸ Γ.withCenter).out)⁻¹ * δ ∈ Γ.withCenter :=
    QuotientGroup.eq.mp (Quotient.out_eq _)
  have h := peterssonInner_slash_slash_of_mem_withCenter f G hmem δ⁻¹
  have hcancel : ((QuotientGroup.mk δ : SL(2, ℤ) ⧸ Γ.withCenter).out)⁻¹ * δ * δ⁻¹ =
      ((QuotientGroup.mk δ : SL(2, ℤ) ⧸ Γ.withCenter).out)⁻¹ := by group
  rwa [← SlashAction.slash_mul, ← SlashAction.slash_mul, hcancel] at h

/-! ### Trace adjunction -/

/-- **Trace adjunction with explicit coset representatives**: `⟪f, Σᵢ G ∣ γᵢ⁻¹⟫_Γ = ⟪res f, G⟫_Γ'`. -/
theorem cuspModPairing_sum_slash_right {Γ Γ' : Subgroup SL(2, ℤ)} [Γ.FiniteIndex]
    [Γ'.FiniteIndex] (hle : Γ' ≤ Γ) (hneg : (-1 : SL(2, ℤ)) ∈ Γ → (-1 : SL(2, ℤ)) ∈ Γ')
    {ι : Type*} [Fintype ι] (γ : ι → Γ)
    (hγ : Function.Bijective fun i => (QuotientGroup.mk (γ i) : Γ ⧸ Γ'.subgroupOf Γ))
    (f : CuspForm (Γ.map (mapGL ℝ)) k) (G : _root_.ModularForm (Γ'.map (mapGL ℝ)) k)
    (F : _root_.ModularForm (Γ.map (mapGL ℝ)) k)
    (hF : ⇑F = ∑ i, ⇑G ∣[k] ((γ i : SL(2, ℤ)))⁻¹) :
    cuspModPairing f F = cuspModPairing (CuspForm.restrict (Subgroup.map_mono hle) f) G := by
  set Φ : (SL(2, ℤ) ⧸ Γ.withCenter) × ι → SL(2, ℤ) ⧸ Γ'.withCenter :=
    fun x => QuotientGroup.mk (x.1.out * (γ x.2 : SL(2, ℤ))) with hΦ_def
  have hwc : Γ'.withCenter ≤ Γ.withCenter :=
    Subgroup.withCenter_le_iff.mpr ⟨hle.trans Γ.le_withCenter, Γ.center_le_withCenter⟩
  set j : ι → Γ.withCenter ⧸ Γ'.withCenter.subgroupOf Γ.withCenter :=
    fun i => QuotientGroup.mk ⟨γ i, Γ.le_withCenter (γ i).2⟩
  have hj : Function.Bijective j := by
    refine ⟨fun i i' hii' => hγ.1 (QuotientGroup.eq.mpr ?_), fun q => ?_⟩
    · have hx : (γ i : SL(2, ℤ))⁻¹ * γ i' ∈ Γ ⊓ Γ'.withCenter :=
        ⟨Γ.mul_mem (Γ.inv_mem (γ i).2) (γ i').2,
          Subgroup.mem_subgroupOf.mp ((QuotientGroup.eq (s := Γ'.withCenter.subgroupOf _)).mp hii')⟩
      rwa [Subgroup.inf_withCenter_eq_of_le hle hneg] at hx
    · obtain ⟨x, hx, hsign⟩ := Subgroup.mem_withCenter_iff_exists_eq_or_eq_neg.mp q.out.2
      obtain ⟨i, hi⟩ := hγ.2 (QuotientGroup.mk ⟨x, hx⟩)
      have hix : (γ i : SL(2, ℤ))⁻¹ * x ∈ Γ' := by
        have := (QuotientGroup.eq (s := Γ'.subgroupOf Γ)).mp hi
        rwa [Subgroup.mem_subgroupOf, Subgroup.coe_mul, Subgroup.coe_inv] at this
      refine ⟨i, ?_⟩
      rw [← QuotientGroup.out_eq' q]
      refine QuotientGroup.eq.mpr (Subgroup.mem_withCenter_iff_exists_eq_or_eq_neg.mpr
        ⟨_, hix, ?_⟩)
      rw [Subgroup.subtype_apply, Subgroup.coe_mul, Subgroup.coe_inv]
      rcases hsign with hsign | hsign <;> rw [hsign]
      · exact Or.inl rfl
      · exact Or.inr (mul_neg _ _)
  have hΦ : Function.Bijective Φ :=
    (Subgroup.quotientEquivProdOfLE' hwc Quotient.out Quotient.out_eq').symm.bijective.comp
      (Function.bijective_id.prodMap hj)
  rw [cuspModPairing_def, cuspModPairing_def,
    ← (Equiv.ofBijective Φ hΦ).sum_comp, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun p _ => ?_
  have hsummand : ∀ i, (⇑f ∣[k] (p.out)⁻¹) = (⇑f ∣[k] ((γ i : SL(2, ℤ))⁻¹ * (p.out)⁻¹)) :=
    fun i => by
      rw [SlashAction.slash_mul, SlashInvariantFormClass.SL_slash_eq f _ (Γ.inv_mem (γ i).2)]
  rw [hF, SlashAction.sum_slash, UpperHalfPlane.peterssonInner_sum_right k fd Finset.univ _ _
    fun i _ => by
      rw [hsummand i, ← SlashAction.slash_mul]
      simpa only [CuspForm.coe_restrict] using
        integrableOn_petersson_slash_left k _ (CuspForm.restrict (Subgroup.map_mono hle) f) G _]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Equiv.ofBijective_apply, hΦ_def, peterssonInner_slash_inv_out, mul_inv_rev, hsummand i,
    CuspForm.coe_restrict, SlashAction.slash_mul, SlashAction.slash_mul]

/-- **Trace adjunction** for the actual modular-form trace: `⟪f, tr G⟫_Γ = ⟪res f, G⟫_Γ'`. -/
theorem cuspModPairing_trace_right {Γ Γ' : Subgroup SL(2, ℤ)} [Γ.FiniteIndex] [Γ'.FiniteIndex]
    [(Γ'.map (mapGL ℝ)).IsFiniteRelIndex (Γ.map (mapGL ℝ))]
    (hle : Γ' ≤ Γ) (hneg : (-1 : SL(2, ℤ)) ∈ Γ → (-1 : SL(2, ℤ)) ∈ Γ')
    (f : CuspForm (Γ.map (mapGL ℝ)) k) (G : _root_.ModularForm (Γ'.map (mapGL ℝ)) k) :
    cuspModPairing f (_root_.ModularForm.trace (Γ.map (mapGL ℝ)) G) =
      cuspModPairing (CuspForm.restrict (Subgroup.map_mono hle) f) G := by
  have hinj : Function.Injective (mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ) := mapGL_injective
  set e := Subgroup.equivMapOfInjective Γ (mapGL ℝ) hinj
  have key : ∀ y : Γ.map (mapGL ℝ), ((e.symm y : Γ) : SL(2, ℤ)) ∈ Γ' ↔
      (y : GL (Fin 2) ℝ) ∈ Γ'.map (mapGL ℝ) := by
    intro y
    have hy : mapGL ℝ ((e.symm y : Γ) : SL(2, ℤ)) = y := by
      rw [← Subgroup.coe_equivMapOfInjective_apply Γ (mapGL ℝ) hinj, MulEquiv.apply_symm_apply]
    rw [← Subgroup.mem_map_iff_mem hinj, hy]
  let : Fintype (Γ.map (mapGL ℝ) ⧸ (Γ'.map (mapGL ℝ)).subgroupOf (Γ.map (mapGL ℝ))) :=
    Fintype.ofFinite _
  let E : Γ.map (mapGL ℝ) ⧸ (Γ'.map (mapGL ℝ)).subgroupOf (Γ.map (mapGL ℝ)) ≃
      Γ ⧸ Γ'.subgroupOf Γ :=
    Quotient.congr e.symm.toEquiv fun a b => by
      rw [QuotientGroup.leftRel_apply, QuotientGroup.leftRel_apply, Subgroup.mem_subgroupOf,
        Subgroup.mem_subgroupOf, MulEquiv.toEquiv_eq_coe, MulEquiv.coe_toEquiv, ← map_inv,
        ← map_mul, key]
  have hE : (fun q => (QuotientGroup.mk (e.symm q.out) : Γ ⧸ Γ'.subgroupOf Γ)) = E := by
    funext q
    conv_rhs => rw [← QuotientGroup.out_eq' q]
    rfl
  refine cuspModPairing_sum_slash_right hle hneg
    (fun q : Γ.map (mapGL ℝ) ⧸ (Γ'.map (mapGL ℝ)).subgroupOf (Γ.map (mapGL ℝ)) => e.symm q.out)
    (hE ▸ E.bijective) f G _ ?_
  rw [_root_.ModularForm.coe_trace]
  refine Finset.sum_congr rfl fun q _ => ?_
  have hq : (((e.symm q.out : Γ) : SL(2, ℤ)) : GL (Fin 2) ℝ) = (q.out : GL (Fin 2) ℝ) :=
    (Subgroup.coe_equivMapOfInjective_apply Γ (mapGL ℝ) hinj _).symm.trans
      (congrArg Subtype.val (e.apply_symm_apply _))
  conv_lhs => rw [← Quotient.out_eq q]
  rw [SlashInvariantForm.quotientFunc_mk, ModularForm.SL_slash, map_inv, map_inv, hq]

/-- **Restriction scales the pairing by the relative index**:
`⟪res f, res G⟫_Γ' = [Γ : Γ'] ⟪f, G⟫_Γ`. -/
theorem cuspModPairing_restrict_restrict {Γ Γ' : Subgroup SL(2, ℤ)} [Γ.FiniteIndex]
    [Γ'.FiniteIndex] [(Γ'.map (mapGL ℝ)).IsFiniteRelIndex (Γ.map (mapGL ℝ))]
    (hle : Γ' ≤ Γ) (hneg : (-1 : SL(2, ℤ)) ∈ Γ → (-1 : SL(2, ℤ)) ∈ Γ')
    (f : CuspForm (Γ.map (mapGL ℝ)) k) (G : _root_.ModularForm (Γ.map (mapGL ℝ)) k) :
    cuspModPairing (CuspForm.restrict (Subgroup.map_mono hle) f)
        (_root_.ModularForm.restrict (Subgroup.map_mono hle) G) =
      ((Γ'.map (mapGL ℝ)).relIndex (Γ.map (mapGL ℝ)) : ℂ) * cuspModPairing f G := by
  rw [← cuspModPairing_trace_right hle hneg f, _root_.trace_restrict,
    ← Nat.cast_smul_eq_nsmul ℂ, cuspModPairing_smul_right]

/-! ### Principal congruence levels -/

open DivisionEisensteinLevelMaps (principal_group_le traceIndex traceIndex_ne_zero)

set_option quotPrecheck false in
local notation "ΓP" N => (CongruenceSubgroup.Gamma N).map (mapGL ℝ)

theorem neg_one_not_mem_Gamma (N : ℕ) (h3 : 3 ≤ N) :
    (-1 : SL(2, ℤ)) ∉ CongruenceSubgroup.Gamma N := by
  intro h
  rw [CongruenceSubgroup.Gamma_mem] at h
  obtain ⟨h00, -, -, -⟩ := h
  have h1 : (((-1 : ℤ) : ℤ) : ZMod N) = ((1 : ℤ) : ZMod N) := by
    have : ((-1 : SL(2, ℤ)) 0 0 : ℤ) = -1 := by simp
    rw [this] at h00
    simpa using h00
  have hd := (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ N).mp h1
  norm_num at hd
  have := Int.le_of_dvd (by norm_num) hd
  omega

theorem Gamma_le_of_dvd {N M : ℕ} (hNM : N ∣ M) :
    CongruenceSubgroup.Gamma M ≤ CongruenceSubgroup.Gamma N :=
  (Subgroup.map_le_map_iff_of_injective mapGL_injective).mp (principal_group_le hNM)

/-- **Principal-level trace adjunction**, `3 ≤ N ∣ M`, any weight. -/
theorem principal_pairing_trace (N M : ℕ) [NeZero N] [NeZero M] (h3 : 3 ≤ N) (hNM : N ∣ M)
    (f : CuspForm (ΓP N) k) (G : _root_.ModularForm (ΓP M) k) :
    cuspModPairing f (_root_.ModularForm.trace (ΓP N) G) =
      cuspModPairing (CuspForm.restrict (principal_group_le hNM) f) G :=
  cuspModPairing_trace_right (Gamma_le_of_dvd hNM)
    (fun h => absurd h (neg_one_not_mem_Gamma N h3)) f G

/-- **Normalized principal-level adjunction**: the relative index enters exactly once. -/
theorem principal_pairing_normalizedTrace (N M : ℕ) [NeZero N] [NeZero M] (h3 : 3 ≤ N)
    (hNM : N ∣ M) (f : CuspForm (ΓP N) k) (G : _root_.ModularForm (ΓP M) k) :
    cuspModPairing f (((traceIndex N M : ℂ)⁻¹) • _root_.ModularForm.trace (ΓP N) G) =
      (traceIndex N M : ℂ)⁻¹ * cuspModPairing (CuspForm.restrict (principal_group_le hNM) f) G := by
  rw [cuspModPairing_smul_right, principal_pairing_trace N M h3 hNM]

theorem restrict_pairing_eq (N M : ℕ) [NeZero N] [NeZero M] (h3 : 3 ≤ N) (hNM : N ∣ M)
    (f : CuspForm (ΓP N) k) (G : _root_.ModularForm (ΓP M) k) :
    cuspModPairing (CuspForm.restrict (principal_group_le hNM) f) G =
      (traceIndex N M : ℂ) *
        cuspModPairing f (((traceIndex N M : ℂ)⁻¹) • _root_.ModularForm.trace (ΓP N) G) := by
  have hidx : (traceIndex N M : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (traceIndex_ne_zero N M (Nat.pos_of_ne_zero (NeZero.ne M)))
  rw [principal_pairing_normalizedTrace N M h3 hNM, ← mul_assoc, mul_inv_cancel₀ hidx, one_mul]

/-! ### Orthogonality transport -/

/-- Weight three: orthogonality to the same-level mixed space transports to every divisible
level. -/
theorem mixed_orthogonal_restrict (N M : ℕ) [NeZero N] [NeZero M] (h3 : 3 ≤ N) (hM : 0 < M) (hNM : N ∣ M)
    (f : CuspForm (ΓP N) 3)
    (horth : ∀ g ∈ MixedAllLevelTrace.mixedSpace N (by omega), cuspModPairing f g = 0) :
    ∀ G ∈ MixedAllLevelTrace.mixedSpace M hM,
      cuspModPairing (CuspForm.restrict (principal_group_le hNM) f) G = 0 := by
  intro G hG
  rw [restrict_pairing_eq N M h3 hNM]
  have ht := MixedAllLevelTrace.mixed_trace_all h3 hM hNM hG
  rw [RepeatedPrimeMixedTrace.normalizedTrace3_apply] at ht
  rw [horth _ ht, mul_zero]

/-- Weight two: orthogonality to the same-level admissible degree-two product span transports to
every divisible level. -/
theorem product_orthogonal_restrict (N M : ℕ) [NeZero N] [NeZero M] (h3 : 3 ≤ N) (hM : 0 < M) (hNM : N ∣ M)
    (f : CuspForm (ΓP N) 2)
    (horth : ∀ g ∈ TorsionQuadraticGenerators.productSpan N (by omega), cuspModPairing f g = 0) :
    ∀ G ∈ TorsionQuadraticGenerators.productSpan M hM,
      cuspModPairing (CuspForm.restrict (principal_group_le hNM) f) G = 0 := by
  intro G hG
  rw [restrict_pairing_eq N M h3 hNM]
  have ht := AllLevelPrincipalProductTrace.trace_productSpan_all h3 hM hNM hG
  rw [DivisionEisensteinLevelMaps.normalizedTrace_apply] at ht
  rw [horth _ ht, mul_zero]

/-! ### One integral over a fundamental domain, and conjugation -/

theorem cuspModPairing_eq_sum_smul_fd {Γ : Subgroup SL(2, ℤ)} [Γ.FiniteIndex]
    (f : CuspForm (Γ.map (mapGL ℝ)) k) (G : _root_.ModularForm (Γ.map (mapGL ℝ)) k) :
    cuspModPairing f G = ∑ q : SL(2, ℤ) ⧸ Γ.withCenter,
      UpperHalfPlane.peterssonInner k ((q.out)⁻¹ • fd) ⇑f ⇑G := by
  rw [cuspModPairing_def]
  exact Finset.sum_congr rfl fun q _ => UpperHalfPlane.peterssonInner_slash_slash_SL _ _ _ _ _

/-- The pairing is one integral over the union of translates of the open standard domain; the
integrand is integrable on each translate because `f` is cuspidal. -/
theorem cuspModPairing_eq_peterssonInner {Γ : Subgroup SL(2, ℤ)} [Γ.FiniteIndex]
    (f : CuspForm (Γ.map (mapGL ℝ)) k) (G : _root_.ModularForm (Γ.map (mapGL ℝ)) k) :
    cuspModPairing f G = UpperHalfPlane.peterssonInner k
      (⋃ q : SL(2, ℤ) ⧸ Γ.withCenter, ((q.out)⁻¹ • fdo)) ⇑f ⇑G := by
  rw [UpperHalfPlane.peterssonInner_def, integral_iUnion_fintype
      (fun q => (isOpen_smul_fdo _).measurableSet)
      (ModularGroup.pairwise_disjoint_smul_fdo_out_withCenter Γ)
      (fun q => (UpperHalfPlane.integrableOn_petersson_sl_smul_fd_left
        k (Γ.map (mapGL ℝ)) f G _).mono_set (Set.smul_set_mono fdo_subset_fd)),
    cuspModPairing_eq_sum_smul_fd]
  refine Finset.sum_congr rfl fun q _ => ?_
  have hae : ((((q.out)⁻¹ : SL(2, ℤ)) • fd : Set ℍ)) =ᵐ[volume]
      (((q.out)⁻¹ : SL(2, ℤ)) • fdo) := by
    rw [ModularGroup.sl_smul_set, ModularGroup.sl_smul_set]
    exact (MeasureTheory.smul_set_ae_eq _).mpr fd_ae_eq_fdo
  rw [UpperHalfPlane.peterssonInner_congr_set hae, UpperHalfPlane.peterssonInner_def]

/-- **Conjugation**: if `α` (positive determinant) conjugates `Γ'` onto `Γ`, slashing a cusp form
and a modular form for `Γ'` by `α` multiplies the pairing by `(det α)^(k-2)`. -/
theorem cuspModPairing_slash_of_inv_conjAct_eq {Γ Γ' : Subgroup SL(2, ℤ)} [Γ.FiniteIndex]
    [Γ'.FiniteIndex] {α : GL (Fin 2) ℝ} (hdet : 0 < (α : Matrix (Fin 2) (Fin 2) ℝ).det)
    (hα : ConjAct.toConjAct α⁻¹ • Γ'.map (mapGL ℝ) = Γ.map (mapGL ℝ))
    {f : CuspForm (Γ'.map (mapGL ℝ)) k} {g : _root_.ModularForm (Γ'.map (mapGL ℝ)) k}
    {F : CuspForm (Γ.map (mapGL ℝ)) k} {G : _root_.ModularForm (Γ.map (mapGL ℝ)) k}
    (hF : ⇑F = ⇑f ∣[k] α) (hG : ⇑G = ⇑g ∣[k] α) :
    cuspModPairing F G =
      ((α : Matrix (Fin 2) (Fin 2) ℝ).det : ℂ) ^ (k - 2) * cuspModPairing f g := by
  rw [cuspModPairing_eq_peterssonInner, cuspModPairing_eq_peterssonInner, hF, hG,
    UpperHalfPlane.peterssonInner_slash_slash_of_det_pos k hdet,
    UpperHalfPlane.peterssonInner_eq_of_isFundamentalDomain k f g
      (isFundamentalDomain_smul_of_inv_conjAct_eq hα
        (isFundamentalDomain_iUnion_out_inv_smul_fdo_withCenter Γ))
      (isFundamentalDomain_iUnion_out_inv_smul_fdo_withCenter Γ')]

/-- **Translate adjunction.** Let `α` have positive determinant, let `Γ''` be the conjugate
`α Γ α⁻¹`, contained in `Γ₁`, with `-I ∈ Γ₁ → -I ∈ Γ''`. For a cusp form `f` for `Γ₁` with
translate `F = f ∣ α` (a cusp form for `Γ`) and a modular form `G` for `Γ` with `G' = G ∣ α⁻¹`,

`⟪F, G⟫_Γ = (det α)^(k-2) · ⟪f, tr_{Γ''→Γ₁} G'⟫_Γ₁`. -/
theorem cuspModPairing_translate {Γ Γ₁ Γ'' : Subgroup SL(2, ℤ)} [Γ.FiniteIndex]
    [Γ₁.FiniteIndex] [Γ''.FiniteIndex] [(Γ''.map (mapGL ℝ)).IsFiniteRelIndex (Γ₁.map (mapGL ℝ))]
    {α : GL (Fin 2) ℝ} (hdet : 0 < (α : Matrix (Fin 2) (Fin 2) ℝ).det)
    (hΓ'' : Γ''.map (mapGL ℝ) = ConjAct.toConjAct α • Γ.map (mapGL ℝ)) (hle : Γ'' ≤ Γ₁)
    (hneg : (-1 : SL(2, ℤ)) ∈ Γ₁ → (-1 : SL(2, ℤ)) ∈ Γ'')
    (f : CuspForm (Γ₁.map (mapGL ℝ)) k) (G : _root_.ModularForm (Γ.map (mapGL ℝ)) k)
    (F : CuspForm (Γ.map (mapGL ℝ)) k) (hF : ⇑F = ⇑f ∣[k] α)
    (G' : _root_.ModularForm (Γ''.map (mapGL ℝ)) k) (hG' : ⇑G' = ⇑G ∣[k] α⁻¹) :
    cuspModPairing F G = ((α : Matrix (Fin 2) (Fin 2) ℝ).det : ℂ) ^ (k - 2) *
      cuspModPairing f (_root_.ModularForm.trace (Γ₁.map (mapGL ℝ)) G') := by
  have hα : ConjAct.toConjAct α⁻¹ • Γ''.map (mapGL ℝ) = Γ.map (mapGL ℝ) := by
    rw [hΓ'', map_inv, inv_smul_smul]
  have hG : ⇑G = ⇑G' ∣[k] α := by
    rw [hG', ← SlashAction.slash_mul, inv_mul_cancel, SlashAction.slash_one]
  rw [cuspModPairing_trace_right hle hneg f G',
    cuspModPairing_slash_of_inv_conjAct_eq hdet hα
      (f := CuspForm.restrict (Subgroup.map_mono hle) f) (g := G')
      (by rw [CuspForm.coe_restrict]; exact hF) hG]

/-! ### Positive rational translates at principal levels -/

open ConjAct in
/-- A rational matrix as a real one. -/
def ratGL (g : GL (Fin 2) ℚ) : GL (Fin 2) ℝ := g.map (Rat.castHom ℝ)

open ConjAct in
/-- The integral points of `g Γ(L) g⁻¹`. -/
def conjLevel (g : GL (Fin 2) ℚ) (L : ℕ) : Subgroup SL(2, ℤ) :=
  (toConjAct (ratGL g) • (ΓP L)).comap (mapGL ℝ)

open ConjAct in
theorem Gamma_le_conjLevel (g : GL (Fin 2) ℚ) (L : ℕ) [NeZero L] :
    ∃ L' ≠ 0, CongruenceSubgroup.Gamma L' ≤ conjLevel g L := by
  obtain ⟨L', hL', h⟩ := CongruenceSubgroup.exists_Gamma_le_conj' g⁻¹ L
  refine ⟨L', hL', fun γ hγ => ?_⟩
  rw [conjLevel, Subgroup.mem_comap, Subgroup.mem_pointwise_smul_iff_inv_smul_mem]
  have he : (toConjAct (ratGL g))⁻¹ = toConjAct (g⁻¹.map (Rat.castHom ℝ)) := by
    rw [ratGL, map_inv, map_inv]
  rw [he]
  exact h (Subgroup.smul_mem_pointwise_smul _ _ _ ⟨γ, hγ, rfl⟩)

instance conjLevel_finiteIndex (g : GL (Fin 2) ℚ) (L : ℕ) [NeZero L] :
    (conjLevel g L).FiniteIndex := by
  obtain ⟨L', hL', h⟩ := Gamma_le_conjLevel g L
  have : NeZero L' := ⟨hL'⟩
  exact Subgroup.finiteIndex_of_le h

instance conjLevel_relIndex (g : GL (Fin 2) ℚ) (L N : ℕ) [NeZero L] :
    ((conjLevel g L).map (mapGL ℝ)).IsFiniteRelIndex (ΓP N) := by
  obtain ⟨L', hL', h⟩ := Gamma_le_conjLevel g L
  rw [Subgroup.isFiniteRelIndex_iff_relIndex_ne_zero]
  have h0 : (ΓP L').relIndex (ΓP N) ≠ 0 := traceIndex_ne_zero N L' (Nat.pos_of_ne_zero hL')
  intro hz
  have hd := Subgroup.relIndex_dvd_of_le_left (L := ΓP N) (Subgroup.map_mono (f := mapGL ℝ) h)
  rw [hz] at hd
  exact h0 (Nat.eq_zero_of_zero_dvd hd)

open ConjAct in
theorem conjLevel_map (g : GL (Fin 2) ℚ) (N L : ℕ)
    (hconj : toConjAct (ratGL g) • (ΓP L) ≤ ΓP N) :
    (conjLevel g L).map (mapGL ℝ) = toConjAct (ratGL g) • (ΓP L) := by
  rw [conjLevel, Subgroup.map_comap_eq]
  apply inf_eq_right.mpr
  intro x hx
  obtain ⟨γ, -, he⟩ := Subgroup.mem_map.mp (hconj hx)
  exact ⟨γ, he⟩

open ConjAct in
theorem conjLevel_le (g : GL (Fin 2) ℚ) (N L : ℕ)
    (hconj : toConjAct (ratGL g) • (ΓP L) ≤ ΓP N) :
    conjLevel g L ≤ CongruenceSubgroup.Gamma N := fun _ hγ =>
  (Subgroup.mem_map_iff_mem mapGL_injective).mp (hconj hγ)

open ConjAct in
theorem translate_level_le (g : GL (Fin 2) ℚ) (N L : ℕ)
    (hconj : toConjAct (ratGL g) • (ΓP L) ≤ ΓP N) :
    (ΓP L) ≤ toConjAct (ratGL g)⁻¹ • (ΓP N) := by
  intro x hx
  rw [map_inv, Subgroup.mem_inv_pointwise_smul_iff]
  exact hconj (Subgroup.smul_mem_pointwise_smul _ _ _ hx)

open ConjAct in
theorem inverse_translate_level_le (g : GL (Fin 2) ℚ) (N L : ℕ)
    (hconj : toConjAct (ratGL g) • (ΓP L) ≤ ΓP N) :
    (conjLevel g L).map (mapGL ℝ) ≤ toConjAct (ratGL g)⁻¹⁻¹ • (ΓP L) := by
  rw [inv_inv, conjLevel_map g N L hconj]

open ConjAct in
/-- Every positive rational `g` and level `N` have a common level: for some `L₀ ≠ 0`, every
`L` divisible by `L₀` has `g Γ(L) g⁻¹ ≤ Γ(N)`. -/
theorem exists_common_level (g : GL (Fin 2) ℚ) (N : ℕ) [NeZero N] :
    ∃ L₀ ≠ 0, ∀ L, L₀ ∣ L → toConjAct (ratGL g) • (ΓP L) ≤ ΓP N := by
  obtain ⟨L₀, hL₀, h⟩ := CongruenceSubgroup.exists_Gamma_le_conj' g N
  refine ⟨L₀, hL₀, fun L hL x hx => h ?_⟩
  rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem] at hx ⊢
  exact principal_group_le hL hx

open ConjAct in
/-- **Positive rational translate adjunction at principal levels.** For `g ∈ GL(2, ℚ)` of
positive determinant, `3 ≤ N`, and a level `L` with `g Γ(L) g⁻¹ ≤ Γ(N)` (always available by
`exists_common_level`), a cusp form `f` for `Γ(N)` and a modular form `G` for `Γ(L)`:

`⟪f ∣ g, G⟫_{Γ(L)} = (det g)^(k-2) · ⟪f, tr_{g Γ(L) g⁻¹ → Γ(N)} (G ∣ g⁻¹)⟫_{Γ(N)}`. -/
theorem principal_rational_translate (g : GL (Fin 2) ℚ)
    (hdet : 0 < ((ratGL g : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ).det)
    (N L : ℕ) [NeZero N] [NeZero L] (h3 : 3 ≤ N)
    (hconj : toConjAct (ratGL g) • (ΓP L) ≤ ΓP N)
    (f : CuspForm (ΓP N) k) (G : _root_.ModularForm (ΓP L) k) :
    cuspModPairing (CuspForm.restrict (translate_level_le g N L hconj)
        (CuspForm.translate f (ratGL g))) G =
      ((ratGL g : Matrix (Fin 2) (Fin 2) ℝ).det : ℂ) ^ (k - 2) *
        cuspModPairing f (_root_.ModularForm.trace (ΓP N)
          (_root_.ModularForm.restrict (inverse_translate_level_le g N L hconj)
            (_root_.ModularForm.translate G (ratGL g)⁻¹))) :=
  cuspModPairing_translate hdet (conjLevel_map g N L hconj) (conjLevel_le g N L hconj)
    (fun h => absurd h (neg_one_not_mem_Gamma N h3)) f G _
    (by rw [CuspForm.coe_restrict, CuspForm.coe_translate]) _
    (by rw [_root_.ModularForm.coe_restrict, _root_.ModularForm.coe_translate])

open ConjAct in
/-- **Main-involution form.** With `G'' = (det g)^(k-2) • (G ∣ g⁻¹)`, whose function is
`G ∣ g^ι` for the adjugate `g^ι = (det g) g⁻¹`, the translate adjunction has no scalar:
`⟪f ∣ g, G⟫_{Γ(L)} = ⟪f, tr G''⟫_{Γ(N)}`. -/
theorem principal_rational_translate_adjugate (g : GL (Fin 2) ℚ)
    (hdet : 0 < ((ratGL g : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ).det)
    (N L : ℕ) [NeZero N] [NeZero L] (h3 : 3 ≤ N)
    (hconj : toConjAct (ratGL g) • (ΓP L) ≤ ΓP N)
    (f : CuspForm (ΓP N) k) (G : _root_.ModularForm (ΓP L) k) :
    let G'' := (((ratGL g : Matrix (Fin 2) (Fin 2) ℝ).det : ℂ) ^ (k - 2)) •
      _root_.ModularForm.restrict (inverse_translate_level_le g N L hconj)
        (_root_.ModularForm.translate G (ratGL g)⁻¹)
    cuspModPairing (CuspForm.restrict (translate_level_le g N L hconj)
        (CuspForm.translate f (ratGL g))) G =
      cuspModPairing f (_root_.ModularForm.trace (ΓP N) G'') ∧
    ⇑G'' = ⇑G ∣[k] TauCeti.adjugateGL (ratGL g) := by
  intro G''
  refine ⟨?_, ?_⟩
  · rw [principal_rational_translate g hdet N L h3 hconj f G]
    have ht : _root_.ModularForm.trace (ΓP N) G'' =
        (((ratGL g : Matrix (Fin 2) (Fin 2) ℝ).det : ℂ) ^ (k - 2)) •
          _root_.ModularForm.trace (ΓP N)
            (_root_.ModularForm.restrict (inverse_translate_level_le g N L hconj)
              (_root_.ModularForm.translate G (ratGL g)⁻¹)) :=
      map_smul (_root_.ModularForm.traceₗ (ΓP N)) _ _
    rw [ht, cuspModPairing_smul_right]
  · rw [ModularForm.slash_adjugateGL]
    change (((ratGL g : Matrix (Fin 2) (Fin 2) ℝ).det : ℂ) ^ (k - 2)) •
      ⇑(_root_.ModularForm.restrict (inverse_translate_level_le g N L hconj)
        (_root_.ModularForm.translate G (ratGL g)⁻¹)) = _
    rw [_root_.ModularForm.coe_restrict, _root_.ModularForm.coe_translate]

end ZInQ.Contrib.HeckePrimeRationality.MixedPeterssonTrace
