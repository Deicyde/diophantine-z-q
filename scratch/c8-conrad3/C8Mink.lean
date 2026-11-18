import ZInQKernel.Contrib.OneProof.C8CFT

set_option linter.style.longLine false
set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false

noncomputable section

namespace HDec.G0Galois.C8Conrad

namespace MinkDict

open _root_.GlueB3Unram NumberField
open scoped Pointwise

/-- A place of `ℚ̄` over a prime `q` exists (copy of the proof of `ValuationSubring.exists_liesOverPrime`,
vendored AnthropicFLT `Def_WeierstrassCurve_ReductionMap`, Apache-2.0: Mathlib's
`Ideal.image_subset_nonunits_valuationSubring` applied to `q ℤ`). -/
theorem exists_place_over (q : ℕ) (hq : q.Prime) : ∃ w : ValuationSubring Qbar, LiesOver w q := by
  set R : Subring Qbar := ⊥ with hR
  have hqR : ¬IsUnit ((q : ℕ) : R) := by
    rw [isUnit_iff_exists_inv]
    rintro ⟨y, hy⟩
    have hy' : (q : Qbar) * (y : Qbar) = 1 := by
      have := congrArg (R.subtype) hy
      simpa using this
    obtain ⟨n, hn⟩ := Subring.mem_bot.mp y.2
    rw [← hn] at hy'
    have hqn : (q : ℤ) * n = 1 := by
      have : (((q : ℤ) * n : ℤ) : Qbar) = ((1 : ℤ) : Qbar) := by push_cast; linear_combination hy'
      exact_mod_cast this
    have h1 : (q : ℤ) ≤ 1 := Int.le_of_dvd one_pos ⟨n, hqn.symm⟩
    have h2 : 2 ≤ q := hq.two_le
    omega
  obtain ⟨W, -, hW⟩ :=
    Ideal.image_subset_nonunits_valuationSubring (Ideal.span {((q : ℕ) : R)})
      (fun h => hqR (Ideal.span_singleton_eq_top.mp h))
  refine ⟨W, ?_⟩
  have : (q : Qbar) ∈ W.nonunits := hW ⟨((q : ℕ) : R), Ideal.subset_span rfl, by simp⟩
  exact (ValuationSubring.mem_nonunits_iff W).mp this

theorem liesOver_iff (w : ValuationSubring Qbar) (q : ℕ) : PkgI4.LiesOver w q ↔ LiesOver w q :=
  ValuationSubring.mem_nonunits_iff w

theorem liesOver_smul {w : ValuationSubring Qbar} {q : ℕ} (hw : LiesOver w q) (g : Gal) :
    LiesOver (g • w) q := by
  show (g • w).valuation (q : Qbar) < 1
  rw [val_smul_lt_one_iff, map_natCast]
  exact hw

section Lift

variable (F : IntermediateField ℚ Qbar) [FiniteDimensional ℚ F] [IsGalois ℚ F]

omit [FiniteDimensional ℚ F] [IsGalois ℚ F] in
theorem isIntegral_coe_ringOfIntegers (x : 𝓞 F) : IsIntegral ℤ (algebraMap F Qbar (x : F)) :=
  (RingOfIntegers.isIntegral_coe x).map (IsScalarTower.toAlgHom ℤ F Qbar)

/-- `𝓞 F → B`. -/
def iotaB : 𝓞 F →+* B :=
  ((algebraMap F Qbar).comp (algebraMap (𝓞 F) F)).codRestrict B
    (fun x => (mem_integralClosure_iff ℤ Qbar).mpr (isIntegral_coe_ringOfIntegers F x))

@[simp] theorem coe_iotaB (x : 𝓞 F) : ((iotaB F x : B) : Qbar) = algebraMap F Qbar (x : F) := rfl

theorem iotaB_injective : Function.Injective (iotaB F) := by
  intro x y h
  have := congrArg (fun b : B => (b : Qbar)) h
  simp only [coe_iotaB] at this
  exact RingOfIntegers.ext ((algebraMap F Qbar).injective this)

/-- An element of `B` fixed by `G_F` comes from `𝓞 F`. -/
theorem exists_of_fixed (b : B) (hb : ∀ h ∈ F.fixingSubgroup, (h : Gal) (b : Qbar) = b) :
    ∃ x : 𝓞 F, iotaB F x = b := by
  have hmem : (b : Qbar) ∈ F := by
    rw [← InfiniteGalois.fixedField_fixingSubgroup F]
    exact fun h => hb h h.2
  let y : F := ⟨b, hmem⟩
  have hint : IsIntegral ℤ y := by
    have h1 : IsIntegral ℤ (algebraMap F Qbar y) := (mem_integralClosure_iff ℤ Qbar).mp b.2
    exact (isIntegral_algHom_iff (IsScalarTower.toAlgHom ℤ F Qbar)
      (algebraMap F Qbar).injective).mp h1
  exact ⟨⟨y, hint⟩, Subtype.ext rfl⟩

/-- An element `g` of `G_ℚ` restricting to an element `σ` of the inertia group of `P` moves every element of `𝓞 F`
(seen in `B`) by an element of any prime `Q` of `B` over `P`. -/
theorem smul_sub_mem (P : Ideal (𝓞 F)) (Q : Ideal B) (hQ : Q.comap (iotaB F) = P)
    (σ : F ≃ₐ[ℚ] F) (hσ : σ ∈ P.inertia (F ≃ₐ[ℚ] F)) (g : Gal)
    (hg : ∀ y : F, g (algebraMap F Qbar y) = algebraMap F Qbar (σ y)) (x : 𝓞 F) :
    g • iotaB F x - iotaB F x ∈ Q := by
  have h1 : σ • x - x ∈ P := Ideal.mem_inertia.mp hσ x
  rw [← hQ, Ideal.mem_comap, map_sub] at h1
  convert h1 using 2
  apply Subtype.ext
  rw [coe_smul, coe_iotaB, coe_iotaB, hg]
  rfl

set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 1000000 in
/-- **Inertia lifts from `F` to `ℚ̄`.** For `F/ℚ` finite Galois, a prime `P` of `𝓞 F` over `p` and `σ` in the inertia
group of `P`, some element of the inertia group of some place of `ℚ̄` over `p` restricts to `σ` on `F`. (Mathlib's
profinite transitivity and surjectivity of `Stab(Q) → Aut((B/Q)/(A/Q∩A))` for `G_F` acting on `B`, as in
`GlueB3Unram.exists_inertia_neg`.) -/
theorem exists_inertia_lift (p : ℕ) (hp : p.Prime) (P : Ideal (𝓞 F)) [P.IsPrime] (hpP : (p : 𝓞 F) ∈ P)
    (σ : F ≃ₐ[ℚ] F) (hσ : σ ∈ P.inertia (F ≃ₐ[ℚ] F)) :
    ∃ w : ValuationSubring Qbar, LiesOver w p ∧ ∃ s : Gal,
      s ∈ (w.inertiaSubgroup ℚ).map (w.decompositionSubgroup ℚ).subtype ∧
      ∀ y : F, s (algebraMap F Qbar y) = algebraMap F Qbar (σ y) := by
  classical
  -- a prime `Q` of `B` over `P`
  letI : Algebra (𝓞 F) B := (iotaB F).toAlgebra
  haveI : Algebra.IsIntegral (𝓞 F) B := by
    constructor
    intro b
    have hb : IsIntegral ℤ b := by
      have h1 : IsIntegral ℤ (b : Qbar) := (mem_integralClosure_iff ℤ Qbar).mp b.2
      exact (isIntegral_algHom_iff (B.val) Subtype.val_injective).mp h1
    haveI : IsScalarTower ℤ (𝓞 F) B := IsScalarTower.of_algebraMap_eq (fun z => by simp)
    exact hb.tower_top
  have hker : (⊥ : Ideal B).under (𝓞 F) ≤ P := by
    intro x hx
    rw [Ideal.under, Ideal.mem_comap, Ideal.mem_bot] at hx
    have : x = 0 := iotaB_injective F (by rw [map_zero]; exact hx)
    rw [this]; exact P.zero_mem
  obtain ⟨Q, -, hQprime, hQP⟩ := Ideal.exists_ideal_over_prime_of_isIntegral P ⊥ hker
  have hQP' : Q.comap (iotaB F) = P := hQP
  -- a place `w` over `p` with center `Q`
  obtain ⟨w₀, hw₀⟩ := exists_place_over p hp
  have hQunder : Q.under ℤ = Ideal.span {(p : ℤ)} := by
    have hmem : (p : ℤ) ∈ Q.under ℤ := by
      rw [Ideal.under, Ideal.mem_comap]
      have : (algebraMap ℤ B (p : ℤ)) = iotaB F (p : 𝓞 F) := by simp
      rw [this, ← Ideal.mem_comap, hQP']
      exact hpP
    have hle : Ideal.span {(p : ℤ)} ≤ Q.under ℤ :=
      Ideal.span_le.mpr (Set.singleton_subset_iff.mpr hmem)
    have : Fact p.Prime := ⟨hp⟩
    exact ((Int.ideal_span_isMaximal_of_prime p).eq_of_le
      (Ideal.comap_isPrime (algebraMap ℤ B) Q).ne_top hle).symm
  obtain ⟨g₀, hg₀⟩ := exists_smul_eq (centerIdeal w₀) Q (by rw [centerIdeal_under w₀ p hp hw₀, hQunder])
  set w : ValuationSubring Qbar := g₀ • w₀ with hwdef
  have hw : LiesOver w p := liesOver_smul hw₀ g₀
  have hcw : centerIdeal w = Q := by rw [hwdef, centerIdeal_smul, hg₀]
  refine ⟨w, hw, ?_⟩
  -- a lift `g'` of `σ`
  let g' : Gal := σ.liftNormal Qbar
  have hg'F : ∀ y : F, g' (algebraMap F Qbar y) = algebraMap F Qbar (σ y) :=
    fun y => (AlgEquiv.liftNormal_commutes σ Qbar y)
  -- `G_F` and the algebraic integers `A` of `F`
  let H : Subgroup Gal := F.fixingSubgroup
  have hHF : ∀ h : H, ∀ y : F, (h : Gal) (algebraMap F Qbar y) = algebraMap F Qbar y :=
    fun h y => h.2 y
  have hHclosed : IsClosed (H : Set Gal) := InfiniteGalois.fixingSubgroup_isClosed F
  haveI : CompactSpace H := isCompact_iff_compactSpace.mp hHclosed.isCompact
  let A := FixedPoints.subalgebra ℤ B H
  haveI : SMulCommClass H A B := ⟨fun h a b => by
    rw [Subalgebra.smul_def, Subalgebra.smul_def, smul_eq_mul, smul_eq_mul, smul_mul', a.2 h]⟩
  have hA : ∀ a : A, ∃ x : 𝓞 F, iotaB F x = (a : B) := by
    intro a
    refine exists_of_fixed F (a : B) fun h hh => ?_
    have := a.2 ⟨h, hh⟩
    exact congrArg Subtype.val this
  -- an element of `G_ℚ` restricting to `σ` (or `σ⁻¹`) moves `A` inside `Q`
  have hmove : ∀ (τ : F ≃ₐ[ℚ] F), τ ∈ P.inertia (F ≃ₐ[ℚ] F) → ∀ g : Gal,
      (∀ y : F, g (algebraMap F Qbar y) = algebraMap F Qbar (τ y)) → ∀ a : A, g • (a : B) - (a : B) ∈ Q := by
    intro τ hτ g hg a
    obtain ⟨x, hx⟩ := hA a
    rw [← hx]
    exact smul_sub_mem F P Q hQP' τ hτ g hg x
  have hσinv : σ⁻¹ ∈ P.inertia (F ≃ₐ[ℚ] F) := (P.inertia (F ≃ₐ[ℚ] F)).inv_mem hσ
  have hg'inv : ∀ y : F, g'⁻¹ (algebraMap F Qbar y) = algebraMap F Qbar (σ⁻¹ y) := by
    intro y
    have h1 := hg'F (σ⁻¹ y)
    rw [show σ (σ⁻¹ y) = y from σ.apply_symm_apply y] at h1
    rw [← h1]
    show (g'⁻¹ * g') _ = _
    rw [inv_mul_cancel]; rfl
  -- step 1: `g' • Q` and `Q` lie over the same prime of `A`
  haveI hg'Q : (g' • Q).IsPrime := by rw [← hcw, ← centerIdeal_smul]; infer_instance
  have hunder : (g' • Q).under A = Q.under A := by
    ext a
    rw [Ideal.under, Ideal.under, Ideal.mem_comap, Ideal.mem_comap,
      Ideal.mem_pointwise_smul_iff_inv_smul_mem]
    have h := hmove σ⁻¹ hσinv g'⁻¹ hg'inv a
    show g'⁻¹ • (a : B) ∈ Q ↔ (a : B) ∈ Q
    constructor
    · intro h1
      have : (a : B) = g'⁻¹ • (a : B) - (g'⁻¹ • (a : B) - (a : B)) := by abel
      rw [this]; exact Q.sub_mem h1 h
    · intro h1
      have : g'⁻¹ • (a : B) = (g'⁻¹ • (a : B) - (a : B)) + (a : B) := by abel
      rw [this]; exact Q.add_mem h h1
  -- step 2: transitivity over `A`
  obtain ⟨g, hg⟩ := Algebra.IsInvariant.exists_smul_of_under_eq_of_profinite (A := A) (G := H)
    (g' • Q) Q hunder
  let τ : Gal := (g : Gal) * g'
  have hτQ : τ • Q = Q := by
    show ((g : Gal) * g') • Q = Q
    rw [mul_smul]; exact hg.symm
  have hτF : ∀ y : F, τ (algebraMap F Qbar y) = algebraMap F Qbar (σ y) := by
    intro y
    show (g : Gal) (g' (algebraMap F Qbar y)) = _
    rw [hg'F]
    exact hHF g (σ y)
  -- step 3: `τ` induces an `A/P`-automorphism of `B/Q`
  let f : B ≃+* B := MulSemiringAction.toRingEquiv Gal B τ
  have hQf : Q = Q.map f := by
    ext b
    rw [Ideal.mem_map_of_equiv]
    constructor
    · intro hb
      refine ⟨τ⁻¹ • b, ?_, by simp [f]⟩
      rw [← Ideal.mem_pointwise_smul_iff_inv_smul_mem, hτQ]; exact hb
    · rintro ⟨x, hx, rfl⟩
      rw [← hτQ]
      exact Ideal.smul_mem_pointwise_smul_iff.mpr hx
  let e : (B ⧸ Q) ≃+* (B ⧸ Q) := Ideal.quotientEquiv Q Q f hQf
  have he : ∀ b : B, e (Ideal.Quotient.mk Q b) = Ideal.Quotient.mk Q (τ • b) := fun b => rfl
  let φ : (B ⧸ Q) ≃ₐ[A ⧸ Q.under A] (B ⧸ Q) := AlgEquiv.ofRingEquiv (f := e) (by
    intro x
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
    rw [Ideal.Quotient.algebraMap_mk_of_liesOver, he, Ideal.Quotient.eq]
    exact hmove σ hσ τ hτF a)
  -- step 4: `h' ∈ H` acting on `B/Q` as `τ`
  obtain ⟨h', hh'⟩ := Ideal.Quotient.stabilizerHom_surjective_of_profinite (G := H)
    (Q.under A) Q φ
  have hact : ∀ b : B, Ideal.Quotient.mk Q (((h' : H) : Gal) • b) =
      Ideal.Quotient.mk Q (τ • b) := by
    intro b
    have := congrArg (fun ψ => ψ (Ideal.Quotient.mk Q b)) hh'
    exact this
  let k : Gal := ((h' : H) : Gal)
  have hkQ : k • Q = Q := h'.2
  let s : Gal := k⁻¹ * τ
  refine ⟨s, ?_, ?_⟩
  · apply mem_inertia_of_center hp hw s
    · show (k⁻¹ * τ) • centerIdeal w = centerIdeal w
      rw [hcw, mul_smul, hτQ, inv_smul_eq_iff, hkQ]
    · intro b
      rw [hcw]
      have h1 := hact (s • b)
      have h2 : ((h' : H) : Gal) • (s • b) = τ • b := by
        show k • ((k⁻¹ * τ) • b) = τ • b
        rw [mul_smul, smul_inv_smul]
      rw [h2, Ideal.Quotient.eq] at h1
      have h3 : b - s • b ∈ Q := by
        have h4 : τ • (b - s • b) ∈ τ • Q := by rw [hτQ, smul_sub]; exact h1
        rwa [Ideal.smul_mem_pointwise_smul_iff] at h4
      have := Q.neg_mem h3
      rwa [neg_sub] at this
  · intro y
    show k⁻¹ (τ (algebraMap F Qbar y)) = _
    rw [hτF]
    have hk : (⟨k⁻¹, H.inv_mem h'.1.2⟩ : H) = ((h' : H))⁻¹ := rfl
    exact hHF ⟨k⁻¹, H.inv_mem (h' : H).2⟩ (σ y)

end Lift

section Mink

/-- If `x` is fixed by every inertia group of every place of `ℚ̄` over a prime, so is every conjugate `g x`
(`I_{g⁻¹ w} = g⁻¹ I_w g`, `GlueB3Unram.inertia_conj`). -/
theorem fixed_conj (x : Qbar) (hx : ∀ q : ℕ, q.Prime → ∀ w : ValuationSubring Qbar, LiesOver w q →
      ∀ s : Gal, s ∈ (w.inertiaSubgroup ℚ).map (w.decompositionSubgroup ℚ).subtype → s x = x)
    (g : Gal) (q : ℕ) (hq : q.Prime) (w : ValuationSubring Qbar) (hw : LiesOver w q) (s : Gal)
    (hs : s ∈ (w.inertiaSubgroup ℚ).map (w.decompositionSubgroup ℚ).subtype) : s (g x) = g x := by
  have h1 := inertia_conj (g⁻¹ • w) w g (by rw [smul_inv_smul]) s hs
  have h2 := hx q hq (g⁻¹ • w) (liesOver_smul hw g⁻¹) _ h1
  have h3 : g ((g⁻¹ * s * g) x) = g x := by rw [h2]
  rw [AlgEquiv.mul_apply, AlgEquiv.mul_apply] at h3
  have e : g (g⁻¹ (s (g x))) = s (g x) := by
    show (g * g⁻¹) (s (g x)) = s (g x)
    rw [mul_inv_cancel]; rfl
  rwa [e] at h3

/-- **`MinkowskiInertiaQ` proved** (Minkowski's theorem in Mathlib, `NumberField.exists_not_isUnramifiedAt_int_of_isGalois`,
read on inertia groups of places of `ℚ̄`). -/
theorem minkowskiInertiaQ_proof : MinkowskiInertiaQ := by
  intro x hx0
  have hx : ∀ q : ℕ, q.Prime → ∀ w : ValuationSubring Qbar, LiesOver w q →
      ∀ s : Gal, s ∈ (w.inertiaSubgroup ℚ).map (w.decompositionSubgroup ℚ).subtype → s x = x := by
    intro q hq w hw s hs
    obtain ⟨t, ht, rfl⟩ := Subgroup.mem_map.mp hs
    exact hx0 q hq w ((liesOver_iff w q).mpr hw) ⟨t, ht⟩
  let K₀ : IntermediateField ℚ Qbar := IntermediateField.adjoin ℚ {x}
  haveI : FiniteDimensional ℚ K₀ :=
    IntermediateField.adjoin.finiteDimensional (Algebra.IsIntegral.isIntegral (R := ℚ) x)
  let F : IntermediateField ℚ Qbar := IntermediateField.normalClosure ℚ K₀ Qbar
  haveI : FiniteDimensional ℚ F := normalClosure.is_finiteDimensional ℚ K₀ Qbar
  haveI : IsGalois ℚ F := IsGalois.normalClosure ℚ K₀ Qbar
  haveI : NumberField F := { to_charZero := inferInstance, to_finiteDimensional := inferInstance }
  have hxF : x ∈ F := IntermediateField.le_normalClosure K₀ (IntermediateField.mem_adjoin_simple_self ℚ x)
  -- every inertia group fixes `F`
  have hF : ∀ q : ℕ, q.Prime → ∀ w : ValuationSubring Qbar, LiesOver w q → ∀ s : Gal,
      s ∈ (w.inertiaSubgroup ℚ).map (w.decompositionSubgroup ℚ).subtype → ∀ y ∈ F, s y = y := by
    intro q hq w hw s hs
    let S : Subgroup Gal := (w.inertiaSubgroup ℚ).map (w.decompositionSubgroup ℚ).subtype
    have hle : F ≤ IntermediateField.fixedField S := by
      show IntermediateField.normalClosure ℚ K₀ Qbar ≤ _
      rw [IntermediateField.normalClosure_def'']
      refine iSup_le fun f => ?_
      rw [IntermediateField.adjoin_map, Set.image_singleton, IntermediateField.adjoin_simple_le_iff]
      rintro ⟨s', hs'⟩
      exact fixed_conj x hx f q hq w hw s' hs'
    intro y hy
    exact (hle hy) ⟨s, hs⟩
  by_cases h1 : Module.finrank ℚ F = 1
  · have hbot : F = ⊥ := IntermediateField.finrank_eq_one_iff.mp h1
    have : x ∈ (⊥ : IntermediateField ℚ Qbar) := hbot ▸ hxF
    obtain ⟨r, hr⟩ := IntermediateField.mem_bot.mp this
    exact ⟨r, hr⟩
  · exfalso
    have hgt : 1 < Module.finrank ℚ F := lt_of_le_of_ne Module.finrank_pos (Ne.symm h1)
    obtain ⟨p, hp, hram⟩ := NumberField.exists_not_isUnramifiedAt_int_of_isGalois (K := F) (𝒪 := 𝓞 F) hgt
    obtain ⟨w₀, hw₀⟩ := exists_place_over p hp
    let P : Ideal (𝓞 F) := (centerIdeal w₀).comap (iotaB F)
    haveI : P.IsPrime := Ideal.comap_isPrime _ _
    have hpP : (p : 𝓞 F) ∈ P := by
      show iotaB F (p : 𝓞 F) ∈ centerIdeal w₀
      rw [mem_centerIdeal]
      have e : ((iotaB F (p : 𝓞 F) : B) : Qbar) = (p : Qbar) := by simp
      rw [e]; exact hw₀
    apply hram P inferInstance hpP
    let G := F ≃ₐ[ℚ] F
    have hinert : ∀ σ ∈ P.inertia G, σ = 1 := by
      intro σ hσ
      obtain ⟨w, hw, s, hs, hsσ⟩ := exists_inertia_lift F p hp P hpP σ hσ
      refine AlgEquiv.ext fun y => ?_
      have h2 := hsσ y
      rw [hF p hp w hw s hs (algebraMap F Qbar y) y.2] at h2
      exact ((algebraMap F Qbar).injective h2).symm
    have hcard : Nat.card (P.inertia G) = 1 := by
      rw [Nat.card_eq_one_iff_unique]
      exact ⟨⟨fun a b => Subtype.ext ((hinert a a.2).trans (hinert b b.2).symm)⟩, ⟨1⟩⟩
    have he : P.ramificationIdx ℤ = 1 := by
      rw [← Ideal.ramificationIdxIn_eq_ramificationIdx (P.under ℤ) P G,
        ← Ideal.card_inertia_eq_ramificationIdxIn (G := G) (P.under ℤ) P, hcard]
    exact Ideal.ramificationIdx_eq_one_iff.mp he

end Mink

end MinkDict

end HDec.G0Galois.C8Conrad

#print axioms HDec.G0Galois.C8Conrad.MinkDict.minkowskiInertiaQ_proof
