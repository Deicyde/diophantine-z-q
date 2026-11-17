/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: P2M.Sol.S_ValuationSubring_exists_isFrobeniusAt_of_liesOverPrime (git blob bd12adb9f848a63454efd82d8e4797dd594826c3, sha256 a75bbf417fc64c3a6c8f77f067b091d9605acaa6f01cfc6b8b809d535ea7143e).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_ValuationSubring_exists_integral_mul_eq_of_liesOverPrime
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Definitions.Def_FLTPrelim_Ramification
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Definitions.Def_EllipticCurve_FrobeniusTrace

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

namespace P2MW.S_ValuationSubring_exists_isFrobeniusAt_of_liesOverPrime.PlaceTransitivity
end P2MW.S_ValuationSubring_exists_isFrobeniusAt_of_liesOverPrime.PlaceTransitivity

namespace P2MW.S_ValuationSubring_exists_isFrobeniusAt_of_liesOverPrime

open scoped Pointwise



namespace PlaceTransitivity

noncomputable abbrev Zbar : Subalgebra ℤ (AlgebraicClosure ℚ) := integralClosure ℤ (AlgebraicClosure ℚ)



theorem coe_mem (A : ValuationSubring (AlgebraicClosure ℚ)) (b : (Zbar)) : (b : (AlgebraicClosure ℚ)) ∈ A := by
  have hb : IsIntegral ℤ (b : (AlgebraicClosure ℚ)) := b.2
  have hbA : IsIntegral A (b : (AlgebraicClosure ℚ)) := by
    obtain ⟨p, hp, hpb⟩ := hb
    refine ⟨p.map (Int.castRingHom A), hp.map _, ?_⟩
    rw [Polynomial.eval₂_map]
    have : (algebraMap A (AlgebraicClosure ℚ)).comp (Int.castRingHom A) = algebraMap ℤ (AlgebraicClosure ℚ) := RingHom.ext_int _ _
    rw [this]
    exact hpb
  obtain ⟨y, hy⟩ := (IsIntegrallyClosed.isIntegral_iff (R := A) (K := (AlgebraicClosure ℚ))).mp hbA
  rw [← hy]
  exact y.2

noncomputable def toPlace (A : ValuationSubring (AlgebraicClosure ℚ)) : (Zbar) →+* A :=
  ((Subalgebra.val (Zbar)).toRingHom).codRestrict A.toSubring (coe_mem A)

@[scoped simp] theorem coe_toPlace (A : ValuationSubring (AlgebraicClosure ℚ)) (b : (Zbar)) : (toPlace A b : (AlgebraicClosure ℚ)) = b := rfl

noncomputable def center (A : ValuationSubring (AlgebraicClosure ℚ)) : Ideal (Zbar) :=
  Ideal.comap (toPlace A) (IsLocalRing.maximalIdeal A)

theorem mem_center_iff {A : ValuationSubring (AlgebraicClosure ℚ)} {b : (Zbar)} :
    b ∈ center A ↔ (b : (AlgebraicClosure ℚ)) ∈ A.nonunits := by
  rw [center, Ideal.mem_comap, ← ValuationSubring.coe_mem_nonunits_iff, coe_toPlace]

scoped instance center_isPrime (A : ValuationSubring (AlgebraicClosure ℚ)) : (center A).IsPrime :=
  Ideal.comap_isPrime _ _

theorem center_under {q : ℕ} (hq : q.Prime) {A : ValuationSubring (AlgebraicClosure ℚ)} (hA : A.LiesOverPrime q) :
    (center A).under ℤ = Ideal.span {(q : ℤ)} := by
  have hmax : (Ideal.span {(q : ℤ)}).IsMaximal :=
    PrincipalIdealRing.isMaximal_of_irreducible (Nat.prime_iff_prime_int.mp hq).irreducible
  refine (hmax.eq_of_le ?_ ?_).symm
  · exact Ideal.comap_ne_top _ (Ideal.IsPrime.ne_top inferInstance)
  · rw [Ideal.span_le, Set.singleton_subset_iff]
    show algebraMap ℤ (Zbar) (q : ℤ) ∈ center A
    rw [mem_center_iff]
    have : ((algebraMap ℤ (Zbar) (q : ℤ) : (Zbar)) : (AlgebraicClosure ℚ)) = (q : (AlgebraicClosure ℚ)) := by
      rw [map_natCast]; rfl
    rw [this]
    exact hA

theorem mem_smul_nonunits_iff {K L : Type*} [Field K] [Field L] [Algebra K L]
    {τ : L ≃ₐ[K] L} {A : ValuationSubring L} {x : L} :
    x ∈ (τ • A).nonunits ↔ τ.symm x ∈ A.nonunits := by
  rw [ValuationSubring.mem_nonunits_iff_or, ValuationSubring.mem_nonunits_iff_or]
  have e0 : x = 0 ↔ τ.symm x = 0 := by
    constructor
    · intro h; rw [h, _root_.map_zero]
    · intro h; simpa using congrArg τ h
  have e1 : x⁻¹ ∈ τ • A ↔ (τ.symm x)⁻¹ ∈ A := by
    rw [ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem]
    have : (τ⁻¹ : L ≃ₐ[K] L) • x⁻¹ = (τ.symm x)⁻¹ := by
      show τ.symm x⁻¹ = (τ.symm x)⁻¹
      exact map_inv₀ _ _
    rw [this]
  rw [e0, e1]

theorem le_of_forall_not_mem_nonunits {q : ℕ} (hq : q.Prime) {V W : ValuationSubring (AlgebraicClosure ℚ)}
    (hV : V.LiesOverPrime q)
    (h : ∀ s : (Zbar), (s : (AlgebraicClosure ℚ)) ∉ V.nonunits → (s : (AlgebraicClosure ℚ)) ∉ W.nonunits) : V ≤ W := by
  intro x hx
  obtain ⟨x', s, hs, hxs⟩ :=
    ValuationSubring.exists_integral_mul_eq_of_liesOverPrime V hq hV x hx
  have hsW : (s : (AlgebraicClosure ℚ)) ∉ W.nonunits := h s hs
  rw [ValuationSubring.mem_nonunits_iff_or, not_or, not_not] at hsW
  obtain ⟨hs0, hsinv⟩ := hsW
  have hx_eq : x = (x' : (AlgebraicClosure ℚ)) * (s : (AlgebraicClosure ℚ))⁻¹ := by
    rw [← hxs, mul_assoc, mul_inv_cancel₀ hs0, mul_one]
  rw [hx_eq]
  exact W.mul_mem _ _ (coe_mem W x') hsinv

section Bundle

theorem isGalois_Qbar : IsGalois ℚ (AlgebraicClosure ℚ) := by
  have h : @IsGalois ℚ _ (AlgebraicClosure ℚ) _ (AlgebraicClosure.instAlgebra ℚ) := inferInstance
  exact h

theorem isAlgebraic_Qbar : Algebra.IsAlgebraic ℚ (AlgebraicClosure ℚ) := by
  have h : @Algebra.IsAlgebraic ℚ (AlgebraicClosure ℚ) _ _ (AlgebraicClosure.instAlgebra ℚ) := inferInstance
  exact h

end Bundle

theorem exists_smul_center_eq {q : ℕ} (hq : q.Prime) {A A₀ : ValuationSubring (AlgebraicClosure ℚ)}
    (hA : A.LiesOverPrime q) (hA₀ : A₀.LiesOverPrime q) :
    ∃ g : (AlgebraicClosure ℚ) ≃ₐ[ℚ] (AlgebraicClosure ℚ), center A₀ = g • center A := by
  classical
  haveI := isGalois_Qbar
  haveI := isAlgebraic_Qbar
  haveI : Algebra.IsIntegral ℚ (AlgebraicClosure ℚ) := Algebra.isAlgebraic_iff_isIntegral.mp inferInstance
  letI : TopologicalSpace (Zbar) := ⊥
  haveI : DiscreteTopology (Zbar) := ⟨rfl⟩
  haveI : ContinuousSMul ((AlgebraicClosure ℚ) ≃ₐ[ℚ] (AlgebraicClosure ℚ)) (Zbar) := by
    refine continuousSMul_iff_stabilizer_isOpen.mpr fun b => ?_
    haveI : FiniteDimensional ℚ (IntermediateField.adjoin ℚ {(b : (AlgebraicClosure ℚ))}) :=
      IntermediateField.adjoin.finiteDimensional (Algebra.IsIntegral.isIntegral (b : (AlgebraicClosure ℚ)))
    refine Subgroup.isOpen_mono ?_
      (IntermediateField.fixingSubgroup_isOpen (IntermediateField.adjoin ℚ {(b : (AlgebraicClosure ℚ))}))
    intro g hg
    rw [MulAction.mem_stabilizer_iff]
    apply Subtype.ext
    change g • (b : (AlgebraicClosure ℚ)) = b
    rw [IntermediateField.mem_fixingSubgroup_iff] at hg
    exact hg _ (IntermediateField.mem_adjoin_simple_self ℚ (b : (AlgebraicClosure ℚ)))
  haveI : Algebra.IsInvariant ℤ (Zbar) ((AlgebraicClosure ℚ) ≃ₐ[ℚ] (AlgebraicClosure ℚ)) := ⟨fun b hb => by
    have hb' : (b : (AlgebraicClosure ℚ)) ∈ Set.range (algebraMap ℚ (AlgebraicClosure ℚ)) := by
      rw [InfiniteGalois.mem_range_algebraMap_iff_fixed]
      intro g
      exact congrArg (fun z : (Zbar) => (z : (AlgebraicClosure ℚ))) (hb g)
    obtain ⟨r, hr⟩ := hb'
    have hrint : IsIntegral ℤ r := by
      have h := b.2
      rw [mem_integralClosure_iff, ← hr] at h
      exact (isIntegral_algHom_iff (IsScalarTower.toAlgHom ℤ ℚ (AlgebraicClosure ℚ))
        (algebraMap ℚ (AlgebraicClosure ℚ)).injective).mp h
    obtain ⟨n, hn⟩ := (IsIntegrallyClosed.isIntegral_iff (R := ℤ) (K := ℚ)).mp hrint
    refine ⟨n, Subtype.ext ?_⟩
    show ((algebraMap ℤ (Zbar) n : (Zbar)) : (AlgebraicClosure ℚ)) = b
    rw [← hr, ← hn]
    simp⟩
  have hu : (center A).under ℤ = (center A₀).under ℤ := by
    rw [center_under hq hA, center_under hq hA₀]
  exact Algebra.IsInvariant.exists_smul_of_under_eq_of_profinite
    (A := ℤ) (G := (AlgebraicClosure ℚ) ≃ₐ[ℚ] (AlgebraicClosure ℚ)) (center A) (center A₀) hu

end PlaceTransitivity
open scoped _root_.P2MW.S_ValuationSubring_exists_isFrobeniusAt_of_liesOverPrime.PlaceTransitivity

namespace PlaceTransitivity

theorem smul_eq_of_smul_center_eq {q : ℕ} (hq : q.Prime) {A : ValuationSubring (AlgebraicClosure ℚ)}
    (hA : A.LiesOverPrime q) {g : (AlgebraicClosure ℚ) ≃ₐ[ℚ] (AlgebraicClosure ℚ)} (hg : g • center A = center A) : g • A = A := by
  classical
  have key : ∀ s : Zbar, (s : (AlgebraicClosure ℚ)) ∈ (g • A).nonunits ↔ (s : (AlgebraicClosure ℚ)) ∈ A.nonunits := by
    intro s
    rw [mem_smul_nonunits_iff, ← mem_center_iff (A := A), ← hg,
      Ideal.mem_pointwise_smul_iff_inv_smul_mem, mem_center_iff]
    have : ((g⁻¹ • s : Zbar) : (AlgebraicClosure ℚ)) = g.symm s := by
      rw [integralClosure.coe_smul, AlgEquiv.smul_def, AlgEquiv.aut_inv]
    rw [this]
  have hgA : (g • A).LiesOverPrime q := by
    show (q : (AlgebraicClosure ℚ)) ∈ (g • A).nonunits
    rw [mem_smul_nonunits_iff, map_natCast]
    exact hA
  apply le_antisymm
  · exact le_of_forall_not_mem_nonunits hq hgA fun s hs => fun h => hs ((key s).mpr h)
  · exact le_of_forall_not_mem_nonunits hq hA fun s hs => fun h => hs ((key s).mp h)

theorem exists_frobenius_algEquiv {q : ℕ} (hq : q.Prime) {A : ValuationSubring (AlgebraicClosure ℚ)}
    [(center A).LiesOver (Ideal.span {(q : ℤ)})] :
    ∃ f : (Zbar ⧸ center A) ≃ₐ[ℤ ⧸ Ideal.span {(q : ℤ)}] (Zbar ⧸ center A),
      ∀ b : Zbar, f (Ideal.Quotient.mk (center A) b) = (Ideal.Quotient.mk (center A) b) ^ q := by
  classical
  haveI : Fact q.Prime := ⟨hq⟩

  have hqmem : ((q : ℤ) : Zbar) ∈ center A := by
    have := (Ideal.mem_of_liesOver (center A) (Ideal.span {(q : ℤ)}) (q : ℤ)).mp
      (Ideal.mem_span_singleton_self _)
    simpa using this
  haveI : CharP (Zbar ⧸ center A) q := by
    rw [CharP.charP_iff_prime_eq_zero hq]
    have : ((q : ℕ) : Zbar ⧸ center A) = Ideal.Quotient.mk (center A) ((q : ℤ) : Zbar) := by
      simp
    rw [this]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr hqmem
  let fr : (Zbar ⧸ center A) →+* (Zbar ⧸ center A) := frobenius (Zbar ⧸ center A) q
  have fr_apply : ∀ y, fr y = y ^ q := fun y => rfl

  let fa : (Zbar ⧸ center A) →ₐ[ℤ ⧸ Ideal.span {(q : ℤ)}] (Zbar ⧸ center A) :=
    { fr with
      commutes' := fun r => by
        obtain ⟨n, rfl⟩ := Ideal.Quotient.mk_surjective r
        rw [Ideal.Quotient.algebraMap_mk_of_liesOver]
        show fr (Ideal.Quotient.mk (center A) (algebraMap ℤ Zbar n)) =
          Ideal.Quotient.mk (center A) (algebraMap ℤ Zbar n)
        rw [eq_intCast, map_intCast, map_intCast] }
  have fa_apply : ∀ y, fa y = y ^ q := fun y => rfl

  have hinj : Function.Injective fa := by
    intro y₁ y₂ h
    rw [fa_apply, fa_apply] at h
    exact frobenius_inj (Zbar ⧸ center A) q h
  have hsurj : Function.Surjective fa := by
    intro y
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective y
    obtain ⟨c, hc⟩ := IsAlgClosed.exists_pow_nat_eq (b : (AlgebraicClosure ℚ)) hq.pos
    have hcint : IsIntegral ℤ c := by
      refine IsIntegral.of_pow hq.pos ?_
      rw [hc]; exact b.2
    refine ⟨Ideal.Quotient.mk (center A) ⟨c, hcint⟩, ?_⟩
    rw [fa_apply, ← map_pow]
    congr 1
    exact Subtype.ext hc
  exact ⟨AlgEquiv.ofBijective fa ⟨hinj, hsurj⟩, fun b => rfl⟩

end PlaceTransitivity
open scoped _root_.P2MW.S_ValuationSubring_exists_isFrobeniusAt_of_liesOverPrime.PlaceTransitivity

open PlaceTransitivity in

theorem solution {q : ℕ} (hq : q.Prime) (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime q) : ∃ φ : (AlgebraicClosure ℚ) ≃ₐ[ℚ] (AlgebraicClosure ℚ), A.IsFrobeniusAt φ q := by
  classical

  haveI := isGalois_Qbar
  haveI := isAlgebraic_Qbar
  haveI : Algebra.IsIntegral ℚ (AlgebraicClosure ℚ) := Algebra.isAlgebraic_iff_isIntegral.mp inferInstance
  letI : TopologicalSpace Zbar := ⊥
  haveI : DiscreteTopology Zbar := ⟨rfl⟩
  haveI : ContinuousSMul ((AlgebraicClosure ℚ) ≃ₐ[ℚ] (AlgebraicClosure ℚ)) Zbar := by
    refine continuousSMul_iff_stabilizer_isOpen.mpr fun b => ?_
    haveI : FiniteDimensional ℚ (IntermediateField.adjoin ℚ {(b : (AlgebraicClosure ℚ))}) :=
      IntermediateField.adjoin.finiteDimensional (Algebra.IsIntegral.isIntegral (b : (AlgebraicClosure ℚ)))
    refine Subgroup.isOpen_mono ?_
      (IntermediateField.fixingSubgroup_isOpen (IntermediateField.adjoin ℚ {(b : (AlgebraicClosure ℚ))}))
    intro g hg
    rw [MulAction.mem_stabilizer_iff]
    apply Subtype.ext
    change g • (b : (AlgebraicClosure ℚ)) = b
    rw [IntermediateField.mem_fixingSubgroup_iff] at hg
    exact hg _ (IntermediateField.mem_adjoin_simple_self ℚ (b : (AlgebraicClosure ℚ)))
  haveI : Algebra.IsInvariant ℤ Zbar ((AlgebraicClosure ℚ) ≃ₐ[ℚ] (AlgebraicClosure ℚ)) := ⟨fun b hb => by
    have hb' : (b : (AlgebraicClosure ℚ)) ∈ Set.range (algebraMap ℚ (AlgebraicClosure ℚ)) := by
      rw [InfiniteGalois.mem_range_algebraMap_iff_fixed]
      intro g
      exact congrArg (fun z : Zbar => (z : (AlgebraicClosure ℚ))) (hb g)
    obtain ⟨r, hr⟩ := hb'
    have hrint : IsIntegral ℤ r := by
      have h := b.2
      rw [mem_integralClosure_iff, ← hr] at h
      exact (isIntegral_algHom_iff (IsScalarTower.toAlgHom ℤ ℚ (AlgebraicClosure ℚ))
        (algebraMap ℚ (AlgebraicClosure ℚ)).injective).mp h
    obtain ⟨n, hn⟩ := (IsIntegrallyClosed.isIntegral_iff (R := ℤ) (K := ℚ)).mp hrint
    refine ⟨n, Subtype.ext ?_⟩
    show ((algebraMap ℤ Zbar n : Zbar) : (AlgebraicClosure ℚ)) = b
    rw [← hr, ← hn]
    simp⟩

  haveI hover : (center A).LiesOver (Ideal.span {(q : ℤ)}) := ⟨(center_under hq hA).symm⟩
  obtain ⟨f, hf⟩ := exists_frobenius_algEquiv (A := A) hq
  obtain ⟨g, hg⟩ := Ideal.Quotient.stabilizerHom_surjective_of_profinite
    (G := (AlgebraicClosure ℚ) ≃ₐ[ℚ] (AlgebraicClosure ℚ)) (Ideal.span {(q : ℤ)}) (center A) f

  have hgQ : (g : (AlgebraicClosure ℚ) ≃ₐ[ℚ] (AlgebraicClosure ℚ)) • center A = center A := g.2
  have hgA : (g : (AlgebraicClosure ℚ) ≃ₐ[ℚ] (AlgebraicClosure ℚ)) • A = A := smul_eq_of_smul_center_eq hq hA hgQ
  have hgD : (g : (AlgebraicClosure ℚ) ≃ₐ[ℚ] (AlgebraicClosure ℚ)) ∈ A.decompositionSubgroup ℚ := MulAction.mem_stabilizer_iff.mpr hgA
  refine ⟨g, hgD, ?_⟩

  let ψ : Zbar →+* IsLocalRing.ResidueField A := (IsLocalRing.residue A).comp (toPlace A)
  have hψ : ∀ b : Zbar, ψ ((g : (AlgebraicClosure ℚ) ≃ₐ[ℚ] (AlgebraicClosure ℚ)) • b) = ψ b ^ q := by
    intro b
    have h1 : Ideal.Quotient.mk (center A) (g • b) = (Ideal.Quotient.mk (center A) b) ^ q := by
      rw [← hf b, ← hg, Ideal.Quotient.stabilizerHom_apply]
    rw [← map_pow, Ideal.Quotient.eq] at h1
    have h1' : toPlace A (g • b) - toPlace A (b ^ q) ∈ IsLocalRing.maximalIdeal A := by
      have := h1
      unfold center at this
      rw [Ideal.mem_comap, map_sub] at this
      exact this
    have h2 := (Ideal.Quotient.eq (I := IsLocalRing.maximalIdeal A)).mpr h1'
    show IsLocalRing.residue A (toPlace A ((g : (AlgebraicClosure ℚ) ≃ₐ[ℚ] (AlgebraicClosure ℚ)) • b)) =
      (IsLocalRing.residue A (toPlace A b)) ^ q
    rw [← map_pow, ← map_pow]
    exact h2

  intro x
  obtain ⟨a, rfl⟩ := IsLocalRing.residue_surjective x
  obtain ⟨x', s, hs, hxs⟩ :=
    ValuationSubring.exists_integral_mul_eq_of_liesOverPrime A hq hA a a.2
  set d : A.decompositionSubgroup ℚ := ⟨g, hgD⟩
  have hψs : ψ s ≠ 0 := by
    intro h0
    apply hs
    have : toPlace A s ∈ IsLocalRing.maximalIdeal A :=
      (IsLocalRing.residue_eq_zero_iff _).mp h0
    rw [← ValuationSubring.coe_mem_nonunits_iff] at this
    exact this

  have e1 : a * toPlace A s = toPlace A x' := Subtype.ext hxs
  have e2 : (d • a) * toPlace A ((g : (AlgebraicClosure ℚ) ≃ₐ[ℚ] (AlgebraicClosure ℚ)) • s) = toPlace A ((g : (AlgebraicClosure ℚ) ≃ₐ[ℚ] (AlgebraicClosure ℚ)) • x') := by
    apply Subtype.ext
    show (g : (AlgebraicClosure ℚ) ≃ₐ[ℚ] (AlgebraicClosure ℚ)) (a : (AlgebraicClosure ℚ)) * (g : (AlgebraicClosure ℚ) ≃ₐ[ℚ] (AlgebraicClosure ℚ)) (s : (AlgebraicClosure ℚ)) = (g : (AlgebraicClosure ℚ) ≃ₐ[ℚ] (AlgebraicClosure ℚ)) (x' : (AlgebraicClosure ℚ))
    rw [← map_mul, hxs]
  have e1' : IsLocalRing.residue A a * ψ s = ψ x' := by
    show IsLocalRing.residue A a * IsLocalRing.residue A (toPlace A s) =
      IsLocalRing.residue A (toPlace A x')
    rw [← map_mul, e1]
  have e2' : IsLocalRing.residue A (d • a) * ψ ((g : (AlgebraicClosure ℚ) ≃ₐ[ℚ] (AlgebraicClosure ℚ)) • s) =
      ψ ((g : (AlgebraicClosure ℚ) ≃ₐ[ℚ] (AlgebraicClosure ℚ)) • x') := by
    show IsLocalRing.residue A (d • a) * IsLocalRing.residue A (toPlace A ((g : (AlgebraicClosure ℚ) ≃ₐ[ℚ] (AlgebraicClosure ℚ)) • s)) =
      IsLocalRing.residue A (toPlace A ((g : (AlgebraicClosure ℚ) ≃ₐ[ℚ] (AlgebraicClosure ℚ)) • x'))
    rw [← map_mul, e2]
  rw [hψ s, hψ x', ← e1', mul_pow] at e2'
  have hcancel := mul_right_cancel₀ (pow_ne_zero q hψs) e2'
  show d • IsLocalRing.residue A a = (IsLocalRing.residue A a) ^ q
  have : d • (IsLocalRing.residue A a) = IsLocalRing.residue A (d • a) :=
    (IsLocalRing.ResidueField.residue_smul (A.decompositionSubgroup ℚ) d a).symm
  exact this.trans hcancel
