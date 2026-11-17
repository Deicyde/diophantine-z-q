import ZInQKernel.Contrib.OneProof.T21Proof.Brandt

/-!
# t21-proof: the test vector at `n = 3` and `f_3(1) = ±3`

Task t21-proof.
* `twoRep_partner_mem`: the partner class `t*(s)` lies in `B^× H` (`twoRep v t* ∈ R̂_3^×`);
* `gT τ`: the function `−3` on `B^× H` (the double coset of `1`) and `1` elsewhere;
* `inPiZ_gT`: `gT τ ∈ π_ℤ^{U_3}` (TYZ's `InPiZ`, L536–550): the invariances hold by construction,
  the two orthogonality sums by `twoRep_ne`, `twoRep_partner_mem` and `sums_check`;
* `brandtValueAt3`: every test vector `f_3` (a generator of `π_ℤ^{U_3}`) has `f_3(1) = ±3`.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.style.longLine false
set_option linter.unusedSimpArgs false
set_option linter.deprecated false

noncomputable section

namespace ZInQ.Contrib.T21Proof

open ZInQ.Contrib.TYZDecomp.H29Split IsDedekindDomain NumberField
open scoped Quaternion FiniteAdeleExtension
open ZInQ.RouteK.Rank5b

local instance (p : Nat.Primes) : Fact p.1.Prime := ⟨p.2⟩

/-! ## `ιAt` and integral adeles -/

theorem ιAt_mul (v : HeightOneSpectrum (𝓞 ℚ)) (α β : ℍ[ℚ]) :
    ιAt v α * ιAt v β = ιAt v (α * β) := by
  apply piQ_injective
  intro w
  rw [map_mul]
  by_cases h : w = v
  · subst h; rw [piQ_ιAt_self, piQ_ιAt_self, piQ_ιAt_self, map_mul]
  · rw [piQ_ιAt_ne h, piQ_ιAt_ne h, piQ_ιAt_ne h, mul_one]

theorem ιAt_one (v : HeightOneSpectrum (𝓞 ℚ)) : ιAt v 1 = 1 := by
  apply piQ_injective
  intro w
  by_cases h : w = v
  · subst h; rw [piQ_ιAt_self, map_one, map_one]
  · rw [piQ_ιAt_ne h, map_one]

/-- `ιAt v α` as a unit (`α ≠ 0`). -/
def ιAtU (v : HeightOneSpectrum (𝓞 ℚ)) (α : ℍ[ℚ]) (hα : α ≠ 0) : ℍ[AQ]ˣ :=
  ⟨ιAt v α, ιAt v α⁻¹, by rw [ιAt_mul, mul_inv_cancel₀ hα, ιAt_one],
    by rw [ιAt_mul, inv_mul_cancel₀ hα, ιAt_one]⟩

theorem mem_integrals_of_ev {w : HeightOneSpectrum (𝓞 ℚ)} {a : AQ} (h : ‖ev w a‖ ≤ 1) :
    a w ∈ w.adicCompletionIntegers ℚ := by
  obtain ⟨x, hx, hxe⟩ := (Rat.HeightOneSpectrum.adicCompletion.padicEquiv_bijOn w).surjOn h
  have : x = a w := (pe w).injective hxe
  rw [← this]; exact hx

theorem integral_of_ev {a : AQ} (h : ∀ w, ‖ev w a‖ ≤ 1) :
    a ∈ FiniteAdeleRing.integralAdeles (𝓞 ℚ) ℚ := fun w => mem_integrals_of_ev (h w)

theorem eAt_mul_integral {v : HeightOneSpectrum (𝓞 ℚ)} {r : ℚ} (hr : ‖(r : ℚ_[Pw v])‖ ≤ 1) :
    eAt v * algebraMap ℚ AQ r ∈ FiniteAdeleRing.integralAdeles (𝓞 ℚ) ℚ := by
  refine integral_of_ev fun w => ?_
  rw [map_mul, ev_algebraMap]
  by_cases h : w = v
  · subst h; rw [ev_eAt_self, one_mul]; exact hr
  · rw [ev_eAt_ne h, zero_mul, norm_zero]; exact zero_le_one

theorem one_sub_eAt_integral (v : HeightOneSpectrum (𝓞 ℚ)) :
    1 - eAt v ∈ FiniteAdeleRing.integralAdeles (𝓞 ℚ) ℚ := by
  refine integral_of_ev fun w => ?_
  rw [map_sub, map_one]
  by_cases h : w = v
  · subst h; rw [ev_eAt_self]; simp
  · rw [ev_eAt_ne h]; simp

/-! ## `τ̂` on the base field -/

theorem tauHat_algebraMap_AQ (τ : QNeg 3 →ₐ[ℚ] ℍ[ℚ]) (z : AQ) :
    tauHat 3 τ (algebraMap AQ (FiniteAdeleRing (𝓞 (QNeg 3)) (QNeg 3)) z) = algebraMap AQ ℍ[AQ] z := by
  simp only [tauHat, RingHom.coe_comp, Function.comp_apply]
  change (AlgHom.liftEquiv ℚ AQ (QNeg 3) ℍ[AQ] ((qι).comp τ))
    ((TauCeti.GlobalNumberFields.finiteAdeleBaseChangeAlgEquiv ℚ (QNeg 3)).symm
      (algebraMap AQ _ z)) = _
  rw [AlgEquiv.commutes, AlgHom.commutes]

theorem algebraMap_AQ_integral {z : AQ} (hz : z ∈ FiniteAdeleRing.integralAdeles (𝓞 ℚ) ℚ) :
    algebraMap AQ (FiniteAdeleRing (𝓞 (QNeg 3)) (QNeg 3)) z ∈
      FiniteAdeleRing.integralAdeles (𝓞 (QNeg 3)) (QNeg 3) := by
  intro w'
  rw [IsDedekindDomain.algebraMap_finiteAdeleExtensionAlgebra,
    IsDedekindDomain.finiteAdeleExtension_apply]
  exact HeightOneSpectrum.adicCompletionExtension_mem_adicCompletionIntegers ℚ (QNeg 3) _ w'
    ⟨_, hz _⟩

theorem ωK_integral : algebraMap (QNeg 3) (FiniteAdeleRing (𝓞 (QNeg 3)) (QNeg 3))
    ((ωK : 𝓞 (QNeg 3)) : QNeg 3) ∈ FiniteAdeleRing.integralAdeles (𝓞 (QNeg 3)) (QNeg 3) :=
  (FiniteAdeleRing.algebraMap_mem_integralAdeles_iff _).mpr ⟨ωK, rfl⟩

theorem piQ_smul (w : HeightOneSpectrum (𝓞 ℚ)) (z : AQ) (y : ℍ[AQ]) :
    piQ w (z • y) = ev w z • piQ w y := by
  rw [Algebra.smul_def, map_mul, piQ_algebraMap, Quaternion.coe_mul_eq_smul]

theorem qp_comb {p : ℕ} [Fact p.Prime] (r1 r2 : ℚ) (ω y : ℍ[ℚ]) :
    qp p (r1 • (1 : ℍ[ℚ]) + r2 • ω + (4 : ℚ) • y) =
      (r1 : ℚ_[p]) • (1 : ℍ[ℚ_[p]]) + (r2 : ℚ_[p]) • qp p ω + (4 : ℚ_[p]) • qp p y := by
  ext <;> simp [qp]

/-- **`ιAt v α ∈ R̂_3`** for `α = r₁ + r₂ ω_s + 4ρ`, `r₁, r₂, ρ` integral at `2`. -/
theorem ιAt_mem_RnHat {τ : QNeg 3 →ₐ[ℚ] ℍ[ℚ]} {s : Signs}
    (hs : τ ((ωK : 𝓞 (QNeg 3)) : QNeg 3) = ωq s) (v : HeightOneSpectrum (𝓞 ℚ)) (r1 r2 : ℚ)
    (h1 : ‖(r1 : ℚ_[Pw v])‖ ≤ 1) (h2 : ‖(r2 : ℚ_[Pw v])‖ ≤ 1) (ρ : H4 ℚ)
    (hρ0 : ‖(ρ.a0 : ℚ_[Pw v])‖ ≤ 1) (hρ1 : ‖(ρ.a1 : ℚ_[Pw v])‖ ≤ 1)
    (hρ2 : ‖(ρ.a2 : ℚ_[Pw v])‖ ≤ 1) (hρ3 : ‖(ρ.a3 : ℚ_[Pw v])‖ ≤ 1) :
    ιAt v (r1 • (1 : ℍ[ℚ]) + r2 • ωq s + (4 : ℚ) • hur ρ) ∈ RnHat 3 τ := by
  set e := eAt v
  set z1 : AQ := (1 - e) + e * algebraMap ℚ AQ r1 with hz1
  set z2 : AQ := e * algebraMap ℚ AQ r2 with hz2
  set hr : ℍ[AQ] := algebraMap AQ ℍ[AQ] e * qι (hur ρ) with hhr
  have heq : ιAt v (r1 • (1 : ℍ[ℚ]) + r2 • ωq s + (4 : ℚ) • hur ρ) =
      algebraMap AQ ℍ[AQ] z1 + z2 • qι (ωq s) + 4 * hr := by
    apply piQ_injective
    intro w
    have a3 : piQ w (4 * hr) = (4 : ℚ_[Pw w]) • ((ev w e : ℚ_[Pw w]) • qp (Pw w : ℕ) (hur ρ)) := by
      rw [map_mul, map_ofNat, hhr, map_mul, piQ_algebraMap, piQ_qι,
        Quaternion.coe_mul_eq_smul, ← QuaternionAlgebra.coe_ofNat (R := ℚ_[Pw w])]
      exact Quaternion.coe_mul_eq_smul _ _
    have a1 : piQ w (algebraMap AQ ℍ[AQ] z1) = (ev w z1 : ℚ_[Pw w]) • (1 : ℍ[ℚ_[Pw w]]) := by
      rw [piQ_algebraMap, ← Quaternion.coe_mul_eq_smul, mul_one]
    have a2 : piQ w (z2 • qι (ωq s)) = (ev w z2 : ℚ_[Pw w]) • qp (Pw w : ℕ) (ωq s) := by
      rw [piQ_smul, piQ_qι]
    rw [map_add, map_add, a1, a2, a3]
    by_cases hw : w = v
    · subst hw
      rw [piQ_ιAt_self, qp_comb, hz1, hz2]
      simp only [map_add, map_sub, map_mul, map_one, ev_eAt_self, ev_algebraMap, sub_self,
        zero_add, one_mul, one_smul, e]
    · rw [piQ_ιAt_ne hw, hz1, hz2]
      simp only [map_add, map_sub, map_mul, map_one, ev_eAt_ne hw, sub_zero, zero_mul, add_zero,
        zero_smul, smul_zero, one_smul, e]
  rw [heq]
  have hz1i : z1 ∈ FiniteAdeleRing.integralAdeles (𝓞 ℚ) ℚ :=
    Subalgebra.add_mem _ (one_sub_eAt_integral v) (eAt_mul_integral h1)
  have hz2i : z2 ∈ FiniteAdeleRing.integralAdeles (𝓞 ℚ) ℚ := eAt_mul_integral h2
  refine AddSubgroup.add_mem _ (AddSubgroup.add_mem _ ?_ ?_) ?_
  · exact AddSubgroup.subset_closure (Or.inl ⟨_, algebraMap_AQ_integral hz1i,
      tauHat_algebraMap_AQ τ z1⟩)
  · refine AddSubgroup.subset_closure (Or.inl ⟨_, Subalgebra.mul_mem _
      (algebraMap_AQ_integral hz2i) ωK_integral, ?_⟩)
    rw [map_mul, tauHat_algebraMap_AQ, tauHat_algebraMap, hs, Algebra.smul_def]
  · refine AddSubgroup.subset_closure (Or.inr ⟨hr, ?_, rfl⟩)
    have ie : ∀ r : ℚ, ‖(r : ℚ_[Pw v])‖ ≤ 1 →
        e * algebraMap ℚ AQ r ∈ FiniteAdeleRing.integralAdeles (𝓞 ℚ) ℚ :=
      fun r hr' => eAt_mul_integral hr'
    refine ⟨e * algebraMap ℚ AQ ρ.a0, e * algebraMap ℚ AQ ρ.a1, e * algebraMap ℚ AQ ρ.a2, 0,
      e * algebraMap ℚ AQ ρ.a3, ie _ hρ0, ie _ hρ1, ie _ hρ2, Subalgebra.zero_mem _, ie _ hρ3, ?_⟩
    rw [hhr]
    have hd : ρ.a3 / 2 = ρ.a3 * (1 / 2) := by ring
    apply QuaternionAlgebra.ext <;>
      simp only [qι, hur, QuaternionAlgebra.algebraMap_eq, AlgHom.coe_mk, RingHom.coe_mk,
        MonoidHom.coe_mk, OneHom.coe_mk, Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul,
        Quaternion.imK_mul, hd, map_sub, map_add, map_mul] <;> ring

/-! ## The partner class -/

/-- Scalar multiple in `H4 ℚ`. -/
def smulQ (c : ℚ) (x : H4 ℚ) : H4 ℚ := ⟨c * x.a0, c * x.a1, c * x.a2, c * x.a3⟩

theorem hur_smulQ (c : ℚ) (x : H4 ℚ) : hur (smulQ c x) = c • hur x := by
  ext <;> simp [hur, smulQ] <;> ring

theorem star_hur (x : H4 ℚ) : star (hur x) = hur (starH x) := by
  apply hc_injective; rw [hc_star, hc_hur, hc_hur]

theorem ωq_star (s : Signs) : star (ωq s) = 1 - ωq s := by
  rw [ωq_eq]; ext <;> simp <;> ring

theorem partner_form (s : Signs) :
    twoRepQ (tstar s) = ((px s : ℤ) : ℚ) • (1 : ℍ[ℚ]) + (2 : ℚ) • ωq s +
      (4 : ℚ) • hur (mapH (Int.castRingHom ℚ) (pq s)) := by
  apply hc_injective
  rw [twoRepQ_eq, hc_hurZ, hc_add, hc_add, hc_smul, hc_smul, hc_smul, hc_one, ωq, hc_hurZ, hc_hur]
  have e := partner_eq s
  rw [H4.ext_iff] at e
  obtain ⟨e0, e1, e2, e3⟩ := e
  ext <;> simp only [mapH, eq_intCast]
  · rw [e0]; push_cast; ring
  · rw [e1]; push_cast; ring
  · rw [e2]; push_cast; ring
  · rw [e3]; push_cast; ring

theorem twoRepQ_ne_zero (t : Fin 2 × Fin 2 × Fin 2) : twoRepQ t ≠ 0 := by
  intro h
  have := congrArg Quaternion.normSq h
  rw [twoRepQ_eq, normSq_hurZ, map_zero] at this
  obtain ⟨r, hr⟩ := nrdH_βZ_odd t
  have : ((nrdH (βZ t) : ℤ) : ℚ) = 0 := this
  rw [hr] at this
  have : (2 * r + 1 : ℤ) = 0 := by exact_mod_cast this
  omega

theorem norm_int_div_odd {p : ℕ} [Fact p.Prime] (hp : p = 2) (m N : ℤ) (hN : Odd N) :
    ‖(((m : ℚ) / N : ℚ) : ℚ_[p])‖ ≤ 1 := by
  subst hp
  have hN1 : ‖((N : ℚ) : ℚ_[2])‖ = 1 := by
    push_cast
    refine le_antisymm (Padic.norm_int_le_one _) (not_lt.mp fun hlt => ?_)
    have := Padic.norm_intCast_lt_one_iff.mp hlt
    obtain ⟨r, hr⟩ := hN; omega
  push_cast
  rw [norm_div]
  push_cast at hN1
  rw [hN1, div_one]
  exact Padic.norm_int_le_one m

theorem norm_int_le {p : ℕ} [Fact p.Prime] (m : ℤ) : ‖(((m : ℚ)) : ℚ_[p])‖ ≤ 1 := by
  push_cast; exact Padic.norm_int_le_one m

/-- **The partner class lies in `B^× H`.** -/
theorem partner_mem {τ : QNeg 3 →ₐ[ℚ] ℍ[ℚ]} {s : Signs}
    (hs : τ ((ωK : 𝓞 (QNeg 3)) : QNeg 3) = ωq s) {v : HeightOneSpectrum (𝓞 ℚ)} (hv : IsPlaceTwo v) :
    ∃ h ∈ Hgrp τ, twoRep v (tstar s) = qι 1 * ↑h := by
  obtain ⟨β, hβdef⟩ : ∃ β, β = twoRepQ (tstar s) := ⟨_, rfl⟩
  have hβ : β ≠ 0 := by rw [hβdef]; exact twoRepQ_ne_zero _
  refine ⟨ιAtU v β hβ, ?_, by
    rw [map_one, one_mul]; change ιAt v (twoRepQ (tstar s)) = ιAt v β; rw [hβdef]⟩
  apply Subgroup.subset_closure
  left
  apply Subgroup.subset_closure
  left
  have hp2 := Pw_eq_two hv
  set N : ℤ := nrdH (βZ (tstar s))
  have hNodd : Odd N := nrdH_βZ_odd _
  have hNq : Quaternion.normSq β = (N : ℚ) := by
    rw [hβdef, twoRepQ_eq, normSq_hurZ]
  constructor
  · change ιAt v β ∈ RnHat 3 τ
    rw [hβdef, partner_form]
    exact ιAt_mem_RnHat hs v _ _ (norm_int_le _) (by simpa using norm_int_le (p := (Pw v : ℕ)) 2) _
      (norm_int_le _) (norm_int_le _) (norm_int_le _) (norm_int_le _)
  · change ιAt v β⁻¹ ∈ RnHat 3 τ
    have hinv : β⁻¹ = (((px s + 2 : ℤ) : ℚ) / N) • (1 : ℍ[ℚ]) + ((-2 : ℤ) / (N : ℚ)) • ωq s +
        (4 : ℚ) • hur (smulQ (1 / N) (mapH (Int.castRingHom ℚ) (starH (pq s)))) := by
      rw [Quaternion.inv_def, hNq, hur_smulQ]
      conv_lhs => rw [hβdef, partner_form]
      rw [star_add, star_add, Quaternion.star_smul, Quaternion.star_smul, Quaternion.star_smul,
        star_one, ωq_star, star_hur, ← mapH_starH]
      have hN0 : (N : ℚ) ≠ 0 := by
        intro h0; have : N = 0 := by exact_mod_cast h0
        obtain ⟨r, hr⟩ := hNodd; omega
      push_cast
      simp only [smul_add, smul_sub, smul_smul]
      field_simp
      module
    rw [hinv]
    refine ιAt_mem_RnHat hs v _ _ (norm_int_div_odd hp2 _ _ hNodd) (norm_int_div_odd hp2 _ _ hNodd)
      _ ?_ ?_ ?_ ?_ <;>
    · simp only [smulQ, mapH, eq_intCast]
      rw [one_div_mul_eq_div]
      exact norm_int_div_odd hp2 _ _ hNodd

end ZInQ.Contrib.T21Proof
