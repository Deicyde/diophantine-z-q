import ZInQKernel.Contrib.OneProof.ConradAppB.Defs

/-!
# Finite inertia from the three inputs

The unramified part is removed with its period, the result is induced to `ℂ_p ⊗ L`, and the
normalized-trace theorem on the cyclotomic tower over `ℚ_p` shows that the remaining
character has finite order.
-/

set_option autoImplicit false

noncomputable section

namespace ZInQ.Contrib.SenWeightZero

open ZInQ.Contrib.CloudB3W11TateTrace
open scoped TensorProduct

theorem cpVal_mul (p : ℕ) [Fact p.Prime] {L : IntermediateField ℚ_[p] (PadicAlgCl p)}
    (a b : Lˣ) : cpVal p (a * b) = cpVal p a * cpVal p b :=
  map_mul ((IsScalarTower.toAlgHom ℚ_[p] (PadicAlgCl p) ℂ_[p]).comp L.val) (a : L) (b : L)

theorem cpVal_ne_zero (p : ℕ) [Fact p.Prime] {L : IntermediateField ℚ_[p] (PadicAlgCl p)}
    (a : Lˣ) : cpVal p a ≠ 0 :=
  (map_ne_zero ((IsScalarTower.toAlgHom ℚ_[p] (PadicAlgCl p) ℂ_[p]).comp L.val)).mpr a.ne_zero

/-- **Finite inertia from a weight-zero period**, from the three inputs. -/
theorem finite_inertia_of_period (hS : UnramifiedCyclotomicSplitting) (hU : UnramifiedPeriod)
    (hI : PeriodInduction) (p : ℕ) [Fact p.Prime] (L : IntermediateField ℚ_[p] (PadicAlgCl p))
    [FiniteDimensional ℚ_[p] L] [IsGalois ℚ_[p] L]
    (χ : (PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p) →* Lˣ)
    (hcont : Continuous (fun σ => (((χ σ : Lˣ) : L) : PadicAlgCl p)))
    (c : ℂ_[p]) (hc0 : c ≠ 0) (hc : ∀ σ ∈ L.fixingSubgroup, σ • c = cpVal p (χ σ) * c) :
    (Set.range fun σ : ↥(L.fixingSubgroup ⊓ TauCeti.inertiaSubgroup ℚ_[p]) => χ σ.1).Finite := by
  classical
  obtain ⟨μ, η, hχ, hμcont, hμI, hηcyc⟩ := hS p L χ hcont
  obtain ⟨u, hu0, hu⟩ := hU p L μ hμcont hμI
  -- remove the unramified part
  have hc' : ∀ σ ∈ L.fixingSubgroup, σ • (c * u⁻¹) = cpVal p (η σ) * (c * u⁻¹) := by
    intro σ hσ
    have hμ0 := cpVal_ne_zero p (μ σ)
    rw [smul_mul', smul_inv'', hc σ hσ, hu σ hσ, hχ σ, cpVal_mul]
    field_simp
  obtain ⟨x, hx0, hx⟩ := hI p L η (c * u⁻¹) (mul_ne_zero hc0 (inv_ne_zero hu0)) hc'
  -- decompletion on the cyclotomic tower over `ℚ_p`
  let Kb : IntermediateField ℚ_[p] (PadicAlgCl p) := ⊥
  let Km : ℕ → IntermediateField ℚ_[p] (PadicAlgCl p) := CyclotomicTrace.TCT.F p
  let ψ : Kb.fixingSubgroup →* Lˣ := η.comp (Subgroup.subtype _)
  have hψ' : ∀ σ : Kb.fixingSubgroup,
      (∀ m : ℕ, (σ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p) ∈ (Km m).fixingSubgroup) →
        ψ σ = 1 := by
    intro σ hσ
    apply hηcyc
    apply (TauCeti.cyclotomicCharacter_eq_one_iff p).mpr
    intro n ζ hζ
    exact (IntermediateField.mem_fixingSubgroup_iff (Km n) (σ : _)).mp (hσ n) ζ
      (PadicAlgCl.cyclotomicTower_mono p (Nat.le_add_right n 2)
        (PadicAlgCl.mem_cyclotomicTower_of_pow_eq_one p hζ))
  have hxσ : ∀ σ : Kb.fixingSubgroup,
      Algebra.TensorProduct.map (PadicComplex.galAlgHom p (σ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p))
          (AlgHom.id ℚ_[p] L) x =
        ((1 : ℂ_[p]) ⊗ₜ[ℚ_[p]] ((ψ σ : Lˣ) : L)) * x :=
    fun σ => hx σ
  obtain ⟨d, -, hR⟩ := CyclotomicTrace.solution p
  obtain ⟨n, hn, hfin⟩ := TensorTwist.solution p Kb Km (CyclotomicTrace.TCT.F_mono p)
    (fun _ => bot_le) (CyclotomicTrace.TCT.finiteDimensional_F p) d 0
    (fun m _ => hR m) L ψ hψ' x hx0 hxσ
  -- on inertia, `χ = η` has order dividing `n`
  have hbot : ∀ σ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p, σ ∈ Kb.fixingSubgroup := by
    intro σ
    simp [Kb, IntermediateField.fixingSubgroup_bot]
  have : NeZero n := ⟨hn.ne'⟩
  refine (Set.finite_coe_iff.mp (inferInstance : Finite (rootsOfUnity n L))).subset ?_
  rintro _ ⟨σ, rfl⟩
  have hσI : IsInertia p σ.1 := (Subgroup.mem_inf.mp σ.2).2
  have hη : η σ.1 ^ n = 1 := hfin ⟨σ.1, hbot σ.1⟩
  change χ σ.1 ∈ rootsOfUnity n L
  rw [mem_rootsOfUnity, hχ σ.1, hμI σ.1 hσI, one_mul, hη]

theorem senFiniteInertia_of_inputs (hS : UnramifiedCyclotomicSplitting)
    (hU : UnramifiedPeriod) (hI : PeriodInduction) : SenFiniteInertia :=
  fun p _ L _ _ χ hcont c hc0 hc => finite_inertia_of_period hS hU hI p L χ hcont c hc0 hc

end ZInQ.Contrib.SenWeightZero
