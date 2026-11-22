import ZInQKernel.Contrib.CloudB3W11TateTrace.CyclotomicTrace
import ZInQKernel.Contrib.CloudB3W11TateTrace.TensorTwist
import ZInQKernel.Contrib.CloudB3W11Cyclotomic.InfiniteImage
import TauCeti.NumberTheory.Cyclotomic.CyclotomicCharacter

/-!
# Whole-group nonzero-twist vanishing in the genuine `C_p`

Adapted from anthropics/fermats-last-theorem, commit
6e837e75355538c7f80bab5b956861e86c4eacc2,
`P2M/Sol/S_PadicComplex_eq_zero_of_forall_smul_eq_cyclotomicCharacter_zpow_mul.lean`;
Copyright 2026 Anthropic, PBC; Apache License 2.0 (see LICENSE and NOTICE).

The genuine continuous Tate trace is proved in `CyclotomicTrace`. The
finite-order-character conclusion is proved in `TensorTwist`. The arithmetic
infinite-image finishing step is REUSED from Author D's compiled theorem,
not duplicated here. The character is local, so no global-Qbar transport,
P2M utilities or new notation is imported.
-/

set_option autoImplicit false
set_option linter.style.haveILetI false
set_option linter.style.longLine false

noncomputable section

namespace ZInQ.Contrib.CloudB3W11TateTrace.TwistWholeGroup

open ZInQ.Contrib.G9.PkgI4
open scoped TensorProduct

/-- A nonzero cyclotomic twist has no invariant in the genuine `C_p` for
`G_{ℚ_p}`. All trace and arithmetic inputs are compiled proofs, not hypotheses. -/
theorem solution (p : ℕ) [Fact p.Prime] (k : ℤ) (hk : k ≠ 0) (c : ℂ_[p])
    (hc : ∀ σ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p,
      σ • c = (algebraMap ℚ_[p] ℂ_[p]
        (((cyclotomicCharacter (PadicAlgCl p) p σ.toRingEquiv : ℤ_[p]ˣ) : ℤ_[p]) : ℚ_[p])) ^ k * c) :
    c = 0 := by
  by_contra hc0
  let Kb : IntermediateField ℚ_[p] (PadicAlgCl p) := ⊥
  let Km : ℕ → IntermediateField ℚ_[p] (PadicAlgCl p) := CyclotomicTrace.TCT.F p
  let χQ : GQp p →* ℚ_[p]ˣ :=
    (Units.map (PadicInt.Coe.ringHom (p := p) : ℤ_[p] →* ℚ_[p])).comp
      (ZInQ.Contrib.CloudB3W11Cyclotomic.cycHom p)
  have hχQ : ∀ σ : GQp p, ((χQ σ : ℚ_[p]ˣ) : ℚ_[p]) = ((cyc p σ : ℤ_[p]) : ℚ_[p]) :=
    fun _ => rfl
  let ψ : Kb.fixingSubgroup →* ℚ_[p]ˣ := (zpowGroupHom k).comp (χQ.comp (Subgroup.subtype _))
  have hψ : ∀ σ : Kb.fixingSubgroup,
      ((ψ σ : ℚ_[p]ˣ) : ℚ_[p]) = ((cyc p σ : ℤ_[p]) : ℚ_[p]) ^ k := by
    intro σ
    simp only [ψ, MonoidHom.coe_comp, Function.comp_apply, Subgroup.coe_subtype,
      zpowGroupHom_apply, Units.val_zpow_eq_zpow_val, hχQ]
  have hc' : ∀ σ : GQp p,
      σ • c = (algebraMap ℚ_[p] ℂ_[p] ((cyc p σ : ℤ_[p]) : ℚ_[p])) ^ k * c := hc
  let x : TensorProduct ℚ_[p] ℂ_[p] ℚ_[p] := c ⊗ₜ[ℚ_[p]] (1 : ℚ_[p])
  have hx : x ≠ 0 := by
    intro h
    apply hc0
    have h2 : (TensorProduct.rid ℚ_[p] ℂ_[p]) x = (TensorProduct.rid ℚ_[p] ℂ_[p]) 0 := by rw [h]
    rw [LinearEquiv.map_zero] at h2
    simpa [x] using h2
  have hxσ : ∀ σ : Kb.fixingSubgroup,
      Algebra.TensorProduct.map (PadicComplex.galAlgHom p (σ : GQp p)) (AlgHom.id ℚ_[p] ℚ_[p]) x =
        ((1 : ℂ_[p]) ⊗ₜ[ℚ_[p]] ((ψ σ : ℚ_[p]ˣ) : ℚ_[p])) * x := by
    intro σ
    simp only [x, Algebra.TensorProduct.map_tmul, PadicComplex.galAlgHom_apply,
      AlgHom.coe_id, id_eq, Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_one]
    rw [hc', hψ, ← map_zpow₀, Algebra.algebraMap_eq_smul_one,
      smul_mul_assoc, one_mul, TensorProduct.smul_tmul]
    simp only [smul_eq_mul, mul_one]
  obtain ⟨d, -, hR⟩ := CyclotomicTrace.solution p
  have hψ' : ∀ σ : Kb.fixingSubgroup,
      (∀ m : ℕ, (σ : GQp p) ∈ (Km m).fixingSubgroup) → ψ σ = 1 := by
    intro σ hσ
    have hchar : cyc p (σ : GQp p) = 1 := by
      change cyclotomicCharacter (PadicAlgCl p) p (σ : GQp p).toRingEquiv = 1
      apply (TauCeti.cyclotomicCharacter_eq_one_iff p).mpr
      intro n ζ hζ
      exact (IntermediateField.mem_fixingSubgroup_iff (Km n) (σ : GQp p)).mp (hσ n) ζ
        (PadicAlgCl.cyclotomicTower_mono p (Nat.le_add_right n 2)
          (PadicAlgCl.mem_cyclotomicTower_of_pow_eq_one p hζ))
    apply Units.ext
    rw [hψ, hchar, Units.val_one, PadicInt.coe_one, one_zpow, Units.val_one]
  obtain ⟨n, hn, hfin⟩ := TensorTwist.solution p Kb Km (CyclotomicTrace.TCT.F_mono p)
    (fun _ => bot_le) (CyclotomicTrace.TCT.finiteDimensional_F p) d 0
    (fun m _ => hR m) ℚ_[p] ψ hψ' x hx hxσ
  have hinjU : Function.Injective (Units.map (PadicInt.Coe.ringHom (p := p) : ℤ_[p] →* ℚ_[p])) := by
    intro u v huv
    apply Units.ext
    have h' := congrArg (fun w : ℚ_[p]ˣ => (w : ℚ_[p])) huv
    simp only [Units.coe_map] at h'
    exact Subtype.val_injective h'
  apply hk
  apply ZInQ.Contrib.CloudB3W11Cyclotomic.eq_zero_of_exists_pow_cyc_zpow_eq_one p Kb k
  refine ⟨n, hn, fun σ hσ => ?_⟩
  apply hinjU
  rw [map_pow, map_one, map_zpow]
  simpa only [ψ, χQ, MonoidHom.coe_comp, Function.comp_apply, Subgroup.coe_subtype,
    zpowGroupHom_apply, ZInQ.Contrib.CloudB3W11Cyclotomic.cycHom_apply] using hfin ⟨σ, hσ⟩

end ZInQ.Contrib.CloudB3W11TateTrace.TwistWholeGroup

end
