import ZInQKernel.Contrib.OneProof.GrossZagierOptimal

/-!
# period-odd: the period lattice of a weight-2 newform is not zero

Task period-odd (2026-11-16). Report `docs/research/period-odd.md`.

`periodLattice_ne_zero`: for every weight-2 newform `f` of level `N`, some period
`φ_f(γτ) − φ_f(τ)`, `γ ∈ Γ₀(N)`, of the Eichler integral `φ_f` is nonzero.

Proof. Otherwise `φ_f` is `Γ₀(N)`-invariant. It is holomorphic on `ℍ` (`mdiff_eichler`) and, at
every cusp `γ∞`, `φ_f(γτ) = K₀ + Σ_{m ≥ 1} b_m q_N^m` (gz-heegner's `exists_const_eichler`) is
bounded. So `φ_f` is a modular form of weight `0` for `Γ₀(N)`, hence constant (Mathlib's
`ModularForm.eq_const_of_weight_zero`), and `f = D φ_f = 0` (`D_eichler`), contradicting `f ≠ 0`.

No `sorry`, no `axiom`.
-/

noncomputable section

open UpperHalfPlane Filter Topology CongruenceSubgroup HeckeRing.GL2
open scoped MatrixGroups ModularForm

namespace ZInQ.PeriodOdd

open ZInQ.GZHeegner in
/-- **The period lattice of a weight-2 newform is not zero.** -/
theorem periodLattice_ne_zero {N : ℕ} [NeZero N] (f : Newform N 2) :
    ∃ l ∈ ZInQ.GZOptimal.periodLattice f, l ≠ 0 := by
  by_contra hcon
  push Not at hcon
  have hinv : ∀ γ ∈ Gamma0 N, ∀ τ : ℍ, ZInQ.GZHL3.eichler f (γ • τ) = ZInQ.GZHL3.eichler f τ :=
    fun γ hγ τ => sub_eq_zero.mp (hcon _ (Submodule.subset_span ⟨γ, hγ, τ, rfl⟩))
  let F : ModularForm ((Gamma0 N : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)) 0 :=
    { toFun := ZInQ.GZHL3.eichler f
      slash_action_eq' := by
        intro γ hγ
        obtain ⟨g, hg, rfl⟩ := Subgroup.mem_map.mp hγ
        change (ZInQ.GZHL3.eichler f ∣[(0 : ℤ)] g) = _
        rw [eichler_slash]
        funext τ
        exact hinv g hg τ
      holo' := mdiff_eichler f
      bdd_at_cusps' := by
        intro c hc
        rw [OnePoint.isBoundedAt_iff_forall_SL2Z (hc.mono (Subgroup.map_le_range _ _))]
        intro γ _
        rw [eichler_slash]
        obtain ⟨K₀, hK⟩ := exists_const_eichler f γ
        have hN : (0 : ℝ) < N := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N)
        have h1 := (analyticAt_Gser f γ).continuousAt.tendsto.comp (qParam_tendsto_atImInfty hN)
        have ht : Tendsto (fun τ : ℍ => ZInQ.GZHL3.eichler f (γ • τ)) atImInfty
            (𝓝 (K₀ + (Gser f γ).sum 0)) := by
          have e : (fun τ : ℍ => ZInQ.GZHL3.eichler f (γ • τ)) =
              fun τ => K₀ + ((Gser f γ).sum ∘ fun τ : ℍ => Function.Periodic.qParam (N : ℝ) τ) τ := by
            funext τ
            rw [hK, Gq_eq]
            rfl
          rw [e]
          exact tendsto_const_nhds.add h1
        exact ht.isBigO_one ℝ }
  obtain ⟨c, hc⟩ := ModularForm.eq_const_of_weight_zero F
  have hE : ZInQ.GZHL3.eichler f = fun _ => c := hc
  have hfz : (f.toCuspForm : ℍ → ℂ) = 0 := by
    rw [← D_eichler f, hE]
    funext τ
    simp [Derivative.normalizedDerivOfComplex, Function.comp_def]
  exact f.ne_zero (CuspForm.ext fun τ => congrFun hfz τ)

end ZInQ.PeriodOdd
