import ZInQKernel.Contrib.OneProof.DS965Reroute.RepExists

/-! # `r11r12 : PanBerger` without Diamond–Shurman 9.6.5 (ds965-reroute)

`PanDict.panBerger_of_F` reads its Diamond–Shurman arguments (`DSThm965Printed`,
`EigenformCoeffFieldFinite`, `DSThm966Printed`) only through
`PanBergerSplit.coeff_mem_range`, that is, only for the algebraicity of the Hecke eigenvalue
`a_q(g)` of Pan's eigenform `g` (weight `k ≥ 1`). Any semisimple representation attached to
`g` gives it (`coeff_mem_range_of_rep`). `panBerger_of_F'` is `panBerger_of_F` with that one
step replaced; `panBerger_of_F_mht` takes the representation from the live rows
`modularHTCoeff` and `dsThm966Printed` (`DS965Reroute.eigenformRepExistsG9_of_modularHT`).
-/

namespace HDec
namespace PkgI4
namespace PanDict

open BmaxOne BergerBst PanBergerSplit FontaineSt

/-- **Algebraicity of Hecke eigenvalues from `EigenformRepExists`** (any weight `k ≥ 1`): the trace
clause of an attached representation at `q ∤ Nℓ` gives `a_q(g) ∈ ι_C(ℚ̄)`. Replaces
`coeff_mem_range`, which reached the same representation through `r14Det_of_printed`. -/
theorem coeff_mem_range_of_rep (hR : ZInQ.Contrib.G9.PkgI4.EigenformRepExists) (ℓ : ℕ)
    [Fact ℓ.Prime] (ιC : Qbar →ₐ[ℚ] ℂ) (ιL : Qbar →ₐ[ℚ] PadicAlgCl ℓ) {N : ℕ} {k : ℤ}
    {χ : DirichletCharacter ℂ N} {g : CF N k} (hN : 0 < N) (hk : 1 ≤ k)
    (hg : IsNormalizedEigenform g χ) {q : ℕ} (hq : q.Prime) (hqN : ¬ q ∣ N * ℓ) :
    ∃ α : Qbar, ιC α = coeff g q := by
  obtain ⟨ρg, -, hatt⟩ := hR ℓ ιC ιL N k χ g hN hk hg
  obtain ⟨-, α, hα, -⟩ := hatt q hq hqN
  exact ⟨α, hα⟩

/-- **`r11r12 : PanBerger` from Pan's and Berger's theorems over Fontaine's `B_st`, without the
Diamond–Shurman arguments**: `panBerger_of_F` verbatim except that the algebraicity of
`a_q(g)` comes from `EigenformRepExists` (`coeff_mem_range_of_rep`). -/
theorem panBerger_of_F' (hP : PanPrintedF) (hB : BergerSurveyF)
    (hR : ZInQ.Contrib.G9.PkgI4.EigenformRepExists) : PanBerger := by
  intro p _ hp ρ hirr hfr hdr hodd hdist
  have hdr' : LocalIsDeRhamU p 2 ((dualRep ρ).restrictLocal p) := by
    rw [dualRep_restrictLocal]
    exact localIsDeRhamU_dualHom p _ hdr
  have hpst' := bergerB_F_of_survey hB p 2 _ ((dualRep ρ).continuous_toHom.comp
    (Field.absoluteGaloisGroup.map (algebraMap ℚ ℚ_[p])).continuous) hdr'
  have hht' : LocalDistinctHTU p ((dualRep ρ).restrictLocal p) := by
    rw [dualRep_restrictLocal]
    exact localDistinctHTU_dualHom p ρ hdist
  obtain ⟨Φ⟩ := exists_complex_equiv p
  obtain ⟨N, k, χ, g, hN, hk, hg, ψ, S, htr⟩ := panPrintedB_F_of_printedF hP p hp Φ.symm (dualRep ρ)
    (dualRep_isIrreducible ρ hirr) (dualRep_finitelyRamified ρ hfr) hpst'
    (dualRep_isOdd ρ hodd) hht'
  obtain ⟨Sr, hSr⟩ := hfr
  let ιC : Qbar →ₐ[ℚ] ℂ := IsAlgClosed.lift
  let ιL : Qbar →ₐ[ℚ] PadicAlgCl p := (Φ : ℂ →+* PadicAlgCl p).toRatAlgHom.comp ιC
  refine ⟨N, k, χ, g, hN, hk, hg, charInv ψ, ιC, ιL, S ∪ Sr ∪ Finset.range (N * p + 1), ?_⟩
  intro q hq hqS
  simp only [Finset.mem_union, Finset.mem_range, not_or, not_lt] at hqS
  obtain ⟨⟨hqS, hqSr⟩, hqNp⟩ := hqS
  have hNp : 0 < N * p := Nat.mul_pos hN (Fact.out : p.Prime).pos
  have hqdvd : ¬ q ∣ N * p := fun h => by
    have := Nat.le_of_dvd hNp h
    omega
  refine ⟨hSr q hq hqSr, ?_⟩
  obtain ⟨α, hα⟩ := coeff_mem_range_of_rep hR p ιC ιL hN hk hg hq hqdvd
  refine ⟨α, hα, fun v σ hv hσ => ?_⟩
  have h1 := htr q hq hqS v σ hv hσ
  rw [trace_dualRep_inv] at h1
  rw [h1, charInv_apply]
  congr 1
  change Φ.symm.symm (coeff g q) = Φ (ιC α)
  rw [hα]
  rfl

/-- **`r11r12 : PanBerger` from `panPrintedF`, `bergerSurveyF`, `modularHTCoeff` and
`dsThm966Printed`** (no Diamond–Shurman 9.6.5). -/
theorem panBerger_of_F_mht (hP : PanPrintedF) (hB : BergerSurveyF)
    (h : HTNewAssembly.ModularHTCoeff) (hDS : DSThm966EV.DSThm966Printed) : PanBerger :=
  panBerger_of_F' hP hB (DS965Reroute.eigenformRepExistsG9_of_modularHT h hDS)

end PanDict
end PkgI4
end HDec
