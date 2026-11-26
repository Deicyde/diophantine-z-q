import ZInQKernel.OneProof.H.TailZ102

/-! # Representations attached to eigenforms without Diamond–Shurman 9.6.5 (ds965-reroute)

R14 without its determinant (`EigenformRepExists`) from the live rows `modularHTCoeff`
(weight `k ≥ 2`) and `dsThm966Printed` (weight `1`), with no use of `dsThm965AtPrimes`:

* weight `k ≥ 2`, newforms: `modularHTCoeff` gives, at every level and every `ℓ`, a
  continuous `ρ` unramified outside `Nℓ` whose Frobenius traces are the `a_p` (in one of two
  normalizations). The steps are those of `EigenformHTPrinted.eigenformHTNew_of_printed`:
  `modularHTPrinted_of_coeff`, the algebraicity of the `a_p` (`exists_alg_coeff` with
  `eigenformCoeffFieldFinite_proof`), dualization in the geometric normalization
  (`dual_arith_of_geom`, `htDual`), semisimplification (`exists_ss`) and `attached_of_trace`;
* weight `k ≥ 2`, eigenforms of any level: T25 (`HodgeLF7.newformOfEigenformG9`, proved)
  gives a newform of level `N ∣ M` with the same `a_p` for `p ∤ M`; a representation attached
  to it is attached to the eigenform, since `p ∤ Mℓ` implies `p ∤ Nℓ` (the step of
  `eigenformHT_of_new`);
* weight `1`: `artinTransport_proof` from Deligne–Serre (`DSThm966EV.dsThm966_of_printed`).

The determinant clause of `R14Det` is not produced: traces at primes do not determine it, and
the live route does not read it.
-/

namespace DS965Reroute

open ZInQ.Contrib.HodgeSplit ZInQ.Contrib.G9 ZInQ.Contrib.G9.PkgI4

/-- Weight `k ≥ 2`, newforms (G9 layer): a semisimple attached representation from
`modularHTCoeff`. -/
theorem newformRep_of_modularHT (h : HTNewAssembly.ModularHTCoeff) (ℓ : ℕ) [Fact ℓ.Prime]
    (ιC : Qbar →ₐ[ℚ] ℂ) (ιL : Qbar →ₐ[ℚ] PadicAlgCl ℓ) {N : ℕ} {k : ℤ}
    {χ : DirichletCharacter ℂ N} {f : CF N k} (hN : 0 < N) (hk : 2 ≤ k) (hf : IsNewform f χ) :
    ∃ ρ : GaloisRep ℓ 2, ρ.IsSemisimple ∧ ρ.AttachedTo ιC ιL f := by
  obtain ⟨_, g, rfl, -⟩ := (NewformDict.g9_isNewform_iff hN).mp hf
  have halg : ∀ p : ℕ, ∃ α : Qbar, ιC α = coeff (g.toCuspForm : CF N k) p :=
    EigenformHTPrinted.exists_alg_coeff eigenformCoeffFieldFinite_proof ιC hN hk hf.1
  obtain ⟨ρ₀, h₀⟩ := HTNewAssembly.modularHTPrinted_of_coeff h ℓ ιC ιL N k g hk
  have key : ∃ ρ₁ : GaloisRep ℓ 2, ρ₁.AttachedTo ιC ιL (g.toCuspForm : CF N k) ∧
      ρ₁.HasHTWeightsAtSelf ℓ {0, 1 - k} := by
    rcases h₀ with ⟨ha, hHT⟩ | ⟨hg, hHT⟩
    · exact ⟨ρ₀, EigenformHTPrinted.attached_of_univ halg ha, hHT⟩
    · refine ⟨EigenformHTPrinted.dualGR ρ₀, EigenformHTPrinted.attached_of_univ halg
        (EigenformHTPrinted.dual_arith_of_geom ρ₀ hg), ?_⟩
      have h2 := EigenformHTPrinted.htDual ℓ 2 ρ₀ {0, k - 1} (by simp) hHT
      have hS : (({0, k - 1} : Multiset ℤ).map Neg.neg) = {0, 1 - k} := by
        simp only [Multiset.insert_eq_cons, Multiset.map_cons, Multiset.map_singleton, neg_zero,
          neg_sub]
      rwa [hS] at h2
  obtain ⟨ρ₁, ha₁, hHT₁⟩ := key
  obtain ⟨ρ', hss', -, htr, hun⟩ := EigenformHTPrinted.exists_ss ρ₁ {0, 1 - k} (by simp) hHT₁
  exact ⟨ρ', hss', EigenformHTPrinted.attached_of_trace ha₁ htr hun⟩

/-- Weight `k ≥ 2`, normalized eigenforms of any level (G9 layer), through T25. -/
theorem eigenformRep_wtGe2 (h : HTNewAssembly.ModularHTCoeff) (ℓ : ℕ) [Fact ℓ.Prime]
    (ιC : Qbar →ₐ[ℚ] ℂ) (ιL : Qbar →ₐ[ℚ] PadicAlgCl ℓ) {M : ℕ} {k : ℤ}
    {χ : DirichletCharacter ℂ M} {g : CF M k} (hM : 0 < M) (hk : 2 ≤ k)
    (hg : IsNormalizedEigenform g χ) :
    ∃ ρ : GaloisRep ℓ 2, ρ.IsSemisimple ∧ ρ.AttachedTo ιC ιL g := by
  obtain ⟨N, χ', f, hN, hNM, hf, hcoef⟩ :=
    HDec.HSyn.HodgeLF7.newformOfEigenformG9 M k χ g hM hg
  obtain ⟨ρ, hss, hatt⟩ := newformRep_of_modularHT h ℓ ιC ιL hN hk hf
  refine ⟨ρ, hss, fun p hp hpM => ?_⟩
  have hpN : ¬ p ∣ N * ℓ := fun hd => hpM (by
    rcases (Nat.Prime.dvd_mul hp).mp hd with h1 | h1
    · exact Dvd.dvd.mul_right (h1.trans hNM) ℓ
    · exact Dvd.dvd.mul_left h1 M)
  have hpM' : ¬ p ∣ M := fun hd => hpM (Dvd.dvd.mul_right hd ℓ)
  obtain ⟨hu, α, hα, htr⟩ := hatt p hp hpN
  exact ⟨hu, α, hα.trans (hcoef p hp hpM'), htr⟩

/-- Weight `1` (G9 layer), from Deligne–Serre through `artinTransport_proof`. -/
theorem eigenformRep_wt1 (hDS : DSThm966EV.DSThm966Printed) (ℓ : ℕ) [Fact ℓ.Prime]
    (ιC : Qbar →ₐ[ℚ] ℂ) (ιL : Qbar →ₐ[ℚ] PadicAlgCl ℓ) {N : ℕ}
    {χ : DirichletCharacter ℂ N} {g : CF N 1} (hN : 0 < N) (hg : IsNormalizedEigenform g χ) :
    ∃ ρ : GaloisRep ℓ 2, ρ.IsSemisimple ∧ ρ.AttachedTo ιC ιL g := by
  obtain ⟨ρ, hss, hatt, -⟩ :=
    artinTransport_proof (DSThm966EV.dsThm966_of_printed hDS) ℓ ιC ιL N χ g hN hg
  exact ⟨ρ, hss, hatt⟩

/-- **R14 without its determinant, on the G9 layer, from the live rows** `modularHTCoeff` and
`dsThm966Printed`. This is the type that `eigenformHT_of_kato` reads. -/
theorem eigenformRepExistsG9_of_modularHT (h : HTNewAssembly.ModularHTCoeff)
    (hDS : DSThm966EV.DSThm966Printed) : ZInQ.Contrib.G9.PkgI4.EigenformRepExists := by
  intro ℓ _ ιC ιL N k χ g hN hk hg
  rcases eq_or_lt_of_le hk with hk1 | hk2
  · subst hk1
    exact eigenformRep_wt1 hDS ℓ ιC ιL hN hg
  · exact eigenformRep_wtGe2 h ℓ ιC ιL hN (by omega) hg

/-- `EigenformRepExists` moved from the G9 layer to the chain's copy `HSyn.EigenformRepExists`
(same statement over `HSyn`'s copies of the objects; the converse of
`eigenformRepExists_of_hsyn`). -/
theorem eigenformRepExists_hsyn_of_g9 (h : ZInQ.Contrib.G9.PkgI4.EigenformRepExists) :
    HDec.HSyn.EigenformRepExists := by
  intro ℓ _ ιC ιL N k χ g hN hk hg
  obtain ⟨ρ, hss, hatt⟩ := h ℓ ιC ιL N k χ g hN hk hg
  exact ⟨⟨ρ.toHom, ρ.continuous_toHom⟩, hss, hatt⟩

/-- **R14 without its determinant, on the chain's copy** (`HSyn.EigenformRepExists`, the type of
the field `r14` of the chain's `ResearchLeaves3` bundles), from `modularHTCoeff` and
`dsThm966Printed`. -/
theorem eigenformRepExists_of_modularHT (h : HTNewAssembly.ModularHTCoeff)
    (hDS : DSThm966EV.DSThm966Printed) : HDec.HSyn.EigenformRepExists :=
  eigenformRepExists_hsyn_of_g9 (eigenformRepExistsG9_of_modularHT h hDS)

/-- **R13 (`EigenformHT`, G9 layer) without Diamond–Shurman 9.6.5**: `eigenformHT_of_kato` with
`EigenformRepExists` from the live rows (replaces `eigenformHT_of_kato_ds`). -/
theorem eigenformHT_of_kato_mht (hNew : EigenformHTNew) (h : HTNewAssembly.ModularHTCoeff)
    (hDS : DSThm966EV.DSThm966Printed) : ZInQ.Contrib.G9.PkgI4.EigenformHT :=
  eigenformHT_of_kato hNew HDec.HSyn.HodgeLF7.newformOfEigenformG9
    (eigenformRepExistsG9_of_modularHT h hDS)

end DS965Reroute
