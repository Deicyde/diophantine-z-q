import ZInQKernel.Contrib.OneProof.CarayolDDT31Full
import ZInQKernel.Contrib.OneProof.AfTateLambda

/-!
# The packaged Carayol leaf is equivalent to Darmon–Diamond–Taylor's Theorem 3.1 form

`CarayolDDT.carayolThmAFrob_of_DDT31Full` (in `CarayolDDT31Full.lean`) derives the open row
`CarayolRefold.CarayolThmAFrob` from `CarayolDDT.CarayolDDT31Full`. This file proves the converse,
`carayolDDT31Full_of_thmAFrob`, so the two leaves (and `CarayolDDT.CarayolDDT31`) are equivalent:
replacing one by the other changes the interface, not the mathematical assumption.
-/

open PkgI4 LadicCond NumberField IsDedekindDomain
open scoped Topology

namespace CarayolDDT.ThmAFrobConverse

private theorem liesOver_of_prime_mem {K : Type} [Field K] [NumberField K]
    {ℓ : ℕ} [Fact ℓ.Prime] (lam : HeightOneSpectrum (𝓞 K))
    (hlam : (ℓ : 𝓞 K) ∈ lam.asIdeal) : lam.asIdeal.LiesOver (AfTateLam.vQ ℓ).asIdeal := by
  have hmem : (ℓ : 𝓞 ℚ) ∈ lam.asIdeal.comap (algebraMap (𝓞 ℚ) (𝓞 K)) := by
    rw [Ideal.mem_comap, map_natCast]
    exact hlam
  let w : HeightOneSpectrum (𝓞 ℚ) :=
    { asIdeal := lam.asIdeal.comap (algebraMap (𝓞 ℚ) (𝓞 K))
      isPrime := Ideal.comap_isPrime _ _
      ne_bot := by
        intro h
        rw [h, Ideal.mem_bot] at hmem
        exact (Nat.cast_ne_zero.2 (Fact.out : ℓ.Prime).ne_zero) hmem }
  have hw : Rat.HeightOneSpectrum.primesEquiv w = AfTateLam.primeL ℓ := by
    have hdvd : Rat.HeightOneSpectrum.natGenerator w ∣ ℓ := by
      rw [Rat.HeightOneSpectrum.natGenerator_dvd_iff]
      have := Ideal.mem_map_of_mem (Rat.IsIntegralClosure.intEquiv (𝓞 ℚ)) hmem
      rwa [map_natCast] at this
    apply Subtype.ext
    exact (Nat.prime_dvd_prime_iff_eq (Rat.HeightOneSpectrum.prime_natGenerator w)
      (Fact.out : ℓ.Prime)).1 hdvd
  have hv : AfTateLam.vQ ℓ = w := (Equiv.symm_apply_eq _).2 hw.symm
  exact ⟨by rw [hv]⟩

private theorem exists_continuous_intHom {K : Type} [Field K] [NumberField K]
    {ℓ : ℕ} [Fact ℓ.Prime] (lam : HeightOneSpectrum (𝓞 K))
    (hlam : (ℓ : 𝓞 K) ∈ lam.asIdeal) :
    ∃ ι : ℤ_[ℓ] →+* lam.adicCompletion K, Continuous ι := by
  have : lam.asIdeal.LiesOver (AfTateLam.vQ ℓ).asIdeal := liesOver_of_prime_mem lam hlam
  exact ⟨(AfTateLam.algQl ℓ lam).comp PadicInt.Coe.ringHom,
    (AfTateLam.continuous_algQl lam).comp continuous_subtype_val⟩

private theorem absolute_of_irreducible_odd
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    {G : Type*} [Group G] (ρ : G →* GL (Fin 2) K)
    (h2 : (2 : K) ≠ 0)
    (hirr : ∀ W : Submodule K (Fin 2 → K),
      (∀ σ : G, ∀ v ∈ W, (ρ σ : Matrix (Fin 2) (Fin 2) K).mulVec v ∈ W) →
      W = ⊥ ∨ W = ⊤)
    (c : G) (hcc : c * c = 1)
    (hdet : (ρ c : Matrix (Fin 2) (Fin 2) K).det = -1) :
    ∀ W : Submodule L (Fin 2 → L),
      (∀ σ : G, ∀ v ∈ W,
        ((ρ σ : Matrix (Fin 2) (Fin 2) K).map (algebraMap K L)).mulVec v ∈ W) →
      W = ⊥ ∨ W = ⊤ := by
  have hCC : (ρ c : Matrix (Fin 2) (Fin 2) K) *
      (ρ c : Matrix (Fin 2) (Fin 2) K) = 1 := by
    rw [← Units.val_mul, ← map_mul, hcc, map_one, Units.val_one]
  have hspan := CarayolPrinted.adjoin_eq_top_of_irreducible_odd
    (fun σ : G => (ρ σ : Matrix (Fin 2) (Fin 2) K)) h2 hirr
    (ρ c : Matrix (Fin 2) (Fin 2) K) (Algebra.subset_adjoin ⟨c, rfl⟩) hCC hdet
  have hmap := CarayolPrinted.adjoin_map_eq_top (φ := algebraMap K L)
    (fun σ : G => (ρ σ : Matrix (Fin 2) (Fin 2) K)) hspan
  exact CarayolPrinted.eq_bot_or_top_of_adjoin _ hmap

private theorem guarded_global_det_of_frob
    {N : ℕ} [NeZero N] (ψ : (ZMod N)ˣ →* ℂˣ)
    (K : IntermediateField ℚ ℂ) {E : Type*} [NormedField E] [Algebra K E]
    {ℓ : ℕ} [Fact ℓ.Prime] (ρ : GQ →* GL (Fin 2) E) (hρ : Continuous ρ)
    (ι : ℤ_[ℓ] →+* E) (hι : Continuous ι)
    (hfrob : ∀ p : ℕ, p.Prime → ¬ p ∣ N * ℓ →
      ∀ (v : ValuationSubring Qbar) (τ : GQ), LiesOver v p → IsArithFrob τ v p →
      ∀ (u : (ZMod N)ˣ) (b : K),
        (u : ZMod N) = (p : ZMod N) → (b : ℂ) = (p : ℂ) * ((ψ u : ℂˣ) : ℂ) →
        (ρ τ : Matrix (Fin 2) (Fin 2) E).det = algebraMap K E b) :
    ∀ σ : GQ, ∀ h : ((ψ (CarayolDDT.cycN N σ) : ℂˣ) : ℂ) ∈ K,
      (ρ σ : Matrix (Fin 2) (Fin 2) E).det =
        algebraMap K E ⟨_, h⟩ * ι (CarayolDDT.cycL ℓ σ : ℤ_[ℓ]) := by
  have hcyc : Continuous (CarayolDDT.cycL ℓ) := by
    simpa [CarayolDDT.cycL] using cyclotomicCharacter.continuous ℓ ℚ Qbar
  intro σ h
  let α : K := ⟨((ψ (CarayolDDT.cycN N σ) : ℂˣ) : ℂ), h⟩
  let d : GQ → E := fun τ => (ρ τ : Matrix (Fin 2) (Fin 2) E).det
  let t : GQ → E := fun τ => algebraMap K E α * ι (CarayolDDT.cycL ℓ τ : ℤ_[ℓ])
  have hd : Continuous d := (Units.continuous_val.comp hρ).matrix_det
  have ht : Continuous t :=
    continuous_const.mul (hι.comp (Units.continuous_val.comp hcyc))
  change d σ = t σ
  by_contra hne
  have hopen : IsOpen {x : GQ | d x ≠ t x} := isOpen_ne_fun hd ht
  have hmem : (fun y : GQ => σ * y) ⁻¹' {x | d x ≠ t x} ∈ 𝓝 (1 : GQ) := by
    apply (hopen.preimage (continuous_const.mul continuous_id)).mem_nhds
    simpa using hne
  obtain ⟨L, hL, hsub⟩ := (krullTopology_mem_nhds_one_iff ℚ Qbar _).mp hmem
  let U : Subgroup GQ := L.fixingSubgroup ⊓ (CarayolDDT.cycN N).ker
  have hU : IsOpen (U : Set GQ) :=
    (IntermediateField.fixingSubgroup_isOpen L).inter (CarayolRefold.isOpen_ker_cycN N)
  obtain ⟨p, hp, hpS, v, τ, hv, hτ, hU'⟩ :=
    CarayolLevel.frobeniusDense_C9 U hU σ (N * ℓ).primeFactors
  have hfix : σ⁻¹ * τ ∈ L.fixingSubgroup := by
    have := L.fixingSubgroup.inv_mem hU'.1
    simpa using this
  have hneq := hsub hfix
  simp only [Set.mem_preimage, mul_inv_cancel_left, Set.mem_ofPred_eq] at hneq
  have hτN : CarayolDDT.cycN N τ = CarayolDDT.cycN N σ := by
    have hk := hU'.2
    change CarayolDDT.cycN N (τ⁻¹ * σ) = 1 at hk
    rw [map_mul, map_inv, inv_mul_eq_one] at hk
    exact hk
  have hNl : N * ℓ ≠ 0 := mul_ne_zero (NeZero.ne N) (Fact.out : ℓ.Prime).ne_zero
  have hpNl : ¬ p ∣ N * ℓ := fun h => hpS (Nat.mem_primeFactors.2 ⟨hp, h, hNl⟩)
  have hpN : ¬ p ∣ N := fun h => hpNl (dvd_mul_of_dvd_left h _)
  have hpl : p ≠ ℓ := fun h => hpNl (h ▸ dvd_mul_left p N)
  let u : (ZMod N)ˣ := CarayolDDT.cycN N τ
  let b : K := (p : K) * α
  have hu : (u : ZMod N) = (p : ZMod N) :=
    CarayolRefold.cycN_arithFrob hp hpN hv hτ
  have hb : (b : ℂ) = (p : ℂ) * ((ψ u : ℂˣ) : ℂ) := by
    simp [b, α, u, hτN]
  have heq : d τ = t τ := by
    change (ρ τ : Matrix (Fin 2) (Fin 2) E).det =
      algebraMap K E α * ι (CarayolDDT.cycL ℓ τ : ℤ_[ℓ])
    rw [hfrob p hp hpNl v τ hv hτ u b hu hb, CarayolRefold.cycL_arithFrob hp hpl hv hτ]
    simp only [b, map_mul, map_natCast]
    ring
  exact hneq heq

/-- **The packaged Frobenius leaf implies the DDT form.** `CarayolRefold.CarayolThmAFrob` gives
`CarayolDDT31Full` on the same representation: absolute irreducibility from irreducibility and oddness
(the full matrix algebra survives field extension), the continuous map `ℤ_ℓ → K_{F,λ}` from the
completion at the place over `ℓ`, and the global determinant identity from the Frobenius determinants
by density of Frobenius elements in each cyclotomic fibre and continuity. -/
theorem carayolDDT31Full_of_thmAFrob (h : CarayolRefold.CarayolThmAFrob) : CarayolDDT.CarayolDDT31Full := by
  intro N _ F ψ hF _ ℓ _ lam hlam
  obtain ⟨f, rfl, rfl, hnew, h1⟩ := hF
  let nf : HeckeRing.GL2.Newform N 2 :=
    ⟨⟨f.toCuspForm, f.χ, f.mem_charSpace, fun n _ => f.eigenvalue n,
      fun n _ => f.isEigen n, f.ne_zero⟩, hnew, h1⟩
  obtain ⟨ρ, hc, hirr, hatt, hcond⟩ := h N nf ℓ lam hlam
  have hodd : ∃ c : GQ, c * c = 1 ∧
      (ρ c : Matrix (Fin 2) (Fin 2) (lam.adicCompletion
        (DSCoeffExt.coeffField (nf.toCuspForm : CF N 2)))).det = -1 := by
    refine CarayolRefold.odd_of_frobDet (N := N)
      (CarayolHerbrand.norm_natCast_lt_one lam hlam) (CarayolRefold.two_ne_zero_adic lam)
      ρ hc ?_
    intro p hp hpNl v σ hv hσ hσN
    have hpN : ¬ p ∣ N := fun h => hpNl (dvd_mul_of_dvd_left h _)
    have hu : ((-1 : (ZMod N)ˣ) : ZMod N) = (p : ZMod N) := by
      rw [← CarayolRefold.cycN_arithFrob hp hpN hv hσ, hσN, Units.val_neg, Units.val_one]
    have hb : (((p : DSCoeffExt.coeffField (nf.toCuspForm : CF N 2))) : ℂ) =
        (p : ℂ) * ((nf.χ (-1) : ℂˣ) : ℂ) := by
      rw [CarayolDDT.chi_neg_one_eq_one nf, mul_one]
      rfl
    rw [((hatt p hp hpNl).2 v σ hv hσ).2 (-1) _ hu hb, map_natCast]
  obtain ⟨c, hcc, hdet⟩ := hodd
  obtain ⟨ι, hι⟩ := exists_continuous_intHom lam hlam
  refine ⟨ρ, hc, absolute_of_irreducible_odd ρ (CarayolRefold.two_ne_zero_adic lam)
    hirr c hcc hdet, ⟨ι, hι, ?_⟩, ?_, hcond⟩
  · exact guarded_global_det_of_frob nf.χ
      (DSCoeffExt.coeffField (nf.toCuspForm : CF N 2)) ρ hc ι hι
      (fun p hp hpNl v σ hv hσ => ((hatt p hp hpNl).2 v σ hv hσ).2)
  · intro p hp hpNl
    exact ⟨(hatt p hp hpNl).1, fun v σ hv hσ => ((hatt p hp hpNl).2 v σ hv hσ).1⟩

/-- **The two leaves are equivalent**: the packaged Frobenius form `CarayolThmAFrob` and the DDT form
`CarayolDDT31Full` (hence also `CarayolDDT31`). -/
theorem carayolDDT31Full_iff_thmAFrob : CarayolDDT.CarayolDDT31Full ↔ CarayolRefold.CarayolThmAFrob :=
  ⟨CarayolDDT.carayolThmAFrob_of_DDT31Full, carayolDDT31Full_of_thmAFrob⟩

end CarayolDDT.ThmAFrobConverse
