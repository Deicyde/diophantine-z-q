import ZInQKernel.OneProof.H.TailT

/-! # modular-split, row eigenformHTNew: `ZInQ.Contrib.HodgeSplit.EigenformHTNew` reduced to Kato's theorem at
one realization

The row (bundle field `eigenformHTNew`, `ZInQKernel/OneProof/H/TailS.lean` §10) is imported, not copied. It
quantifies over every semisimple `ρ` attached to the newform `f`. Kato's theorem is about one representation,
his `V_{F_λ}(f)` (a quotient of the étale cohomology of a modular curve with coefficients). The transport to
every semisimple attached `ρ` is proved here from `attachedConj_proof` (T18 + T19) and `htConj_proof`
(Hodge–Tate weights are conjugation invariant), both proved in the kernel (hodge-split). What is left is the
leaf `KatoRealization`. -/

set_option linter.unusedSectionVars false
set_option linter.style.longLine false

namespace ModularSplit.EigenHT

open ZInQ.Contrib.HodgeSplit ZInQ.Contrib.G9.PkgI4

/-- **LEAF candidate (consequence, see the report): Kato's theorem at his realization, dualized.**
For a newform `f ∈ S_k(Γ₁(N))`, `k ≥ 2`, with nebentypus `χ`, a prime `ℓ` and embeddings `ιC`, `ιL`,
**there is** a semisimple continuous `ρ : G_ℚ → GL₂(ℚ̄_ℓ)` attached to `f` (arithmetic Frobenius at
`p ∤ Nℓ` has trace `ιL ιC⁻¹ a_p(f)`) with Hodge–Tate weights `{0, 1 − k}` at `ℓ` (convention: the
cyclotomic character has weight `−1`).

Source: Kato, *p-adic Hodge theory and values of zeta functions of modular forms*, Astérisque 295 (2004),
§§9.2–9.4 and (9.2.2) (UNVERIFIED locators, hodge-split): `V_{F_λ}(f)` is de Rham at `ℓ` with Hodge–Tate
weights `0` and `k − 1` (cohomological normalization). The witness is the dual `V_{F_λ}(f)^∨` with
coefficients extended along `ιL ιC⁻¹` (dualizing turns geometric into arithmetic Frobenius and negates the
weights), irreducible by Ribet 1977 / 1985 (UNVERIFIED locators), hence semisimple. Not stronger than the
published statements: it asserts the conclusion for one realization only. -/
def KatoRealization : Prop :=
  ∀ (ℓ : ℕ) [Fact ℓ.Prime] (ιC : Qbar →ₐ[ℚ] ℂ) (ιL : Qbar →ₐ[ℚ] PadicAlgCl ℓ)
    (N : ℕ) (k : ℤ) (χ : DirichletCharacter ℂ N) (f : CF N k),
    0 < N → 2 ≤ k → IsNewform f χ →
    ∃ ρ : GaloisRep ℓ 2, ρ.IsSemisimple ∧ ρ.AttachedTo ιC ιL f ∧ ρ.HasHTWeightsAtSelf ℓ {0, 1 - k}

/-- **Row eigenformHTNew from `KatoRealization`.** -/
theorem eigenformHTNew_of_realization (hK : KatoRealization) : EigenformHTNew := by
  intro ℓ _ ιC ιL N k χ f ρ hN hk hf hss hatt
  obtain ⟨ρ0, hss0, hatt0, hHT0⟩ := hK ℓ ιC ιL N k χ f hN hk hf
  have hconj : IsConj ρ0 ρ := by
    refine attachedConj_proof ℓ ρ0 ρ (N * ℓ).primeFactors hss0 hss fun p hp hpS => ?_
    have hpN : ¬ p ∣ N * ℓ := by
      intro h
      exact hpS (Nat.mem_primeFactors.mpr ⟨hp, h, Nat.mul_ne_zero (by omega)
        (Fact.out : ℓ.Prime).ne_zero⟩)
    obtain ⟨hu0, α0, hα0, htr0⟩ := hatt0 p hp hpN
    obtain ⟨hu, α, hα, htr⟩ := hatt p hp hpN
    have heq : α0 = α := by
      apply ιC.toRingHom.injective
      change ιC α0 = ιC α
      rw [hα0, hα]
    refine ⟨hu0, hu, fun v σ hv hσ => ?_⟩
    rw [htr0 v σ hv hσ, htr v σ hv hσ, heq]
  exact htConj_proof ℓ 2 ρ0 ρ _ hconj hHT0

end ModularSplit.EigenHT

#print axioms ModularSplit.EigenHT.eigenformHTNew_of_realization
