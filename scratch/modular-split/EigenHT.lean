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


/-! ## The dualization, split off

`KatoRealization` asserts the conclusion in the Tate normalization (arithmetic Frobenius, weights `{0, 1 − k}`).
Kato's printed theorem is about the cohomological realization (geometric Frobenius, weights `{0, k − 1}` in this
convention). The passage is the contragredient `ρ^∨(σ) = ρ(σ⁻¹)ᵀ`: its attachment and semisimplicity are proved
below; the negation of Hodge–Tate weights is the named GLUE `HTDual`. -/

section Dual

variable {ℓ : ℕ} [Fact ℓ.Prime] {n : ℕ}

theorem mat_mul_inv (ρ : GaloisRep ℓ n) (σ : GQ) :
    ρ.mat σ * ρ.mat σ⁻¹ = 1 := by
  rw [GaloisRep.mat, GaloisRep.mat, ← Units.val_mul, ← map_mul, mul_inv_cancel, map_one, Units.val_one]

theorem mat_inv_mul (ρ : GaloisRep ℓ n) (σ : GQ) :
    ρ.mat σ⁻¹ * ρ.mat σ = 1 := by
  rw [GaloisRep.mat, GaloisRep.mat, ← Units.val_mul, ← map_mul, inv_mul_cancel, map_one, Units.val_one]

/-- The contragredient `ρ^∨(σ) = ρ(σ⁻¹)ᵀ` as a homomorphism. -/
noncomputable def dualHom (ρ : GaloisRep ℓ n) : GQ →* GL (Fin n) (PadicAlgCl ℓ) where
  toFun σ := ⟨(ρ.mat σ⁻¹).transpose, (ρ.mat σ).transpose,
    by rw [← Matrix.transpose_mul, mat_mul_inv, Matrix.transpose_one],
    by rw [← Matrix.transpose_mul, mat_inv_mul, Matrix.transpose_one]⟩
  map_one' := Units.ext (by simp [GaloisRep.mat])
  map_mul' σ τ := Units.ext (by
    simp only [GaloisRep.mat, mul_inv_rev, map_mul, Units.val_mul, Matrix.transpose_mul])

/-- **The contragredient** `ρ^∨(σ) = ρ(σ⁻¹)ᵀ` of a continuous representation. -/
noncomputable def dualGR (ρ : GaloisRep ℓ n) : GaloisRep ℓ n where
  toHom := dualHom ρ
  continuous_toHom := by
    rw [Units.continuous_iff]
    constructor
    · change Continuous fun σ : GQ => (ρ.mat σ⁻¹).transpose
      exact ((Units.continuous_val.comp ρ.continuous_toHom).comp continuous_inv).matrix_transpose
    · change Continuous fun σ : GQ => (ρ.mat σ).transpose
      exact (Units.continuous_val.comp ρ.continuous_toHom).matrix_transpose

theorem dualGR_mat (ρ : GaloisRep ℓ n) (σ : GQ) : (dualGR ρ).mat σ = (ρ.mat σ⁻¹).transpose := rfl

/-- The contragredient of an irreducible (Burnside form) representation is irreducible. -/
theorem dualGR_isIrreducible (ρ : GaloisRep ℓ n) (h : ρ.IsIrreducible) : (dualGR ρ).IsIrreducible := by
  let A := Algebra.adjoin (PadicAlgCl ℓ) (Set.range (dualGR ρ).mat)
  let S : Subalgebra (PadicAlgCl ℓ) (Matrix (Fin n) (Fin n) (PadicAlgCl ℓ)) :=
    { carrier := {M | M.transpose ∈ A}
      mul_mem' := by
        intro a b ha hb
        change (a * b).transpose ∈ A
        rw [Matrix.transpose_mul]; exact A.mul_mem hb ha
      add_mem' := by
        intro a b ha hb
        change (a + b).transpose ∈ A
        rw [Matrix.transpose_add]; exact A.add_mem ha hb
      algebraMap_mem' := by
        intro c
        change (algebraMap (PadicAlgCl ℓ) (Matrix (Fin n) (Fin n) (PadicAlgCl ℓ)) c).transpose ∈ A
        rw [Algebra.algebraMap_eq_smul_one, Matrix.transpose_smul, Matrix.transpose_one,
          ← Algebra.algebraMap_eq_smul_one]
        exact A.algebraMap_mem c }
  have hle : Algebra.adjoin (PadicAlgCl ℓ) (Set.range ρ.mat) ≤ S := by
    rw [Algebra.adjoin_le_iff]
    rintro _ ⟨σ, rfl⟩
    change (ρ.mat σ).transpose ∈ A
    have : (ρ.mat σ).transpose = (dualGR ρ).mat σ⁻¹ := by rw [dualGR_mat, inv_inv]
    rw [this]
    exact Algebra.subset_adjoin ⟨σ⁻¹, rfl⟩
  rw [h] at hle
  refine eq_top_iff.mpr fun M _ => ?_
  have : M.transpose ∈ S := hle Algebra.mem_top
  change M.transpose.transpose ∈ A at this
  rwa [Matrix.transpose_transpose] at this

end Dual

/-- **GLUE (named, unproved): Hodge–Tate weights of the contragredient.** If `ρ|_{G_{ℚ_ℓ}}` is Hodge–Tate with
weight multiset `S` (`card S = n`), then `ρ^∨|_{G_{ℚ_ℓ}}` is Hodge–Tate with weights `−S`. Needs: with `E`
containing the entries, `ℂ_ℓ ⊗ V ≅ ⊕ ℂ_ℓ(−w)` (`V` Hodge–Tate) gives `ℂ_ℓ ⊗ V^∨ ≅ ⊕ ℂ_ℓ(w)`, and Tate's
`H⁰(G, ℂ_ℓ(i)) = 0` for `i ≠ 0`, `= ℚ_ℓ`-dimension `1` for `i = 0` (the kernel's leaves `TateTwistInvariants`,
`AxSenTate`, used the same way by hodge-split's `htMultOver_of_decomp`). STANDARD (Fontaine–Ouyang, *Theory of
p-adic Galois representations*, §2.2–2.3; Brinon–Conrad, *CMI notes*, §2.4; UNVERIFIED numbers). -/
def HTDual : Prop :=
  ∀ (ℓ : ℕ) [Fact ℓ.Prime] (n : ℕ) (ρ : GaloisRep ℓ n) (S : Multiset ℤ), S.card = n →
    ρ.HasHTWeightsAtSelf ℓ S → (dualGR ρ).HasHTWeightsAtSelf ℓ (S.map Neg.neg)

/-- **LEAF candidate (consequence; closer to the printed form than `KatoRealization`): Kato's theorem at his
realization, in the cohomological normalization.** For a newform `f ∈ S_k(Γ₁(N))`, `k ≥ 2`, a prime `ℓ` and
embeddings `ιC`, `ιL`, **there is** an irreducible continuous `ρ : G_ℚ → GL₂(ℚ̄_ℓ)` such that for `p ∤ Nℓ`, `ρ` is
unramified at `p` and every **geometric** Frobenius `σ⁻¹` (`σ` arithmetic) has trace `ιL ιC⁻¹ a_p(f)`, and
`ρ|_{G_{ℚ_ℓ}}` is Hodge–Tate with weights `{0, k − 1}` (convention: the cyclotomic character has weight `−1`).

Sources: the witness is Kato's `V_{F_λ}(f)` (Astérisque 295 (2004), §§8.3, 9.2–9.4 and (9.2.2); UNVERIFIED locators)
with coefficients extended along `ιL ιC⁻¹`. Its geometric Frobenius traces are `a_p` (Eichler–Shimura–Deligne
normalization of `H¹_ét`). Kato's de Rham statement with Hodge–Tate weights `0, k − 1` is in the cohomological
normalization; its translation into this file's convention is UNVERIFIED (no source on this host). Irreducibility
is Ribet 1977 (`k = 2`) / Ribet 1985 (UNVERIFIED locators). The existential over `ρ` makes it a consequence, not
the printed statement, which is about the specific `V_{F_λ}(f)`. -/
def KatoRealizationCoh : Prop :=
  ∀ (ℓ : ℕ) [Fact ℓ.Prime] (ιC : Qbar →ₐ[ℚ] ℂ) (ιL : Qbar →ₐ[ℚ] PadicAlgCl ℓ)
    (N : ℕ) (k : ℤ) (χ : DirichletCharacter ℂ N) (f : CF N k),
    0 < N → 2 ≤ k → IsNewform f χ →
    ∃ ρ : GaloisRep ℓ 2, ρ.IsIrreducible ∧
      (∀ p : ℕ, p.Prime → ¬ p ∣ N * ℓ → ρ.UnramifiedAt p ∧ ∃ α : Qbar, ιC α = coeff f p ∧
        ∀ (v : ValuationSubring Qbar) (σ : GQ), LiesOver v p → IsArithFrob σ v p →
          (ρ.mat σ⁻¹).trace = ιL α) ∧
      ρ.HasHTWeightsAtSelf ℓ {0, k - 1}

/-- **`KatoRealization` from the cohomological form and the glue `HTDual`** (the contragredient is attached,
irreducible hence semisimple). -/
theorem katoRealization_of_coh (hK : KatoRealizationCoh) (hD : HTDual) : KatoRealization := by
  intro ℓ _ ιC ιL N k χ f hN hk hf
  obtain ⟨ρ, hirr, hatt, hHT⟩ := hK ℓ ιC ιL N k χ f hN hk hf
  refine ⟨dualGR ρ, ?_, ?_, ?_⟩
  · have h := dualGR_isIrreducible ρ hirr
    exact C9Rhof.isSemisimple_of_isIrreducible (ℓ := ℓ) ⟨(dualGR ρ).toHom, (dualGR ρ).continuous_toHom⟩ h
  · intro p hp hpN
    obtain ⟨hu, α, hα, htr⟩ := hatt p hp hpN
    refine ⟨fun v hv σ hσ => ?_, α, hα, fun v σ hv hσ => ?_⟩
    · have h1 := hu v hv σ⁻¹ ((v.inertiaSubgroup ℚ).inv_mem hσ)
      apply Units.ext
      change (ρ.mat ((σ : v.decompositionSubgroup ℚ) : GQ)⁻¹).transpose = 1
      have : ((σ⁻¹ : v.decompositionSubgroup ℚ) : GQ) = ((σ : v.decompositionSubgroup ℚ) : GQ)⁻¹ := rfl
      rw [GaloisRep.mat, ← this, h1, Units.val_one, Matrix.transpose_one]
    · rw [dualGR_mat, Matrix.trace_transpose, htr v σ hv hσ]
  · have h := hD ℓ 2 ρ {0, k - 1} (by simp) hHT
    have hS : (({0, k - 1} : Multiset ℤ).map Neg.neg) = {0, 1 - k} := by
      simp only [Multiset.insert_eq_cons, Multiset.map_cons, Multiset.map_singleton, neg_zero, neg_sub]
    rwa [hS] at h

/-- **Row eigenformHTNew from the cohomological form of Kato's theorem and the glue `HTDual`.** -/
theorem eigenformHTNew_of_coh (hK : KatoRealizationCoh) (hD : HTDual) : EigenformHTNew :=
  eigenformHTNew_of_realization (katoRealization_of_coh hK hD)

end ModularSplit.EigenHT

#print axioms ModularSplit.EigenHT.eigenformHTNew_of_realization
#print axioms ModularSplit.EigenHT.eigenformHTNew_of_coh
