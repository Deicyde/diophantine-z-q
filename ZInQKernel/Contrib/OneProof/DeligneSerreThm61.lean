import ZInQKernel.Contrib.OneProof.DSCoeffExt

/-! # Deligne–Serre's theorem in weights at least two

The trace and determinant statement of Théorème 6.1 implies the characteristic-polynomial
statement over the coefficient-field completion. The Hecke coefficient relation proves that
the coefficient field contains the required nebentypus values; no extra hypothesis is needed.
-/

noncomputable section

namespace DSCoeffExt

open UpperHalfPlane CongruenceSubgroup HeckeRing.GL2 NumberField IsDedekindDomain
open Polynomial (X C)
open ZInQ.Contrib.G9.PkgI4 (Qbar GQ CF coeff LiesOver IsArithFrob)

/-- Deligne–Serre, *Formes modulaires de poids 1*, Ann. Sci. ÉNS (4) 7 (1974),
Théorème 6.1, p. 520; Frobenius convention p. 513.

Clause-by-clause encoding of the printed theorem:
* `CF N k` restricts the printed modular forms to cusp forms on `Γ₁(N)`, hence to forms
  holomorphic at all cusps. The hypotheses are `f ≠ 0` and `2 ≤ k`.
* Type `(k, χ)` is membership in `cuspFormCharSpace k (MulChar.toUnitHom χ)`: the diamond
  operators act by `χ(d)`, equivalently `f|_k γ = χ(d) f` for `γ ∈ Γ₀(N)`.
* `a : ℕ → ℂ` records the `T_p` eigenvalues. Only primes `p ∤ N` are constrained, using
  `heckeTCuspNat`; there is no normalization and no hypothesis at primes dividing `N`.
* `K : IntermediateField ℚ ℂ` with `NumberField K` is the given finite extension of `ℚ`.
  `haK` and `hχK` require precisely the eigenvalues and character values at primes `p ∤ N`
  to belong to `K`.
* A finite place of residual characteristic `ℓ` is `lam : HeightOneSpectrum (𝓞 K)`
  containing the prime `ℓ`; its completed field is `lam.adicCompletion K`.
* The conclusion retains a continuous homomorphism to `GL₂(K_λ)`. Semisimplicity is
  omitted, so the conclusion is weaker than the printed one.
* Unramified outside `Nℓ` means triviality on every inertia group above each prime
  `p ∤ Nℓ`. For every such place and every `IsArithFrob`, trace is the image of `a p`
  and determinant is the image of `χ(p)` times `p^(k - 1)`. This is arithmetic, not
  geometric, Frobenius, as in the printed footnote. -/
def DeligneSerreThm61 : Prop :=
  ∀ (N : ℕ) [NeZero N] (k : ℤ) (χ : DirichletCharacter ℂ N) (f : CF N k)
    (a : ℕ → ℂ),
    2 ≤ k → f ≠ 0 → f ∈ cuspFormCharSpace k (MulChar.toUnitHom χ) →
    (∀ (p : ℕ) (hp : p.Prime), ¬ p ∣ N →
      heckeTCuspNat k p (_hn := ⟨hp.ne_zero⟩) f = a p • f) →
    ∀ (K : IntermediateField ℚ ℂ) [NumberField K]
      (haK : ∀ p : ℕ, p.Prime → ¬ p ∣ N → a p ∈ K)
      (hχK : ∀ p : ℕ, p.Prime → ¬ p ∣ N → χ (p : ZMod N) ∈ K)
      (ℓ : ℕ) [Fact ℓ.Prime] (lam : HeightOneSpectrum (𝓞 K)),
      (ℓ : 𝓞 K) ∈ lam.asIdeal →
      ∃ ρ : GQ →* GL (Fin 2) (lam.adicCompletion K), Continuous ρ ∧
        ∀ (p : ℕ) (hp : p.Prime) (hpNl : ¬ p ∣ N * ℓ),
          (∀ v : ValuationSubring Qbar, LiesOver v p →
            ∀ σ ∈ v.inertiaSubgroup ℚ, ρ ((σ : v.decompositionSubgroup ℚ) : GQ) = 1) ∧
          ∀ (v : ValuationSubring Qbar) (σ : GQ), LiesOver v p → IsArithFrob σ v p →
            (ρ σ : Matrix (Fin 2) (Fin 2) (lam.adicCompletion K)).trace =
              algebraMap K (lam.adicCompletion K)
                ⟨a p, haK p hp (fun hpN => hpNl (dvd_mul_of_dvd_left hpN ℓ))⟩ ∧
            (ρ σ : Matrix (Fin 2) (Fin 2) (lam.adicCompletion K)).det =
              algebraMap K (lam.adicCompletion K)
                ⟨χ (p : ZMod N), hχK p hp (fun hpN => hpNl (dvd_mul_of_dvd_left hpN ℓ))⟩ *
                (p : lam.adicCompletion K) ^ (k - 1)

/-- The Hecke relation `a_p² - a_{p²} = χ(p) p^(k - 1)` puts `χ(p)` in the
coefficient field: divide by the nonzero rational power `p^(k - 1)`. -/
theorem char_mem_coeffField_of_normalizedEigenformDS
    {N : ℕ} [NeZero N] {k : ℤ} {χ : DirichletCharacter ℂ N} {f : CF N k}
    (hf : IsNormalizedEigenformDS f χ) {p : ℕ} (hp : p.Prime) :
    χ (p : ZMod N) ∈ coeffField f := by
  have hrel := coeff_sq_relation (isNormalizedEigenform_of_DS hf) hp
  have hden : (p : ℂ) ^ (k - 1) ≠ 0 := zpow_ne_zero _ (Nat.cast_ne_zero.mpr hp.ne_zero)
  rw [show χ (p : ZMod N) =
    (coeff f p ^ 2 - coeff f (p * p)) / (p : ℂ) ^ (k - 1) from
      (eq_div_iff hden).mpr hrel.symm]
  exact div_mem (sub_mem (pow_mem (coeff_mem_coeffField f p) 2)
    (coeff_mem_coeffField f (p * p))) (zpow_mem (natCast_mem _ p) (k - 1))

/-- The characteristic polynomial of a two-dimensional matrix is `X² - tr(M) X + det(M)`. -/
theorem charpoly_fin_two_trace_det {K : Type*} [Field K] (M : Matrix (Fin 2) (Fin 2) K) :
    M.charpoly = X ^ 2 - C M.trace * X + C M.det := by
  simpa only [Matrix.trace_fin_two, Matrix.det_fin_two] using
    DS965Weak.charpoly_fin_two M

/-- Deligne–Serre's Théorème 6.1 implies the coefficient-field statement `DSThm965Printed`.
Normalization gives nonvanishing and identifies each prime eigenvalue with `coeff f p`.
The coefficient field contains the character values by the Hecke relation. The trace and
determinant identities give the left, characteristic-polynomial, disjunct. -/
theorem dsThm965Printed_of_deligneSerre61 (h : DeligneSerreThm61) : DSThm965Printed := by
  intro N _ k χ f hk hf _ ℓ _ lam hlam
  have hf' := isNormalizedEigenform_of_DS hf
  have hχK : ∀ p : ℕ, p.Prime → ¬ p ∣ N → χ (p : ZMod N) ∈ coeffField f :=
    fun _ hp _ => char_mem_coeffField_of_normalizedEigenformDS hf hp
  obtain ⟨ρ, hc, hρ⟩ := h N k χ f (coeff f) hk (ne_zero_of_coeff_one hf'.2.1)
    (T25.mem_cuspFormCharSpace_of_hasNebentypus hf'.1)
    (fun _ hp _ => heckeTCuspNat_eq_coeff_smul_all hf' hp)
    (coeffField f) (fun p _ _ => coeff_mem_coeffField f p) hχK ℓ lam hlam
  refine ⟨ρ, hc, fun p hp hpNl => ?_⟩
  obtain ⟨hun, hfr⟩ := hρ p hp hpNl
  refine ⟨hun, fun b hb v σ hv hσ => Or.inl ?_⟩
  obtain ⟨htr, hdet⟩ := hfr v σ hv hσ
  have hb' : (⟨χ (p : ZMod N),
      hχK p hp (fun hpN => hpNl (dvd_mul_of_dvd_left hpN ℓ))⟩ : coeffField f) *
      (p : coeffField f) ^ (k - 1) = b := by
    apply Subtype.ext
    change (coeffField f).val
      ((⟨χ (p : ZMod N),
        hχK p hp (fun hpN => hpNl (dvd_mul_of_dvd_left hpN ℓ))⟩ : coeffField f) *
        (p : coeffField f) ^ (k - 1)) = (b : ℂ)
    rw [map_mul, map_zpow₀, map_natCast (coeffField f).val p]
    exact hb.symm
  have hdet' : (ρ σ : Matrix (Fin 2) (Fin 2) (lam.adicCompletion (coeffField f))).det =
      algebraMap (coeffField f) (lam.adicCompletion (coeffField f)) b := by
    rw [← hb', map_mul, map_zpow₀,
      map_natCast (algebraMap (coeffField f) (lam.adicCompletion (coeffField f))) p]
    exact hdet
  rw [charpoly_fin_two_trace_det, htr, hdet']

end DSCoeffExt
