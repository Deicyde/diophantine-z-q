import ZInQKernel.Contrib.OneProof.RC.KummerMaps.ActualComplements
import ZInQKernel.Contrib.OneProof.RC.KummerMaps.NonVacuity
import ZInQKernel.Contrib.OneProof.RC.FibreDuality.Duality

/-!
# Lane RC29 (round 3): the consumers' shape and non-vacuity of the actual local complements

Manuscript `diophantine_zq.tex`, Lemma `ex:arith-conjugate-duality` (tex 2761–2830) and Lemma
`ex:arith-local-kummer` (tex 3413–3468).

* `actualLocalComplements_iff_fibre`: **the per-pair hypothesis of lane RC31's consumers is lane
  RC26's for discrete coefficients** — for a field `k` and discrete modules, RC31's
  `FibreOrthogonalComplementsT β hβ (continuous_pairing β) ΔA ΔB I tr htr` (the hypothesis `horth`
  of `fibreSelmerDualityT`, `fibreSelmerDuality_conj`) and RC26's
  `OrthogonalComplementsT K β hβ ΔA ΔB I tr htr` (the hypothesis `horth` of `genuineSelmerDualityT`)
  are the same proposition (definitional). The actual data of this lane have the finite
  coefficient ring `A_i` (not a field), so they feed RC26's consumer (`actualSelmerDuality`); RC31's
  consumers take field coefficients `k(𝔭)`.
* **Non-vacuity** (`actL_nonvacuous`): for every number field `K`, with `S₀ = S = P` the places
  above `6` (= `2N` for `E_1 : y² = x(x − 1)(x + 3)`, of discriminant `2⁸ 3²`), `E_1`, `h = 1`,
  `s = 1`, the trivial moving character and `i = 1`, every hypothesis of `actualLocalComplements`
  other than the PRINTs, `IsTotallyComplex K` and the traces holds, and the actual conditions are
  the Kummer conditions at every place; for `K = ℚ` (`actL_nonvacuous_rat`) this is round 1's
  instantiation (`S` = the primes above `6`). The global theorems need `K` totally complex (Nekovář's
  condition (P) for `p = 2`, tex 2748–2753), which `ℚ` is not; the generic-`K` statement covers the
  totally complex fields of the text.

Kinds: PROVED.
-/

noncomputable section

namespace ZInQ.Manuscript.RC.KummerMaps

open ZInQ.Manuscript.RC.SelmerComplex ZInQ.Manuscript.RC.CoefModules
open ZInQ.Contrib.CloudB3RC53.PairedFunctional ZInQ.Contrib.CloudB3RC53.SelmerDuality
  ZInQ.Contrib.CloudB3RC53.SwitchInputs
open NumberField IsDedekindDomain
open ZInQ.Manuscript.RC.HeegnerAlgebra (Acoef)

/-! ### The consumers' shape -/

section Shape

variable {K : Type} [Field K] [NumberField K] {S : Set (HeightOneSpectrum (𝓞 K))}
  {k : Type} [Field k] {M M' T : Type}
  [AddCommGroup M] [Module k M] [DistribMulAction (GKS K S) M] [SMulCommClass (GKS K S) k M]
  [TopologicalSpace M] [DiscreteTopology M] [ContinuousSMul (GKS K S) M]
  [AddCommGroup M'] [Module k M'] [DistribMulAction (GKS K S) M'] [SMulCommClass (GKS K S) k M']
  [TopologicalSpace M'] [DiscreteTopology M'] [ContinuousSMul (GKS K S) M']
  [AddCommGroup T] [Module k T] [DistribMulAction (GKS K S) T] [SMulCommClass (GKS K S) k T]
  [TopologicalSpace T] [DiscreteTopology T] [ContinuousSMul (GKS K S) T]
  (β : M →ₗ[k] M' →ₗ[k] T) (hβ : ∀ (g : GKS K S) (a : M) (b : M'), β (g • a) (g • b) = g • β a b)

/-- PROVED (definitional). **Lane RC31's per-pair hypothesis is lane RC26's** for discrete
coefficient modules over a field: `FibreOrthogonalComplementsT` (with the joint continuity
`continuous_pairing β`) and `OrthogonalComplementsT` are the same proposition. -/
theorem actualLocalComplements_iff_fibre (ΔA : GaloisLocalConditions K S k M)
    (ΔB : GaloisLocalConditions K S k M') (I : GaloisTruncIsotropyData K S k β hβ ΔA ΔB)
    (tr : (galoisCompactTT K S k β hβ ΔA ΔB I).X 3 →ₗ[k] k)
    (htr : ∀ z, tr ((galoisCompactTT K S k β hβ ΔA ΔB I).d 2 3 rfl z) = 0) :
    ZInQ.Manuscript.RC.FibreDuality.FibreOrthogonalComplementsT β hβ (continuous_pairing β) ΔA ΔB I
        tr htr ↔
      OrthogonalComplementsT K β hβ ΔA ΔB I tr htr :=
  Iff.rfl

end Shape

/-! ### Non-vacuity -/

section NonVacuity

variable (K : Type) [Field K] [NumberField K]

/-- Definition (non-vacuity). **The places above `6`**, `{v | v ∣ 6}` (for `E_1` these are the
places above `2N`). -/
def actLS6 : Set (HeightOneSpectrum (𝓞 K)) :=
  {v | v.asIdeal ∣ Ideal.span {(6 : 𝓞 K)}}

/-- PROVED. There are finitely many places above `6`. -/
theorem actLS6_finite : (actLS6 K).Finite := by
  refine Ideal.finite_factors ?_
  rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
  exact_mod_cast (show ((6 : ℕ) : 𝓞 K) ≠ 0 from Nat.cast_ne_zero.2 (by norm_num))

/-- PROVED. The places above `2` lie above `6`. -/
theorem actLS6_two (v : HeightOneSpectrum (𝓞 K)) (h2 : (2 : 𝓞 K) ∈ v.asIdeal) :
    v ∈ actLS6 K := by
  change v.asIdeal ∣ Ideal.span {(6 : 𝓞 K)}
  rw [Ideal.dvd_iff_le, Ideal.span_singleton_le_iff_mem]
  have h6 : (6 : 𝓞 K) = 2 * 3 := by norm_num
  rw [h6]
  exact Ideal.mul_mem_right _ _ h2

variable (S : Set (HeightOneSpectrum (𝓞 K)))

omit [NumberField K] in
/-- PROVED (non-vacuity). `1 ∈ K_S` is a square root of `h = 1`. -/
theorem actL_one_sq : (1 : KS K S) ^ 2 = algebraMap K (KS K S) 1 := by
  rw [one_pow, map_one]

/-- Definition (non-vacuity). The character `α = χ_1 · (1 + t)^0` of `M_1` for `h = 1` and the
trivial moving character, over any number field. -/
abbrev actLAlphaOne (i : ℕ) : GKS K S →* (Acoef i)ˣ :=
  alphaChar i (quadChar (1 : KS K S) (actL_one_sq K S) one_ne_zero)
    (1 : GKS K S →* Multiplicative (ZMod (2 ^ (2 * i))))

/-- PROVED (non-vacuity). `actLAlphaOne` has open kernel. -/
instance actLAlphaOne_isOpenKer (i : ℕ) : IsOpenKer (actLAlphaOne K S i) := by
  refine alphaChar_isOpenKer i _ _ ?_
  have : ((1 : GKS K S →* Multiplicative (ZMod (2 ^ (2 * i)))).ker : Set (GKS K S)) =
      Set.univ := by
    ext g
    simp
  rw [this]
  exact isOpen_univ

/-- PROVED (non-vacuity of the ELLIOT hypothesis `hα`). For the trivial moving character the
character of `M_i` is `χ_h` on every decomposition group. -/
theorem actLAlphaOne_quad (i : ℕ) (v : HeightOneSpectrum (𝓞 K)) :
    IsLocallyQuadAt i (actLAlphaOne K S i) (quadChar (1 : KS K S) (actL_one_sq K S) one_ne_zero) v :=
  isLocallyQuadAt_alphaChar i _ 1 v fun _ => rfl

open scoped Classical in
/-- PROVED (non-vacuity of `actualLocalComplements`, tex 3413–3468). For every number field `K`,
with `S₀ = S = P` the places above `6`, `E_1 : y² = x(x − 1)(x + 3)`, `h = 1`, `s = 1`, the trivial
moving character and `i = 1`: `S` is finite and contains the places above `2`, `E_1` has full
`2`-torsion over `K_S`, `K_S` contains the square roots of unity, the character of `M_1` is `χ_1` on
every decomposition group (`hα`), and the actual conditions are the Kummer conditions at every place
(on `M_1(α)` and on `M_1(α⁻¹)`). With these, `actualLocalComplements` and the global theorems apply
as soon as `K` is totally complex (and the PRINTs and traces are given). -/
theorem actL_nonvacuous :
    letI := acoefTop 1
    haveI := acoefTop_discrete 1
    haveI := isElliptic_curveEll (K := K) (one_ne_zero : (1 : K) ≠ 0)
    (actLS6 K).Finite ∧ (∀ v : HeightOneSpectrum (𝓞 K), (2 : 𝓞 K) ∈ v.asIdeal → v ∈ actLS6 K) ∧
      FullTorsion K (actLS6 K) (curveEll (1 : K)) (2 ^ 1) ∧ HasRootsOfUnity K (actLS6 K) (2 ^ 1) ∧
      (∀ v ∈ actLS6 K, IsLocallyQuadAt (S := actLS6 K) 1 (actLAlphaOne K (actLS6 K) 1)
        (quadChar (1 : KS K (actLS6 K)) (actL_one_sq K (actLS6 K)) one_ne_zero) v) ∧
      ∀ (v : Places K (actLS6 K)),
        actLCondA (subset_refl _) (curveEll (1 : K)) 1 (1 : KS K (actLS6 K))
            (actL_one_sq K (actLS6 K)) one_ne_zero
            (by rw [pow_one]; exact fullTorsion_two_curveEll one_ne_zero) (actLS6 K)
            (actLAlphaOne K (actLS6 K) 1) (fun v _ => actLAlphaOne_quad K (actLS6 K) 1 v) v =
          actualKummerAtS (subset_refl _) (curveEll (1 : K)) 1 (1 : KS K (actLS6 K))
            (actL_one_sq K (actLS6 K)) one_ne_zero (actLAlphaOne K (actLS6 K) 1)
            (by rw [pow_one]; exact fullTorsion_two_curveEll one_ne_zero) v
            (actLAlphaOne_quad K (actLS6 K) 1 v.1) ∧
        actLCondB (subset_refl _) (curveEll (1 : K)) 1 (1 : KS K (actLS6 K))
            (actL_one_sq K (actLS6 K)) one_ne_zero
            (by rw [pow_one]; exact fullTorsion_two_curveEll one_ne_zero) (actLS6 K)
            (actLAlphaOne K (actLS6 K) 1) (fun v _ => actLAlphaOne_quad K (actLS6 K) 1 v) v =
          actualKummerAtS (subset_refl _) (curveEll (1 : K)) 1 (1 : KS K (actLS6 K))
            (actL_one_sq K (actLS6 K)) one_ne_zero (charInv (actLAlphaOne K (actLS6 K) 1))
            (by rw [pow_one]; exact fullTorsion_two_curveEll one_ne_zero) v
            (isLocallyQuadAt_charInv (actLAlphaOne_quad K (actLS6 K) 1 v.1)) := by
  letI := acoefTop 1
  have := acoefTop_discrete 1
  have := isElliptic_curveEll (K := K) (one_ne_zero : (1 : K) ≠ 0)
  refine ⟨actLS6_finite K, actLS6_two K, ?_, cycloInfl_hasRootsOfUnity_two (actLS6 K),
    fun v _ => actLAlphaOne_quad K (actLS6 K) 1 v, fun v => ⟨?_, ?_⟩⟩
  · rw [pow_one]
    exact fullTorsion_two_curveEll one_ne_zero
  · exact actLCondA_of_P (subset_refl _) _ 1 _ _ _ _ (actLS6 K) _ _ v.2 v.2
  · exact actLCondB_of_P (subset_refl _) _ 1 _ _ _ _ (actLS6 K) _ _ v.2 v.2

/-- PROVED (non-vacuity over `ℚ`, as in round 1): the instance `K = ℚ`, `S` = the primes above
`6`, of `actL_nonvacuous`. -/
theorem actL_nonvacuous_rat : (actLS6 ℚ).Finite ∧
    (∀ v : HeightOneSpectrum (𝓞 ℚ), (2 : 𝓞 ℚ) ∈ v.asIdeal → v ∈ actLS6 ℚ) ∧
    FullTorsion ℚ (actLS6 ℚ) (curveEll (1 : ℚ)) (2 ^ 1) ∧ HasRootsOfUnity ℚ (actLS6 ℚ) (2 ^ 1) :=
  ⟨(actL_nonvacuous ℚ).1, (actL_nonvacuous ℚ).2.1, (actL_nonvacuous ℚ).2.2.1,
    (actL_nonvacuous ℚ).2.2.2.1⟩

end NonVacuity

end ZInQ.Manuscript.RC.KummerMaps
