import ZInQKernel.Contrib.GZStatements.Weak
import ZInQKernel.Contrib.GZTheta.ALFinal

/-!
# gz-statements: the level `N` in the restricted leaves is `32 d²`

In `FHNonvanishingCd`, `GrossZagierHeegnerCd` and `GrossZagierRankCd` the newform `f` is any
newform of weight 2 and trivial nebentypus with `aₙ(f) = aₙ(C_d)` for `n ≥ 1`. Its level is
forced: `N = 32 d²` (`level_eq_of_coeff_cd`), by strong multiplicity one across levels
(`ZInQ.GZTheta.newformUniqueAcrossLevels`, task atkin-li) and the level-`32 d²` newform of
gz-theta / atkin-li. Hence the Heegner hypothesis `HeegnerHyp N D` of the restricted leaves is
`HeegnerHyp (32 d²) D`: `χ_D(2) = 1` (that is, `D ≡ 1 mod 8`) and `χ_D(p) = 1` for every `p ∣ d`.
-/

open UpperHalfPlane HeckeRing.GL2 WeierstrassCurve CongruenceSubgroup

namespace ZInQ.GZStatements

open ZInQ.GZDecomp ZInQ.Contrib.HeckeFE

/-- `aₙ(C_d)` is the Hecke coefficient `heckeCoeff d n` (Deuring's identity, proved). -/
theorem LFunction_cd_eq_heckeCoeff {d : ℕ} (hd4 : d % 4 = 1) (hsq : Squarefree d) {n : ℕ}
    (hn : n ≠ 0) : (((shortCurve (-(d : ℚ) ^ 2)).LFunction n : ℤ) : ℂ) = heckeCoeff d n := by
  have hD := deuringCd_of_gaussPointCount hd4 hsq ZInQ.Contrib.GaussFE.gaussPointCount n hn
  rw [← hD, ZInQ.Contrib.HeckeAll.LFunction_cd_apply' hsq hn]
  simp [ZInQ.Literature.cdCoeff, hn]

/-- The newform of `C_d` at level `32 d²` (gz-theta's `cmForm32` and atkin-li's `newCM`). -/
theorem exists_newform_level32 {d : ℕ} (hd4 : d % 4 = 1) (hsq : Squarefree d) :
    ∃ (_ : NeZero (32 * d ^ 2)) (g : Newform (32 * d ^ 2) 2), g.χ = 1 ∧
      ∀ n : ℕ, n ≠ 0 → coeff g n = heckeCoeff d n := by
  have : NeZero d := ⟨by omega⟩
  obtain ⟨F, hF⟩ := ZInQ.GZTheta.cmForm32
  obtain ⟨E, hE, hEχ⟩ := ZInQ.GZTheta.exists_eigenformAway_cmForm hF d hd4 hsq
  refine ⟨inferInstance, ⟨E, ?_, ?_⟩, hEχ, fun n _ => ?_⟩
  · rw [hE]
    exact ZInQ.GZTheta.newCM d hd4 hsq _ (ZInQ.GZTheta.qExpansion_cmForm_coeff hF d)
  · rw [hE, ZInQ.GZTheta.qExpansion_cmForm_coeff hF d 1, heckeCoeff_one]
  · show (qExpansion 1 E.toCuspForm).coeff n = _
    rw [hE, ZInQ.GZTheta.qExpansion_cmForm_coeff hF d n]

/-- **The level of a newform of `C_d` is `32 d²`.** If `f` is a newform of weight 2, level `N`
and trivial nebentypus with `aₙ(f) = aₙ(C_d)` for all `n ≥ 1` (`d ≡ 1 mod 4` squarefree), then
`N = 32 d²`. -/
theorem level_eq_of_coeff_cd {d : ℕ} (hd4 : d % 4 = 1) (hsq : Squarefree d) {N : ℕ} [NeZero N]
    (f : Newform N 2) (hχ : f.χ = 1)
    (hf : ∀ n : ℕ, n ≠ 0 → coeff f n = ((shortCurve (-(d : ℚ) ^ 2)).LFunction n : ℂ)) :
    N = 32 * d ^ 2 := by
  obtain ⟨hN32, g, hgχ, hg⟩ := exists_newform_level32 hd4 hsq
  have hL : NeZero (N * (32 * d ^ 2)) := ⟨mul_ne_zero (NeZero.ne N) (NeZero.ne _)⟩
  refine (ZInQ.GZTheta.newformUniqueAcrossLevels (N * (32 * d ^ 2)) 2 N (32 * d ^ 2) 1 f g
    (dvd_mul_right _ _) (dvd_mul_left _ _) (by rw [hχ]; rfl) (by rw [hgχ]; rfl)
    (fun p hp hpL => ?_)).1
  have e1 := f.qExpansion_coeff_eq_eigenvalue f.isNorm ⟨p, hp.pos⟩
    (hpL.coprime_dvd_right (dvd_mul_right _ _))
  have e2 := g.qExpansion_coeff_eq_eigenvalue g.isNorm ⟨p, hp.pos⟩
    (hpL.coprime_dvd_right (dvd_mul_left _ _))
  change coeff f p = _ at e1
  change coeff g p = _ at e2
  rw [← e1, ← e2, hf p hp.ne_zero, hg p hp.ne_zero, LFunction_cd_eq_heckeCoeff hd4 hsq hp.ne_zero]

/-- **The Heegner hypothesis of the restricted leaves, made explicit.** For the newform of `C_d`
the condition `HeegnerHyp N D` is `HeegnerHyp (32 d²) D`. -/
theorem heegnerHyp_iff_of_coeff_cd {d : ℕ} (hd4 : d % 4 = 1) (hsq : Squarefree d) {N : ℕ}
    [NeZero N] (f : Newform N 2) (hχ : f.χ = 1)
    (hf : ∀ n : ℕ, n ≠ 0 → coeff f n = ((shortCurve (-(d : ℚ) ^ 2)).LFunction n : ℂ)) (D : ℤ) :
    HeegnerHyp N D ↔ HeegnerHyp (32 * d ^ 2) D := by
  rw [level_eq_of_coeff_cd hd4 hsq f hχ hf]

/-- `HeegnerHyp (32 d²) D` in elementary terms: `(2 / |D|) = 1` and `(p / |D|) = 1` for every
prime `p ∣ d`. -/
theorem heegnerHyp_32_iff {d : ℕ} (hd : d ≠ 0) (D : ℤ) :
    HeegnerHyp (32 * d ^ 2) D ↔
      jacobiSym 2 D.natAbs = 1 ∧ ∀ p : ℕ, p.Prime → p ∣ d → jacobiSym (p : ℤ) D.natAbs = 1 := by
  constructor
  · intro h
    refine ⟨by exact_mod_cast h 2 Nat.prime_two (dvd_mul_of_dvd_left (by norm_num) _),
      fun p hp hpd => h p hp (dvd_mul_of_dvd_right (dvd_pow hpd two_ne_zero) _)⟩
  · rintro ⟨h2, hd'⟩ p hp hpN
    rcases (Nat.Prime.dvd_mul hp).mp hpN with h32 | hdd
    · have : p = 2 := by
        have h32' : p ∣ 2 ^ 5 := by norm_num; exact h32
        exact (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (hp.dvd_of_dvd_pow h32')
      subst this
      exact_mod_cast h2
    · exact hd' p hp (hp.dvd_of_dvd_pow hdd)

end ZInQ.GZStatements
