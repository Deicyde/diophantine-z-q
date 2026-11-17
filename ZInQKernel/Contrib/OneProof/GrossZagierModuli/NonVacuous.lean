import ZInQKernel.Contrib.OneProof.GrossZagierModuli
import ZInQKernel.Contrib.OneProof.GrossZagierHeegner.WeilLattice

/-!
# gz-moduli: the hypotheses of `GrossZagierModuliAt` are satisfiable on the route

Task gz-moduli (2026-11-16). Two sanity checks on the leaf `GZModuli.GrossZagierModuliAt`
(`GrossZagierModuli.lean`), so that it is not vacuous on the curves `C_d`:

* complete sets of Heegner points exist (`exists_heegnerPointReps`, from gz-hl3's proved
  `heegnerRepsExist` and `isHeegnerPointReps_of`);
* every `C_d` (`d ≡ 5 (mod 8)` squarefree) has an algebraic modular parametrization in the sense of
  `IsModularParam` for every newform `f` with `aₙ(f) = aₙ(C_d)` (`exists_modularParam_cd`, from
  gz-weil's proved `ShimuraCMParamCd` and period lattice of `C_d`, and `isModularParam_of`).

No `sorry`, no `axiom`.
-/

noncomputable section

open UpperHalfPlane HeckeRing.GL2 WeierstrassCurve ZInQ.GZDecomp

namespace ZInQ.GZModuli

/-- **Complete sets of representatives of the Heegner points exist.** -/
theorem exists_heegnerPointReps (N : ℕ) [NeZero N] {D β : ℤ} (hD : IsOddImagFundDisc D)
    (hβ : (4 * N : ℤ) ∣ D - β ^ 2) :
    ∃ (R : Type) (_ : Fintype R) (τ : R → ℍ), IsHeegnerPointReps N D β τ := by
  obtain ⟨S, hS⟩ := ZInQ.GZHL3.heegnerRepsExist N D β hD hβ
  exact ⟨S, inferInstance, _, isHeegnerPointReps_of hD hS⟩

/-- **Every `C_d` has an algebraic modular parametrization** `X₀(N) → C_d` over `ℚ` (in the sense of
`IsModularParam`) for every newform `f` of level `N` with `aₙ(f) = aₙ(C_d)`. -/
theorem exists_modularParam_cd {d : ℕ} (hd : d % 8 = 5) (hsq : Squarefree d) (N : ℕ) [NeZero N]
    (f : Newform N 2) (hχ : f.χ = 1)
    (hf : ∀ n : ℕ, n ≠ 0 → coeff f n = ((shortCurve (-(d : ℚ) ^ 2)).LFunction n : ℂ)) :
    ∃ X Y : ℍ → ℂ, IsModularParam N (shortCurve (-(d : ℚ) ^ 2)) X Y := by
  have := shortCurve_cd_isElliptic (d := d) (by omega)
  obtain ⟨L, hL⟩ := ZInQ.GZWeil.exists_isPeriodLattice_cd (d := d) (by omega)
  obtain ⟨c, hc, hP⟩ := ZInQ.GZWeil.shimuraCMParamCd_proved d hd hsq N f hχ hf L hL
  exact ⟨_, _, isModularParam_of (E := shortCurve (-(d : ℚ) ^ 2)) ⟨hχ, hf, hL, hc, hP⟩⟩

end ZInQ.GZModuli
