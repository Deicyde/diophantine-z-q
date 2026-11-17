import ZInQKernel.Contrib.OneProof.GrossZagierOptimal
import ZInQKernel.Contrib.OneProof.GrossZagierHeegner.WeilLattice

/-!
# gz-optimal: the optimal-parametrization hypothesis is satisfiable

Task gz-optimal (2026-11-16). Sanity checks on `GZOptimal.IsOptimalParam`, so that the leaf
`GZOptimal.GrossZagierModuliOptAt` is not vacuous where the routes use it:

* route A: if `C_d` is its own strong Weil curve (`CdOptimal`), it has an optimal modular
  parametrization (in the sense of `IsModularParam` and `IsOptimalParam`) for every newform `f` with
  `aₙ(f) = aₙ(C_d)` (`exists_optimalParam_cd`);
* route B: the strong Weil curve given by `StrongWeilOptimal` has one (`exists_optimalParam_of_sw`).

No `sorry`, no `axiom`.
-/

noncomputable section

open UpperHalfPlane HeckeRing.GL2 WeierstrassCurve ZInQ.GZDecomp

namespace ZInQ.GZOptimal

open ZInQ.GZHeegner (ParamSetting)

/-- **Route A: `C_d` has an optimal parametrization** if it is its own strong Weil curve. -/
theorem exists_optimalParam_cd (hOpt : CdOptimal) {d : ℕ} (hd : d % 8 = 5) (hsq : Squarefree d)
    (N : ℕ) [NeZero N] (f : Newform N 2) (hχ : f.χ = 1)
    (hf : ∀ n : ℕ, n ≠ 0 → coeff f n = ((shortCurve (-(d : ℚ) ^ 2)).LFunction n : ℂ)) :
    ∃ X Y : ℍ → ℂ, ZInQ.GZModuli.IsModularParam N (shortCurve (-(d : ℚ) ^ 2)) X Y ∧
      IsOptimalParam N f (shortCurve (-(d : ℚ) ^ 2)) X Y := by
  have := shortCurve_cd_isElliptic (d := d) (by omega)
  obtain ⟨L, hL⟩ := ZInQ.GZWeil.exists_isPeriodLattice_cd (d := d) (by omega)
  obtain ⟨c₀, hlat⟩ := hOpt d hd hsq N f hχ hf L hL
  have hs : ParamSetting (shortCurve (-(d : ℚ) ^ 2)) f L c₀ :=
    ⟨hχ, hf, hL, ne_zero_of_lattice hlat, periodsIn_of_lattice hlat⟩
  exact ⟨_, _, ZInQ.GZModuli.isModularParam_of hs, L, c₀, hL, hlat, ZInQ.GZModuli.modPt_eq hs⟩

/-- **Route B: the strong Weil curve of `StrongWeilOptimal` has an optimal parametrization.** -/
theorem exists_optimalParam_of_sw (hSW : StrongWeilOptimal) (N : ℕ) [NeZero N] (f : Newform N 2)
    (hχ : f.χ = 1) (hrat : ∀ n : ℕ, n ≠ 0 → ∃ q : ℚ, coeff f n = q) :
    ∃ (E' : WeierstrassCurve ℚ) (_ : E'.IsElliptic) (X Y : ℍ → ℂ),
      ZInQ.GZModuli.IsModularParam N E' X Y ∧ IsOptimalParam N f E' X Y := by
  obtain ⟨E', hE', -, hf, L', c, hL', hlat⟩ := hSW N f hχ hrat
  have hs : ParamSetting E' f L' c := ⟨hχ, hf, hL', ne_zero_of_lattice hlat, periodsIn_of_lattice hlat⟩
  exact ⟨E', hE', _, _, ZInQ.GZModuli.isModularParam_of hs, L', c, hL', hlat,
    ZInQ.GZModuli.modPt_eq hs⟩

end ZInQ.GZOptimal
