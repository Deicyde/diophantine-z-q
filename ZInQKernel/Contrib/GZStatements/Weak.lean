import ZInQKernel.Contrib.GZTheta.NewCMFinal

/-!
# gz-statements: the two remaining Gross–Zagier leaves, weakened to what the glue uses

Task gz-statements (statement review of `ZInQ.GZDecomp.FHNonvanishing` and
`ZInQ.GZDecomp.GrossZagierHeegner`; report `docs/research/gz-statements.md`).

The glue of gz-decomp (`ZInQ.GZDecomp.grossZagierCd_of_leaves`) applies the two leaves once
each, to the newform `f` of the curve `C_d : y² = x³ − d²x` with `d ≡ 5 (mod 8)` squarefree, and
`FHNonvanishing` only with the bound `B = 4`. This file states the leaves restricted to that use
and proves:

* each original leaf implies its restricted form (so the restricted forms are weaker);
* the restricted forms, with the proved leaf `HeckeThetaNewform` (task atkin-li), still give
  `GrossZagierCd` and Theorem 1.1;
* the restricted Gross–Zagier leaves are implied by `GrossZagierCd`, hence by the original premise
  `Literature.GrossZagier` (so they are never stronger than the premise they replace).

Objects: all from `ZInQKernel/Contrib/GZDecomp/Decomp.lean` (`coeff`, `rootNumber`, `chiD`,
`IsOddImagFundDisc`, `HeegnerHyp`, `twistCoeff`, `IsEntireCont`), Tau Ceti's `Newform`, and
Mathlib's `WeierstrassCurve.LFunction`, `Affine.Point`, `Affine.Point.map`.
-/

open UpperHalfPlane HeckeRing.GL2 WeierstrassCurve
open scoped WeierstrassCurve.Affine

namespace ZInQ.GZStatements

open ZInQ.GZDecomp

/-! ## The restricted leaves -/

/-- **(L2, restricted) Friedberg–Hoffstein for the newform of `C_d`, `d ≡ 5 (mod 8)`.** Let `f` be
a newform of weight 2, level `N`, trivial nebentypus, with `aₙ(f) = aₙ(C_d)` for `n ≥ 1` and
root number `−1`. Then there is an odd imaginary fundamental discriminant `D < −4` such that every
prime `p ∣ N` splits in `ℚ(√D)` and the entire continuation of `L(f ⊗ χ_D, s)` does not vanish
at the centre `s = 1`.

A published theorem (research tier), applied to one family: S. Friedberg, J. Hoffstein, Ann. of
Math. 142 (1995), 385-423, main nonvanishing theorem for central values (UNVERIFIED number, cited
as Thm B by gz-decomp), with `π = π_f`, `S = {∞, 2} ∪ {p ∣ N}`, `χ_∞ = sgn`, `χ_v = 1` at
`v ∣ 2N`; "infinitely many `χ`" is used only to avoid `D = −3`. Folded in (textbook):
`ε(f ⊗ χ_D) = ε(f) χ_D(−N) = +1` for `(D, N) = 1`. It is implied by `GZDecomp.FHNonvanishing`
(`fhNonvanishingCd_of_fhNonvanishing`). -/
def FHNonvanishingCd : Prop :=
  ∀ d : ℕ, d % 8 = 5 → Squarefree d →
  ∀ (N : ℕ) [NeZero N] (f : Newform N 2) (hχ : f.χ = 1),
    (∀ n : ℕ, n ≠ 0 → coeff f n = ((shortCurve (-(d : ℚ) ^ 2)).LFunction n : ℂ)) →
    rootNumber f hχ = -1 →
    ∃ D : ℤ, D < -4 ∧ IsOddImagFundDisc D ∧ HeegnerHyp N D ∧
      ∀ G : ℂ → ℂ, IsEntireCont (twistCoeff f D) 2 G → G 1 ≠ 0

/-- **(L3, restricted) Gross–Zagier with Gross's conjugation relation for `C_d`,
`d ≡ 5 (mod 8)`.** `GZDecomp.GrossZagierHeegner` with `E = C_d`. For `C_d` (CM by `ℤ[i]`) the
modular parametrization `X₀(N) → C_d` is Shimura's (Nagoya Math. J. 43 (1971), UNVERIFIED), so
Faltings' isogeny theorem, folded into the unrestricted leaf, is not needed.

A published theorem (research tier): B. Gross, D. Zagier, Invent. Math. 84 (1986), 225-320
(Thm I.6.3 and Ch. V, UNVERIFIED numbers), with Gross, *Heegner points on X₀(N)* (1984) for
`ȳ_K = −ε y_K` mod torsion (UNVERIFIED). Implied by `GZDecomp.GrossZagierHeegner`
(`grossZagierHeegnerCd_of_grossZagierHeegner`) and by `GZDecomp.GrossZagierCd`
(`grossZagierHeegnerCd_of_grossZagierCd`). -/
def GrossZagierHeegnerCd : Prop :=
  ∀ d : ℕ, d % 8 = 5 → Squarefree d →
  ∀ (N : ℕ) [NeZero N] (f : Newform N 2), f.χ = 1 →
    (∀ n : ℕ, n ≠ 0 → coeff f n = ((shortCurve (-(d : ℚ) ^ 2)).LFunction n : ℂ)) →
    ∀ D : ℤ, IsOddImagFundDisc D → D < -4 → HeegnerHyp N D →
    ∀ F G : ℂ → ℂ, IsEntireCont (coeff f) 2 F → IsEntireCont (twistCoeff f D) 2 G →
      analyticOrderAt F 1 = 1 → G 1 ≠ 0 →
    ∀ (K : Type) [Field K] [DecidableEq K] [Algebra ℚ K], Module.finrank ℚ K = 2 →
      (∃ δ : K, δ ^ 2 = algebraMap ℚ K D) →
      ∃ y : ((shortCurve (-(d : ℚ) ^ 2))⁄K).Point, ¬IsOfFinAddOrder y ∧
        ∀ σ : K ≃ₐ[ℚ] K, IsOfFinAddOrder (Affine.Point.map σ.toAlgHom y - y)

/-- **(L3, weakest) Gross–Zagier's rank corollary for `C_d`, `d ≡ 5 (mod 8)`.** If `L(C_d, s)`
has a simple zero at `s = 1` and there is an odd Heegner discriminant `D < −4` for the level with
`L(C_d ⊗ χ_D, 1) ≠ 0`, then `C_d(ℚ)` has a point of infinite order. This is the form in which
Gross–Zagier (1986) state the rank consequence (`L'(E/K, 1) ≠ 0` ⇒ `y_K` of infinite order, and
`y_K + ȳ_K = 2 y_K` mod torsion is rational; Ch. V, UNVERIFIED locator). Implied by
`GrossZagierHeegnerCd` (`grossZagierRankCd_of_grossZagierHeegnerCd`) and by
`GZDecomp.GrossZagierCd` (`grossZagierRankCd_of_grossZagierCd`). -/
def GrossZagierRankCd : Prop :=
  ∀ d : ℕ, d % 8 = 5 → Squarefree d →
  ∀ (N : ℕ) [NeZero N] (f : Newform N 2), f.χ = 1 →
    (∀ n : ℕ, n ≠ 0 → coeff f n = ((shortCurve (-(d : ℚ) ^ 2)).LFunction n : ℂ)) →
    ∀ D : ℤ, IsOddImagFundDisc D → D < -4 → HeegnerHyp N D →
    ∀ F G : ℂ → ℂ, IsEntireCont (coeff f) 2 F → IsEntireCont (twistCoeff f D) 2 G →
      analyticOrderAt F 1 = 1 → G 1 ≠ 0 →
      ∃ P : (shortCurve (-(d : ℚ) ^ 2)).toAffine.Point, ¬IsOfFinAddOrder P

/-! ## The restricted forms are weaker -/

theorem fhNonvanishingCd_of_fhNonvanishing (h : FHNonvanishing) : FHNonvanishingCd := by
  intro d _ _ N _ f hχ _ hw
  obtain ⟨D, hDB, hDisc, hHeeg, hG⟩ := h N f hχ hw 4
  exact ⟨D, by simpa using hDB, hDisc, hHeeg, hG⟩

theorem grossZagierHeegnerCd_of_grossZagierHeegner (h : GrossZagierHeegner) :
    GrossZagierHeegnerCd := by
  intro d hd hsq N _ f hχ hf D hDisc hD4 hHeeg F G hF hG h1 hG1 K _ _ _ hK hδ
  have : (shortCurve (-(d : ℚ) ^ 2)).IsElliptic :=
    shortCurve_cd_isElliptic (by omega)
  exact h _ N f hχ hf D hDisc hD4 hHeeg F G hF hG h1 hG1 K hK hδ

/-- The Heegner-point form gives the rank form (glue G4 and G5 of gz-decomp). -/
theorem grossZagierRankCd_of_grossZagierHeegnerCd (h : GrossZagierHeegnerCd) :
    GrossZagierRankCd := by
  intro d hd hsq N _ f hχ hf D hDisc hD4 hHeeg F G hF hG h1 hG1
  have hD0 : (D : ℚ) < 0 := by exact_mod_cast hDisc.1
  obtain ⟨K, hKf, hKa, hK2, δ, hδ⟩ := exists_quadratic_field hD0
  classical
  obtain ⟨y, hy, hyσ⟩ := h d hd hsq N f hχ hf D hDisc hD4 hHeeg F G hF hG h1 hG1 K hK2
    ⟨δ, by simpa using hδ⟩
  exact exists_rat_point_of_heegner hK2 y hy hyσ

/-! ## The restricted forms still close the chain -/

/-- **`GrossZagierCd` from the restricted Friedberg–Hoffstein leaf and the rank form of
Gross–Zagier** (with the proved leaf `HeckeThetaNewform` and the proved glue G1-G3, G6). -/
theorem grossZagierCd_of_fhNonvanishingCd_grossZagierRankCd (hL2 : FHNonvanishingCd)
    (hL3 : GrossZagierRankCd) : GrossZagierCd := by
  intro d hd hsq F hF h1
  obtain ⟨N, hN, f, hχ, hf⟩ := modular_cd ZInQ.GZTheta.heckeThetaNewform (by omega) hsq
  have hFf : IsEntireCont (coeff f) 2 F := isEntireCont_of_isLContinuation hf hF
  have hw : rootNumber f hχ = -1 := signOfSimpleZero N f hχ F hFf h1
  obtain ⟨D, hD4, hDisc, hHeeg, hGne⟩ := hL2 d hd hsq N f hχ hf hw
  obtain ⟨G, hG⟩ := exists_isEntireCont_twist f (ne_of_lt hDisc.1)
  exact hL3 d hd hsq N f hχ hf D hDisc hD4 hHeeg F G hFf hG h1 (hGne G hG)

/-- **`GrossZagierCd` from the two restricted leaves.** -/
theorem grossZagierCd_of_fhNonvanishingCd_grossZagierHeegnerCd (hL2 : FHNonvanishingCd)
    (hL3 : GrossZagierHeegnerCd) : GrossZagierCd :=
  grossZagierCd_of_fhNonvanishingCd_grossZagierRankCd hL2
    (grossZagierRankCd_of_grossZagierHeegnerCd hL3)

/-- **Theorem 1.1 from `SixContactMin`, TYZ reading A and the two restricted leaves.** -/
theorem frozenTarget_of_sixContactMin_tyzThm35ReadingA_fhNonvanishingCd_grossZagierHeegnerCd
    (hH : SixContactMin) (hA : ZInQ.Literature.TYZThm35ReadingA) (hL2 : FHNonvanishingCd)
    (hL3 : GrossZagierHeegnerCd) : FrozenTarget :=
  frozenTarget_of_sixContactMin_tyzThm35ReadingA_grossZagierCd hH hA
    (grossZagierCd_of_fhNonvanishingCd_grossZagierHeegnerCd hL2 hL3)

/-- **Theorem 1.1 from `SixContactMin`, TYZ reading A, the restricted Friedberg–Hoffstein leaf
and the rank form of Gross–Zagier.** -/
theorem frozenTarget_of_sixContactMin_tyzThm35ReadingA_fhNonvanishingCd_grossZagierRankCd
    (hH : SixContactMin) (hA : ZInQ.Literature.TYZThm35ReadingA) (hL2 : FHNonvanishingCd)
    (hL3 : GrossZagierRankCd) : FrozenTarget :=
  frozenTarget_of_sixContactMin_tyzThm35ReadingA_grossZagierCd hH hA
    (grossZagierCd_of_fhNonvanishingCd_grossZagierRankCd hL2 hL3)

/-! ## The restricted Gross–Zagier leaves are no stronger than the premise they replace -/

/-- A continuation of `L(f, s)` from `Re s > 2`, for the newform `f` of `C_d`, is a continuation
of `L(C_d, s)` from `Re s > 3/2` (Hecke's continuation `ZInQ.Contrib.heckeContinuation`, proved,
and uniqueness of entire continuations). -/
theorem isLContinuation_of_isEntireCont {d : ℕ} (hd : d ≠ 0) {N : ℕ} [NeZero N]
    {f : Newform N 2}
    (hf : ∀ n : ℕ, n ≠ 0 → coeff f n = ((shortCurve (-(d : ℚ) ^ 2)).LFunction n : ℂ))
    {F : ℂ → ℂ} (hF : IsEntireCont (coeff f) 2 F) :
    ZInQ.Literature.IsLContinuation (shortCurve (-(d : ℚ) ^ 2)) F := by
  obtain ⟨F', hF'⟩ := ZInQ.Contrib.heckeContinuation d hd
  have hF'f : IsEntireCont (coeff f) 2 F' := isEntireCont_of_isLContinuation hf hF'
  rw [hF.eq hF'f]
  exact hF'

/-- A rational point of infinite order gives a point of `E(K)` of infinite order fixed by
`Aut(K/ℚ)`. -/
theorem exists_fixed_point_of_rat_point {E : WeierstrassCurve ℚ} {K : Type} [Field K]
    [DecidableEq K] [Algebra ℚ K] (h : ∃ P : E.toAffine.Point, ¬IsOfFinAddOrder P) :
    ∃ y : (E⁄K).Point, ¬IsOfFinAddOrder y ∧
      ∀ σ : K ≃ₐ[ℚ] K, IsOfFinAddOrder (Affine.Point.map σ.toAlgHom y - y) := by
  have hE : E⁄ℚ = E := by
    simp [WeierstrassCurve.baseChange, Algebra.algebraMap_self]
  have key : ∀ W : WeierstrassCurve ℚ, W = E → (∃ Q : W.toAffine.Point, ¬IsOfFinAddOrder Q) →
      ∃ Q : (E⁄ℚ).Point, ¬IsOfFinAddOrder Q := by
    rintro W rfl hQ
    rw [hE]
    exact hQ
  obtain ⟨Q, hQ⟩ := key E rfl h
  refine ⟨Affine.Point.baseChange ℚ K Q, ?_, fun σ => ?_⟩
  · intro hy
    exact hQ ((Function.Injective.isOfFinAddOrder_iff
      (Affine.Point.map_injective (W' := E) (f := Algebra.ofId ℚ K))).mp hy)
  · rw [Affine.Point.map_baseChange, sub_self]
    exact IsOfFinAddOrder.zero

/-- **`GrossZagierCd` implies the rank form**: so `GrossZagierRankCd` is no stronger than
`GZDecomp.GrossZagierCd`, hence than `Literature.GrossZagier`. -/
theorem grossZagierRankCd_of_grossZagierCd (h : GrossZagierCd) : GrossZagierRankCd := by
  intro d hd hsq N _ f _ hf _ _ _ _ F _ hF _ h1 _
  exact h d hd hsq F (isLContinuation_of_isEntireCont (by omega) hf hF) h1

/-- **`GrossZagierCd` implies the restricted Heegner-point leaf**: the base change of a rational
point of infinite order is a point of `C_d(K)` of infinite order fixed by `Aut(K/ℚ)`. So
`GrossZagierHeegnerCd` is no stronger than `Literature.GrossZagier`. -/
theorem grossZagierHeegnerCd_of_grossZagierCd (h : GrossZagierCd) : GrossZagierHeegnerCd := by
  intro d hd hsq N _ f _ hf _ _ _ _ F _ hF _ h1 _ K _ _ _ _ _
  exact exists_fixed_point_of_rat_point
    (h d hd hsq F (isLContinuation_of_isEntireCont (by omega) hf hF) h1)

/-- The restricted Heegner-point leaf from the original premise. -/
theorem grossZagierHeegnerCd_of_grossZagier (h : ZInQ.Literature.GrossZagier) :
    GrossZagierHeegnerCd :=
  grossZagierHeegnerCd_of_grossZagierCd (grossZagierCd_of_grossZagier h)

end ZInQ.GZStatements
