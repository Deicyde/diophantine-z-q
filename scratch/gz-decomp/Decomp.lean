import ZInQKernel.Hypotheses.CR3Literature
import ZInQKernel.Contrib.HeckeFE.Basic
import ZInQKernel.Contrib.GaussFE.FunctionalEquation5
import ZInQKernel.Contrib.HeckeAll.LocalCd
import ZInQKernel.Contrib.TauCeti.NumberTheory.ModularForms.LFunction.Sign
import ZInQKernel.Contrib.TauCeti.AlgebraicGeometry.EllipticCurve.GaloisDescent

/-!
# gz-decomp, steps (2)-(3): `GrossZagierCd` from three leaves and glue

Objects (all genuine: Mathlib, or Tau Ceti vendored at `ZInQKernel/Contrib/TauCeti/`):
* `HeckeRing.GL2.Newform N k` (Tau Ceti): a newform of level `Γ₁(N)`, weight `k`, nebentypus
  `f.χ`, normalized `a₁ = 1`, in the new subspace;
* `coeff f n`: its `n`-th Fourier coefficient at `∞` (Mathlib's `qExpansion`, width `1`);
* `rootNumber f hχ = i² ε_N(f)` for `f.χ = 1`: the sign of Tau Ceti's functional equation
  `Λ_N(2 − s, f) = rootNumber · Λ_N(s, f)` (`HeckeRing.GL2.Newform.frickeCompletedL_sub_eq`),
  `Λ_N(s, f) = N^{s/2} (2π)^{−s} Γ(s) L(f, s)`;
* `chiD D n = (n / |D|)` (Jacobi): for `D ≡ 1 (mod 4)` a fundamental discriminant this is the
  Kronecker character `χ_D` of `ℚ(√D)`;
* `IsEntireCont a σ G`: `G` is entire and equals `∑ aₙ n^{−s}` on `Re s > σ`;
* Mathlib's `WeierstrassCurve.LFunction`, `Affine.Point`, `Affine.Point.map`.

The Prop `GrossZagierCd` is restated from `Scope.lean` (the two scratch files are never imported
together).
-/

open UpperHalfPlane HeckeRing.GL2 WeierstrassCurve
open scoped WeierstrassCurve.Affine

namespace ZInQ.GZDecomp

/-! ## Objects -/

/-- The `n`-th Fourier coefficient `aₙ(f)` of a newform (expansion at `∞` in `q = e^{2πiτ}`). -/
noncomputable def coeff {N : ℕ} [NeZero N] {k : ℤ} (f : Newform N k) (n : ℕ) : ℂ :=
  (qExpansion 1 f.toCuspForm).coeff n

/-- `G` is an entire continuation of the Dirichlet series `∑ aₙ n^{−s}` from `Re s > σ`. -/
def IsEntireCont (a : ℕ → ℂ) (σ : ℝ) (G : ℂ → ℂ) : Prop :=
  Differentiable ℂ G ∧ ∀ s : ℂ, σ < s.re → G s = LSeries a s

/-- Entire continuations are unique (identity theorem). -/
theorem IsEntireCont.eq {a : ℕ → ℂ} {σ : ℝ} {F G : ℂ → ℂ} (hF : IsEntireCont a σ F)
    (hG : IsEntireCont a σ G) : F = G := by
  have hU : {s : ℂ | σ < s.re} ∈ nhds ((σ + 1 : ℝ) : ℂ) :=
    (isOpen_lt continuous_const Complex.continuous_re).mem_nhds (by simp)
  have hev : F =ᶠ[nhds ((σ + 1 : ℝ) : ℂ)] G :=
    Filter.mem_of_superset hU fun s hs => (hF.2 s hs).trans (hG.2 s hs).symm
  funext z
  have hFa := Complex.analyticOnNhd_univ_iff_differentiable.mpr hF.1
  have hGa := Complex.analyticOnNhd_univ_iff_differentiable.mpr hG.1
  exact hFa.eqOn_of_preconnected_of_eventuallyEq hGa isPreconnected_univ (Set.mem_univ _) hev
    (Set.mem_univ z)

/-- The **root number** of a weight-2 newform of trivial nebentypus: the sign `i² ε_N(f)` of its
functional equation (Tau Ceti, `Newform.frickeCompletedL_sub_eq`; it is `±1` by
`Newform.I_zpow_mul_frickeSign_eq_one_or_neg_one`). -/
noncomputable def rootNumber {N : ℕ} [NeZero N] (f : Newform N 2) (hχ : f.χ = 1) : ℂ :=
  Complex.I ^ (2 : ℤ) * f.frickeSign hχ

/-- The quadratic character `n ↦ (n / |D|)`; for a fundamental discriminant `D ≡ 1 (mod 4)` it is
the Kronecker character `χ_D` of `ℚ(√D)`. -/
noncomputable def chiD (D : ℤ) (n : ℕ) : ℂ := (jacobiSym (n : ℤ) D.natAbs : ℂ)

/-- `D` is an odd negative fundamental discriminant: `D < 0`, `D ≡ 1 (mod 4)`, squarefree. -/
def IsOddImagFundDisc (D : ℤ) : Prop := D < 0 ∧ D % 4 = 1 ∧ Squarefree D

/-- **Heegner hypothesis**: every prime `p ∣ N` splits in `ℚ(√D)`, i.e. `χ_D(p) = 1`. -/
def HeegnerHyp (N : ℕ) (D : ℤ) : Prop :=
  ∀ p : ℕ, p.Prime → p ∣ N → jacobiSym (p : ℤ) D.natAbs = 1

/-- The coefficient sequence of the twist `f ⊗ χ_D`. -/
noncomputable def twistCoeff {N : ℕ} [NeZero N] {k : ℤ} (f : Newform N k) (D : ℤ) (n : ℕ) : ℂ :=
  coeff f n * chiD D n

/-! ## Leaves -/

/-- **(L1) Hecke–Shimura: the theta series of the Hecke character of `C_d` is a newform.**
For squarefree `d ≡ 1 (mod 4)`, the series `∑ₙ heckeCoeff d n qⁿ`, where
`heckeCoeff d n = ¼ ∑_{α ∈ ℤ[i], N(α) = n} (N(α)/d)·u(α)·α` is the Hecke character `ψ_d` of `ℚ(i)`
attached to `C_d` (`HeckeFE.heckeCoeff`), is a newform of weight 2 and trivial nebentypus at
some level `N`.

Literature: E. Hecke (1936-37, Math. Ann. 114); G. Shimura, *Introduction to the arithmetic theory
of automorphic functions* (1971); T. Miyake, *Modular forms* (1989), Theorem 4.8.2 (primitive
Hecke character of an imaginary quadratic field ↦ primitive form of level `|d_K| N(𝔪)`); H.
Iwaniec, *Topics in classical automorphic forms*, Theorem 12.5. All UNVERIFIED (no copy on this
host). The level (`32 d²`) is not asserted. -/
def HeckeThetaNewform : Prop :=
  ∀ d : ℕ, d % 4 = 1 → Squarefree d →
    ∃ (N : ℕ) (_ : NeZero N) (f : Newform N 2), f.χ = 1 ∧
      ∀ n : ℕ, n ≠ 0 → coeff f n = ZInQ.Contrib.HeckeFE.heckeCoeff d n

/-- **(L2) Friedberg–Hoffstein / Bump–Friedberg–Hoffstein: nonvanishing of central twisted values
with the Heegner local conditions.** Let `f` be a newform of weight 2, level `N`, trivial
nebentypus, with root number `−1`. Then for every bound `B` there is an odd imaginary
fundamental discriminant `D < −B` such that every prime `p ∣ N` splits in `ℚ(√D)` and the twisted
L-series `L(f ⊗ χ_D, s) = ∑ aₙ(f) χ_D(n) n^{−s}` has an entire continuation not vanishing at the
centre `s = 1`.

Literature: S. Friedberg, J. Hoffstein, Ann. of Math. 142 (1995), 385-423, Theorem B (UNVERIFIED
number); D. Bump, S. Friedberg, J. Hoffstein, Invent. Math. 102 (1990), 543-618 (UNVERIFIED);
alternatively Waldspurger, Compositio Math. 54 (1985) / J. Math. Pures Appl. 60 (1981) with
local conditions. Folded in (textbook): the root number of the twist,
`ε(f ⊗ χ_D) = ε(f) χ_D(−N) = +1` for `(D, N) = 1` (Shimura; Atkin–Li, Invent. Math. 48 (1978)),
which is the compatibility hypothesis of the source; and the continuation of `L(f ⊗ χ_D, s)`
(Shimura; Tau Ceti `CuspForm.twist` with `CuspForm.hasEntireExtension_qExpansion_coeff`). -/
def FHNonvanishing : Prop :=
  ∀ (N : ℕ) [NeZero N] (f : Newform N 2) (hχ : f.χ = 1), rootNumber f hχ = -1 →
    ∀ B : ℕ, ∃ D : ℤ, D < -(B : ℤ) ∧ IsOddImagFundDisc D ∧ HeegnerHyp N D ∧
      ∃ G : ℂ → ℂ, IsEntireCont (twistCoeff f D) 2 G ∧ G 1 ≠ 0

/-- **(L3) Gross–Zagier with Gross's conjugation relation, in the form that can be stated today.**
Let `E/ℚ` be an elliptic curve whose L-series is that of a weight-2 newform `f` of level `N` and
trivial nebentypus (`aₙ(f) = aₙ(E)` for all `n ≥ 1`). Let `D < −4` be an odd fundamental
discriminant with the Heegner hypothesis for `N`, and suppose `L(f, s)` has a simple zero at
`s = 1` while `L(f ⊗ χ_D, 1) ≠ 0` (so `L'(E/K, 1) = L'(f, 1) L(f ⊗ χ_D, 1) ≠ 0`). Then for every
field `K ≅ ℚ(√D)` the group `E(K)` has a point `y` of infinite order (the Heegner point `y_K`)
with `σ y − y` torsion for every `σ ∈ Aut(K/ℚ)` (`ȳ_K = −ε y_K` up to torsion, `ε = −1`).

Literature: B. Gross, D. Zagier, Invent. Math. 84 (1986), 225-320, Theorem I.6.3 and its
corollaries in Ch. V (UNVERIFIED numbers): `L'(E/K, 1) = c ĥ(y_K)` with `c ≠ 0`; B. Gross,
*Heegner points on X₀(N)*, Modular forms (Durham 1983), 1984, for `ȳ_K = −ε y_K` mod torsion
(UNVERIFIED). Folded in, because the modular curve `X₀(N)`, the parametrization and the Heegner
point cannot be stated in Lean today: the modular parametrization `X₀(N) → E` (Eichler–Shimura
construction of the strong Weil curve `E_f`, Shimura 1971, Thm 7.14-7.15, UNVERIFIED, plus
Faltings 1983 Korollar 2 (`L(E) = L(E_f)` ⇒ `E ∼ E_f`), or for CM curves Shimura, Nagoya Math. J.
43 (1971)); and nondegeneracy of `ĥ` on `E(K)` (proved in Tau Ceti:
`Affine.Point.canonicalHeight_eq_zero_iff_isOfFinAddOrder`). -/
def GrossZagierHeegner : Prop :=
  ∀ (E : WeierstrassCurve ℚ) [E.IsElliptic] (N : ℕ) [NeZero N] (f : Newform N 2), f.χ = 1 →
    (∀ n : ℕ, n ≠ 0 → coeff f n = (E.LFunction n : ℂ)) →
    ∀ D : ℤ, IsOddImagFundDisc D → D < -4 → HeegnerHyp N D →
    ∀ F G : ℂ → ℂ, IsEntireCont (coeff f) 2 F → IsEntireCont (twistCoeff f D) 2 G →
      analyticOrderAt F 1 = 1 → G 1 ≠ 0 →
    ∀ (K : Type) [Field K] [DecidableEq K] [Algebra ℚ K], Module.finrank ℚ K = 2 →
      (∃ δ : K, δ ^ 2 = algebraMap ℚ K D) →
      ∃ y : (E⁄K).Point, ¬IsOfFinAddOrder y ∧
        ∀ σ : K ≃ₐ[ℚ] K, IsOfFinAddOrder (Affine.Point.map σ.toAlgHom y - y)

/-! ## Glue -/

/-- **(G3) The sign of a simple zero.** If `L(f, s)` has a simple zero at the centre then the
root number is `−1`. From Tau Ceti's functional equation (`Newform.frickeCompletedL_sub_eq`,
sign `±1`): with sign `+1`, `Λ_N(1 + z)` is even, so its order at `z = 0` is even, and
`Λ_N = N^{s/2}(2π)^{−s}Γ(s) F` with a nonvanishing factor at `s = 1`. Open (medium) unless proved
below. -/
def SignOfSimpleZero : Prop :=
  ∀ (N : ℕ) [NeZero N] (f : Newform N 2) (hχ : f.χ = 1) (F : ℂ → ℂ),
    IsEntireCont (coeff f) 2 F → analyticOrderAt F 1 = 1 → rootNumber f hχ = -1

/-- `GrossZagierCd` (as in `Scope.lean`). -/
def GrossZagierCd : Prop :=
  ∀ d : ℕ, d % 8 = 5 → Squarefree d → ∀ F : ℂ → ℂ,
    ZInQ.Literature.IsLContinuation (shortCurve (-(d : ℚ) ^ 2)) F → analyticOrderAt F 1 = 1 →
      ∃ P : (shortCurve (-(d : ℚ) ^ 2)).toAffine.Point, ¬IsOfFinAddOrder P

/-- **(G1) Modularity of `C_d` in L-series form**, from (L1) and Deuring's identity
`cdCoeff d = heckeCoeff d` (proved: `HeckeFE.deuringCd_of_gaussPointCount`,
`GaussFE.gaussPointCount`). -/
theorem modular_cd (hL1 : HeckeThetaNewform) {d : ℕ} (hd4 : d % 4 = 1) (hsq : Squarefree d) :
    ∃ (N : ℕ) (_ : NeZero N) (f : Newform N 2), f.χ = 1 ∧
      ∀ n : ℕ, n ≠ 0 → coeff f n = ((shortCurve (-(d : ℚ) ^ 2)).LFunction n : ℂ) := by
  obtain ⟨N, hN, f, hχ, hf⟩ := hL1 d hd4 hsq
  refine ⟨N, hN, f, hχ, fun n hn => ?_⟩
  have hD := ZInQ.Contrib.HeckeFE.deuringCd_of_gaussPointCount hd4 hsq
    ZInQ.Contrib.GaussFE.gaussPointCount n hn
  rw [hf n hn, ← hD, ZInQ.Contrib.HeckeAll.LFunction_cd_apply' hsq hn]
  simp [ZInQ.Literature.cdCoeff, hn]

/-- **(G2) Transfer of the continuation.** If `aₙ(f) = aₙ(E)` for `n ≥ 1`, an entire continuation
of `L(E, s)` from `Re s > 3/2` is one of `L(f, s)` from `Re s > 2`. -/
theorem isEntireCont_of_isLContinuation {E : WeierstrassCurve ℚ} {N : ℕ} [NeZero N]
    {f : Newform N 2} (hf : ∀ n : ℕ, n ≠ 0 → coeff f n = (E.LFunction n : ℂ)) {F : ℂ → ℂ}
    (hF : ZInQ.Literature.IsLContinuation E F) : IsEntireCont (coeff f) 2 F := by
  refine ⟨hF.1, fun s hs => ?_⟩
  rw [hF.2 s (by linarith)]
  exact LSeries_congr (fun {n} hn => (hf n hn).symm) s

/-- `σ ↦ map σ` is multiplicative on points. -/
theorem map_mul_apply {E : WeierstrassCurve ℚ} {K : Type} [Field K] [DecidableEq K] [Algebra ℚ K]
    (σ τ : K ≃ₐ[ℚ] K) (y : (E⁄K).Point) :
    Affine.Point.map (σ * τ).toAlgHom y = Affine.Point.map σ.toAlgHom (Affine.Point.map τ.toAlgHom y) := by
  rw [Affine.Point.map_map]
  rfl

theorem map_one_apply {E : WeierstrassCurve ℚ} {K : Type} [Field K] [DecidableEq K] [Algebra ℚ K]
    (y : (E⁄K).Point) : Affine.Point.map (1 : K ≃ₐ[ℚ] K).toAlgHom y = y := by
  cases y <;> rfl

/-- **(G4) Descent of the Heegner point.** If `y ∈ E(K)`, `[K : ℚ] = 2`, has infinite order and
`σ y − y` is torsion for every `σ ∈ Aut(K/ℚ)`, then `E(ℚ)` has a point of infinite order
(`y + σ y`, `σ ≠ 1`, is `σ`-fixed, hence rational, and is `2y` up to torsion). -/
theorem exists_rat_point_of_heegner {E : WeierstrassCurve ℚ} {K : Type} [Field K] [DecidableEq K]
    [Algebra ℚ K] (hK : Module.finrank ℚ K = 2) (y : (E⁄K).Point) (hy : ¬IsOfFinAddOrder y)
    (hσ : ∀ σ : K ≃ₐ[ℚ] K, IsOfFinAddOrder (Affine.Point.map σ.toAlgHom y - y)) :
    ∃ P : E.toAffine.Point, ¬IsOfFinAddOrder P := by
  have : Algebra.IsQuadraticExtension ℚ K := ⟨hK⟩
  have : FiniteDimensional ℚ K := Module.finite_of_finrank_eq_succ hK
  obtain ⟨σ, hσ1⟩ := Algebra.IsQuadraticExtension.exists_algEquiv_ne_one (K := ℚ) (L := K)
  set z := y + Affine.Point.map σ.toAlgHom y with hz
  have hfix : Affine.Point.map σ.toAlgHom z = z := by
    rw [hz, map_add, ← map_mul_apply, Algebra.IsQuadraticExtension.algEquiv_mul_self,
      map_one_apply, add_comm]
  have hz_tors : ¬IsOfFinAddOrder z := by
    intro h
    apply hy
    have h2 : IsOfFinAddOrder ((2 : ℕ) • y) := by
      have : (2 : ℕ) • y = z - (Affine.Point.map σ.toAlgHom y - y) := by
        rw [hz, two_nsmul]; abel
      rw [this, sub_eq_add_neg]
      exact h.add (hσ σ).neg
    exact IsOfFinAddOrder.of_nsmul h2 two_ne_zero
  obtain ⟨Q, hQ⟩ := WeierstrassCurve.Affine.Point.exists_baseChange_eq_of_map_eq K hσ1 hfix
  have hQt : ¬IsOfFinAddOrder Q := fun h => hz_tors (hQ ▸ AddMonoidHom.isOfFinAddOrder _ h)
  have hE : E⁄ℚ = E := by
    simp [WeierstrassCurve.baseChange, Algebra.algebraMap_self]
  have key : ∀ W : WeierstrassCurve ℚ, W = E → (∃ Q : W.toAffine.Point, ¬IsOfFinAddOrder Q) →
      ∃ P : E.toAffine.Point, ¬IsOfFinAddOrder P := by
    rintro _ rfl h; exact h
  exact key _ hE ⟨Q, hQt⟩

/-! ## The quadratic field `ℚ(√D)` -/

theorem irreducible_X_sq_sub {D : ℚ} (hD : D < 0) :
    Irreducible (Polynomial.X ^ 2 - Polynomial.C D : Polynomial ℚ) := by
  have hm : (Polynomial.X ^ 2 - Polynomial.C D : Polynomial ℚ).Monic :=
    Polynomial.monic_X_pow_sub_C D (by norm_num)
  have hdeg : (Polynomial.X ^ 2 - Polynomial.C D : Polynomial ℚ).natDegree = 2 :=
    Polynomial.natDegree_X_pow_sub_C
  rw [Polynomial.Monic.irreducible_iff_roots_eq_zero_of_degree_le_three hm (by omega) (by omega)]
  refine Multiset.eq_zero_of_forall_notMem fun r hr => ?_
  rw [Polynomial.mem_roots hm.ne_zero, Polynomial.IsRoot, Polynomial.eval_sub,
    Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_C, sub_eq_zero] at hr
  nlinarith [sq_nonneg r]

theorem exists_quadratic_field {D : ℚ} (hD : D < 0) :
    ∃ (K : Type) (_ : Field K) (_ : Algebra ℚ K), Module.finrank ℚ K = 2 ∧
      ∃ δ : K, δ ^ 2 = algebraMap ℚ K D := by
  have hirr := irreducible_X_sq_sub hD
  have : Fact (Irreducible (Polynomial.X ^ 2 - Polynomial.C D : Polynomial ℚ)) := ⟨hirr⟩
  refine ⟨AdjoinRoot (Polynomial.X ^ 2 - Polynomial.C D), inferInstance, inferInstance, ?_,
    AdjoinRoot.root _, ?_⟩
  · rw [(AdjoinRoot.powerBasis hirr.ne_zero).finrank, AdjoinRoot.powerBasis_dim,
      Polynomial.natDegree_X_pow_sub_C]
  · have h := AdjoinRoot.eval₂_root (Polynomial.X ^ 2 - Polynomial.C D)
    rw [Polynomial.eval₂_sub, Polynomial.eval₂_X_pow, Polynomial.eval₂_C, sub_eq_zero] at h
    rw [h]
    rfl

/-! ## Assembly -/

/-- **`GrossZagierCd` from the three leaves and the sign glue (G3).** -/
theorem grossZagierCd_of_leaves (hL1 : HeckeThetaNewform) (hL2 : FHNonvanishing)
    (hL3 : GrossZagierHeegner) (hG3 : SignOfSimpleZero) : GrossZagierCd := by
  intro d hd hsq F hF h1
  have hd0 : d ≠ 0 := by omega
  have hEll : (shortCurve (-(d : ℚ) ^ 2)).IsElliptic := by
    have hd0' : (d : ℚ) ≠ 0 := by exact_mod_cast hd0
    exact shortCurve_isElliptic (neg_ne_zero.mpr (pow_ne_zero 2 hd0'))
  obtain ⟨N, hN, f, hχ, hf⟩ := modular_cd hL1 (by omega) hsq
  have hFf : IsEntireCont (coeff f) 2 F := isEntireCont_of_isLContinuation hf hF
  have hw : rootNumber f hχ = -1 := hG3 N f hχ F hFf h1
  obtain ⟨D, hDB, hDisc, hHeeg, G, hG, hG1⟩ := hL2 N f hχ hw 4
  have hD0 : (D : ℚ) < 0 := by exact_mod_cast hDisc.1
  obtain ⟨K, hKf, hKa, hK2, δ, hδ⟩ := exists_quadratic_field hD0
  classical
  obtain ⟨y, hy, hyσ⟩ := hL3 _ N f hχ hf D hDisc (by simpa using hDB) hHeeg F G hFf hG h1 hG1
    K hK2 ⟨δ, by simpa using hδ⟩
  exact exists_rat_point_of_heegner hK2 y hy hyσ

end ZInQ.GZDecomp

#print axioms ZInQ.GZDecomp.grossZagierCd_of_leaves
#print axioms ZInQ.GZDecomp.modular_cd
#print axioms ZInQ.GZDecomp.exists_rat_point_of_heegner
