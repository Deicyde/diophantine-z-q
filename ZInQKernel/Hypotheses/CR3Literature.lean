import Mathlib.AlgebraicGeometry.EllipticCurve.LFunction
import Mathlib.Analysis.Analytic.Order
import Mathlib.Analysis.Analytic.Uniqueness
import Mathlib.Analysis.Complex.CauchyIntegral
import ZInQKernel.RouteK.Rank.Statements

/-!
# CR₃ from three literature statements

The hypothesis `RouteK.Rank.CertifiedRankTYZClRk` (positive rank of `C_d : y² = x³ − d²x` for
squarefree `d ≡ 5 (mod 8)` with `T5bCl d = 1`), from which Lean derives every form of CR₃,
follows from three Props over Mathlib's L-series of an elliptic curve
(`certifiedRankTYZClRk_of_literature`). The plan is `docs/research/wk-cr3.md`.

**The L-series.** `L(E, s)` is Mathlib's `WeierstrassCurve.LSeries`: the Euler product of the
local factors of the minimal model (arithmetic normalization, centre `s = 1`, absolute
convergence for `Re s > 3/2` by Hasse's bound). "The order of vanishing of `L(E, s)` at `s = 1`"
is `analyticOrderAt F 1` for an entire `F` that agrees with the series on `Re s > 3/2`
(`IsLContinuation`). Such an `F` is unique (`IsLContinuation.eq`), so no Prop depends on the
choice of continuation.

## Trust

* `GrossZagier` is a textbook theorem: Gross–Zagier (Invent. Math. 84 (1986)) with an auxiliary
  imaginary quadratic twist (Bump–Friedberg–Hoffstein 1990, Friedberg–Hoffstein 1995) and
  modularity (Breuil–Conrad–Diamond–Taylor 2001).
* `FunctionalEquation5` is a textbook theorem: the functional equation of the Hecke L-function
  of the CM curve `C_d` (Deuring, Hecke), conductor `32 d²`, root number `−1` for
  `d ≡ 5 (mod 8)` (Birch–Stephens, Topology 5 (1966)). It is stated on the strip `0 < Re s < 2`
  only.
* `TYZRow5b` follows, with Hecke's continuation, from Tian–Yuan–Zhang's Theorem 3.5(2)
  (`n ≡ 5 (mod 8)`, row `(7, 3)`, contrapositive) in reading A, which no refereed text that we
  have read prints. TYZ was read in its arXiv version 1411.4728v1 only, whose Theorem 1.2 is false
  read literally. It is proved from unambiguous TYZ statements by Proposition N
  (`docs/research/nt-tyz.md` §4; two reviews by AI models, none by a human). The documented route is
  `tyzRow5b_of_readingA`, from `TYZThm35ReadingA` and Hecke's continuation `HeckeContinuation`.
-/

namespace ZInQ.Literature

open WeierstrassCurve ZInQ.RouteK.Rank5b

/-- `F` is an entire continuation of `L(E, s)` from the half-plane `Re s > 3/2`. -/
def IsLContinuation (E : WeierstrassCurve ℚ) (F : ℂ → ℂ) : Prop :=
  Differentiable ℂ F ∧ ∀ s : ℂ, 3 / 2 < s.re → F s = E.LSeries s

/-- Two entire continuations agree everywhere (identity theorem), so the Props below do not
depend on the choice of `F`. -/
theorem IsLContinuation.eq {E : WeierstrassCurve ℚ} {F G : ℂ → ℂ} (hF : IsLContinuation E F)
    (hG : IsLContinuation E G) : F = G := by
  have hU : {s : ℂ | 3 / 2 < s.re} ∈ nhds (2 : ℂ) :=
    (isOpen_lt continuous_const Complex.continuous_re).mem_nhds (by norm_num)
  have hev : F =ᶠ[nhds (2 : ℂ)] G :=
    Filter.mem_of_superset hU fun s hs => (hF.2 s hs).trans (hG.2 s hs).symm
  funext z
  have hFa := Complex.analyticOnNhd_univ_iff_differentiable.mpr hF.1
  have hGa := Complex.analyticOnNhd_univ_iff_differentiable.mpr hG.1
  exact hFa.eqOn_of_preconnected_of_eventuallyEq hGa isPreconnected_univ (Set.mem_univ 2) hev
    (Set.mem_univ z)

/-- **Gross–Zagier** (positive-rank half, for every elliptic curve over `ℚ`). If `L(E, s)` has a
simple zero at `s = 1`, then `E(ℚ)` has a point of infinite order.

Literature: B. Gross, D. Zagier, Invent. Math. 84 (1986), 225–320 (Heegner point of infinite
order when `L'(E/K, 1) ≠ 0`); an auxiliary imaginary quadratic `K` with the Heegner hypothesis
and `L(E^K, 1) ≠ 0` (Bump–Friedberg–Hoffstein, Invent. Math. 102 (1990), through Waldspurger's
formula; or Friedberg–Hoffstein, Ann. of Math. 142 (1995); `docs/research/cr3-trust.md`, step
D2); modularity of `E` (Breuil–Conrad–Diamond–Taylor, J. AMS 14 (2001); for CM curves Shimura
1971). Kolyvagin (Math. USSR Izv. 32 (1989)) adds `rank = 1`, not used. -/
def GrossZagier : Prop :=
  ∀ (E : WeierstrassCurve ℚ), E.IsElliptic → ∀ F : ℂ → ℂ, IsLContinuation E F →
    analyticOrderAt F 1 = 1 → ∃ P : E.toAffine.Point, ¬IsOfFinAddOrder P

/-- **Root number `−1` for `C_d`, `d ≡ 5 (mod 8)`**: the continuation of `L(C_d, s)` vanishes at
`s = 1`. Literature: the functional equation `Λ(2 − s) = w Λ(s)` with
`Λ(s) = N^{s/2}(2π)^{−s}Γ(s)L(s)` (Hecke, Deuring: `C_d` has CM by `ℤ[i]`) and
`w(C_d) = −1` for `d ≡ 5, 6, 7 (mod 8)` (Birch–Stephens, Topology 5 (1966)); then
`Λ(1) = −Λ(1)` and `Γ(1) ≠ 0`. -/
def RootNumberVanishing : Prop :=
  ∀ d : ℕ, d % 8 = 5 → Squarefree d → ∀ F : ℂ → ℂ,
    IsLContinuation (shortCurve (-(d : ℚ) ^ 2)) F → F 1 = 0

/-- **Tian–Yuan–Zhang, row 5b** ("`𝓛(n) ≠ 0`"): for squarefree `d ≡ 5 (mod 8)` with odd `(7, 3)`
genus sum `T5bCl d`, `L(C_d, s)` has an entire continuation whose order at `s = 1` is at most 1.

Literature: TYZ, arXiv:1411.4728v1 (the journal text, Asian J. Math. 21 (2017), was not
compared), Theorem 3.5(2) for `n ≡ 5 (mod 8)` in reading A
(`d₁ = 1` admitted; `docs/research/nt-tyz.md` §1.3), contrapositive, row `(7, 3)` only; the
existence of the continuation is Hecke's (CM). Not a literal published sentence: the only
statement of reading A that we have found is Smith's (arXiv:1603.08479, Theorem 2.1,
unrefereed), and it is proved from unambiguous TYZ statements by Proposition N (nt-tyz §4). -/
def TYZRow5b : Prop :=
  ∀ d : ℕ, d % 8 = 5 → Squarefree d → T5bCl d = 1 →
    ∃ F : ℂ → ℂ, IsLContinuation (shortCurve (-(d : ℚ) ^ 2)) F ∧ analyticOrderAt F 1 ≤ 1

theorem enat_eq_one {x : ℕ∞} (h1 : x ≤ 1) (h0 : x ≠ 0) : x = 1 :=
  le_antisymm h1 (Order.one_le_iff_ne_zero.mpr h0)

/-- **Analytic rank one for the TYZ curves**, from TYZ row 5b and the root number. -/
theorem analyticOrder_eq_one (hT : TYZRow5b) (hW : RootNumberVanishing) {d : ℕ} (hd : d % 8 = 5)
    (hsq : Squarefree d) (h5b : T5bCl d = 1) :
    ∃ F : ℂ → ℂ, IsLContinuation (shortCurve (-(d : ℚ) ^ 2)) F ∧ analyticOrderAt F 1 = 1 := by
  obtain ⟨F, hF, hle⟩ := hT d hd hsq h5b
  refine ⟨F, hF, enat_eq_one hle ?_⟩
  exact analyticOrderAt_ne_zero.mpr ⟨hF.1.analyticAt 1, hW d hd hsq F hF⟩

/-- **CR₃^TYZ_Cl,Rk from the literature**: Tian–Yuan–Zhang row 5b, the root number, and
Gross–Zagier. By the existing Lean chains this gives every form of CR₃. -/
theorem certifiedRankTYZClRk_of_literature (hT : TYZRow5b) (hW : RootNumberVanishing)
    (hG : GrossZagier) : RouteK.Rank.CertifiedRankTYZClRk := by
  intro d hd hsq h5b
  obtain ⟨F, hF, h1⟩ := analyticOrder_eq_one hT hW hd hsq h5b
  have hd0 : (d : ℚ) ≠ 0 := by exact_mod_cast (show d ≠ 0 by omega)
  exact hG _ (shortCurve_isElliptic (neg_ne_zero.mpr (pow_ne_zero 2 hd0))) F hF h1

/-! ### Reading A of TYZ Theorem 3.5(2) for `n ≡ 5 (mod 8)` (both rows), and Hecke -/

/-- The condition of `T_5a(d)`: exactly one block `≡ 5`, all other blocks `≡ 1 (mod 8)`. -/
def Admissible5aNat (d : ℕ) (P : Finpartition (Finset.univ : Finset d.primeFactors)) : Prop :=
  (P.parts.filter fun B => dProd B % 8 = 5).card = 1 ∧
  ∀ B ∈ P.parts, dProd B % 8 = 5 ∨ dProd B % 8 = 1

instance (d : ℕ) (P : Finpartition (Finset.univ : Finset d.primeFactors)) :
    Decidable (Admissible5aNat d P) := by
  unfold Admissible5aNat; infer_instance

/-- TYZ's first sum for `n ≡ 5`: `T_5a(d) = Σ_{d₀ ≡ 5} g(d₀) 𝓛₁(d/d₀)` with `g = #2Cl`. -/
noncomputable def T5aCl (d : ℕ) : ZMod 2 :=
  ∑ P : Finpartition (Finset.univ : Finset d.primeFactors),
    if Admissible5aNat d P then ∏ B ∈ P.parts, ((gCl (dProd B) : ℕ) : ZMod 2) else 0

/-- **Entire continuation of `L(C_d, s)`** (Deuring, Hecke: `C_d` has CM by `ℤ[i]`, so
`L(C_d, s)` is the L-function of a Hecke character of `ℚ(i)`). -/
def HeckeContinuation : Prop :=
  ∀ d : ℕ, d ≠ 0 → ∃ F : ℂ → ℂ, IsLContinuation (shortCurve (-(d : ℚ) ^ 2)) F

/-- **TYZ Theorem 3.5(2), `n ≡ 5 (mod 8)`, reading A, with `𝓛(n) = 0`**: if
`ord_{s=1} L(C_d, s) ≥ 2` then `T_5a(d)` and `T_5b(d)` are both even. (Only the case
`𝓛(n) = 0` of TYZ's hypothesis "`2^{−ρ(n)}𝓛(n)` even" is used; that case is covered without the
unproved "i.e." of their Theorem 3.5(2): nt-tyz §2.2 F6, §4.1.) -/
def TYZThm35ReadingA : Prop :=
  ∀ d : ℕ, d % 8 = 5 → Squarefree d → ∀ F : ℂ → ℂ,
    IsLContinuation (shortCurve (-(d : ℚ) ^ 2)) F → 2 ≤ analyticOrderAt F 1 →
      T5aCl d = 0 ∧ T5bCl d = 0

theorem two_le_of_not_le_one {x : ℕ∞} (h : ¬x ≤ 1) : 2 ≤ x := by
  have h1 : 1 < x := not_le.mp h
  have := Order.add_one_le_of_lt h1
  simpa [one_add_one_eq_two] using this

/-- Reading A (row 5b suffices) and Hecke's continuation give `TYZRow5b`. -/
theorem tyzRow5b_of_readingA (hA : TYZThm35ReadingA) (hH : HeckeContinuation) : TYZRow5b := by
  intro d hd hsq h5b
  obtain ⟨F, hF⟩ := hH d (by omega)
  refine ⟨F, hF, ?_⟩
  by_contra h
  have h0 := (hA d hd hsq F hF (two_le_of_not_le_one h)).2
  rw [h0] at h5b
  exact zero_ne_one h5b

/-! ### The functional equation with root number `−1` -/

/-- The completed L-function `Λ(s) = N^{s/2} (2π)^{−s} Γ(s) F(s)` for conductor `N`. -/
noncomputable def completedL (N : ℕ) (F : ℂ → ℂ) (s : ℂ) : ℂ :=
  (N : ℂ) ^ (s / 2) * (2 * Real.pi : ℂ) ^ (-s) * Complex.Gamma s * F s

/-- **Functional equation of `L(C_d, s)` for `d ≡ 5 (mod 8)`, on the strip `0 < Re s < 2`**:
`Λ(2 − s) = −Λ(s)` for `0 < Re s < 2`, with conductor `N = 32 d²`. Literature: Deuring (CM,
Hecke L-function of `ℚ(i)`) for the functional equation; conductor `32 d²` for odd squarefree
`d`; root number `−1` for `d ≡ 5, 6, 7 (mod 8)` (Birch–Stephens, Topology 5 (1966)).

Why the strip: Mathlib's `Complex.Gamma` takes the junk value `0` at `0, −1, −2, …`
(`Complex.Gamma_zero`, `Complex.Gamma_neg_nat_eq_zero`), whereas the true `Γ` has poles there.
For all `s` the identity would say at `s = 0` that `Λ(2) = −Λ(0) = 0`, that is `L(C_d, 2) = 0`,
which is false (`L(C_d, 2)` is a nonzero absolutely convergent Euler product). On
`0 < Re s < 2` both `Γ(s)` and `Γ(2 − s)` take their true values, so the Prop is a consequence
of the textbook functional equation; it is used only at `s = 1`. -/
def FunctionalEquation5 : Prop :=
  ∀ d : ℕ, d % 8 = 5 → Squarefree d → ∀ F : ℂ → ℂ,
    IsLContinuation (shortCurve (-(d : ℚ) ^ 2)) F →
      ∀ s : ℂ, 0 < s.re → s.re < 2 →
        completedL (32 * d ^ 2) F (2 - s) = -completedL (32 * d ^ 2) F s

/-- The functional equation at the centre `s = 1` gives `Λ(1) = 0`, hence `L(C_d, 1) = 0`. -/
theorem rootNumberVanishing_of_functionalEquation (h : FunctionalEquation5) :
    RootNumberVanishing := by
  intro d hd hsq F hF
  have h1 := h d hd hsq F hF 1 (by norm_num) (by norm_num)
  norm_num only at h1
  have h2 : completedL (32 * d ^ 2) F 1 = 0 := by linear_combination h1 / 2
  simp only [completedL, Complex.Gamma_one, mul_one] at h2
  have hN : ((32 * d ^ 2 : ℕ) : ℂ) ≠ 0 := by
    have : d ≠ 0 := by omega
    exact_mod_cast (by positivity : 32 * d ^ 2 ≠ 0)
  have hpi : (2 * Real.pi : ℂ) ≠ 0 := by
    exact_mod_cast (by positivity : (2 * Real.pi : ℝ) ≠ 0)
  rcases mul_eq_zero.mp h2 with h3 | h3
  · rcases mul_eq_zero.mp h3 with h4 | h4
    · exact absurd h4 (Complex.cpow_ne_zero_iff_of_exponent_ne_zero (by norm_num) |>.mpr hN)
    · exact absurd h4 (Complex.cpow_ne_zero_iff_of_exponent_ne_zero (by norm_num) |>.mpr hpi)
  · exact h3

end ZInQ.Literature
