import Mathlib.AlgebraicGeometry.EllipticCurve.LFunction
import Mathlib.Analysis.Analytic.Order
import Mathlib.Analysis.Analytic.Uniqueness
import Mathlib.Analysis.Complex.CauchyIntegral
import ZInQKernel.RouteK.Rank.Statements

/-!
# wk-cr3 draft: CR₃ from three literature statements

Draft for `docs/research/wk-cr3.md` §4. The L-series is Mathlib's `WeierstrassCurve.LSeries`
(Euler product of the local factors of the minimal model; arithmetic normalization, centre
`s = 1`, absolute convergence for `Re s > 3/2` by Hasse's bound). "The order of vanishing of
`L(E, s)` at `s = 1`" is `analyticOrderAt F 1` for an entire function `F` that agrees with the
series on `Re s > 3/2`; such an `F` is unique (`IsLContinuation.eq`).
-/

namespace ZInQ.WkCR3

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
  exact (Complex.analyticOnNhd_univ_iff_differentiable.mpr hF.1).eqOn_of_preconnected_of_eventuallyEq
    (Complex.analyticOnNhd_univ_iff_differentiable.mpr hG.1) isPreconnected_univ (Set.mem_univ 2) hev
    (Set.mem_univ z)

/-- **Gross–Zagier–Kolyvagin** (positive-rank half, for every elliptic curve over `ℚ`). If `L(E, s)`
has a simple zero at `s = 1`, then `E(ℚ)` has a point of infinite order.

Literature: B. Gross, D. Zagier, Invent. Math. 84 (1986), 225–320 (Heegner point of infinite order
when `L'(E/K, 1) ≠ 0`); an auxiliary imaginary quadratic `K` with the Heegner hypothesis and
`L(E^K, 1) ≠ 0` (Bump–Friedberg–Hoffstein, Invent. Math. 102 (1990); Murty–Murty, Ann. of Math.
133 (1991)); modularity of `E` (Breuil–Conrad–Diamond–Taylor, J. AMS 14 (2001); for CM curves
Shimura 1971). Kolyvagin (Math. USSR Izv. 32 (1989)) adds `rank = 1`, not used. -/
def GrossZagierKolyvagin : Prop :=
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

Literature: TYZ, Asian J. Math. 21 (2017), Theorem 3.5(2) for `n ≡ 5 (mod 8)` in reading A
(`d₁ = 1` admitted; `docs/research/nt-tyz.md` §1.3), contrapositive, row `(7, 3)` only; the
existence of the continuation is Hecke's (CM). Not a literal published sentence: reading A is
stated in print only by Smith (arXiv:1603.08479, Theorem 2.1, unrefereed), and is proved from
unambiguous TYZ statements by Proposition N (nt-tyz §4). -/
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
    (hG : GrossZagierKolyvagin) : RouteK.Rank.CertifiedRankTYZClRk := by
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

/-- **Entire continuation of `L(C_d, s)`** (Deuring, Hecke: `C_d` has CM by `ℤ[i]`, so `L(C_d, s)` is
the L-function of a Hecke character of `ℚ(i)`). -/
def HeckeContinuation : Prop :=
  ∀ d : ℕ, d ≠ 0 → ∃ F : ℂ → ℂ, IsLContinuation (shortCurve (-(d : ℚ) ^ 2)) F

/-- **TYZ Theorem 3.5(2), `n ≡ 5 (mod 8)`, reading A, with `𝓛(n) = 0`**: if `ord_{s=1} L(C_d, s) ≥ 2`
then `T_5a(d)` and `T_5b(d)` are both even. (TYZ's hypothesis "`2^{−ρ(n)}𝓛(n)` even" is weakened
to `𝓛(n) = 0`; nt-tyz §2.2 F6, §4.1.) -/
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

end ZInQ.WkCR3

#print axioms ZInQ.WkCR3.IsLContinuation.eq
#print axioms ZInQ.WkCR3.certifiedRankTYZClRk_of_literature
#print axioms ZInQ.WkCR3.tyzRow5b_of_readingA
