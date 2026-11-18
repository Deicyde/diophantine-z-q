import ZInQKernel.Contrib.OneProof.SelmerTwoPower
import ZInQKernel.Contrib.PoleRC.CRM
import ZInQKernel.Contrib.PoleRC.LocalP
import ZInQKernel.Contrib.PoleRC.DescentM

/-!
# Lemma 5.4 of the manuscript and the leaves of Lemma 5.5 over genuine definitions, and the support bound

Fork issue #83, round 2 (task pc-s12), corrections (a), (b), (e) of the Theorem 5.3 design review.

* `IsModular`: modularity of `E/ℚ`, written fresh: the Dirichlet coefficients of Mathlib's
  `E.LFunction` are the `q`-expansion coefficients of a weight-2 cusp form on `Γ₀(N)`.
* `BCDTThmA` (printed leaf): every elliptic curve over `ℚ` is modular.
* `KolyvaginThm1` (consequence of Kolyvagin's Theorem 1, the `r = 1` case: Kolyvagin assumes a weak Weil
  parametrization, and `IsModular` gives one through Shimura's construction and Faltings' isogeny theorem):
  a modular elliptic curve with `ord_{s=1} L(E,s) = 1` has rank one and finite `Ш(E/ℚ)` (Tau Ceti's Ш,
  `SelmerTwoPower.sha`).
* `kolyvaginRankOne_of_printed`: round 1's `KolyvaginRankOne` from the two prints.
* `Lemma54` (a lemma of the manuscript, tex `lem:corank`, not a printed leaf: the manuscript proves it
  from the Kummer sequence and Cassels–Tate via Poonen–Stoll): full rational
  two-torsion and `#Sel₂(E/ℚ) = 8` give `corank_{ℤ₂} Sel_{2^∞}(E/ℚ) = 1`, over Tau Ceti's
  `Sel₂ = selmerAt E 1` and `SelmerTwoPower.SelmerCorankOne`.
* `KummerSelmerM` (textbook GLUE, proved by `PoleS12.kummerSelmerM` in
  `Contrib/OneProof/PoleCompletenessFromRCGenuineFinal.lean`, from `PoleRC.kummerSelmerM_proof`): for `E_ℓ`,
  the explicit system `SelM ℓ` has as many
  elements as the cohomological `Sel₂(E_ℓ/ℚ)` (the Kummer identification, Silverman X.1.4).
* `lemma54At_of_printed`: round 1's interface `Lemma54At SelmerCorankOne` from the two.
* `selM_finite` (correction (e), proved): `SelM ℓ` is finite, so `ncard = 8` is not vacuous.
-/

namespace ZInQ.Manuscript.PoleS12

open ZInQ.Manuscript.PoleRC ZInQ.Manuscript.SelmerTwoPower

/-! ### Lemma 5.5: modularity and Kolyvagin -/

/-- **`E/ℚ` is modular** (written fresh for this task): there are `N > 0` and a weight-2 cusp
form `f` on `Γ₀(N)` whose `q`-expansion coefficients are the Dirichlet coefficients of Mathlib's
`L`-function of `E` (`WeierstrassCurve.LFunction`, Euler product of the local factors of the
minimal model). Equality of the coefficients for all `n ≥ 1` is `L(E, s) = L(f, s)`. -/
def IsModular (E : WeierstrassCurve ℚ) : Prop :=
  ∃ (N : ℕ) (_ : 0 < N) (f : CuspForm (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) 2),
    ∀ n : ℕ, 0 < n → (UpperHalfPlane.qExpansion 1 f).coeff n = (E.LFunction n : ℂ)

/-- **Breuil–Conrad–Diamond–Taylor, Theorem A** (printed leaf; J. Amer. Math. Soc. 14 (2001)
843–939; the manuscript cites the author manuscript, `\cite[Theorem A]{bcdt}`, tex L1092):
every elliptic curve over `ℚ` is modular (Theorem A, p. 1 of the author manuscript). The print's
notion of "modular" is its Introduction's conditions (1)–(6) (p. 3); condition (2) says that
`L(E, s) = L(f, s)` for an eigenform `f` of weight 2 and level `N(E)`, on `Γ₁(N(E))` (cusp forms
p. 1, eigenforms p. 2). `IsModular` is a consequence of (2): trivial nebentypus takes `Γ₁(N(E))`
to `Γ₀(N(E))`, and equality of the Dirichlet series gives equality of the coefficients for every
`n ≥ 1`. Read (AI) on fork issue #83:
https://github.com/Deicyde/diophantine-z-q/issues/83#issuecomment-6962416523 -/
def BCDTThmA : Prop :=
  ∀ E : WeierstrassCurve ℚ, E.IsElliptic → IsModular E

/-- **Kolyvagin, Theorem 1, the case `r = 1`** (consequence of the print, not the printed statement; cited: "On the Mordell–Weil group
and the Shafarevich–Tate group of modular elliptic curves", MPIM preprint MPI/90-69 (1990),
Theorems 1–5, pp. 4–5; tex L1093, `\cite[Theorem 1, pp. 4–5]{kolyvagin}`; read (AI) on fork
issue #83: https://github.com/Deicyde/diophantine-z-q/issues/83#issuecomment-6962416523):
a modular elliptic curve `E/ℚ` with `ord_{s=1} L(E, s) = 1` has `rank E(ℚ) = 1` and finite
`Ш(E/ℚ)`. Theorem 1 (p. 4) assumes a weak Weil parametrization `X₀(N) → E` with `N` the conductor
(p. 3). `IsModular` is a weaker hypothesis, so this statement is a consequence of the print: it follows
from Kolyvagin's weak Weil parametrization hypothesis only through Shimura's construction (an abelian
variety quotient of `J₀(N)` attached to the newform) and Faltings' isogeny theorem (with trivial
nebentypus), the step BCDT cite
for (2) ⇒ (6) on p. 3 of their author manuscript. `Ш` is `SelmerTwoPower.sha` (Tau Ceti's Shafarevich–Tate group, local triviality at every
place). The print is a preprint, not a refereed paper (Known issue, round 1); its `r = 0` case is
not used. -/
def KolyvaginThm1 : Prop :=
  ∀ E : WeierstrassCurve ℚ, E.IsElliptic → IsModular E → AnalyticRankOne E →
    Module.rank ℤ E.toAffine.Point = 1 ∧ Finite (sha E)

/-- **Lemma 5.5 (`lem:forward-rank`), the rank half at `r = 1`, from the two prints.**
ON THE SPOT (correction (c)): only `rank = 1` is used downstream. Tex L1111–1113 uses "rank one
and finite Ш, hence Ш[2] = 0"; here, with `#E_ℓ(ℚ)[2] = 4`, Mordell–Weil and `#SelM ℓ = 8`, the
Kummer map is onto by counting (`descentGlueM`), which re-derives `r + dim Ш[2] = 1` without the
finiteness of Ш. -/
theorem kolyvaginRankOne_of_printed (hB : BCDTThmA) (hK : KolyvaginThm1) : KolyvaginRankOne :=
  fun E hE hA => (hK E hE (hB E hE) hA).1

/-! ### Lemma 5.4 over the genuine Selmer groups -/

/-- **Full rational two-torsion**: `#E(ℚ)[2] = 4`. -/
def FullTwoTorsion (E : WeierstrassCurve ℚ) : Prop :=
  Nat.card (nsmulAddMonoidHom 2 : E.toAffine.Point →+ _).ker = 4

/-- **Lemma 5.4 (`lem:corank`, tex L1072–1084), a lemma of the manuscript (not a printed leaf),
stated over genuine definitions.** For an
elliptic curve `E/ℚ` with full rational two-torsion, `dim_{𝔽₂} Sel₂(E/ℚ) = 3` (`#Sel₂ = 8`, with
`Sel₂ = selmerAt E 1`, Tau Ceti's 2-Selmer group with the conditions at every place) implies
`corank_{ℤ₂} Sel_{2^∞}(E/ℚ) = 1` (`SelmerTwoPower.SelmerCorankOne`). Provenance (b): the manuscript
proves it from the Kummer sequence and the Cassels–Tate pairing, citing Poonen–Stoll, Ann. of
Math. 150 (1999) 1109–1149 (`\cite{poonenstoll}`, tex L1081). It is a hypothesis here, a lemma that
the manuscript proves and not a published theorem; it is not proved in Lean. -/
def Lemma54 : Prop :=
  ∀ E : WeierstrassCurve ℚ, E.IsElliptic → FullTwoTorsion E →
    Nat.card (selmerAt E 1) = 8 → SelmerCorankOne E

/-- **The Kummer identification for `E_ℓ`** (textbook GLUE, proved: `PoleS12.kummerSelmerM`, with standard
axioms only; Silverman, *The
Arithmetic of Elliptic Curves*, 2nd ed., Prop. X.1.4, p. 315, as S12 L242 cites it): for positive
squarefree `ℓ`, the explicit 2-Selmer system `SelM ℓ` (pairs of squarefree integers whose class
is in the local Kummer image of `E_ℓ` in the coordinates `(x + 3ℓ, x − ℓ)` at `ℝ` and every
`ℚ_p`) has as many elements as the cohomological `Sel₂(E_ℓ/ℚ)`. It follows from the isomorphism
`H¹(K, E[2]) ≅ (K*/K*²)²` for a curve with full `K`-rational two-torsion, its compatibility with
restriction, and the description of the Kummer map; it is not a printed statement. Silverman is
in the manuscript's bibliography (`\bibitem{silverman}`, which names Chapters IV and VII only). -/
def KummerSelmerM : Prop :=
  ∀ ℓ : ℕ, 0 < ℓ → Squarefree ℓ → Nat.card (selmerAt (curve (ℓ : ℚ)) 1) = (SelM ℓ).ncard

/-- **Round 1's interface `Lemma54At` at the genuine predicate**, from Lemma 5.4 and the Kummer
identification. -/
theorem lemma54At_of_printed (h54 : Lemma54) (hKum : KummerSelmerM) :
    Lemma54At SelmerCorankOne := by
  intro ℓ hℓ hsf _ h8
  have hℓ0 : (ℓ : ℚ) ≠ 0 := by exact_mod_cast hℓ.ne'
  exact h54 _ (curve_isElliptic hℓ0) (card_ker_two_nsmul_eq_four_M hℓ0)
    ((hKum ℓ hℓ hsf).trans h8)

/-! ### The support bound (correction (e)) -/

theorem natAbs_dvd_of_primeFactors_subset {x : ℤ} {m : ℕ} (hx : Squarefree x) (hm : m ≠ 0)
    (h : x.natAbs.primeFactors ⊆ m.primeFactors) : x.natAbs ∣ m := by
  rw [← Nat.prod_primeFactors_of_squarefree (Int.squarefree_natAbs.mpr hx)]
  exact (Finset.prod_dvd_prod_of_subset _ _ _ h).trans (Nat.prod_primeFactors_dvd m)

/-- **The support bound** (correction (e)): a class `(a, b)` of `SelM ℓ` has `a, b` supported on
the primes of `6ℓ`: a prime `p ∤ 6ℓ` divides neither (`localGood_nec`, round 1). -/
theorem selM_support {ℓ : ℕ} (hℓ : 0 < ℓ) {a b : ℤ} (hab : (a, b) ∈ SelM ℓ) :
    a.natAbs ∣ 6 * ℓ ∧ b.natAbs ∣ 6 * ℓ := by
  obtain ⟨ha, hb, -, hp⟩ := hab
  simp only at ha hb hp
  have h6 : 6 * ℓ ≠ 0 := by omega
  have key : ∀ x : ℤ, Squarefree x → (∀ p : ℕ, p.Prime → ¬ p ∣ 6 * ℓ → ¬ (p : ℤ) ∣ x) →
      x.natAbs ∣ 6 * ℓ := by
    intro x hx hgood
    refine natAbs_dvd_of_primeFactors_subset hx h6 fun p hp' => ?_
    obtain ⟨hpp, hpd, -⟩ := Nat.mem_primeFactors.mp hp'
    refine Nat.mem_primeFactors.mpr ⟨hpp, by_contra fun hnd => hgood p hpp hnd ?_, h6⟩
    exact Int.natCast_dvd.mpr hpd
  refine ⟨key a ha fun p hpp hnd => ?_, key b hb fun p hpp hnd => ?_⟩
  · have := Fact.mk hpp
    exact (localGood_nec hnd ha hb (hp p)).1
  · have := Fact.mk hpp
    exact (localGood_nec hnd ha hb (hp p)).2

/-- **`SelM ℓ` is finite** (correction (e)): so `(SelM ℓ).ncard = 8` is a genuine count. -/
theorem selM_finite {ℓ : ℕ} (hℓ : 0 < ℓ) : (SelM ℓ).Finite := by
  refine ((Set.finite_Icc (-(6 * ℓ : ℤ)) (6 * ℓ)).prod
    (Set.finite_Icc (-(6 * ℓ : ℤ)) (6 * ℓ))).subset fun ab hab => ?_
  obtain ⟨h1, h2⟩ := selM_support hℓ hab
  have hb1 := Nat.le_of_dvd (by omega) h1
  have hb2 := Nat.le_of_dvd (by omega) h2
  simp only [Set.mem_prod, Set.mem_Icc]
  omega

end ZInQ.Manuscript.PoleS12
