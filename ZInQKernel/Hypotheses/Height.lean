import Mathlib

/-!
# Hypothesis H: the six-contact height estimate

`SixContactEstimate` is Theorem 4.1 (`thm:height`) of the frozen 11/5 manuscript
`diophantine_zq.tex` (sha256 `cb1148cd…`), with the manuscript's numerals. The statement
concerns only rational numbers, but its proof needs Shimura curves, modularity and Arakelov
geometry, none of which is in Mathlib. It therefore enters the main theorems as an explicit
hypothesis, through its one used instance `SixContactMin` (`Hypotheses/HeightMin.lean`).

## Trust statement

The proof uses no unpublished upstream proof supplement. `docs/research/h-trust.md` §1 lists
every step with its supplier and status (review: `docs/research/rv-h-trust.md`). It rests
principally on the following.

* **Refereed theorems.**
  - The discriminant-six Shimura curve: its canonical model and moduli interpretation (Shimura
    1967; Deligne 1971, 1979; Kottwitz 1992), its branch data and Igusa coordinates
    (Baba–Granath 2008; Lin–Yang 2020; Igusa 1967; Lauter–Naehrig–Yang 2015), and its CM points
    (González–Rotger 2006).
  - Abelian varieties: Mumford's book (1970) with GAGA, Skolem–Noether, and the Brauer group of `ℚ`
    (Milne's *Arithmetic duality theorems*; Tate in Cassels–Fröhlich).
  - Reduction: tame specialization (SGA 1, Exp. X, XIII), semistable reduction (SGA 7, Exp. IX),
    and Néron–Ogg–Shafarevich (Serre–Tate 1968).
  - Galois representations: Faltings' finiteness theorems (1983); Scholze's de Rham comparison
    (2013, with its 2016 corrigendum); Berger's p-adic monodromy theorem (2002); Pan's
    Fontaine–Mazur theorem (J. Amer. Math. Soc. 35 (2022), Theorem 1.0.4 of
    arXiv:1901.07166v2); the p-adic Hodge theory of modular forms, in the Tate-module
    (arithmetic-Frobenius) normalization with weights `{0, 1−k}`, at every level including
    levels divisible by 5 (Saito 1997, Scholl 1990 with Scholze 2013, or Kato 2004), and
    Deligne–Serre 1974 for weight one; Li 1975, Shimura 1973 and the Eichler–Shimura relation
    (Shimura 1971) for newforms and `A_f`; Carayol's local–global compatibility (1986,
    Théorème A).
  - Local fields: local class field theory and ramification (Serre), and Raynaud's criterion
    (Silverberg–Zarhin 1995).
  - Heights: Javanpeykar 2014, the isogeny theorem of Gaudron–Rémond (2014, Theorem 1.4),
    Faltings' height variation, and Pazuki 2012.
  - Four citations of the manuscript to lecture notes or preprints are replaced by refereed
    editions (`docs/research/h-trust.md` §2.4).
* **Manuscript arguments reviewed by models only, never by a human referee.**
  - The scalar descent, the uniform conductor bound `N ≤ Q_R M²` and the transfer from
    `J₁(N)`: `docs/research/rv-h-novel.md`, plus four scoped Astra reviews of the 11/4 text
    (`docs/reviews/height-replacement/`).
  - The geometric bookkeeping: the level-three degree and the conjugates, the Hom field and the
    endomorphism dichotomy (Astra "whole").
  - Oddness (Astra "descent", on the 11/4 text), and the twist and weight argument (Astra
    "descent" on the 11/4 text and `docs/research/rv-h-c8.md` on the 11/5 text).
  - The theta-height comparison and the return to `u` (Astra "height").
  - The application of Pan's theorem: Astra "descent" and "whole" on the manuscript's text, and
    `docs/research/rv-h-a011.md`.
  - Three passages are new in the 11/5 text, and each has two independent model reviews: the
    de Rham descent lemma (`lem:de-rham-descent`; `docs/research/rv-h-trust.md` and
    `docs/research/rv-h-c3.md`), and the paragraph on Hodge endomorphisms in the dichotomy and
    the Li–Shimura sentence on the newform (`rv-h-trust.md` and `docs/research/rv-h-a9c9.md`).
* **Repository arguments that replace manuscript text.**
  - The CM branch is empty for rational `u` (`docs/research/h-cm.md`; model review
    `rv-h-cm.md`).
  - The fibre field is unramified outside `S ∪ supp M_S(u)`, and the fibre surface has good
    reduction away from 3. Both come from tame specialization and a vertical-ramification
    lemma, with no integral model of the Shimura curve (`docs/research/h-b1.md`, Lemma PR;
    model review `docs/research/rv-h-b1.md`: holds, and its repairs are bookkeeping). It uses
    the canonical model of the level-three curve as the PEL moduli scheme over `ℚ`, with one
    `ℚ`-structure for the vertical-ramification lemma, the good-reduction step and
    Baba–Granath's `j` (h-b1 §4A).
* **Exact computations** in `scratch/`, each with its saved output: the polarization form, the
  Igusa normalization, the ramification case analysis, the branch values and the constants.

None of the replacements changes the constant `H₆` or the exponent 24. Published locators
that could not be read when the trust statement was written are listed in
`docs/research/h-trust.md` §2.5; those read by a model only are marked ASTRA-READ there.
-/

namespace ZInQ

open scoped BigOperators

/-- The logarithmic height `h(a/b) = log max(|a|, b)` of a rational number in lowest terms. -/
noncomputable def ratHeight (u : ℚ) : ℝ :=
  Real.log (max |(u.num : ℝ)| (u.den : ℝ))

/-- The six contact values `𝒞 = {0, -15, -20, -24, -30, -60}`. -/
def contactSet : Finset ℚ := {0, -15, -20, -24, -30, -60}

open Classical in
/-- `M_S(u)`: the product of the primes `p ∉ S` at which `v_p(u - c)` is positive and odd for
some contact value `c`. Negative valuations of `u` do not contribute. -/
noncomputable def contactSupport (S : Finset ℕ) (u : ℚ) : ℕ :=
  ∏ p ∈ (∏ c ∈ contactSet, (u - c).num.natAbs).primeFactors with
      p ∉ S ∧ ∃ c ∈ contactSet, 0 < padicValRat p (u - c) ∧ Odd (padicValRat p (u - c)),
    p

/-- A positive `p`-adic valuation of a rational number comes from its numerator. -/
theorem dvd_num_natAbs_of_padicValRat_pos {p : ℕ} {q : ℚ} (h : 0 < padicValRat p q) :
    p ∣ q.num.natAbs := by
  rw [padicValRat_def] at h
  have h1 : padicValInt p q.num ≠ 0 := by omega
  exact padicValNat.dvd_of_ne_zero h1

/-- `contactSupport S u` is the manuscript's `M_S(u)`: a product of distinct primes, and a
prime divides it exactly when it lies outside `S` and has positive odd valuation in some
`u - c`. -/
theorem prime_dvd_contactSupport_iff {S : Finset ℕ} {u : ℚ} (hu : u ∉ contactSet) {p : ℕ}
    (hp : p.Prime) :
    p ∣ contactSupport S u ↔
      p ∉ S ∧ ∃ c ∈ contactSet, 0 < padicValRat p (u - c) ∧ Odd (padicValRat p (u - c)) := by
  classical
  have hn : (∏ c ∈ contactSet, (u - c).num.natAbs) ≠ 0 := by
    rw [Finset.prod_ne_zero_iff]
    intro c hc
    rw [Int.natAbs_ne_zero, Rat.num_ne_zero, sub_ne_zero]
    rintro rfl
    exact hu hc
  unfold contactSupport
  rw [Prime.dvd_finsetProd_iff hp.prime]
  constructor
  · rintro ⟨a, ha, hpa⟩
    rw [Finset.mem_filter] at ha
    rw [Nat.prime_dvd_prime_iff_eq hp (Nat.prime_of_mem_primeFactors ha.1)] at hpa
    subst hpa
    convert ha.2 using 0
  · rintro ⟨hS, c, hc, hpos, hodd⟩
    refine ⟨p, ?_, dvd_rfl⟩
    rw [Finset.mem_filter, Nat.mem_primeFactors]
    exact ⟨⟨hp, (dvd_num_natAbs_of_padicValRat_pos hpos).trans (Finset.dvd_prod_of_mem _ hc), hn⟩,
      hS, c, hc, hpos, hodd⟩

/-- `F₀ = 324!`. -/
noncomputable def heightF0 : ℕ := Nat.factorial 324

/-- `D = F₀ · 3^(256 F₀⁴)`. -/
noncomputable def heightD : ℕ := heightF0 * 3 ^ (256 * heightF0 ^ 4)

/-- `G₀ = 116064000000`. -/
def heightG0 : ℕ := 116064000000

/-- `E₀ = 10 (D G₀)²`. -/
noncomputable def heightE0 : ℕ := 10 * (heightD * heightG0) ^ 2

/-- `B_cm = D² 3^(21000 D²) + 1`. -/
noncomputable def heightBcm : ℕ := heightD ^ 2 * 3 ^ (21000 * heightD ^ 2) + 1

/-- `C_cm = 2 B_cm + 4096 (1028 + 5 D + 84000 D²)`. -/
noncomputable def heightCcm : ℕ := 2 * heightBcm + 4096 * (1028 + 5 * heightD + 84000 * heightD ^ 2)

/-- `Q_R = R^(R E₀)`. -/
noncomputable def heightQ (R : ℝ) : ℝ := R ^ (R * heightE0)

/-- `H₆(S; R) = 2·10¹³ · max(1, C_cm, Q_R¹⁷)`. It depends on `S` only through the
admissible range of `R`. -/
noncomputable def heightH6 (R : ℝ) : ℝ :=
  2 * 10 ^ 13 * max 1 (max (heightCcm : ℝ) (heightQ R ^ 17))

/-- **Hypothesis H** (Theorem 4.1, the six-contact estimate). For every finite set `S` of
primes containing all primes at most `324`, every `R ≥ max(D, max S, 10¹²)` and every
`u ∈ ℚ \ 𝒞`, `h(u) ≤ H₆(S; R) M_S(u)²⁴`.

Not proved in Lean. Its proof rests on refereed theorems, together with manuscript and
repository arguments that have been reviewed by models but not refereed, and uses no
unpublished upstream proof supplement. See the module docstring and
`docs/research/h-trust.md`. The main theorems use only the instance `SixContactMin`. -/
def SixContactEstimate : Prop :=
  ∀ S : Finset ℕ, (∀ p ∈ S, p.Prime) → (∀ p : ℕ, p.Prime → p ≤ 324 → p ∈ S) →
    ∀ R : ℝ, (heightD : ℝ) ≤ R → (∀ p ∈ S, (p : ℝ) ≤ R) → (10 : ℝ) ^ 12 ≤ R →
      ∀ u : ℚ, u ∉ contactSet → ratHeight u ≤ heightH6 R * (contactSupport S u : ℝ) ^ 24

end ZInQ
