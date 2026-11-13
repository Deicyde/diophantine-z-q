import ZInQKernel.Contrib.PSide.TYZInputsIff
import ZInQKernel.Contrib.HeckeAll.Provider

/-!
# tyz-decomp: `TYZThm35ReadingA` as literature leaves plus glue

Report: `docs/research/tyz-decomp.md`. Results log: `scratch/tyz-decomp/log.md`.

Tian–Yuan–Zhang (TYZ), *Genus periods, genus points and congruent number problem*,
arXiv:1411.4728v1 (the only arXiv version), Asian J. Math. 21 (2017), 721–774 (refereed). Line
numbers `Lnnnn` refer to the arXiv source `Period7.tex`; they are quoted from
`docs/research/nt-tyz.md`, `pn-design.md`, `rv-nt-tyz.md`, `rv-tyz-inputs.md`, where earlier tasks
read them in the source. The source is not on this host, so no locator was re-read by this task.

Layout.
* §1. The three readings A, B, C of TYZ Theorem 3.5(2) for `n ≡ 5 (mod 8)` in its case
  `𝓛(n) = 0`, over genuine definitions; reading A in its literal two-sum form is
  `TYZThm35ReadingA` (`readingA_iff`). B, C (and A′) are false (nt-tyz §1.4, exact computation at
  `n = 26565`); `not_readingB_of` records the shape of the refutation.
* §2. TYZ's `𝓛` pinned by genuine definitions: on the classes `1, 3 (mod 8)` by the value at `s = 1`
  of the continuation of `L(C_m, s)` and the explicit period `Ω_m` (TYZ L338–353), on the class
  `5` by its zero set (TYZ L338–345). The leaves `TYZThm11Integral`, `TYZLcalOne`,
  `TYZLemma29Mod2` (alternatively `TYZThm11Mod2`) are stated over these definitions.
* §3. The genus-point package of TYZ §3 (`TYZGenusPackage`), over the pinned `𝓛` and the abstract
  `PropN.GenusData`. It is the one leaf that cannot be split over Mathlib's definitions (no
  modular parametrization of `X₀(32)`, no CM points, no ring class fields).
* §4. Glue (proved): the leaves give `PropN.TYZInputs` and hence `TYZThm35ReadingA`; and given the
  §2 leaves, `TYZGenusPackage ↔ TYZThm35ReadingA` (Hecke's continuation is a theorem of the fork,
  `ZInQ.Contrib.heckeContinuation`).

No `sorry`, no `axiom`.
-/

noncomputable section

namespace ZInQ.Contrib.TYZDecomp

open ZInQ.Literature ZInQ.PropN ZInQ.RouteK.Rank5b ZInQ.Contrib.PSide

/-- `C_n : y² = x³ − n²x` over `ℚ` (TYZ's `E_n : ny² = x³ − x` is `ℚ`-isomorphic to it by
`(x, y) ↦ (nx, n²y)`, rv-prop-n §1). -/
abbrev curveC (n : ℕ) : WeierstrassCurve ℚ := shortCurve (-(n : ℚ) ^ 2)

/-! ## §1. The readings of TYZ Theorem 3.5(2) for `n ≡ 5 (mod 8)`, case `𝓛(n) = 0`

TYZ Theorem 3.5(2) (L1353–1374; journal p. 740 per `locators.md`, not re-read): if
`2^{−ρ(n)}𝓛(n)` is even and `n ≡ 5, 7 (mod 8)`, then the two sums of Theorem 1.2 vanish mod 2.
For `n ≡ 5` the first sum is `T_5a(n)` under every reading, and the second sum is
`S₅₁(n) + T_5b(n)`, where the `(d₀, d₁) ≡ (5, 1)` part `S₅₁(n)` depends on the reading
(nt-tyz §1.3): A (`d₁ = 1` admitted): `S₅₁ = T_5a`; B (all `d_i > 1`, non-ordered): the
partitions with at least one class-1 block; C (`d₁ > 1` distinguished): each partition counted
once per class-1 block. The case `𝓛(n) = 0` of the hypothesis is the case `ord_{s=1} ≥ 2`
(definition of `𝓛`, L338–345), and in it the "i.e." of Theorem 3.5(2) is not needed (nt-tyz §2.2
F6). -/

/-- Reading B of the `(5, 1)` part of the second sum: set partitions of the primes of `n` with one
block `≡ 5`, all others `≡ 1 (mod 8)`, and at least two blocks. -/
def S51B (n : ℕ) : ZMod 2 :=
  ∑ P : Finpartition (Finset.univ : Finset n.primeFactors),
    if Admissible5aNat n P ∧ 2 ≤ P.parts.card then
      ∏ B ∈ P.parts, ((gCl (dProd B) : ℕ) : ZMod 2) else 0

/-- Reading C of the `(5, 1)` part: each admissible partition weighted by its number of class-1
blocks (the choices of the distinguished factor `d₁ > 1`). -/
def S51C (n : ℕ) : ZMod 2 :=
  ∑ P : Finpartition (Finset.univ : Finset n.primeFactors),
    if Admissible5aNat n P then
      ((P.parts.card - 1 : ℕ) : ZMod 2) * ∏ B ∈ P.parts, ((gCl (dProd B) : ℕ) : ZMod 2) else 0

/-- **TYZ Theorem 3.5(2), `n ≡ 5 (mod 8)`, case `ord_{s=1} L(C_n, s) ≥ 2`, literal two-sum form**,
with the `(5, 1)` part `S51` of the second sum left as a parameter (the reading). -/
def Thm35Reading (S51 : ℕ → ZMod 2) : Prop :=
  ∀ d : ℕ, d % 8 = 5 → Squarefree d → ∀ F : ℂ → ℂ,
    IsLContinuation (curveC d) F → 2 ≤ analyticOrderAt F 1 →
      T5aCl d = 0 ∧ S51 d + T5bCl d = 0

/-- Reading A (`d₁ = 1` admitted; the reading the route needs). -/
abbrev Thm35ReadingA : Prop := Thm35Reading T5aCl
/-- Reading B (all `d_i > 1`, non-ordered; the literal sentence of arXiv Theorem 1.2 = journal
Theorem 1.4). False: nt-tyz §1.4. -/
abbrev Thm35ReadingB : Prop := Thm35Reading S51B
/-- Reading C (`d₁ > 1` distinguished). False: nt-tyz §1.4. -/
abbrev Thm35ReadingC : Prop := Thm35Reading S51C

/-- Reading A′ (found in this task's review, not in nt-tyz): `d₁ = 1` admitted *and* `d₁`
distinguished, so a partition with `k` class-1 blocks is counted `k + 1` times
(`d₁ = 1` or `d₁` one of the blocks). Its `(5, 1)` part is `T_5a + S₅₁^C`. False by the same
computation as C (at `n = 26565`, `T_5a = 0`, `S₅₁^C = 1`). -/
abbrev Thm35ReadingA' : Prop := Thm35Reading fun n => T5aCl n + S51C n

/-- **Reading A in its literal two-sum form is the premise `TYZThm35ReadingA`.** -/
theorem readingA_iff : Thm35ReadingA ↔ TYZThm35ReadingA := by
  constructor
  · intro h d hd hsq F hF h2
    obtain ⟨h1, h2'⟩ := h d hd hsq F hF h2
    rw [h1, zero_add] at h2'
    exact ⟨h1, h2'⟩
  · intro h d hd hsq F hF h2
    obtain ⟨h1, h2'⟩ := h d hd hsq F hF h2
    exact ⟨h1, by rw [h1, h2', add_zero]⟩

/-- The shape of the refutation of a reading (nt-tyz §1.4): one `n ≡ 5` with `ord ≥ 2`,
`T_5a(n) = T_5b(n) = 0` and odd `S₅₁(n)` refutes it. At `n = 26565 = 3·5·7·11·23` (and
`n = 33117`) this holds for B and C: `rank C_n(ℚ) = 3` (three explicit points, Kummer images of
dimension 5), hence `ord ≥ 2` by Gross–Zagier–Kolyvagin; `T_5a = T_5b = 0` and
`S51B = S51C = 1` with certified class groups (VERIFIED by nt-tyz, `scratch/nt-tyz/`; not
re-run here). -/
theorem not_reading_of {S51 : ℕ → ZMod 2} {n : ℕ} (hn : n % 8 = 5) (hsq : Squarefree n)
    {F : ℂ → ℂ} (hF : IsLContinuation (curveC n) F) (h2 : 2 ≤ analyticOrderAt F 1)
    (hb : T5bCl n = 0) (hS : S51 n = 1) : ¬ Thm35Reading S51 := by
  intro h
  have := (h n hn hsq F hF h2).2
  rw [hb, hS, add_zero] at this
  exact one_ne_zero this

/-! ## §2. TYZ's `𝓛` over genuine definitions -/

/-- `∫₁^∞ dx / √(x³ − x)` (the real period of `y² = x³ − x` is twice it). -/
def omegaInt : ℝ := ∫ x in Set.Ioi (1 : ℝ), 1 / Real.sqrt (x ^ 3 - x)

/-- TYZ's period `Ω_m = Ω_{m,∞} = (2/√m) ∫₁^∞ dx/√(x³ − x)` of `E_m : my² = x³ − x`
(TYZ L338–353, as transcribed in `scratch/rv-tyz-inputs/tyzcalc.py`; not re-read here). -/
def omegaTYZ (m : ℕ) : ℝ := 2 / Real.sqrt m * omegaInt

open Classical in
/-- `L(C_m, 1)`: the value at `s = 1` of the entire continuation of Mathlib's `L(C_m, s)`
(junk `0` if there is none; there always is, `ZInQ.Contrib.heckeContinuation`). The continuation
is unique (`IsLContinuation.eq`), so the value is pinned (`lValOne_eq`). -/
def lValOne (m : ℕ) : ℂ :=
  if h : ∃ F : ℂ → ℂ, IsLContinuation (curveC m) F then h.choose 1 else 0

set_option linter.deprecated false in
theorem lValOne_eq {m : ℕ} {F : ℂ → ℂ} (hF : IsLContinuation (curveC m) F) :
    lValOne m = F 1 := by
  have h : ∃ F : ℂ → ℂ, IsLContinuation (curveC m) F := ⟨F, hF⟩
  rw [lValOne, dif_pos h, h.choose_spec.eq hF]

/-- **TYZ's `𝓛(m)²` for odd squarefree `m ≡ 1, 3 (mod 8)`** (TYZ L338–353, transcribed in
`scratch/rv-tyz-inputs/tyzcalc.py`, and VERIFIED numerically there on about 200 values to be the
square of an integer; `scratch/rv-nt-tyz/calL_small.py`: value `1` at `m = 1, 3, 11, 19, 33`):
`𝓛(m)² = L(E_m, 1) / (2^{2k(m)−3} Ω_m)`, `k(m)` the number of prime factors of `m`
(TYZ's `2^{2k−2−a}` with `a(m) = 1` for odd `m`). For `m ≡ 1, 3` the root number is `+1`, so this
covers both `ord_{s=1} = 0` and `ord ≥ 2` (value `0`). -/
def lcalSq (m : ℕ) : ℂ :=
  lValOne m / ((2 : ℂ) ^ ((2 * m.primeFactors.card : ℤ) - 3) * (omegaTYZ m : ℂ))

/-- **`ℓ` is (a sign choice of) TYZ's `𝓛`** on the squarefree arguments of classes `1, 3, 5`:
`ℓ 1 = 1` (L1082); `ℓ(m)² = 𝓛(m)²` on classes `1, 3`; and on class `5` the zero set of TYZ's `𝓛`
(L338–345: `𝓛(n) = 0` iff `ord_{s=1} L(E_n, s) > 1`; the order is `≥ 1` by the root number, and
in the order-one case `𝓛(n)² = L′/(2^{2k−3}Ω_n R_n) ≠ 0`, `R_n ≠ 0` by Gross–Zagier–Kolyvagin).
On class `5` only the zero set is pinned; that is all that the route reads. -/
def IsTYZLcal (ℓ : ℕ → ℤ) : Prop :=
  ℓ 1 = 1 ∧
  (∀ m : ℕ, Squarefree m → (m % 8 = 1 ∨ m % 8 = 3) → ((ℓ m : ℂ)) ^ 2 = lcalSq m) ∧
  (∀ n : ℕ, Squarefree n → n % 8 = 5 →
    (ℓ n = 0 ↔ ¬ ∃ F : ℂ → ℂ, IsLContinuation (curveC n) F ∧ analyticOrderAt F 1 ≤ 1))

/-- **Leaf TYZ-1.1a (TYZ Theorem 1.1, first assertion, odd case)**: for odd squarefree
`m ≡ 1, 3 (mod 8)`, `𝓛(m)` is an integer. TYZ Theorem 1.1 (L371–380, for `n ≡ 1, 2, 3`) and
Theorem 3.5(1); refereed (journal number of Theorem 1.1 UNVERIFIED: §1 was renumbered). -/
def TYZThm11Integral : Prop :=
  ∀ m : ℕ, Squarefree m → (m % 8 = 1 ∨ m % 8 = 3) → ∃ ℓ : ℤ, (ℓ : ℂ) ^ 2 = lcalSq m

/-- **Leaf TYZ-L1 (`𝓛(1) = 1`)**: `L(E₁, 1) = Ω₁/8 = ¼ ∫₁^∞ dx/√(x³−x)`. TYZ L1082 ("Since
`𝓛(1) = 1`", asserted); the classical value of `L(E, 1)` for `y² = x³ − x` (BSD for the conductor-32
CM curve: Coates–Wiles, Rubin; or a direct evaluation of the Hecke L-value; exact textbook locator
UNVERIFIED). Numerically VERIFIED to 10 digits (`scratch/rv-nt-tyz/calL_small.py`). -/
def TYZLcalOne : Prop := lcalSq 1 = 1

/-- **Leaf TYZ-2.9 (TYZ Lemma 2.9 with Proposition 2.3, modulo 2)**, for every sign choice `ℓ` of
`𝓛` on the classes `1, 3`: the congruence `PropN.LemmaTwoEight ℓ`, i.e.
`Σ_{m = d₁d₂ non-ordered, d₂ ≡ 1} 𝓛(d₁)𝓛(d₂) ≡ g(m) (mod 2)` for squarefree `m ≡ 1, 3`
(L1062–1066, L580–586; the signs `ε` and the odd factor `w_K` (rv-nt-tyz B1) vanish mod 2).
Refereed; Lemma 2.9 has the same number in the journal per `locators.md`. -/
def TYZLemma29Mod2 : Prop :=
  ∀ ℓ : ℕ → ℤ, (∀ m : ℕ, Squarefree m → (m % 8 = 1 ∨ m % 8 = 3) → ((ℓ m : ℂ)) ^ 2 = lcalSq m) →
    LemmaTwoEight ℓ

/-- **Alternative leaf TYZ-1.1b (TYZ Theorem 1.1, congruence, set-partition reading)**:
`𝓛(m) ≡ Λ(m) (mod 2)` for squarefree `m ≡ 1, 3`. The printed sentence ("non-ordered with
`d_i > 1`") is read as set partitions; Lemma N1 (nt-tyz §4.3) shows that Lemma 2.9 forces this
reading. Either this leaf or `TYZLemma29Mod2` suffices (`lemma29Mod2_of_thm11Mod2`). -/
def TYZThm11Mod2 : Prop :=
  ∀ ℓ : ℕ → ℤ, (∀ m : ℕ, Squarefree m → (m % 8 = 1 ∨ m % 8 = 3) → ((ℓ m : ℂ)) ^ 2 = lcalSq m) →
    ∀ m : ℕ, Squarefree m → (m % 8 = 1 ∨ m % 8 = 3) → ((ℓ m : ℤ) : ZMod 2) = Lam m

/-! ## §3. The genus-point package of TYZ §3 -/

/-- **Leaf TYZ-§3 (the genus-point package)**: for every sign choice `ℓ` of TYZ's `𝓛` and every
squarefree `n ≡ 5 (mod 8)`, the genus-point data `PropN.GenusData ℓ n` exist. Its fields are, in
TYZ: the recursion defining `P` (§3.1, L1325–1330) with the `ε`-classes of Theorem 3.3
(L1299–1311); Theorem 3.5, first assertion (L1353–1356, with `𝒫(n) = 0` if `𝓛(n) = 0`, L1295);
the uniformization `τ` (L1385–1402); Lemma 3.16 (L2182–2185) and Lemma 3.18 (L2230–2232); one
lifting `β'` of `β₁ = r_∞(−1)r₂(−2)` (L2496–2500), fixing `ℚ(i)` (L2581), and Lemma 3.21(1), (4)
(L2504–2516); plus F4 (`[i]` is defined over `ℚ(i)`), standard and unprinted, for the typing of
`β` (see `PropN.GenusData`). Field-by-field justification: `pn-design.md` §2,
`rv-tyz-inputs.md`, `rv-pn-encoding.md` (AI reviews).

The objects of the package (`A(ℍ'_n)`, the genus points `Z(e)`, the points `P(e)`, `β'`) are
existential and are not pinned by genuine definitions: Mathlib has no modular parametrization
`X₀(32) → A`, no CM points and no ring class fields. So the package is one bundled leaf; split
into separate leaves, its clauses would not talk about the same objects. Given the §2 leaves it is
equivalent to `TYZThm35ReadingA` (`genusPackage_iff_readingA`). Universal over `ℓ`: a sign change
of `ℓ(d₁)` is absorbed into `ε(d₀, d₁)` (classes `±1`, `±i` are sign-stable), and `GenusData` reads
`ℓ` only at classes `1, 3` (recursion) and at `n` (zero test), which `IsTYZLcal` pins. -/
def TYZGenusPackage : Prop :=
  ∀ ℓ : ℕ → ℤ, IsTYZLcal ℓ → ∀ n : ℕ, n % 8 = 5 → Squarefree n → Nonempty (GenusData ℓ n)

/-! ## §4. Glue -/

open Classical in
/-- A sign choice of TYZ's `𝓛` (class `5`: `1` or `0` by the zero set). -/
def lcalChoice (h11 : TYZThm11Integral) : ℕ → ℤ := fun m =>
  if m = 1 then 1
  else if hm : Squarefree m ∧ (m % 8 = 1 ∨ m % 8 = 3) then (h11 m hm.1 hm.2).choose
  else if Squarefree m ∧ m % 8 = 5 ∧
      ∃ F : ℂ → ℂ, IsLContinuation (curveC m) F ∧ analyticOrderAt F 1 ≤ 1 then 1
  else 0

set_option linter.deprecated false in
/-- **Pinned `𝓛` exists** (from integrality and `𝓛(1) = 1`). -/
theorem isTYZLcal_lcalChoice (h11 : TYZThm11Integral) (h1 : TYZLcalOne) :
    IsTYZLcal (lcalChoice h11) := by
  have e1 : lcalChoice h11 1 = 1 := by simp [lcalChoice]
  refine ⟨e1, fun m hsq hcl => ?_, fun n hsq hn => ?_⟩
  · by_cases hm1 : m = 1
    · subst hm1
      rw [e1, Int.cast_one, one_pow]
      exact h1.symm
    · have hm : Squarefree m ∧ (m % 8 = 1 ∨ m % 8 = 3) := ⟨hsq, hcl⟩
      have e : lcalChoice h11 m = (h11 m hsq hcl).choose := by
        rw [lcalChoice, if_neg hm1, dif_pos hm]
      rw [e]
      exact (h11 m hsq hcl).choose_spec
  · have hn1 : n ≠ 1 := by omega
    have hnc : ¬ (Squarefree n ∧ (n % 8 = 1 ∨ n % 8 = 3)) := by omega
    by_cases hc : ∃ F : ℂ → ℂ, IsLContinuation (curveC n) F ∧ analyticOrderAt F 1 ≤ 1
    · have : lcalChoice h11 n = 1 := by
        rw [lcalChoice, if_neg hn1, dif_neg hnc, if_pos ⟨hsq, hn, hc⟩]
      simp [this, hc]
    · have : lcalChoice h11 n = 0 := by
        rw [lcalChoice, if_neg hn1, dif_neg hnc, if_neg (fun h => hc h.2.2)]
      simp [this, hc]

/-- Theorem 1.1's congruence (set-partition reading) gives the Lemma 2.9 congruence
(`PropN.lemmaN1_core`: `Λ` satisfies it). -/
theorem lemma29Mod2_of_thm11Mod2 (h : TYZThm11Mod2) : TYZLemma29Mod2 := by
  intro ℓ hℓ
  have hLam := h ℓ hℓ
  obtain ⟨-, c2, c3⟩ := lemmaN1_core
  constructor
  · intro m hsq hm1 hm
    rw [← c2 m hsq hm1 hm]
    push_cast
    refine Finset.sum_congr rfl fun d hd => ?_
    simp only [Finset.mem_filter, Nat.mem_divisors] at hd
    obtain ⟨⟨hdm, -⟩, hd8, -⟩ := hd
    have hq8 : m / d % 8 = 1 := by rw [div_mod8_of hdm hm hd8 (Or.inl rfl)]
    rw [hLam d (hsq.squarefree_of_dvd hdm) (Or.inl hd8),
      hLam (m / d) (hsq.squarefree_of_dvd (Nat.div_dvd_of_dvd hdm)) (Or.inl hq8)]
  · intro m hsq hm
    rw [← c3 m hsq hm]
    push_cast
    refine Finset.sum_congr rfl fun d hd => ?_
    simp only [Finset.mem_filter, Nat.mem_divisors] at hd
    obtain ⟨⟨hdm, -⟩, hd8⟩ := hd
    have hq8 : m / d % 8 = 3 := by rw [div_mod8_of hdm hm hd8 (Or.inl rfl)]
    rw [hLam d (hsq.squarefree_of_dvd hdm) (Or.inl hd8),
      hLam (m / d) (hsq.squarefree_of_dvd (Nat.div_dvd_of_dvd hdm)) (Or.inr hq8)]

/-- **The leaves give `PropN.TYZInputs`** (with `L` the pinned `𝓛`). -/
theorem tyzInputs_of_leaves (h11 : TYZThm11Integral) (h1 : TYZLcalOne) (h29 : TYZLemma29Mod2)
    (hG : TYZGenusPackage) : TYZInputs := by
  have hP := isTYZLcal_lcalChoice h11 h1
  refine ⟨lcalChoice h11, hP.1, h29 _ hP.2.1, fun n hn hsq hLn => ?_, fun n hn hsq =>
    hG _ hP n hn hsq⟩
  by_contra hc
  exact hLn ((hP.2.2 n hsq hn).mpr hc)

/-- **Main glue: the leaves give the premise `TYZThm35ReadingA`** (through Proposition N,
`PropN.tyzThm35ReadingA_of_tyzInputs`). -/
theorem tyzThm35ReadingA_of_leaves (h11 : TYZThm11Integral) (h1 : TYZLcalOne)
    (h29 : TYZLemma29Mod2) (hG : TYZGenusPackage) : TYZThm35ReadingA :=
  tyzThm35ReadingA_of_tyzInputs (tyzInputs_of_leaves h11 h1 h29 hG)

/-- The same with Theorem 1.1's congruence in place of Lemma 2.9. -/
theorem tyzThm35ReadingA_of_leaves' (h11 : TYZThm11Integral) (h1 : TYZLcalOne)
    (h11b : TYZThm11Mod2) (hG : TYZGenusPackage) : TYZThm35ReadingA :=
  tyzThm35ReadingA_of_leaves h11 h1 (lemma29Mod2_of_thm11Mod2 h11b) hG

/-- **At one `n`, the content of the package is reading A at `n`**: for a pinned `ℓ` with
`ℓ n = 0` (i.e. no continuation of order `≤ 1`), `GenusData ℓ n` is inhabited iff
`T_5a(n) = T_5b(n) = 0`. -/
theorem genusData_nonempty_iff {ℓ : ℕ → ℤ} (hℓ : IsTYZLcal ℓ) (h29 : TYZLemma29Mod2) {n : ℕ}
    (hn : n % 8 = 5) (hsq : Squarefree n) (h0 : ℓ n = 0) :
    Nonempty (GenusData ℓ n) ↔ T5aCl n = 0 ∧ T5bCl n = 0 := by
  have hLam := lemmaN1 hℓ.1 (h29 ℓ hℓ.2.1)
  obtain ⟨p5, p7⟩ := parity_sums_eq hn hsq (L := ℓ) hLam
  rw [Witness.genusData_nonempty_iff_parities ℓ n hn hsq hℓ.1 h0, p5, p7]

/-- **Given the §2 leaves, the genus-point package is exactly the premise**: all of the content
of `TYZThm35ReadingA` beyond the §2 leaves sits in `TYZGenusPackage`. (Hecke's continuation is
the fork's theorem `ZInQ.Contrib.heckeContinuation`.) -/
theorem genusPackage_iff_readingA (h11 : TYZThm11Integral) (h1 : TYZLcalOne)
    (h29 : TYZLemma29Mod2) : TYZGenusPackage ↔ TYZThm35ReadingA := by
  refine ⟨tyzThm35ReadingA_of_leaves h11 h1 h29, fun hA ℓ hℓ n hn hsq => ?_⟩
  by_cases h0 : ℓ n = 0
  · have hno := (hℓ.2.2 n hsq hn).mp h0
    obtain ⟨F, hF⟩ := ZInQ.Contrib.heckeContinuation n (by omega)
    have h2 : 2 ≤ analyticOrderAt F 1 := two_le_of_not_le_one fun hle => hno ⟨F, hF, hle⟩
    exact (genusData_nonempty_iff hℓ h29 hn hsq h0).mpr (hA n hn hsq F hF h2)
  · exact Witness.genusData_nonempty ℓ n h0

end ZInQ.Contrib.TYZDecomp

/-! ### Axiom audit -/
#print axioms ZInQ.Contrib.TYZDecomp.readingA_iff
#print axioms ZInQ.Contrib.TYZDecomp.not_reading_of
#print axioms ZInQ.Contrib.TYZDecomp.lValOne_eq
#print axioms ZInQ.Contrib.TYZDecomp.isTYZLcal_lcalChoice
#print axioms ZInQ.Contrib.TYZDecomp.lemma29Mod2_of_thm11Mod2
#print axioms ZInQ.Contrib.TYZDecomp.tyzInputs_of_leaves
#print axioms ZInQ.Contrib.TYZDecomp.tyzThm35ReadingA_of_leaves
#print axioms ZInQ.Contrib.TYZDecomp.tyzThm35ReadingA_of_leaves'
#print axioms ZInQ.Contrib.TYZDecomp.genusData_nonempty_iff
#print axioms ZInQ.Contrib.TYZDecomp.genusPackage_iff_readingA
