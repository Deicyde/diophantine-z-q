# tyz-decomp: the premise `TYZThm35ReadingA` as literature leaves plus glue

Task tyz-decomp, 2026-11-13. Lean: `scratch/tyz-decomp/TYZDecomp.lean`, `scratch/tyz-decomp/CurveA.lean`
(both compile with `lake env lean`; no `sorry`, no `axiom`). Results log: `scratch/tyz-decomp/log.md`.
No existing file was edited.

Marks. **VERIFIED**: read in a source named here, computed, or compiled. **STANDARD**: a published
theorem with its reference. **SPECULATIVE**: an assessment. **UNVERIFIED**: a locator or theorem number
that was not read by this task or by an earlier task that recorded reading it. TYZ means Tian–Yuan–Zhang,
*Genus periods, genus points and congruent number problem*, arXiv:1411.4728v1 (the only arXiv version),
Asian J. Math. 21 (2017), no. 4, 721–774 (refereed). `Lnnnn` is a line of the arXiv source `Period7.tex`.
**`Period7.tex` is not on this host** (VERIFIED: `~/tyz-src` does not exist). Every line number below is
quoted from `nt-tyz.md`, `pn-design.md`, `rv-nt-tyz.md`, `rv-tyz-inputs.md` or `rv-pn-encoding.md`, where an
earlier task recorded reading it in the source ("VERIFIED by nt-tyz" etc.); this task re-read none of them.
Journal page numbers are those of the AI locator audit `docs/research/locators.md` (2026-11-12); all other
journal locators are UNVERIFIED.

## Caveats that stay attached to every statement below

1. **Reading A is not printed in any refereed text.** The only printed statement of it that the project
   has found is Smith, arXiv:1603.08479, Theorem 2.1 (unrefereed; nt-tyz §3).
2. **TYZ was read in arXiv v1 only**, by AI agents. The journal text was read only by the AI locator audit
   (`locators.md`), and only for the locators quoted below. arXiv Theorem 1.2 (journal Theorem 1.4,
   pp. 723–724) is **false read literally** (readings B and C; nt-tyz §1.4, `n = 26565, 33117`).
3. **Proposition N** (nt-tyz §4; Lean `ZInQKernel/RouteK/PropN.lean`) and every field-by-field faithfulness
   argument for `PropN.GenusData` (`pn-design.md` §2, `rv-tyz-inputs.md`, `rv-pn-encoding.md`) **have been
   reviewed by AI models only**, never by a human.
4. The constant of TYZ Theorem 3.3 rests on a computation TYZ do not print (L2014–2015); `tyz-t1.md` closes
   it by an AI-written derivation from TYZ's Theorem A.9 plus numerics, not by a printed source.

## 0. Main result

**The decomposition.** `TYZThm35ReadingA` follows, by glue proved in Lean, from five leaves:

| leaf (Lean, namespace `ZInQ.Contrib.TYZDecomp`) | printed source | refereed? | over genuine definitions? |
|---|---|---|---|
| `TYZThm11Integral` | TYZ Theorem 1.1, first assertion (L371–380), odd case | yes (journal number UNVERIFIED) | **yes** |
| `TYZLcalOne` | TYZ L1082 ("Since `𝓛(1) = 1`", asserted); classical value of `L(E₁, 1)` | yes (asserted, not proved, in TYZ) | **yes** |
| `TYZLemma29Mod2` (or the alternative `TYZThm11Mod2`) | TYZ Lemma 2.9 (L1062–1066) with Proposition 2.3 (L580–586), mod 2 (resp. Theorem 1.1, congruence, set-partition reading) | yes (Lemma 2.9: same number in the journal per `locators.md`) | **yes** |
| `TYZGenusPackage` | TYZ §3: recursion (L1325–1330), Theorem 3.3 `ε`-classes (L1299–1311), Theorem 3.5 first assertion (L1353–1356, L1295), `τ` facts (L1383–1404, from Tian, Cambridge J. Math. 2 (2014)), Lemmas 3.16, 3.18, 3.21(1),(4) (L2182–2185, L2230–2232, L2504–2516), plus F4 (standard, unprinted) | yes, except F4; but see caveats 3–4 (field-by-field faithfulness reviewed by AI only; Theorem 3.3's constant rests on a computation TYZ do not print) | **no**: bundled existential over the abstract `PropN.GenusData` (§3) |
| `CurveA.TYZLemma316` (statable now; an input to the justification of the package fields `β_τ`, `tors_mem_range`; not used by the glue) | TYZ Lemma 3.16, second assertion (L2182–2185) | yes | **yes** |

Hecke's continuation, which the premise and the leaves presuppose, is a theorem of the fork
(`ZInQ.Contrib.heckeContinuation`), not a leaf.

**What the decomposition shows** (all VERIFIED, compiled):

1. `tyzThm35ReadingA_of_leaves`: the first four leaves give the premise (through Proposition N).
2. `genusPackage_iff_readingA`: **given the three genuine leaves `TYZThm11Integral`, `TYZLcalOne`,
   `TYZLemma29Mod2`, the genus-point package is equivalent to the premise.** So the decomposition isolates
   exactly the arithmetic of `𝓛` on the classes `1, 3 (mod 8)` (genuine, refereed, unambiguous leaves) and
   leaves all of the remaining content of reading A in one bundled leaf, the genus-point package.
3. That package cannot be split into separately stated leaves over Mathlib's definitions: its objects
   (`A(ℍ'_n)`, the genus points `Z(e)`, the points `P(e)`, the lifting `β'`) are existential, and Mathlib has
   no modular parametrization `X₀(32) → A`, no CM (Heegner) points and no ring class fields to pin them.
   Split into separate leaves, the clauses would talk about different existential objects and the glue
   would be unprovable (the rv-g0pieces failure mode). §3 lists the missing objects and the field-by-field
   sources, and §4.2 says what a pinned version needs.
4. `readingA_iff`: reading A of TYZ Theorem 3.5(2), stated literally over genuine definitions (both sums),
   *is* the premise. Readings B, C and the fourth reading D of rv-nt-tyz §5 are stated too; all
   three are false (nt-tyz §1.4 numbers; `not_reading_of` is the shape of the refutation).
5. A finding about the existing encoding (F0, VERIFIED, already in the fork): by
   `ZInQ.Contrib.PSide.tyzInputs_iff_readingA_of_hecke`, the existing `PropN.TYZInputs`, whose `L` and
   `GenusData` are both existential, is equivalent to reading A. This task pins `L` to TYZ's `𝓛` by
   genuine definitions, so that its arithmetic becomes three separate genuine leaves; the genus data stay
   existential.

### 0.1 The declarations proved (exact types)

From `scratch/tyz-decomp/TYZDecomp.lean` (`open ZInQ.Literature ZInQ.PropN ZInQ.RouteK.Rank5b
ZInQ.Contrib.PSide`):

```lean
theorem readingA_iff : Thm35ReadingA ↔ TYZThm35ReadingA

theorem not_reading_of {S51 : ℕ → ZMod 2} {n : ℕ} (hn : n % 8 = 5) (hsq : Squarefree n)
    {F : ℂ → ℂ} (hF : IsLContinuation (curveC n) F) (h2 : 2 ≤ analyticOrderAt F 1)
    (hb : T5bCl n = 0) (hS : S51 n = 1) : ¬ Thm35Reading S51

theorem lValOne_eq {m : ℕ} {F : ℂ → ℂ} (hF : IsLContinuation (curveC m) F) : lValOne m = F 1

theorem isTYZLcal_lcalChoice (h11 : TYZThm11Integral) (h1 : TYZLcalOne) :
    IsTYZLcal (lcalChoice h11)

theorem lemma29Mod2_of_thm11Mod2 (h : TYZThm11Mod2) : TYZLemma29Mod2

theorem tyzInputs_of_leaves (h11 : TYZThm11Integral) (h1 : TYZLcalOne) (h29 : TYZLemma29Mod2)
    (hG : TYZGenusPackage) : TYZInputs

theorem tyzThm35ReadingA_of_leaves (h11 : TYZThm11Integral) (h1 : TYZLcalOne)
    (h29 : TYZLemma29Mod2) (hG : TYZGenusPackage) : TYZThm35ReadingA

theorem tyzThm35ReadingA_of_leaves' (h11 : TYZThm11Integral) (h1 : TYZLcalOne)
    (h11b : TYZThm11Mod2) (hG : TYZGenusPackage) : TYZThm35ReadingA

theorem genusData_nonempty_iff {ℓ : ℕ → ℤ} (hℓ : IsTYZLcal ℓ) (h29 : TYZLemma29Mod2) {n : ℕ}
    (hn : n % 8 = 5) (hsq : Squarefree n) (h0 : ℓ n = 0) :
    Nonempty (GenusData ℓ n) ↔ T5aCl n = 0 ∧ T5bCl n = 0

theorem genusPackage_iff_readingA (h11 : TYZThm11Integral) (h1 : TYZLcalOne)
    (h29 : TYZLemma29Mod2) : TYZGenusPackage ↔ TYZThm35ReadingA
```

From `scratch/tyz-decomp/CurveA.lean` (namespace `ZInQ.Contrib.TYZDecomp.CurveA`):

```lean
theorem nonsingular_iPt {x y : Qbar} (h : curveAbar.toAffine.Nonsingular x y) :
    curveAbar.toAffine.Nonsingular (-x) (iQ * y)
theorem lemma316_zero : IsDefinedOver Qi (0 : PtA) ∧ 2 • ((0 : PtA) + iPt 0) = 0
theorem slope_iPt (x₁ x₂ y₁ y₂ : Qbar) :
    curveAbar.toAffine.slope (-x₁) (-x₂) (iQ * y₁) (iQ * y₂) =
      -iQ * curveAbar.toAffine.slope x₁ x₂ y₁ y₂
theorem iPt_add (P Q : PtA) : iPt (P + Q) = iPt P + iPt Q      -- [i] is additive
theorem iPt_iPt (P : PtA) : iPt (iPt P) = -P                   -- [i]² = −1
def iHom : PtA →+ PtA := AddMonoidHom.mk' iPt iPt_add
```

`#print axioms` output (VERIFIED, 2026-11-13, `lake env lean`):

```
'ZInQ.Contrib.TYZDecomp.readingA_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
'ZInQ.Contrib.TYZDecomp.not_reading_of' depends on axioms: [propext, Classical.choice, Quot.sound]
'ZInQ.Contrib.TYZDecomp.lValOne_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'ZInQ.Contrib.TYZDecomp.isTYZLcal_lcalChoice' depends on axioms: [propext, Classical.choice, Quot.sound]
'ZInQ.Contrib.TYZDecomp.lemma29Mod2_of_thm11Mod2' depends on axioms: [propext, Classical.choice, Quot.sound]
'ZInQ.Contrib.TYZDecomp.tyzInputs_of_leaves' depends on axioms: [propext, Classical.choice, Quot.sound]
'ZInQ.Contrib.TYZDecomp.tyzThm35ReadingA_of_leaves' depends on axioms: [propext, Classical.choice, Quot.sound]
'ZInQ.Contrib.TYZDecomp.tyzThm35ReadingA_of_leaves'' depends on axioms: [propext, Classical.choice, Quot.sound]
'ZInQ.Contrib.TYZDecomp.genusData_nonempty_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
'ZInQ.Contrib.TYZDecomp.genusPackage_iff_readingA' depends on axioms: [propext, Classical.choice, Quot.sound]
'ZInQ.Contrib.TYZDecomp.CurveA.nonsingular_iPt' depends on axioms: [propext, Classical.choice, Quot.sound]
'ZInQ.Contrib.TYZDecomp.CurveA.lemma316_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
'ZInQ.Contrib.TYZDecomp.CurveA.iPt_add' depends on axioms: [propext, Classical.choice, Quot.sound]
'ZInQ.Contrib.TYZDecomp.CurveA.iPt_iPt' depends on axioms: [propext, Classical.choice, Quot.sound]
```

No leaf is proved here; the leaves are `def … : Prop`. The glue is proved.

## 1. The printed statements the route needs (question 1)

The route is: premise `⟸` Proposition N (`PropN.tyzThm35ReadingA_of_tyzInputs`, in Lean) `⟸`
`PropN.TYZInputs` (`TYZInputs.lean`) `⟸` the leaves of §0 (`tyzInputs_of_leaves`). Splitting
`TYZInputs` into TYZ's separate printed statements gives the following list. Line numbers: VERIFIED by
the task named in the last column (not re-read here). Journal: `locators.md` (AI audit) where given,
UNVERIFIED otherwise.

| id | printed statement | arXiv v1 locator | journal locator | used in | read by |
|---|---|---|---|---|---|
| T-def | definition of `𝓛(n)` (via `L(E_n,1)/Ω_n` for `n ≡ 1,2,3`; via `L′/(Ω_n R_n)` for `n ≡ 5,6,7`; `𝓛(n) = 0` if `ord_{s=1} > 1`), `Ω_n`, `k`, `a` | L338–353 | UNVERIFIED | `lcalSq`, `IsTYZLcal` | nt-tyz, rv-nt-tyz, rv-tyz-inputs |
| T-1.1 | Theorem 1.1: `𝓛(n) ∈ ℤ` and `𝓛(n) ≡ Σ Π g(d_i) (mod 2)` for squarefree `n ≡ 1,2,3` | L371–380 | UNVERIFIED (§1 renumbered in the journal) | `TYZThm11Integral`, `TYZThm11Mod2` | nt-tyz |
| T-L1 | "Since `𝓛(1) = 1`" | L1082 | UNVERIFIED | `TYZLcalOne` | nt-tyz, pn-design |
| T-2.9 | Lemma 2.9: `Σ ε(d₁,d₂)𝓛(d₁)𝓛(d₂) = Q(n)` (non-ordered, `d₂ ≡ 1`) | L1062–1066 | Lemma 2.9 (`locators.md`) | `TYZLemma29Mod2` | nt-tyz, rv-tyz-inputs |
| T-2.3 | Proposition 2.3: `Q(n) ≡ g(n) (mod 2)` | L580–586 | UNVERIFIED | `TYZLemma29Mod2` | nt-tyz |
| T-rec | the recursion defining `P(n)` (`d₁ > 1` explicit; `ε` "as in Theorem 3.3"; `𝓛(d₁) ∈ ℤ`) | L1320–1330 | UNVERIFIED | package: `recursion` | nt-tyz, pn-design |
| T-3.3 | Theorem 3.3, `ε`-part: `ε = ±i` on `(5,3)`, `±1` otherwise | L1299–1311 | UNVERIFIED | package: `eps_53`, `eps_pm1` | nt-tyz, rv-tyz-inputs |
| T-3.5a | Theorem 3.5, first assertion: `P(n)` represents `𝒫(n) = 2^{−1−ρ(n)}𝓛(n)α_n` in `A(ℍ'_n) ⊗ ℚ`; `𝒫(n) = 0` if `𝓛(n) = 0` | L1353–1356, L1295 | UNVERIFIED (Theorem 3.5(2) is p. 740) | package: `torsion_of_zero` | nt-tyz, rv-tyz-inputs |
| T-τ | the uniformization `τ : ℂ/(1+i)ℤ[i] ≅ A(ℂ)` and its values on `½ℤ[i]` (facts (1)–(3), from Tian, Cambridge J. Math. 2 (2014)) | L1383–1404 | UNVERIFIED | package: `τ`, `τ_eq_zero` | rv-tyz-inputs §1.5a (cusp dictionary recomputed) |
| T-3.16 | Lemma 3.16: `ℚ(A[4]) = ℚ(√2, i)`, `A(ℚ(i)) = A[(1+i)³]` | L2182–2185 | UNVERIFIED | package: `β_τ`; `CurveA.TYZLemma316` | nt-tyz, rv-tyz-inputs |
| T-3.18 | Lemma 3.18: `A(ℍ'_n)_tors = A[(1+i)³]` for odd `n` | L2230–2232 | UNVERIFIED | package: `tors_mem_range` | nt-tyz, rv-tyz-inputs |
| T-β | `β₁ = r_∞(−1)r₂(−2)`, "any liftings"; "β acts on `ℚ(i)` trivially" | L2496–2500, L2581 | UNVERIFIED | package: `β`, `β_τ` | pn-design, rv-tyz-inputs |
| T-3.21 | Lemma 3.21(1): `Z(n)^{β'+1} ∈ g(n)τ((1−i)/2) + ℤτ(1)` (`n ≡ 5`); (4): `= g(n)τ(1/2)` (`n ≡ 7`) | L2504–2516 | UNVERIFIED | package: `beta_five`, `beta_seven` | nt-tyz, rv-tyz-inputs |
| T-3.5(2) | Theorem 3.5(2) (ambiguous; §2) | L1353–1374 | p. 740 (`locators.md`) | readings, §2 | nt-tyz |
| F4 | `[i]` is defined over `ℚ(i)` (so `β'` commutes with `[i]`) | not printed | — | package: typing of `β` | STANDARD |

Not used: Theorem 1.2 (journal 1.4; false literally), Proposition 3.4 (ambiguous statement, sketched proof),
the "i.e." of Theorem 3.5(2), `ρ(n)`, Proposition 3.2(1) and F5 (no longer needed: `TYZInputs` types `β`
through F4), the root number (needed only for `TYZRow5b`, and proved in the fork as
`FunctionalEquation5`). Rédei's formulas are not needed: `T5aCl`, `T5bCl` and `gCl` are stated with the
genuine class group.

### 1.1 Inputs inside TYZ's proofs (second level; not reached by the encoding)

The encoding reaches TYZ's numbered statements, not the theorems their proofs cite. For the record (all
locators from `rv-tyz-inputs.md`, which read the proofs; theorem numbers of the outside papers UNVERIFIED):

| TYZ statement | external inputs of its proof |
|---|---|
| Theorem 1.1, Lemma 2.9 | Theorem 2.1 (L554–560), from TYZ's explicit Waldspurger formula (Theorem 4.2, derived from Yuan–Zhang–Zhang, *The Gross–Zagier formula on Shimura curves*, Ann. of Math. Stud. 184 (2013), Theorem 1.4 per rv-tyz-inputs) and the test vectors of Theorems 2.4, 2.6; symmetry Lemma 2.8 (`lem2.6`, L1009) |
| Theorem 3.3 | TYZ Theorem A.9 (`EGZ`, L3062–3077; explicit Gross–Zagier formula from Yuan–Zhang–Zhang); Lemmas 3.14 (`char'`, L1868), 3.15 (`multiples1`, L1919–1921); Gross–Zagier (Invent. Math. 84 (1986)) and Kolyvagin (Math. USSR Izv. 32 (1989); Grothendieck Festschrift II (1990)), cited at L1993 and in the bibliography L3297–3304; the unprinted computation of L2014–2015 (closed by `tyz-t1.md`, AI) |
| Theorem 3.5, first assertion | Theorem 3.3 and the character formula (proof L2343–2380) |
| Lemmas 3.16, 3.18 | main theorem of CM for `A` (STANDARD); rank 0 of `A` and its `−1`-twist over `ℚ`; ramification and reduction arguments (proof L2182–2342) |
| Lemma 3.21 | Theorem 3.6 (L1413 ff.), from Lemma 3.7, Proposition 3.8, Corollary 3.9 (explicit 2-adic matrices, verified by computer in rv-tyz-inputs with one harmless misprint), Shimura reciprocity (STANDARD), the facts (1)–(3) of L1383–1404 from Tian (2014) |
| definition of `𝓛` on class 5 | Gross–Zagier–Kolyvagin (the rank-one case uses a generator); only the zero set is read here |

## 2. Theorem 3.5(2) and its readings (question 2, ambiguous statement)

For squarefree `n ≡ 5 (mod 8)` the two sums of Theorem 3.5(2) (copied from Theorem 1.2) are: first sum
`T_5a(n)` under every reading; second sum `S₅₁(n) + T_5b(n)`, where the `(d₀, d₁) ≡ (5, 1)` part `S₅₁`
depends on how `d₁` is read (nt-tyz §1.3). In Lean (`Thm35Reading S51`, over Mathlib's L-series, the
genuine class group `gCl`, and `Finpartition`s of `n.primeFactors`):

```lean
def Thm35Reading (S51 : ℕ → ZMod 2) : Prop :=
  ∀ d : ℕ, d % 8 = 5 → Squarefree d → ∀ F : ℂ → ℂ,
    IsLContinuation (curveC d) F → 2 ≤ analyticOrderAt F 1 →
      T5aCl d = 0 ∧ S51 d + T5bCl d = 0
```

| reading | `S₅₁(n)` | Lean | status |
|---|---|---|---|
| A: `d₁ = 1` admitted, set partitions | `T_5a(n)` | `Thm35ReadingA := Thm35Reading T5aCl` | **the one the route needs**; `readingA_iff : Thm35ReadingA ↔ TYZThm35ReadingA`; printed only by Smith (unrefereed) |
| B: all `d_i > 1`, non-ordered (literal Theorem 1.2/1.4) | partitions with ≥ 2 blocks (`= T_5a + g(n)`, nt-tyz) | `Thm35ReadingB := Thm35Reading S51B` | false (`n = 26565`: `T_5a = T_5b = 0`, `S51B = 1`, `ord ≥ 2`) |
| C: `d₁ > 1` distinguished | `Σ_π k(π) w(π)`, `k` = number of class-1 blocks | `Thm35ReadingC := Thm35Reading S51C` | false (same `n`, `S51C = 1`) |
| D (rv-nt-tyz §5): `d₁ = 1` admitted *and* distinguished | `T_5a + Σ_π k(π) w(π)` | `Thm35ReadingD` | false (same `n`: `0 + 1`; refuted in rv-nt-tyz) |

The hypothesis "`2^{−ρ(n)}𝓛(n)` even" is used only in its case `𝓛(n) = 0`, which is `ord_{s=1} ≥ 2` by the
definition of `𝓛` (L338–345); so `Thm35Reading` is weaker than the printed theorem (case `𝓛(n) ≠ 0` even
dropped) and does not need the unproved "i.e." (nt-tyz §2.2 F6). The refutation numbers are nt-tyz's
(VERIFIED there with certified class groups and an algebraic rank bound `≥ 3`; analytic `ord ≥ 2` then
follows from Gross–Zagier–Kolyvagin); they were not recomputed here (no PARI on this host: installing it
needs the network). As a direct citation, reading A is therefore a reading of a refereed but ambiguous
sentence whose other readings are false, plus Smith's unrefereed restatement; this is the caveat that the
decomposition below tries to remove for the arithmetic of `𝓛`, and cannot yet remove for the genus points.

## 3. The leaves in Lean (question 2)

### 3.1 TYZ's `𝓛` over genuine definitions

```lean
def omegaInt : ℝ := ∫ x in Set.Ioi (1 : ℝ), 1 / Real.sqrt (x ^ 3 - x)
def omegaTYZ (m : ℕ) : ℝ := 2 / Real.sqrt m * omegaInt
def lValOne (m : ℕ) : ℂ :=      -- value at 1 of the (unique) entire continuation of L(C_m, s)
  if h : ∃ F : ℂ → ℂ, IsLContinuation (curveC m) F then h.choose 1 else 0
def lcalSq (m : ℕ) : ℂ :=
  lValOne m / ((2 : ℂ) ^ ((2 * m.primeFactors.card : ℤ) - 3) * (omegaTYZ m : ℂ))
def IsTYZLcal (ℓ : ℕ → ℤ) : Prop :=
  ℓ 1 = 1 ∧
  (∀ m : ℕ, Squarefree m → (m % 8 = 1 ∨ m % 8 = 3) → ((ℓ m : ℂ)) ^ 2 = lcalSq m) ∧
  (∀ n : ℕ, Squarefree n → n % 8 = 5 →
    (ℓ n = 0 ↔ ¬ ∃ F : ℂ → ℂ, IsLContinuation (curveC n) F ∧ analyticOrderAt F 1 ≤ 1))
```

`curveC n = shortCurve (−n²)`. Pinning: the continuation exists (`heckeContinuation`) and is unique
(`IsLContinuation.eq`), so `lValOne m` is `L(C_m, 1)` (`lValOne_eq`); `omegaInt` is the Bochner integral
of an integrable function (`x^{−1/2}`-singularity at 1, `x^{−3/2}` decay), `= Γ(1/4)²/(2√(2π)) ≈ 2.622`.
The normalization `𝓛(m)² = L(E_m, 1)/(2^{2k(m)−3}Ω_m)` (TYZ's `2^{2k−2−a}`, `a = 1` for odd `m`;
`Ω_m = (2/√m)∫₁^∞`) is TYZ L338–353 as transcribed in `scratch/rv-tyz-inputs/tyzcalc.py`; rv-tyz-inputs
VERIFIED by PARI that it gives integer squares on about 200 values and that Lemma 2.9 mod 2 and
Theorem 1.1 (set-partition reading) hold on 30 values of `m`. `ℓ` is any sign choice of `𝓛` (TYZ: `𝓛` is
defined up to sign, L361). On class 5 only the zero set is pinned: TYZ's `𝓛(n) = 0` iff `ord > 1`
(definition; in the order-one case `𝓛(n)² = L′/(2^{2k−3}Ω_n R_n) ≠ 0`, `R_n ≠ 0` by
Gross–Zagier–Kolyvagin). That is all the route reads.

The leaves:

```lean
def TYZThm11Integral : Prop :=
  ∀ m : ℕ, Squarefree m → (m % 8 = 1 ∨ m % 8 = 3) → ∃ ℓ : ℤ, (ℓ : ℂ) ^ 2 = lcalSq m
def TYZLcalOne : Prop := lcalSq 1 = 1
def TYZLemma29Mod2 : Prop :=
  ∀ ℓ : ℕ → ℤ, (∀ m : ℕ, Squarefree m → (m % 8 = 1 ∨ m % 8 = 3) → ((ℓ m : ℂ)) ^ 2 = lcalSq m) →
    LemmaTwoEight ℓ
def TYZThm11Mod2 : Prop :=
  ∀ ℓ : ℕ → ℤ, (∀ m : ℕ, Squarefree m → (m % 8 = 1 ∨ m % 8 = 3) → ((ℓ m : ℂ)) ^ 2 = lcalSq m) →
    ∀ m : ℕ, Squarefree m → (m % 8 = 1 ∨ m % 8 = 3) → ((ℓ m : ℤ) : ZMod 2) = Lam m
```

(`LemmaTwoEight` is `PropN.LemmaTwoEight`, the mod-2 form of Lemma 2.9 with Proposition 2.3 that pn-design and
rv-pn-encoding compared with the source; `Lam` is `PropN.Lam`, the set-partition sum.)

* `TYZThm11Integral` is Theorem 1.1's first assertion restricted to odd `m` (weaker than printed).
* `TYZLcalOne` is the number `L(C₁, 1) = ¼∫₁^∞dx/√(x³−x)` (`≈ 0.6555`); TYZ assert it (L1082). It is the
  exact evaluation `L(E, 1)/Ω = 1/8` for 32a2 (`Ω = 2∫₁^∞`), from modular symbols (Cremona's tables) or
  Tunnell (Invent. Math. 72 (1983), `n = 1`); locators UNVERIFIED. It does not follow from the known cases
  of BSD (the factor `1/8` sits at `p = 2`). Numerically VERIFIED (`calL_small.py`).
* `TYZLemma29Mod2` is unambiguous: the signs `ε` and the odd factor `w_K` at `m = 3` (rv-nt-tyz B1) vanish
  mod 2, and the universal quantifier over sign choices is harmless because `ℓ = ±𝓛` pointwise.
* `TYZThm11Mod2` is the alternative: Theorem 1.1's congruence, in the set-partition reading that Lemma N1
  shows is forced by Lemma 2.9. `lemma29Mod2_of_thm11Mod2` makes it a sufficient replacement.

### 3.2 The genus-point package

```lean
def TYZGenusPackage : Prop :=
  ∀ ℓ : ℕ → ℤ, IsTYZLcal ℓ → ∀ n : ℕ, n % 8 = 5 → Squarefree n → Nonempty (GenusData ℓ n)
```

`PropN.GenusData ℓ n` (`ZInQKernel/Hypotheses/TYZInputs.lean`) is the structure whose fields are the TYZ §3
statements of the table in §1 (rows T-rec … T-3.21 and F4), over an abstract `ℤ[i]`-module `M` (the role of
`A(ℍ'_n)`). The package is universal over sign choices of `𝓛`: a sign change of `ℓ(d₁)` is absorbed into
`ε(d₀, d₁)` (each pair occurs in one recursion only; the classes `±1`, `±i` are sign-stable), and
`GenusData` reads `ℓ` only on classes `1, 3` (recursion) and at `n` (zero test), where `IsTYZLcal` pins
it. So TYZ's own objects witness `GenusData ℓ n` for every pinned `ℓ` (given the field-by-field arguments
of pn-design §2 and rv-pn-encoding, AI-reviewed). `genusData_nonempty_iff` shows what one instance means:
when `ℓ n = 0`, `GenusData ℓ n` is inhabited iff `T_5a(n) = T_5b(n) = 0`.

**Why it stays one leaf.** Every object of the package is existential: `M`, `Z`, `P`, `ε`, `τ`, `β`.
Separate leaves "Lemma 3.18 holds for `M`", "Lemma 3.21 holds for `Z`", "Theorem 3.5 holds for `P`" would
each carry their own existential, and nothing would force them to be about the same `M`, `Z`, `P`; the glue
(Proposition N) needs one `M` carrying all fields. The only way to split the package is to pin the objects
by genuine definitions, which needs (§4.2) objects absent from Mathlib.

### 3.3 Lemma 3.16 over genuine definitions (`CurveA.lean`)

```lean
abbrev Qbar : Type := AlgebraicClosure ℚ
def curveA : WeierstrassCurve ℚ := shortCurve 4          -- y² = x³ + 4x
abbrev PtA : Type := (curveA.baseChange Qbar).toAffine.Point
def iQ : Qbar := exists_sqrt_neg_one.choose               -- a fixed i, i² = −1
def iPt : PtA → PtA                                       -- [i] : (x, y) ↦ (−x, iy)
  | .zero => .zero
  | .some x y h => .some (-x) (iQ * y) (nonsingular_iPt h)
def IsDefinedOver (K : IntermediateField ℚ Qbar) : PtA → Prop
  | .zero => True
  | .some x y _ => x ∈ K ∧ y ∈ K
def Qi : IntermediateField ℚ Qbar := IntermediateField.adjoin ℚ {iQ}
def TYZLemma316 : Prop := ∀ P : PtA, IsDefinedOver Qi P ↔ 2 • (P + iPt P) = 0
```

TYZ's `A : 2y² = x³ + x` is `ℚ`-isomorphic to `y² = x³ + 4x` by `(x, y) ↦ (2x, 4y)` (this model is 32a1,
`= X₀(32)`; rv-tyz-inputs §1.5a). The isomorphism commutes with `[i]` and `Gal(ℚ̄/ℚ)` and preserves
fields of definition. `A[(1+i)³] = {P : 2(P + [i]P) = 0}` because `(1+i)³ = 2i(1+i)` and `[i]` is an
additive automorphism; the statement is independent of the choice of `i` (`(1−i)³` generates the same
ideal). The leaf is not a field of the package: it is one of the TYZ inputs that justify the fields `β_τ` and
`tors_mem_range` (with L2581 and Lemma 3.18), which are stated over the abstract `M`; so the glue does
not use `TYZLemma316`; it is
included to show which TYZ inputs are statable over Mathlib today. Non-vacuity: `A(ℚ(i))` has the 8 points
`O, (0,0), (2,±4), (−2,±4i), (±2i,0)` (rv-tyz-inputs §1.5a), and `lemma316_zero` checks `O`.

## 4. Glue (question 3)

### 4.1 What is proved

Beyond Proposition N (already in Lean), the glue is:

* `isTYZLcal_lcalChoice`: from `TYZThm11Integral` and `TYZLcalOne`, a pinned `ℓ` exists (on class 5:
  `1` or `0` by the zero set). This is what makes the universal leaves `TYZLemma29Mod2`, `TYZThm11Mod2`
  and `TYZGenusPackage` non-vacuous *given* `TYZThm11Integral` and `TYZLcalOne` (if the normalization of
  `lcalSq` were wrong, those three could be vacuously true on their own; the glue stays sound because it
  consumes all leaves together).
* `tyzInputs_of_leaves`: the four leaves give `PropN.TYZInputs` with `L := lcalChoice` (I7 is the class-5
  clause of `IsTYZLcal`, by contraposition).
* `tyzThm35ReadingA_of_leaves` (and `'` with `TYZThm11Mod2`): the premise.
* `genusData_nonempty_iff`, `genusPackage_iff_readingA`: the package is exactly the premise, given the §3.1
  leaves (proof: `PropN.lemmaN1`, `PSide.parity_sums_eq`, `PropN.Witness.genusData_nonempty_iff_parities`,
  `PropN.Witness.genusData_nonempty`, `heckeContinuation`).
* `readingA_iff`: the premise is reading A in its literal two-sum form.

### 4.2 What remains: the objects a split of the package needs (SPECULATIVE design)

To state the package's fields as separate leaves over genuine definitions, Lean needs, in this order:

1. **`A(K)` as a `ℤ[i]`-module with Galois action.** Available in part: `CurveA.lean` has `A(ℚ̄)`, `[i]`
   with `[i]` additive and `[i]² = −1` (`iPt_add`, `iPt_iPt`, proved here), and `A(K)` for `K ⊆ ℚ̄`;
   Mathlib has `Point.map` for the Galois action. Missing: the `ℤ[i]`-module instance built from `iHom`
   (routine) and the arithmetic of the explicit 2-power torsion points. With them, `τ` is pinned by its explicit values (the cusp
   dictionary of rv-tyz-inputs §1.5a: `τ(1) = (0,0)`, `τ(±1/2) = (2,∓4)`, `τ((1±i)/2) = (∓2i,0)` up to the
   signs listed there), and Lemma 3.16 becomes a usable field.
2. **The lifting `β'`.** Pinnable as any `σ ∈ Gal(ℚ̄/ℚ)` with `σ(√D) = sgn(D)·(−2, D)₂·√D` for all
   squarefree `D` (the action of the idele `r_∞(−1)r₂(−2)` on quadratic fields; no normalization ambiguity,
   quadratic characters). Whether this agrees with "a lifting of `β₁`" on `ℍ'_n` needs
   `ℍ'_n ∩ ℚ^ab` to be multiquadratic (true for each generalized dihedral `H'_d`; for the compositum
   UNVERIFIED).
3. **Ring class fields** `H_{d,4}` (conductor 4 over `K_d = ℚ(√−d)`), `H'_d` and `ℍ'_n = L_n(i)·Π H'_{d₀}`.
   Possible routes: Tau Ceti's class field theory (vendored oct16 modules include local and global CFT;
   whether the existence theorem gives a usable "class field of a norm group" object was not checked), or
   `K_d(j(O))` for the order `O` of conductor 4 (needs `j` of a CM lattice). Then Lemma 3.18 is a genuine
   leaf.
4. **CM points and the modular parametrization.** `A = X₀(32)` (32a1 is optimal, Manin constant 1). The
   Heegner point `P_n` and the genus point `Z(n) = Σ_{t∈Φ₀} f_n(P_n)^t` need either the moduli
   interpretation of `X₀(32)` or the analytic parametrization `φ(z) = Σ a_m(A) q^m/m` (with `a_m` the
   coefficients of Mathlib's `L(A, s)`) followed by the Weierstrass uniformization `ℂ/Λ_A ≅ A(ℂ)`, plus the
   algebraicity of CM values (Shimura) as a leaf. Then Lemma 3.21 and the recursion become genuine.
5. **`𝒫(n)` and Theorem 3.5's first assertion** need the Néron–Tate height and `α_n` (a generator of
   `A(K_n)^− ⊗ ℚ`); only "`𝓛(n) = 0 ⟹ P(n)` torsion" is read, which needs only items 1–4.

Each item is a formalization project of its own; none is attempted here. Until 1–4 exist, the package is
the honest granularity.

## 5. Review of the leaves (question 4)

Each statement was gone over a second time against its source (as quoted in the earlier notes), asking:
does each clause pin the object it names; could it be vacuous; could it be stronger than the source.

| leaf | pins its objects? | vacuous? | stronger than source? | verdict |
|---|---|---|---|---|
| `TYZThm11Integral` | yes: `lcalSq m` is `L(C_m,1)` (unique continuation) over an explicit real number. The model `shortCurve (−m²)` has `Δ = 64m⁶`, so `v_p(Δ) ≤ 6 < 12` at every prime for odd squarefree `m` and the model is minimal; even a model-dependent `LSeries` would give `L(E_m, s)` | no (an existential over `ℤ` with a fixed target; false if the normalization were wrong, not vacuous) | no: restricted to odd `m ≡ 1, 3`; signs free | OK. Residual risk: the normalization is a second-hand transcription (not re-read); a wrong power of 4 would make this leaf or `TYZLemma29Mod2` false, which the numerics of rv-tyz-inputs exclude on ~200 values |
| `TYZLcalOne` | yes (a closed numerical identity) | no | no | OK; TYZ only assert it; classical value |
| `TYZLemma29Mod2` | yes on classes 1, 3; `LemmaTwoEight` reads `ℓ` only on squarefree divisors of classes 1, 3 | universal over `ℓ`; non-vacuous given `TYZThm11Integral` and `TYZLcalOne` (`isTYZLcal_lcalChoice`) | no: mod 2, signs and `w_K` drop; restricted to odd `m` | OK |
| `TYZThm11Mod2` | yes | as above | depends on reading "non-ordered, `d_i > 1`" as set partitions; Lemma N1 shows this is the only reading consistent with Lemma 2.9 | OK as an alternative; prefer `TYZLemma29Mod2` (unambiguous) |
| `TYZGenusPackage` | **no** for `M, Z, P, ε, τ, β` (existential, by design); yes for `ℓ` (pinned) and `g` (genuine class group) | universal over `ℓ` (non-vacuous given `TYZThm11Integral`, `TYZLcalOne`); each instance has real content (`genusData_nonempty_iff`) | no, given pn-design §2 and rv-pn-encoding (AI): every field is a consequence of a printed TYZ statement, except F4 (standard). Universal over sign choices: checked above | OK as one bundled leaf; **must not be split** (§3.2). Its trust is that of reading A (`genusPackage_iff_readingA`) |
| `CurveA.TYZLemma316` | yes (genuine curve, `ℚ̄`, `ℚ(i)`, explicit `[i]`) | no (8 points on each side; `O` checked) | no: exactly the printed second assertion, transported along a `ℚ`-isomorphism commuting with `[i]` | OK; not used by the glue |
| `Thm35Reading S51` (readings) | yes (`T5aCl`, `T5bCl`, `S51B`, `S51C` are genuine finite sums) | no | weaker than Theorem 3.5(2) (only the case `𝓛(n) = 0`) | OK. Reading D (rv-nt-tyz §5) included, also false |

Further points checked:

* *The class-5 clause of `IsTYZLcal`.* The package needs `ℓ n = 0 ⟹ 𝓛(n) = 0` (so that TYZ's
  Theorem 3.5 gives the torsion field). `ℓ n = 0` means no continuation of order `≤ 1`; with Hecke's
  continuation this is `ord ≥ 2`, and then `𝓛(n) = 0` by definition. The converse direction (needed only
  for the existence of a pinned `ℓ`, where we choose `ℓ`) holds by construction.
* *Junk values.* `lValOne` has a junk branch (no continuation), unreachable by `heckeContinuation`;
  `omegaInt` would be junk `0` if the integrand were not integrable, but it is integrable; `Real.sqrt` is
  applied to `x³ − x > 0` on `(1, ∞)` and to `m ≥ 1`. `ℓ` at non-squarefree arguments is unconstrained and
  never read.
* *Sign choices and `ε`.* A global sign change `ℓ(d₁) ↦ −ℓ(d₁)` and `ε(d₀, d₁) ↦ −ε(d₀, d₁)` keeps the
  recursion; `ε` is per-`n` in `GenusData`, and each pair `(d₀, d₁)` with `d₀d₁ ∣ n` occurs only in the
  recursion of `d = d₀d₁`, so the adjustment is consistent.
* *rv-g0pieces failure mode.* The only leaf with unpinned objects is the package, and it is not split; no
  two leaves share an unpinned object. The three genuine leaves share `lcalSq`, which is pinned.

### 5.1 Second, independent review (AI subagent, 2026-11-13)

An independent model reviewer read the two Lean files and this note against nt-tyz, pn-design,
rv-tyz-inputs, rv-pn-encoding, `TYZInputs.lean`, `PropN.lean` and the PARI scripts, without seeing the
review above. **No blocker.** It confirmed the pinning of `omegaInt`, `lcalSq` (including that a uniform
normalization error would break `TYZLcalOne` and a `k`-dependent one integrality, since `𝓛(3) = ±1`),
`lValOne`, `IsTYZLcal`, the soundness of quantifying over sign choices, the readings, `readingA_iff`, and
`TYZLemma316` (model transport, `ker[(1+i)³]`, the 8 points). Its findings and their disposition:

| # | finding | disposition |
|---|---|---|
| 1 | the fourth reading is rv-nt-tyz §5 reading D (already refuted there), not new | fixed: renamed `Thm35ReadingD`, credited |
| 2 | `TYZLcalOne` was justified by "BSD (Coates–Wiles, Rubin)", which cannot give the 2-part `1/8` | fixed: exact evaluation (modular symbols / Tunnell), locators UNVERIFIED |
| 3 | stale name `not_readingB_of` in the module docstring | fixed |
| 4 | "Theorem 3.5(1)" cited for integrality on classes 1, 3 (Theorem 3.5 is about `n ≡ 5, 6, 7`) | fixed: dropped |
| 5 | Lemma 3.16 called "a field of the package" | fixed: "an input to the justification of `β_τ`, `tors_mem_range`" |
| 6 | non-vacuity of the universal leaves is conditional on `TYZThm11Integral`, `TYZLcalOne` | fixed in §4.1 and the table |
| 7 | "`rank = 3`" in a docstring where only `≥ 3` is proved by the Kummer images | fixed |
| 8 | the integrability of the `omegaInt` integrand is argued in prose only | see §5.2 |
| 9 | the §0 table should point the package's "refereed" entry to caveats 3–4 | fixed |

## 6. Recommended citation and next steps

* **Cite for the premise:** TYZ (arXiv:1411.4728v1; Asian J. Math. 21 (2017)) Theorem 1.1 (integrality),
  `𝓛(1) = 1`, Lemma 2.9 with Proposition 2.3, and the §3 package (recursion, Theorem 3.3, Theorem 3.5 first
  assertion, Lemmas 3.16, 3.18, 3.21, Tian 2014 for `τ`), assembled by Proposition N (nt-tyz §4; Lean
  `PropN.lean`) as in `tyzThm35ReadingA_of_leaves`. State all four caveats at the top of this note.
* **Next step with the largest trust gain:** item 1 of §4.2 (`[i]` additive, `τ` pinned, a genuine-ambient
  version of `GenusData` with `M ⊆ A(ℚ̄)` and `β` a genuine Galois element), followed by item 3 (ring class
  fields). That would make Lemmas 3.16 and 3.18 separate genuine leaves and pin `τ` and `β`; the genus
  points (item 4) would remain the one existential.
* **Adoption:** the two scratch files can be moved to new files under `ZInQKernel/Contrib/` unchanged
  (they import only `ZInQKernel.Contrib.PSide.TYZInputsIff`, `ZInQKernel.Contrib.HeckeAll.Provider`,
  `ZInQKernel.Model.Field.ShortWeierstrass` and Mathlib).
