# kolyv-cst-printed: Kolyvagin Theorem 1 and Cai–Shu–Tian Theorem 1.1 in printed form

Task kolyv-cst-printed, 2026-11-17. Base: fork main `d435851d` with `origin/wip/pc-from-rc`
(`5404a9fe`, fork issue #83) merged (clean). Lean 4.35.0, Mathlib v4.35.0. Following the owner's
ruling of 11-17 ("cited leaves only"): both theorems enter as printed-form cited leaves. No proof of
either theorem, and no Gross–Zagier or Tian–Yuan–Zhang argument, is written here.

## 0. Main result

* **Kolyvagin.** pc-s12's `PoleS12.KolyvaginThm1` states only the case `r = 1`. The manuscript
  cites Theorem 1 "whose statement includes both `r = 0` and `r = 1`" (tex L1093), and the proof of
  Theorem 5.3 uses the `r = 0` case (the "forward rank-zero theorem": tex L2386, L7626, L7780,
  L8264). New file `ZInQKernel/Contrib/OneProof/KolyvCST/Kolyvagin.lean`:
  `KolyvaginThm1Printed` (the case `r ≤ 1`), the bridge `kolyvaginThm1_of_printed :
  KolyvaginThm1Printed → PoleS12.KolyvaginThm1`, all of Lemma 5.5 (`ForwardRank`,
  `ForwardCorank`) from the two prints plus Mordell–Weil and a Kummer-sequence Prop, and
  `kolyvaginRankOne_of_forwardRank`, which gives pc-from-rc's hypothesis `KolyvaginRankOne`.
* **Cai–Shu–Tian.** New file `ZInQKernel/Contrib/OneProof/KolyvCST/CaiShuTian.lean`:
  `CSTThm11Split`, a **special case** (never stronger) of Theorem 1.1. It covers non-CM `E`, every
  prime of `N` split in `K`, `disc K ∉ {−3, −4}`, `gcd(c, N) = 1`, a primitive ring class character
  `χ`, and the constant `8π²(f,f)/deg φ` replaced by `∃ C > 0` depending only on the
  parametrization. This is exactly the domain of both manuscript uses (tex L2428–2432, L8268–8272),
  and the manuscript fixes `E` non-CM (tex L1013, L2836, L6835). It is stated over genuine
  definitions: Mathlib's `℘`, `L`-series local factors, cusp forms and `q`-expansions, and Tau
  Ceti's ring class fields, Artin isomorphism, `Pic`, Néron–Tate pairing and Eichler integral.
  Four definitions were written fresh and are flagged: `newformLevel`, `phiAn` (the
  complex-analytic modular parametrization), `twistedLFunction` (`L(s, E, χ)` as an Euler product
  over the primes of `K`) and `heightK` (the hermitian height of `P_χ` relative to `K`). Stop rule:
  `X₀(N)` over `ℚ`, its algebraic Heegner points, `deg φ` and the Rankin–Selberg
  `L(s, f × θ_χ)` are absent from Mathlib and Tau Ceti. The statement therefore uses the analytic
  model and the `E/K`-Euler product, and §2.3 lists exactly what is missing. Two small lemmas
  formalize how the manuscript uses the formula: `deriv_ne_zero_iff_heightK_ne_zero` (tex L8269,
  L4345, L9439) and `conductor_factor_ratio` (tex L2428–2436).
* **Nothing was read in the print** (no network in this sandbox). Every clause of both leaves is
  **UNVERIFIED (pending reading)**, so both count **GLUE** until a print reader checks §1, §2 and
  §8. No error was found in the manuscript. §6 records the gaps found.
* Compiles: both files with `lake env lean` and `lake build`, with no errors, warnings or `sorry`.
  `#print axioms` for all 33 new declarations gives `[propext, Classical.choice, Quot.sound]` or a
  subset (§7).

## 1. Kolyvagin, Theorem 1: statement check per clause

Print as the manuscript cites it: `\cite[Theorem 1, pp. 4–5]{kolyvagin}` (tex L1093). Bibitem tex
L11163–11166: V. A. Kolyvagin, "On the Mordell–Weil group and the Shafarevich–Tate group of modular
elliptic curves", MPIM preprint MPI/90-69 (1990), Theorems 1–5, pp. 4–5, with an MPIM archive URL.
Provenance (b), cited. The only page text in the repository is secondhand: an earlier audit,
`docs/theorem-application-audit/evidence/parallel-forward-modularity-report.md` (row A020), reports
p. 3 (definition of "modular") and p. 4 (Theorem 1). This task did not read the print.

| # | Clause (`KolyvaginThm1Printed`) | Lean form | Check |
|---|---|---|---|
| K1 | `E` an elliptic curve over `ℚ` | `E : WeierstrassCurve ℚ`, `E.IsElliptic` | UNVERIFIED (pending reading); standard |
| K2 | `E` modular | `PoleS12.IsModular E` (L-series form, written fresh by pc-s12) | UNVERIFIED. The audit reports that the print's "modular" means a weak Weil parametrization `X₀(N) → E` with `N` the conductor. That is a different predicate: see Known issue 5.1 |
| K3 | `ord_{s=1} L(E, s) = r`, with `r ≤ 1` | `AnalyticRank E r`: an entire `F` equal to Mathlib's `E.LSeries` on `Re s > 3/2` with `analyticOrderAt F 1 = r` | UNVERIFIED. `AnalyticRank E 1 ↔ Manuscript.AnalyticRankOne E` is proved (`analyticRank_one_iff`) |
| K4 | `rank E(ℚ) = r` | `Module.rank ℤ E.toAffine.Point = r` | UNVERIFIED |
| K5 | `Ш(E/ℚ)` finite | `Finite (SelmerTwoPower.sha E)` (Tau Ceti's Ш, local triviality at every place) | UNVERIFIED |
| K6 | "includes both `r = 0` and `r = 1`" (tex L1093) | the quantifier `∀ r ≤ 1` | UNVERIFIED. The audit summary supports it ("whenever analytic rank ≤ 1") |

What the manuscript adds (tex L1094–1097): "Its Theorems 3–5 provide the auxiliary imaginary
quadratic field, the nonzero Heegner height, and finiteness over that field." These describe the
proof of Theorem 1 and are not used as separate leaves. The restriction step (the kernel of
`Ш(A/ℚ) → Ш(A/K)` lies in `Ш(A/ℚ)[2]`, since corestriction after restriction is `[2]`) is a
correct standard argument (STANDARD; ELLIOT for its use here).

**Rating of `KolyvaginThm1Printed`.** Provenance (b), cited (bibitem `kolyvagin`). Kind published.
**Counts GLUE**, flag "pending reading: Kolyvagin MPI/90-69 Theorem 1 p. 4 (both `r = 0` and
`r = 1`; meaning of 'modular' on p. 3)". After reading, it becomes LEAF only in the combination
`BCDTThmA ∧ KolyvaginThm1Printed`, or once restated over geometric modularity (5.1).

## 2. Cai–Shu–Tian, Theorem 1.1: statement check per clause

Print: `\cite[Theorem 1.1]{cst}` (tex L2428, L8269). Bibitem tex L11181–11183: L. Cai, J. Shu and
Y. Tian, "Explicit Gross–Zagier and Waldspurger formulae", Algebra & Number Theory 8 (2014),
URL arXiv:1408.1733. The bibitem gives no issue or page numbers. The earlier audit
(`docs/theorem-application-audit/evidence/applications.md`, row "Cai–Shu–Tian" and §6) gives
ANT 8:10 (2014) 2523–2572, Theorem 1.1 on pp. 2524–2525, and summarizes the hypotheses.
Provenance (b), cited. This task did not read the print.

### 2.1 Clauses of `CSTThm11Split`

| # | Print clause (as the manuscript and the audit summary describe it) | Lean form | Check |
|---|---|---|---|
| C1 | `E/ℚ` elliptic, conductor `N`, newform `f` of weight 2 on `Γ₀(N)` | `E.IsElliptic`; `f : CuspForm (Γ₀(newformLevel E)) 2` whose `q`-coefficients equal `E.LFunction n` | UNVERIFIED. `newformLevel` (written fresh) is the least level carrying such a form. That this level is the conductor is Carayol's theorem (translation, not used in Lean) |
| C2 | (restriction) `E` without CM | `IsNonCMLattice Lat` | Special case. Harmless: the manuscript's `E` is non-CM (tex L1013, L2836, L6835; VERIFIED in the tex) |
| C3 | `φ : X₀(N) → E` a modular parametrization over `ℚ` with `φ(∞) = O` | `phiAn E f Lat κ τ = weierPt(κ · Σ (aₘ/m) qᵐ)`, `IsLatticeOf E Lat`, `IsParamScale N f Lat κ` | Translation, provenance (c), see 2.2. For non-CM `E` these are exactly the nonzero parametrizations over `ℚ` with `∞ ↦ O` |
| C4 | `K` imaginary quadratic, discriminant `D` | `finrank ℚ K = 2`, `IsTotallyComplex K`, `discr K` | UNVERIFIED |
| C5 | (restriction) `u = [O_c^× : ℤ^×] = 1` | `discr K ≠ −3, −4` | Special case, stronger than needed (`u = 1` already holds for `c > 1`). Matches "extra-unit fields are excluded" (tex L2430, L8272) |
| C6 | Conditions at `p ∣ N`: no inert `p ∣ N`, `p` split when `p² ∣ N`, a special condition at `p ∣ (N, D)` (audit summary) | **every** prime of `N` split in `K` (`SplitsIn`) | Special case. Then `μ(N, D) = 0` and the condition at `(N, D)` is vacuous. Matches "all level primes split" (tex L2429, L8271). UNVERIFIED |
| C7 | `c ≥ 1`, `gcd(c, N) = 1` | `[NeZero c]`, `Nat.Coprime c (newformLevel E)` | UNVERIFIED; matches tex L2429 |
| C8 | `χ` a primitive ring class character of conductor `c` | `χ : Pic(O_c) →* ℂˣ` with `O_c = ℤ + c𝓞_K` (`conductorOrder`, copied from `TYZGenus.RingClass`), `IsPrimitiveRingClassChar` (no factorization through `Gal(H_{c'}/K)` for `c' ∣ c`, `c' ≠ c`) | UNVERIFIED. Tau Ceti's `Pic`, `ringClassField`, `ringClassArtinEquiv` |
| C9 | Heegner point `x_c ∈ X₀(N)(H_c)` and `P_χ(f) = Σ_{t ∈ Pic(O_c)} χ(t) φ(x_c^t)`, unaveraged | `τ = cmPoint` of a primitive form `[A, B, C]` with `N ∣ A` and discriminant `Dc²`; any `y ∈ E(H_c)` with `ι(y) = φ(τ)` for some `ι : H_c → ℂ`; `P_χ = Σ_σ χ(σ) σ(y)` | Translation, provenance (c), see 2.2. "Unaveraged" (the literal class sum) matches tex L2431, L8269 and the audit |
| C10 | `L(s, E, χ)` = Rankin–Selberg `L(s, f × θ_χ)`, centre `s = 1` | `LSeries (twistedLFunction E (chiAt O_c χ))`: Euler product over `𝔭 ⊂ 𝓞_K` of Mathlib's local factor of `E/K_𝔭` at `T = χ(𝔭)N𝔭^{-s}`, with `χ(𝔭) = 0` for `𝔭 ∣ c`; `F` any entire continuation | Translation, provenance (c), see 2.2 |
| C11 | `ĥ_K` the Néron–Tate height over `K`, extended hermitian to `E(H_c) ⊗ ℂ` | `heightK = [H_c:K]⁻¹ Σ_{σ,σ'} χ(σ) conj χ(σ') ⟨σy, σ'y⟩_{H_c}`, where `⟨,⟩_{H_c}` is Tau Ceti's `neronTatePairing` over `H_c` | Normalization VERIFIED in source: Tau Ceti's height is `lim h_x(2ⁿP)/4ⁿ` with `h_x` Mathlib's `logHeight` over `H_c`, which is *relative* (infinite places with multiplicity, normalized `FinitePlace`s), and `⟨P, P⟩ = ĥ(P)`. So `heightK` is relative to `K` up to a fixed factor. Whether CST's `ĥ_K` is relative or absolute, `h_x` or `h_x/2`, changes only a constant independent of `(K, c, χ)`, which `C` absorbs. UNVERIFIED which convention the print uses |
| C12 | `L'(1, E, χ) = 2^{-μ(N,D)} · 8π²(f, f)_{Γ₀(N)} / (u² √|Dc²|) · ĥ_K(P_χ(f)) / deg φ` (as recalled; tex L2430 confirms the factor `c √|disc K|`) | `∃ C > 0` (depending on `E, f, Lat, κ` only) with `deriv F 1 = C / (c √|D|) · heightK` | Consequence of the print with `μ = 0`, `u = 1`, `C = 8π²(f,f)/deg φ` (positive, fixed by the parametrization). The exact constant is UNVERIFIED (recalled, not read) |

### 2.2 The translations (provenance (c), on the spot; not LEAF)

* **C3, analytic parametrization.** The period lattice `Λ_f` of `2πi f dz` on `Γ₀(N)` gives
  `A_f(ℂ) = ℂ/Λ_f` for the optimal quotient `J₀(N) → A_f`, which is defined over `ℚ` (STANDARD,
  Shimura, *Introduction to the arithmetic theory of automorphic functions*, §7.5; theorem number
  UNVERIFIED). An analytic map `ℍ → ℂ/Lat, τ ↦ κ ∫f` that is `Γ₀(N)`-invariant needs
  `κΛ_f ⊆ Lat`. It is then `β ∘ φ_opt` for a homomorphism of complex tori
  `β : A_f(ℂ) → E(ℂ)`, which is algebraic over `ℚ̄` (GAGA). For non-CM `E`, `Hom_{ℚ̄}(A_f, E)` has
  rank 1 and contains a `ℚ`-isogeny, so all of it is defined over `ℚ`. Every `phiAn` allowed by
  the hypotheses is therefore a modular parametrization over `ℚ` with `∞ ↦ O`, and conversely.
  `weierPt` uses `x = ℘ − b₂/12`, `y = (℘' − a₁x − a₃)/2`, and `IsLatticeOf` uses
  `g₂ = c₄/12`, `g₃ = c₆/216`. Mathlib's convention `℘'² = 4℘³ − g₂℘ − g₃` was checked
  (VERIFIED in `Mathlib/Analysis/SpecialFunctions/Elliptic/Weierstrass.lean`). The sign of `y`
  is a choice of `±κ`, which the statement allows.
* **C9, Heegner points.** If `gcd(N, Dc²) = 1`, which follows from C6 and C7, the root `τ` of a
  primitive `[A, B, C]` with `N ∣ A` and its multiple `Nτ` both have endomorphism ring `O_c`.
  Proof: a prime `q` dividing `A/N`, `B` and `NC` divides `N` and `Dc²`. So `τ` is a Heegner
  point of conductor `c` (VERIFIED by this argument), and the algebraic `y` exists by CM theory.
  The statement quantifies over every `ι`, every `𝔫`-type (`B mod 2N`) and every class. A
  Galois-conjugate base point multiplies `P_χ` by a root of unity, which leaves the height
  unchanged. The conjugate embedding of `K` and the opposite convention for the Artin map both
  turn `P_χ` into a conjugate of `P_{χ̄}`. Here `L(s, E, χ̄) = L(s, E, χ)` (reindex `𝔭 ↦ 𝔭̄`,
  since `E` is defined over `ℚ`). So these choices do not change the identity, *provided* the
  print allows any `𝔫` with `O_c/𝔫 ≅ ℤ/N` (UNVERIFIED, §8 item 3).
* **C10, the `L`-function.** At `𝔭 ∤ cN` the factors are those of `f × θ_χ` (STANDARD). At
  `𝔭 ∣ N`, which is split by C6, `K_𝔭 = ℚ_p` and `χ` is unramified there (`gcd(c, N) = 1`), so the
  factor is `E/ℚ_p`'s factor twisted by `χ(𝔭)` (STANDARD). At `𝔭 ∣ c` the local components of a
  primitive `χ` are ramified at every place over `p`, so the Rankin–Selberg factor is `1`.
  `rescale 0` of a local series with constant term `1` is `1`. This is a standard local
  computation, SPECULATIVE at the level of exact references. The archimedean factor is not
  included, matching the classical finite `L`-function with centre `s = 1`.

### 2.3 What is not stated (stop rule)

1. `X₀(N)` as a curve over `ℚ`, the algebraic Heegner point `x_c ∈ X₀(N)(H_c)`, and an algebraic
   `φ : X₀(N) → E` with its degree. They are absent from Mathlib and Tau Ceti (searched). They are
   replaced by the analytic model, with the dictionary 2.2 as a translation.
2. The Rankin–Selberg `L`-function `L(s, f × θ_χ)` and the theta series `θ_χ`: absent. Replaced by
   `twistedLFunction`, with C10 as the translation.
3. The explicit constant `8π²(f, f)_{Γ₀(N)} / deg φ`. Tau Ceti has Petersson products
   (`CuspForm.peterssonInnerCosets`), but `deg φ` needs item 1. Replaced by `∃ C > 0`, a
   consequence.
4. The general hypotheses at nonsplit primes of `N`, `μ(N, D) > 0` and `u > 1`: not stated
   (special case only; the manuscript does not use them).
5. The Waldspurger half of the paper (Theorem 1.2 or later; UNVERIFIED): not cited at these lines,
   not stated.

**Rating of `CSTThm11Split`.** Provenance (b), cited (bibitem `cst`). Kind published, special case
of the print, over written-fresh definitions (`newformLevel`, `phiAn`, `twistedLFunction`,
`heightK`) and translations (2.2, provenance (c)). **Counts GLUE**, flag "pending reading: Cai–Shu–
Tian ANT 8 (2014) Theorem 1.1 pp. 2524–2525 (constant, `ĥ_K` normalization, choice of `𝔫`)". The
translations of 2.2 stay GLUE even after reading.

## 3. New declarations and ratings

Namespace `ZInQ.Manuscript.KolyvCST` (file `Kolyvagin.lean`):

| Declaration | What | Rating / provenance |
|---|---|---|
| `AnalyticRank E r` | `ord_{s=1} L(E, s) = r` over Mathlib's `LSeries` | definition |
| `analyticRank_one_iff` | `AnalyticRank E 1 ↔ AnalyticRankOne E` | proved |
| `KolyvaginThm1Printed` | Kolyvagin Thm 1, `r ≤ 1` | printed leaf, (b) cited; GLUE, pending reading |
| `kolyvaginThm1_of_printed` | `KolyvaginThm1Printed → PoleS12.KolyvaginThm1` | proved |
| `ForwardRank` | Lemma 5.5, first sentence (tex L1087–1088) | target Prop |
| `forwardRank_of_printed` | `BCDTThmA → KolyvaginThm1Printed → ForwardRank` (tex L1092–1093) | proved |
| `kolyvaginRankOne_of_forwardRank` | `ForwardRank → PoleRC.KolyvaginRankOne` | proved |
| `KummerCorank` | Kummer sequence for `E[2^∞]`, corank form (tex L1097–1102) | textbook GLUE, (a) ELLIOT for the deduction; flag tex L1097 |
| `ForwardCorank` | Lemma 5.5, second sentence (tex L1089) | target Prop |
| `forwardCorank_of` | `ForwardRank → MordellWeil → KummerCorank → ForwardCorank` | proved |
| `forwardRank_and_corank_of_printed` | Lemma 5.5 in full | proved |

Namespace `ZInQ.Manuscript.KolyvCST.CST` (file `CaiShuTian.lean`):

| Declaration | What | Rating / provenance |
|---|---|---|
| `conductorOrderSubalgebra`, `…_le_integralClosure`, `conductorOrder` | `ℤ + c𝓞_K` (copy of `TYZGenus.RingClass`, whose module imports Route K) | definition, proved |
| `HasCuspFormAtLevel`, `newformLevel` | level of the newform | written fresh |
| `eichlerPotential`, `weierPt`, `IsLatticeOf`, `IsNonCMLattice`, `IsParamScale`, `phiAn` | analytic parametrization | written fresh (over Mathlib `℘`, Tau Ceti Eichler integral) |
| `IsHeegnerForm`, `cmPoint` | Heegner forms and their roots | written fresh (classical) |
| `chiAt`, `twistedLFunction` | `χ(𝔭)` and `L(s, E, χ)` | written fresh |
| `IsPrimitiveRingClassChar`, `SplitsIn` | primitivity, splitting | written fresh |
| `ntPairing`, `heightK` | Néron–Tate pairing over `H`, `ĥ_K(P_χ)` | `ntPairing` is Tau Ceti's; `heightK` written fresh |
| `CSTThm11Split` | CST Thm 1.1, split special case | printed leaf, (b) cited; GLUE, pending reading |
| `deriv_ne_zero_iff_heightK_ne_zero` | `L' ≠ 0 ↔ ĥ ≠ 0` given the formula | proved (use at tex L8269, L4345, L9439) |
| `conductor_factor_ratio` | two instances, common `C`: `a₁x₁y₂ = a₂x₂y₁` | proved (use at tex L2428–2436) |

## 4. Where each statement is used

* **Kolyvagin → pc-from-rc.** `poleCompleteness_of_restrictedConverse_final` takes
  `hK : KolyvaginRankOne` (`ZInQKernel/Contrib/PoleRC/CRM.lean`). It is obtained from the prints by
  `kolyvaginRankOne_of_forwardRank (forwardRank_of_printed hB hK)` with `hB : BCDTThmA`,
  `hK : KolyvaginThm1Printed`, or through pc-s12's `kolyvaginRankOne_of_printed` composed with
  `kolyvaginThm1_of_printed`. Only the rank at `r = 1` is used there.
* **Kolyvagin `r = 0` → proof of Theorem 5.3.** `ForwardCorank` at `r = 0` (and finite Ш) is the
  "forward rank-zero theorem" at tex L2386–2387 (§3, Selmer corank zero of `E^{(hk')}`),
  L7624–7627 and L7780–7781 (finite Ш and corank zero at `L_*(h) ≠ 0`), and L8264 (rank zero of the
  `h_*`-component). None of these is in a Lean statement yet: Theorem 5.3 is a target Prop
  (`Manuscript.RestrictedConverse`), not decomposed.
* **Cai–Shu–Tian → proof of Theorem 5.3, sections 7–8.** tex L2428–2436 (Proposition
  `ex:sec7-genus-lower`, (3.4): the formula twice, once for the genus character of conductor one
  over `ℚ(√(hh_*))` and once for `χ_h` at conductor `|h|` over `ℚ(√k')`; the constant cancels,
  `conductor_factor_ratio`). tex L8268–8272 (Proposition `ex:app-detector`: `P_{D_w}` nontorsion,
  `deriv_ne_zero_iff_heightK_ne_zero`). Uncited reuses: L2464 ("the explicit height formula"),
  L4345 ("the conductor-one height formula", the direction `L' = 0 ⇒` torsion), L9439 ("the height
  formula", same direction), and the table row L6797–6799.

## 5. Known issues

1. **"Modular" in Kolyvagin.** The earlier audit reports that the print defines modular as a weak
   Weil parametrization `X₀(N) → E` with `N` the conductor (p. 3). `PoleS12.IsModular` is the
   L-series form (a cusp form on `Γ₀(N)` with the same `L`-series). Weil-modular implies
   `IsModular` (Eichler–Shimura), but the converse needs the Eichler–Shimura construction of `A_f`
   and isogeny invariance. So `KolyvaginThm1Printed` over `IsModular` is literally a consequence
   of Kolyvagin's Theorem 1 *together with* BCDT Theorem A (every `E/ℚ` is Weil-modular), not of
   Kolyvagin's theorem alone. `ForwardRank`, the statement downstream uses, is a consequence of
   the two prints combined, so nothing downstream changes. The same applies to pc-s12's
   `KolyvaginThm1`.
2. **Kolyvagin is cited as a preprint** (MPI/90-69), not a refereed paper (already reported by
   pc-from-rc, item 5). A paper with the same title is in Proc. ICM 1990 (Kyoto), from memory,
   UNVERIFIED. The analytic inputs that the manuscript attributes to Kolyvagin's Theorems 3–5 (an
   auxiliary `K` with `L(E^K, 1) ≠ 0` or `L'` nonzero, and a nonzero Heegner height) come
   historically from Bump–Friedberg–Hoffstein / Murty–Murty and Gross–Zagier. A print reader
   should check whether the preprint's Theorems 3–5 quote those results (the table row at tex
   L6803 cites `gz` alongside `kolyvagin`). From memory, UNVERIFIED.
3. **CST bibitem incomplete.** The bibitem `cst` (tex L11181–11183) gives "Algebra & Number Theory
   8 (2014)" and an arXiv URL, without issue, pages or theorem locator. The earlier audit gives
   8:10, 2523–2572, Theorem 1.1 pp. 2524–2525 (UNVERIFIED here). If the arXiv version differs
   from the print in numbering or constant, the citation is ambiguous.
4. **Line drift in pc-s12 docstrings.** `PoleS12.BCDTThmA` and `PoleS12.KolyvaginThm1` cite tex
   L1099 and L1100. On this base the citations are at L1092 and L1093. Not edited here (other
   task's file).
5. **The CST statement is a special case over translations.** It is not the print verbatim. The
   analytic `φ`, the Euler product over `K` and the hermitian `heightK` replace the print's
   objects (2.2, 2.3). The translations are provenance (c) and are not LEAF. The non-CM and
   all-split restrictions are harmless for the manuscript.
6. **Height normalization.** Tau Ceti's height is in the `h_x` convention (twice Silverman's `ĥ`),
   relative to the field. The factor between conventions is absorbed by `∃ C`, so this is no issue
   for the statement, but any later use of an explicit `C` must fix it.

## 6. Manuscript check

| tex lines | Step | Verdict |
|---|---|---|
| L1086–1089 | Lemma 5.5 statement (`r ≤ 1`: rank `r`, Ш finite, `corank Sel_{2^∞} = r`) | OK. Formalized as `ForwardRank ∧ ForwardCorank`, proved from the prints + `MordellWeil` + `KummerCorank` |
| L1092 | modularity from `\cite[Theorem A]{bcdt}` | unverified (print not read; the BCDT leaf is pc-s12's) |
| L1093 | `\cite[Theorem 1, pp. 4–5]{kolyvagin}`, "includes both `r = 0` and `r = 1`" | unverified (print not read; secondhand audit agrees). Gap filled: Kolyvagin's "modular" (Weil parametrization) is not the L-series form, so BCDT must give Weil-modularity (Known issue 5.1) |
| L1094–1096 | Theorems 3–5 supply the auxiliary field, the nonzero Heegner height, finiteness over it | unverified (attribution of analytic inputs, Known issue 5.2) |
| L1096–1097 | restriction kernel of Ш lies in the finite `Ш(A/ℚ)[2]` | OK (res–cores; finiteness of `Ш[2]` from `Sel₂`, STANDARD) |
| L1097–1102 | Kummer sequence gives the corank assertion | gap filled: the sequence splits because `(ℚ₂/ℤ₂)^r` is divisible, and finiteness of Ш is needed. Stated as `KummerCorank` (textbook GLUE) |
| L1103–1108 | Kato Cor. 14.3 for `r = 0` | not used by this work (unverified, out of scope) |
| L2386–2387, L7624–7627, L7780–7781, L8264 | "forward rank-zero theorem" = Lemma 5.5 at `r = 0` | OK as a use of Lemma 5.5. Requires Kolyvagin's `r = 0` case, now stated (`KolyvaginThm1Printed`) |
| L2428 | `\cite[Theorem 1.1]{cst}` "applies twice" | unverified (print not read). Formalized as `CSTThm11Split` (special case) |
| L2429 | level primes split; conductors prime to `N` | OK. These are hypotheses C6 and C7 of the special case. Application-side unverified: primitivity of `χ_h` at conductor `|h|` over `ℚ(√k')` was not checked here |
| L2430 | extra-unit fields excluded; same parametrization | OK. `disc ≠ −3, −4` (C5); one `(f, Lat, κ)` gives one `C` for both instances |
| L2430–2431 | conductor factor `c √|disc K|`, unaveraged sum | OK as reading. Matches `C/(c √|D|)` and the literal class sum `heightK` (constant unverified) |
| L2432 | common factor `L(E^{(h)}, s)` of the two Rankin products | OK (genus factorization; uncited, ELLIOT, flag tex L2432; not formalized) |
| L2433–2436 | (3.4) from the two instances | not checked beyond the cancellation of `C` (`conductor_factor_ratio`); the index bookkeeping is out of scope |
| L2464 | "the explicit height formula makes `P_{D_w}^{gen}` nontorsion" | OK (uncited reuse of CST; same as L8269) |
| L4345 | "conductor-one height formula": `L'(E/K, 1) = 0` ⇒ torsion | OK, via `deriv_ne_zero_iff_heightK_ne_zero` with `χ` trivial, `c = 1` (uncited reuse of CST) |
| L6797–6799 | table row "CM norms and heights \cite{ccl,cst,cornutjetchev}" with its restrictions | OK (consistent with C5–C9) |
| L6803 | "Forward finiteness \cite{gz,kolyvagin}": only at known nonvanishing or simple zeros or a nontorsion Heegner trace | OK (consistent with `r ≤ 1` hypotheses) |
| L8264 | `h_*`-component rank zero by the forward rank-zero theorem | OK (Lemma 5.5, `r = 0`, applied to `E^{(h_*)}` with `L(E^{(h_*)}, 1) ≠ 0`) |
| L8268–8270 | CST: Rankin derivative `L'(E^{(D_w)},1) L(E^{(h_*)},1) ≠ 0`, so `P_{D_w}` nontorsion | gap filled: the derivative of `L(E^{(D_w)}, s) L(E^{(h_*)}, s)` at `1` is that product only because `L(E^{(D_w)}, 1) = 0`. That holds because the root number of `E^{(D_w)}` is `w(E)·χ_{D_w}(−N) = (−1)·χ_{D_w}(−1)·χ_{D_w}(N) = −1` (`w(E) = −1` at L8250; `χ_{D_w}(−1) = 1` as `D_w > 0`; `χ_{D_w}(N) = 1` as every prime of `N` splits; STANDARD twist formula for `gcd(D_w, N) = 1`). The text leaves this implicit. Also, `ĥ ≠ 0 ⇒` nontorsion uses that `P_χ` is an actual point for a quadratic `χ` (Tau Ceti `canonicalHeight_eq_zero_iff_isOfFinAddOrder`) |
| L8271–8272 | conductor one, all primes of `N` split, extra-unit fields excluded | OK (`c = 1`, C6, C5; `h_*` odd with `|h_*| > 4`) |
| L9439 | "the height formula gives a torsion genus point" if not a simple zero | OK (uncited reuse; direction `L' = 0 ⇒ ĥ = 0`) |
| L11163–11166 | bibitem `kolyvagin` | OK as a locator (preprint, Known issue 5.2); unverified content |
| L11181–11183 | bibitem `cst` | gap: no issue, pages or theorem locator (Known issue 5.3) |

## 7. Compile and axioms

* `lake env lean ZInQKernel/Contrib/OneProof/KolyvCST/Kolyvagin.lean`: no output (no errors or
  warnings).
* `lake env lean ZInQKernel/Contrib/OneProof/KolyvCST/CaiShuTian.lean`: no output.
* `lake build` of both modules: success. Neither file imports `ZInQKernel.OneProof.Main`. Imports:
  `PoleS12.Leaves`, Tau Ceti `RingClass.Field`, `CanonicalHeight.Basic`, `EichlerIntegral.Basic`.
* `scratch/kolyv-cst-printed/Axioms.lean` (output in `scratch/kolyv-cst-printed/axioms-out.txt`):
  all 33 declarations of §3 depend on `[propext, Classical.choice, Quot.sound]`, except
  `IsHeegnerForm`, which depends on `[propext]` only. No `sorry`.

## 8. What a print reader should check

1. Kolyvagin MPI/90-69, **p. 3**: the definition of "modular elliptic curve" (weak Weil
   parametrization? conductor level?).
2. Kolyvagin MPI/90-69, **p. 4, Theorem 1**: hypotheses exactly ("`E` modular,
   `ord_{s=1} L(E,s) ≤ 1`"?), conclusions (`rank E(ℚ) = ord`, `Ш` finite), and whether `r = 0`
   is included. **pp. 4–5, Theorems 2–5**: whether they are Kolyvagin's own or quoted
   (BFH / Murty–Murty, Gross–Zagier).
3. Cai–Shu–Tian, ANT 8 (2014), **pp. 2524–2525, Theorem 1.1** (and arXiv:1408.1733 v-number,
   Theorem 1.1, for agreement):
   (a) hypotheses at `p ∣ N`, the special condition at `p ∣ (N, D)`, and `gcd(c, N) = 1`;
   (b) whether `χ` must be primitive of conductor `c`, and the definition of `P_χ(f)` (sum over
   `Pic(O_c)`, base point, choice of `𝔫`, unaveraged);
   (c) the exact constant (`2^{-μ(N,D)}`, `8π²`, `(f,f)_{Γ₀(N)}` normalization, `u²`,
   `√|Dc²|`, `deg φ`);
   (d) the normalization of `ĥ_K` (relative to `K` or absolute; `h_x` or `h_x/2`) and of the
   hermitian extension;
   (e) whether `L(s, E, χ)` includes the factors at `p ∣ c` and has centre `s = 1`.
4. Whether `E` with CM is allowed in Theorem 1.1. This does not matter for the statement here,
   which assumes non-CM.
