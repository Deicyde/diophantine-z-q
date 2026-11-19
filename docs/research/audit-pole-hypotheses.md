# Audit of the four pole-completeness hypotheses of `ZInQ.OneProof.frozenTarget`

Repository `Deicyde/diophantine-z-q`, branch `main`, commit `181efe5b1b93b5cf913107454aeb60a032e20370` (2026-11-18). All line numbers are at this commit.

This is a reading by an AI model (Claude), made on 2026-11-18. In this project it counts as **AI-READ** evidence. It is not a human reading and it clears no flag (`docs/one-proof/STATEMENT-CHECKS.md`, "Integrity rules"). Nothing was built, edited or posted to GitHub. I read the Lean as source text. That it compiles and uses only the standard axioms is the evidence of the hosted workflow `main build cache`, not of this report.

Source statements are restated closely, with page locators, and are not quoted at length. The project already holds verbatim quotations of the same passages (section 10), and I checked those against the PDFs.

The findings are filed as fork issues #124 (`hRC`), #125 (`hCT`), #126 (`hB`), #127 (`hK`), #128 (the missing records) and #129 (the index). When they were filed, `main` was at `2b7c66a76`, and none of the files cited here had changed since the audited commit.

## 1. Result

| Hypothesis | Lean name | Source | Verdict | Main point |
|---|---|---|---|---|
| `hRC` | `SelmerTwoPower.RestrictedConverseGenuine` | 5 November 2026 manuscript, Theorem 5.3 | **Matches** the manuscript's statement | It is unproved in Lean and unpublished, and it carries almost all of the arithmetic weight of pole completeness |
| `hCT` | `PoleS12.CasselsTatePairingCurves` | Poonen–Stoll's report of Cassels' theorem | **Weaker** (a direct instance, in existence form) | The locator is an introductory sentence about Cassels' theorem, not a theorem of that paper, and `reviews.tsv` has no row for it |
| `hB` | `PoleS12.BCDTThmA` | Breuil–Conrad–Diamond–Taylor, Theorem A | **Weaker** (a consequence) | The derivation is short and elementary. Some docstrings still call it a "printed leaf" |
| `hK` | `PoleS12.KolyvaginThm1` | Kolyvagin, MPI/90-69, Theorem 1 | **Stronger** than the printed theorem in its modularity hypothesis, and only the case of analytic rank 1 | It does not follow from Kolyvagin's theorem by the bridge the board names. It needs BCDT Theorem A as a second input, or else newform theory and Carayol's theorem |

No statement is vacuous or trivially true or false. I found no step in the proof of pole completeness that uses more than the four hypotheses state (section 7). The one finding that changes what a row should say is on `hK` (finding F1, section 8). The most important fact for a reader is the status of `hRC` (section 3.4).

## 2. The definitions the four statements rest on

Each item gives the Lean definition and what it means.

**The curves.** `Manuscript.curve ℓ` is the Weierstrass equation with coefficients `(0, 2ℓ, 0, −3ℓ², 0)` (`ZInQKernel/Hypotheses/PoleManuscript.lean:56`), that is

  E_ℓ : y² = x³ + 2ℓx² − 3ℓ²x = x(x − ℓ)(x + 3ℓ).

Its discriminant is 2304ℓ⁶ (`PoleManuscript.lean:63`), so it is an elliptic curve for ℓ ≠ 0 (`ZInQKernel/Contrib/PoleRC/CRM.lean:26`). E_ℓ is the quadratic twist by ℓ of E_1 : y² = x(x − 1)(x + 3).

**The L-function.** `E.LFunction` and `E.LSeries` are Mathlib's, at the pinned Mathlib commit `56a005855ea1` (`lake-manifest.json`), file `Mathlib/AlgebraicGeometry/EllipticCurve/LFunction.lean`. For each prime p, Mathlib takes a minimal Weierstrass equation of E over ℤ_p (`Reduction.lean:300`, chosen with `Classical.choose`) and the polynomial f_p(T) (`LFunction.lean:43–50`):

* 1 − a_p T + pT², with a_p = p + 1 − #Ẽ(𝔽_p), if the reduction is good (`Reduction.lean:324`);
* 1 − T if it is split multiplicative (`:360`), 1 + T if it is non-split multiplicative (`:341`);
* 1 if it is additive (`:348`).

`E.LFunction : ℕ → ℤ` is the coefficient sequence a_n(E) of the formal Euler product ∏_p 1/f_p(p^(−s)) (`LFunction.lean:79–81`), with a_0 = 0. `E.LSeries s` is Σ_{n≥1} a_n(E) n^(−s), with the value 0 where the series is not summable (`LFunction.lean:84–85`). These are the usual local factors of the Hasse–Weil L-function. The repository proves that the coefficient at p^k is the k-th coefficient of 1/f_p (`ZInQKernel/Contrib/OneProof/RC/TwistDictionary/Dictionary.lean:88`) and that a_n is multiplicative (`ZInQKernel/RouteK/Rank/LFunctionCd.lean:615`), so the Euler product does not take its junk value.

**Analytic rank one.** `AnalyticRankOne E` (`PoleManuscript.lean:71–73`): there is an entire function F with F(s) = `E.LSeries s` for Re s > 3/2 and with a zero of order exactly 1 at s = 1. Such an F is unique, so this says that L(E, s) has an entire continuation with a simple zero at s = 1. The statement includes the existence of the continuation.

**Galois cohomology.** It is the vendored Tau Ceti library (commit `5a01f5fe3621` in the file headers), under `ZInQKernel/Contrib/TauCeti/`:

* G_K is `Gal(SeparableClosure K / K)` with Mathlib's Krull topology (`FieldTheory/Galois/AbsoluteGaloisGroup/Basic.lean:313`).
* E(K^s) is the group of points over the separable closure with the discrete topology and the action on coordinates (`AlgebraicGeometry/EllipticCurve/GaloisCohomology/Coefficients.lean:113`). E(K^s)[m] is its m-torsion (`:207`).
* H¹(G, M) is continuous 1-cocycles modulo coboundaries (`RepresentationTheory/Homological/ContCohomology/LowDegree.lean:508, 185, 831`).
* For an extension L/K and a K-embedding K^s → L^s, the restriction H¹(G_K, E(K^s)) → H¹(G_L, E(L^s)) is the pullback along G_L → G_K and E(K^s) → E(L^s) (`AlgebraicGeometry/EllipticCurve/GaloisCohomology/Restriction.lean:281`). Ш and the m-Selmer group for a family of extensions are defined in `AlgebraicGeometry/EllipticCurve/GaloisCohomology/Selmer.lean:123, 170`.

**Ш and the Selmer groups.** In `ZInQKernel/Contrib/OneProof/SelmerTwoPower.lean`:

* `sha E` (`:120–121`) is the set of classes in H¹(G_ℚ, E(ℚ^s)) whose restriction is zero in H¹(G_{ℚ_p}, E(ℚ_p^s)) for every prime p and in H¹(G_ℝ, E(ℝ^s)). This is Ш(E/ℚ), with all places.
* `selmerAt E n` (`:150–151`) is the set of classes in H¹(G_ℚ, E[2^n]) whose image in H¹(G_ℚ, E) lies in Ш. This is Sel_{2^n}(E/ℚ).
* `selmerTwoPower E` (`:127–130`) is the same with E[2^∞] = E(ℚ^s)[2^∞] (`:84`). This is Sel_{2^∞}(E/ℚ) = ker(H¹(ℚ, E[2^∞]) → ∏_v H¹(ℚ_v, E)).
* `Z2Corank M r` (`:202–203`): there is a finite abelian group F with M ≅ (ℚ₂/ℤ₂)^r × F as abelian groups. The number r is determined by M.
* `SelmerCorankOne E` (`:206–207`) is `Z2Corank (selmerTwoPower E) 1`.

**Modularity.** `IsModular E` (`ZInQKernel/Contrib/OneProof/PoleS12/Leaves.lean:41–43`): there are N ≥ 1 and f in Mathlib's `CuspForm (Γ₀(N)) 2` whose n-th `qExpansion 1` coefficient is a_n(E) for every n ≥ 1. In Mathlib (`Mathlib/NumberTheory/ModularForms/`), a cusp form for a subgroup of GL₂(ℝ) is a holomorphic function on the upper half-plane, invariant under the weight-k slash action of the subgroup, that vanishes at every cusp (`Basic.lean:83–85`, `BoundedAtCusp.lean:54`, `Cusps.lean:58`). Γ₀(N) enters as its image in GL₂(ℝ) (`ArithmeticSubgroups.lean:97–98`), and for a matrix of SL₂(ℤ) the slash action is f(γτ)(cτ + d)^(−k). `qExpansion 1` is the expansion in q = e^(2πiτ) (`QExpansion.lean:172`). So `IsModular E` says: some f ∈ S₂(Γ₀(N)), for some N, has Fourier coefficients a_n(f) = a_n(E) for all n ≥ 1. It does not say that N is the conductor of E or that f is an eigenform.

**Rank.** `Module.rank ℤ E.toAffine.Point` is the rank of E(ℚ) as a ℤ-module, which for a finitely generated group is the Mordell–Weil rank.

## 3. `hRC`: the restricted converse

### 3.1 The Lean statement

`RestrictedConverseGenuine := RestrictedConverse SelmerCorankOne` (`SelmerTwoPower.lean:217–218`, with `PoleManuscript.lean:87–89`). Unfolded:

> For every integer ℓ ≥ 1 that is squarefree with ℓ ≡ 11 (mod 12): if Sel_{2^∞}(E_ℓ/ℚ) ≅ ℚ₂/ℤ₂ × F for some finite abelian group F, then L(E_ℓ, s) has an entire continuation with a zero of order exactly 1 at s = 1.

### 3.2 The source

Theorem 5.3 of the manuscript, `diophantine_zq.tex` L1005–1011, repeated as (RC) at L1771–1775: for every positive squarefree ℓ ≡ 11 (mod 12), corank_{ℤ₂} Sel_{2^∞}(E_ℓ/ℚ) = 1 implies ord_{s=1} L(E_ℓ, s) = 1, with E_ℓ : y² = x(x − ℓ)(x + 3ℓ) (L986, L1763). The manuscript's own text treats Sel_{2^∞} as the classical 2-primary Selmer group: the proof of its Lemma 5.5 displays the sequence 0 → A(ℚ) ⊗ ℚ₂/ℤ₂ → Sel_{2^∞}(A/ℚ) → Ш(A/ℚ)[2^∞] → 0 (L1098–1103).

### 3.3 Comparison

**Verdict: matches.** The domain (positive, squarefree, ≡ 11 mod 12), the curve, the Selmer group, the corank and the order of vanishing are the manuscript's. Two remarks, neither a discrepancy with the manuscript:

* The conclusion includes the existence of the entire continuation of L(E_ℓ, s). The manuscript's notation presupposes it, and gets it from modularity (L1779–1780).
* The statement is more general than the proof of pole completeness needs. That proof applies it only at two parameters n and nθ per input B, both with #Sel₂ = 8 (`ZInQKernel/Contrib/PoleRC/Reduction.lean:23`, `Defs.lean:55`).

What an adversarial reader would check, and what I found:

| Check | Finding |
|---|---|
| Is the premise ever true, or is the implication vacuous? | Not vacuous. The Lean proof derives `SelmerCorankOne (curve n)` for the n it constructs, from `hCT` and proved lemmas (`Lemma54FromCasselsTate.lean:83`), and then applies `hRC`. |
| Is the Selmer group cut out by other local conditions? | No. It is the kernel of localisation to H¹(ℚ_v, E) at every place, including ℝ (section 2). |
| Is the Galois cohomology abstract rather than continuous? | No. Cocycles are continuous for the Krull topology, with discrete coefficients. |
| Is the L-function a junk value? | No (section 2). |
| Are the four hypotheses jointly inconsistent? | I see no way. For a curve of Selmer corank one they give analytic rank 1, rank 1 and finite Ш, which agrees with corank = rank + corank of Ш[2^∞]. |

### 3.4 Weight and status

**Status.** `hRC` is unproved and unpublished.

* It is a hypothesis of `frozenTarget` (`ZInQKernel/OneProof/Main.lean:216`). The board classes it "manuscript hypothesis", GLUE, held by the project on issue 83 (`docs/one-proof/kinds.tsv:31`, `OPEN.md:585–591`).
* Its only source is the manuscript itself, which says (L1014–1016) that Theorem 5.3 is proved in its Sections 7–9 and Appendices E–G. The manuscript is dated 5 November 2026. Its AI usage statement (L11251–11258) says it was developed primarily by AI agents and that their reviews are not independent human peer review. No published theorem is cited for it.
* The project's Lean reduction, `ZInQ.Manuscript.RC.Wiring.restrictedConverseGenuine_of_leaves` (`ZInQKernel/Contrib/OneProof/RC/Wiring/Leaves.lean:490`), is not used by the headline theorem. It reduces Theorem 5.3 to printed results (`Prints`) and to the structure `RCLeaves`. That file's own header (`Leaves.lean:95–121`) lists eight leaves as "conclusion-shaped": the manuscript's steps themselves, or close to them.

**Weight.** Pole completeness is one of the two inputs of the headline theorem, and `hRC` is the only one of its four hypotheses whose truth is not established anywhere.

* In the manuscript, the reduction of Theorem 5.2 to Theorem 5.3 takes about 100 lines (L1019–1121). The proof of Theorem 5.3 takes Sections 7–9 (L1760–5744) and Appendices E–G (L6825–10935): about 8,100 of the manuscript's 11,259 lines.
* In Lean, everything else in pole completeness is proved: the bookkeeping, the simultaneous construction, the local conditions, the 2-descent, Mordell–Weil for E_ℓ, the Kummer identification and Lemma 5.4 from the pairing. `hCT`, `hB` and `hK` are consequences of established theorems.
* So if `hRC` is false, `frozenTarget` is still a correct Lean theorem, but it has a false hypothesis and proves nothing about ℤ in ℚ.

`hRC` is a converse to the theorem of Gross–Zagier and Kolyvagin at the prime 2, for the quadratic twists of a curve without complex multiplication and with full rational 2-torsion. I did not search the literature for results of this kind.

## 4. `hCT`: the Cassels–Tate pairing on the curves E_ℓ

### 4.1 The Lean statement

`CasselsTatePairingCurves` (`ZInQKernel/Contrib/OneProof/CasselsTatePairing.lean:481–482`), with `CasselsTatePairing` (`:90–92`), `QZ` (`:43`) and `divisiblePart` (`:48–49`). Unfolded:

> For every squarefree integer ℓ ≥ 1 with ℓ ≡ 11 (mod 12), there is a biadditive map b : Ш(E_ℓ/ℚ) × Ш(E_ℓ/ℚ) → ℚ/ℤ such that b(x, x) = 0 for all x, and such that for every x: b(x, y) = 0 for all y if and only if x lies in the maximal divisible subgroup of Ш(E_ℓ/ℚ).

`divisiblePart A` is the subgroup generated by all divisible subgroups of A. The file proves that it is divisible and contains every divisible subgroup (`:52`, `:59`), so it is the maximal divisible subgroup.

### 4.2 The source

B. Poonen and M. Stoll, *The Cassels–Tate pairing on polarized abelian varieties*, Ann. of Math. (2) 150 (1999), 1109–1149. I read two copies:

* the author's version that the manuscript's bibliography links (L11098–11100), dated November 6, 1998, with a minor correction of August 23, 2014, 32 pages;
* arXiv:math/9911267v1, which carries the Annals page numbers.

**Locator.** Section 1 (Introduction), first paragraph: page 2 of the author's version, **page 1110 of the journal pagination** (from the arXiv copy).

**Statement, restated.** Cassels proved that for an elliptic curve E over a number field there is a pairing Ш(E) × Ш(E) → ℚ/ℤ that becomes nondegenerate after Ш(E) is divided by its maximal divisible subgroup, and that this pairing is alternating: ⟨x, x⟩ = 0 for all x. The paper attributes this to Cassels (its reference [Ca]).

Supporting passages in the author's version:

* Section 2, pp. 3–4: M_div is the maximal divisible subgroup, M_nd = M/M_div, pairings are bilinear, and "alternating" means ⟨a, a⟩ = 0 for all a.
* p. 5: Ш(A) is the Shafarevich–Tate group of A over the global field k, the locally trivial principal homogeneous spaces.
* Section 3.1, p. 6: the pairing, as a sum of local invariants over all places.
* Corollary 7 (p. 11), Corollary 12 and the Remarks after it (p. 14): for genus 1 these recover Cassels' theorem that the pairing is alternating for elliptic curves.

**Corroboration, also read.** J. S. Milne, *Arithmetic Duality Theorems*, 2nd edition, electronic version of 2006:

* Chapter I, Theorem 6.13 (a), p. 82, and Theorem 6.26 (a), p. 92: the left and right kernels of the canonical pairing between the m-primary parts of Ш(K, A) and Ш(K, A^t) are the divisible subgroups.
* p. 81: the pairing on Ш(K, A) is alternating when the polarization is defined by a K-rational divisor.
* Notes, p. 93: Theorem 6.13 is due to Cassels for elliptic curves and to Tate in general.

### 4.3 Comparison

**Verdict: weaker than the source, and a direct instance of it.**

| Lean clause | Source |
|---|---|
| E_ℓ over ℚ, with ℓ ≠ 0 | an elliptic curve over a number field |
| `sha E`: classes of H¹(G_ℚ, E) trivial at every place | Ш(E) |
| `b : sha E →+ sha E →+ QZ` | a (bilinear) pairing with values in ℚ/ℤ |
| `∀ x, b x x = 0` | alternating |
| the left kernel equals `divisiblePart (sha E)` | nondegenerate after dividing by the maximal divisible subgroup: the pairing factors through the quotient, and has trivial kernel there |
| `∃ b` | Cassels' specific pairing; the Lean does not name it |

The Lean statement is weaker in three ways: it asserts only that some pairing exists, it is over ℚ only, and it is for the family E_ℓ only. Nothing in it is stronger: it has no finiteness of Ш, no perfectness on Ш[2], and no compatibility between choices.

Adversarial checks:

* The statement is not trivially true. As stated it is a property of the abstract group Ш, and it fails for a group such as ℤ/2. The consumer `casselsTateSquare_of_pairing` (`CasselsTatePairing.lean:409`) uses exactly this property: it derives that the 2-torsion of the finite part of Ш[2^∞] has square order.
* The alternating property and the kernel property are asserted of the same pairing, as in the source.
* The restriction to elliptic curves matters. For principally polarized abelian varieties in general the pairing is only antisymmetric, which is the point of the paper (abstract, p. 1; Milne, footnote 17, p. 82).

Concrete problems are F3 and F6 in section 8.

## 5. `hB`: modularity

### 5.1 The Lean statement

`BCDTThmA` (`PoleS12/Leaves.lean:54–55`). Unfolded:

> For every Weierstrass equation E over ℚ with nonzero discriminant, there are N ≥ 1 and a cusp form f of weight 2 on Γ₀(N) with a_n(f) = a_n(E) for every n ≥ 1.

### 5.2 The source

C. Breuil, B. Conrad, F. Diamond and R. Taylor, *On the modularity of elliptic curves over ℚ: wild 3-adic exercises*, J. Amer. Math. Soc. 14 (2001), 843–939. I read the author manuscript that the manuscript's bibliography cites (L11150–11154; 79 pages). Page numbers are that copy's. The journal pages are unverified, because the AMS server refused the request.

* **Theorem A, p. 1** (restated): every elliptic curve E over ℚ is modular.
* p. 1: Γ₁(N). A cusp form of weight k and level N is a holomorphic f on the upper half-plane, with the weight-k transformation law under Γ₁(N) and with |f(z)|²(Im z)^k bounded. S_k(N) is the space of these. The expansion is f = Σ_{n≥1} c_n(f) e^(2πinz), and L(f, s) = Σ c_n(f) n^(−s).
* p. 2: the operators T_p for p ∤ N. An *eigenform* is a simultaneous eigenvector of the T_p for p ∤ N, with eigenvalues a_p(f) and c_p(f) = a_p(f)c_1(f). N(E) is the conductor.
* pp. 2–3: six conditions, stated to be equivalent, and E is called modular when they hold (p. 3).
  1. L(E, s) = L(f, s) for some eigenform f.
  2. The same with f of weight 2 and level N(E).
  3. ρ_{E,ℓ} is modular for some ℓ.
  4. ρ_{E,ℓ} is modular for all ℓ.
  5. There is a non-constant holomorphic map X₁(N)(ℂ) → E(ℂ) for some N.
  6. There is a non-constant morphism X₁(N(E)) → E over ℚ.
* p. 3, the attributions: (3) ⇒ (2) to theorems of Carayol and Faltings; (2) ⇒ (6) to a construction of Shimura and a theorem of Faltings; (1) ⇒ (4) to the characterisation of L(E, s) by ρ_{E,ℓ}; (5) ⇒ (3) to Mazur.

### 5.3 Derivation of the Lean statement from Theorem A

Let E be an elliptic curve over ℚ and N = N(E).

1. By Theorem A and the definition of "modular", condition (2) holds: there is f ∈ S₂(N), an eigenvector of every T_p with p ∤ N, with L(f, s) = L(E, s).
2. Both Dirichlet series converge absolutely in a half-plane, so c_n(f) = a_n(E) for every n ≥ 1. In particular c_1(f) = 1, and the eigenvalue of T_p is a_p(f) = c_p(f) = a_p(E).
3. **Trivial nebentypus.** For p ∤ N, the formula for T_p on p. 2 gives, on q-expansions, c_n(T_p f) = c_{pn}(f) + p·c_{n/p}(⟨p⟩f), where ⟨p⟩ is the diamond operator. Take n = pm in T_p f = a_p(E) f. Then p·c_m(⟨p⟩f) = a_p(E)a_{pm}(E) − a_{p²m}(E) = p·a_m(E), because p is a prime of good reduction and the Euler factor there is 1/(1 − a_p T + pT²). So ⟨p⟩f = f for every prime p ∤ N. Every class of (ℤ/N)^× is a product of classes of such primes, so f is invariant under Γ₀(N).
4. **Dictionary.** A holomorphic function of weight 2 for Γ₀(N) with |f|²(Im z)² bounded vanishes at every cusp, so f is an element of Mathlib's `CuspForm (Γ₀(N)) 2`. Its `qExpansion 1` coefficients are the c_n(f). Mathlib's a_n(E) are the coefficients of the usual L(E, s).

Hence `IsModular E`, with N = N(E).

**Further results needed.** Only the standard formula for T_p and ⟨p⟩ on q-expansions, uniqueness of Dirichlet coefficients, the equivalence of the growth condition with vanishing at the cusps, and the agreement of Mathlib's local factors with the usual ones. No Galois representations and no theorem on primes in progressions are needed.

### 5.4 Comparison

**Verdict: weaker than the source; a consequence of Theorem A through condition (2).** The Lean statement forgets that N can be taken to be the conductor, that f is an eigenform, and conditions (3)–(6). That is harmless for `hB`. It matters for `hK`, where `IsModular` is a premise (section 6). The board's classification of this row, "consequence" (`kinds.tsv:33`), is right.

Adversarial checks: the statement is not vacuous, since a_1(E) = 1 forces f ≠ 0. The objects are the source's: weight 2, level structure Γ₀, expansion in e^(2πiτ), vanishing at all cusps. The introduction of the paper does not define L(E, s); it refers to its characterisation by ρ_{E,ℓ} (p. 3), which is the usual Hasse–Weil function.

Concrete problems are F4 and F6 in section 8.

## 6. `hK`: Kolyvagin's theorem

### 6.1 The Lean statement

`KolyvaginThm1` (`PoleS12/Leaves.lean:70–72`). Unfolded:

> For every elliptic curve E over ℚ: if some cusp form of weight 2 on some Γ₀(N) has a_n(f) = a_n(E) for all n ≥ 1, and L(E, s) has an entire continuation with a zero of order exactly 1 at s = 1, then E(ℚ) has rank 1 and Ш(E/ℚ) is finite.

### 6.2 The source

V. A. Kolyvagin, *On the Mordell–Weil group and the Shafarevich–Tate group of modular elliptic curves*, Max-Planck-Institut für Mathematik preprint MPI/90-69 (1990). I read the scan at the URL in the manuscript's bibliography (L11163–11167). It has 15 numbered pages; printed page n is PDF page n + 2.

* p. 1: Ш(R, E) is the kernel of H¹(R, E) → ∏_v H¹(R(v), E) over all places v, with H¹(L, E) = H¹(G(L̄/L), E(L̄)).
* p. 2: E(R) ≅ F × ℤ^r with F finite, and r = r(R, E) is the rank. L(E, s) is defined for Re s > 3/2 as an Euler product equal to Σ a_n n^(−s).
* p. 3: N is the conductor. The local factor is (1 − a_q q^(−s) + q^(1−2s))^(−1) for q ∤ N, and 1 or (1 ± q^(−s))^(−1) for q | N. Then comes the standing assumption: E is modular, meaning that "there exists a weak Weil parametrization γ : X₀(N) → E" (p. 3; the paper's reference [12] is Mazur and Swinnerton-Dyer). Under it, L(E, s) is entire with a functional equation, and ar(E) is its order of vanishing at s = 1.
* **Theorem 1, p. 4** (restated): r(E) = ar(E) and Ш(E) is finite, if ar(E) ≤ 1.
* pp. 4–5: Theorems 2–5 and the scheme of the proof. Theorem 1 is equivalent to Theorem 2, which follows from Kolyvagin's Theorem 5 (his references [6]–[8]), from Theorem 3 (Gross–Zagier, [5]) and from Theorem 4 (Waldspurger [21] for ar(E) = 1; Bump–Friedberg–Hoffstein [2] and Murty–Murty [14] for ar(E) = 0).

The preprint is a survey of results. It states Theorem 1 with a scheme of proof and gives the proofs by reference.

### 6.3 Comparison

| Lean clause | Source | Agreement |
|---|---|---|
| `E.IsElliptic`, E over ℚ | elliptic curve over ℚ | same |
| `IsModular E` | a weak Weil parametrization X₀(N) → E, N the conductor | **different** |
| `AnalyticRankOne E` | ar(E) = 1 | same, by uniqueness of the continuation; L(E, s) has the same local factors |
| `Module.rank ℤ E(ℚ) = 1` | r(E) = 1 | same |
| `Finite (sha E)` | Ш(E) finite | same object: all places; algebraic and separable closure agree in characteristic 0 |
| only analytic rank 1 | ar(E) ≤ 1 | Lean is the case ar(E) = 1 |

**Verdict: stronger than the printed theorem in its modularity hypothesis, and narrower in scope (analytic rank 1 only).** The Lean premise `IsModular E` asks for less than the printed premise, so the Lean statement is not Theorem 1 and not an instance of it. It is true, as a consequence of BCDT Theorem A and Kolyvagin's Theorem 1 together (route A below). The defect is in the stated derivation, not in the truth of the row.

### 6.4 Derivation, and every further result it needs

Let E be elliptic over ℚ with `IsModular E` and `AnalyticRankOne E`. Kolyvagin's premise must be produced: a non-constant morphism X₀(N) → E over ℚ, with N the conductor. There are two ways.

**Route A: use BCDT Theorem A and ignore the premise `IsModular E`.**

1. By BCDT Theorem A, E satisfies condition (2): an eigenform f of weight 2 and level N(E) with L(f, s) = L(E, s). By steps 2–3 of section 5.3, f lies in S₂(Γ₀(N(E))) and its eigenvalues are the integers a_p(E).
2. Shimura's construction attaches to these eigenvalues a quotient A of J₀(N(E)) over ℚ, of dimension 1, whose L-function agrees with L(f, s) at almost all primes (the Eichler–Shimura relation).
3. Faltings' isogeny theorem then gives a ℚ-isogeny A → E.
4. Composing with X₀(N(E)) → J₀(N(E)) gives the parametrization.

This is BCDT's implication (2) ⇒ (6), with Γ₀ in place of Γ₁. It needs **BCDT Theorem A**, Shimura's construction with the Eichler–Shimura relation, and Faltings' isogeny theorem.

**Route B: use the premise `IsModular E` and not BCDT Theorem A.**

The premise gives f ∈ S₂(Γ₀(N′)) for some N′ with c_n(f) = a_n(E). It does not say that N′ is the conductor or that f is an eigenform.

1. From the Euler product of L(E, s), T_p f = a_p(E) f for the primes p that divide neither N′ nor N(E). For a prime p ∤ N′ of bad reduction this computation gives T_p f = a_p f + p·f(pτ), which is not a multiple of f. So f is not yet an eigenform in BCDT's sense, and BCDT's condition (1) is not available directly.
2. Atkin–Lehner–Li newform theory gives a newform g of some level M dividing N′ with a_p(g) = a_p(E) for almost all p.
3. Shimura's construction and Faltings' theorem show that E is isogenous to the quotient A_g of J₀(M).
4. Carayol's theorem shows that M is the conductor of A_g, hence of E.

BCDT attribute their (3) ⇒ (2) to theorems of Carayol and Faltings (p. 3). So route B needs Atkin–Lehner–Li theory, Shimura's construction with the Eichler–Shimura relation, Faltings' isogeny theorem and **Carayol's theorem**.

With the premise in hand, the rest is a dictionary:

* Analytic side: Kolyvagin's L(E, s) on Re s > 3/2 is `E.LSeries` there. `AnalyticRankOne E` is ar(E) = 1.
* Theorem 1, p. 4, gives r(E) = 1 and Ш(E) finite.
* Arithmetic side: r(E) is `Module.rank ℤ E(ℚ)`, and Ш(E) is `sha E`.

Behind Theorem 1 stand the results the preprint names: Kolyvagin's own papers, Gross–Zagier, and Waldspurger for the case of analytic rank 1.

**What the board says, and why it falls short.** The flag of the row (`kinds.tsv:34`, `OPEN.md:644`), the docstring (`Leaves.lean:57–69`) and the headline's docstring (`Main.lean:16–17, 211`) say that `IsModular` implies Kolyvagin's premise "via Shimura's construction plus Faltings' isogeny theorem (BCDT's (2) => (6))", with trivial nebentypus. But `IsModular` is not condition (2): it has no level condition and no eigenform condition. Shimura and Faltings alone do not bridge that gap. Route A needs BCDT Theorem A as a second cited input of this row, and then the premise `IsModular E` does no work. Route B needs Atkin–Lehner–Li and Carayol.

The repository already says this in two other places:

* `ZInQKernel/Contrib/CloudB3RC53/Prints/Kolyvagin.lean:5–12, 28–37` states Kolyvagin's theorem with its own premise, names the passage from modularity to that premise as a gap (`ModularToWeakWeil`, `:79`), says of the old `IsModular` form that "its premise is not Kolyvagin's", and names Carayol's theorem for the level.
* `ZInQKernel/Contrib/OneProof/RC/Wiring/Leaves.lean:365–369` records "Atkin–Lehner/Carayol" as glue for the newform of level N(E).

The earlier AI page read on issue 83 (comment 6962416523, section 2) also concluded that this row relies on BCDT twice and is not an instance of Theorem 1 alone. The board row carries neither point.

Other observations on `hK`:

* Only the rank half is used. `kolyvaginRankOne_of_printed` (`Leaves.lean:79–80`) takes the first component, and `Finite (sha E)` is never used. The manuscript's "finite Ш, hence Ш[2] = 0" (L1111–1113) is replaced in Lean by a counting argument (`ZInQKernel/Contrib/PoleRC/DescentM.lean:367`).
* `hB` and `hK` only ever appear composed, as `KolyvaginRankOne` (`ZInQKernel/Contrib/PoleRC/CRM.lean:54`): analytic rank 1 implies rank 1, for every elliptic curve over ℚ. The predicate `IsModular` cancels. This composed statement is exactly "BCDT Theorem A and Kolyvagin's Theorem 1", by route A.
* The print is a preprint and a survey (section 6.2). The docstring notes the first point.

## 7. The proof of pole completeness from the four hypotheses

`poleCompleteness_of_restrictedConverseGenuine_casselsTatePairing` (`CasselsTatePairing.lean:499–503`) is a composition. I traced it:

1. `hCT` gives the square property of the curves E_ℓ (`CasselsTatePairing.lean:484`, from `:409`).
2. The square property gives Lemma 5.4 at the curves E_ℓ: #SelM ℓ = 8 implies `SelmerCorankOne (curve ℓ)` (`Lemma54FromCasselsTate.lean:83`). It uses three proved facts: Mordell–Weil for E_ℓ (`PoleRC/MordellWeilM.lean:297`), #E_ℓ(ℚ)[2] = 4, and the Kummer identification #Sel₂(E_ℓ/ℚ) = #SelM ℓ (`KummerSelmerMProof.lean:22`).
3. `hB` and `hK` give `KolyvaginRankOne` (`Leaves.lean:79`).
4. `crm_of_restrictedConverse_proved` (`MordellWeilM.lean:337`) chains them: #SelM ℓ = 8, so Selmer corank one, so by `hRC` analytic rank one, so rank one, so a point of infinite order, so every Selmer class is the class of a rational point (the proved 2-descent, `DescentM.lean:367`).
5. `poleCompleteness_of_crm` (`Reduction.lean:23`) applies this at n and at nθ from the proved simultaneous construction (`PoleCompletenessFromRCGenuine.lean:49`) and produces the eleven witnesses.

Nothing beyond the four hypotheses enters. A static scan found no `axiom` declaration anywhere under `ZInQKernel/` and no `sorry` in the files of this chain. I did not compile anything; the axiom check is the hosted workflow's (`.github/workflows/main-build-cache.yml:8–9, 187–194`).

How each hypothesis is used:

* `hRC` at exactly two parameters per B.
* `hCT` only through the square property of the 2-primary part.
* `hB` only to feed `hK`.
* `hK` only for the rank.

So the four are somewhat stronger than the proof needs: `hRC` for all ℓ of corank one rather than those with #Sel₂ = 8, and `hK` with a finiteness conclusion that is unused.

Side check, outside the task: `ZInQ.PoleCompleteness` (`ZInQKernel/Hypotheses/Pole.lean:39–41`) and `polePoly` (`:23–31`) read as the manuscript's Theorem 5.2 (L1001–1004) and Q_pole (L976–982).

## 8. Concrete problems

| ID | Hypothesis | Problem | Where |
|---|---|---|---|
| F1 | `hK` | The premise `IsModular E` is not the print's premise (a weak Weil parametrization X₀(N) → E with N the conductor, p. 3). The stated bridge, "Shimura's construction and Faltings' isogeny theorem, the step BCDT cite for (2) ⇒ (6)", starts from condition (2), which `IsModular` does not give. The derivation needs BCDT Theorem A as a second input (then the premise is idle), or Atkin–Lehner–Li theory and Carayol's theorem. | `docs/one-proof/kinds.tsv:34`; `docs/one-proof/OPEN.md:644, 654–666`; `ZInQKernel/Contrib/OneProof/PoleS12/Leaves.lean:57–72`; `ZInQKernel/OneProof/Main.lean:16–17, 211`. The repository's own statement of the gap: `ZInQKernel/Contrib/CloudB3RC53/Prints/Kolyvagin.lean:5–12, 28–37, 79`; `ZInQKernel/Contrib/OneProof/RC/Wiring/Leaves.lean:365–369` |
| F2 | `hRC` | Not a mismatch, but the main caveat: the statement is unproved and unpublished, its source is an AI-developed manuscript without human peer review, and it stands for about 8,100 of the manuscript's 11,259 lines. The Lean reduction on issue 83 is not used by the headline and still has "conclusion-shaped" leaves. | `ZInQKernel/OneProof/Main.lean:216`; `ZInQKernel/Contrib/OneProof/SelmerTwoPower.lean:217–218`; `diophantine_zq.tex:1005–1017, 11251–11258`; `ZInQKernel/Contrib/OneProof/RC/Wiring/Leaves.lean:95–121, 490` |
| F3 | `hCT` | The locator is a sentence of the Introduction that reports Cassels' theorem. Poonen–Stoll do not prove the nondegeneracy half (they attribute it to Cassels and Tate). They do recover alternation for elliptic curves (Remarks after Corollary 12). Cassels 1962 is unread, by the project and by me. The row is rated `published`, LEAF, on AI readings only. The board gives only the author-version page; the journal page is 1110. | `docs/one-proof/kinds.tsv:32`; `docs/one-proof/OPEN.md:606–609`, against `OPEN.md:19–22, 29–30`; `ZInQKernel/Contrib/OneProof/CasselsTatePairing.lean:82–89`; `docs/research/cassels-tate-pairing.md:30–32, 57`; `docs/research/lem54-ct-check.md:59–60` |
| F4 | `hB` | Label inconsistency: the board classes the row as a consequence, GLUE, while the headline's docstrings and the module header call it a "printed leaf". | `ZInQKernel/OneProof/Main.lean:15–16, 210–211`; `ZInQKernel/Contrib/OneProof/PoleS12/Leaves.lean:13, 45`; against `docs/one-proof/kinds.tsv:33` |
| F5 | `hK`, `hB` | The conclusion `Finite (sha E)` is never used, and `hB` is used only to feed `hK`. The pair could be one statement, `KolyvaginRankOne`, whose derivation is route A. | `ZInQKernel/Contrib/OneProof/PoleS12/Leaves.lean:72, 79–80`; `ZInQKernel/Contrib/PoleRC/CRM.lean:54` |
| F6 | all four | No statement check is recorded: `reviews.tsv` has one data row, for another field, and OPEN.md shows "Human readings recorded: none" for each of the four. The AI readings exist only in `docs/research/` and in an issue comment. | `docs/one-proof/reviews.tsv:2`; `docs/one-proof/OPEN.md:590, 609, 625, 647` |
| F7 | all four | OPEN.md's counts ("Strict count: 5 published / 24 glue", "By kind") cover the 29 hypotheses of the H part only. The opening line names the four by field name, and line 580 says they are outside the counts, but only the section at the end says what they are. A reader who stops at the counts does not learn that the manuscript's own unproved Theorem 5.3 is outside them. | `docs/one-proof/OPEN.md:16–23, 580, 585–591` |
| F8 | `hRC`, `hK` | For information: `AnalyticRankOne` includes the existence of the entire continuation, so `hRC` asserts it for the curves it covers. This agrees with the manuscript's usage. | `ZInQKernel/Hypotheses/PoleManuscript.lean:71–73` |
| F9 | `hRC`, `hB`, `hK` | For information: the statements rest on Mathlib's 2026 definition of the L-function of a Weierstrass curve (minimal model by choice, junk values for non-summable series) and on the vendored Tau Ceti cohomology. I read these definitions and found the standard objects, but no reading of them is recorded. | Mathlib at `56a005855ea1`, `Mathlib/AlgebraicGeometry/EllipticCurve/LFunction.lean:43–85`; `ZInQKernel/Contrib/TauCeti/AlgebraicGeometry/EllipticCurve/GaloisCohomology/Selmer.lean:123, 170` |

None of these makes a hypothesis false. F1 is an error in the recorded derivation of a row. F2 is the limit of what the theorem establishes. F3, F4, F6 and F7 are about what the board and the docstrings claim.

Where each is filed: F1 and F5 in #127, F2 in #124, F3 in #125, F4 in #126, F6 and F7 in #128. F8 and F9 are recorded in the index, #129. The issues give the replacement text for the board rows and docstrings, which are the integrator's to change.

## 9. What I could not verify

1. **Compilation and axioms.** I did not build, by instruction. I rely on the hosted workflow for both. My static scan (no `axiom`, no `sorry` in the chain) is not a substitute.
2. **The proof of Theorem 5.3.** I did not read the manuscript's proof (L1760–5744, L6825–10935) and have no opinion on its correctness, or on whether it proves the statement at the generality of `hRC`. I did not search the literature for comparable theorems.
3. **Cassels 1962**, the primary source of `hCT`, is unread. The statement is checked against Poonen–Stoll's report of it and against Milne.
4. **Journal pages of BCDT.** The AMS server returned 403 for the journal PDF. Theorem A on "p. 843" and the page of conditions (1)–(6) in J. Amer. Math. Soc. 14 are UNVERIFIED. The author manuscript, which the manuscript cites, was read (pp. 1–4).
5. **The journal print of Poonen–Stoll.** Page 1110 is taken from arXiv:math/9911267v1, which is typeset with the Annals page numbers. I did not see the journal print itself.
6. **Kolyvagin.** I read printed pp. 1–5 and the references (pp. 13–15). I did not read sections 2 onward, his papers [6]–[8], or Gross–Zagier, Waldspurger, Bump–Friedberg–Hoffstein and Murty–Murty. I believe this preprint is the text of Kolyvagin's address to the 1990 International Congress, later printed in its proceedings; that is from memory and UNVERIFIED.
7. **Theorems named in the derivations of section 6.4.** Atkin–Lehner–Li theory, Carayol's theorem, Shimura's construction, the Eichler–Shimura relation and Faltings' isogeny theorem are named from general knowledge; I read none of them, and I give no locators. That BCDT attribute their implications to Carayol, Shimura and Faltings is verified on p. 3 of the author manuscript; their reference list was not read. The computation in route B, step 1, and the nebentypus argument in section 5.3 are my own and were not checked against a print.
8. **Mathlib.** I read `EllipticCurve/LFunction.lean`, `EllipticCurve/Reduction.lean`, `ArithmeticFunction/LFunction.lean`, and the definitions of `CuspForm`, `IsZeroAt`, `qExpansion`, `Gamma0`, the coercion to GL₂(ℝ), `analyticOrderAt` and `LSeries`, at the pinned commit, fetched from GitHub. I did not read the group law on points, `SeparableClosure`, the Krull topology, the body of `IsCusp`, `Periodic.qParam`, `Module.rank`, or the adic completions. I checked the criterion for split multiplicative reduction only for equations with a₁ = a₃ = 0, not in residue characteristics 2 and 3.
9. **Tau Ceti.** I read the definitions of the coefficient modules, H¹, the pullback maps, the map of Galois groups, the restriction maps, Ш, the Selmer groups and the Selmer structure. I did not read `ForcedDiscrete`, the point map along a field map, or the proof that the groups do not depend on the embeddings.
10. **The rest of the Lean proof.** The simultaneous construction, the local conditions and the descent (`ZInQKernel/Contrib/PoleRC/`, `ZInQKernel/Contrib/OneProof/PoleS12/`) are outside the four hypotheses, and I did not audit them. I did not audit `SixContactMin` or the headline assembly.
11. **The equivalence of BCDT's cusp-form definition with Mathlib's** (bounded |f|²(Im z)^k against vanishing at every cusp) is a standard fact that I did not check against a print.

## 10. Sources read

| Source | Copy | Pages read | SHA-256 (first 16 hex digits) |
|---|---|---|---|
| Poonen–Stoll, author's version | `https://math.mit.edu/~poonen/papers/sha.pdf`, 32 pp., dated November 6, 1998, minor correction August 23, 2014 | 1–6, 10–14 | `3b9a619423358bc8` |
| Poonen–Stoll, arXiv | `https://arxiv.org/pdf/math/9911267` (v1, 1 Nov 1999), Annals pagination | 1109–1110 | `a7f6b91f8dbc38d8` |
| BCDT, author manuscript | `https://virtualmath1.stanford.edu/~conrad/papers/tswfinal.pdf`, 79 pp. | 1–4 | `13043cf6e9043a69` |
| Kolyvagin, MPI/90-69 | `https://archive.mpim-bonn.mpg.de/id/eprint/325/1/preprint_1990_69.pdf`, scan, 17 PDF pages | printed 1–5, 13–15 | `bacdf23d05d5120d` |
| Milne, *Arithmetic Duality Theorems*, 2nd ed. | `https://www.jmilne.org/math/Books/ADTnot.pdf`, 347 pp., file dated 1 July 2006 | 81–82, 92–93 | `2c6195ec76a974f3` |
| Manuscript | `diophantine_zq.tex` in the repository | L955–1139, L1760–1829, L6590–6827, bibliography, L11251–11259 | at the commit above |
| Mathlib | `leanprover-community/mathlib4` at `56a005855ea17e0b0958f73ec801ae140b0a1679` | files named in section 9, item 8 | at that commit |

Verbatim quotations of the same passages are already in the repository or on the fork, and I compared them with the PDFs above:

* `docs/research/cassels-tate-pairing.md` (Poonen–Stoll: abstract, Introduction, Remarks after Corollary 12; Milne: Theorems 6.13 (a) and 6.26 (a), p. 81, the Notes, footnote 17). They agree with the PDFs. Milne's print has a stray closing parenthesis in Theorem 6.13 (a). The arXiv copy of Poonen–Stoll differs from the author's version in two spellings in the abstract.
* Issue 83, comment 6962416523 (BCDT: Theorem A, condition (2), the definition of "modular"; Kolyvagin: Theorem 1, the modularity assumption, Theorems 3–5). They agree with the PDFs.
