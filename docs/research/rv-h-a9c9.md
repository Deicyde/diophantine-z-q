# rv-h-a9c9: second review of A9's Milne paragraph and C9's Li–Shimura sentence

Task rv-h-a9c9, 2026-11-11. Branch `wip/rv-h-a9c9` (from `origin/wip/integrate-w15`).
Object: the two passages of the frozen 11/5 manuscript (`diophantine_zq.tex`, commit `97cec7fd`,
"N5 L…") that had one model review (rv-h-trust §2.1):

- **A9**, N5 L564-577: polarizable tori, Hodge endomorphisms algebraic and defined over `ℚ̄`, and
  the centralizer computation giving `End⁰(A_ℚ̄) ∈ {B, M₂(k)}`.
- **C9**, N5 L768-774: absorb the finite twist, pass to the primitive newform `f`, Li's Fricke
  formula, Shimura 1973 Thm 1, "`r₅` is a constituent of `V₅(A_f)`", "this duality preserves the
  conductor".

Labels: **VERIFIED** (checked here by exact or high-precision computation, scripts in
`scratch/rv-h-a9c9/`, or by a complete argument written out here); **STANDARD** (published
theorem, reference given; locators UNVERIFIED unless stated); **AUDIT-READ** (the upstream
theorem-application audit under `docs/theorem-application-audit/evidence/` reports reading the page
scan; I had no copy of the source); **SPECULATIVE**. Log: `scratch/rv-h-a9c9/log.md`.

Order of work: §§1-2 (own verdicts) were written and committed before I read rv-h-trust's
treatment of these passages; §3 is the comparison.

## 1. A9: the Milne paragraph (N5 L564-577)

### 1.1 What the paragraph claims

(a) Polarizable complex tori are abelian varieties, and analytic homomorphisms between them are
algebraic (cited: Milne, *Abelian varieties*, course notes v2.00, Part I, Thms 2.8-2.9).
(b) Hence `End⁰(A_ℂ)` equals the algebra of rational Hodge endomorphisms of `H₁(A,ℚ)`, i.e. the
commutant of the complex structure `J`.
(c) Every element of `End(A_ℂ)` is defined over `ℚ̄`: for `τ ∈ Aut(ℂ/ℚ̄)`, `φ` and `ᵗφ` agree on
torsion, which is Zariski dense.
(d) `H₁(A,ℚ) ≅ B` with `B` acting on the left; `J` is right multiplication by some `J ∈ B ⊗ ℝ`,
`J² = −1`; in `End_ℚ(B) = B ⊗ B^op`, commuting with `J` forces each right coefficient to commute
with `J`; the rational centralizer `Z_B(J)` is `ℚ` or an imaginary quadratic `k`; hence
`End⁰(A_ℚ̄) = B` or `M₂(k)`.

### 1.2 Checks

1. **(d), the algebra.** VERIFIED (argument and computation).
   - `B ⊗ B^op → End_ℚ(B)`, `b ⊗ c ↦ (x ↦ bxc)`, is an isomorphism (`B` central simple); it stays
     one after `⊗ℝ`. Write an element as `Σ bᵢ ⊗ cᵢ` with `(bᵢ)` a fixed ℚ-basis of `B`. It
     commutes with `R_J` iff `Σ bᵢ ⊗ [cᵢ, J] = 0` in `B_ℝ ⊗ B_ℝ^op`, iff every `[cᵢ, J] = 0`
     (the `bᵢ` stay an ℝ-basis). So the commutant is `B ⊗ Z_B(J)^op`.
   - `Z_{B_ℝ}(J) = ℝ[J] ≅ ℂ` (`B_ℝ ≅ M₂(ℝ)`, `J` has eigenvalues `±i`). So `Z_B(J)` is a
     subfield of `B` of degree ≤ 2. A non-central `c = a + bJ` (`a, b ∈ ℝ`, `b ≠ 0`) satisfies
     `x² − 2ax + a² + b²`, of discriminant `−4b² < 0`, and this is its rational reduced
     characteristic polynomial: `Z_B(J)` is `ℚ` or imaginary quadratic. A quadratic `k ⊂ B` is a
     maximal subfield, so splits `B`: `B ⊗ k ≅ M₂(k)`.
   - Computation (`a9_centralizer.py`): `B = (−1,3)_ℚ` is ramified exactly at 2, 3 (Hilbert
     symbols), so has discriminant 6; `L(B)R(B)` spans `M₄(ℚ)` (rank 16); the ℚ-dimension of the
     commutant of `R_J` is 4 for a generic `J = √10 i + j + √2 k`, and 8 for `J = 2i + j`
     (`k = ℚ(i)`) and for `J = (3i+j+k)/√3` (`k = ℚ(√−3)`); in the last two cases the commutant
     contains a nonzero nilpotent, so it is `M₂(k)`, not a division algebra.
   - The paragraph proves equality (the full commutant), not just an inclusion, and the
     equality is what A8 and A10 use.
2. **(a)-(b), the analytic bridge.** STANDARD. Riemann's theorem (a complex torus with a Riemann
   form is projective) and the full faithfulness of `A ↦ A(ℂ)` (GAGA, or Chow): Mumford,
   *Abelian varieties* (1970), §§1-3; Serre, GAGA (1956); Milne in Cornell–Silverman (1986).
   N5's citation is to course notes, which are [P]; the upstream audit reports that Part I
   Thms 2.8-2.9, printed p.14, state exactly (a) (AUDIT-READ,
   `parallel-geometry-report.md` L97). Note: N5's bibliography entry for `milne-av` names
   only "Part I, Theorem 12.1(a)" (N5 L11024-11026), the locator of its other use (L10968); the
   in-text locator at L564 is the one to keep. Cosmetic.
3. **(c), descent `ℂ → ℚ̄`.** VERIFIED as an argument, with one standard step left implicit.
   For `τ ∈ Aut(ℂ/ℚ̄)` and a torsion point `P`, `P` and `φ(P)` lie in `A(ℚ̄)`, so
   `(ᵗφ)(P) = τ(φ(τ⁻¹P)) = φ(P)`; torsion is dense, so `ᵗφ = φ`. The implicit step, "a
   `ℂ`-morphism between `ℚ̄`-varieties fixed by `Aut(ℂ/ℚ̄)` is defined over `ℚ̄`", is standard
   (`ℚ̄` is the fixed field of `Aut(ℂ/ℚ̄)` and is perfect; Weil descent of the graph). A cleaner
   standard citation: for abelian varieties over an algebraically closed `k` and any extension
   `K/k`, `Hom(A,B) → Hom(A_K,B_K)` is bijective (rigidity; e.g. Conrad, *Chow's K/k-image and
   K/k-trace*, Enseign. Math. 52 (2006), §3; locator UNVERIFIED).
4. **The hypotheses the paragraph needs from earlier steps.** That `B` (an order of it) acts on
   `A_ℚ̄` faithfully and unitally, so `H₁(A,ℚ)` is a free left `B`-module of rank one (dimension
   count, `B` a division algebra). That is the QM structure of the fibre (A1-A7, outside this
   review).

### 1.3 Attempted refutations (none succeeded)

- *A real quadratic centralizer.* Impossible: `Z_B(J) ⊂ ℝ[J]` and a non-central rational element
  of `ℝ[J]` has negative discriminant (above).
- *A larger commutant from cancellation between left coefficients.* Impossible: the left basis
  stays ℝ-independent; the computation confirms dimension exactly 4 or 8.
- *`End⁰(A_ℂ) ≠ End⁰(A_ℚ̄)`.* Excluded by (c).
- *Other algebras (`M₂(ℚ)`, `ℚ × ℚ`, a quartic CM field).* All excluded: the commutant always
  contains `L(B)`, and it is `B ⊗ Z_B(J)^op`.

### 1.4 Verdict on A9

**Holds as stated.** Repairs, both citation-level:
- R-A9-1: replace the course-notes citation by a refereed one (Mumford 1970 §§1-3 with GAGA, or
  Milne 1986 in Cornell–Silverman); fix the `milne-av` bibliography locator.
- R-A9-2: name the descent fact in (c) (fixed by `Aut(ℂ/ℚ̄)` ⇒ defined over `ℚ̄`, or the
  rigidity bijection for abelian varieties over algebraically closed fields).

## 2. C9: the Li–Shimura sentence (N5 L768-774)

### 2.1 What the sentence claims, and what later steps use

From C8: `r₅ ≅ ρ_g ⊗ ψ` (Tate normalization, `g` a weight-2 cuspidal eigenform, `ψ` finite).
C9: absorb `ψ`, take the primitive newform `f` (level `N`, nebentypus `ε`, coefficient field
`K_f`); Li's Fricke formula makes `V_f = span{f^σ}` Fricke-stable; Shimura 1973 Thm 1 (quotient
construction, Euler factors) gives: `r₅` is a constituent of `V₅(A_f) ⊗ E`, equivalently `r₅^∨`
is a constituent of `H¹`; and the conductor of `V^∨` equals that of `V`.

Used later: C10 (trace of `r₅(Frob_p)` is `ι₅(a_p(f))` for `p ∤ N·T·15`; transport to `ℓ = 3`),
D5 (Carayol: `v_p(N)` equals the conductor exponent of `ρ_{f,λ}`, and the conductor of `r_ℓ` is
bounded locally; this needs only that `r_ℓ` and `ρ_{f,λ}` have the same conductor, up to
duality), E1 (Faltings' Hom theorem applied to `V₅(A) ⊃ r₅ ⊂ V₅(J₁(N))`).

### 2.2 Checks

1. **Absorbing the twist; "primitive newform".** STANDARD, with a wording point.
   - Twisting by a Dirichlet character `ψ` of conductor `m` sends a cusp form of level `M` to
     level dividing `Mm²` and multiplies `a_n` by `ψ(n)`: Shimura, *Introduction…* (1971),
     Prop. 3.64; Shimura 1973 §4, (4.1) (AUDIT-READ, `parallel-galois-height-report.md`).
     In the Tate normalization `ρ_g ⊗ ψ` and `ρ_{g⊗ψ}` have the same Frobenius traces
     `a_p(g)ψ(p)` at good `p`.
   - Wording: if `g` were not normalized (`a₁ = 0`, e.g. `g(z) = f₁(3z)` with `f₁` = 11a and
     `ψ` mod 3) the twist is 0. Pan's "cuspidal eigenform" is normalized (it has an attached
     Galois representation via `a₁ = 1`), so `a₁(g⊗ψ) = 1` and the twist is nonzero; or argue
     with eigenvalue systems at `p ∤ Mm`. Then strong multiplicity one (Li 1975 Thm 5,
     Miyake Thm 4.6.19) gives a unique newform `f` with those eigenvalues. "Primitive" is Li's
     term for a normalized newform; it must **not** be read as "twist-minimal" (Atkin–Li), or
     `r₅` would only be a twist of `ρ_f`. Cosmetic (R-C9-3).
2. **Li's Fricke formula ⇒ the conjugate span is Fricke-stable.** VERIFIED (argument), STANDARD
   (theorem), numerically checked.
   - Li: for a normalized newform `F` of level `M`, any character, `F|H_M = γ·F|K` with
     `F|K(τ) = \overline{F(−\bar τ)}`, i.e. `Σ \bar a_n q^n` (Li 1975 p.296, paragraph before
     Lemma 6, AUDIT-READ; also Atkin–Li 1978 Thm 1.1). `γ ≠ 0` since `H_M` is invertible.
   - `F|K = c(F)`, `c` complex conjugation in `Aut(ℂ)`, and every `f^σ` is a newform of level `N`
     (Galois conjugation preserves newness: Shimura 1971 Thm 3.52 rationality of the old/new
     decomposition, with strong multiplicity one). So `f^σ|H_N = γ_σ f^{cσ} ∈ V_f`: `V_f` is
     stable, with no hypothesis on `ε` or `K_f`.
   - Computation (`c9_li_fricke.py`, output `c9_li_fricke.out`): 30 (newform, embedding) pairs,
     weight 2, nontrivial even character of order 2-14, `N = 13..29`; direct evaluation of
     `N(Nz)^{-2} f(−1/(Nz))` and of `Σ \bar a_n q^n` (500 terms) at three points. The ratio is
     constant to `1.5·10⁻⁹⁵`, has modulus 1 to `2·10⁻⁹⁶`, and equals PARI's
     `mfatkineigenvalues`. This is a sample check of a published theorem, not a proof.
   - Shimura's map is `h(z) ↦ h(−1/(Nz))/z²`, which is `N` times Li's `|₂H_N`; stability is the
     same. (That this is Shimura's hypothesis is AUDIT-READ, Shimura 1973 Thm 1 p.526.)
3. **"Shimura … therefore show that `r₅` is a constituent of `V₅(A_f)`."** Holds; the stated
   reason is incomplete. VERIFIED (counterexample to the bare inference) and STANDARD (repair).
   - The zeta identity `L(A_f, s) ≐ Π_σ L(f^σ, s)` controls only the *total* characteristic
     polynomial of `Frob_p` on `V₅(A_f)`. Divisibility of characteristic polynomials at every
     element does not make a representation a constituent: for `G = ℤ/2 × ℤ/2`, `V = 1 ⊕ a ⊕ b`,
     `U = ab`, `charpoly_U(g) | charpoly_V(g)` for all `g` while `⟨U, V⟩ = 0`
     (`c9_charpoly_divisibility.py`).
   - What does give it (STANDARD): Shimura's Thm 1 also gives the `K_f`-action on `A_f` with
     `θ(T_n) = a_n` (unconditional part, AUDIT-READ); `V_ℓ(A_f)` is free of rank 2 over
     `K_f ⊗ ℚ_ℓ` (Shimura 1971 §7, Ribet 1977 / Diamond–Im 1995 §12.5); the Eichler–Shimura
     relation `T_p = Frob_p + p⟨p⟩Frob_p⁻¹` on `J₁(N)` (Shimura 1971 Thm 7.9; Diamond–Shurman
     GTM 228, Thm 8.7.2 and §9.5; locators UNVERIFIED) gives `tr(Frob_p | V_λ) = a_p` over
     `K_{f,λ}`. Then `V₅(A_f) ⊗ E = ⊕_{τ: K_f → E} V_τ`, and `V_{ι₅|K_f}` has the traces of `r₅`
     at almost all `p`; both are semisimple (Faltings 1983 Satz 3; `r₅` irreducible), so
     Chebotarev and Brauer–Nesbitt give `r₅ ≅ V_{ι₅}`. Alternatively: the zeta identity plus the
     existence of every `ρ_{f^σ, ι}` (Deligne/Shimura) plus Brauer–Nesbitt, which is the route the
     upstream audit takes (`parallel-galois-height-report.md`, "A011").
   - Either way the Fricke condition is needed only for Shimura's zeta identity; the `K_f`-linear
     route does not use it, so Li's formula is a convenience, not a necessity.
   - Normalization: `V₅(A_f)` has Hodge–Tate weights `{0, −1}` (cyclotomic weight −1), the same as
     `r₅` in C8's Tate normalization; `r₅^∨` (weights `{0, 1}`) is *not* a constituent of
     `V₅(A_f)`. So "constituent of the Tate module" is the right side, given C8's repairs. Whether
     Eichler–Shimura's convention yields traces `a_p` or `\bar a_p = ε(p)⁻¹a_p` on the Tate module
     does not matter: `\bar f = f^c` is in the orbit, so both `ρ_f` and `ρ_{\bar f}` occur.
4. **"This duality preserves the conductor."** VERIFIED (argument), STANDARD. For `ℓ ≠ p`: the
   Swan conductor is computed on wild inertia, which acts through a finite group, so the break
   decomposition of `V^∨` is the dual of that of `V`; the tame part is
   `dim V − dim (ker N)^{I}`, and `N^∨ = −N^t`, `I` acting through a finite quotient, gives
   equal dimensions (Serre, *Corps locaux* VI §2; Deligne 1973, §8; uncited in N5).

### 2.3 Attempted refutations (none succeeded)

- *Fricke-stability fails for nontrivial nebentypus* (single forms are not Fricke eigenforms).
  It holds for the span: the image of `f^σ` is a multiple of `f^{cσ}`; 30 samples agree.
- *Conjugates of a newform drop level.* No: Galois-stability of old/new spaces and strong
  multiplicity one.
- *Wrong side of the duality.* Excluded by the Hodge–Tate weights and by C8's Tate normalization.
- *The Euler-factor inference.* The bare inference is invalid in general (Klein-four example),
  but the conclusion follows from standard facts listed in 2.2.3. No refutation of the claim.

### 2.4 Verdict on C9

**Holds after the listed repairs** (all expository or citation-level; no mathematical change):
- R-C9-1 (the substantive one): replace "Shimura's … Euler-factor identity therefore show" by
  the `K_f`-linear Eichler–Shimura statement (or zeta identity + existence of all `ρ_{f^σ}`)
  followed by Chebotarev, Brauer–Nesbitt and Faltings' semisimplicity.
- R-C9-2: cite the Galois-stability of the newform property (needed to apply Li to every
  `f^σ`) and the conductor invariance under duality.
- R-C9-3: "primitive newform" in Li's sense (normalized newform), applied to a normalized
  eigenform; not "twist-minimal".

## 3. Comparison with rv-h-trust

rv-h-trust §2.1 (read after §§1-2 were committed) treats both passages in a few lines.

| Point | rv-h-trust §2.1 | here |
| --- | --- | --- |
| A9 descent `ℂ → ℚ̄` | correct (torsion density) | agree; the "fixed ⇒ defined over `ℚ̄`" step is named (R-A9-2) |
| A9 centralizer | `B ⊗ Z_B(J)`, `Z_B(J) = ℚ` or imaginary quadratic: correct | agree; full argument, imaginarity proof, and an exact computation for three `J` |
| A9 analytic bridge | not discussed (citation status in h-trust A9) | standard; the `milne-av` bibliography entry names the wrong theorem (12.1(a)) |
| C9 Shimura hypothesis | correct *provided* Thm 1 asks for a Hecke- and Fricke-stable span (UNVERIFIED) | the conjugate span is Hecke-, diamond-, `Aut(ℂ)`- and Fricke-stable, so any of these hypotheses is met; the upstream audit reports the Fricke condition on p.526 (AUDIT-READ); the `K_f`-linear route avoids it entirely |
| C9 Li's formula | assumed | argument for every conjugate (newness is Galois-stable), 30-sample numerical check |
| C9 constituent | "Eichler–Shimura, Chebotarev and Faltings place `r₅` in `V₅(A_f)`" | agree; adds that the zeta identity alone does not suffice (Klein-four example), so the `K_f`-linear Eichler–Shimura statement is the needed input (R-C9-1) |
| C9 duality / conductor | not discussed | weights pick the Tate side; conductor invariance proved (R-C9-2) |
| C9 twist / "primitive" | twist and Li's newform theorem as uncited inputs | agree; adds the normalization and "primitive ≠ twist-minimal" wording (R-C9-3) |

No disagreement on any verdict. This review is more detailed on C9 and resolves rv-h-trust's
single open provision.

## 4. Consequence for H's trust statement

- A9's Milne paragraph and C9's Li–Shimura sentence now have **two model reviews** (rv-h-trust,
  rv-h-a9c9). With C3 (rv-h-trust, rv-h-c3) and C8 (Astra, rv-h-c8), every passage new in the
  11/5 text has two model reviews. Item (vii) of h-trust's list of single-review passages can be
  closed. These remain model reviews, not human refereeing.
- Statuses unchanged: A9 **[M]** (citation still [P] until R-A9-1); C9 **[R]** with application
  **[M]**. The "To check" for Shimura 1973 Thm 1 in h-trust C9 and its §2.4 item 4 can read: met
  for the conjugate span whatever the exact form (Hecke, `Aut(ℂ)` or Fricke stability), the
  Fricke form being AUDIT-READ; and not needed on the `K_f`-linear Eichler–Shimura route.
- Suggested additions to h-trust C9's supplier list: the `K_f`-linear Eichler–Shimura relation
  (`V_ℓ(A_f)` free of rank 2 over `K_f ⊗ ℚ_ℓ`, `tr Frob_p = a_p`), Galois-stability of newforms,
  and conductor invariance under duality. To A9's: the descent fact (R-A9-2).
- Nothing here changes the Lean side (`ZInQ.SixContactMin` remains a hypothesis).

## 5. Next step

Read Shimura 1973 Thm 1 (p.526) and Li 1975 p.296 against a copy of the papers, to turn the two
AUDIT-READ items into VERIFIED locators; this is the only remaining open point here, and the
`K_f`-linear route (Shimura 1971 Thm 7.9 and §7.5) makes even that optional.
