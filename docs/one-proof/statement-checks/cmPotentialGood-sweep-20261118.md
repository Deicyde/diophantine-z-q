Recorded from the statement-check sweep of 2026-11-18: an AI-READ report written by an AI agent that the project runs (no person checked it), against OPEN.md commit `2895a9c195344cdbca2454ba9bf58d748a3a9ce5`. It clears no flag.

---

# Statement check: `cmPotentialGood`

Report in the format of `docs/one-proof/STATEMENT-CHECKS.md`. Evidence class: **AI-READ** (see the last fields).

## Field and commit

* Field: `OpenResearchLeaves65.cmPotentialGood` (bundle `HDec.HSyn.OpenResearchLeaves65`,
  `ZInQKernel/OneProof/H/TailZ91.lean` L66-67), whose type is `HDec.CMBranch.CMPotentialGood`
  (`ZInQKernel/Contrib/OneProof/CMBranch.lean` L99-109).
* Commit read (Lean, OPEN.md, kinds.tsv, manuscript): `2895a9c195344cdbca2454ba9bf58d748a3a9ce5`.
* kinds.tsv row: kind consequence, strict GLUE, flag pending-review. Source line: "diophantine_zq.tex
  L596-597 (uncited; reason given there: j integral); classical: Serre-Tate, Good reduction of abelian
  varieties, Ann. of Math. 88 (1968) (UNVERIFIED locator); Barquero-Sanchez et al. 2017 proof of Thm 1.3,
  p. 15 (upstream audit)". The Lean docstring adds "§6 Thm 7" and "Silverman, AEC VII.5.5 with the
  integrality of singular moduli".
* Manuscript, `diophantine_zq.tex` L596-597: "After a finite extension $E$ has everywhere good reduction,
  since its $j$-invariant is integral." L629-630 adds: "No bound for the degree of the auxiliary
  good-reduction extension enters the isogeny estimate."

## The Lean, unfolded

```lean
def CMPotentialGood : Prop :=
  ∀ (L : Type) [Field L] [NumberField L] (E : ZInQ.DefFaltings.AbVar L), E.dim = 1 →
    ∀ (k : Type) [Field k] [NumberField k] (R : Subring k), IsImagQuadOrder k R → IsCMBy E k R →
      ∃ (L₁ : Type) (_ : Field L₁) (_ : NumberField L₁) (_ : Algebra L L₁)
        (𝒢 : ZInQ.DefFaltings.GroupModel E L₁), IsProper 𝒢.G.hom
```

* The hypotheses are those of `cmjDegree`. `E` is an abelian variety of dimension 1 over the number field
  `L`, i.e. an elliptic curve. In the project's definition, `ZInQ.DefFaltings.AbVar = PkgI3.AbVar`
  (`ZInQKernel/Contrib/HeightBC/G0StableBC.lean` L18) is a group scheme over `Spec L` that is proper, smooth
  and geometrically integral (`ZInQKernel/HDecomp/Objects.lean` L160-168), and `dim` is the Krull dimension
  (L181).
* `IsImagQuadOrder k R` (`CMBranch.lean` L34-38): `R` is an order of the imaginary quadratic field `k`. The
  conductor is the index `[𝓞_k : R]`, nonzero (`ZInQKernel/HDecomp/QM/Leaves.lean` L147-149).
* `IsCMBy E k R` (`CMBranch.lean` L60-64): there is a ring isomorphism from the group-scheme endomorphism
  ring of `E ×_L L̄` onto `R`, where `L̄` is Mathlib's `AlgebraicClosure L` and the product is composition
  (`Objects.lean` L183-240, L374-382). So `E` has CM over `L̄`. The endomorphisms need not be defined over
  `L`.
* `∃ L₁ (Field, NumberField, Algebra L L₁)`: a number field `L₁` with a field map `L → L₁`. Since both are
  finite over `ℚ`, `L₁/L` is finite. No bound on `[L₁ : L]` is asserted.
* `ZInQ.DefFaltings.GroupModel E L₁` (`ZInQKernel/HDecomp/Faltings/Models.lean` L29-43; the name resolves to
  this kernel structure) has these fields:
  * `G`: a scheme over `Spec 𝓞_{L₁}`.
  * `grp`: a group-object structure on `G` over `Spec 𝓞_{L₁}`, i.e. a group scheme.
  * `smooth`, `separated`, `qc`: `G → Spec 𝓞_{L₁}` is smooth, separated and quasi-compact.
  * `gen`: an isomorphism of `L₁`-schemes from the generic fibre to `E_{L₁}`. The generic fibre
    `genericFibre L₁ G` is the pullback along `Spec L₁ → Spec 𝓞_{L₁}` (Models.lean L24-27).
  * `gen_hom`: `gen` is a homomorphism for the group structure transported to the generic fibre.
* `IsProper 𝒢.G.hom` (Mathlib at revision `56a005855ea17e0b0958f73ec801ae140b0a1679`,
  `Mathlib/AlgebraicGeometry/Morphisms/Proper.lean` L39-41): separated, universally closed and locally of
  finite type. Universal closedness implies quasi-compactness.

In words: over some finite extension `L₁` of `L`, `E_{L₁}` is the generic fibre, as a group scheme, of a
smooth proper group scheme over `𝓞_{L₁}`. This is exactly an abelian scheme in the sense of the print below
(Milne, footnote 5), that is, good reduction at every finite prime of `L₁`, all from one model. The Lean
does not require `𝒢` to be a Néron model or to have connected fibres. An abelian scheme has both
properties, but neither is needed here.

## Edition, page, display

* Primary print: J. S. Milne, *Complex Multiplication*, course notes v0.10 (July 14, 2020):
  * Proposition 7.12, p. 55.
  * The definitions it uses: good reduction and footnote 5 (abelian scheme) on p. 49; potential good
    reduction on p. 51; complex multiplication over `k` on p. 52.
  * Further results: Theorem 6.12 (Néron criterion) and Corollary 6.13, p. 51; Corollary 6.6 (uniqueness of
    the abelian-scheme extension), p. 49; Corollary 6.14 (isogeny invariance), pp. 51-52.
* For the manuscript's own reason ("its j-invariant is integral"):
  * K. Rubin, *Elliptic curves with complex multiplication and the conjecture of Birch and
    Swinnerton-Dyer*, lecture notes (Arizona Winter School 1999 archive copy, 68 pp.; a version is printed
    in LNM 1716, Springer 1999, but I did not compare the numbering). From these notes: §3, Lemma 3.2(i),
    p. 7; §4, p. 12 (the convention at a prime of a number field); §5, Definition 5.1 and Proposition 5.3,
    p. 15; Theorem 5.7, p. 16.
  * A. V. Sutherland, MIT 18.783 (Spring 2021), Lecture 20, Corollary 20.13, p. 6.

## Copy

* Milne: the author's PDF from his website.
* Rubin: the PDF in the Arizona Winter School archive.
* Sutherland: the MIT OpenCourseWare PDF.
* URLs and SHA-256 hashes are under Sources.

## Quote

* Milne, p. 55: "PROPOSITION 7.12 Let A be an abelian variety over a number field k with complex
  multiplication. Then A has potential good reduction at all finite primes of k." The proof begins:
  "After possibly extending k, we may suppose that A has complex multiplication by E over k."
* Milne, p. 49: "Let R be a discrete valuation ring with field of fractions K and residue field k. We say
  that an abelian variety over K has good reduction if it is the generic fibre of an abelian scheme A over
  R". Footnote 5: "An abelian scheme over a scheme S is a smooth proper scheme over S together with a group
  structure."
* Milne, p. 51: "An abelian variety over K is said to have potential good reduction if it acquires good
  reduction over a finite extension of K."
* Milne, p. 52, where (46) is `[End⁰(A) : Q]_red ≤ 2 dim A`: "When equality holds in (46), we say that A has
  complex multiplication over k".
* Rubin, p. 7: "We say that E has potentially good reduction if there is a finite extension F′ of F such that
  E has good reduction over F′. Lemma 3.2. (i) E has potentially good reduction if and only if j(E) ∈ O."
* Rubin, p. 16: "Theorem 5.7. Suppose F is a finite extension of Qℓ for some ℓ. (i) E has potentially good
  reduction. (ii) Suppose p is a prime of O and n ∈ Z+ is such that the multiplicative group 1 + pⁿOp is
  torsion-free (where Op is the completion of O at p). If p ∤ ℓ then E has good reduction over F(E[pⁿ]) at all
  primes not dividing p."
* Sutherland, Lecture 20, p. 6: "Corollary 20.13. Let E/C be an elliptic curve with complex multiplication.
  Then j(E) is an algebraic integer."

## Standing hypotheses

* Milne §6 (pp. 48-51): `R` is a discrete valuation ring whose fraction field `K` has characteristic 0 and
  whose residue field is perfect. Good reduction means being the generic fibre of an abelian scheme over
  `R`, where an abelian scheme is a smooth proper scheme with a group structure. Potential good reduction
  means acquiring good reduction over a finite extension `K′/K`; the definition does not say which discrete
  valuation rings of `K′` over `R` are meant.
* Milne §7: CM over `k` means `[End⁰(A):Q]_red = 2 dim A`, with endomorphisms over `k`. In Prop. 7.12, `k` is
  a number field, and "at all finite primes" means the local notion at each prime separately. The proof uses
  6.13, which first reduces to a complete local field.
* Rubin §3 and §4: `F` is a finite extension of `Q_p` with integers `O`. Good reduction means that a minimal
  Weierstrass equation has unit discriminant. "At a prime q of a number field" means over the completion
  `F_q` (p. 12).
* Rubin §5: CM over `F` means that `End_F(E)` is an imaginary quadratic order. From p. 16 on, the notes assume
  `O = O_K`, reducing to this case by an isogeny over `F` (Prop. 5.3). Theorem 5.7 is stated under that
  assumption, for local `F`.
* Sutherland: `E` is an elliptic curve over `ℂ`.

## Comparison

| Lean clause | Print | Match |
|---|---|---|
| `L` a number field, `E` an abelian variety over `L` with `E.dim = 1` | Milne 7.12: an abelian variety over a number field, of any dimension | Direct: dimension 1 is a special case. |
| `IsImagQuadOrder k R`, `IsCMBy E k R`: `End(E_{L̄}) ≅ R` | Milne 7.12: "with complex multiplication", which §7 defines over the base field | Step S1: `End⁰(E_{L̄}) ≅ k` has degree `2 = 2 dim E`, so `E` has CM over `L̄`. If 7.12 is read as requiring CM over `k` itself, first pass to a finite `L′ ⊇ L` over which the finitely many generators of `End(E_{L̄})` are defined. The conclusion allows any finite `L₁`, so this costs nothing, and Milne's proof itself opens with "After possibly extending k". |
| one `L₁` for all primes | 7.12: potential good reduction at each finite prime, separately | Step S2. `E/L′` has good reduction outside finitely many primes `𝔭₁, …, 𝔭ᵣ`: a Weierstrass model has unit discriminant away from finitely many primes. For each `𝔭ᵢ`, take a finite `Mᵢ/L′` over which `E` acquires good reduction at `𝔭ᵢ`, and enlarge `Mᵢ` to its Galois closure. Conjugation then gives good reduction at every prime above `𝔭ᵢ`, because `E` is defined over `L′`. Let `L₁` be the compositum of the `Mᵢ`. Good reduction persists under finite extension, since an abelian scheme base-changes to the local rings above. So `E_{L₁}` has good reduction at every finite prime. Alternative: Serre–Tate §2, Cor. 3, as usually quoted, gives good reduction over `L(E[m])` for `m ≥ 3` prime to the residue characteristic (not read here). Rubin Thm 5.7(ii) is the local CM version, for the maximal order. If "potential" is read over completions (Rubin §4), a Krasner-type step realizes each local extension inside a global one. |
| `𝒢 : GroupModel E L₁` over `𝓞_{L₁}` with `IsProper` | Milne: an abelian scheme over each local ring `𝓞_{L₁,𝔓}` | Step S3 (local to global). Over the open set `U ⊆ Spec 𝓞_{L₁}` where an integral Weierstrass model has unit discriminant, that model is an abelian scheme. At each of the finitely many primes outside `U`, spread the local abelian scheme out to an open neighbourhood, then glue along the generic fibre. The gluing is unique by Milne Cor. 6.6 / Prop. 6.4: an abelian scheme over a discrete valuation ring has the Néron property. Equivalently: take the Néron model over the Dedekind scheme `Spec 𝓞_{L₁}` (Bosch–Lütkebohmert–Raynaud 1.4/3, not read; the same bundle has it as the leaf `neronSchemeExtensionDedekind`). Its localizations are the local Néron models, which are proper here, and properness is local on the base. |
| the fields of `GroupModel` and `IsProper` | footnote 5: "a smooth proper scheme over S together with a group structure" | Step S4 (dictionary). An abelian scheme supplies `grp` and `smooth`. Properness supplies `separated` and, through universal closedness, `qc`. `gen` and `gen_hom` hold by construction: the generic fibre is `E_{L₁}` with its group law, since an isomorphism of abelian varieties that preserves the origin is a homomorphism. The Lean asks for nothing beyond Milne's abelian scheme. |
| (the manuscript's reason: `j` integral) | Sutherland Cor. 20.13; Rubin Lemma 3.2(i) | `j(E) ∈ L` (see the `cmjDegree` report), and Cor. 20.13 for `E_ℂ = E ⊗_σ ℂ` makes `j(E)` an algebraic integer. So `j(E) ∈ 𝓞_{L_q}` at each finite prime `q`, and Rubin 3.2(i) gives potential good reduction at `q`. This is the same per-prime statement as Milne 7.12, so Steps S2-S4 are still needed. (Rubin Thm 5.7(i) gives the CM statement directly, for the maximal order. A general order reduces to it by Prop. 5.3 and the isogeny invariance of good reduction, Milne Cor. 6.14.) |

## Verdict

**CONSEQUENCE.** The Lean follows from Milne, *Complex Multiplication*, Prop. 7.12 (p. 55), read with the
definitions on pp. 49, 51 and 52, by four further steps:

* S1: CM over `L̄` becomes CM over a finite extension.
* S2: one finite extension `L₁` serves all finitely many bad primes (Galois closure and compositum, or
  Serre–Tate's `L(E[m])`).
* S3: the local abelian schemes glue to one over the Dedekind ring `𝓞_{L₁}` (spreading out with Milne
  Cor. 6.6, or the Néron model over a Dedekind base).
* S4: the dictionary to the Lean `GroupModel` fields.

The Lean is not stronger than the print together with these standard steps. It claims no bound on
`[L₁ : L]`, which matches manuscript L629-630, and it claims nothing about the model beyond "abelian scheme".

## False, incomplete or unclear

The Lean statement is true, so this is not a NO. But it is not a direct instance of anything I read. The
print states potential good reduction prime by prime, and the single extension (S2) and the global model
(S3) are further steps. The manuscript (L596-597) leaves them implicit too.

Locators:

* Serre–Tate 1968 ("§6 Thm 7" in the Lean docstring) was not checked, because no legitimate free copy was
  found: the publisher's page links only to JSTOR. It remains UNVERIFIED.
* Silverman, AEC VII.5.5 was not read.
* Milne's Prop. 7.12 is a freely available printed statement of exactly the per-prime claim, and could be
  added to the source line.

Two points in Milne are unclear, both harmless:

* whether "with complex multiplication" in 7.12 means over `k` or over `k̄` (covered by S1);
* which discrete valuation rings of the finite extension carry the good reduction in the definition on
  p. 51 (covered by the Galois closure in S2).

## Not read

* Serre–Tate, Ann. of Math. 88 (1968).
* Silverman, AEC Prop. VII.5.5 and ATAEC II.6.1.
* Bosch–Lütkebohmert–Raynaud, *Néron models*.
* Barquero-Sanchez, Cadwallader, Cannon, Genao and Masri, Res. Number Theory 3 (2017) art. 13 (the
  manuscript's `[cmheight]`), proof of Thm 1.3, p. 15. I could not retrieve the publisher's PDF and found no
  confirmed free copy. The 2016 REU report of the same title, posted by Texas A&M (15 pp.), does not contain
  Theorem 1.3. A search-engine cache of the publisher's HTML (not counted as a page read) shows a proof that
  deduces potential good reduction from the integrality of `j` via AEC Prop. VII.5.5. It then takes "a
  finite extension L′/L such that E/L′ has everywhere good reduction", leaving S2 implicit as the manuscript
  does.
* The proofs of Milne 6.12, 6.13 and 7.12 (skimmed only), and of Rubin's Lemma 3.2 and Theorem 5.7.

## AI use

An AI agent (a large language model with web search) did all of this work:

* It found the free copies and downloaded them.
* It extracted their text with `pdftotext` (poppler) and located the displays.
* It wrote the unfolding of the Lean definitions, the quotes and the comparison.

No human has read the print for this report. The quotes come from the PDF text layers, not from page images.
Mathlib definitions were read from the source files at the pinned revision.

## Evidence

**AI-READ.** This report clears no flag: the row's flag is pending-review, not unread.

## Sources

| Source | URL | SHA-256 | Pages used |
|---|---|---|---|
| Milne, *Complex Multiplication* v0.10 (2020) | https://www.jmilne.org/math/CourseNotes/CM.pdf | `0ac337a885d72f6938f15724b897f568fe350d0d754d0b52370b8f3a01d2e2b5` | 49, 51, 52, 55 |
| Rubin, CM and BSD, Arizona Winter School 1999 copy | https://swc-math.github.io/aws/1999/99RubinCM.pdf | `dcb99254ea3042d1f0c81d0cd2383399188954402b8453ce36ec988a5df3f1c5` | 7, 12, 15, 16 |
| Sutherland, 18.783 S21 Lecture 20 | https://ocw.mit.edu/courses/18-783-elliptic-curves-spring-2021/771db89d54782bdfab8ae93c2315931e_MIT18_783S21_notes20.pdf | `1029192ce0bff0111d56edcd9692604e44fffe58fb997293d43ebbc54a576851` | 6 |
| Mathlib `AlgebraicGeometry/Morphisms/Proper.lean` @ `56a00585` | https://raw.githubusercontent.com/leanprover-community/mathlib4/56a005855ea17e0b0958f73ec801ae140b0a1679/Mathlib/AlgebraicGeometry/Morphisms/Proper.lean | `27d096df8f79a30ee6e1960dd44f1eb52bedd17458ec26f3b2398edfe8b8f5d0` | L39-41 |
| Checked, passage absent: BSCCGM REU report (2016) | https://artsci.tamu.edu/mathematics/_files/_docs/reu/results/2016/ccgreport.pdf | `3f4f925d1c66600ab303cf04bedc467d6c2f8500bec741bcde3e4e7940621be7` | whole (15 pp.) |
