Recorded from the statement-check sweep of 2026-11-18: an AI-READ report written by an AI agent that the project runs (no person checked it), against OPEN.md commit `2895a9c195344cdbca2454ba9bf58d748a3a9ce5`. It clears no flag.

---

# Statement check: `cmjDegree`

Report in the format of `docs/one-proof/STATEMENT-CHECKS.md`. Evidence class: **AI-READ** (see the last fields).

## Field and commit

* Field: `OpenResearchLeaves65.cmjDegree` (bundle `HDec.HSyn.OpenResearchLeaves65`,
  `ZInQKernel/OneProof/H/TailZ91.lean` L64-65), whose type is `HDec.CMBranch.CMjDegree`
  (`ZInQKernel/Contrib/OneProof/CMBranch.lean` L89-97).
* Commit read (Lean, OPEN.md, kinds.tsv, manuscript): `2895a9c195344cdbca2454ba9bf58d748a3a9ce5`.
* kinds.tsv row: kind consequence, strict GLUE, flag pending-review. Source line: "diophantine_zq.tex
  L586-587 (uncited); classical: [Q(j(E)):Q] = h(R) for End(E) = R (Cox, Primes of the form x^2+ny^2,
  Thm 11.1, UNVERIFIED number)".
* Manuscript, `diophantine_zq.tex` L585-587: "Let $\Delta<0$ be the discriminant of the full geometric
  endomorphism order of $E$. The degree of $j(E)$ is its order class number, so $h(\Delta)\le d\le D$."

## The Lean, unfolded

```lean
def CMjDegree : Prop :=
  ∀ (L : Type) [Field L] [NumberField L] (E : ZInQ.DefFaltings.AbVar L), E.dim = 1 →
    ∀ (k : Type) [Field k] [NumberField k] (R : Subring k), IsImagQuadOrder k R → IsCMBy E k R →
      Nat.card (CommRing.Pic R) ≤ Module.finrank ℚ L
```

* `ZInQ.DefFaltings.AbVar L` is an abbreviation of `PkgI3.AbVar L`
  (`ZInQKernel/Contrib/HeightBC/G0StableBC.lean` L18): a group object `X` in schemes over `Spec L` whose
  structure map is proper, smooth and geometrically integral (`ZInQKernel/HDecomp/Objects.lean` L160-168).
  `LeafAdopt.abVarEquiv` is the identity on the data (`ZInQKernel/OneProof/H/LPrefix.lean` L5322-5326).
* `E.dim` is the Krull dimension of the underlying topological space (`Objects.lean` L181). `E.dim = 1`:
  `E` is an abelian variety of dimension 1 over `L`, i.e. an elliptic curve over `L` (origin = unit section).
* `IsImagQuadOrder k R` (`CMBranch.lean` L34-38): `k` is totally complex (Mathlib `IsTotallyComplex`: every
  infinite place is complex) of degree 2 over `ℚ`, `R ≤ 𝓞_k` (`integralClosure ℤ k`), and
  `LeafQM.AV.conductor R ≠ 0`. Here `conductor R` is the `relIndex` of `R` in `𝓞_k` as additive groups
  (`ZInQKernel/HDecomp/QM/Leaves.lean` L147-149), i.e. `[𝓞_k : R]`, and Mathlib's index is `0` exactly
  when it is infinite. So `IsImagQuadOrder k R` says that `R` is an order of the imaginary quadratic field
  `k`, and every such order qualifies.
* `orderDisc R = [𝓞_k : R]² · disc(k)` (`CMBranch.lean` L40-44). This row does not use it.
* `IsCMBy E k R` (`CMBranch.lean` L60-64): there is a ring isomorphism
  `End(E ×_L L̄) ≃+* R`, where `L̄` is Mathlib's `AlgebraicClosure L`. Base change is `Over.pullback` along
  `Spec L̄ → Spec L` (`Objects.lean` L374-382). `End` is the ring of group-scheme endomorphisms over `L̄`:
  `L̄`-morphisms that are monoid homomorphisms, with the group law as sum and composition as product
  (`Objects.lean` L183-240). The isomorphism is an abstract ring isomorphism onto the whole ring `R`,
  with no normalization by the action on the tangent space.
* `CommRing.Pic R` (Mathlib at the pinned revision `56a005855ea17e0b0958f73ec801ae140b0a1679`,
  `Mathlib/RingTheory/PicardGroup.lean` L427-430): the invertible `R`-modules up to isomorphism, with
  multiplication `⊗`. For a domain, Mathlib proves `ClassGroup.equivPic : ClassGroup R ≃* Pic R`
  (L875-879). Here `ClassGroup R` is the group of invertible fractional ideals modulo the principal ones
  (`Mathlib/RingTheory/ClassGroup/Basic.lean` L86-91). `Nat.card` is the cardinality, or `0` for an infinite
  type.

In words: if an elliptic curve `E` over a number field `L` has geometric endomorphism ring isomorphic to an
order `R` of an imaginary quadratic field, then the number of invertible fractional `R`-ideals modulo
principal ones is at most `[L : ℚ]`.

## Edition, page, display

* Primary print: G. Fowler, "Some uniform effective results on André–Oort for sums of powers in ℂⁿ",
  Math. Proc. Camb. Phil. Soc. 180 (2026) 607–641, doi:10.1017/S0305004125101825 (first published online
  13 January 2026). §2·1 "Properties of singular moduli", p. 613, the unnumbered display
  `[Q(x_i) : Q] = [Q(√Δ, x_i) : Q(√Δ)] = h(Δ)`. Also §1, p. 607, first paragraph, which defines the
  discriminant of a singular modulus. The manuscript already cites this paper as `[fowler]`, for its
  Proposition 2.7. The arXiv version 2405.06456v2 has the same text in §2.1, p. 6.
* For the class number: A. V. Sutherland, MIT 18.783 Elliptic Curves (Spring 2021), lecture notes.
  Lecture 17, p. 2 (the definition `h(O) = #cl(O)`) and Corollary 17.11, p. 5. Second reading of the
  degree: Lecture 20, Theorem 20.12, p. 6, and Lecture 21, Corollary 21.2, p. 4.
* For the base change `L̄ → ℂ`: J. S. Milne, *Complex Multiplication*, course notes v0.10 (July 14, 2020),
  Proposition 7.9, p. 54.
* For the Weierstrass model: J. S. Milne, *Elliptic Curves* (BookSurge 2006, author's PDF),
  Chapter II, Theorem 2.1(a) on p. 50 and 2.1(c) on p. 51.

## Copy

* Fowler: the publisher's open-access PDF (CC BY 4.0), and the arXiv PDF.
* Sutherland: the MIT OpenCourseWare PDFs.
* Milne: the author's PDFs from his website.
* URLs and SHA-256 hashes are under Sources.

## Quote

* Fowler, p. 613: "Let x1, . . . , xn be all the distinct singular moduli of some discriminant Δ. Then, by
  [10, theorem 11·1 and proposition 13·2], the polynomial HΔ(z) = ∏_{i=1}^{n} (z − xi) has coefficients in Z
  and is irreducible over Q and over Q(√Δ). Hence, for every i ∈ {1, . . . , n}, we have that
  [Q(xi) : Q] = [Q(√Δ, xi) : Q(√Δ)] = h(Δ), where h(Δ) denotes the class number of the imaginary quadratic
  order of discriminant Δ." In this paper, [10] is Cox, *Primes of the form x² + ny²*, third edition,
  AMS Chelsea 2022.
* Fowler, p. 607: "A singular modulus is the j-invariant of an elliptic curve with complex multiplication.
  The discriminant of a singular modulus is defined to be the discriminant of the imaginary quadratic order
  isomorphic to the endomorphism ring of the corresponding elliptic curve."
* Sutherland, Lecture 17, p. 2: "Its cardinality is the class number h(O) = # cl(O)."
  Corollary 17.11, p. 5: "The ideal class group cl(O) is the group of invertible fractional O-ideals modulo
  its subgroup of principal fractional O-ideals (in particular cl(O) is a group)."
* Sutherland, Theorem 20.12, p. 6: "The coefficients of the Hilbert class polynomial HD (X) are integers."
  Corollary 21.2, p. 4: "Let O be an imaginary quadratic order with discriminant D. The Hilbert class
  polynomial HD (x) is irreducible over K = Q(√D) and for any elliptic curve E/C with CM by O the field
  K(j(E)) is a finite abelian extension of K with Gal(K(j(E))/K) ≅ cl(O)."
* Milne, *Complex Multiplication*, Prop. 7.9, p. 54: "Let k be an algebraically closed subfield of C. The
  functor A ⇝ A_C from abelian varieties over k to abelian varieties over C is fully faithful, ..."
* Milne, *Elliptic Curves*, Thm II.2.1, pp. 50-51: "Let k be a field of characteristic ≠ 2, 3: (a) Every
  elliptic curve (E, O) is isomorphic to a curve of the form E(a, b): Y²Z = X³ + aXZ² + bZ³, a, b ∈ k, ..."
  and "(c) ... j(E) = 1728(4a³)/(4a³ + 27b²). Then j(E) depends only on (E, O), ...".

## Standing hypotheses

* Fowler §2·1. A singular modulus is `j(τ)` for `τ` in the upper half plane with `[Q(τ):Q] = 2`. Its
  discriminant is `Δ = b² − 4ac` for the primitive `(a, b, c)` with `aτ² + bτ + c = 0`. By §1, this is the
  discriminant of the order isomorphic to `End(E)`. `HΔ` runs over all singular moduli of discriminant
  `Δ`, and the base field is `ℂ`.
* Sutherland, Lectures 17-21. `E/ℂ` has CM by `O` when `End(E) = O(L)`, the multiplier ring of its
  lattice, and `O` is an order of an imaginary quadratic field. `cl(O)` is the set of proper `O`-ideals up
  to homothety. It equals the invertible fractional ideals modulo principal ones (Cor. 17.11), it is
  finite, and `h(O) = h(D) = #cl(O)`.
* Milne, *Complex Multiplication* §7: abelian varieties over fields of characteristic 0. Prop. 7.9 needs an
  algebraically closed `k ⊆ ℂ`.
* Milne, *Elliptic Curves*: an elliptic curve over `k` is a nonsingular complete curve of genus 1 with a
  distinguished point (Introduction, p. 1). Thm 2.1 needs characteristic ≠ 2, 3.

## Comparison

| Lean clause | Print | Match |
|---|---|---|
| `L` a number field, `E : AbVar L`, `E.dim = 1` | Fowler and Sutherland work with elliptic curves over `ℂ` | Step A (dictionary): a 1-dimensional abelian variety over `L` is an elliptic curve over `L`. Its origin is an `L`-point and its genus is `dim H⁰(Ω¹) = dim Lie = 1`. Fix an embedding `σ : L̄ → ℂ` (it exists because `L̄/ℚ` is algebraic) and put `E_ℂ = E ⊗_{L,σ} ℂ`. |
| `IsCMBy E k R`: `End(E_{L̄}) ≃+* R` | Fowler's `Δ` is the discriminant of the order isomorphic to `End(E)` over `ℂ` | Step B: `End(E_{L̄}) → End(E_ℂ)` is a ring isomorphism (Milne CM Prop. 7.9, with `k = σ(L̄)`). So `End(E_ℂ) ≅ R`, `Δ = disc(R)`, and `h(Δ)` is the class number of `R`, because a ring isomorphism of orders preserves the discriminant and the class group. The full endomorphism ring is used on both sides, as in manuscript L586 ("full geometric endomorphism order"). |
| (implicit) `j(E) ∈ L` | `x = j(E_ℂ)` is a singular modulus of discriminant `Δ` | Step C: `E` has a Weierstrass equation over `L` (Milne EC Thm II.2.1(a), characteristic 0), so `j(E) ∈ L` by the formula in II.2.1(c), and `j(E_ℂ) = σ(j(E))`. Then `ℚ(j(E_ℂ)) ⊆ σ(L)`, and the tower law gives `[ℚ(j(E_ℂ)):ℚ] ≤ [L:ℚ]`. |
| degree | `[Q(x):Q] = h(Δ)` | Direct (Fowler p. 613). Sutherland gives it a second time: `H_D` is monic in `ℤ[X]` (Thm 20.12) and irreducible over `K` (Cor. 21.2), hence irreducible over `ℚ`, so its degree `h(D)` is the degree of each root. |
| `Nat.card (CommRing.Pic R)` | `h(Δ)`, the class number of the order | Step D: `h(R) = #cl(R)`, the invertible fractional ideals modulo principal ones (Sutherland Cor. 17.11). That is `#ClassGroup R`, Mathlib's definition, which equals `#Pic R` by Mathlib's theorem `ClassGroup.equivPic`, valid for every domain. The group is finite (Sutherland L17 p. 2), so `Nat.card` equals the class number. |
| conclusion `≤ [L:ℚ]` | an equality `[Q(x):Q] = h(Δ)` | Combining the steps: `#Pic(R) = h(Δ_R) = [ℚ(j(E)):ℚ] ≤ [L:ℚ]`. The quantifiers (over all `L, E, k, R`) match. There are no constants. As for boundary cases, `R ≠ ℤ` because it has finite index in `𝓞_k`, and `Δ < 0`. |

## Verdict

**CONSEQUENCE.** The Lean follows from Fowler §2·1, p. 613, in four further steps, none of them
research-level:

* A: the Lean's dimension-1 abelian variety is an elliptic curve.
* B: `End(E_{L̄}) = End(E_ℂ)` (Milne, *Complex Multiplication*, Prop. 7.9).
* C: `j(E) ∈ L` from a Weierstrass model over `L` (Milne, *Elliptic Curves*, Thm II.2.1), with the tower
  law `ℚ(j(E)) ⊆ L`.
* D: `h(R) = #cl(R) = #ClassGroup(R) = #Pic(R)` (Sutherland Cor. 17.11; Mathlib `ClassGroup.equivPic`).

The Lean is not stronger than the print, and it drops no hypothesis.

## False, incomplete or unclear

The Lean statement is true and follows from the print, so this is not a NO. There is a locator point. The
OPEN.md and kinds.tsv source line cites only "Cox Thm 11.1" for `[Q(j(E)):Q] = h(R)`. Fowler (Cox, third
edition) cites Cox Theorem 11.1 together with Proposition 13.2 for `HΔ ∈ Z[z]` being irreducible over `Q`
and over `Q(√Δ)`, and cites Lemma 9.3 with Theorem 11.1 for `Gal(Q(√Δ, x)/Q(√Δ)) ≅ cl(Δ)`. Which part each
Cox item supplies was not checked. I did not read Cox, so the Cox locator remains UNVERIFIED. The source
line could add Fowler 2026 §2·1, p. 613. That is an open-access refereed print, the same paper the
manuscript already cites as `[fowler]`, and it states the degree for every imaginary quadratic order with no
exceptions. A further point is unclear but harmless:
Fowler's quoted sentence does not define "class number of the order". The standard meaning (Cox) is the
order of the group of proper ideal classes, which is what Sutherland's `h(O) = #cl(O)` and Mathlib's
`ClassGroup` count.

## Not read

* Cox, *Primes of the form x² + ny²*, in any edition. Fowler's citations "theorem 11·1 and proposition 13·2"
  and "lemma 9·3 and theorem 11·1" were not checked against Cox.
* The rest of Fowler, apart from §1 p. 607 and §2·1 pp. 612-613.
* The proofs of Sutherland's Theorems 20.12 and 21.1 and Corollary 21.2 (only skimmed), and Lectures 18-19
  on the modular polynomial.
* The proof of Milne's Prop. 7.9 (skimmed).
* Silverman, *The Arithmetic of Elliptic Curves*. In particular its Weierstrass-model and `j ∈ L`
  statements were not read; Milne's *Elliptic Curves*, Thm II.2.1, is used instead.
* No printed locator was read for step A (a dimension-1 abelian variety is a genus-1 curve). It is standard,
  and I used it without a citation.

## AI use

An AI agent (a large language model with web search) did all of this work:

* It found the free copies and downloaded them.
* It extracted their text with `pdftotext` (poppler) and located the displays.
* It wrote the unfolding of the Lean definitions, the quotes and the comparison.

No human has read the print for this report. The quotes come from the PDF text layers, not from page images.
The text layer of the published Fowler PDF drops the Δ glyph, so Δ was restored from the arXiv v2 text,
which reads identically there. Mathlib definitions were read from the source files at the pinned revision.

## Evidence

**AI-READ.** This report clears no flag: the row's flag is pending-review, not unread.

## Sources

| Source | URL | SHA-256 | Pages used |
|---|---|---|---|
| Fowler, MPCPS 180 (2026), open access | https://www.cambridge.org/core/services/aop-cambridge-core/content/view/A72ABDB14BEB62DE7E9B47953B77DBDC/S0305004125101825a.pdf/some_uniform_effective_results_on_andreoort_for_sums_of_powers_in_mathbbcn.pdf | `bc676f4d5b6a2a70fa3e6bed55a4449622d6728167d4c668068b89da6b2d55ae` | 607, 612-613 |
| Fowler, arXiv:2405.06456v2 | https://arxiv.org/pdf/2405.06456v2 | `91669100e54b048c9fd55d951bfd36a3b3d0acaf40508e369f73f431f03eebee` | 6 |
| Sutherland, 18.783 S21 Lecture 17 | https://ocw.mit.edu/courses/18-783-elliptic-curves-spring-2021/5fcff4d009b75161913b27bce2d67458_MIT18_783S21_notes17.pdf | `25b7f161c228a7eae7133062aa70aca54f78c537f55fdcfd479e97fe21952563` | 1-2, 5 |
| Sutherland, 18.783 S21 Lecture 20 | https://ocw.mit.edu/courses/18-783-elliptic-curves-spring-2021/771db89d54782bdfab8ae93c2315931e_MIT18_783S21_notes20.pdf | `1029192ce0bff0111d56edcd9692604e44fffe58fb997293d43ebbc54a576851` | 6 |
| Sutherland, 18.783 S21 Lecture 21 | https://ocw.mit.edu/courses/18-783-elliptic-curves-spring-2021/0986055752ecf04dc7cfc16f30ade1c8_MIT18_783S21_notes21.pdf | `d8fa8cfaf9c45a347f821e60ee77afa1e4b7af93d6e43635598fd81312e3dbd9` | 4 |
| Milne, *Complex Multiplication* v0.10 (2020) | https://www.jmilne.org/math/CourseNotes/CM.pdf | `0ac337a885d72f6938f15724b897f568fe350d0d754d0b52370b8f3a01d2e2b5` | 54 |
| Milne, *Elliptic Curves* (2006) | https://www.jmilne.org/math/Books/ectext6.pdf | `14a89055a0a7f52b08fad1d53786c9165caba8be837491024b9b210afa384486` | 1, 50-51 |
| Mathlib `RingTheory/PicardGroup.lean` @ `56a00585` | https://raw.githubusercontent.com/leanprover-community/mathlib4/56a005855ea17e0b0958f73ec801ae140b0a1679/Mathlib/RingTheory/PicardGroup.lean | `2cb65ea466b0639d59f0616ab807062de17f8ae727c8b39342728a6ddc075a88` | L427-430, L875-879 |
| Mathlib `RingTheory/ClassGroup/Basic.lean` @ `56a00585` | https://raw.githubusercontent.com/leanprover-community/mathlib4/56a005855ea17e0b0958f73ec801ae140b0a1679/Mathlib/RingTheory/ClassGroup/Basic.lean | `ea6b0b19938593430694875b5a5b556146ba12d142d51c75d3efb9b3bbebb917` | L86-91 |
| Mathlib `GroupTheory/Index.lean` @ `56a00585` | https://raw.githubusercontent.com/leanprover-community/mathlib4/56a005855ea17e0b0958f73ec801ae140b0a1679/Mathlib/GroupTheory/Index.lean | `b74ca58bf109e30e666af408c65d93883961fe3d5dafcc8d78a19bbe3d2f5486` | L53-63 |
