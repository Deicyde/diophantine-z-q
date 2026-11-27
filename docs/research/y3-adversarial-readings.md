# Adversarial AI readings: the eight `y3FullThreeRepZ30` inputs (2026-11-26)

**Result.** All eight Lean statements are implied by their printed sources, read from page images
of hashed copies. Each of the 21 readings returned FAITHFUL WITH CAVEATS. None returned NOT
FAITHFUL, none found a BLOCKER, and no reader found a Lean clause stronger than the print. The
one definitional difference, that `FEC` lacks Buzzard's injectivity condition on ι, is harmless:
injectivity is automatic over a nonempty base (B-1), and over the empty base every statement holds
trivially. The caveats are of three kinds:

* steps that the prints do not contain and that the authors' notes (README B-1 to B-6) left
  incomplete; every reader who raised one also gave a fix, collected in section 4;
* one convention the print leaves open: Buzzard does not define a polarization over a base;
* standing hypotheses the notes did not check in writing (Buzzard's conditions (i) to (iii) at
  `V₁(5)`); the readers checked them.

The three Milne rows (`MilneProp207 3`, `MilneProp207 5`, `GeomCard3`) drew MINOR caveats only.
`ZeroPreservingIsHomLN` drew one MAJOR, about the scope of Milne's printed proof rather than of
his statement. The four remaining rows stay consequences: they rest on unprinted steps, now
checked and repaired, and, for `ProjectiveFEC`, on the polarization convention.

No person has read these pages. The maintainer ruled on 2026-11-26 that, with no human reader
available, an adversarial AI reading can stand in for the human reading; whether it does for
these rows, and which, is the maintainer's call. The evidence stays AI-READ.

## 1. Method

Twenty-one independent AI readings: seven units (`MilneProp207 3` and `MilneProp207 5` were read
together) times three lenses. The three readers of a unit were configured with three different
model families, so that they would not share blind spots. Lenses as in
`docs/research/pb-adversarial-readings.md`:

| Lens | Task |
| --- | --- |
| Fidelity | Unfold the Lean statement into atomic clauses and map each clause to the printed text: MATCH, MATCH AFTER A STATED IDENTIFICATION, DIRECT INSTANCE, MISMATCH, STRONGER or WEAKER THAN THE PRINT. |
| Skeptic | Try to break the match: hidden standing hypotheses, conventions, quantifiers, vacuity, base and characteristic conditions, whether each Lean definition means the printed notion, and whether each unprinted step is correct as written. |
| Red team | Read the source cold before the Lean, state what it asserts and under which hypotheses, then list every difference with the Lean. |

Every reader read the page images (150 dpi, rendered from the PDFs below), with the PDF text
layer as a secondary aid, and the Lean files at the fold head
`0184f542796ba6fee3743d7fed058ae6bbf9b919`. Each returned verbatim quotes with printed page
numbers. All quotes were then checked mechanically: 503 source quotes against the text layer of
the cited page (or of the whole PDF, where a reader cited a page outside its list), and 447 Lean
quotes against the Lean files. Every source quote was found: 400 exactly after normalization and
103 by fuzzy matching where the text layer garbles mathematics (subscripts, hats, script letters);
one short formula, "(i) det(U) = Ẑ^×", where the text layer reads "bZ×", was confirmed by hand.
Every Lean quote was found, three of them with small transcription slips by the reader. No verdict
rests on a quotation that is not in the source.

Definitions outside the reading files were settled by kernel queries on the built tree and given
to the readers: `LeafQM.B = QuaternionAlgebra ℚ 2 0 (-3)`; `LeafQM.O` is the image of
`ofInt n = (n₀ + n₂/2) + (n₁ + n₃/2) i + (n₂/2) j + (n₃/2) k`, that is `ℤ⟨1, i, (1+j)/2, (i+k)/2⟩`,
with `i² = 2`, `j² = -3`, `ij = k` kernel-checked; `Y3RouteA.Z30 = Localization.Away 30`, so
`Z30Base = Spec ℤ[1/30]`; `GeometricallyConnected` is Mathlib's class (connected fibres over every
field-valued point, equivalent to connected geometric fibres); `actS` and `actT` are the action
leg and the projection leg on `∐_G Z`.

Sources (legal copies; SHA-256):

| Source | URL | SHA-256 |
| --- | --- | --- |
| K. Buzzard, *Integral models of certain Shimura curves*, Duke Math. J. 87 (1997); author's preprint | https://www.ma.imperial.ac.uk/~buzzard/maths/research/papers/shimura.pdf | `4854cb4adc99fec7eac47596dea86832e2e468f3c80d78726afeb98d2404b915` |
| J. S. Milne, *Abelian Varieties*, in Cornell and Silverman (eds.), *Arithmetic Geometry* (Springer 1986); author's retyped edition (2022) | https://www.jmilne.org/math/xnotes/AVs.pdf | `bffdf81c57c77420b5454b31270007989d12f332abea62424be15c424079fc7c` |
| J. S. Milne, *Abelian Varieties*, course notes v2.0 (2008) | https://www.jmilne.org/math/CourseNotes/AV.pdf | `f5ca4e63e5092a4b102daad1470e4cbed5fe8f82115e3a28c8881e3f67f6aaef` |
| K.-W. Lan, *Arithmetic compactifications of PEL-type Shimura varieties*, Harvard thesis (2008) | http://www.kwlan.org/articles/cpt-PEL-type-thesis-single.pdf | `9d6a2014cd39b5e74047b893c1410ffbe43b579e24aa4ddf5da119340e9e2a4a` |
| the same thesis, revised 14 March 2021 | http://www.kwlan.org/articles/cpt-PEL-type-thesis-revision.pdf | `a7a454f5d0735f4bf11f00a8afc14c361c5fc2cefd691d7466f7620ab4c3a079` |
| J. Voight, *Quaternion Algebras*, GTM 288; author's PDF | https://jvoight.github.io/quat-book.pdf | `a9316b834dbd500c52cd3a981c3205c9f4145b217042b213d23f696aee84b0f0` |
| The Stacks Project, tags 01VT, 0C4K, 0B45, 02GW, 025G (HTML pages of 26 Nov 2026) | https://stacks.math.columbia.edu/tag/ | below |

Stacks HTML pages, SHA-256: 01VT `00834372cfa3a2ef7afb82ffd1580aa5c4ae0d5bca8a679691abaa315c0a809f`,
0C4K `441e44c5d503eedd1cfb8540b8704108838daa9c52b7bc5fdbe3f90f9f97b335`,
0B45 `d3057d3998eeec4460af5c5f4cac7be7e9d3f8683ffde265108cb76d3f2523f2`,
02GW `5cf83828f4345e78ce147be947c30f4a0f9fe558b047f962a68fe27814713050`,
025G `5a0a1fa5b437ce4b43c8dd4e02530b4d2bd85c40f9684540ec3875a9ba2fd40f`.

Page numbers below are printed page numbers of these copies: the preprint's for Buzzard and the
retyped edition's for Milne 1986. The journal pages and the 1986 printing's pages are UNVERIFIED.

## 2. Verdicts

| Unit | Lean | Print | Fidelity | Skeptic | Red team |
| --- | --- | --- | --- | --- | --- |
| U1 | `BuzzardThm21Cor23V15'` | Buzzard Thm 2.1 (p. 5), Lemma 2.2 (p. 6), Cor. 2.3 (p. 7), at `U = V₁(5)` | FWC, MAJOR | FWC, MAJOR | FWC, MAJOR |
| U2 | `BuzzardFrameRepTorsor 5` | Buzzard §1, the sentence after Def. 1.1 (p. 4) | FWC, MAJOR | FWC, MAJOR | FWC, MAJOR |
| U3 | `MilneProp207 3`, `MilneProp207 5` | Milne 1986 Prop. 20.7 (p. 44) | FWC, MINOR | FWC, MINOR | FWC, MINOR |
| U4 | `GeomCard3` | Milne 1986 Rem. 8.4 (p. 14), §20 (p. 42) | FWC, MINOR | FWC, MINOR | FWC, MINOR |
| U5 | `ZeroPreservingIsHomLN` | Milne 1986 Cor. 20.2(a) (p. 43); Lan Cor. 1.3.1.6 | FWC, MINOR | FWC, MAJOR | FWC, MINOR |
| U6 | `SerreRigidityLevel3'` | Milne 1986 Cor. 2.2 (p. 3), Prop. 17.5(b) (p. 37); Buzzard §1 (p. 3) | FWC, MAJOR | FWC, MINOR | FWC, MAJOR |
| U7 | `ProjectiveFEC` | Buzzard §1 (p. 3); Lan Prop. 1.3.2.15 (2021); Stacks 01VT, 0C4K, 0B45 | FWC, MAJOR | FWC, MAJOR | FWC, MAJOR |

FWC is FAITHFUL WITH CAVEATS; the second entry is the highest severity the reader found (BLOCKER:
not implied; MAJOR: implied only through a step that is missing or incomplete as written, or a
convention the print does not fix; MINOR: citation, page or wording).

## 3. The units

**U1, `BuzzardThm21Cor23V15'`.** Theorem 2.1, p. 5: "X_D(U) is an algebraic stack over
Z[1/M_U d]. Moreover, the morphism X_D(U) → Spec(Z[1/M_U d]) is proper and smooth of relative
dimension 1." Corollary 2.3, p. 7, for U satisfying (i) to (iii): "X_D(U) is the stack associated
to a regular scheme, and the morphism X_D(U) → Spec(Z[1/M_U d]) is projective." All three readers
mapped every clause: properness, smoothness of relative dimension 1 and the closed immersion into
`PN N` over the base (projective over an affine base; Stacks 0B45) are direct; the universal
property and the uniqueness of the comparison square are the representability of the stack by a
scheme, with uniqueness of the square from the absence of automorphisms in the proof of
Cor. 2.3 (p. 7: "to show that the objects of the category X^D(U) have no non-trivial
automorphisms"). The MAJOR caveats:
* the notes never check Buzzard's hypotheses (i) to (iii) at `V₁(5)`; the readers did (section 4);
* `FEC` has no injectivity field (B-1), and the empty base needs a sentence;
* `V15` is the étale-sheafified `V₁(5)`-structure for a choice of κ (B-5);
* `V15Fibre` does not ask the comparison map to be a homomorphism; it is one, because it preserves
  the zero section (ι(0) = 0) and a zero-preserving morphism of abelian schemes is a
  homomorphism over any base (Lan Cor. 1.3.1.6).

**U2, `BuzzardFrameRepTorsor 5`.** Buzzard, p. 4, for M prime to d and S a Z[1/Md]-scheme: "Then
F_{A/S,M} is represented by a closed subscheme of A[M], and this representing scheme is an étale
(O_D ⊗ Z/MZ)×-torsor"; the paper gives no proof. The Lean is that sentence at M = 5 through the
dictionary of B-4 (a full level structure α is determined by P = α(1)); the torsor condition is
the kernel-pair square of `actS` and `actT`, which the readers checked against their definitions.
The MAJOR caveat, raised by all three: B-4 as written does not show that the closed immersion of
the representing scheme into A is evaluation at 1. The fix is in section 4.

**U3, `MilneProp207 3` and `MilneProp207 5`.** Prop. 20.7, p. 44: "Let 𝒜 be an abelian scheme of
relative dimension g over S, and let n_𝒜 be multiplication by n on 𝒜. Then n_𝒜 is flat,
surjective, and finite, and its kernel 𝒜_n is a finite flat group scheme over S of order n^{2g}.
Moreover n_𝒜 (and therefore its kernel) is étale if and only if n is not divisible by any of the
characteristics of the residue fields of S." Direct instances at g = 2, n = 3 and n = 5; ι(n) is
multiplication by n by the `FEC` axioms; no residue characteristic of a ℤ[1/30]-scheme divides 3
or 5. The only caveats were the definitions now settled by the kernel queries.

**U4, `GeomCard3`.** Rem. 8.4, p. 14: "If k is separably algebraically closed and n is not
divisible by its characteristic, then the theorem says that the kernel A_n(k) of n : A(k) → A(k)
has n^{2g} elements." Direct instance at g = 2, n = 3 on the geometric fibre, an abelian surface
by §20 (p. 42) and `SmoothOfRelativeDimension 2`. MINOR: the dimension comes from the `FEC`
field, not from p. 42.

**U5, `ZeroPreservingIsHomLN`.** Cor. 20.2(a), p. 43: "Every morphism of abelian schemes carrying
the zero section into the zero section is a homomorphism." The Lean is the special case over a
locally noetherian base. The 2021 revision of Lan's Cor. 1.3.1.6 states it over a base scheme for
a separated target. The skeptic's MAJOR: Milne's proof applies Prop. 20.1, which is stated for a
connected base, and Lan fixes conventions on schemes (separated preschemes in 2008,
quasi-separated in 2021). The fidelity and red-team readers rated this MINOR: the statement as
printed has no connectedness hypothesis, and the 2021 corollary covers the case directly. Two
remarks that are not from the readings (BACKGROUND): the connected components of a locally
noetherian scheme are open, so Milne's proof applies on each component; and locally noetherian
schemes are quasi-separated, which meets the 2021 convention.

**U6, `SerreRigidityLevel3'`.** Cor. 2.2, p. 3: "Every morphism f : A → B of abelian varieties is
the composite of a homomorphism with a translation." Prop. 17.5(b), p. 37: "For any integer
n ≥ 3, an automorphism of (A, λ) acting as the identity on A_n(k̄) is equal to the identity."
Buzzard, p. 3: a false elliptic curve has "a unique principal polarisation on A such that if s is
a geometric point of S, then the corresponding Rosati involution on End(A_s) induces ∗ on O_D".
The Lean follows on the geometric fibre through B-2 and B-3. MAJOR (fidelity and red team): B-3
invokes Buzzard's polarization before establishing that the fibre satisfies Buzzard's hypotheses
(d invertible, ι injective); both hold, and the fix is in section 4. Prop. 17.5(b) is applied at
n = 3 in characteristic other than 3, as its proof (via 12.6) requires. In characteristic p,
Buzzard's uniqueness is printed with a sketched proof.

**U7, `ProjectiveFEC`.** The chain of B-6: Buzzard's principal polarization, read in Milne's sense
(p. 46: at every geometric point of the form φ_L with L ample), is symmetric, hence a polarization
in Lan's sense (2021 revision, Def. 1.3.2.16), and Prop. 1.3.2.15, (1) ⇒ (3), with base X, makes
(Id, λ)*P relatively ample over X; Stacks 01VT, 0C4K and 0B45 give a closed immersion of the total
space into projective space over ℤ[1/30], which is more than the Lean asks (the Lean does not ask
the immersion to lie over the base). MAJOR, all three readers: Buzzard does not define a
polarization over a base, so the first step is a convention.

## 4. Fixes to the unprinted steps

These complete the README's steps; none changes a Lean statement.

* **Standing hypotheses at `V₁(5)` (U1).** O is maximal: its reduced discriminant is 6, the
  discriminant of (2, -3)_ℚ (Voight Thm 15.5.5, p. 241). (i) det(V₁(5)) = Ẑ^×: at the split primes
  use diag(u, 1); at 2 and 3 the reduced norm is surjective on local units. (ii) V₁(5) is maximal
  at 2 and 3 by definition. (iii) holds with N = 5, which is at least 4 and prime to 6.
  M_U = 5: V_5 ⊆ V₁(5), and V_M ⊄ V₁(5) when 5 does not divide M. So Z[1/M_U d] = Z[1/30].
* **B-1.** Over the empty base the statements are not vacuous, since `FEC ∅` is inhabited; they
  hold trivially, because the total space is empty and every map is unique. The injectivity
  argument is correct; an alternative clears denominators of a⁻¹ to get b with ab = n > 0. (A
  Lean proof of B-1 from Milne 1986 Rem. 8.4 at g = 2, for every n prime to the characteristic,
  now exists outside this pull request; it is not used here.)
* **B-2.** Add that θ⁻¹ is also a homomorphism (Cor. 2.2) and that λ is an isomorphism. The
  pull-back formula λ_{u*L} = u^∨ λ_L u is Milne 2008, p. 64 (unrefereed).
* **B-3.** First base-change to the geometric point: A_s is an abelian surface over Spec k, on
  which 6 is invertible because char k is not 2 or 3, and ι_s is injective (B-1 on the fibre, or
  because B is a division algebra and End(A_s) ⊗ ℚ is nonzero). Then θ_s(0) = 0, Cor. 2.2, B-2,
  `IsGenAt` clause 2, and Prop. 17.5(b) at n = 3.
* **B-4.** The closed immersion is evaluation at 1: the universal frame gives e : Z → A[5], a
  monomorphism (a frame is determined by its value at 1), étale (Stacks 02GW), hence an open
  immersion (Stacks 025G); a finite open immersion is closed; compose with the closed immersion
  A[5] → A. Also: α_P(ā) = ι(a)P does not depend on the lift a (it changes by ι(b)[5]P = 0);
  injectivity on geometric fibres gives universal injectivity; the torsor square uses the action
  leg first, matching `actS`; over the empty base take Z = ∅.
* **B-5.** State that the theorems are applied for a κ with κ(e5) ≡ diag(1, 0) mod 5 (Buzzard fixes
  κ arbitrarily, p. 2), add that α ↦ α(E₂₂) is natural in S, and obtain the local lift from the
  printed torsor: étale locally a section Q is a matrix with zero first row and nonzero second
  row, which completes to an invertible matrix.
* **B-6.** Use the 2021 wording ("relatively ample over S") of Prop. 1.3.2.15 with base X. Cover
  N = 0 (then X is affine and O_X is ample). 0C4K needs O_X(1) ample relative to Spec ℤ[1/30],
  which 01VT gives. The polarization convention stays a convention.

## 5. What the readings do not establish

* **Copies.** Buzzard was read in the author's preprint and Milne 1986 in the author's retyped
  edition; the journal text and the 1986 printing were not read. Lan's thesis and its revision and
  Milne's 2008 notes are unrefereed; they carry only supporting steps.
* **Printed without proof.** Buzzard's representability sentence (U2) and his uniqueness of the
  polarization in characteristic p (U6, U7).
* **Convention.** Buzzard's polarization over a base (U7).
* **Proof scope.** Milne's proof of Cor. 20.2(a) goes through Prop. 20.1, stated for a connected
  base (U5); the statement has no such hypothesis.
* **Compilation.** The readers did not build the Lean; the build and the discharge check are
  recorded on the pull request.

## 6. Effect on the board

Proposed, for the maintainer:

* `milneProp207At3`, `milneProp207At5`, `milneTorsionCount3`: direct instances, MINOR caveats only;
  candidates for LEAF under the 2026-11-26 ruling.
* `milneZeroPreservingHomLN`: the statement is a special case of the printed one; one MAJOR on the
  printed proof's scope. The maintainer's call.
* `buzzardThm21Cor23V15`, `buzzardFrameRepTorsor5`, `serreRigidityLevel3`,
  `projectiveFalseEllipticCurve`: remain consequences (GLUE). Their unprinted steps are checked and
  repaired above; `projectiveFalseEllipticCurve` also rests on the polarization convention.

## 7. Addendum: unit U8, `MilneRem84` and `GeomCard5`

A follow-up contribution (#215, folded into this pull request) proves `BuzzardFrameRepTorsor 5` in Lean from `MilneProp207 5` and
`GeomCard5` (`buzzardFrameRepTorsor5_of_milne`), and both counts `GeomCard3` and `GeomCard5` from
`MilneRem84` (`geomCard3_of_rem84`, `geomCard5_of_rem84`). Its new input, `MilneRem84`, was read
the same way as U1 to U7: three independent lenses on three model families, from the page images
of the hashed copies above, with every quote checked mechanically.

| Unit | Lean | Print | Fidelity | Skeptic | Red team |
| --- | --- | --- | --- | --- | --- |
| U8 | `MilneRem84`, `GeomCard5` (Defs.lean at `034e0cedd3de0e5a935bcf8ead74044524a0850c`, SHA-256 `09201b4da9a1a55331fc668cbb104577f6f15b153f5a727aaf2900281ecc51b6`) | Milne 1986 Thm 8.2 (p. 13), Rem. 8.4 (p. 14), §20 (p. 42) | FWC, MINOR | FAITHFUL | FWC, MINOR |

Rem. 8.4, p. 14: "If k is separably algebraically closed and n is not divisible by its
characteristic, then the theorem says that the kernel A_n(k) of n : A(k) → A(k) has n^{2g}
elements." `MilneRem84` is its instance at g = 2 on the geometric fibres of an `FEC` over a
ℤ[1/30]-scheme, for every n with `(n : k) ≠ 0`, which is the printed hypothesis (n > 0 from
Thm 8.2, and n not divisible by the characteristic); `x ^ n = 1` in the group of k-points of the
fibre is the kernel A_n(k). `GeomCard5` is the instance n = 5. The caveats are MINOR and concern
the docstring: it should also cite Thm 8.2, which Rem. 8.4 refers to, and the dimension g = 2
comes from the `FEC` field `SmoothOfRelativeDimension 2`, not from p. 42, which supplies only that
geometric fibres are abelian varieties. All 42 source quotes and 46 Lean quotes were found; one,
the Milne 2008 Rem. 7.3 display "A_n(k) ≝ Ker(n : A(k) → A(k)) has order n^{2g}", whose text layer
reads "An.k/ dfD Ker.nW A.k/ ! A.k// has order n2g", was confirmed by hand.

Both docstring fixes were applied after the reading, comments only, at commit
`7c408638d7e5ed45abc03bcb40a216809e4b5a39` (Defs.lean SHA-256
`0f96770c343ae739d48830dfb60127f324041d9840d07a371b211448abf266e1`; the code is identical after
stripping comments). The Thm 8.2 quotation added there matches p. 13 of the retyped edition.

Effect (folded in this pull request at the owner's request): `milneTorsionCount3` and
`buzzardFrameRepTorsor5` leave the board and one row, `milneTorsionCount` (`MilneRem84`), enters,
so the count is 28 rather than 29. The unit U2 reading (Buzzard's sentence printed without proof)
is no longer relied on. In section 6, `milneTorsionCount` takes the place of `milneTorsionCount3`
among the LEAF candidates, and `buzzardFrameRepTorsor5` leaves the consequence rows.

## 8. Addendum: units U9 and U10, `BuzzardLemma22Full5` and `MilneThm125Pts`

A further contribution (#222) proves, in Lean, the rigidity statement the construction uses on
geometric fibres over ℤ[1/30] (`SerreRigidityFibreZ30`) from two printed statements, so that
`SerreRigidityLevel3'`, a consequence row resting on Buzzard's principal polarization (steps B-2
and B-3), is no longer an input. The proof: θ preserves the zero section, so it is a homomorphism
(`ZeroPreservingIsHomLN`); a generator of the 5-torsion has a finite orbit under θ, so some power
θ^m fixes it, and `BuzzardLemma22Full5` gives θ^m = 1; an elementary 3-adic argument on
A[3^n](k) ≅ (ℤ/3^n)^4 (from `MilneRem84`) shows θ is the identity on all 3-power torsion; and
`MilneThm125Pts` gives θ = 1. The two new inputs were read the same way as U1 to U8: three
independent lenses on three model families, from the page images of the hashed copies in
section 1, with every quote checked mechanically.

| Unit | Lean | Print | Fidelity | Skeptic | Red team |
| --- | --- | --- | --- | --- | --- |
| U9 | `BuzzardLemma22Full5` | Buzzard Lemma 2.2 at N = 5 (preprint p. 6), with Def. 1.1 (p. 3) and the V₁(N)-structures (pp. 4-6) | FWC, MINOR | FWC, MAJOR | FWC, MAJOR |
| U10 | `MilneThm125Pts` | Milne 1986 Thm 12.5 (p. 21), with Rem. 8.4 (p. 14) and Cor. 2.4 (p. 3) | FAITHFUL, MINOR | FWC, MINOR | FAITHFUL |

Lean: `SerreRigidityZ30/Leaves.lean` at `094b793426ed5eb2d10be6b100d47be2ab2f2e45` (SHA-256
`976318d65cb1abdb41747ad284ae3bc8b268128d8d65e62ce37e5beea32020a6`), as read.

**U9.** Lemma 2.2, p. 6: "Let N ≥ 4 be an integer prime to d, and let k be an algebraically closed
field of either characteristic 0 or of characteristic p prime to Nd. Let (A/k, i) be a false
elliptic curve over k, and let α be a V1(N)-structure on A/k. Then the only automorphism of
(A/k, i) which fixes α is the identity." The Lean statement takes N = 5 (at least 4 and prime to
d = 6), k algebraically closed with (30 : k) ≠ 0, ι injective (Buzzard's definition), θ a group
automorphism commuting with ι, and a point P such that x ↦ ι(x)P is a bijection from O/5O onto
the 5-torsion; if θ fixes P, then θ = 1. No reader found a mismatch. The two MAJOR caveats were
about the docstring: it did not say why the bijection on k-points is an isomorphism of k-schemes,
as Def. 1.1 asks (A[5] is finite étale because 5 is invertible, Milne 1986 Prop. 20.7, hence
constant over the algebraically closed k), and it did not verify Buzzard's standing hypotheses
for `O` (B = (2, −3)_ℚ indefinite and non-split with d = 6; `O` maximal by Voight Thm 15.5.5).
The red team also noted that the leaf is Lemma 2.2 applied to the V₁(5)-structure generated by
the full level-5 structure x ↦ ι(x)P, so its hypothesis is weaker than "fixes α" only in form:
θ fixing P gives θβ = β. Both docstring points were then added, comments only, at
`27bbe32ff4008df1f3a3fc065af8ba9cb844d8f6` (Leaves.lean SHA-256
`df73487256a4c874a094fe195f1a8162dc8173c71210cedd2f7a28de36eb1a04`; the code is identical after
stripping comments).

**U10.** Thm 12.5, p. 21: "For all abelian varieties A and B, Hom(A,B) is a free Z-module of
finite rank ≤ 4 dim A dim B; for each prime l ≠ char(k), the natural map Z_l ⊗ Hom(A,B) →
Hom(T_l A, T_l B) is injective with torsion-free cokernel." The Lean statement: over an
algebraically closed k, two endomorphisms of a false elliptic curve that agree on every point of
l-power order, for a prime l ≠ char k, are equal. All three readers confirmed the derivation uses
only the printed statement: f − g vanishes on every A_{l^n}(k), so T_l(f − g) = 0 (T_l A as in
Rem. 8.4, p. 14); injectivity gives 1 ⊗ (f − g) = 0; End(A) is free (printed in the same
theorem), so f = g; the difference is taken in the commutative End(A) (Cor. 2.4, p. 3). The
MINOR caveats were citations (Rem. 8.4; the exact commutativity reference), added in the same
comment-only edition.

All 109 source quotes and 67 Lean quotes of U9 and U10 were found in the text layers and the Lean
files; five, which join separated passages with ellipses or carry LaTeX markup, were confirmed by
hand (Buzzard p. 3 Def. 1.1; p. 4 the action of (O_D ⊗ Z/MZ)^× and the definition of u_M and
V₁(M); Voight p. 234 the discriminant).

Effect, if the contribution is folded: `serreRigidityLevel3` leaves the board, and two rows enter,
`buzzardLemma22Full5` and `milneThm125Pts`, both direct instances of single printed statements
(after the stated identifications), candidates for LEAF under the 2026-11-26 rulings.

## 9. Addendum: unit U11, `BuzzardXDV15Lit`

A further contribution (#225) replaces the consequence input `BuzzardThm21Cor23V15'` (unit U1,
which rested on the unprinted dictionary B-5 between Buzzard's level structures and the
generator-encoded `V15` record) by Buzzard's Thm 2.1 with Cor. 2.3 at U = V₁(5), stated with his
own definitions, and proves `BuzzardThm21Cor23V15'` from it in Lean (with `MilneProp207 5` and
`GeomCard5`, both already inputs). The leaf, `XDV15.BuzzardXDV15Lit`, uses:
- literal full level-5 structures (`LitFrame`): O-linear isomorphisms (O_D ⊗ ℤ/5ℤ)_T ≅ A[5]_T of
  T-schemes, recorded by their restrictions to the copies of T (Def. 1.1, p. 3);
- the left action α ↦ α ∘ r_δ (pp. 3-4), the group H = κ⁻¹{(a b; 0 1)} ⊂ (O/5O)^× for a fixed
  κ (`kappa5`, built from matrix units), the orbit spaces H\F_{A/S,5}(T) and their étale
  sheafification on S-schemes (p. 4), level structures as elements of F_{A/S,H}(S) (Def. 1.2);
- the morphisms of X^D(U) (p. 5) and Thm 2.1 with Cor. 2.3 in fine-moduli form (a universal
  object, unique base maps, unique comparison maps); "algebraic stack" and "regular" are dropped,
  and "projective" is a closed immersion into ℙ^N over ℤ[1/30] (EGA II (5.5.4)(ii)).

It was read like U1 to U10: three lenses on three model families, from page images of hashed
copies (Buzzard's preprint as in section 1, and EGA II, Publ. Math. IHÉS 8 (1961), open-access
copy, SHA-256 111834efffe9e90d068389d418f08925a82b4a54ae2957f080712d4180e032eb, pp. 103-105).

| Unit | Fidelity | Skeptic | Red team |
| --- | --- | --- | --- |
| U11 `BuzzardXDV15Lit` | FWC, MINOR | FWC, MAJOR | FWC, MAJOR |

Lean as read: `BuzzardXDV15/Leaf.lean` at `7d89d72022503077a6357b3ac7bc2117567b0e33` (SHA-256
`35606160239543302d6147340321c243cdfc96356df0cfb9625a282108b41ab5`), with `LitFrames.lean`
(`8e36bf5c2d9d0f05e3f91e731b72f13286e5253ce9c13821523e99911a7d7073`) and `Kappa5.lean`
(`d463db48e86f60e75d78432b8404567c08f55a049c5678cf512acbd6a0e2ac14`).

No reader found a mismatch. The two MAJOR findings were unstated steps:
- **Comparison maps** (red team). Buzzard's first two bullets ask that A → B_S be an isomorphism
  compatible with i; the leaf asks for a cartesian square with an O-linear h and no separate
  homomorphism condition. They agree: O-linearity at a = 0 makes h preserve the zero section, and
  a zero-preserving morphism of abelian schemes is a homomorphism (Milne 1986 Cor. 20.2(a),
  p. 43, stated in §20 for abelian schemes over any scheme S; Milne proves it through the rigidity
  of Prop. 20.1, and a proof over an arbitrary base is in Mumford's GIT, Cor. 6.4, not read here).
  So the uniqueness clauses quantify over exactly Buzzard's morphisms.
- **The empty base** (skeptic). Buzzard's i is injective, which excludes S = ∅, while `FEC`
  admits the empty curve; over ∅ every clause of the leaf holds trivially, so the leaf is not
  stronger than the print.

The MINOR findings: the docstring's "Buzzard fixes his isomorphism κ arbitrarily" paraphrased
"Fix once and for all an isomorphism κ" (p. 2), and its lifting argument for `kappa5` omitted two
steps (an automorphism of M₂(F₅) is F₅-linear, hence inner; extend the lift by the identity at the
other primes of R = ∏_{p∤6} ℤ_p); a header said "S-schemes" for "T-schemes"; the projectivity
encoding should cite EGA II (5.5.4)(ii) with the ampleness of O_Y on an affine scheme. All three
readers confirmed the remaining identifications: `LitFrame` is Def. 1.1; the action is Buzzard's
left action; `V15Group` is the image of V₁(5) (u₅ is surjective) and V₁(5) satisfies (i)-(iii)
with M_U = 5; `LevelPreLit` is the étale sheafification of the orbit presheaf; `LevelFibreLit`
expresses the third bullet, with ψ determined by its constraint; the fine-moduli form is "the
stack associated to a scheme" together with the absence of non-trivial automorphisms; dropping
"algebraic stack" and "regular" only weakens the statement.

All findings were addressed in the docstrings, comments only, at
`ec7ac6e020c45b9701b5f17bd71beed4362b837f` (`Leaf.lean` SHA-256
`ff2fecb0cb62f510b8549c3a882a2a189522032df5e8f06f518fcec1d7fa1865`, `LitFrames.lean` SHA-256
`7744ed08e05a9a8a92db489b8576f4f618c2882e786e3ffe67abae7409254d63`; the code is identical after
stripping comments).

All 91 source quotes and 79 Lean quotes were found in the text layers and the Lean files; one,
"(i) det(U) = Ẑ×" (Buzzard p. 4, where the text layer renders the hat as "bZ"), was confirmed by
hand.

Effect, if folded: `buzzardThm21Cor23V15` (a consequence row) is replaced by
`buzzardXDV15Lit`, a direct instance of Buzzard's Thm 2.1 with Cor. 2.3 after the stated
identifications, with no new inputs and the count unchanged.
