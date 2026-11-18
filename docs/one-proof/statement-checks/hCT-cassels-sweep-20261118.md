Recorded from the statement-check sweep of 2026-11-18, against commit `636c2761c6bc6099cd76b9fb9a515149beec7f6d` (AI-READ). This report was produced by an AI agent run by the project. Jack McCarthy is accountable for the project's posted checks; that does not mean that this report was read or verified by a person. No person independently checked it. This recording changes no flags, ratings or counts and discharges no Lean theorem. Sources not read and AI use are disclosed below.

---

# Statement check: frozenTarget.hCT against Cassels

## Field and commit

- **Field:** `ZInQ.OneProof.frozenTarget.hCT`, with statement `ZInQ.Manuscript.PoleS12.CasselsTatePairingCurves`.
- **Commit read:** `636c2761c6bc6099cd76b9fb9a515149beec7f6d`, the supplied repository's `origin/main` when read. The commissioning message's abbreviated spelling `636c2761c8bc…` did not resolve; this report uses the actual full commit, not a guessed correction.
- Pinned definitions: [pairing, rational-mod-integer target and maximal divisible subgroup](https://github.com/Deicyde/diophantine-z-q/blob/636c2761c6bc6099cd76b9fb9a515149beec7f6d/ZInQKernel/Contrib/OneProof/CasselsTatePairing.lean#L42-L92); [restriction to the manuscript curves](https://github.com/Deicyde/diophantine-z-q/blob/636c2761c6bc6099cd76b9fb9a515149beec7f6d/ZInQKernel/Contrib/OneProof/CasselsTatePairing.lean#L478-L482); [all-place Sha](https://github.com/Deicyde/diophantine-z-q/blob/636c2761c6bc6099cd76b9fb9a515149beec7f6d/ZInQKernel/Contrib/OneProof/SelmerTwoPower.lean#L117-L121); [checklist](https://github.com/Deicyde/diophantine-z-q/blob/636c2761c6bc6099cd76b9fb9a515149beec7f6d/docs/one-proof/STATEMENT-CHECKS.md); [open row](https://github.com/Deicyde/diophantine-z-q/blob/636c2761c6bc6099cd76b9fb9a515149beec7f6d/docs/one-proof/OPEN.md#L604-L618).

## Edition, page, display

**Principal source:** J. W. S. Cassels, “Arithmetic on Curves of Genus 1. IV. Proof of the Hauptvermutung,” *Journal für die reine und angewandte Mathematik* **211** (1962), 95–112, original journal pagination. Relevant locators:

- §1, Theorem 1.1, p. 95: existence, rational-mod-integer values, all-positive-integer orthogonality/divisibility criterion, and complete duality after quotienting by infinitely divisible elements.
- §1, p. 98 and footnote 12: all local completions; identification with continuous Galois H¹, with the Krull/discrete topologies; the group is torsion.
- §3, p. 101: construction on Sha × Sha, target Q/Z and intended biadditivity; stages (v)–(vii), pp. 102–104, establish the additive properties and independence of representatives.
- §3, stage (viii), p. 104: explicit diagonal-zero assertion and its proof.
- §4, Lemma 4.1, p. 104; Proof of Theorem 1.1, p. 105: exact prime-divisibility criterion and finite primary components of the reduced group.

**Corroborating primary sources:** Cassels, “Arithmetic on curves of genus 1. VII. The dual exact sequence,” **216** (1964), 150–158, especially §1, p. 151, footnote 3, and the correction on p. 158; Cassels, “Arithmetic on curves of genus 1. VIII. On conjectures of Birch and Swinnerton-Dyer,” **217** (1965), 180–199, especially §1, Theorem 1.2 and its corollary proof, p. 184.

## Copy

Institutional scans provided freely for research/private reading by the Niedersächsische Staats- und Universitätsbibliothek Göttingen. IV and VIII were downloaded as the archive's article PDFs; VII was read from the archive's volume PDF. No unofficial or pirate scan was used. Only links and short quotations, not copies of the scans, are included here.

The IV article PDF has one archive information sheet followed by printed pp. 95–112: **PDF page = printed page − 93**. VIII likewise has one archive sheet: **PDF page = printed page − 178** for pp. 180–199. In the VII volume PDF, printed pp. 150–158 are **PDF pp. 155–163**.

## Quote

These are visual transcriptions, not unverified OCR. Line breaks and line-end word division are joined; emphasis and mathematical font distinctions are normalized. The printed Sha glyph is rendered Ш; χ and U replace the corresponding printed blackletter symbols. Formula spacing and subscripts are normalized. Printed terminology, including “skewsymmetric” in stage (viii), is retained. **OCR fixes: none.**

**IV, §1, Theorem 1.1, p. 95:**

> “Then there exists a naturally-defined skew-symmetric form l(ξ, η)”

> “taking values in the group Q/Z of the rationals modulo 1”

The explanatory sentence following the theorem identifies the quotienting subgroup:

> “where χ is the group of infinitely divisible elements of Ш.”

**IV, §1, p. 98, definition of Ш:**

> “where k_p runs through all the local completions of k.”

**IV, p. 98, footnote 12, on continuous H¹:**

> “i. e. arising from continuous cocycles when Γ has the Krull topology and Ḡ the discrete topology.”

**IV, §3, p. 101, on the constructed form:**

> “bilinear in ξ, η”

**IV, §3, stage (viii), p. 104:**

> “l(ξ, η) is skewsymmetric, i. e. l(ξ, ξ) = 0 for all ξ.”

**IV, §4, Lemma 4.1, p. 104:**

> “A necessary and sufficient condition for ξ ∈ Ш to be divisible by q in Ш is that l(ξ, η) = 0 for all η ∈ Ш with qη = 0.”

Here the lemma's preceding sentence specifies that q is prime.

**IV, §4, Proof of Theorem 1.1, p. 105**, with U = Ш/χ:

> “Hence the q-primary part U(q) of U is a finite group.”

**VII, §1, footnote 3, p. 151**, specifying elementwise divisibility:

> “i. e. divisible in Ш by every natural number.”

**VIII, §1, proof of the corollary to Theorem 1.2, p. 184:**

> “l_2 is a duality on the torsion group Ш_2 modulo its divisible part.”

The VIII sentence explicitly recalls a fact proved in IV. It is not conditional on the whole Sha being finite; the corollary has a separate hypothesis concerning divisible elements killed by the isogeny degree.

## Standing hypotheses

1. IV Theorem 1.1 assumes an arbitrary algebraic number field k and an abelian variety C of dimension one over k, hence an elliptic curve with its distinguished k-rational origin. It does **not** assume that Ш is finite, that its divisible subgroup vanishes, or that a primary component of Ш is finite. The nonzero-divisible-part question is explicitly left open immediately after the theorem.
2. Ш consists of principal homogeneous-space classes which are everywhere locally trivial, at **all** local completions. On p. 98 Cassels identifies the Weil–Châtelet group with continuous H¹(Γ, C(k̄)) and gives it that group's additive structure; it is a commutative torsion group. The local condition is the kernel of restriction at every completion.
3. For Q, all completions are Q_p for every rational prime p and R. In characteristic zero, a separable closure is an algebraic closure. There is no omission of the infinite place or replacement of continuous cohomology by abstract cohomology.
4. The target is the additive group Q/Z. The statement asks for an algebraic biadditive pairing, not an additional topology on Sha or a chosen normalization of its sign.
5. The row restricts to E_ℓ: y² = x(x − ℓ)(x + 3ℓ) for positive squarefree natural ℓ with ℓ ≡ 11 modulo 12. Positivity implies ℓ ≠ 0; the pinned curve definition and proved discriminant formula give Δ(E_ℓ) = 2304ℓ⁶ ≠ 0. These are therefore elliptic curves over Q. Squarefreeness and the congruence are restrictions of scope, not additional hypotheses needed for Cassels's pairing theorem.

## Comparison

### 1. Quantifiers and existence

The row is ∀ℓ satisfying the stated restrictions, ∃b on the whole Sha(E_ℓ). Cassels constructs a single form l on the whole Ш of each elliptic curve over a number field. Instantiation at k = Q and C = E_ℓ supplies this quantifier order. The Lean existential forgets naturality and the name of the constructed form, so it asks for less, not more. No uniform pairing across different ℓ is required.

The auxiliary definition `CasselsTatePairing E` can be written for any Weierstrass curve; this check concerns the specified row, where the discriminant is nonzero. It is not a claim about singular Weierstrass equations.

### 2. The group and its local conditions

The pinned `sha E` is the intersection of the restriction-zero subgroups for every Q_p and for R. The underlying `H1` is the quotient of continuous 1-cocycles by coboundaries; `PointCoeff` is E(Qˢ) with the discrete topology and coordinatewise Galois action. The restriction map pulls back along the induced absolute Galois-group map and the embedding of geometric points.

These definitions were checked against the actual coefficient, low-degree cohomology and restriction definitions, not only their comments. They match Cassels's p. 98 description, including footnote 12. Cassels's principal homogeneous-space description and the Lean cochain description are the same group under the continuous-H¹ correspondence printed there, with the same all-place kernel. Ш is neither the 2-primary component alone nor a finite-prime-only kernel.

### 3. Codomain

Lean's `QZ = ℚ ⧸ AddSubgroup.zmultiples (1 : ℚ)` divides the additive rationals by their integer subgroup. This is precisely Cassels's Q/Z, not R/Z or only its 2-primary part.

### 4. Biadditivity

`sha E →+ sha E →+ QZ` is a homomorphism in each variable. Cassels's §3 construction and verification give exactly biadditivity on equivalence classes. No stronger linearity or continuity requirement is present in Lean.

### 5. Alternation, not merely skew-symmetry

The Lean clause is b(x,x) = 0 for every x. This is printed explicitly in IV §3(viii), p. 104, and proved there. It must not be inferred merely from b(x,y) = −b(y,x), because Q/Z has nonzero 2-torsion. Cassels uses “skewsymmetric” here with an explicit diagonal-zero explanation, which removes that ambiguity for elliptic curves.

### 6. Radical versus infinite divisibility

Put A = Ш. IV Theorem 1.1, p. 95, gives for every positive integer m:

    if l(ξ,η) = 0 for every ξ ∈ A with mξ = 0,
    then η = mH for some H ∈ A.

The converse follows from biadditivity. Lemma 4.1, p. 104, prints the necessary-and-sufficient prime version. Crucially, the root lies **in Ш**, not just in the larger Weil–Châtelet group.

Therefore the radical is χ = ⋂_{m≥1} mA: a radical element satisfies the theorem's annihilator condition for every m; conversely, if x ∈ χ and y has order dividing m, write x = mz and use l(x,y) = l(z,my) = 0. A is torsion, so this tests every y. Alternation and biadditivity identify the left and right radicals. This argument does not assume A finite.

### 7. The explicit extra step: χ is the maximal divisible subgroup

For an arbitrary abelian group, one must **not** silently identify ⋂m mA with the maximal divisible subgroup: separate roots need not give compatible divisible roots. Here the printed finite-primary assertion on p. 105 closes the issue.

For each prime q, let A_q be the q-primary component, χ_q = χ ∩ A_q, and U = A/χ. Primary decomposition of torsion groups gives A_q/χ_q ≅ U(q). By the printed assertion, choose r ≥ 0 such that qʳU(q) = 0.

For x ∈ χ_q, choose z ∈ A with q^(r+1)z = x, and take its q-primary component z_q. Set y = qʳz_q. Then qy = x, while qʳU(q) = 0 implies y ∈ χ_q. Thus multiplication by q is surjective on χ_q. Multiplication by any integer prime to q is invertible on a q-primary group, so χ_q is divisible. Summing the finitely many primary components of each element shows χ is divisible.

Every divisible subgroup D of A lies in every mA, hence in χ. Consequently χ is the **maximal divisible subgroup**. This is the subgroup Lean calls `divisiblePart A`, whose divisibility and maximality are proved in the pinned pairing definition. Only the printed finiteness of each **reduced** U(q) was used, not finiteness of A or of all U.

### 8. VII and VIII do not strengthen the assumptions

VII Theorem 1.1, p. 151, concerns a different dual exact sequence and assumes that zero is the only element of Ш divisible by every natural number. Its p. 151 identification of the Ш self-duality is stated in a finite-Ш case. Neither passage alone justifies the unrestricted radical clause. Likewise, VII p. 154's root η belongs to WC, not necessarily Ш; it must not be substituted for IV's internal-Ш root.

VIII p. 184 confirms Cassels's own later use of duality modulo the divisible part without a whole-Ш finiteness assumption. The isogeny corollary's separate extra hypothesis is not imported into this row. The explicit alternation evidence remains IV p. 104, rather than VIII's bare use of the term skew-symmetric.

## Verdict

**CONSEQUENCE.** Every clause of `frozenTarget.hCT` follows from Cassels IV Theorem 1.1 and the construction/properties on pp. 98, 101–105. The named further step is the elementary identification of Cassels's infinitely divisible subgroup with the maximal divisible subgroup, using his printed finiteness of each reduced primary component on p. 105.

Existence, biadditivity, Q/Z values, alternation, all-place Sha and the number-field scope match directly. No finiteness hypothesis on the whole Sha has been dropped. Under the checklist's strict wording, the modern maximal-divisible-subgroup formulation is recorded as a consequence, not claimed as a verbatim YES for the 1962 statement. This is one statement-check report; it makes no change to the recorded row or its classification.

## False, incomplete or unclear

No false statement or missing finiteness assumption was found for this row. The point requiring explanation is terminological: IV p. 95 prints infinitely divisible elements, not the literal modern phrase maximal divisible subgroup. Replacing those terms for an arbitrary torsion group would be unjustified; the p. 105 reduced-primary finiteness provides the necessary bridge here. VII's finite-case statement is insufficient by itself.

## Not read

The principal visual reading inspected IV pp. 95, 98, 101–106 and 110–112, including the diagonal-zero proof and the p. 105 reduced-group argument. The other IV pages and the full class-field-theoretic proof of Lemma 4.1 were not independently audited. Paper III and the cited Lang–Tate, class-field-theory and Mordell–Weil finiteness arguments were not read or re-proved. The finite-U(q) assertion is used as a printed source statement, not inferred from finiteness of A/qA alone.

AI source readers inspected all of VII pp. 150–158 and VIII pp. 180–199; VIII p. 184 was also inspected in the principal reading. VII p. 158 corrects IV p. 106's word “isomorphism” to “injection”; this report does not rely on the stronger uncorrected proof sentence. This is a statement check, not a new audit of Cassels's entire proof.

Poonen–Stoll and Milne were not re-read for this report and are not needed for the primary-source conclusion. No Lean build, proof replay, repository edit, issue comment or public submission was performed.

## AI use

AI language-model assistants discovered the institutional sources, read rendered scan pages, transcribed quotations, compared the pinned definitions and supplied and checked the elementary group-theoretic bridge. Standard utilities downloaded the files, computed SHA256, attempted text extraction and rendered page images. The article scans had no usable article text layer; quotations were taken from page images. This report is AI-produced and is not a human reading.

## Evidence

**AI-READ.** The primary printed pages supporting the statement were read. This report is not HUMAN-READ and does not itself clear a human-review or statement-check flag, change a count, or constitute a maintainer ruling.

## Source URLs and SHA256

Hashes identify the original downloaded PDFs, including the archive information sheets.

- **Cassels IV (1962), article PDF:** https://gdz.sub.uni-goettingen.de/download/pdf/PPN243919689_0211/LOG_0012.pdf
  - SHA256: `660a9e4fd00cd6447108464d47600d667330ff1d1e1128985e3bec215b0f31fc`
  - 2,383,069 bytes; 19 PDF pages. Stable volume: https://resolver.sub.uni-goettingen.de/purl?PPN243919689_0211
- **Cassels VII (1964), original volume PDF:** https://gdz.sub.uni-goettingen.de/download/pdf/PPN243919689_0216/PPN243919689_0216.pdf
  - SHA256: `e215eb15d3979fecc6dd1b119213a1d7834c4e21aee3661e830b62041e65d34e`
  - 32,451,908 bytes; 227 PDF pages; article at PDF pp. 155–163. Stable volume: https://resolver.sub.uni-goettingen.de/purl?PPN243919689_0216
- **Cassels VIII (1965), article PDF:** https://gdz.sub.uni-goettingen.de/download/pdf/PPN243919689_0217/LOG_0013.pdf
  - SHA256: `23de7b856cb4a0fcf9e61c4a861cd4b7ddad0607bd70546798382adca7742a31`
  - 2,054,288 bytes; 21 PDF pages. Bibliographic record: https://eudml.org/doc/150666
