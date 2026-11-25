# Statement checks (no Lean needed)

A statement check compares one open hypothesis of `ZInQ.OneProof.frozenTarget`, as stated in Lean, with the
theorem printed in the book or paper it cites. You need the source and a knowledge of the area, not Lean.

## Why it matters

The Lean kernel checks that `frozenTarget` follows from its open hypotheses. It cannot see whether a hypothesis
labelled "SGA 3 VI_B 3.10" says what SGA 3 prints there. A statement that is stronger than its source, or that
drops a hypothesis, would let the proof rest on something nobody has proved. In OPEN.md, many sources carry a
locator marked UNVERIFIED, and some rows are flagged as pending a reading. A careful human reading is what turns
the LEAF and GLUE ratings into evidence, and a reading that finds a mismatch is as valuable as one that confirms.

## Pick a packet

Statements are grouped into reading packets, each tied to one source or one area. The Packets section of
[OPEN.md](OPEN.md) lists each packet's statements and their flags, and each hypothesis entry names its packet.
A packet with no rows in OPEN.md is not open yet. The packets:

* R1: the reduction block (SGA 7 IX, BLR 1.2 Prop. 4, Serre-Tate 1968).
* R2: unread locators.
* R3: Tian-Yuan-Zhang and Gross-Zagier. Retired with Route K: no current hypothesis comes from these sources, so
  it has no rows.
* R4: the discriminant-6 Shimura curve.
* R5: heights.
* R6: theta and Siegel forms.
* R7: p-adic Hodge theory and modular Galois representations.
* R8: Lean-definition faithfulness (whether a project definition means what the literature means).
* R9: reading A. Retired with Route K, like R3.
* R10: the Picard scheme and the Weil pairing.

For a reader who knows the area, most readings are a cheap win to a medium investment; R8 is a bigger
investment. [pages-wanted.md](pages-wanted.md) lists the printed pages that someone needs to read.

## Claim it

A packet is claimed on its own issue if it has one (linked from OPEN.md's Packets section); otherwise on the
statement-checks issue; until that issue exists, on [issue #14](https://github.com/Deicyde/diophantine-z-q/issues/14).
Comment there:

```text
Claiming reading <packet>
```

If you stop, comment `Releasing reading <packet>: <what blocked you>`. The claim rules of the root
[CONTRIBUTING.md](../../CONTRIBUTING.md#choose-and-claim-one-statement) apply: one claim to start, and the same
lapse policy.

## The checklist

Post one report per statement, in the thread where you claimed the packet or with the "Statement check report"
issue form. Fill every field:

* **Field and commit**: the Lean field name as OPEN.md shows it, and the commit of OPEN.md you read.
* **Edition, page, display**: the edition you read, the page, and the theorem or display number.
* **Copy**: library print, author copy, or scan.
* **Quote**: a short verbatim quote of the printed statement, enough that a second reader with the same edition
  can check it.
* **Standing hypotheses**: the conventions that the chapter or section head imposes (base ring or scheme,
  noetherian or finiteness assumptions, normalizations).
* **Comparison**: clause by clause, the print against the Lean: quantifier order, base ring, boundary cases,
  constants and normalizations.
* **Verdict**, one of:
  * YES: the Lean says what the print says, or is a direct instance of it (a special case that needs no
    argument).
  * CONSEQUENCE: the Lean follows from the print by a further step; name the step.
  * NO-statement: the Lean does not follow from the print (stronger, a missing hypothesis, a wrong constant).
  * NO-locator: the print at that place is a different statement; give the right place if you know it.
  * UNVERIFIED: you could not decide; say why.
* **False, incomplete or unclear**: for a NO, whether the Lean statement is false, or only not justified by
  this source, or the source is unclear.
* **Not read**: what you did not read (other sections, the proof, cited lemmas).
* **AI use**: none, or which tool did what.
* **Evidence**: HUMAN-READ if you read the print yourself and the quote and comparison are your own; AI-READ if
  a tool produced the reading. An AI-READ report is recorded, but it never counts as a human reading.

A reviewer replies in the same thread with what the Lean says, in plain words, if you ask.

## Reading a Lean Prop

Each OPEN.md entry shows the hypothesis as a Lean name or term. Here is `sga7_IX_3_3`, in packet R1 with the
label long-pole and a pending-reading flag. Its OPEN.md entry gives the source and the Lean block:

* Source: SGA 7 IX 3.3 (may be stated over a strictly henselian trait; used at number-field DVRs)

```lean
CToPrinted.SGA7_IX_3_3
```

The Lean block is a name. Its definition is in `ZInQKernel/OneProof/H/TailZ19.lean` (search for
`def SGA7_IX_3_3`):

```lean
def SGA7_IX_3_3 : Prop :=
  ∀ (K : Type) [Field K] (O : ValuationSubring K) [IsDiscreteValuationRing O]
    (K' : Type) [Field K'] [Algebra K K'] [FiniteDimensional K K'] (O' : ValuationSubring K')
    [IsDiscreteValuationRing O'] (hO : O'.comap (algebraMap K K') = O) (A : PkgI3.AbVar K),
    HasSemistableReduction A O →
    ∀ 𝒩 : GroupModelO A O, 𝒩.IsNeronModel →
    ∀ 𝒩' : GroupModelO (A.baseChange K') O', 𝒩'.IsNeronModel →
    letI : GrpObj (bcO hO 𝒩.G) := Functor.grpObjObj
    ∀ c : bcO hO 𝒩.G ⟶ 𝒩'.G, IsMonHom c → IsIso ((Over.pullback (jO O')).map c) →
    ∀ U : (bcO hO 𝒩.G).left.Opens, (U : Set (bcO hO 𝒩.G).left) = idCompSet (bcO hO 𝒩.G) →
      IsOpenImmersion (U.ι ≫ c.left) ∧ Set.range (U.ι ≫ c.left).base = idCompSet 𝒩'.G
```

It uses this set, defined earlier in the same file:

```lean
def idCompSet (G : Over S) [GrpObj G] : Set G.left :=
  {x | x ∈ connectedComponentIn (G.hom.base ⁻¹' {G.hom.base x})
    ((η[G] : 𝟙_ (Over S) ⟶ G).left.base (G.hom.base x))}
```

The docstring above the definition gives the printed form "as recalled", with number and wording marked
UNVERIFIED; a check is what settles it. Square brackets mark structure or properties that are assumed. Clause by clause:

* `∀ (K : Type) [Field K] (O : ValuationSubring K) [IsDiscreteValuationRing O]`: for every field `K` and every
  valuation ring `O` of `K` that is a discrete valuation ring.
* `(K' : Type) [Field K'] [Algebra K K'] [FiniteDimensional K K']`: a field `K'` over `K` with `K'/K` finite.
* `(O' : ValuationSubring K') [IsDiscreteValuationRing O']`: a valuation ring `O'` of `K'` that is a discrete
  valuation ring.
* `(hO : O'.comap (algebraMap K K') = O)`: `O' ∩ K = O`. The ring map `O → O'` this gives is `comapHom hO`
  (`ZInQKernel/OneProof/H/TailZ7.lean`).
* `(A : PkgI3.AbVar K)`: an abelian variety `A` over `K`, in the project's definition
  (`ZInQKernel/HDecomp/Objects.lean`): a group object among schemes over `Spec K` whose structure morphism is
  proper, smooth and geometrically integral.
* `HasSemistableReduction A O →`: assume `A` has semistable reduction at `O`. In `TailZ7.lean` this means that
  some Néron model of `A` over `O` has semistable special fibre: its geometric special fibre has an open
  connected subgroup scheme with a faithfully flat homomorphism onto an abelian variety whose kernel is a split
  torus (`HasSemiAbelianIdentityComponent`, `ZInQKernel/OneProof/H/TailY.lean`).
* `∀ 𝒩 : GroupModelO A O, 𝒩.IsNeronModel →`: for every Néron model `𝒩` of `A` over `O`. In `TailZ7.lean`, a
  `GroupModelO A O` is a smooth, separated, quasi-compact group scheme `𝒩.G` over `O` with an isomorphism of
  group schemes from its generic fibre to `A`; `IsNeronModel` says that for every smooth `O`-scheme `Y`, sending
  a morphism `Y → 𝒩.G` to its generic fibre composed with that isomorphism is a bijection onto the
  `K`-morphisms from the generic fibre of `Y` to `A`.
* `∀ 𝒩' : GroupModelO (A.baseChange K') O', 𝒩'.IsNeronModel →`: for every Néron model `𝒩'` over `O'` of
  `A_{K'}`, the base change of `A` to `K'`.
* `letI : GrpObj (bcO hO 𝒩.G) := Functor.grpObjObj`: not a hypothesis. It gives `bcO hO 𝒩.G`, the base change
  `𝒩 ×_O O'` along `O → O'` as a scheme over `O'`, its group-scheme structure.
* `∀ c : bcO hO 𝒩.G ⟶ 𝒩'.G, IsMonHom c → IsIso ((Over.pullback (jO O')).map c) →`: for every morphism
  `c : 𝒩 ×_O O' → 𝒩'` of `O'`-schemes that is a homomorphism of group schemes and whose generic fibre (the
  pullback along `jO O' : Spec K' → Spec O'`) is an isomorphism.
* `∀ U : (bcO hO 𝒩.G).left.Opens, (U : Set (bcO hO 𝒩.G).left) = idCompSet (bcO hO 𝒩.G) →`: for every open subset `U` of
  `𝒩 ×_O O'` equal to `idCompSet` of `𝒩 ×_O O'`. If that set is not open, there is no such `U`, and the
  statement asserts nothing for that `𝒩`.
* `IsOpenImmersion (U.ι ≫ c.left) ∧ Set.range (U.ι ≫ c.left).base = idCompSet 𝒩'.G`: the conclusion. The
  composite `U → 𝒩 ×_O O' → 𝒩'` (the inclusion of `U`, then `c`) is an open immersion, and its image is
  `idCompSet 𝒩'.G`.
* `idCompSet G` is the set of points `x` of `G` such that, with `s` the image of `x` in the base
  (`G.hom.base x`), the point `x` lies in the connected component of `e(s)` inside the fibre over `s`. Here the
  fibre is the set of points of `G` that map to `s` (`G.hom.base ⁻¹' {G.hom.base x}`), with the subspace
  topology, and `e(s)` is the image of `s` under the unit section `η[G]`. In words: the union over `s` of the
  identity components of the fibres.

So the Lean says: let `K'/K` be finite, `O ⊆ K` and `O' ⊆ K'` discrete valuation rings with `O' ∩ K = O`, `A`
an abelian variety over `K` with semistable reduction at `O`, and `𝒩`, `𝒩'` Néron models of `A` over `O` and
of `A_{K'}` over `O'`. Then every group homomorphism `c : 𝒩 ×_O O' → 𝒩'` that is an isomorphism on generic
fibres maps the union of the identity components of the fibres of `𝒩 ×_O O'`, where that set is open, by an
open immersion onto the union of the identity components of the fibres of `𝒩'`.

A check compares this with the print, clause by clause: the kind of extension of discrete valuation rings the
print allows (OPEN.md's source line notes it may be stated over a strictly henselian trait), whether it speaks
of the canonical morphism or of any such `c`, the meaning of semistable reduction, and whether its conclusion
is this open immersion onto the identity component. If the print is more general and the Lean is a direct
instance of it, the verdict is YES. If OPEN.md's entry for this field changes after a fold, the method is the
same.

## Integrity rules

A reading counts as HUMAN-READ only if it states AI use (none, or what a tool did) and quotes the printed
statement verbatim and briefly, with edition and page, so that a second reader with that edition can check it.
The quote makes the reading checkable without trusting the reader's paraphrase.

A reading clears a flag of class pending-reading or reading-risk only when two independent readings agree, or
when one reading is by a reader that Jack or the maintainer has marked as known (the known_reader column of
[reviews.tsv](reviews.tsv)). One reading can be wrong, and clearing a flag can change the count.

A verdict that changes a count (LEAF to GLUE or back, a statement repair, a new consequence row) is ruled by Jack
or the maintainer, and the ruling is recorded in the reviews.tsv row (ruled_by). A flag in kinds.tsv clears only
through a pull request that cites that row. The person who records a reading is not the one who decides what it
changes.

**Row dependencies (Jack, 2026-11-24).** A bridge for row R may rest on row S only if S is a `frozenTarget`
hypothesis rated LEAF or proved; the dependency is recorded on R; demoting S demotes R in the same commit; two
rows can never certify each other.

Readings produced by AI tools, the project's included, are recorded as AI-READ evidence. An AI-READ reading clears
exactly one flag, `unread`, and only when the row's log records a page read of the cited print; for a source the
manuscript cites, the arXiv version it cites counts as the print for this flag (the next section says what else it
needs). It never counts as a human reading, and it clears no other flag: reading risks and statement checks stay
the reviewer's call.

Each reviews.tsv row has an evidence column: HUMAN-READ when a person read the print and the row meets the rule
above (AI use stated, a short verbatim quote, edition and page), AI-READ otherwise. AI-READ never counts as a human
reading: OPEN.md's count of human readings counts only distinct readers with evidence HUMAN-READ.

## Preprints and author copies

Published means refereed (ruling 2026-11-20):

* **Unrefereed sources.** A statement whose only source has not been refereed (an arXiv-only paper, a preprint
  series such as an MPIM preprint, lecture notes) is never published and never LEAF, whatever a reading finds. It
  counts as glue until it is proved in Lean or reduced to refereed sources, for example a refereed paper or book
  that states it.
* **Refereed papers read from an author copy.** When the reading used an author copy or an arXiv version of a
  refereed paper (the version the manuscript cites included), the quoted statement is checked against the
  journal text. The row keeps its rating while that check is pending. If the journal statement differs in a way
  that matters, the row becomes glue until it is repaired.

## What happens to a report

Each report becomes a row of [reviews.tsv](reviews.tsv): field, commit, reader, edition, page, display, copy,
quote, verdict, what was not read, AI use, the link to the report, any ruling, and the evidence (HUMAN-READ or
AI-READ). The next fold report states its effect. Apart from the `unread` rule above, only HUMAN-READ reports have
the effects below:

* YES on a row with no flag: the evidence mark becomes HUMAN-READ; the count does not change.
* YES on a flagged row: the flag clears under the two-reader or known-reader rule above, with a ruling where
  clearing it changes the count.
* CONSEQUENCE: the missing step becomes a new row of the open list.
* NO-statement: the statement is repaired, and the repair is credited to you.
* NO-locator: the citation is fixed.

If you find a statement false, vacuous or stronger than its source, the "Statement bug" issue form takes a
corrected statement. That is a credited result.

## AI use

You may use AI tools, for example to find a page or to translate. Say which tool did what. The quote and the
comparison must come from your own reading of the print. A reading that a tool produced is recorded as AI-READ
and does not count as a human check. Replies from the project that explain the Lean may be written by AI agents
that the project runs; each one carries a note saying so, and Jack McCarthy is accountable for them.

## Credit

Every recorded statement check and statement fix goes into [credits.tsv](credits.tsv) under your GitHub handle or
a pseudonym you choose, is named in the next fold report, and keeps your name when the work moves to the upstream
repository.
