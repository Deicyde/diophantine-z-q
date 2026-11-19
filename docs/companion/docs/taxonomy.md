# Item↔Lean classification, for two repositories

Shared by every mapping, verifying, judging and skeptic agent. Adapted from the ternary Goldbach
companion's `TAXONOMY.md` and the Yang–Mills companion's `docs/taxonomy.md`. There a book or a
manuscript was compared with one Lean development. Here one manuscript, "[M]", is compared with
two repositories separately:

- **[F]**, `Deicyde/diophantine-z-q` at `f81ade8be515a0864bab15aacb80ffdbfd923d5d`;
- **[N]**, `nasqret/z-in-q-lean` at `de33a32dc47dfdb1efa6c70d0b837bc6a5c9a2c6`, with its kernel
  dependency `elliotglazer/diophantine-z-q` at `2358394558aafae202a1ce6d3bd1b536b79ad3d0`
  ("ndep").

Every judgment answers one question per repository: **does this repository state what [M] prints
here, and does it prove it?** The first half is the status; the second is the standing. The
book-only fields of the Goldbach guide (role in the proof, literature, changes since 2013) are
dropped.

## Sources

Paths are relative to the workspace the audit ran in, which held this folder as `repo/`.

- [M]: `m/diophantine_zq.tex` at `97cec7f`. The statements' LaTeX is in `scratch/items-text.json`.
- [F]: `fork/`. [N]: `nasqret/`. ndep: `ndep/`. None is built. Read the source, and trust the Lean
  statement over its docstring.
- The repositories' own maps, evidence of where to look and never of what is true: for [F],
  `blueprint/roadmap/**.md` (front matter `lean:`), `blueprint/sources/*-locators.md`,
  `docs/one-proof/OPEN.md`; for [N], `README.md`, `bounded/README.md`,
  `docs/qualitative-existence.md`, `docs/blueprint/`.
- Tool: `python3 -I repo/scripts/mapping/tool.py help` (`batch`, `item`, `tex`, `decl`, `search`,
  `exists`, `headlines`, `check`). Grep the source freely.

## Rules

1. Read-only everywhere except your own output file. Never run `lake`; never build.
2. Every declaration named is fully qualified and passes `tool.py exists <repo>`.
3. Compare statements, not names or summaries. Read the Lean signature and hypotheses in full,
   including section `variable`s, structure fields and the definitions the statement uses, before
   choosing a status.
4. **Two repositories, never mixed.** Judge each repository on its own source. Never carry a
   verdict from one to the other: [N]'s dependency is an earlier state of [F]'s kernel, and the
   two differ (for example in the pole curves).
5. `no-match` needs a real search of that repository: names, the repository's map, and greps for
   the item's distinctive symbols, constants and words. Record the searches in `searched`.
6. Own words in `note`: one or two sentences, premises before conclusions, no hedges, at most a
   short quoted phrase of [M].

## Status (per item, per repository)

| status | meaning | finding? |
|---|---|---|
| `exact` | A declaration states the item: same hypotheses and conclusion, same constants, the same objects (curves, polynomials, sets), up to notation, encoding (casts, `Finset` sums, bundled structures) and junk values. | no |
| `close` | The same claim with a difference a reader should know but no direction of strength: a normalization, an equivalent reformulation that takes an argument to see, the item's constants named abstractly. Name the difference. | no |
| `parts` | No single declaration states the item; the listed key declarations each state one of its claims, and together all of them. If a claim has no counterpart, the status is `no-match` or `weaker`, never `parts`. | no |
| `inlined` | A step (usually a display or passage inside a proof) with no standalone declaration, proved inside a named declaration's proof. Give the declaration and the `file:line` range of the step. | no |
| `definition-match` | A definition of [M] that agrees with the repository's. | no |
| `definition-close` | A definition that agrees up to a difference a reader should know (an equivalent but differently packaged condition, a normalization). | no |
| `not-formalized-not-needed` | The item asserts no mathematics the repository could prove: motivation, a summary pointing to other items, notation, a bibliography passage. Say why. | no |
| `no-match` | The item asserts mathematics and the repository holds no counterpart, alone or in parts, after a real search. Also when only some of its claims are there: say which are missing. | no (a checked absence) |
| `stronger` | The repository states more than [M] prints: weaker hypotheses, a stronger conclusion, a better constant. Say what. | **yes** |
| `weaker` | The repository states the item's shape but less: a worse constant, a narrower range, a weaker conclusion, a missing clause. Say which. | **yes** |
| `missing-hypothesis` | The repository's declaration needs a hypothesis that restricts the item's objects and that [M]'s statement (with the standing assumptions of its section) omits. Name it. Hypotheses that stand for theorems are not this: see *Standing*. | **yes** |
| `differs` | The repository states a different claim in the item's place, and neither implies the other: a different object (another curve, another polynomial, another set), different constants in both directions. For a definition this is written `definition-differs`. | **yes** |
| `unclear` | You could not decide. Say what blocks the decision. | — |

Conventions:
- `exact` / `definition-match` when hypotheses and conclusion agree once the repository's
  structures and definitions are unfolded and [M]'s standing assumptions are applied.
- `stronger` whenever the repository is more general in a mathematical way, even mildly.
- A display inside a statement maps to the declaration that states that part of the statement. A
  display or passage in a proof maps to the lemma that states the step (`exact` and the like) or
  to the proof that contains it (`inlined`).
- A passage of [M] that is a whole statement maps like that statement.
- Where a repository states an item twice (an internal and a public form, a kernel copy and a
  manuscript copy), list both as `key`.
- `parts` stays `parts` when some parts are stated more generally than [M] (a wider range of a
  parameter); say so in the note. `stronger` and `weaker` are for an item whose claims are
  stated together, or for `parts` where some claim is stated only in a weaker form (`weaker`).
- A repository may replace an argument of [M] by its own (for example [F]'s route AP in place of
  Proposition 6.2). The replacing argument's lemmas are not counterparts of the steps of [M]'s
  argument, even when they bound similar quantities for other sets: those steps are `no-match`,
  with the closest replacing declarations as `support` links named in the note. The exception is
  a replacing lemma that implies the step, for example by bounding a set that contains the
  step's set (Eq (6) and `card_TL_le`): compare it as a counterpart. `differs` needs a
  declaration about the item's own objects, or one that takes the item's own place.
- `definition-match` only when every object the item defines has a definition with the same
  content. When an object has no standalone definition (it occurs only inline or through
  instances) or is packaged with a changed range, the status is `definition-close`, naming it.
- A passage that defines objects and also asserts facts about them is `parts` (its definitions
  and its facts are the parts), with the verdict standing the weakest of its parts; a passage that
  only defines is `definition-*`.
- For [N], prefer [N]'s own declarations (including its copies of kernel definitions, such as
  `ZInQBlueprint.PublicText.*`) over ndep's. A `via_dependency` verdict's note says whether any
  [N] declaration uses the dependency declaration (grep `nasqret/` for its name).
- A finding names exactly what differs, and the declaration that comes closest. Before claiming
  one, look for what would refute it: the hypothesis supplied by a structure field, a section
  `variable`, a definition's body, [M]'s standing assumptions at the start of the section; the
  stronger claim proved elsewhere under another name.

## Standing (per declaration, from the index; per verdict, from the key declarations)

The standing values of the common brief, for one declaration, as the declaration index records
them (`tool.py decl` prints it; copy it):

| standing | meaning |
|---|---|
| `proved` | A theorem (or `example`, instance) whose own text has a complete proof: no `sorry`, no `admit`. |
| `assumed` | A `Prop` that the repository takes as a hypothesis of a headline theorem (also a field of such a hypothesis structure), or lists as open (`docs/one-proof/OPEN.md` for [F]). It is stated, not proved. |
| `definition` | A `def`, `abbrev`, `structure`, `class`, `inductive`, field or `opaque` that is not an assumed `Prop`. A `Prop`-valued definition with this standing is stated and neither proved by itself nor assumed by a headline. |
| `sorry` | A theorem whose proof contains `sorry` or `admit`. |

A theorem whose hypotheses include named `Prop`s that stand for theorems (of [M], or of the
literature [M] cites), such as `ZInQ.SixContactMin`, is `proved` as a declaration but its
statement is conditional. Its link lists those hypotheses in `assumes`. Such hypotheses do not
change the status: the status compares the remaining hypotheses and the conclusion with [M].

A link's standing is `conditional` when its declaration is `proved` and assumes a named `Prop`
that the repository does not prove outright. The Props proved outright, by a theorem with no
hypotheses and no `sorry`, are `HaltingAddMulBound`, `MordellWeilE`, `CatalogueBound8` (and in
[F] `KummerSelmerM`); `scripts/mapping/standing.py` lists them with their theorems.

The verdict for an item and a repository has one standing, from its carrying declarations (the
key links; for a `via_dependency` verdict, the dependency's links), not counting definitions.
For `parts` and `via_dependency` verdicts each carrying link is one claim of the item, so the
verdict takes the weakest of their standings; otherwise each key states the whole item, so it
takes the strongest. From strongest to weakest (`scripts/mapping/standing.py` computes it):

| verdict standing | meaning |
|---|---|
| `proved` | The carrying declarations that decide it are `proved`, and assume no Prop beyond those proved outright. |
| `conditional` | They are `proved` from a named `Prop` the repository does not prove outright (listed in `assumes`). The repository proves the item only from those hypotheses. Counted with `assumed` where a count asks whether the item is proved. |
| `assumed` | A deciding declaration is an assumed `Prop`. The repository takes the item, or a part of it, as a hypothesis. |
| `sorry` | A deciding declaration's proof has `sorry`. |
| `definition` | The carrying declarations are all definitions: the item is a definition, or a `Prop` the repository states without proving or assuming it. |
| `none` | No key declaration (`no-match`, `not-formalized-not-needed`, `unclear`). |

A link must never let an assumed or conditional statement read as a proved one. A note on an
assumed or conditional verdict says so and names the hypotheses.

## Roles of declarations (`lean[].role`)

| role | meaning |
|---|---|
| `key` | states the item (or, for `parts`, one of its claims; for `inlined`, contains the step in its proof) |
| `attributed` | the repository's own map attributes the item to it, and it is relevant, but it does not state the item |
| `support` | a definition or structure the statement is read through, a lemma that states a hypothesis or an ingredient; for [N], a dependency declaration where [N] has none of its own |
| `helper` | a lemma used in the key declaration's proof that carries a step the item mentions |

[N] and its dependency: [N] reaches much of [F]'s old kernel through ndep, which its build
compiles. Link an item to the [N] declaration that uses or restates the dependency's
declaration, and name the dependency's declaration in the note, or as a `support` link with
`"repo": "ndep"`. Only where [N] has no declaration of its own may a dependency declaration carry
the item, and then only with role `support`: set `"via_dependency": true` on the verdict, give the
status by comparing [M] with that dependency declaration, and take the standing from it. The
standing of a dependency declaration is the dependency index's (`tool.py decl ndep <name>`), and
ndep's `ZInQ.SixContactMin` and `ZInQ.Literature.GrossZagier` are assumed by [N]'s headlines.

## Status → relation (subject: [M]'s item; object: the Lean declaration)

Direction follows Literature Links (`ll/docs/companion.md`, *Relations*): `broadMatch` says the
object (the Lean declaration) is more general, `narrowMatch` that the subject ([M]) is.

| status | key link | other links |
|---|---|---|
| `exact`, `definition-match` | `exactMatch` | `relatedMatch` |
| `close`, `definition-close` | `closeMatch` | `relatedMatch` |
| `stronger` | `broadMatch` | `relatedMatch` |
| `weaker`, `missing-hypothesis` | `narrowMatch` | `relatedMatch` |
| `parts` | `hasPart` on each key link | `relatedMatch` |
| `inlined` | `relatedMatch` | `relatedMatch` |
| `differs`, `definition-differs` | `relatedMatch` | `relatedMatch` |
| `no-match`, `not-formalized-not-needed` | `noMatch` against the repository at its pin | `relatedMatch` |
| `unclear` | none | none |

The relation compares statements only. The standing travels beside it on every link, and the
note states it.

## Output (one JSON file per batch)

```json
{
  "batch": "S05-1",
  "agent": "mapper | verifier | judge",
  "items": [
    {
      "id": "Theorem 5.2",
      "fork": {
        "status": "exact",
        "standing": "assumed",
        "lean": [
          {"decl": "ZInQ.PoleCompleteness", "role": "key", "standing": "assumed",
           "where": "ZInQKernel/Hypotheses/Pole.lean:40-52", "assumes": [],
           "note": "what this declaration contributes, if not obvious"}
        ],
        "note": "One or two sentences on what differs and on the standing, premises first.",
        "step": "for a step in a proof: the declaration whose proof contains it, with file:line",
        "searched": ["for no-match / not-formalized-not-needed: names, greps, map pages searched"],
        "confidence": "high | medium | low"
      },
      "nasqret": {
        "status": "differs",
        "standing": "...",
        "lean": [{"decl": "...", "repo": "nasqret | ndep", "role": "key", "standing": "...",
                  "where": "...", "assumes": []}],
        "note": "...", "searched": [], "confidence": "..."
      }
    }
  ]
}
```

`where` is the repository-relative `file:line-line`. For [N] links, `repo` is `nasqret` or
`ndep`. `via_dependency` is present, and true, only on an [N] verdict carried by a dependency
declaration. Run `python3 -I repo/scripts/mapping/tool.py check <file>` and fix every error before you
finish.
