# h-leaves: the reduced trust base of the six-contact estimate H

Deliverable: `docs/research/h-leaves.md`. No manuscript, blueprint, Lean or other research file
was edited. No Lean was run (none was needed).

## Final table (after NoCM, R5.1 via GR14 + Tate, R5.2 option (b); with the unrecorded inputs I1, I2)

| # | Leaf | Statement as used | Best source (status) | Constant |
| --- | --- | --- | --- | --- |
| 1 | A001 | QM polarization, `P¹_j`, branch data `0, ∞, -16/27` / `4, 6, 2`, labelling of `j` | Baba–Granath, CJM 2008 (audit uses 2005 preprint); Lin–Yang arXiv (publication not determined) | none |
| 2 | A002 | integral model of the level-3 curve via `V₁(5)` | Buzzard, Duke 1997 (audit uses corrected 2002 author version) | none |
| 3 | A078 | stable-model extension, free quotients, tame Kummer form | SGA 1, Deligne–Mumford 1969 (now Stacks) | none |
| 4 | A061 | restriction of scalars, End rank, NOS, Hom field `L` | Mumford 1970; Serre–Tate 1968 | none |
| 5 | A079 | analytic QM data, `End⁰ ∈ {B, M₂(k)}` | Mumford 1970 | none |
| 6 | NoCM | CM points of `X⁶` over `t(u)`: reciprocity, count, Atkin–Lehner rule, (Emb) | González–Rotger JMSJ 2006 §5; Shimura 1967; Vignéras LNM 800; Cox | none |
| 7 | A062 | Skolem–Noether | Reiner, *Maximal orders* | none |
| 8 | A007 | `Br(ℚ)[2]` splitting | Cassels–Fröhlich; Milne ADT | none |
| 9 | A008, A063 | semisimplicity and End theorem for `A/L'` at `ℓ = 3, 5`; Hom theorem for `(A, J₁(N))` | GR14 Thm 1.4 (= A015) + Tate's argument (note §2.3) | none |
| 10 | A009 (new) | Lemma PG (good reduction over `L'_v(A[3])`, `v` above 5); crystalline comparison; descent | (Cris): Faltings 1989 / Coleman–Iovita 1999 / Breuil 2000 (UNCHECKED); PG from A013, A061 | none |
| 11 | A011 | Pan Thm 1.0.4 at `p = 5`; local algebraicity; Li; Shimura's `A_f` | Pan JAMS 2022; Serre 1968; Li 1975; Shimura 1973 | none |
| 12 | A064 | char. polynomials, Chebotarev, Brauer–Nesbitt | Mumford §19; Cassels–Fröhlich | none |
| 13 | I2 | reduction of homomorphisms (Néron mapping property) | BLR, *Néron models* | none |
| 14 | A012 | ramification breaks, conductor `≤ 2 + 2U₀` | Serre in Cassels–Fröhlich | none |
| 15 | A013 | semistable over `F(A[3])`, unipotent inertia | Silverberg–Zarhin 1995; SGA 7 IX 4.7 (UNCHECKED) | none |
| 16 | A071 | `Ĝ_m` logarithm at 2 | Silverman | none |
| 17 | I1 | level of `f` ≤ conductor of `ρ_{f,λ}` | Carayol 1986, Théorème (A) | none |
| 18 | A014 | `h_F(J₁(N)) ≤ 1.3·10⁷ N¹²` | Javanpeykar ANT 2014 | none |
| 19 | A015 | isogeny `J → A × Z`, degree `≤ κ(J)` | GR14 Thm 1.4 | none |
| 20 | A006 | height variation, additivity | Faltings 1983 Lemma 5; Raynaud, Astérisque 127 | none |
| 21 | A016 | `h_F(Z) ≥ -(3/2) dim Z` | GR14 §9 (Bost) | none |
| 22 | A017 | theta formula for `j` | Lauter–Naehrig–Yang JNT; Lin–Yang | none |
| 23 | A018 | theta vs Faltings height | Pazuki BSMF 2012 | none |

`H₆(S;R)` is unchanged; `SixContactEstimate` and `SixContactMin` hold as stated with the same
numerals (checked against `Hypotheses/Height.lean` lines 70-98 and `HeightMin.lean` lines 36-38).

## What changed

- **Inventory.** The proof of H consumes 26 audit records (A001-A018, A061-A065, A071, A078,
  A079). Two inputs have **no audit record and no citation**: Carayol's local–global
  compatibility (lines 852-857, the level of `f` is bounded by the conductor) and the Néron
  mapping property (lines 781-784). Both are standard but belong in the audit.
- **CM branch.** NoCM removes A003, A004, A005 and the H-use of A065 (26 → 22 records). The
  González–Rotger text was checked: their §5 proves the needed CM statements themselves, so
  Jordan's unpublished thesis is cited but not a leaf.
- **R5.1 works.** Both Faltings uses are qualitative, over `L'`, need no polarization and are at
  fixed `ℓ = 3, 5`. They follow from finiteness of the `L'`-isogeny class, which GR14 Thm 1.4
  (already A015) gives at once, by Tate's argument (written out in the note). Faltings 1983 then
  enters only through Lemma 5 (A006). The mod-`ℓ` refinements of Masser–Wüstholz 1995 (as
  restated by Zywina) need `ℓ ≥ c·max(d, h)^γ` and do **not** cover `ℓ = 3, 5`.
- **R5.2 works, and does better than planned.** Pan's hypothesis is potential semistability
  (checked in arXiv v2). A QM surface has good reduction over `L'_v(A[3])` at `v | 5` (Lemma PG,
  from A013, NOS and `B ⊗ ℚ₃` division), so `r₅` is potentially crystalline by the classical
  crystalline comparison for good reduction. This removes Scholze (with corrigendum) **and**
  Berger (A010). Option (a), the algebraic de Rham comparison (Fontaine 1983, Faltings 1989,
  Tsuji 1999), removes only Scholze.
- **Further leaves.** Raynaud's criterion (SGA 7) predates Silverberg–Zarhin. Milne's notes,
  Milne CFT, Brinon–Conrad, Conrad's preprint and the Stacks project have published
  replacements with the same statements; Baba–Granath, Buzzard and Pan are cited as preprint
  versions of published papers. No older replacement exists for Pan, Javanpeykar, Pazuki, GR14 or
  the theta formula.

## Open questions

1. **GR14 non-circularity.** Check in the pinned GR14 file that the proof of Theorem 1.4 uses
   neither the Tate conjecture, nor semisimplicity, nor Faltings' finiteness theorem. If it does,
   cite Masser–Wüstholz 1993 (isogeny paper) for the finiteness, after checking that it needs no
   polarization hypothesis.
2. **(Cris).** Pin a primary source and theorem number for "good reduction ⇒ `V_p` crystalline,
   with `D_cris` = `H¹_dR` and its Hodge filtration" over an arbitrary finite extension of `ℚ₅`.
3. Masser–Wüstholz 1993/1995, Bost's Bourbaki exposé, GR14, Faltings 1983/1989, Tsuji, Fontaine,
   Coleman–Iovita, Breuil, Tate 1966/1967, SGA 7 and Carayol could not be read here (only arXiv
   was reachable). Their statements are marked UNCHECKED, and attributions are taken from texts
   that were read (Berger's survey, Zywina, von Känel, Gaudron–Rémond 2011).

## Suggestions

- Add audit records for I1 (Carayol, weight 2, direction "level ≤ conductor") and I2 (Néron
  mapping property).
- When the CM paragraph is replaced by NoCM, also restate Lemma `lem:de-rham-descent` for the QM
  fibre with Lemma PG, delete the appeal to Berger, and change the sources of A008/A063 to
  "GR14 Thm 1.4 + Tate's argument". None of this touches a constant or the Lean statements.
- Prefer the three-case proof of NoCM or the short GR Thm 5.12 proof freely: both rest only on
  González–Rotger §5 (with Shimura 1967 and Eichler's optimal embeddings), not on Jordan's thesis.
