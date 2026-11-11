# rv-h-trust: report

**Verdict: adopt h-trust.md after the listed repairs.** The repairs are bookkeeping and citations.
No argument changes, no constant changes, and no unpublished upstream supplement is an input.
Full review: `docs/research/rv-h-trust.md`; log and scripts: `scratch/rv-h-trust/`.

Findings (VERIFIED unless marked):

1. **Completeness.**
   - Every line range of N5 L405-964, and the lemma at L10938-11000, falls in some step.
   - The Lean `SixContactEstimate` and `SixContactMin` match Theorem 4.1. Nothing is skipped.
   - Missing supplier in C8: the twist and weight argument needs the eigenform's 5-adic
     representation to be Hodge–Tate or de Rham with weights {0, 1−k}. That is p-adic Hodge theory
     of modular forms (Faltings 1987, Scholl 1990 or Saito 1997; STANDARD). N5 does not cite it,
     and neither does h-trust.
   - Minor uncited standard inputs in C9, C10, D4 and A4 (polarization uniqueness).
   - For rational u ∉ 𝒞, J(u) is never a branch value (`branch_check.py`).
2. **Review attributions.** I diffed the 11/4 text that Astra accepted (09c0c3f3, sha256
   `bfc4192d`) against N5. Three N5 passages were new and had no review before this one:
   - C3's de Rham lemma (11/4 used a Faltings 1988 sentence instead);
   - A9's Milne paragraph;
   - C9's Li–Shimura sentence.

   I reviewed all three here and they hold. h-trust credits C3 to Astra; that is wrong.
3. **Stale statuses.** rv-h-b1 was merged before h-trust. So A4-A6 are model-reviewed, not [U],
   and the docstring line "not yet reviewed" and the KERNEL_PLAN wording "review pending" must
   change.
4. **Unread locators overstated.** The Astra records already contain primary-source readings of
   Faltings 1983, Silverberg–Zarhin Thm 3.5, Berger, Javanpeykar, GR14 Thm 1.4 and §9, Pazuki,
   Baba–Granath and Pan v2.
   - The Berger reading gives the published numbering Thm 0.7 / Cor. 5.22.
   - The Faltings reading puts the Hom theorem at **Korollar 1**, not at Satz 4 as h-trust's E1
     says.
5. **D1 and D2 are valid.**
   - D2 does make W4 irrelevant.
   - D1's reason ("no new repository argument") rests on an N5 lemma that had no review until
     this one.
6. **Residuals.**
   - Item (iii) (Lemma PR and A4) is covered by rv-h-b1.
   - To add: the C8 supplier, the three single-review passages, and the height-normalization note.
   - N5's own integral-model route (reviewed by Astra) is a second route for A5-A6.
7. **Scripts.** All seven reruns are identical or agree, including c3_breaks.py ("ALL OK"), which
   h-trust had not rerun.

Repairs are listed by section in rv-h-trust.md §6. Still open: the network locator checks (Pan's
JAMS text, Carayol's Théorème A, the C8 supplier, Shimura 1973 Thm 1).
