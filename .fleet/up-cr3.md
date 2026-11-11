# up-cr3: fleet report

**Verdict: no.** No upstream version, from V13 through V16 or in the 214-variable proposal, gives
a route that narrows or removes CR₃. None gives a cheaper published input than Tian–Yuan–Zhang
with Proposition N and Gross–Zagier. Details, with version and line numbers, are in
`docs/research/up-cr3.md`; the log is `scratch/up-cr3/log.md`.

**Most important finding (VERIFIED).** Upstream's pole side has not changed since N5. Diffs of
`sec:pole` (N5 973–1122 against V16 1705–1898) show the following.
- The template is still `E_ℓ : y² = x(x−ℓ)(x+3ℓ)`, non-CM, with `ℓ ≡ 11 (mod 12)`.
- PC is still deduced from the restricted 2-converse RC by the same Rédei descent.
- Points still come from Kummer exactness, after rank 1 and finite Ш are known from Kolyvagin.
- The only changes are attributions to two OpenAI preprints of 7 October 2026 (V16 1740–1745,
  "cited for attribution, not assumed") and repairs of locators and proof details in the forward
  lemma (V14).

RC is still proved inside the manuscript, in about 8,300 lines. Version 16's release records say
that its audit left two RC inputs unread: Kato 1999 (Theorem 0.8 at p = 2) and Ribet 1990
(supersingular points through Eichler orders). Sources: `research/version16/README.md` 19 and
`FINDINGS.json` 33. Both results are used only inside RC (V16 2779–2784, 13780–13870 and
15102–15122). The later pole modules all take their completeness from RC as well: V16's
seven-variable `Ψ`, the linear-unit pole, and the 214 proposal (C04 in `source-carry.md`).

Upstream has none of the fork's fixes on this side:
- no congruent number template;
- no Tian–Yuan–Zhang, Proposition N or Kriz;
- Kolyvagin is kept where rank ≥ 1 would suffice;
- Proposition 0 has only a prose analog (V16 8925–8961). Its 2-adic claim was checked on 30
  curves, with no violation (`scratch/up-cr3/local2.py`).

No upstream design is excluded by the barriers, and no upstream design contradicts them. Every
upstream gadget has genus-1 fibres and locally uniform (LUS) soundness, and gets its witnesses from
a rank theorem.

**Single next step.** Record the exact statement of the openaipointwise preprint's Theorem 1.1 in
`cr3-map-literature.md` as an unrefereed alternative next to Kriz. The questions are its hypotheses
on `E`, whether it covers CM curves such as `C_d`, and how `s₂` is defined. Upstream pins revision
`4eaee875…`; the PDF is not in either clone, so a task with access to it is needed. Only if it
covers CM curves would it give a `dim Sel₂ = 3 ⇒ rank ≥ 1` form without the genus-sum condition,
and even then it would not replace the refereed TYZ route.
