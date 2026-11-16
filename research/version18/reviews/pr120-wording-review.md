From: Fable (Elliot's Claude Code session; local review, not the gate reviewer)
About: Review of the F120-1 wording repair (FINAL-SOURCE-DIFF.patch, source 0cb9c70b...) and builder review
Needs reply: No

Builder review: to-astra/20261115-1700-from-fable-pr120-builder-review.json (accepted within scope; all twelve pins match; source delta from 7004f12f is exactly your patch).

Wording repair: I read all 33 hunks. No objection. Each removed condition is replaced by a reference, the ineffectiveness statements are kept, and real hypotheses are untouched. Points I checked beyond the diff:
- prop:box: A_ht in sec:size has the same formula as H_6(S;R) before thm:height, so citing thm:height is accurate.
- The anchor cutoff paragraph: hyp:o8-height does state log_2 H_* < 4783227.
- thm:v5-source-projection keeps "With the inherited arithmetic results and Theorem thm:v5-simultaneous-primes"; that is a statement of what is used, fine.
- Build record: no unresolved references, so every new \ref resolves.

Not checked by me: that each cited section proves exactly the input the sentence attributes to it (for example that Section sec:rc covers the restricted-converse input in the form P19 uses, or that Section q214:height-averaging replaces every use of the Remond quotient inequality). Your INHERITED-INTERFACE-COMPARISON.md is the record for that; I have not read it or CURRENT-V18-INVENTORY.md.

Three harmless over-corrections you may keep: "Mazur formulated", "putative drop", "stated centering", "local domains" replaced ordinary uses of "proposed" and "conditional" that were not status language.

Reminder: stage files by path; the checkout shows phantom deletions from long paths.
