From: Fable (Elliot's Claude Code session; local review, not the gate reviewer)
About: Review of the predecessor-transport checker and the dependency records in work/v18-release-final
Needs reply: No

Read in full: scripts/check_v18_predecessor_transport.py (303 lines), research/version18/dependencies/PREDECESSOR-TRANSPORT.md, CURRENT-FOUNDATION-STATUS.md, and the research-checks.yml hunk. Skimmed: the test file. Not read: CURRENT-V18-INVENTORY.md and CURRENT-V18-LABELS.json beyond their size. I ran both commands in that checkout: 7 tests OK; checker PASS (188 / 186 / 186).

No objection. The checker is a real derivation and not a copy: it parses the printed q214:rows section, compares it with the pinned candidate214 IR, builds the 212 rows from the displayed formulas (elementary symmetric functions of the five contact values, the additive aggregate, deletion of coordinates 119-120 and rows 64-65), builds the 204 rows (R-weights, the two reciprocal-pair blocks over Q(sqrt 2), the ratio equations, the weighted aggregate), and compares every coefficient with the pinned 204 table. It imports nothing from upstream. The scope statements in the docstring and in PREDECESSOR-TRANSPORT.md are right: finite identities only; the changed aggregate and division by R rest on the proof.

Small hardening, not blocking:
1. The three comparisons use zip. Printed counts are fixed at 214 and 188 and the 204 row count is checked afterwards, but len(source['coordinates']) == 214, len(source['residuals']) == 188 and len(target['coordinates']) == 204 are never asserted. Add the three length checks so a longer pinned file cannot pass by truncation (the hash pins make this theoretical).
2. The 212 intermediate is not compared with a pinned 212 table inside the checker. You did that separately against Jose's table b2f32d64; if that file is in the repository, add the comparison, otherwise say in PREDECESSOR-TRANSPORT.md that the 212 stage is certified only through the end-to-end 204 equality.

CURRENT-FOUNDATION-STATUS.md states the H201 and H170 position accurately and with the right limits.

Working-tree warning: git status in that checkout shows eight " D" entries under research/version14/evidence/release-completion-019/... (Windows "Filename too long"). They are not real deletions. Do not stage with git add -A or commit -a; add the new files by path, and check git diff --cached --stat before committing.
