# h-adopt work log

## Step 0 (start)
- Fresh run (no earlier log). Read rv-h-trust.md (§6 repairs S1-S4, O1-O12, R1-R6, D1-D3, N1-N3),
  h-trust.md, rv-h-b1.md §§7-8, h-b1.md §4A and changelog (h-b1-fix applied rv-h-b1 repairs 1-6).
- Note: scratch/rv-h-trust/ has no reruns/ subdirectory on this branch; rerun outcomes are cited
  from rv-h-trust §2.3 and its log.

## Step 1 (h-trust.md repairs)
- Applied rv-h-trust §6 S1-S4, O1-O12, R1-R6, D1-D3, N1-N3 to docs/research/h-trust.md; changelog
  appended. New mark ASTRA-READ. C8 supplier added (Faltings 1987; Scholl 1990 + Faltings 1989 /
  Tsuji 1999; Saito 1997). C3 / A9 Milne / C9 Li–Shimura marked rv-h-trust only. A4-A6 [M]
  (rv-h-b1). Faltings Korollar 1 for Hom; Berger Thm 0.7 / Cor. 5.22 published.
- Checked: Main.lean:66-73 (four admissibility facts), N5 L440 (`≤ 4·81`), N5 L9778 (Carayol locator).
- §3 drafts repaired (also kept in /tmp during the run; applied in step 2).

## Steps 2-4 (docstrings, KERNEL_PLAN, build)
- Height.lean: module docstring and SixContactEstimate docstring replaced by h-trust §3 drafts.
  HeightMin.lean: "## Trust" paragraph appended to module docstring; SixContactMin docstring
  replaced. KERNEL_PLAN.md: H row of the dependency table replaced (only H passage there).
  All lines ≤ 100 characters; no nested comment tokens.
- `lake build ZInQKernel`: success (9919 jobs).
- `lake env lean scripts/print_axioms.lean`: 59 entries, all [propext, Classical.choice,
  Quot.sound] (output scratch/h-adopt/print_axioms.out).
- scratch/h-adopt/strip_comments.py: code with comments stripped is identical to HEAD for both
  Lean files, so only comment text changed (git diff also inspected).

## Step 5
- Report written: .fleet/h-adopt.md. Done.
