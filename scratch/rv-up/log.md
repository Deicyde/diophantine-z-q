# rv-up log

Adversarial verification of up-map, up-h, up-cr3, up-rest. Sources: N5 = diophantine_zq.tex (this worktree);
V13-V16 under ~/upstream (commit d76bcde); V15 = ~/upstream/research/version15/snapshots/v15-222-004/manuscript/quartic_v15.tex.

## Step 0
- No prior log; fresh start. Read docs/research/up-map.md (556 lines).

## Step 1 — item 1 (statements byte-identical N5 vs V16)
Script: scratch/rv-up/envcmp.py (own, independent of up-map's extract.py); compares CR-stripped lines.
- thm:target N5 60-76 = V16 113-129 IDENTICAL; thm:height N5 404-409 = V16 707-712 IDENTICAL;
  hyp:PC 1001-1004 = 1736-1739; hyp:RC 1005-1011 = 1746-1752; prop:fixed-prime-pattern 1267-1297 = 2076-2106;
  prop:cutoff 6285-6293 = 7268-7276; lem:pole 988-991 = 1723-1726; prop:generator 268-270 = 364-366;
  lem:assembly 110-113 = 204-207; prop:box 1225-1229 = 2034-2038. All IDENTICAL.
- H setup + constants block: N5 378-399 = V16 479-500 IDENTICAL (22 lines; constants F_0..H_6 at N5 391-396 = V16 492-497).
  up-map's "N5 l.390-400 = V16 l.489-499" is a misalignment (ranges differ, offset is +101 not +99); up-rest's
  "N5 L389-397 = V16 L491-499" also off by ~one. Minor locator error only. The line after (N5 400 vs V16 501) differs:
  "direct modularity argument" -> "published prime-five modularity theorem" (not part of statement).
- Pole section opening N5 973-1011 vs V16 1705-1752: only additions = openaihtp attribution (V16 1706-1707) and
  openaipointwise/openaigoldfeld paragraph (V16 1740-1744). Q_pole, E_l: y^2=x(x-l)(x+3l) (N5 986 = V16 1721) identical.
- Catalogue definition N5 238-245 = V16 331-338 IDENTICAL.
- Sections 9-12 (+ start of 13): N5 4382-6442 = V16 5365-7425 IDENTICAL (2061 lines). Includes catalogue bound in §12.
- lean/Frozen/BoundedIntegerPolynomial.lean: cmp byte-identical (sha256 0889579a...). lean/: 60 files each, only README.md differs.
- construction/: 28 files each; only README.md differs (upstream retitles "Original large construction"). up-rest says
  exactly this; the task prompt's "construction/ byte-identical" is true except README.md.
Verdict item 1: CONFIRMED (with locator correction for the constants block; construction/ modulo README.md).
