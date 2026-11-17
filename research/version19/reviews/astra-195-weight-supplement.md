# Supplement: exact counts of the printed 195 weights

16 November 2026. The original `REVIEW.md` is unchanged at SHA256 `49158d020dbf219e168ae36eb9f913899fc821209efdd53e1f9687f408fe861e`.

The original report's counts **186 nonzero Laurent weights** and **64 nonzero final C-balancing weights** are correct. Neither count includes a zero entry. Recounting the individual indices in the printed lists gives:

| Weight value | Laurent count | Final C-balancing count |
|---:|---:|---:|
| -3 | 2 | 0 |
| -1 | 7 | 26 |
| 0 | 0 | 0 |
| 1 | 165 | 36 |
| 2 | 2 | 2 |
| 3 | 10 | 0 |
| **Total printed nonzero entries** | **186** | **64** |

There are no duplicate indices in either list. The default-zero coordinates are not counted. The three special Laurent substitutions for old coordinates 77, 78 and 79 are also not counted as entries in the listed a_i table.

Both complete dictionaries equal the corresponding dictionaries in the pinned source certificate `affine_laurent195_v45/transformation.json`, SHA256 `5ac9fdcb6becd504d5e698373f52a5bddc99afe9c93614705b07efd3ff4f4e2f`.

The recount also checked both current files:

- `work/version19-250-draft-20261116/quartic_v19.tex`
- `work/version19-release-20261116/repo/manuscripts/quartic_v19.tex`

Both now have SHA256 `1f0e4db9e978115bb7f605f4bfcd84426a715b8cb6adaee3566107b33d61ad03`, and their printed weight dictionaries are identical. The earlier component audit was bound to source `388eb3e8...`; this supplement does not change that binding or claim a fresh audit of the intervening exposition changes.

Carbon's reported counts of 169 and 62 do not equal the sizes of these printed nonzero lists. This is a discrepancy in the reported counts; no additional mathematical check or change to the construction is needed to establish the counts above. I did not inspect Carbon's counting implementation or speculate about the reason for its figures.

The standalone recount and exact evidence are in `recount_weights.py` and `weight-count-supplement.json`. No manuscript, repository file, original report or original manifest was modified. The mathematics was not rerun.
